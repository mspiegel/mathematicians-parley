//! Proof methods: a step's reason: defines, methods, closing.

use super::*;
use crate::notations::{BY_CASES, CARDINALITY};

impl<'a> Proof<'a> {
    /// Whether the define of that label gives its value by cases, as the
    /// page reads its line (the `by-cases` notation).
    pub(super) fn define_by_cases(&self, label: &str) -> bool {
        let Some(d) = self.thm.defines.iter().find(|d| d.label == label) else {
            return false;
        };
        self.rec
            .page
            .entries()
            .filter(|(key, _)| key.line == d.line)
            .any(|(_, n)| n.walk().iter().any(|m| m.notation() == BY_CASES))
    }

    /// The recursion a step cites by its label, the header's or one the
    /// proof lets, whose hypotheses are written alike; None for a citation
    /// of any other define.
    pub(super) fn recursion_cited(
        &self,
        just: &Justification,
    ) -> Option<CitedRecursion> {
        let label = just.defined.as_deref()?;
        let d = self.thm.defines.iter().find(|d| d.label == label)?;
        let by_cases = self.define_by_cases(label);
        match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(rule)) => {
                Some(CitedRecursion {
                    rule,
                    hypothesis: line_name(&d.label),
                    by_cases,
                })
            }
            _ => None,
        }
    }

    /// A step citing a recursion's rule, F(k + 1) = G(k): the first of the
    /// claim's applications of its functions, F(a), says which. At the
    /// numeral 0 it is F's start; at any other a it is F's step at a − 1,
    /// with a − 1 + 1 put back as a, and the arguments put in one form. A
    /// rule by cases is taken at the case the cited lines say: an equation
    /// its condition, `ite_eq_left`; one denied, `otherwise`, `ite_eq_right`.
    /// Its condition is put at a first, a − 1 + 1 inside it as a, for the
    /// cited line to match.
    pub(super) fn recursion_clause(
        &self,
        cited: &CitedRecursion,
        cases: &[super::super::algebra::Cited],
        claim: &Node,
        writer: &Writer,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::Proof;
        use super::super::tactics as t;
        let (r, hyp) = (&cited.rule, &cited.hypothesis);
        let mut case_rewrites: Vec<Tactic> = Vec::new();
        if cited.by_cases {
            for c in cases {
                let lemma = match (c.node.notation(), c.node.children.as_slice()) {
                    (EQUALITY, _) => "ite_eq_left",
                    (crate::notations::LOGICAL_NOT, [inner])
                        if inner.notation() == EQUALITY =>
                    {
                        "ite_eq_right"
                    }
                    _ => continue,
                };
                let rule = Printed::applied(
                    lemma,
                    super::super::doc::Source::Mathlib,
                    vec![c.proof.clone()],
                    super::super::doc::LeanType::Prop,
                );
                case_rewrites
                    .push(t::call("rw", vec![t::rules(vec![rule]), t::at_h(false)]));
            }
        }
        let mut cancel = vec![t::forwards(t::lemma("sub_add_cancel"))];
        if !case_rewrites.is_empty() {
            cancel.push(t::forwards(t::lemma("add_sub_cancel_right")));
        }
        let applied = claim.walk().into_iter().find_map(|n| {
            let [f, a] = n.children.as_slice() else {
                return None;
            };
            let at = r.names.iter().position(|name| *name == *f.text)?;
            (n.notation() == crate::notations::APPLICATION).then(|| (at, a.clone()))
        });
        let Some((at, arg)) = applied else {
            return Route::no("a recursion cited for a claim of none of its functions");
        };
        let n = r.names.len();
        // The hypothesis is the starts and then the steps, joined by ∧.
        let start = projection_path(at, n + 1);
        let steps = projection_path(n, n + 1);
        let step = projection_path(at, n);
        let closed = t::call("linarith", vec![]);
        let worked = t::call("ring_nf", vec![t::at_h(true)]);
        if arg.notation() == crate::notations::NUMERAL && &*arg.text == "0" {
            return Route::Built(Proof::By(Tactic::Seq(vec![
                t::name_h(&fields(t::hyp(hyp), &start)),
                worked,
                closed,
            ])));
        }
        let a = match writer.number_fixed(&arg, super::super::templates::Num::Int) {
            Route::Built(a) => a,
            Route::Declined(d) => return Route::Declined(d),
        };
        // The step at a − 1, a bracketed where it is a sum, as `a - 1`
        // reads it.
        let a = match a.prec() < 66 {
            true => t::bracket(a),
            false => a,
        };
        let int = super::super::doc::LeanType::Num(super::super::templates::Num::Int);
        let one_less = Printed::infix(
            super::super::doc::Op::MINUS,
            a,
            Printed::numeral("1", int.clone()),
            int,
        );
        let rule = fields(t::hyp(hyp), &steps);
        let omega = super::super::tactics::by_term(Proof::By(t::call("omega", vec![])));
        let at = Printed {
            kind: super::super::doc::TermKind::App {
                head: Box::new(rule),
                args: vec![
                    super::super::doc::Arg::Explicit(one_less),
                    super::super::doc::Arg::Explicit(omega),
                ],
                explicit: false,
            },
            ty: None,
        };
        let at_step = fields(t::bracket(at), &step);
        let mut tactics = vec![
            t::name_h(&at_step),
            t::simp_only(false, None, cancel, Some(t::at_h(false))),
        ];
        tactics.extend(case_rewrites);
        tactics.push(worked);
        tactics.push(closed);
        Route::Built(Proof::By(Tactic::Seq(tactics)))
    }

    /// A claim that a term of a wider type is an integer, a rational or a
    /// real, (A + B) − B ∈ ℚ of reals or √b + 1 ∈ ℝ of a square root in ℂ,
    /// where some part of it a line the step names says is in that type, as
    /// the check found it (`integer_line`): the term written there, that
    /// part the number the line gives, as Lean's witness. A citation of an item over ℚ gives such a
    /// claim nothing, as of rationals it holds by their type.
    pub(super) fn member_by_integers(
        &self,
        node: &Node,
    ) -> Option<super::super::doc::Proof> {
        let [term, set] = node.children.as_slice() else {
            return None;
        };
        use super::super::templates::Num;
        // The type the term is said to be in, and the type its parts are
        // said to be in: ℕ₀ is said of an integer, its parts integers.
        let (claimed, ty) = match super::super::expr::system_of(set)? {
            super::super::expr::System::Type(t @ (Num::Int | Num::Rat | Num::Real)) => {
                (t, t)
            }
            super::super::expr::System::NonNegative => (Num::Nat, Num::Int),
            _ => return None,
        };
        let wide = self.writer.carrier(term).built()?;
        if node.notation() != crate::notations::MEMBERSHIP || wide <= ty {
            return None;
        }
        let mut writer = self.writer.with_letters(self.writer.letters.clone());
        let mut lines = Vec::new();
        // The parts within the term: the term itself is what the step
        // claims, and a letter of the type said is in it already; a letter
        // of a wider type, A ∈ ℝ, may be said an integer.
        let whole = writer.grammar.print(term);
        for part in term.walk() {
            let typed = part.is_name()
                && writer.carrier(&part).built().is_some_and(|c| c <= ty);
            if typed
                || part.notation() == crate::notations::NUMERAL
                || writer.grammar.print(&part) == whole
            {
                continue;
            }
            if let Some(said) = self.integer_line(&part, ty) {
                let line = said.proof;
                if lines.contains(&line) {
                    continue;
                }
                writer.integers.push(super::super::expr::SaidInteger {
                    term: writer.grammar.print(&part),
                    proof: line.clone(),
                    ty,
                    value: None,
                    slot_only: false,
                    back: None,
                });
                lines.push(line);
            }
        }
        if lines.is_empty() {
            return None;
        }
        use super::super::tactics as t;
        let witness = writer.number_fixed(term, ty).built()?;
        let rules: Vec<super::super::doc::Rule> = lines
            .iter()
            .map(|line| {
                t::forwards(Printed::applied(
                    "Classical.choose_spec",
                    super::super::doc::Source::Core,
                    vec![line.clone()],
                    super::super::doc::LeanType::Prop,
                ))
            })
            .collect();
        // The witness is the term written with the named integers, so their
        // equations put in leave the two sides one.
        let equal = super::super::tactics::by_term(super::super::doc::Proof::By(
            specs_then(&rules),
        ));
        let parts = match claimed {
            // In ℕ₀: the integer, beside its being at least 0, by the
            // said-once walk's reason for the term (`nonneg_by`).
            Num::Nat => {
                let order = self.said_nonneg(term)?;
                vec![witness, order, equal]
            }
            _ => vec![witness, equal],
        };
        let shown = Tactic::Exact(super::super::expr::anonymous(parts));
        Some(super::super::doc::Proof::By(Tactic::Group(Box::new(shown))))
    }

    pub(super) fn proof_by_reason(
        &self,
        reason: Reason,
        k: usize,
        node: &Node,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::Proof;
        use super::super::tactics as t;
        // A restate step, or a requires line of lines alone, whose claim the
        // checker found a line states (`restated`): that line, met as a
        // whole before any "for all" of the claim is taken apart.
        if matches!(
            reason.just.head,
            Head::Method(Method::Restate) | Head::Lines
        ) {
            if let Some(proof) = self.restated_proof(reason.just.line, node) {
                return Route::Built(proof);
            }
        }
        match &reason.just.head {
            Head::Item { .. } => self.citation(reason, k, node),
            Head::Method(m) => {
                // A claim said of every member of a set is proved of one,
                // taken as the method's letter. Substitute rows each say
                // the whole claim, "for all" and all, and end on it; so does
                // a substitution the checker found into a line's "for all"
                // as a whole, its places counted from the top of it
                // (`substituted`). So does an instance whose values name no
                // letter of the claim's "for all", `L(i) is an upper bound of
                // I(i)` at k := i, which says the "for all" itself.
                let whole = self
                    .substitution_record(reason.just.line, Some(k), false)
                    .is_some_and(|r| r.start.notation() == crate::notations::FOR_ALL);
                let rows = (*m == Method::Substitute
                    && (!reason.just.rows.is_empty() || whole))
                    || (*m == Method::Instantiate
                        && self.instance_says_for_all(reason.just, node));
                let (intros, body, writer) = match rows {
                    true => (
                        Vec::new(),
                        node,
                        self.writer.with_letters(self.writer.letters.clone()),
                    ),
                    false => self.peel(node),
                };
                let opened = !intros.is_empty();
                if opened {
                    *self.intros_now.borrow_mut() = intros.clone();
                }
                let proof = self.method_proof(reason, *m, k, body, &writer);
                if opened {
                    self.intros_now.borrow_mut().clear();
                }
                let proof = match proof {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let before = self.counts_to_integers(*m, reason.just);
                let proof = match before.is_empty() {
                    true => proof,
                    false => Proof::By(Tactic::Seq(
                        before.into_iter().chain([tactic_of(&proof)]).collect(),
                    )),
                };
                Route::Built(with_intros(&intros, proof))
            }
            // A step citing a define claims its equation, which Lean's `set`
            // put in scope under the define's label.
            Head::Define => match self.recursion_cited(reason.just) {
                // A rule said for every n, F(n + 1) = 2F(n): said of one n.
                Some(r) => {
                    let (intros, body, writer) = self.peel(node);
                    let cases = self.cited_parts(&reason.just.from);
                    self.recursion_clause(&r, &cases, body, &writer)
                        .map(|clause| match intros.is_empty() {
                            true => clause,
                            false => Proof::By(Tactic::Seq(vec![
                                Tactic::Intro(intros.clone()),
                                tactic_of(&clause),
                            ])),
                        })
                }
                // A function the header lets by its value: its equation
                // put in, f(a) its value at a, and the claim closed, as it
                // stands where the checker met the claim's sides with the
                // value written out (`define_links`), and once worked out
                // where it recorded arithmetic left. Not of a value by cases,
                // whose case the record does not say, nor of a claim "for
                // all", where the equation's condition, its argument in the
                // function's domain, is to be shown of the claim's letter
                // and `omega` does not show it.
                None => match self.header_function_cited(reason.just) {
                    // A function the header lets by cases on a domain: its
                    // equation at the argument the cited line puts in the
                    // domain (`define_domains`), `hD1 _ h`, and the case the
                    // checker took (`define_cases`).
                    Some(hyp)
                        if reason
                            .just
                            .defined
                            .as_deref()
                            .is_some_and(|l| self.define_by_cases(l))
                            && self
                                .rec
                                .define_cases
                                .contains_key(&reason.just.line)
                            && self
                                .rec
                                .define_domains
                                .contains_key(&reason.just.line) =>
                    {
                        let taken = &self.rec.define_cases[&reason.just.line];
                        let domain = self.domain_proof(
                            &self.rec.define_domains[&reason.just.line],
                            None,
                        );
                        match (domain, self.conditions_put(taken, node)) {
                            (Route::Built(domain), Route::Built(conditions)) => {
                                let equation =
                                    hyp_applied(&hyp, vec![elided_term(), domain]);
                                let mut rules = vec![t::forwards(equation)];
                                rules.extend(conditions);
                                let alone =
                                    taken.meeting.as_ref().is_some_and(unfolds_alone);
                                Route::Built(Proof::By(simp_unfolded(
                                    rules,
                                    alone,
                                    node.notation() == crate::notations::FOR_ALL,
                                )))
                            }
                            _ => Route::Built(header_ways(&hyp)),
                        }
                    }
                    Some(hyp)
                        if self.rec.define_links.contains_key(&reason.just.line)
                            && !reason
                                .just
                                .defined
                                .as_deref()
                                .is_some_and(|l| self.define_by_cases(l))
                            && node.notation() != crate::notations::FOR_ALL =>
                    {
                        let met = &self.rec.define_links[&reason.just.line];
                        let alone = met.as_ref().is_some_and(unfolds_alone);
                        Route::Built(Proof::By(unfolded_by(&[hyp], alone, false)))
                    }
                    // A claim "for all" of a header's function: its equation
                    // at the member, where the record says what puts the
                    // member in the domain (`define_domains`).
                    Some(hyp)
                        if node.notation() == crate::notations::FOR_ALL
                            && !reason
                                .just
                                .defined
                                .as_deref()
                                .is_some_and(|l| self.define_by_cases(l)) =>
                    {
                        match self.for_all_by_header(&hyp, node, reason.just.line) {
                            Route::Built(p) => Route::Built(p),
                            Route::Declined(_) => Route::Built(header_ways(&hyp)),
                        }
                    }
                    Some(hyp) => Route::Built(header_ways(&hyp)),
                    // A define of the proof's, its equation under the
                    // define's label: unfolded, as a calculation row
                    // citing it is, L(k) = N(k)/10^k of L's `set`.
                    None => {
                        let unfold: Vec<String> = reason
                            .just
                            .refs
                            .iter()
                            .filter(|r| self.thm.defines.iter().any(|d| d.label == **r))
                            .filter_map(|r| self.named.get(r).and_then(|n| n.first()))
                            .cloned()
                            .collect();
                        // The claim's sides as the checker met them with the
                        // defines written out (`define_links`).
                        let met = self.rec.define_links.get(&reason.just.line);
                        // A define by cases, `h(i) = g(i) if i ≤ j, else p`,
                        // whose case the cited lines show: what the record
                        // says of its sides does not say which case holds.
                        let by_cases = reason.just.refs.iter().any(|r| {
                            self.thm.defines.iter().any(|d| d.label == *r)
                                && self.define_by_cases(r)
                        });
                        if let (Some(met), false, false) =
                            (met, unfold.is_empty(), by_cases)
                        {
                            let cast = match self.writer.formula(node) {
                                Route::Built(claim) => match &claim.kind {
                                    super::super::doc::TermKind::Infix {
                                        lhs,
                                        rhs,
                                        ..
                                    } => self.unfolds_to_casts(lhs, rhs),
                                    _ => false,
                                },
                                Route::Declined(_) => false,
                            } || self
                                .kinded_at_compound(&reason.just.refs, node);
                            let alone = met.as_ref().is_some_and(unfolds_alone);
                            return Route::Built(Proof::By(unfolded_by(
                                &unfold,
                                alone && !cast,
                                node.notation() == crate::notations::FOR_ALL,
                            )));
                        }
                        // A define by cases at the case the checker took
                        // (`define_cases`): each condition it passed put by
                        // the line that says it, `if_pos` where it holds and
                        // `if_neg` where it fails, and the case's value met
                        // with the other side as the record met them.
                        if let (Some(taken), false, true) = (
                            self.rec.define_cases.get(&reason.just.line),
                            unfold.is_empty(),
                            by_cases,
                        ) {
                            if let Route::Built(conditions) =
                                self.conditions_put(taken, node)
                            {
                                let alone =
                                    taken.meeting.as_ref().is_some_and(unfolds_alone);
                                let mut rules: Vec<super::super::doc::Rule> = unfold
                                    .iter()
                                    .map(|d| t::forwards(t::hyp(d)))
                                    .collect();
                                rules.extend(conditions);
                                return Route::Built(Proof::By(simp_unfolded(
                                    rules,
                                    alone,
                                    node.notation() == crate::notations::FOR_ALL,
                                )));
                            }
                        }
                        // A define Lean writes out in place, a function's
                        // value at its argument, leaves the two sides alike:
                        // `rfl`.
                        if let Route::Built(claim) = self.writer.formula(node) {
                            if let super::super::doc::TermKind::Infix { op, lhs, rhs } =
                                &bare_term(&claim).kind
                            {
                                if op.symbol == "="
                                    && bare_term(lhs).untyped()
                                        == bare_term(rhs).untyped()
                                {
                                    return Route::Built(Proof::Term(
                                        Printed::constant(
                                            "rfl",
                                            super::super::doc::Source::Core,
                                            super::super::doc::LeanType::Prop,
                                        ),
                                    ));
                                }
                            }
                        }
                        if unfold.is_empty() {
                            return Route::no(
                                "a define step Lean writes with two sides apart",
                            );
                        }
                        let why = match by_cases {
                            true => ListReason::DefineByCases,
                            false => ListReason::DefineSides,
                        };
                        ways_proof(why, unfolded(&unfold))
                    }
                },
            },
            // One manipulation of a line: linear arithmetic on the line the
            // checker found it made from (`orders`).
            Head::Manipulation(_) => {
                self.order_proof(reason.just.line, k, node, &self.writer)
            }
            // A requires line's lines: the fact is what they say, or
            // follows from it by arithmetic.
            // A membership of ℕ₀ or ℕ they give, `gcd(s, w)² ∈ ℕ: from 1`,
            // by the said-once walk over them (`member_bound`).
            Head::Lines => match self.member_bound(reason.just, node) {
                Some(p) => Route::Built(Proof::Term(p)),
                None => Route::no("a requires line its lines give no bound for"),
            },
        }
    }

    /// A step that computes by a ring or an order, which ℕ∞ is not, takes
    /// each line it cites that counts a finite set in ℕ∞ to the integers
    /// first, in the step's own proof: each such count rewritten as the
    /// set's count in ℕ cast up, the set finite by why the record says it is
    /// (`Set.Finite.cast_ncard_eq`), the equation in ℕ∞ then read in ℕ
    /// (`norm_cast`), and that said of integers (`zify`). Any other step
    /// meets its lines as they are written.
    pub(super) fn counts_to_integers(
        &self,
        m: Method,
        just: &Justification,
    ) -> Vec<Tactic> {
        use super::super::doc::{CountForm, Location, TermKind};
        use super::super::tactics as t;
        if !matches!(
            m,
            Method::Algebra | Method::Arithmetic | Method::Inequalities
        ) {
            return Vec::new();
        }
        let mut out = Vec::new();
        for cited in self.cited_parts(&just.refs) {
            let (Some(says), TermKind::Letter(name)) = (&cited.says, &cited.proof.kind)
            else {
                continue;
            };
            let mut rules = Vec::new();
            for set in self.counted_sets(&[&cited.node]) {
                let Route::Built(written) = self.writer.set_term(&set) else {
                    continue;
                };
                let extended = says.walk().iter().any(|c| {
                    matches!(&c.kind, TermKind::Count { set, form: CountForm::Extended }
                        if set.untyped() == written.untyped())
                });
                if let (true, Some(finite)) = (extended, self.shown_finite(&set)) {
                    rules.push(t::backwards(cast_ncard_eq(&finite)));
                }
            }
            if rules.is_empty() {
                continue;
            }
            let at = || TacticArg::At(vec![Location::Hypothesis(name.clone())]);
            out.push(t::call("rw", vec![TacticArg::Rules(rules), at()]));
            out.push(t::call("norm_cast", vec![at()]));
            out.push(t::call("zify", vec![at()]));
        }
        out
    }

    /// A claim's leading "for all" taken off: the names its letters and
    /// their guards are introduced by, the body, and the letters in scope
    /// with the claim's own added.
    /// Whether an instantiate's claim, said "for all", is said by the
    /// instance itself: every letter the line's "for all" binds is given a
    /// value, k := i of "for all k ∈ {1, …, N}, … L(k) is an upper bound of
    /// I(k) …", so what is left of the line says the claim's "for all".
    /// Where a letter of the line is given none, j of "for all N, for all
    /// j ∈ {1, …, N}" at N := n, it is read at the claim's own letter, and
    /// the claim is proved of one member.
    pub(super) fn instance_says_for_all(
        &self,
        just: &Justification,
        node: &Node,
    ) -> bool {
        if node.notation() != crate::notations::FOR_ALL || just.values.is_empty() {
            return false;
        }
        let Some(recorded) = self.rec.instantiated.get(&just.line) else {
            return false;
        };
        let Route::Built(part) = self.line_part(&recorded.at) else {
            return false;
        };
        let mut body = &part.node;
        while matches!(
            body.notation(),
            crate::notations::FOR_ALL | crate::notations::FOR_ALL_SETS
        ) {
            let Some(letter) = body.children.first() else {
                return false;
            };
            if !just.values.pairs().any(|(n, _)| *n == *letter.text) {
                return false;
            }
            body = match body.children.last() {
                Some(inner) => inner,
                None => return false,
            };
        }
        true
    }

    pub(super) fn peel<'n>(
        &self,
        node: &'n Node,
    ) -> (Vec<String>, &'n Node, Writer<'a>) {
        let mut writer = self.writer.with_letters(self.writer.letters.clone());
        let mut intros = Vec::new();
        let mut body = node;
        while body.notation() == crate::notations::FOR_ALL {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let name = super::super::names::letter(&letter.text);
            // Over a range, a number system or another set of numbers, [0,
            // 1]: the letter of the numbers' type, and where the type does
            // not say it, the fact that it is in the set. Over a set of
            // things, sets or a group's elements, a member of their type,
            // and the fact.
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
                writer.introduce(
                    &letter.text,
                    super::super::expr::range_letter_system(set),
                );
                (None, true)
            } else {
                match (
                    super::super::expr::system_of(set),
                    self.writer.set_members(set),
                ) {
                    (Some(s), _) => {
                        writer.introduce(&letter.text, s);
                        (None, !matches!(s, super::super::expr::System::Type(_)))
                    }
                    (None, Some(super::super::expr::Members::Numbers(n))) => {
                        (Some(LetterType::Number(n)), true)
                    }
                    (None, Some(m)) => (Some(LetterType::Member(m)), true),
                    (None, None) => break,
                }
            };
            if let Some(ty) = ty {
                writer.letters.insert(letter.text.to_string(), ty);
                writer.wholes.shift_remove(&*letter.text);
            }
            intros.push(name.clone());
            if guarded {
                intros.push(format!("h_{name}"));
            }
            body = inner;
        }
        (intros, body, writer)
    }

    /// A claim that two pairs are equal or differ, by a method that decides
    /// pairs coordinate by coordinate (`METHODS.md`, Pairs): equal by both
    /// coordinates' equations, `Prod.ext (show a = c by …) (show b = d by
    /// …)`; apart at the coordinate the checker found them apart at
    /// (`CheckedTheorem::pairs_apart`), `fun h => (show a ≠ c by …)
    /// (congrArg Prod.fst h)`. Each coordinate's claim is proved as the
    /// method proves a claim of numbers. None where the claim is no
    /// relation between two pairs.
    fn pairs_compared(
        &self,
        reason: Reason,
        m: Method,
        k: usize,
        node: &Node,
        writer: &Writer,
    ) -> Option<Route<super::super::doc::Proof>> {
        use super::super::doc::{LeanType, Proof, Source, TermKind};
        use super::super::tactics as t;
        let (equation, negated) = match (node.notation(), node.children.as_slice()) {
            (crate::notations::LOGICAL_NOT, [inner])
                if inner.notation() == EQUALITY =>
            {
                (inner, true)
            }
            (EQUALITY, _) => (node, false),
            _ => return None,
        };
        let [left, right] = equation.children.as_slice() else {
            return None;
        };
        let l = super::super::expr::pair_coordinates(left)?;
        let r = super::super::expr::pair_coordinates(right)?;
        // The claim of one coordinate, a = c or a ≠ c, shown by the method.
        let coordinate = |i: usize| -> Route<Printed> {
            let equal = equation.with_children(vec![l[i].clone(), r[i].clone()]);
            let claim = match negated {
                true => node.with_children(vec![equal]),
                false => equal,
            };
            let says = match writer.formula(&claim) {
                Route::Built(s) => s,
                Route::Declined(d) => return Route::Declined(d),
            };
            self.method_proof(reason, m, k, &claim, writer)
                .map(|proof| super::conversions::shown(says, proof))
        };
        if !negated {
            return Some(match (coordinate(0), coordinate(1)) {
                (Route::Built(a), Route::Built(b)) => {
                    Route::Built(Proof::Term(Printed::applied(
                        "Prod.ext",
                        Source::Core,
                        vec![a, b],
                        LeanType::Prop,
                    )))
                }
                (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
            });
        }
        let Some(at) = self.rec.pairs_apart.get(&reason.just.line) else {
            return Some(Route::no("pairs apart at no coordinate the checker found"));
        };
        let (i, projection) = match at {
            crate::methods::pairs::Coordinate::First => (0, "Prod.fst"),
            crate::methods::pairs::Coordinate::Second => (1, "Prod.snd"),
        };
        Some(coordinate(i).map(|apart| {
            let equal_there = Printed::applied(
                "congrArg",
                Source::Core,
                vec![
                    Printed::constant(projection, Source::Core, LeanType::Prop),
                    t::hyp("h"),
                ],
                LeanType::Prop,
            );
            Proof::Term(Printed::of(
                TermKind::Lambda {
                    letters: vec!["h".to_string()],
                    body: Box::new(applied_to(apart, equal_there)),
                },
                LeanType::Prop,
            ))
        }))
    }

    /// The proof of a claim by a method that closes it, with the letters
    /// `writer` holds.
    pub(super) fn method_proof(
        &self,
        reason: Reason,
        m: Method,
        k: usize,
        node: &Node,
        writer: &Writer,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::Proof;
        let just = reason.just;
        if matches!(
            m,
            Method::Algebra | Method::Arithmetic | Method::RealArithmetic
        ) {
            if let Some(compared) = self.pairs_compared(reason, m, k, node, writer) {
                return compared;
            }
        }
        Route::Built(match m {
            Method::Algebra => {
                // A cited equation of a narrower type is combined as the
                // claim's type has it.
                let mut cited = self.cited_parts(&just.refs);
                for c in &mut cited {
                    if let Some(read) = self.at_recorded_letter(c, &node.names()) {
                        *c = read;
                    }
                }
                // A define the step cites is written out, in the claim and
                // in each line it cites, as the checker reads the step: in
                // Lean, its equation rewrites them all, and the casts it
                // leaves are pushed in. Lines are widened after, as they
                // then read.
                // A define's value may name another the step cites, v's of
                // ω₁, so they are written out until none is left.
                let defines = self.cited_defines(&just.refs);
                // A function the header lets, rewritten by its equation at
                // each argument the record found (`header_functions_applied`),
                // under a sum term by term.
                let headers = match self.header_functions_applied(just) {
                    Route::Built(h) => h,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let header_rewrite: Vec<Tactic> = match headers.is_empty() {
                    true => Vec::new(),
                    false => vec![super::super::tactics::call(
                        "rw",
                        vec![TacticArg::Rules(
                            headers
                                .iter()
                                .map(|h| {
                                    super::super::tactics::forwards(h.equation.clone())
                                })
                                .collect(),
                        )],
                    )],
                };
                let mut claim = headers
                    .iter()
                    .fold(node.clone(), |n, h| self.put_define(&n, &h.define));
                for d in &defines {
                    cited.retain(|c| c.proof != super::super::tactics::hyp(&d.proof));
                }
                let grammar = &self.sources.checked.grammar;
                let printed = |claim: &Node,
                               cited: &[super::super::algebra::Cited]|
                 -> Vec<String> {
                    std::iter::once(claim)
                        .chain(cited.iter().map(|c| &c.node))
                        .map(|n| grammar.print(n))
                        .collect()
                };
                for _ in 0..=defines.len() {
                    let before = printed(&claim, &cited);
                    for d in &defines {
                        claim = self.put_define(&claim, d);
                        for c in &mut cited {
                            c.node = self.put_define(&c.node, d);
                        }
                    }
                    if printed(&claim, &cited) == before {
                        break;
                    }
                }
                // A claim whose two sides are one term once the defines are
                // put in is closed by writing them out in it, which leaves
                // `a = a`.
                let same_sides = claim.notation() == EQUALITY
                    && matches!(claim.children.as_slice(),
                        [l, r] if grammar.print(l) == grammar.print(r));
                if same_sides && grammar.print(&claim) != grammar.print(node) {
                    let goal = [RewriteAt {
                        at: super::super::doc::Location::Goal,
                        said: vec![node.clone()],
                        stated: writer.formula(node).built().into_iter().collect(),
                    }];
                    // The rewrite leaves the sides one term, which it closes:
                    // no cast is left to push.
                    let mut lines = header_rewrite;
                    lines.extend(written_out_as(&defines, &goal, writer, false));
                    return Route::Built(Proof::By(Tactic::Seq(lines)));
                }
                let mut haves = Vec::new();
                for c in &mut cited {
                    match self.widened(&c.node, &c.proof, &claim, writer) {
                        Route::Built(w) => {
                            haves.extend(w.have);
                            c.proof = w.name;
                        }
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // Each read with its identity elements dropped, as the
                // checker decides it: F(0 + 1) and F(1) are one term, and
                // (d·1).toNat and d.toNat. Lean has them one where the
                // check normalises inside each term (`algebra`'s
                // `inside_terms`): where dropping changes a line, or a
                // function's argument is numerals worked on, F(1 + 1).
                let ctx = self.sources.ctx;
                let print = |n: &Node| self.writer.grammar.print(n);
                let mut inside_terms = numerals_in_an_argument(&claim)
                    || cited.iter().any(|c| numerals_in_an_argument(&c.node));
                let bared = crate::matching::bare(&claim, ctx);
                inside_terms |= print(&bared) != print(&claim);
                let claim = bared;
                for c in &mut cited {
                    let bared = crate::matching::bare(&c.node, ctx);
                    inside_terms |= print(&bared) != print(&c.node);
                    c.node = bared;
                }
                let divisors = match self.divisors_at(just.line, &defines) {
                    Route::Built(d) => d,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let proof = match super::super::algebra::algebra(
                    writer,
                    self.sources.targets,
                    &claim,
                    &cited,
                    inside_terms,
                    &divisors,
                    self.worked_in.get(),
                ) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let mut lines: Vec<Tactic> = header_rewrite;
                lines.extend(written_out(&defines, &self.rewritten_at(node), writer));
                lines.extend(haves);
                return Route::Built(haves_then(lines, proof));
            }
            Method::Arithmetic => {
                let says = match writer.formula(node) {
                    Route::Built(s) => s,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match worked_out(&says) {
                    Route::Built(tactic) => Proof::By(tactic),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            // Arithmetic of real numbers, √8 = 2√2 or ln(2) ≠ 0: each
            // special value put as its value by its law, and the sides
            // compared, as Metamath proves it (`reals`).
            Method::RealArithmetic => {
                match super::super::reals::real_arithmetic(
                    writer,
                    self.sources.targets,
                    node,
                ) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            // Rows are linear moves on the line the first row cites, so the
            // claim follows from that line by linear arithmetic, as a step
            // with no rows does from the lines it cites.
            Method::Inequalities | Method::Transitivity | Method::Antisymmetry => {
                // What the checker recorded the step rests on: a chain's
                // links, composed link by link (`chain_composed`); the facts
                // of an order step (`orders`); the two lines of an
                // antisymmetry (`antisymmetric`).
                return match m {
                    Method::Inequalities => {
                        self.order_proof(just.line, k, node, writer)
                    }
                    Method::Antisymmetry => {
                        self.antisymmetry_proof(just.line, node, writer)
                    }
                    _ => self.chain_composed(just, node, writer),
                };
            }
            Method::Substitute => return self.substitute(just, k, node, writer),
            Method::Calculation => return self.calculation(just, writer),
            Method::Exhibit => return self.exhibit(just, node),
            Method::Instantiate => return self.instantiate(just, k, node, writer),
            Method::Membership => return self.membership(just, node, writer),
            // The lines the checker found each part of the claim in
            // (`joined`), put together.
            Method::Join => return self.join_proof(just.line, k, node, writer),
            Method::Inspection => match self.inspection_proof(just) {
                Some(proof) => proof,
                None => return Route::no("an inspection the record names no case of"),
            },
            Method::Restate => {
                return Route::no("a restatement the record places in no line")
            }
            other => {
                return Route::no(format!(
                    "the method {} is not written in Lean yet",
                    other.as_str()
                ))
            }
        })
    }

    /// An `inspection` claim, by the case the checker found decides it
    /// (`CheckedTheorem::inspected`):
    /// - an "or" of what a term is, read against a cited range, `r ∈ {0, …,
    ///   2}`: the range's bounds, `simp only [Finset.mem_Icc] at h; omega`;
    ///   against a set listed in full: its members' equations, `simp only
    ///   [Set.mem_insert_iff, Set.mem_singleton_iff] at h; tauto`;
    /// - nothing in ∅: `Set.notMem_empty _`;
    /// - a membership of a set listed in full, or its denial, and the size
    ///   of one: `simp`, with the cited equations that give a set or a
    ///   value, and the size lemmas;
    /// - whether a number is prime: `norm_num`, with those equations.
    ///
    /// None for any other case, or where the record has none.
    pub(super) fn inspection_proof(
        &self,
        just: &Justification,
    ) -> Option<super::super::doc::Proof> {
        use super::super::doc::Proof;
        use super::super::tactics as t;
        use crate::checker::record::Inspection;
        // The cited lines that are equations, which give a set or a value.
        let equations: Vec<super::super::doc::Rule> = self
            .cited_parts(&just.refs)
            .into_iter()
            .filter(|c| c.node.notation() == crate::notations::EQUALITY)
            .map(|c| t::forwards(c.proof))
            .collect();
        Some(match self.rec.inspected.get(&just.line)? {
            Inspection::OneOf { from, range } => {
                let member =
                    self.cited_parts(std::slice::from_ref(from))
                        .into_iter()
                        .find(|c| c.node.notation() == crate::notations::MEMBERSHIP)?;
                // The set read through the cited equations that name it, then
                // a range by its bounds, worked out and taken to ℤ where
                // they are written in a wider type; a listed set by its
                // members' equations.
                let steps = match range {
                    true => {
                        let mut rules = equations;
                        rules.extend(lemma_rules(&["Finset.mem_Icc", "Set.mem_Icc"]));
                        vec![
                            t::call(
                                "norm_num",
                                vec![TacticArg::Rules(rules), t::at_h(false)],
                            ),
                            t::call("norm_cast", vec![t::at_h(false)]),
                            t::call("omega", vec![]),
                        ]
                    }
                    false => {
                        let mut rules = equations;
                        rules.extend(lemma_rules(&[
                            "Set.mem_insert_iff",
                            "Set.mem_singleton_iff",
                        ]));
                        vec![
                            t::simp_only(false, None, rules, Some(t::at_h(false))),
                            t::call("tauto", vec![]),
                        ]
                    }
                };
                Proof::By(t::on_h(&member.proof, steps))
            }
            Inspection::Empty => Proof::Term(Printed::applied(
                "Set.notMem_empty",
                super::super::doc::Source::Mathlib,
                vec![Printed::of(
                    super::super::doc::TermKind::Elided,
                    super::super::doc::LeanType::Prop,
                )],
                super::super::doc::LeanType::Prop,
            )),
            Inspection::Member => simp_call("simp", equations),
            Inspection::Size => {
                let mut rules =
                    lemma_rules(&["Set.ncard_insert_of_notMem", "Set.ncard_singleton"]);
                rules.extend(equations);
                simp_call("simp", rules)
            }
            Inspection::Prime => simp_call("norm_num", equations),
            // The set listed as Lean's finite set and counted.
            Inspection::TakenSize => Proof::By(Tactic::Seq(vec![
                t::call(
                    "rw",
                    vec![TacticArg::Rules(lemma_rules(&[
                        "Set.ncard_eq_toFinset_card'",
                    ]))],
                ),
                t::call("decide", vec![]),
            ])),
            // Member by member: each side's members' equations, and the
            // property, odd or even, by the remainder `omega` reads.
            Inspection::Taken => Proof::By(Tactic::Seq(vec![
                t::call("ext", vec![TacticArg::Term(t::hyp("x"))]),
                t::simp_only(
                    false,
                    None,
                    lemma_rules(&[
                        "Set.mem_ofPred_eq",
                        "Set.mem_insert_iff",
                        "Set.mem_singleton_iff",
                        "Int.odd_iff",
                        "Int.even_iff",
                    ]),
                    None,
                ),
                t::call("omega", vec![]),
            ])),
            Inspection::Other => return None,
        })
    }

    /// A recursion a proof lets, `let N(0) = 0, N(k + 1) = 10·N(k) + d(k +
    /// 1), for k ∈ ℕ₀`: its function, of ℤ into the type its rules compute
    /// in, obtained from `recursion_exists`, and its rules one hypothesis
    /// named by its label, as a recursion the header lets is written
    /// (`header_recursions`), which a step cites alike. A recursion of
    /// several functions, over other than ℕ₀, or whose step applies its
    /// function at other than k, is declined.
    pub(super) fn define_recursion(
        &mut self,
        d: usize,
        r: &crate::corpus::Recursion,
        depth: usize,
    ) -> Route<()> {
        use super::super::templates::Num;
        let line = self.thm.defines[d].clone();
        if r.domain.trim() != "ℕ₀" {
            return Route::no("a recursion over other than ℕ₀");
        }
        let rules = match recursion_rules(r, &line, self.rec) {
            Route::Built(rules) => rules,
            Route::Declined(why) => return Route::Declined(why),
        };
        let [rule] = rules.as_slice() else {
            return Route::no("a recursion of several functions a proof lets");
        };
        let saved = self.writer.letters.clone();
        self.writer
            .letters
            .insert(r.index.clone(), LetterType::Number(Num::Int));
        let mut to = Num::Int;
        for n in [&rule.start, &rule.step] {
            self.writer.letters.insert(
                rule.name.clone(),
                LetterType::Function { from: Num::Int, to },
            );
            match self.writer.carrier(n) {
                Route::Built(c) => to = to.max(c),
                Route::Declined(why) => {
                    self.writer.letters = saved;
                    return Route::Declined(why);
                }
            }
        }
        let ty = LetterType::Function { from: Num::Int, to };
        self.writer.letters.insert(rule.name.clone(), ty.clone());
        // The step as `recursion_exists` takes it: of k and the value at k,
        // N(k) in it a letter for that value.
        let previous = fresh_letter(&self.writer, &r.index);
        let at_index = rule
            .step
            .walk()
            .into_iter()
            .find(|n| applied_at(n, rule.name, &r.index));
        let stepped = match &at_index {
            Some(at) => super::super::expr::put_for(
                &rule.step,
                at,
                &Node::name(crate::formula::Sort::none(), &previous),
            ),
            None => rule.step.clone(),
        };
        let still_applied = stepped
            .walk()
            .iter()
            .any(|n| n.is_name() && &*n.text == rule.name.as_str());
        self.writer
            .letters
            .insert(previous.clone(), LetterType::Number(to));
        let written = (
            self.writer.number_fixed(&rule.start, to),
            self.writer.number_fixed(&rule.step, to),
            self.writer.number_fixed(&stepped, to),
        );
        self.writer.letters = saved;
        self.writer.letters.insert(rule.name.clone(), ty);
        if still_applied {
            return Route::no(
                "a recursion whose step applies its function at other than k",
            );
        }
        let (start, step, by_previous) = match written {
            (Route::Built(s), Route::Built(t), Route::Built(g)) => (s, t, g),
            (Route::Declined(why), _, _)
            | (_, Route::Declined(why), _)
            | (_, _, Route::Declined(why)) => return Route::Declined(why),
        };
        let f = super::super::names::letter(rule.name);
        let k = super::super::names::letter(&r.index);
        let v = super::super::names::letter(&previous);
        let label = line_name(&line.label);
        // ∃ f : ℤ → T, f 0 = start ∧ ∀ k : ℤ, 0 ≤ k → f (k + 1) = step.
        use super::super::doc::{LeanType, Op, Quant, TermKind};
        let int = LeanType::Num(super::super::templates::Num::Int);
        let value = LeanType::Num(to);
        let function = LeanType::Fun {
            from: Box::new(int.clone()),
            to: Box::new(value.clone()),
        };
        let k_letter = || Printed::letter(k.clone(), int.clone());
        let f_at = |at: Printed| {
            Printed::of(
                TermKind::App {
                    head: Box::new(Printed::letter(f.clone(), function.clone())),
                    args: vec![super::super::doc::Arg::Explicit(at)],
                    explicit: false,
                },
                value.clone(),
            )
        };
        let equal =
            |a: Printed, b: Printed| Printed::infix(Op::EQUALS, a, b, LeanType::Prop);
        let Some(and) = Op::of("∧") else {
            return Route::no("no ∧ among the writer's operators");
        };
        let Some(le) = Op::of("≤") else {
            return Route::no("no ≤ among the writer's operators");
        };
        let Some(plus) = Op::of("+") else {
            return Route::no("no + among the writer's operators");
        };
        let next = Printed::infix(
            plus,
            k_letter(),
            Printed::numeral("1", int.clone()),
            int.clone(),
        );
        let every = Printed::of(
            TermKind::Quantified {
                quant: Quant::ForAll,
                letter: k.clone(),
                letter_ty: int.clone(),
                guard: Some(Box::new(Printed::infix(
                    le,
                    Printed::numeral("0", int.clone()),
                    k_letter(),
                    LeanType::Prop,
                ))),
                body: Box::new(equal(f_at(next), step)),
                bounded: false,
            },
            LeanType::Prop,
        );
        let both = Printed::infix(
            and,
            equal(f_at(Printed::numeral("0", int.clone())), start),
            every,
            LeanType::Prop,
        );
        let rules = Printed::of(
            TermKind::Quantified {
                quant: Quant::Exists,
                letter: f.clone(),
                letter_ty: function,
                guard: None,
                body: Box::new(both),
                bounded: false,
            },
            LeanType::Prop,
        );
        let exists = Printed::of(
            TermKind::App {
                head: Box::new(super::super::tactics::bridge_lemma(
                    "LeanBridges.Functions.recursion_exists",
                    BridgeModule::Functions,
                )),
                args: vec![
                    super::super::doc::Arg::Explicit(Printed::of(
                        TermKind::Elided,
                        LeanType::Prop,
                    )),
                    super::super::doc::Arg::Explicit(untyped_lambda(
                        &[k.as_str(), v.as_str()],
                        by_previous,
                    )),
                ],
                explicit: false,
            },
            LeanType::Prop,
        );
        self.push_at(
            depth,
            Tactic::Obtain {
                names: vec![f, label.clone()],
                says: Some(rules),
                from: exists,
            },
            line.line,
            Spot::Statement,
        );
        self.named.insert(line.label.clone(), vec![label]);
        Route::Built(())
    }

    /// A define in a proof, `let t = 1/j, a real number`: Lean's `set`, of
    /// the type the line names, or else of the least that holds its value,
    /// whose hypothesis is the define's equation, named by its label.
    pub(super) fn define(&mut self, d: usize, depth: usize) -> Route<()> {
        self.defined.insert(d);
        let line = &self.thm.defines[d];
        let def = match crate::corpus::define_parts(&line.text) {
            Route::Built(crate::corpus::DefineParts::One(def)) => def,
            Route::Built(crate::corpus::DefineParts::Recursion(r)) => {
                return self.define_recursion(d, &r, depth)
            }
            _ => return Route::no("a define of a phrase"),
        };
        if !def.params.is_empty() {
            return self.define_function(d, &def, depth);
        }
        let bodies: Vec<&Node> = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == line.line)
            .map(|(_, node)| node)
            .collect();
        let [body] = bodies.as_slice() else {
            return Route::no(
                "a define whose value the checker did not read as one term",
            );
        };
        let body = (*body).clone();
        // A name for an element or a set, `let b = a⁻¹`: of the type its
        // value has, written as the writer writes such terms.
        let set_like = self
            .writer
            .member_kind(&body)
            .map(|m| m.letter())
            .or_else(|| self.writer.members_of(&body).map(LetterType::Set));
        if let Some(ty) = set_like.filter(|_| def.kind.is_none()) {
            let value = match self.writer.set_term(&body) {
                Route::Built(v) => v,
                Route::Declined(why) => return Route::Declined(why),
            };
            self.name_value(d, &def.name, ty, value, body, depth);
            return Route::Built(());
        }
        // A name for a map, `let p = (t ∈ [a, b] ↦ f(t))`: a function of the
        // types it takes and gives, as a define of a function on its set is
        // (`define_function`), with that set its domain where it is no
        // whole type of reals or wider.
        if let (crate::notations::MAP, [_, set, _]) =
            (body.notation(), body.children.as_slice())
        {
            if def.kind.is_some() {
                return Route::no("a define of a map said of a kind");
            }
            let (from, to) = match self.writer.function_type(&body) {
                Route::Built(t) => t,
                Route::Declined(why) => return Route::Declined(why),
            };
            let value = match self.writer.function_printed(&body) {
                Route::Built(v) => v,
                Route::Declined(why) => return Route::Declined(why),
            };
            let whole = super::super::expr::system_of(set).is_some();
            if !whole && from >= super::super::templates::Num::Real {
                match self.writer.numbers_at(set, from) {
                    Route::Built(p) => {
                        self.writer.domains.insert(def.name.clone(), p);
                    }
                    Route::Declined(why) => return Route::Declined(why),
                }
            }
            let ty = LetterType::Function { from, to };
            self.name_value(d, &def.name, ty, value, body, depth);
            return Route::Built(());
        }
        use super::super::templates::Num;
        // A positive or nonnegative whole number is a natural number named
        // from its kind's fact, whatever its value's type, as `let m ∈ ℕ`
        // names one and as the elaborator puts the name among ℕ's members
        // once the kind is shown (`GOALS.md` decision 20).
        if matches!(
            def.kind.as_deref(),
            Some("a positive integer" | "a natural number" | "a nonnegative integer")
        ) {
            return self.kinded_witness(d, &def.name, body, depth);
        }
        let ty = match def.kind.as_deref() {
            Some("a real number") => Num::Real,
            Some("a rational number") => Num::Rat,
            Some("an integer") => Num::Int,
            Some("a complex number") => Num::Complex,
            Some(other) => return Route::no(format!("a define of {other}")),
            None => match self.writer.carrier(&body) {
                Route::Built(n) => n,
                Route::Declined(why) => return Route::Declined(why),
            },
        };
        // An integer whose value is wider, `let e = p/d, an integer`: Lean's
        // ℤ division would round, so the name is the number its reason
        // shows the value to be.
        let wider = match self.writer.carrier(&body) {
            Route::Built(n) => n > ty,
            Route::Declined(why) => return Route::Declined(why),
        };
        if def.kind.is_some() && wider {
            return self.kinded_witness(d, &def.name, body, depth);
        }
        let value = match self.writer.number_fixed(&body, ty) {
            Route::Built(v) => v,
            Route::Declined(why) => return Route::Declined(why),
        };
        self.name_value(d, &def.name, LetterType::Number(ty), value, body, depth);
        // A define of a kind whose value is already of the type, `let n =
        // a·b, an integer`: the kind's fact is still a line, proved by the
        // define's reason; none where Lean's types give it, `True` of `let
        // X = A^k − 1, a real number`, as a requires line of that is none.
        if def.kind.is_some() {
            let KindShown { says, proof, .. } = match self.kind_shown(d) {
                Route::Built(s) => s,
                Route::Declined(why) => return Route::Declined(why),
            };
            if says.is_truth() {
                return Route::Built(());
            }
            let line = &self.thm.defines[d];
            let label = line_name(&line.label);
            self.push_at(
                depth,
                Tactic::Have {
                    name: format!("{label}_kind"),
                    says,
                    proof: Box::new(proof),
                },
                line.line,
                Spot::Statement,
            );
        }
        Route::Built(())
    }

    /// What closes a block, a part of one or a theorem once its steps are
    /// written, its last step being `last` and what it owes `owed`, the
    /// goal with the block's lines taken off (`Owed::written`): nothing
    /// after a step shown impossible, which closed it; the two lines a step
    /// written `contradicting N` opposes; and otherwise each part of the
    /// last step's "and" proving the part it owes, as the checker met them
    /// (`CheckedTheorem::ends_met`).
    pub(super) fn closing(&self, last: Option<usize>, owed: Owing) -> Route<Closing> {
        let Some(at) = last else {
            return Route::no("a block with no steps");
        };
        let step = &self.thm.steps[at];
        if step.impossible {
            return Route::Built(Closing::Closed);
        }
        let (owes, owed_nodes) = match owed {
            Owing::Written(Some(owed)) => {
                let mut owes = Vec::new();
                for o in owed {
                    match self.writer.formula(o) {
                        Route::Built(p) => owes.push(p),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                (owes, owed.to_vec())
            }
            Owing::Written(None) => (Vec::new(), Vec::new()),
            Owing::Lean { nodes, goal } => (goal, nodes.unwrap_or_default().to_vec()),
        };
        // Two lines that oppose close a contradiction, whose goal is False;
        // a case or a proof block whose assumption cannot hold they close by
        // `absurd`, whatever it owes.
        if let Some(c) = self.rec.contradicted.get(&step.just.line) {
            return self
                .contradiction_closed(step, c, owes.is_empty())
                .map(|t| Closing::Tactic(Box::new(Tactic::Exact(t))));
        }
        if owes.is_empty() {
            return Route::no(format!(
                "step {} ends a block that owes nothing it says, and contradicts no line",
                step.number
            ));
        }
        // How the step meets what it owes, one meeting to each part of its
        // "and", as the checker paired them.
        let Some(meetings) = self.rec.ends_met.get(&step.just.line) else {
            return Route::no(format!(
                "step {} ends its block, and the checker recorded no meeting of it with what it owes",
                step.number
            ));
        };
        let all = match self.claimed_all(step) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let named = all.iter().filter(|(_, _, says)| !says.is_truth()).count();
        let names = Self::names_of(step, named);
        let mut name_of = names.iter();
        // Each side taken apart at the page's "and", as the checker paired
        // them, not at an "and" Lean's statement alone writes.
        let mut parts = Vec::new();
        for (_, node, says) in &all {
            let proof = match says.is_truth() {
                true => None,
                false => name_of.next().map(|n| super::super::tactics::hyp(n)),
            };
            and_leaves(node, says, proof, &mut parts, &self.writer);
        }
        if owed_nodes.len() != owes.len() {
            return Route::no(format!(
                "step {} ends a block whose goal the record says in {} sentences and Lean in {}",
                step.number,
                owed_nodes.len(),
                owes.len()
            ));
        }
        let mut owed_parts = Vec::new();
        for (node, owe) in owed_nodes.iter().zip(&owes) {
            and_leaves(node, owe, None, &mut owed_parts, &self.writer);
        }
        // A sentence the checker met whole that the record writes out as an
        // "and", a phrase as its meaning, is met whole here too.
        let mut whole = false;
        if let ([(_, _, says)], [owe], [_]) =
            (all.as_slice(), owes.as_slice(), meetings.as_slice())
        {
            if parts.len() != 1 {
                parts = vec![(
                    says.clone(),
                    names.first().map(|n| super::super::tactics::hyp(n)),
                )];
                owed_parts = vec![(owe.clone(), None)];
                whole = true;
            }
        }
        if parts.len() != owed_parts.len() || parts.len() != meetings.len() {
            return Route::no(format!(
                "step {} ends its block in {} parts, and it owes {}, of which the checker met {}",
                step.number,
                parts.len(),
                owed_parts.len(),
                meetings.len()
            ));
        }
        let values = self.set_values();
        // The last step that says what is owed as written proves it by its
        // `have`, the goal's own proof.
        if let ([(_, node, says)], [owe], [met], [name]) = (
            all.as_slice(),
            owes.as_slice(),
            meetings.as_slice(),
            names.as_slice(),
        ) {
            // A statement that is no "there is" is no proof of one as it
            // stands: a count Lean asks as some natural number is made
            // below (`count_witness_made`).
            let exists = |p: &Printed| {
                matches!(
                    &p.kind,
                    super::super::doc::TermKind::Quantified {
                        quant: super::super::doc::Quant::Exists,
                        ..
                    }
                )
            };
            if met.as_written()
                && super::super::doc::forms::casts_differ(says, owe, &values).is_none()
                && exists(says) == exists(owe)
            {
                // A count the step writes in ℕ of a set a line shows finite,
                // which what is owed counts in ℕ∞, |H| of a theorem that does
                // not assume H finite, is taken across (`counts_converted`).
                let line = super::super::tactics::hyp(name);
                if let Some(converted) = self.counts_converted(line, says, owe, node) {
                    // The goal shown as the statement writes it first: a
                    // define's `set` writes its name for its value in the
                    // goal, `t '' H` for gH, which the count's rewrite does
                    // not meet.
                    let shown = super::super::tactics::call(
                        "show",
                        vec![super::super::doc::TacticArg::Term(owe.clone())],
                    );
                    return Route::Built(Closing::Tactic(Box::new(Tactic::Seq(vec![
                        shown,
                        Tactic::Exact(converted),
                    ]))));
                }
                return Route::Built(Closing::Last(name.clone()));
            }
        }
        let mut proofs = Vec::new();
        // The page's sentence each part is of, where the step's claim has one
        // for each: a count of a set the closing shows finite is of it.
        let page_parts: Vec<&Node> = match all.len() == parts.len() {
            true => all.iter().map(|(_, node, _)| node).collect(),
            false => Vec::new(),
        };
        for (i, (((says, proof), (owe, _)), met)) in
            parts.iter().zip(&owed_parts).zip(meetings).enumerate()
        {
            // A part that counts a finite set in ℤ, ending a block that owes
            // its count as some natural number (`count_witness_made`).
            let counted_set = page_parts
                .get(i)
                .and_then(|n| n.children.first())
                .filter(|c| c.notation() == CARDINALITY)
                .and_then(|c| c.children.first());
            let witness = match (proof, counted_set) {
                (Some(proof), Some(set)) if met.as_written() => {
                    self.count_witness_made(set, proof, says, owe)
                }
                _ => None,
            };
            // A count the step writes in ℕ of a set it shows finite, where
            // what is owed counts it in ℕ∞, |H| of a theorem that does not
            // assume H finite: each such count taken across
            // (`counted_across`).
            let facing = match met.turned {
                true => super::super::doc::forms::turned_statement(says),
                false => says.clone(),
            };
            let counted = match (proof, page_parts.get(i)) {
                (Some(proof), Some(node)) => {
                    let faced = match met.turned {
                        true => turned_proof(proof.clone(), says),
                        false => proof.clone(),
                    };
                    self.counts_converted(faced, &facing, owe, node)
                }
                _ => None,
            };
            let proved = match (owe.is_truth(), proof, witness.or(counted)) {
                (true, _, _) => Some(Proved::Term(trivial())),
                (false, _, Some(made)) => Some(Proved::Term(made)),
                (false, Some(proof), None) => {
                    self.met_proof(proof.clone(), says, owe, met)
                }
                (false, None, None) => None,
            };
            match proved {
                Some(p) => proofs.push(p),
                None => {
                    return Route::no(format!(
                        "step {} ends its block on {}, met with {} as {met:?}, which no one tactic takes to the other",
                        step.number,
                        says.text(),
                        owe.text()
                    ))
                }
            }
        }
        let mut assembled = Vec::new();
        match whole {
            true => assembled = proofs,
            false => {
                let mut proofs = proofs.into_iter();
                for (node, owe) in owed_nodes.iter().zip(&owes) {
                    match assembled_as(node, owe, &mut proofs, &self.writer) {
                        Some(p) => assembled.push(p),
                        None => {
                            return Route::no(
                                "an ending whose parts do not make what it owes",
                            )
                        }
                    }
                }
            }
        }
        Route::Built(Closing::Tactic(Box::new(match assembled.len() {
            1 => assembled.remove(0).closer(),
            _ => Tactic::Exact(super::super::expr::anonymous(
                assembled.into_iter().map(Proved::term).collect(),
            )),
        })))
    }

    /// Whether the claim applies a function a cited define names with its
    /// kind, at an argument that is no single letter, f(p/q) of `let f(x) =
    /// F(x), a real number`. Its equation is stated in the wider type,
    /// `↑(f x) = F ↑x`, so put in there it leaves the argument cast whole,
    /// `↑(p/q)`, which the claim writes pushed in, `↑p/↑q`.
    pub(super) fn kinded_at_compound(&self, refs: &[String], claim: &Node) -> bool {
        let members = &self.sources.checked.grammar.members;
        let names: Vec<String> = self
            .thm
            .defines
            .iter()
            .filter(|d| refs.contains(&d.label))
            .filter_map(|d| d.kinded(&self.thm.path, members).ok().flatten())
            .filter(|k| k.domain.is_some())
            .map(|k| k.name)
            .collect();
        claim.walk().iter().any(|n| {
            matches!((n.notation(), n.children.as_slice()),
                (crate::notations::APPLICATION, [f, at])
                    if f.is_name() && names.iter().any(|m| *m == *f.text) && !at.is_name())
        })
    }

    /// The sets the two count in two forms, `ncard` in one and `encard` in
    /// the other (`forms::FormDifference::Count`), as Lean writes each.
    fn counted_apart(&self, says: &Printed, wanted: &Printed) -> Vec<Printed> {
        use super::super::doc::forms::{differences, FormDifference};
        let templates = self.sources.templates;
        let widen = |head: &str, at| templates.same_function_at(head, at);
        differences(says, wanted, &widen)
            .into_iter()
            .filter_map(|d| match d {
                FormDifference::Count { line_set, .. } => Some(line_set),
                _ => None,
            })
            .collect()
    }

    /// `wanted` from `proof` of `says`, where the two count sets of `node`,
    /// the page's sentence, in two forms and are otherwise alike: each such
    /// set, shown finite, counted in ℕ (`forms_converted`). None where they
    /// count none apart, or one is not shown finite.
    pub(super) fn counts_converted(
        &self,
        proof: Printed,
        says: &Printed,
        wanted: &Printed,
        node: &Node,
    ) -> Option<Printed> {
        let apart = self.counted_apart(says, wanted);
        if apart.is_empty() {
            return None;
        }
        let mut finite = Vec::new();
        for set in self.counted_sets(&[node]) {
            let written = self.writer.set_term(&set).built()?;
            if apart.iter().any(|a| a.untyped() == written.untyped()) {
                finite.push(self.shown_finite(&set)?);
            }
        }
        if finite.len() != apart.len() {
            return None;
        }
        let conversion = super::conversions::Conversion {
            finite: &finite,
            whole: &[],
            bound: &[],
            cast_powers: false,
            identities: &[],
            numeral_to_nat: false,
        };
        Some(super::super::tactics::by_term(
            super::conversions::forms_converted(&proof, &conversion, false),
        ))
    }

    /// How `proof`, a line that says `says`, proves `wanted`, the two met as
    /// the checker recorded (`Meeting`): turned round by `.symm`, its
    /// identity elements dropped by `simpa only`, and otherwise as it is,
    /// its casts moved where the writer placed them otherwise on the two.
    /// None for parts paired out of order, which no one tactic takes.
    pub(super) fn met_proof(
        &self,
        proof: Printed,
        says: &Printed,
        wanted: &Printed,
        met: &crate::matching::Meeting,
    ) -> Option<Proved> {
        use super::super::doc::forms;
        if met.permuted {
            return None;
        }
        let (proof, says) = match met.turned {
            true => (turned_proof(proof, says), forms::turned_statement(says)),
            false => (proof, says.clone()),
        };
        // A numeral the writer takes to ℕ on one side, `2 ^ (1 : ℤ).toNat`
        // beside 2 ^ 1, is worked out as identity elements are dropped.
        let to_nat: Vec<&'static str> = match forms::written_alike(&says, wanted) {
            true => Vec::new(),
            false => forms::to_nat_rules(&says)
                .into_iter()
                .chain(forms::to_nat_rules(wanted))
                .collect(),
        };
        // A numeral's `toNat` is worked out by its simprocs (`to_nat_rules`),
        // and the cast of a numeral it leaves, ↑0 beside 0, from ℕ or from
        // ℤ, is that numeral (`casts::NUMERAL_CASTS`).
        if met.identities.is_empty() && !to_nat.is_empty() {
            use super::super::templates::Num;
            let mut rules = to_nat;
            rules.extend(
                super::super::casts::NUMERAL_CASTS
                    .iter()
                    .filter(|(from, _, _)| matches!(from, Num::Nat | Num::Int))
                    .map(|(_, _, lemma)| *lemma),
            );
            return Some(Proved::Simplified { rules, line: proof });
        }
        if !met.identities.is_empty() {
            let mut rules: Vec<&'static str> = Vec::new();
            for d in &met.identities {
                let rule = identity_lemma(d)?;
                if !rules.contains(&rule) {
                    rules.push(rule);
                }
            }
            // A 0 or 1 Lean writes cast up, `((1 : ℤ) : ℂ) * T`, is the
            // numeral before the identity is dropped (`cast_unit_lemmas`).
            let units = forms::cast_unit_lemmas(&says)
                .into_iter()
                .chain(forms::cast_unit_lemmas(wanted));
            for rule in to_nat.into_iter().chain(units) {
                if !rules.contains(&rule) {
                    rules.push(rule);
                }
            }
            return Some(Proved::Simplified { rules, line: proof });
        }
        match self.casts_apart(&says, wanted) {
            Some(apart) => cast_proved(apart, proof, &says, wanted),
            None => Some(Proved::Term(proof)),
        }
    }

    /// Keeps a line's sentences under its label. A sentence the writer
    /// states, a step's `have`, keeps what that states (`LineSentence::says`),
    /// which every later reading reads; one Lean states for it, a part an
    /// `obtain` takes from an item, is read as the writer writes its tree.
    pub(super) fn store(&mut self, label: String, said: Vec<LineSentence>) {
        self.trees.insert(label, said);
    }

    /// A line's one sentence that the writer states here as a hypothesis,
    /// a case, an induction's hypothesis, a `let`'s fact or a supposition,
    /// with what Lean is told it says, written now: later readings read it
    /// so, though the writer would write the tree otherwise by then, a
    /// count Lean took in ℕ∞, `V.encard = 2`, before its set was known
    /// finite.
    pub(super) fn stated_here(&self, node: Node, name: String) -> LineSentence {
        LineSentence {
            says: self.writer.formula(&node).built(),
            ..LineSentence::only(node, name)
        }
    }

    /// What the next `intro` takes as a hypothesis where a part's goal
    /// (`opening_goal`) is an "if" once the part's `intro`s so far are taken
    /// off it, `A` of `A → B`, as Lean states it. None where no goal is
    /// known or it is no "if" there.
    pub(super) fn assumed_here(&self) -> Option<Printed> {
        let open = self.opening_goal.as_ref()?;
        let introduced: usize = self.lines[open.from..]
            .iter()
            .filter(|l| l.depth == open.depth)
            .map(|l| match &l.tactic {
                Tactic::Intro(names) => names.len(),
                _ => 0,
            })
            .sum();
        let goal = goal_after_intros(&open.goal, introduced)?;
        match &bare_term(&goal).kind {
            super::super::doc::TermKind::Infix { op, lhs, .. } if op.symbol == "→" => {
                Some((**lhs).clone())
            }
            _ => None,
        }
    }

    /// The guard of the "for all" the next `intro` opens, `k ∈ Finset.Icc 1
    /// ↑(N + 1)` of `∀ k, k ∈ Finset.Icc 1 ↑(N + 1) → P k`, as Lean states
    /// it in the part's goal (`opening_goal`). None where no goal is known
    /// or the next binder has no guard.
    pub(super) fn next_guard(&self) -> Option<Printed> {
        let open = self.opening_goal.as_ref()?;
        let introduced: usize = self.lines[open.from..]
            .iter()
            .filter(|l| l.depth == open.depth)
            .map(|l| match &l.tactic {
                Tactic::Intro(names) => names.len(),
                _ => 0,
            })
            .sum();
        let goal = goal_after_intros(&open.goal, introduced + 1)?;
        match &bare_term(&goal).kind {
            super::super::doc::TermKind::Infix { op, lhs, .. } if op.symbol == "→" => {
                Some((**lhs).clone())
            }
            _ => None,
        }
    }

    /// What a line says in Lean: as it was stated (`store`), or, of a line
    /// not stated so, as the writer writes its tree now.
    pub(super) fn line_statement(
        &self,
        line: &super::super::algebra::Cited,
    ) -> Route<Printed> {
        match &line.says {
            Some(says) => Route::Built(says.clone()),
            None => self.writer.formula(&line.node),
        }
    }

    /// The letters the proof so far names by `set`, with their values.
    pub(super) fn set_values(&self) -> super::super::doc::forms::Values {
        self.lines
            .iter()
            .filter_map(|l| match &l.tactic {
                Tactic::Set {
                    name, value, with, ..
                } => Some((
                    name.clone(),
                    super::super::doc::forms::Value {
                        value: value.clone(),
                        equation: with.clone(),
                    },
                )),
                _ => None,
            })
            .collect()
    }

    /// What closes a block on a step written `contradicting N`: the line that
    /// says the other negated, applied to the other, `h₁ h₂`, where the goal
    /// is False, and otherwise `absurd h₂ h₁`; the other turned round where
    /// Lean writes its equation the other way.
    pub(super) fn contradiction_closed(
        &self,
        step: &Step,
        c: &Contradicted,
        to_false: bool,
    ) -> Route<Printed> {
        use super::super::doc::forms;
        let own = match self.claim(step) {
            Route::Built(said) => match said.as_slice() {
                [(_, says)] => (
                    super::super::tactics::hyp(&Self::names_of(step, 1)[0]),
                    says.clone(),
                ),
                _ => {
                    return Route::no(format!(
                        "step {} contradicts a line and claims several sentences",
                        step.number
                    ))
                }
            },
            Route::Declined(d) => return Route::Declined(d),
        };
        let other = match self.line_says(&c.at) {
            Route::Built(o) => o,
            Route::Declined(d) => return Route::Declined(d),
        };
        let ((negation, says_not), (positive, says)) = match c.negated {
            Negating::Step => (own, other),
            Negating::Line => (other, own),
        };
        let Some(denied) = forms::denied(&says_not) else {
            return Route::no(format!(
                "step {} contradicts {}, and Lean writes neither as a negation",
                step.number, c.at.line
            ));
        };
        // The one met with what the other denies as the checker met them
        // (`Contradicted::meeting`).
        let positive = match self.met_proof(positive, &says, &denied, &c.meeting) {
            Some(Proved::Term(t)) => t,
            Some(other) => other.term(),
            None => {
                return Route::no(format!(
                    "step {} contradicts {}: Lean writes the one as {} and the other denies {}, met as {:?}",
                    step.number,
                    c.at.line,
                    says.text(),
                    denied.text(),
                    c.meeting
                ))
            }
        };
        Route::Built(match to_false {
            true => applied_to(negation, positive),
            false => Printed::applied(
                "absurd",
                super::super::doc::Source::Core,
                vec![positive, negation],
                super::super::doc::LeanType::Prop,
            ),
        })
    }

    /// The fact a substitution is put into, where the checker found it in a
    /// line (`FirstAt`): the sentence or part there, or a fact the line
    /// implies, `k ≤ n` of `k ∈ {1, …, n}`, proved from it (`line_says`).
    pub(super) fn put_into_line(
        &self,
        at: &FirstAt,
    ) -> Route<super::super::algebra::Cited> {
        if at.implied.is_none() {
            return self.line_part(at);
        }
        self.line_says(at)
            .map(|(proof, says)| super::super::algebra::Cited {
                node: at.written.clone(),
                proof,
                says: Some(says),
            })
    }

    /// What stands where the checker found a fact in a line (`FirstAt`), as
    /// a term that proves it and the statement Lean writes for it: the
    /// sentence at that place, a "for all" of the line read at the block's
    /// letter the step names, `hH1 y`, or one part of either joined by
    /// "and", `hH1.2`.
    pub(super) fn line_says(&self, at: &FirstAt) -> Route<(Printed, Printed)> {
        // A membership a define says of the name it gives, `let r = m/p, a
        // natural number`, is the define's kind, kept apart from its
        // equation (`define`).
        let kind = self
            .trees
            .get(&format!("{} kind", at.line))
            .and_then(|said| said.first())
            .filter(|said| {
                matches!(
                    at.implied,
                    Some(crate::citing::Implication::SystemFact { .. })
                ) || crate::matching::alike_top(
                    &said.node,
                    &at.written,
                    self.sources.ctx,
                )
            });
        let found = match kind {
            Some(said) => said.cited(),
            None => match self.line_part(at) {
                Route::Built(f) => f,
                Route::Declined(d) => return Route::Declined(d),
            },
        };
        let Some(rule) = at.implied else {
            return self.line_statement(&found).map(|says| (found.proof, says));
        };
        let says = match self.writer.formula(&at.written) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        self.implied_proof(&found, rule, &says)
            .map(|proof| (proof, says))
    }

    /// The proof of a substitution's own equation where no line says it
    /// (`Substituted::from` None), by the source the step names: worked out
    /// by arithmetic or real arithmetic, a `have` proved as the method table
    /// says (`worked_out`, `reals`); or a define of a name, its hypothesis, turned where
    /// the step writes the name on the right. None of any other source.
    pub(super) fn equation_given(
        &self,
        just: &Justification,
    ) -> Option<(Option<Tactic>, GivenEquation)> {
        use super::super::tactics as t;
        use crate::corpus::skeleton::Source;
        let rec = self.rec.substituted.get(&just.line)?;
        if rec.from.is_some() {
            return None;
        }
        // Worked out by arithmetic, or by real arithmetic, a `have` its
        // tactic proves.
        let worked = |name: &str, real: bool| {
            let says = self.writer.formula(&rec.equation).built()?;
            let proof = match real {
                true => super::super::reals::real_arithmetic(
                    &self.writer,
                    self.sources.targets,
                    &rec.equation,
                )
                .built()?,
                false => super::super::doc::Proof::By(worked_out(&says).built()?),
            };
            let have = Tactic::Have {
                name: name.to_string(),
                says: says.clone(),
                proof: Box::new(proof),
            };
            Some((
                Some(have),
                GivenEquation {
                    change: super::super::algebra::Cited {
                        node: rec.equation.clone(),
                        proof: t::hyp(name),
                        says: Some(says),
                    },
                    above: None,
                },
            ))
        };
        match just.source.as_ref()? {
            Source::Arithmetic => worked("e_arith", false),
            Source::RealArithmetic => worked("e_real", true),
            Source::At(place) => {
                let label = place.named();
                let d = self.thm.defines.iter().find(|d| d.label == label)?;
                let Route::Built(crate::corpus::DefineParts::One(one)) =
                    crate::corpus::define_parts(&d.text)
                else {
                    return None;
                };
                // A define of a name, its equation under the define's label;
                // a function the header lets, of one argument, its equation at
                // the argument the record puts in its domain
                // (`define_domains`), `hD1 _ h`.
                let equation = match one.params.len() {
                    0 => t::hyp(self.named.get(label)?.first()?),
                    1 => {
                        let hyp = self.header_function_named(label)?;
                        let domain = self
                            .domain_proof(
                                self.rec.define_domains.get(&just.line)?,
                                None,
                            )
                            .built()?;
                        hyp_applied(&hyp, vec![elided_term(), domain])
                    }
                    _ => return None,
                };
                // Turned where the step writes it the other way round from
                // the define, as the checker found (`define_facing`).
                let proof = faced(equation, rec.define_facing?);
                Some((
                    None,
                    GivenEquation {
                        change: super::super::algebra::Cited {
                            node: rec.equation.clone(),
                            proof,
                            says: None,
                        },
                        above: None,
                    },
                ))
            }
        }
    }

    /// The rewrites that take a define by cases to the case the checker
    /// took (`define_cases`): `if_pos h` of each condition passed that
    /// holds and `if_neg h` of each that fails, h the line that says so.
    pub(super) fn conditions_put(
        &self,
        taken: &crate::checker::record::TakenCase,
        claim: &Node,
    ) -> Route<Vec<super::super::doc::Rule>> {
        use super::super::doc::forms::relation_type;
        let claim_type = match self.writer.formula(claim) {
            Route::Built(c) => relation_type(&c),
            Route::Declined(d) => return Route::Declined(d),
        };
        let mut out = Vec::new();
        for condition in &taken.passed {
            let Some(at) = &condition.said_by else {
                return Route::no("a case's condition said by no line the step cites");
            };
            let found = match self.line_part(at) {
                Route::Built(f) => f,
                Route::Declined(d) => return Route::Declined(d),
            };
            if at.implied.is_some() {
                return Route::no(
                    "a case's condition a line implies without saying it",
                );
            }
            // A line Lean states in a narrower type than the claim's is the
            // condition stated in the claim's type: cast up, `(by
            // exact_mod_cast h : …)`, or, a fact of numerals alone, `¬ (1/2 :
            // ℚ) < 1/2` beside a define over ℝ, which holds no cast to move,
            // worked out there, `(by norm_num : ¬ (1/2 : ℝ) < 1/2)`.
            let says = match self.line_statement(&found) {
                Route::Built(s) => s,
                Route::Declined(d) => return Route::Declined(d),
            };
            // A condition of things, t ∉ C, is of its own type whatever the
            // claim's, h(t) = g⁻¹(t) of another; only numbers are cast.
            let proof = match (relation_type(&says), &claim_type) {
                (
                    Some(super::super::doc::LeanType::Num(l)),
                    Some(super::super::doc::LeanType::Num(c)),
                ) if l != *c => {
                    if l > *c {
                        return Route::no(
                            "a case's condition said by a line in a wider type than the claim's",
                        );
                    }
                    let restated = match self.writer.closed_formula(&at.written, *c) {
                        Route::Built(r) => r,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    let up = match restated.lettered() {
                        false => norm_num_term(),
                        true => super::super::tactics::by_term(
                            super::super::doc::Proof::By(
                                super::super::tactics::exact_mod_cast(found.proof),
                            ),
                        ),
                    };
                    ascribed(up, restated)
                }
                _ => found.proof,
            };
            let lemma = match condition.holds {
                true => "if_pos",
                false => "if_neg",
            };
            out.push(super::super::tactics::forwards(Printed::applied(
                lemma,
                super::super::doc::Source::Core,
                vec![proof],
                super::super::doc::LeanType::Prop,
            )));
        }
        Route::Built(out)
    }
}
