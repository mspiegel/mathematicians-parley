//! Memberships, implied terms and chains.

use super::*;
use crate::corpus::Intro;
use crate::mm::spell::Binds;
use crate::notations;

impl<'a> Elaborator<'a> {
    /// The innermost part of `whole` whose membership of `system` nothing
    /// offered settles, through +, −, · and /, which make a number of
    /// numbers; `whole` itself where both its parts settle or it is built
    /// otherwise.
    pub(super) fn unsaid_part(
        &mut self,
        whole: &Term,
        system: &str,
        scope: &Rpn,
        offered: &Facts,
    ) -> Checked<Term> {
        let kids = whole.children();
        let arithmetic = whole.variable().is_none()
            && whole.label() == Some("co")
            && kids.len() == 3
            && kids[2]
                .label()
                .is_some_and(|op| rules::ARITHMETIC.contains(&op));
        if !arithmetic {
            return Ok(whole.clone());
        }
        for part in &kids[..2] {
            let want = self.to_term(&t!(self.rpn(part), system, "wcel"));
            if self.settle(&want, scope, offered, 3)?.is_declined() {
                return self.unsaid_part(part, system, scope, offered);
            }
        }
        Ok(whole.clone())
    }

    /// That a term belongs to a number system, which the text writes.
    ///
    /// Membership is a dull fact the page states rather than a step's to
    /// discover, so a term whose membership nothing supplies is a line the
    /// proof owes, and saying so is what this is for. A decline here would
    /// reach the caller as the method not covering the step, which is the
    /// one thing it does not mean.
    pub fn membership(
        &mut self,
        said: &Rpn,
        system: &str,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let want = t!(said, system, "wcel");
        let set = t!(system);
        // What the step's own lines say, first; `part` says in what order.
        if let Built(p) = self.part(said, &set, scope, facts)? {
            return Ok(p);
        }
        // A finite sum is a number because its terms are (`summed`).
        let whole = self.to_term(said);
        if whole.variable().is_none() && whole.label() == Some("csu") {
            if let Built(p) = self.summed(&whole, &set, scope, facts, None)? {
                return Ok(p);
            }
        }
        // What `part` cannot build is searched for, with the step's own
        // lines laid over the scope's copies of the same claims.
        let written = facts.filtered(|_, v| from_requires(v));
        for (k, w) in self.written.entries() {
            if let Some(lifted) = self.lifted_to(&k, &w.proof, &w.at, scope) {
                self.know(&written, k, lifted);
            }
        }
        let offered = facts.with(&written);
        match self.settle(&self.to_term(&want), scope, &offered, 3)? {
            Built(p) => Ok(p),
            Declined(_) => {
                // A quotient is a number once its divisor is not zero, and
                // that is the line a reader is owed where it is missing,
                // whatever says the quotient is a number elsewhere.
                let divisor = (whole.label() == Some("co")
                    && whole.children()[2].label() == Some("cdiv"))
                .then(|| self.rpn(&whole.children()[1]));
                if let Some(divisor) = divisor {
                    let apart = self.to_term(&t!(&divisor, "cc0", "wne"));
                    if self.settle(&apart, scope, &offered, 3)?.is_declined() {
                        return Err(self.defect(
                            self.at,
                            format!(
                                "nothing says {}, which this step needs for {}",
                                self.render(&self.rpn(&apart)),
                                self.render(said)
                            ),
                        ));
                    }
                }
                // What is named is the part nothing says is a number: 2·√a is
                // one once √a is, so it is √a the line owes.
                let missing = self.unsaid_part(&whole, system, scope, &offered)?;
                let named = self.rpn(&missing);
                // A line saying the term is real says it is complex too, and
                // a real term is what most items give: √A ∈ ℝ, never √A ∈ ℂ.
                // So an ask in ℂ names both.
                if system == "cc" {
                    return Err(self.defect(
                        self.at,
                        format!(
                            "nothing says {} ∈ ℝ or ∈ ℂ, which this step needs",
                            self.render(&named)
                        ),
                    ));
                }
                Err(self.defect(
                    self.at,
                    format!(
                        "nothing says {}, which this step needs",
                        self.render(&t!(&named, system, "wcel"))
                    ),
                ))
            }
        }
    }

    /// What a membership says of its term besides itself, as (claim, lemmas)
    /// pairs: the lemmas carry the membership to the claim one after another.
    pub fn implied_terms(&self, said: &Rpn) -> Vec<(Rpn, Vec<String>)> {
        self.implied_chains(said)
            .into_iter()
            .map(|(claim, chain)| (claim, chain.into_iter().map(|l| l.lemma).collect()))
            .collect()
    }

    /// Whether a claim has the shape of a form `rules::OTHER_FORMS` names,
    /// as the notations' targets build them: a part of a set (`wss`), a
    /// member of a power set (a `wcel` whose set is a `cpw`), a member of a
    /// set built by a rule (a `crab`, as line AB is), and collinearity (a
    /// `wo` of an equation and a membership of ℝ, as "is on line" is), each
    /// also denied. No other term is read back to the page to ask whether it
    /// says one.
    pub(super) fn other_form_shaped(node: &Term) -> bool {
        match (node.label(), node.children()) {
            (Some("wn"), [inner]) => Self::other_form_shaped(inner),
            (Some("wss"), [_, _]) => true,
            (Some("wcel"), [_, set]) => matches!(set.label(), Some("cpw" | "crab")),
            (Some("wo"), [equal, real]) => {
                equal.label() == Some("wceq")
                    && real.label() == Some("wcel")
                    && real.children().get(1).and_then(Term::label) == Some("cr")
            }
            _ => false,
        }
    }

    /// The other form of a fact the page writes in one of two forms
    /// (`rules::OTHER_FORMS`), with the lemma that carries it there: the
    /// checker's question, asked of the page's readings, so that "g is
    /// differentiable on (a, b)", whose term is a part of a set, says only
    /// itself in both tools. None for any other fact.
    pub fn other_form(&self, said: &Rpn) -> Option<Link> {
        let node = self.to_term(said);
        if !Self::other_form_shaped(&node) {
            return None;
        }
        let env = crate::sorts::Env {
            g: self.g,
            scopes: self.scopes,
        };
        // The kernel keeps no record of which notation wrote a term, and a
        // point on line AB is A, B and the point collinear in it, so the
        // fact is in one of the two forms where any of its readings is.
        let in_a_form = self
            .page_readings(&node)
            .iter()
            .any(|page| said_otherwise(page, env, &self.sorts_now).is_some());
        if !in_a_form {
            return None;
        }
        rules::OTHER_FORMS
            .iter()
            .flat_map(|family| family.forms)
            .find_map(|form| self.lemma_step(form.lemma, &node))
    }

    /// `implied_terms` with each lemma's binding and what it reaches.
    pub(super) fn implied_chains(&self, said: &Rpn) -> Vec<(Rpn, Vec<Link>)> {
        let node = self.to_term(said);
        if let Some(made) = self.other_form(said) {
            return vec![(self.rpn(&made.reached), vec![made])];
        }
        if node.variable().is_some()
            || node.label() != Some("wcel")
            || node.children().len() != 2
        {
            return Vec::new();
        }
        // A class of more than one token is no number system, and is read
        // as a range below.
        let mut system: &str =
            self.rpn(&node.children()[1]).alone().unwrap_or_default();
        let mut head: Vec<Link> = Vec::new();
        let mut bounds: Vec<(Rpn, Vec<Link>)> = Vec::new();
        if lookup(rules::WITHIN, system).is_none()
            && lookup(rules::IMPLIED, system).is_none()
        {
            // A range is no number system, and a line saying a term is in
            // one says its bounds and nothing past them (`SYNTAX.md`):
            // `mun:range-integer` is how a page says its member is whole. A
            // sum's index is in its range as the sum runs over it, and is a
            // whole number there (`elfznn0`), as a family's values are read.
            for (_page, lemma) in rules::RANGE_BOUNDS {
                if let Some(made) = self.lemma_step(lemma, &node) {
                    bounds.push((self.rpn(&made.reached), vec![made]));
                }
            }
            if self.in_family == 0 {
                return bounds;
            }
            let where_ = &node.children()[1];
            if where_.variable().is_some()
                || where_.label() != Some("co")
                || where_.children().len() != 3
                || self.rpn(&where_.children()[2]).alone() != Some("cfz")
            {
                return Vec::new();
            }
            let start = self.rpn(&where_.children()[0]);
            for row in rules::RANGE_WITHIN {
                if row.first.is_none() || row.first == start.alone() {
                    if let Some(made) = self.lemma_step(row.lemma, &node) {
                        head = vec![made];
                        system = row.system;
                        break;
                    }
                }
            }
            if head.is_empty() {
                return bounds;
            }
        }
        let mut out = bounds;
        if let Some(first) = head.first() {
            out.push((self.rpn(&first.reached), head.clone()));
        }
        let at = head
            .last()
            .map(|l| l.reached.clone())
            .unwrap_or_else(|| node.clone());
        for (_sign, big) in rules::SYSTEM_OF {
            let Some(path) =
                rules::within_path(Some(system), Some(big)).filter(|p| !p.is_empty())
            else {
                continue;
            };
            let mut chain = head.clone();
            let mut here = at.clone();
            for lemma in path {
                let made = self.lemma_step(lemma, &here).unwrap_or_else(|| {
                    panic!("{lemma} does not take {}", self.rpn(&here))
                });
                here = made.reached.clone();
                chain.push(made);
            }
            out.push((self.rpn(&here), chain));
        }
        for (_page, lemma) in rules::implied(Some(system)) {
            let made = self
                .lemma_step(lemma, &at)
                .unwrap_or_else(|| panic!("{lemma} does not take {}", self.rpn(&at)));
            let mut chain = head.clone();
            chain.push(made.clone());
            out.push((self.rpn(&made.reached), chain.clone()));
            // The page writes k ≠ 0 as a denied equation, `nnne0` as =/=.
            if made.reached.label() == Some("wne") {
                let kids = made.reached.children().to_vec();
                let denied = Term::apply("wn", vec![Term::apply("wceq", kids)]);
                chain.push(Link {
                    lemma: "neneqd".to_string(),
                    binding: None,
                    reached: denied.clone(),
                    sets: Vec::new(),
                });
                out.push((self.rpn(&denied), chain));
            }
        }
        out
    }

    /// (lemma, binding, what it concludes) for a lemma `( P -> Q )` applied
    /// to a term matching P, or None where it does not match. A lemma
    /// `( ( X e. V /\ P ) -> Q )` is applied the same way, with V read as
    /// the class of all sets and X ∈ V left for the caller to prove (`sets`):
    /// `gsspw` takes a part of B to a member of 𝒫B where B is a set.
    pub(super) fn lemma_step(&self, lemma: &str, fact: &Term) -> Option<Link> {
        let whole = self.statement(lemma);
        let premise = &whole.children()[0];
        // An antecedent `( X e. V /\ fact )` asks that X be a set, and one
        // `( P e. CC /\ fact )` that P be a complex number, as a point is:
        // the first part is settled from the facts, and the fact carried.
        let asked = (premise.variable().is_none()
            && premise.label() == Some("wa")
            && premise.children()[0].label() == Some("wcel"))
        .then(|| &premise.children()[0])
        .filter(|m| {
            let class = &m.children()[1];
            class.variable().is_some() || class.label() == Some("cc")
        });
        let carried = match asked {
            Some(_) => &premise.children()[1],
            None => premise,
        };
        let mut binding = fit(carried, fact, &Binding::new(), &names_of(&whole))?;
        let mut sets = Vec::new();
        if let Some(asked) = asked {
            if let Some(class) = asked.children()[1].variable_symbol() {
                binding.insert(class, Term::apply("cvv", Vec::new()));
            }
            sets.push(asked.substitute(&binding));
        }
        let reached = whole.children()[1].substitute(&binding);
        Some(Link {
            lemma: lemma.to_string(),
            binding: Some(binding),
            reached,
            sets,
        })
    }

    /// Each thing a membership line also says, with its proof under `scope`
    /// from the line's own `proof`. A lemma that asks a class be a set has
    /// it settled from the facts (`settle`), and where it cannot be, what
    /// that lemma would give is not said.
    pub fn implied(
        &mut self,
        said: &Rpn,
        proof: &Proof,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Facts> {
        let out = Facts::new();
        'claims: for (claim, chain) in self.implied_chains(said) {
            let mut held = proof.clone();
            let mut at = said.clone();
            for link in chain {
                let after = self.rpn(&link.reached);
                // ( scope -> ( X e. _V /\ at ) ), for a lemma asking a set.
                for set in &link.sets {
                    let Built(made) = self.settle(set, scope, facts, 3)? else {
                        continue 'claims;
                    };
                    let both = t!(self.rpn(set), at, "wa");
                    held = self.b.ap(
                        "jca",
                        &binds! {"ph" => scope, "ps" => self.rpn(set), "ch" => &at},
                        &[&made, &held],
                    );
                    at = both;
                }
                if link.lemma == "neneqd" {
                    let node = self.to_term(&at);
                    let (a, b) =
                        (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
                    held = self.b.ap(
                        "neneqd",
                        &binds! {"ph" => scope, "A" => &a, "B" => &b},
                        &[&held],
                    );
                } else {
                    let binding = link.binding.as_ref().expect("a lemma's binding");
                    let binds = self.spelt(binding);
                    let law = self.b.ap(&link.lemma, &binds, &[]);
                    held = pf!(self.b; scope, at, after, held, law, "syl");
                }
                at = after;
            }
            self.know(&out, claim, held);
        }
        Ok(out)
    }

    /// What the lines a step names, and its requires lines, say by what a
    /// membership among them implies (`rules::IMPLIED`), each proved from
    /// its line: a cited `let k ∈ ℕ` says k ≥ 1 and k ≠ 0 (`ELABORATION.md`,
    /// "A line the page cites says what it states and what a membership
    /// among its sentences implies"), which a lemma's antecedent asks as
    /// surely as what the line states.
    pub fn implied_by_named(
        &mut self,
        step: Option<&Step>,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Facts> {
        let out = Facts::new();
        let Some(step) = step else {
            return Ok(out);
        };
        let lines = self.lines.clone();
        let mut said_here: Vec<(Rpn, Proof)> = Vec::new();
        for r in &step.just.refs {
            let Some(line) = self.line_written(r, &lines) else {
                continue;
            };
            let carried = self.carried(r, facts, &lines);
            for (said, proof) in self.stated_by(r, scope, facts, &lines)? {
                let proof = match proof {
                    Some(p) => p,
                    None if said == line.claim => carried.clone(),
                    None => continue,
                };
                said_here.push((said, proof));
            }
        }
        for req in &step.requires {
            let said = self.claim_of(&req.fact)?;
            if let Some(proof) = self.held(facts, &said, scope)? {
                said_here.push((said, proof));
            }
        }
        for (said, proof) in said_here {
            let more = self.implied(&said, &proof, scope, facts)?;
            for (k, v) in more.entries() {
                self.know(&out, k, v);
            }
        }
        Ok(out)
    }

    /// What a step citing a theorem or lemma may use: what it supplies
    /// (`supplied`), the lines it cites laid over that (`with_cited`), and
    /// what they imply (`with_implied`), as `apply_lemma` reads them.
    pub fn known_implied(
        &mut self,
        step: Option<&Step>,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Facts> {
        let supplied = self.supplied(step, scope, facts)?;
        let known = self.with_cited(step, scope, &supplied, None)?;
        self.with_implied(step, scope, &known)?;
        Ok(known)
    }

    /// `known` with what the lines the step names imply laid in where it
    /// does not hold the claim already (`implied_by_named`), or holds it only
    /// from a line the step may not rest on: 1.3.2 above says V ∖ {a} ∈
    /// 𝒫(X ∖ {a}), and a step naming 1.3.1, V ∖ {a} ⊆ X ∖ {a}, rests on that.
    pub fn with_implied(
        &mut self,
        step: Option<&Step>,
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<()> {
        let implied = self.implied_by_named(step, scope, known)?;
        let before = known.copy();
        for (k, v) in implied.entries() {
            if !self.holds(&before, &k) {
                self.know(known, k, v);
            }
        }
        Ok(())
    }

    /// `said ∈ system`, carried in one lemma from a membership written: only
    /// the lemmas `rules::MEMBERSHIP` declares that take a thing in one
    /// number system to another, and only one of them.
    pub fn bridged(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        written: &Facts,
    ) -> Checked<Option<Proof>> {
        for ((source, target), label) in self.bridge_labels() {
            if system.alone() != Some(target.as_str()) {
                continue;
            }
            let claim = t!(said, source, "wcel");
            let mut proof = self.held(written, &claim, scope)?;
            if proof.is_none() {
                if let Some(w) = self.written_held(&claim)? {
                    proof = self.lifted_to(&claim, &w.proof, &w.at, scope);
                }
            }
            // What a requires line wrote, or what a line the step may rest on
            // says (`in_hand`); not what a route worked out on its way, which
            // rests on no line.
            let Some(proof) = proof else {
                continue;
            };
            if proof.origin.is_empty() {
                continue;
            }
            let push = self.sig(&label).push()[0].to_string();
            let law = self.b.ap(&label, &binds! {push => said}, &[]);
            return Ok(Some(self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &claim, "ch" => t!(said, system, "wcel")},
                &[&proof, &law],
            )));
        }
        Ok(None)
    }

    /// The sethood of each class a statement's `let` lines introduce, in the
    /// kernel's sense, which the page never says: each goes into `facts`
    /// sealed as `sethood@<label>`, and those origins are what this gives
    /// back, for `sorts`.
    pub fn sethoods(
        &mut self,
        nodes: &[Node],
        terms: &[Rpn],
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<BTreeSet<String>> {
        let mut out = BTreeSet::new();
        let hypotheses = self.thm.hypotheses.clone();
        for ((h, node), t) in hypotheses.iter().zip(nodes).zip(terms) {
            let Some(label) = h.label.clone().filter(|l| !l.is_empty()) else {
                continue;
            };
            if h.kind != Intro::Let || h.text.contains(" be a set") {
                continue;
            }
            if let Some(origin) = self.let_sethood(&label, node, t, scope, facts)? {
                out.insert(origin);
            }
        }
        Ok(out)
    }

    /// The sethood of the class one `let` line introduces (`sethoods`),
    /// put in `facts` sealed as `sethood@<label>`, an origin any step may
    /// rest on as it may on a sort line (`sorts`): held already, from the
    /// letter's membership (`elex`), or from what the letter is by its
    /// shape and what is in scope (`settle_or_bare`), a subset of a set or
    /// a group's carrier. The origin, or None where none of them gives it.
    pub fn let_sethood(
        &mut self,
        label: &str,
        node: &Node,
        t: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<String>> {
        let subject = node.leftmost().text.to_string();
        let Some(kernel) = self.names.get(&subject).cloned() else {
            return Ok(None);
        };
        let said = t!(kernel, "cvv", "wcel");
        let origin = format!("sethood@{label}");
        let membership = if node.notation() == notations::MEMBERSHIP {
            self.held(facts, t, scope)?
        } else {
            None
        };
        let made = if let Some(held) = self.held(facts, &said, scope)? {
            held
        } else if let Some(held) = membership {
            let parts = self.to_term(t);
            let (a, b) = (
                self.rpn(&parts.children()[0]),
                self.rpn(&parts.children()[1]),
            );
            let law = self.b.ap("elex", &binds! {"A" => &a, "B" => &b}, &[]);
            pf!(self.b; scope, t, said, held, law, "syl")
        } else {
            match self.settle_or_bare(&self.to_term(&said), scope, facts)? {
                Built(p) => p,
                Declined(_) => return Ok(None),
            }
        };
        let sealed = self.seal(made, &origin);
        self.know(facts, said, sealed);
        self.sorts.insert(origin.clone());
        Ok(Some(origin))
    }

    /// `term ∈ V` from the constructor at the term's head; else a decline.
    /// `SETHOOD` names the lemma, and `apply_lemma` asks what it asks — the
    /// parts' sethood — of `settle`, which comes back here for each part.
    pub fn made_a_set(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let head = &wanted.children()[0];
        let lemma = if head.variable().is_none() {
            head.label().and_then(|l| lookup(rules::SETHOOD, l))
        } else {
            None
        };
        // A digit set.mm does not say is a set in one lemma is one because
        // it is a complex number, `4cn` to `9cn`.
        let digit = head
            .label()
            .filter(|_| head.variable().is_none() && head.children().is_empty())
            .and_then(|l| rules::digit_of(l).map(|d| (l, d)));
        if let (None, Some((label, d))) = (lemma, digit) {
            let complex = self.step(&format!("{d}cn"));
            let set =
                self.b
                    .ap("elexi", &binds! {"A" => label, "B" => "cc"}, &[&complex]);
            return Ok(Built(self.b.ap(
                "a1i",
                &binds! {"ph" => t!(label, "cvv", "wcel"), "ps" => scope},
                &[&set],
            )));
        }
        let Some(lemma) = lemma else {
            return Ok(Route::no(format!(
                "no lemma makes a {} a set",
                head.label().unwrap_or("None")
            )));
        };
        self.apply_lemma(lemma, wanted, scope, facts, None, false, None)
    }

    /// A closure lemma at `vars`, from the proofs of what it asks of the
    /// parts, `asked`, each with its claim: one in deduction form takes
    /// them as its hypotheses, and one in closed form, as set.mm states
    /// ℚ's, has them as its antecedent, which `syl`, `syl2anc` or
    /// `syl3anc` discharges. `gives` is what it concludes.
    pub(super) fn closure(
        &mut self,
        lemma: &str,
        vars: &[(&str, &Rpn)],
        asked: &[(Rpn, Proof)],
        gives: &Rpn,
        scope: &Rpn,
    ) -> Proof {
        let proofs: Vec<&Proof> = asked.iter().map(|(_, p)| p).collect();
        let mut binds = Binds::new();
        for (var, term) in vars {
            binds.insert(var.to_string(), (*term).clone());
        }
        if !self.sig(lemma).essentials.is_empty() {
            binds.insert("ph".to_string(), scope.clone());
            return self.b.ap(lemma, &binds, &proofs);
        }
        let law = self.b.ap(lemma, &binds, &[]);
        let (discharge, names) = match asked.len() {
            1 => ("syl", ["ps", "ch", "", ""]),
            2 => ("syl2anc", ["ps", "ch", "th", ""]),
            _ => ("syl3anc", ["ps", "ch", "th", "ta"]),
        };
        let mut around = binds! {"ph" => scope};
        for (name, (claim, _)) in names.iter().zip(asked) {
            around.insert(name.to_string(), claim.clone());
        }
        around.insert(names[asked.len()].to_string(), gives.clone());
        let mut hyps = proofs;
        hyps.push(&law);
        self.b.ap(discharge, &around, &hyps)
    }

    /// `said ∈ system` for a compound, from its parts; else a decline.
    ///
    /// What each part is proved by is the caller's: `parts(term, system)`. A
    /// fixed table and no search, so nothing it cannot build costs more than
    /// a lookup. A quotient is built only where `nonzero(divisor)` is given
    /// to prove its divisor is not zero.
    pub fn built(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        parts: &mut Parts<'_, 'a>,
        nonzero: Option<&mut Nonzero<'_, 'a>>,
    ) -> Checked<Route<Proof>> {
        let node = self.to_term(said);
        // The tables are keyed by a number system's label; a class of more
        // than one token is in none of them.
        let system_label = system.alone().unwrap_or_default();
        if node.variable().is_none()
            && node.label() == Some("co")
            && node.children().len() == 3
        {
            let (left, right) =
                (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
            let op = self.rpn(&node.children()[2]);
            let op_label = op.alone().unwrap_or_default();
            let divided = lookup(rules::DIVIDED, system_label);
            if let (true, Some(nonzero), Some(lemma)) =
                (op_label == "cdiv", nonzero, divided)
            {
                let pa = take!(parts(self, &left, system)?);
                let pb = take!(parts(self, &right, system)?);
                let pn = take!(nonzero(self, &right)?);
                return Ok(Built(self.closure(
                    lemma,
                    &[("A", &left), ("B", &right)],
                    &[
                        (t!(left, system, "wcel"), pa),
                        (t!(right, system, "wcel"), pb),
                        (t!(right, "cc0", "wne"), pn),
                    ],
                    &t!(said, system, "wcel"),
                    scope,
                )));
            }
            // A binomial coefficient or a remainder is a whole number when
            // its parts are what `WHOLE` asks, carried to the system asked
            // by a bridge.
            if let Some(w) = rules::WHOLE.iter().find(|w| op.alone() == Some(w.op)) {
                let (left_var, left_system) = w.left;
                let (right_var, right_system) = w.right;
                let pl = take!(parts(self, &left, &t!(left_system))?);
                let pr = take!(parts(self, &right, &t!(right_system))?);
                let law = self.b.ap(
                    w.lemma,
                    &binds! {left_var => &left, right_var => &right},
                    &[],
                );
                let whole = t!(said, "cn0", "wcel");
                let made = self.b.ap(
                    "syl2anc",
                    &binds! {"ph" => scope, "ps" => t!(left, left_system, "wcel"),
                    "ch" => t!(right, right_system, "wcel"), "th" => &whole},
                    &[&pl, &pr, &law],
                );
                return self.carried_within(said, "cn0", system, made, scope);
            }
            let lemma = op
                .alone()
                .and_then(|o| system.alone().and_then(|s| rules::closed(o, s)));
            let Some(lemma) = lemma else {
                return Ok(Route::no(format!("no closure lemma for {op} in {system}")));
            };
            let pa = take!(parts(self, &left, system)?);
            let into = if op_label == "cexp" {
                t!("cn0")
            } else {
                system.clone()
            };
            let pb = take!(parts(self, &right, &into)?);
            let key = if op_label == "cexp" { "N" } else { "B" };
            return Ok(Built(self.closure(
                lemma,
                &[("A", &left), (key, &right)],
                &[
                    (t!(left, system, "wcel"), pa),
                    (t!(right, into, "wcel"), pb),
                ],
                &t!(said, system, "wcel"),
                scope,
            )));
        }
        if node.variable().is_none()
            && node.label() == Some("cneg")
            && node.children().len() == 1
        {
            let Some(lemma) = lookup(rules::NEGATED, system_label) else {
                return Ok(Route::no(format!(
                    "no closure lemma for negation in {system}"
                )));
            };
            let a = self.rpn(&node.children()[0]);
            let pa = take!(parts(self, &a, system)?);
            return Ok(Built(self.closure(
                lemma,
                &[("A", &a)],
                &[(t!(a, system, "wcel"), pa)],
                &t!(said, system, "wcel"),
                scope,
            )));
        }
        // A value by cases is in a system where the value of each case is.
        if node.variable().is_none()
            && node.label() == Some("cif")
            && node.children().len() == 3
        {
            let condition = self.rpn(&node.children()[0]);
            let (a, b) = (self.rpn(&node.children()[1]), self.rpn(&node.children()[2]));
            let pa = take!(parts(self, &a, system)?);
            let pb = take!(parts(self, &b, system)?);
            return Ok(Built(self.b.ap(
                "ifcld",
                &binds! {"ph" => scope, "ps" => &condition, "A" => &a, "B" => &b,
                "C" => system},
                &[&pa, &pb],
            )));
        }
        Ok(Route::no(NOT_BUILT))
    }

    /// A compound's membership of a number system, from its parts': there is
    /// one way to build a product from its factors, and the factors are
    /// smaller, so walking the term spends no depth. Each factor is settled
    /// in turn with the depth the whole was given.
    pub fn closed_under(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Route<Proof>> {
        let (said, system) = (
            self.rpn(&wanted.children()[0]),
            self.rpn(&wanted.children()[1]),
        );
        self.built(
            &said,
            &system,
            scope,
            &mut |me, term, system| {
                let goal = me.to_term(&t!(term, system, "wcel"));
                me.settle(&goal, scope, facts, depth)
            },
            Some(&mut |me, divisor| {
                let goal = me.to_term(&t!(divisor, "cc0", "wne"));
                me.settle(&goal, scope, facts, depth)
            }),
        )
    }

    /// ( scope -> d =/= 0 ) where the page says once that d is a positive
    /// integer (`SYNTAX.md`): d ∈ ℕ as `introduced_membership` builds it,
    /// k, k + 1, j·(j + 1) or 2^n, and so not zero (`nnne0d`). None for any
    /// other divisor.
    pub fn positive_divisor(
        &mut self,
        divisor: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let Built(member) =
            self.introduced_membership(divisor, &t!("cn"), scope, facts)?
        else {
            return Ok(None);
        };
        Ok(Some(self.b.ap(
            "nnne0d",
            &binds! {"ph" => scope, "A" => divisor},
            &[&member],
        )))
    }

    /// ( scope -> d =/= 0 ) from what the step wrote, or a decline: the
    /// divisor not being zero is the page's to say, in a requires line or a
    /// line the step cites, unless the page says it once, of a term of
    /// numerals alone whose value is not zero or of a positive integer, and
    /// is not searched for (`divisor_apart`). Inside a reason the record
    /// is read for (`reads_record`), as the checker recorded the reason's
    /// divisors (`reason_apart`).
    pub fn divisor_written(
        &mut self,
        divisor: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        match self.reads_record(&self.to_term(divisor)) {
            true => self.reason_apart(divisor, scope, facts, &OnceCell::new(), None),
            false => self.divisor_apart(divisor, scope, facts, &OnceCell::new()),
        }
    }
}
