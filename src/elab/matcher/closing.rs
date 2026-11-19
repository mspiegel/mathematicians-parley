//! Closing a claim by identities, order and pairs.

use std::mem;

use super::*;
use crate::targets;

impl<'a> Elaborator<'a> {
    /// Two terms that are one but for the order of a pair in no order, |AB|
    /// and |BA|, carried by the lemma exchanging it (`same`). None where they
    /// differ otherwise, and the walk goes a level in.
    pub(super) fn closed_in_no_order(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Route<Proof>>> {
        let (a, b) = (self.pairs_in_order(one), self.pairs_in_order(other));
        if self.rpn(one) == self.rpn(other) || self.rpn(&a) != self.rpn(&b) {
            return Ok(None);
        }
        match self.same(one, other, where_, held, None)? {
            Built(p) => Ok(Some(Built(p))),
            Declined(_) => Ok(None),
        }
    }

    /// Two terms that are one once their identity elements are dropped, x + 0
    /// and x, or a^(0 + 1) and a: each is carried to that one (`bared`).
    /// The walk goes a level in at a formula, and where the two are not one.
    pub(super) fn closed_identity(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Route<Proof>>> {
        if self.rpn(one) == self.rpn(other) || self.is_wff(one) {
            return Ok(None);
        }
        let bare = self.without_identities(one);
        if self.rpn(&bare) != self.rpn(&self.without_identities(other)) {
            return Ok(None);
        }
        let mut links = Vec::new();
        if self.rpn(one) != self.rpn(&bare) {
            let made = match self.bared(one, where_, held)? {
                Built(p) => p,
                declined => return Ok(Some(declined)),
            };
            links.push(ChainLink {
                from: one.clone(),
                to: bare.clone(),
                proof: made,
            });
        }
        if self.rpn(other) != self.rpn(&bare) {
            let made = match self.bared(other, where_, held)? {
                Built(p) => p,
                declined => return Ok(Some(declined)),
            };
            links.push(ChainLink {
                from: bare.clone(),
                to: other.clone(),
                proof: self.flipped(where_, other, &bare, &made),
            });
        }
        Ok(Some(Built(self.chained(where_, &links))))
    }

    /// A part of a term carried to itself with its identity elements
    /// dropped, inside `bared`, where an element stands at its head; the
    /// walk goes a level in elsewhere.
    pub(super) fn closed_bare(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Route<Proof>>> {
        if self.rpn(one) == self.rpn(other)
            || self.rpn(&self.without_identities(one)) != self.rpn(other)
            || one.variable().is_some()
        {
            return Ok(None);
        }
        let kids: Vec<Term> = one
            .children()
            .iter()
            .map(|c| self.without_identities(c))
            .collect();
        if self.identity_dropped(&one.with_children(kids)).is_none() {
            return Ok(None);
        }
        Ok(Some(self.bared(one, where_, held)?))
    }

    /// ( where_ -> term = the term with its identity elements dropped ): its
    /// parts first, then each element at its head, by the law of
    /// `rules::IDENTITY` that drops it, which asks the operand be a number.
    pub(super) fn bared(
        &mut self,
        term: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut links = Vec::new();
        let kids: Vec<Term> = term
            .children()
            .iter()
            .map(|c| self.without_identities(c))
            .collect();
        let mut cur = term.with_children(kids);
        if self.rpn(&cur) != self.rpn(term) {
            let made = take!(self.congruence(
                term,
                &cur,
                where_,
                held,
                None,
                &Leaf::Rows(vec![Row::Bare]),
            )?);
            links.push(ChainLink {
                from: term.clone(),
                to: cur.clone(),
                proof: made,
            });
        }
        while let Some(kept) = self.identity_dropped(&cur) {
            let made = take!(self.identity_law(&cur, &kept, where_, held)?);
            links.push(ChainLink {
                from: cur.clone(),
                to: kept.clone(),
                proof: made,
            });
            cur = kept;
        }
        Ok(Built(self.chained(where_, &links)))
    }

    /// ( where_ -> term = kept ), where `kept` is `term` with the identity
    /// element at its head dropped, by the law of `rules::IDENTITY` that
    /// drops it.
    pub(super) fn identity_law(
        &mut self,
        term: &Term,
        kept: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Route<Proof>> {
        // What a law asks, that the operand is a number, may be what a
        // requires line of the step says (`SYNTAX.md`), so the step's own
        // lines are offered over the scope's, as a membership is searched
        // for elsewhere.
        let written = held.filtered(|_, v| from_requires(v));
        for (k, w) in self.written.entries() {
            if let Some(lifted) = self.lifted_to(&k, &w.proof, &w.at, where_) {
                self.know(&written, k, lifted);
            }
        }
        let offered = held.with(&written);
        let goal_rpn = t!(self.rpn(term), self.rpn(kept), "wceq");
        let goal = self.to_term(&goal_rpn);
        for label in rules::IDENTITY {
            if let Built(p) =
                self.apply_lemma(label, &goal, where_, &offered, None, false, None)?
            {
                // A lemma is proved in a frame and carried to the innermost
                // one (`allowed`, `carry`); a scope inside a binder, as a
                // sum's term under its index, is that frame with more
                // added, and the proof is lifted the rest of the way.
                let innermost = self.frames.last().map(|f| f.scope.clone());
                if let Some(at) = innermost.filter(|at| at != where_) {
                    if let Some(lifted) = self.lifted_to(&goal_rpn, &p, &at, where_) {
                        return Ok(Built(lifted));
                    }
                }
                return Ok(Built(p));
            }
        }
        Ok(self.no("no identity law drops it from {}", &[&self.rpn(term)]))
    }

    /// The operand an identity element leaves, where `term` is an operation
    /// with its identity in a hole the notation record allows it: x for
    /// x + 0, 0 + x, x − 0, x·1, 1·x, x/1 and x^1. None otherwise.
    /// Whether a term is the identity element of some operation's identity
    /// law: 0 or 1 as the notation records have them.
    pub(super) fn is_identity_element(&self, term: &Term) -> bool {
        let spelt = self.rpn(term);
        self.identities
            .iter()
            .any(|law| super::super::field::numeral(law.element) == spelt)
    }

    /// A lemma's `pattern` as the checker reads it against a cited line,
    /// with its identity elements dropped (`SYNTAX.md`, "An identity element
    /// goes without saying"): a limit's |x − c| < δ at c := 0 is |x| < δ.
    /// Only a letter `binding` already puts at an identity element is put
    /// in first, since a letter of the proof may share a name with one of
    /// the lemma's.
    pub fn identities_dropped(&self, pattern: &Term, binding: &Binding) -> Term {
        let at_identity: Binding = binding
            .iter()
            .filter(|(_, v)| self.is_identity_element(v))
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        self.without_identities(&pattern.substitute(&at_identity))
    }

    pub(super) fn identity_dropped(&self, term: &Term) -> Option<Term> {
        if term.variable().is_some() {
            return None;
        }
        for law in &self.identities {
            if term.label() != Some(law.constructor.as_str())
                || term.children().len() != law.fixed.len() + 2
                || law.fixed.iter().any(|(k, token)| {
                    self.rpn(&term.children()[*k]).alone() != Some(token.as_str())
                })
            {
                continue;
            }
            let element = super::super::field::numeral(law.element);
            for &hole in &law.holes {
                let (at, other) = if hole == 0 {
                    (law.places.0, law.places.1)
                } else {
                    (law.places.1, law.places.0)
                };
                if self.rpn(&term.children()[at]) == element {
                    return Some(term.children()[other].clone());
                }
            }
        }
        None
    }

    /// Two terms an equation in hand says are equal.
    pub(super) fn closed_held(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Route<Proof>>> {
        let (a, b) = (self.rpn(one), self.rpn(other));
        if a == b {
            return Ok(None);
        }
        Ok(self.held(held, &t!(a, b, "wceq"), where_)?.map(Built))
    }

    /// The place one cited equation rewrote, carried back. The line says
    /// `was = now` or `now = was` (`flip`), and what carries the settled
    /// term back is `now = was`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn closed_cited(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
        was: &Rpn,
        now: &Rpn,
        said: &Rpn,
        flip: bool,
    ) -> Checked<Option<Route<Proof>>> {
        if self.rpn(one) != *now || self.rpn(other) != *was {
            return Ok(None);
        }
        let Some(proof) = self.held(held, said, where_)? else {
            return Ok(Some(self.no("{} is not in hand here", &[said])));
        };
        Ok(Some(Built(if flip {
            pf!(self.b; where_, was, now, proof, "eqcomd")
        } else {
            proof
        })))
    }

    /// The place a lemma's own assumed equation says the two agree: the
    /// equation is handed over as a fact rather than reproved at the leaf.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn closed_assumed(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
        was: &Rpn,
        now: &Rpn,
        under: &Rpn,
    ) -> Checked<Option<Route<Proof>>> {
        if self.rpn(one) == *was && self.rpn(other) == *now {
            Ok(self.held(held, under, where_)?.map(Built))
        } else {
            Ok(None)
        }
    }

    // --- one standard form ----------------------------------------------

    /// ( scope -> given <-> want ), or `=` for classes, where the two have
    /// one standard form; a decline where they do not.
    ///
    /// What a lemma says and what the page says may differ in how they are
    /// written and not in what they say. Each is a rule of `rules::STANDARD`
    /// or `rules::SYMMETRIC`, or a renaming, and the two are the same claim
    /// exactly when their standard forms agree up to the letters they bind.
    pub fn same(
        &mut self,
        given: &Term,
        want: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        self.same_by(given, want, scope, facts, step, vec![Row::Standard])
    }

    /// `same`, where the two may also differ by an identity element left
    /// out (`Row::Identity`): what the checker reads as one term
    /// (`Known::alike`), (∏(y ∈ Y) 1)·1 and ∏(y ∈ Y) 1.
    pub fn alike(
        &mut self,
        given: &Term,
        want: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        self.same_by(
            given,
            want,
            scope,
            facts,
            step,
            vec![Row::Standard, Row::Identity],
        )
    }

    /// `same` by the rows given.
    pub(super) fn same_by(
        &mut self,
        given: &Term,
        want: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        rows: Vec<Row>,
    ) -> Checked<Route<Proof>> {
        // The two are compared with their defined names written out, and
        // what that asks of a part is asked of it written out, so the facts
        // are read the same way.
        let read;
        let facts = if self.reading_facts || self.definitions.is_empty() {
            facts
        } else {
            read = self.read_memberships(scope, facts, step)?;
            &read
        };
        // The standard form reads a defined name as its body, so the letters
        // that body binds are bound in what is compared as well: a body's
        // letter read as a name would put an equation in a different order
        // from the same equation over the page's letter.
        let (given_read, want_read) = (self.read_out(given), self.read_out(want));
        let mut letters = self.letters_bound(&given_read);
        letters.extend(self.letters_bound(&want_read));
        let kept = mem::replace(&mut self.binding, letters);
        let out = self.congruence(given, want, scope, facts, step, &Leaf::Rows(rows));
        self.binding = kept;
        out
    }

    /// The variables a term binds: each set variable standing directly under
    /// a constructor other than `cv`, as `rebound` reads them. A set variable
    /// stands only where a binder puts it or under `cv`; a class variable
    /// under a constructor is a term the statement is about, and is bound by
    /// nothing.
    pub fn letters_bound(&self, term: &Term) -> Vars {
        let mut out = Vars::new();
        let mut rest = vec![term.clone()];
        while let Some(node) = rest.pop() {
            if node.variable().is_some() {
                continue;
            }
            if node.label() != Some("cv") {
                out.extend(
                    node.children()
                        .iter()
                        .filter_map(|c| c.variable_symbol())
                        .filter(|v| self.is_setvar(&self.float_of(v))),
                );
            }
            rest.extend(node.children().iter().cloned());
        }
        out
    }

    /// The term with each letter a binder binds moved to one nothing holds,
    /// where a class inside the binder binds that letter again: a cited
    /// theorem's `A. k e. NN0 ( ( k e. NN0 |-> B ) ` k ) ...`, its own k
    /// put where the citing proof's map for F binds k too. A theorem that
    /// keeps its two letters apart cannot be applied with both at one
    /// letter. None when no letter is left to move one to.
    pub fn unshadowed(&self, term: &Term) -> Option<Term> {
        let mut seen = vec![term.clone()];
        self.unshadowed_in(term, &mut seen)
    }

    pub(super) fn unshadowed_in(
        &self,
        node: &Term,
        seen: &mut Vec<Term>,
    ) -> Option<Term> {
        if node.variable().is_some() {
            return Some(node.clone());
        }
        let mut node = node.clone();
        for letter in self.bound_here(&node) {
            let rebinds = node.children().iter().any(|c| {
                c.variable_symbol() != Some(letter)
                    && self.letters_bound(c).contains(&letter)
            });
            if !rebinds {
                continue;
            }
            let refs: Vec<&Term> = seen.iter().collect();
            let fresh = self.unheld(&refs)?;
            seen.push(fresh.clone());
            let name = self.rpn(&Term::var(letter));
            let spare = self.rpn(&fresh);
            let kids = node
                .children()
                .iter()
                .map(|c| match c.variable_symbol() == Some(letter) {
                    true => fresh.clone(),
                    false => self.free_renamed(c, &name, &spare),
                })
                .collect();
            node = node.with_children(kids);
        }
        let kids = node
            .children()
            .iter()
            .map(|c| self.unshadowed_in(c, seen))
            .collect::<Option<Vec<_>>>()?;
        Some(node.with_children(kids))
    }

    /// The set variables a node binds itself: those standing directly under
    /// it, where it is not `cv` (`letters_bound`).
    pub(super) fn bound_here(&self, node: &Term) -> Vec<Symbol> {
        if node.variable().is_some() || node.label() == Some("cv") {
            return Vec::new();
        }
        node.children()
            .iter()
            .filter_map(|c| c.variable_symbol())
            .filter(|v| self.is_setvar(&self.float_of(v)))
            .collect()
    }

    /// What decides which of a symmetric pair goes first: the term as
    /// reverse Polish, with every letter the statement binds read as a
    /// blank.
    pub(super) fn order_key(&self, term: &Term) -> String {
        if let Some(v) = term.variable() {
            if self.binding.contains(v) {
                return "_".to_string();
            }
            return self.float_of(v);
        }
        let mut parts: Vec<String> =
            term.children().iter().map(|c| self.order_key(c)).collect();
        parts.extend(term.label().map(str::to_string));
        parts.join(" ")
    }

    /// The term with every rule applied, parts first, each pair in order.
    pub fn standard(&mut self, term: &Term) -> Term {
        let key = (self.rpn(term), self.binding.clone(), self.names_readable());
        if let Some(found) = self.standards.get(&key) {
            return found.clone();
        }
        let found = if term.variable().is_some() || term.children().is_empty() {
            term.clone()
        } else if let Some((_, turned)) = self.pair_first(term) {
            self.standard(&turned)
        } else {
            let kids: Vec<Term> =
                term.children().iter().map(|c| self.standard(c)).collect();
            let parts = term.with_children(kids);
            match self.standard_step(&parts) {
                None => parts,
                Some((_, next)) => self.standard(&next),
            }
        };
        self.standards.insert(key, found.clone());
        found
    }

    /// The term with each defined name, and each map applied to an argument,
    /// read as what it stands for (`named_body`, `applied_body`), parts
    /// first, and nothing else changed: no rule rewrites it and no pair is
    /// put in order, so its other parts are spelt as the page spelt them.
    pub fn read_out(&mut self, term: &Term) -> Term {
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        let kids: Vec<Term> =
            term.children().iter().map(|c| self.read_out(c)).collect();
        let parts = term.with_children(kids);
        let binding = self.binding.clone();
        if let Some(body) = self.named_body(&parts, &binding) {
            return self.read_out(&body);
        }
        if let Some(body) = self.applied_body(&parts) {
            return self.read_out(&body);
        }
        parts
    }

    /// One rewrite toward the standard form at the head of `term`; None
    /// where nothing rewrites the head.
    pub fn standard_step(&mut self, term: &Term) -> Option<(How, Term)> {
        if term.variable().is_some() {
            return None;
        }
        let binding = self.binding.clone();
        if let Some(body) = self.named_body(term, &binding) {
            return Some((How::Defined, body));
        }
        if let Some(body) = self.applied_body(term) {
            return Some((How::Applied, body));
        }
        self.written_step(term)
    }

    /// `standard_step` by the rules alone: a declared rule, or a symmetric
    /// pair put in order, and never a defined name or a map read as what it
    /// stands for, which depend on what the step cites and on the scope.
    pub(super) fn written_step(&mut self, term: &Term) -> Option<(How, Term)> {
        if term.variable().is_some() {
            return None;
        }
        for rule in self.rewrites(false).iter() {
            if let Some(bound) = fit(&rule.given, term, &Binding::new(), &rule.names) {
                if rule.gives.names().iter().all(|n| bound.contains_key(&**n)) {
                    return Some((
                        How::Rule(rule.label.clone()),
                        rule.gives.substitute(&bound),
                    ));
                }
            }
        }
        if term.label() == Some("wceq") && term.children().len() == 2 {
            let (a, b) = (&term.children()[0], &term.children()[1]);
            if self.order_key(b) < self.order_key(a) {
                return Some((
                    How::Eqcom,
                    Term::apply("wceq", vec![b.clone(), a.clone()]),
                ));
            }
        }
        for c in self.commutes.clone() {
            let (i, j) = c.places;
            if term.label() != Some(c.constructor.as_str())
                || term.children().len() != c.fixed.len() + 2
            {
                continue;
            }
            if c.fixed.iter().any(|(k, token)| {
                self.rpn(&term.children()[*k]).alone() != Some(token.as_str())
            }) {
                continue;
            }
            if self.order_key(&term.children()[j]) < self.order_key(&term.children()[i])
            {
                let mut kids = term.children().to_vec();
                kids.swap(i, j);
                return Some((How::Commuted, Term::apply(&c.constructor, kids)));
            }
        }
        if let Some(step) = self.pair_step(term) {
            return Some(step);
        }
        self.listing_step(term)
    }

    /// A formula's two holes in no order, put in order on the formula as
    /// written, before its parts are rewritten toward the standard form
    /// (`written_form`, `standard`, `closed_toward`): the parts of a
    /// formula's target are relations the standard form rewrites, as C ≠ A
    /// inside a betweenness becomes ¬ A = C, which would hide the pair. A
    /// term's pair, as |AB|'s, is put in order after its parts
    /// (`written_step`), so that an identity element inside it goes first:
    /// |x − 0| is |x|, not |0 − x|. None for a term, or a formula whose two
    /// are in order.
    pub(super) fn pair_first(&self, term: &Term) -> Option<(How, Term)> {
        if !self.is_wff(term) {
            return None;
        }
        self.pair_step(term)
    }

    /// `one` with its pair exchanged, where `one` and `other` are formulas
    /// of one notation whose pair in no order stands crossed between them:
    /// each one's first is the other's second, and not its first. None
    /// where they are no such formulas, or their pairs correspond as they
    /// stand, as a ≡ b (mod n) and a′ ≡ b′ (mod n) with a and a′ one term
    /// spelt two ways.
    pub(super) fn pair_crossed(
        &mut self,
        one: &Term,
        other: &Term,
    ) -> Option<(How, Term)> {
        if !self.is_wff(one) {
            return None;
        }
        let ours = self.pair_exchanged(one)?;
        let theirs = self.pair_exchanged(other)?;
        if ours.lemma != theirs.lemma {
            return None;
        }
        let in_place = self.alike_in_place(&ours.first, &theirs.first)
            && self.alike_in_place(&ours.second, &theirs.second);
        let across = self.alike_in_place(&ours.first, &theirs.second)
            && self.alike_in_place(&ours.second, &theirs.first);
        (across && !in_place).then_some((How::Exchanged(ours.lemma), ours.term))
    }

    /// `term` with two holes its notation puts in no order exchanged, where
    /// they stand out of order: b ≡ a (mod n) for a ≡ b (mod n), the
    /// target `_3 _1 _2 cmin co cdvds wbr` read with a letter of its own in
    /// each hole and fitted to the term. None where no such notation built
    /// it or its two are in order.
    pub(super) fn pair_step(&self, term: &Term) -> Option<(How, Term)> {
        let exchanged = self.pair_exchanged(term)?;
        exchanged
            .out_of_order
            .then_some((How::Exchanged(exchanged.lemma), exchanged.term))
    }

    /// `term` with the two holes its notation puts in no order exchanged,
    /// whichever order they stand in: b ≡ a (mod n) for a ≡ b (mod n). None
    /// where no such notation built it.
    pub(crate) fn pair_turned(&self, term: &Term) -> Option<Term> {
        self.pair_exchanged(term).map(|e| e.term)
    }

    /// `term` with every two holes a notation puts in no order standing in
    /// the standard order, parts first, and nothing else changed: |AB| for
    /// |BA|. A method that reads a term's atoms by how they are spelt reads
    /// a distance written either way round as one atom so. The letters the
    /// term binds are read as blanks, as `same` reads them, so that the order
    /// is the one `same` carries the term to.
    pub(crate) fn pairs_in_order(&mut self, term: &Term) -> Term {
        let letters = self.letters_bound(term);
        let kept = mem::replace(&mut self.binding, letters);
        let out = self.pairs_put_in_order(term);
        self.binding = kept;
        out
    }

    /// `pairs_in_order` under the binding already set.
    pub(super) fn pairs_put_in_order(&self, term: &Term) -> Term {
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        let kids: Vec<Term> = term
            .children()
            .iter()
            .map(|c| self.pairs_put_in_order(c))
            .collect();
        let parts = term.with_children(kids);
        match self.pair_step(&parts) {
            Some((_, turned)) => turned,
            None => parts,
        }
    }

    /// `term` with its two holes no order is put on exchanged, the lemma
    /// that does it, and whether they stood out of order.
    pub(super) fn pair_exchanged(&self, term: &Term) -> Option<PairExchanged> {
        const LETTERS: [&str; 6] = ["A", "B", "C", "D", "E", "F"];
        for p in &self.pairs_in_any_order {
            let head = p.target.split_whitespace().last();
            if term.label() != head || p.count > LETTERS.len() {
                continue;
            }
            let holes: Vec<Rpn> = LETTERS[..p.count]
                .iter()
                .map(|l| Rpn::from(vec![Symbol::of(&format!("c{l}"))]))
                .collect();
            let pattern = self.to_term(&targets::fill(&p.target, &holes));
            let Some(bound) = fit(&pattern, term, &Binding::new(), &names_of(&pattern))
            else {
                continue;
            };
            let (i, j) = (
                Symbol::of(LETTERS[p.holes.0 - 1]),
                Symbol::of(LETTERS[p.holes.1 - 1]),
            );
            let (Some(a), Some(b)) = (bound.get(&i), bound.get(&j)) else {
                continue;
            };
            let out_of_order = self.order_key(b) < self.order_key(a);
            let mut swapped = bound.clone();
            swapped.insert(i, b.clone());
            swapped.insert(j, a.clone());
            return Some(PairExchanged {
                lemma: p.lemma,
                term: pattern.substitute(&swapped),
                out_of_order,
                first: a.clone(),
                second: b.clone(),
            });
        }
        None
    }

    /// Two elements of a listed set of three or more, next to each other
    /// and out of order, exchanged at the head of `term`; None where the
    /// head is no listing or its elements there are in order. The page
    /// lists a set's elements in no order (`commutes any order`), so a
    /// listing's standard form is its elements in order, as a symmetric
    /// pair's is. The parts are put in order first (`written_form`,
    /// `standard`), so at the head only the last element is out of place,
    /// and each exchange moves it one place toward the front.
    ///
    /// A listing of four or more is a triple joined with a singleton of
    /// each further element, ( ( {a, b, c} ∪ {d} ) ∪ {e} ), and only a
    /// union of that shape is read as one: a union the page writes of
    /// another set is left as it is.
    pub(super) fn listing_step(&self, term: &Term) -> Option<(How, Term)> {
        match term.label() {
            Some("ctp") if term.children().len() == 3 => {
                let kids = term.children();
                let (places, lemma) =
                    if self.order_key(&kids[1]) < self.order_key(&kids[0]) {
                        ((0, 1), rules::LISTED.triple_first)
                    } else if self.order_key(&kids[2]) < self.order_key(&kids[1]) {
                        ((1, 2), rules::LISTED.triple_last)
                    } else {
                        return None;
                    };
                let mut kids = kids.to_vec();
                kids.swap(places.0, places.1);
                Some((How::Listed(lemma), Term::apply("ctp", kids)))
            }
            Some("cun") if term.children().len() == 2 => {
                let (before, added) = (&term.children()[0], &term.children()[1]);
                let element = singleton_element(added)?;
                let ListingEnd { rest, last } = listing_end(before)?;
                if self.order_key(element) >= self.order_key(&last) {
                    return None;
                }
                let (how, before) = match rest {
                    ListingRest::Triple(first, second) => (
                        rules::LISTED.into_triple,
                        Term::apply("ctp", vec![first, second, element.clone()]),
                    ),
                    ListingRest::Union(inner) => (
                        rules::LISTED.singletons,
                        Term::apply("cun", vec![inner, added.clone()]),
                    ),
                };
                let moved = Term::apply("csn", vec![last.clone()]);
                Some((How::Listed(how), Term::apply("cun", vec![before, moved])))
            }
            _ => None,
        }
    }

    /// What a name a `define` introduced names, where `term` is that name
    /// standing free and the proof being built may rest on the define; else
    /// None. A letter the compared statements bind is never a defined name.
    ///
    /// A step that uses what a define says cites it (`SYNTAX.md`), so a name
    /// whose define the step does not cite stays a name: x₁ ∈ S, cited from
    /// the define of S and a line saying x₁ ∈ [a, b], reads S as its set and
    /// x₁ as written.
    pub fn named_body(&self, term: &Term, bound: &Vars) -> Option<Term> {
        if term.variable().is_some()
            || term.label() != Some("cv")
            || term.children().len() != 1
        {
            return None;
        }
        if term.children()[0]
            .variable()
            .is_some_and(|v| bound.contains(v))
        {
            return None;
        }
        let var = self.rpn(&term.children()[0]);
        let var = var.alone().unwrap_or_default();
        if !self.may_read(var) {
            return None;
        }
        let body = self.definitions.get(var)?;
        Some(self.to_term(body))
    }

    /// Whether the proof being built may read the defined name `var` as what
    /// it names: whether it may rest on the name's define.
    pub(super) fn may_read(&self, var: &str) -> bool {
        let label = self.defined_by.get(var);
        if label.is_some_and(|l| self.kept_named.contains(l)) {
            return false;
        }
        match (&self.resting, label) {
            (Some(allowed), Some(label)) => allowed.contains(label),
            _ => true,
        }
    }

    /// The defined names the proof being built may read, as a key.
    pub(super) fn names_readable(&self) -> String {
        let readable: Vec<&str> = self
            .definitions
            .keys()
            .filter(|v| self.may_read(v))
            .map(String::as_str)
            .collect();
        readable.join(" ")
    }

    /// What a map applied to a value comes to: the map's rule with the value
    /// for the name it binds; else None.
    ///
    /// A letter the rule binds is kept apart from every letter the value
    /// spells, bound there or not; where they meet, the rule is read in its
    /// other spelling (`rule_apart`).
    pub(crate) fn applied_body(&mut self, term: &Term) -> Option<Term> {
        if term.label() == Some("co") {
            return self.applied_body_of_two(term);
        }
        let f = self.applied_map(term)?;
        let at = term.children()[0].clone();
        let (bound, rule) = (f.children()[0].clone(), f.children()[2].clone());
        let mut spelt: BTreeSet<String> = self
            .rpn(&at)
            .tokens()
            .iter()
            .map(|t| t.to_string())
            .collect();
        let through = self.read_through(&at, true, None);
        spelt.extend(self.rpn(&through).tokens().iter().map(|t| t.to_string()));
        let own = bound.variable()?.to_string();
        let meets = |me: &Self, one: &Term| {
            me.letters_bound(one)
                .iter()
                .filter(|v| ***v != *own)
                .any(|v| {
                    let label = me.float_of(v);
                    spelt.contains(&label) && me.is_setvar(&label)
                })
        };
        let mut rule = rule;
        if meets(self, &rule) {
            let other = self.rule_apart(&f);
            if !meets(self, &other) {
                rule = other;
            }
        }
        let was = t!(self.rpn(&bound), "cv");
        Some(self.restated(&rule, &was, &self.rpn(&at)))
    }

    /// `term` with each map applied to a value read as its rule at the value
    /// (`applied_body`), parts first, and nothing else changed.
    pub(crate) fn maps_read(&mut self, term: &Term) -> Term {
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        let kids: Vec<Term> =
            term.children().iter().map(|c| self.maps_read(c)).collect();
        let parts = term.with_children(kids);
        match self.applied_body(&parts) {
            Some(body) => self.maps_read(&body),
            None => parts,
        }
    }

    /// The map of two arguments an application `( A F B )` applies, written
    /// as a map or as the name a define gave it; else None.
    pub(super) fn applied_map_of_two(&self, term: &Term) -> Option<Term> {
        if term.variable().is_some()
            || term.label() != Some("co")
            || term.children().len() != 3
        {
            return None;
        }
        let mut f = term.children()[2].clone();
        if let Some(named) = self.named_body(&f, &self.binding) {
            f = named;
        }
        if f.variable().is_some()
            || f.label() != Some("cmpo")
            || f.children().len() != 5
        {
            return None;
        }
        Some(f)
    }

    /// What a map of two arguments applied to two values comes to: its rule
    /// with the first value for its first letter and the second for its
    /// second; else None, and None where a value spells a letter the rule
    /// binds, which would be captured.
    pub(super) fn applied_body_of_two(&mut self, term: &Term) -> Option<Term> {
        let f = self.applied_map_of_two(term)?;
        let (first, second) = (term.children()[0].clone(), term.children()[1].clone());
        let kids = f.children();
        let (x, y, rule) = (kids[0].clone(), kids[1].clone(), kids[4].clone());
        let spelt: BTreeSet<String> = [&first, &second]
            .iter()
            .flat_map(|v| {
                self.rpn(v)
                    .tokens()
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
            })
            .collect();
        let bound: Vec<String> = self
            .letters_bound(&rule)
            .iter()
            .map(|v| self.float_of(v))
            .chain([self.rpn(&x).to_string(), self.rpn(&y).to_string()])
            .collect();
        if bound.iter().any(|v| spelt.contains(v)) {
            return None;
        }
        let at_first = self.restated(&rule, &t!(self.rpn(&x), "cv"), &self.rpn(&first));
        Some(self.restated(&at_first, &t!(self.rpn(&y), "cv"), &self.rpn(&second)))
    }

    /// ( where -> ( A F B ) = S ), S the rule of F's map of two at A and B:
    /// `ovmpoga` at the map as written, and the define's equation carries it
    /// to the name (`oveqd`). A decline where A or B is not shown to be in
    /// its domain.
    pub(super) fn applied_proof_of_two(
        &mut self,
        cur: &Term,
        nxt: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Route<Proof>> {
        let kids = cur.children();
        let (a, b, written) =
            (self.rpn(&kids[0]), self.rpn(&kids[1]), self.rpn(&kids[2]));
        let map = self.applied_map_of_two(cur).expect("an applied map of two");
        let m = map.children();
        let (x, y, c, d, r) = (
            self.rpn(&m[0]),
            self.rpn(&m[1]),
            self.rpn(&m[2]),
            self.rpn(&m[3]),
            self.rpn(&m[4]),
        );
        let s = self.rpn(nxt);
        // The rule moves one letter at a time, the first to A and then the
        // second to B, and `sylan9eq` joins the two moves.
        let (x_is, y_is) = (t!(x, "cv", a, "wceq"), t!(y, "cv", b, "wceq"));
        let halfway = self.rpn(&self.restated(&m[4], &t!(x, "cv"), &a));
        let first = self.to_term(&t!(x_is, t!(r, halfway, "wceq"), "wi"));
        let first =
            take!(self.prove_essential(&first, &Rpn::default(), &Facts::new())?);
        let second = self.to_term(&t!(y_is, t!(halfway, s, "wceq"), "wi"));
        let second =
            take!(self.prove_essential(&second, &Rpn::default(), &Facts::new())?);
        let instance = self.b.ap(
            "sylan9eq",
            &binds! {"ph" => &x_is, "ps" => &y_is, "A" => &r, "B" => &halfway, "C" => &s},
            &[&first, &second],
        );
        let mut members = Vec::new();
        for want in [t!(a, c, "wcel"), t!(b, d, "wcel"), t!(s, "cvv", "wcel")] {
            members.push(take!(self.settle(
                &self.to_term(&want),
                where_,
                held,
                3,
                None,
                None
            )?));
        }
        let mapped = self.rpn(&map);
        let closed = self.b.ap(
            "ovmpoga",
            &binds! {"x" => &x, "y" => &y, "A" => &a, "B" => &b, "C" => &c, "D" => &d,
            "R" => &r, "S" => &s, "F" => &mapped, "H" => "cvv"},
            &[&instance, &pf!(self.b; mapped, "eqid")],
        );
        let three = self.b.ap(
            "3jca",
            &binds! {"ph" => where_, "ps" => t!(a, c, "wcel"), "ch" => t!(b, d, "wcel"),
            "th" => t!(s, "cvv", "wcel")},
            &[&members[0], &members[1], &members[2]],
        );
        let value = t!(t!(a, b, mapped, "co"), s, "wceq");
        let direct = pf!(self.b; where_,
            t!(t!(a, c, "wcel"), t!(b, d, "wcel"), t!(s, "cvv", "wcel"), "w3a"),
            value, three, closed, "syl");
        if written == mapped {
            return Ok(Built(direct));
        }
        // A defined name is carried to its map first.
        let Some(named) = self.held(held, &t!(written, mapped, "wceq"), where_)? else {
            return Ok(Route::no("the equation a define holds is not in hand"));
        };
        let via = self.b.ap(
            "oveqd",
            &binds! {"ph" => where_, "A" => &written, "B" => &mapped, "C" => &a, "D" => &b},
            &[&named],
        );
        Ok(Built(self.b.ap(
            "eqtrd",
            &binds! {"ph" => where_, "A" => t!(a, b, written, "co"), "B" => t!(a, b, mapped, "co"), "C" => &s},
            &[&via, &direct],
        )))
    }
}
