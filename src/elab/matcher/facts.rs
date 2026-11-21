//! What is known, held and settled.

use std::mem;

use super::*;

impl<'a> Elaborator<'a> {
    /// The standard form a fact is stored and found by (`Facts`): the claim
    /// with the normalizer's rules applied, parts first, and each symmetric
    /// pair in order (`written_step`), no letter read as bound. A defined
    /// name and a map's value stay as written, since reading them depends on
    /// the step and the scope, and a fact's key must be the same wherever it
    /// is stored and wherever it is asked for. `0 ≠ k`, `k ≠ 0` and
    /// `¬ k = 0` have one key.
    pub fn fact_key(&mut self, claim: &Rpn) -> Rpn {
        if let Some(found) = self.fact_keys.get(claim) {
            return found.clone();
        }
        let kept = mem::take(&mut self.binding);
        let term = self.to_term(claim);
        let written = self.written_form(&term);
        self.binding = kept;
        let key = self.rpn(&written);
        self.fact_keys.insert(claim.clone(), key.clone());
        key
    }

    /// The term with every rule `written_step` takes applied, parts first,
    /// and every identity element dropped: an identity element goes without
    /// saying wherever it stands (`SYNTAX.md`), so x + 0 = y is found where
    /// x = y is asked, and `held` carries the one to the other.
    pub(super) fn written_form(&mut self, term: &Term) -> Term {
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        if let Some((_, turned)) = self.pair_first(term) {
            return self.written_form(&turned);
        }
        let kids: Vec<Term> = term
            .children()
            .iter()
            .map(|c| self.written_form(c))
            .collect();
        let parts = term.with_children(kids);
        if let Some(kept) = self.identity_dropped(&parts) {
            return self.written_form(&kept);
        }
        match self.written_step(&parts) {
            None => parts,
            Some((_, next)) => self.written_form(&next),
        }
    }

    /// `claim`, proved by `proof`, among `facts`.
    pub fn know(&mut self, facts: &Facts, claim: Rpn, proof: Proof) {
        let key = self.fact_key(&claim);
        facts.store(claim, key, proof);
    }

    /// `know`, where the claim is not held yet as it is spelt.
    pub fn know_default(&mut self, facts: &Facts, claim: Rpn, proof: Proof) {
        let key = self.fact_key(&claim);
        facts.store_default(claim, key, proof);
    }

    /// A proof of `wanted`, under `scope`, among `facts`: the fact with its
    /// standard form proved last, as a later proof of a claim replaces an
    /// earlier one, carried to `wanted` by the normalizer's proof that the
    /// two are one claim (`same`) where it is spelt otherwise. `0 ≠ k` is
    /// held where `k ≠ 0` was proved, and a step's own requires line saying
    /// it is the one taken over a line of the scope saying it earlier.
    /// Every route that asks whether a fact is held asks here.
    pub fn held(
        &mut self,
        facts: &Facts,
        wanted: &Rpn,
        scope: &Rpn,
    ) -> Checked<Option<Proof>> {
        let key = self.fact_key(wanted);
        let claims = facts.under(&key);
        // A claim held as it is wanted is taken as it stands, before one of
        // the same standard form spelt otherwise: an equation is held both
        // ways round (`know_turned`), and the way asked for is the one meant.
        if claims.iter().any(|c| c == wanted) {
            if let Some(proof) = facts.proof(wanted) {
                return Ok(Some(proof));
            }
        }
        let Some(stored) = claims.last() else {
            // An equation is held whichever way round it was proved: `m = |X|`
            // holds `|X| = m`. The standard form keeps the sides as written,
            // so the other way round is a fact of its own to look for.
            if let Some((turned, flip)) = self.turned_claim(wanted) {
                if !facts.under(&self.fact_key(&turned)).is_empty() {
                    if let Some(p) = self.held(facts, &turned, scope)? {
                        let Sides { left, right } = self.equation_sides(&turned);
                        return Ok(Some(pf!(self.b; scope, left, right, p, flip)));
                    }
                }
            }
            return self.held_reordered(facts, wanted, scope);
        };
        let Some(proof) = facts.proof(stored) else {
            return Ok(None);
        };
        if stored == wanted {
            return Ok(Some(proof));
        }
        // The normalizer proves under the innermost frame it may (`allowed`),
        // and the fact is held under `scope`, which may be an outer one: the
        // two are made one claim at a frame of `scope`'s own.
        let (was, now) = (self.to_term(stored), self.to_term(wanted));
        let across = self.frames_kept(|me| {
            me.frames.push(Frame {
                scope: scope.clone(),
                added: None,
                facts: Facts::new(),
            });
            me.same(&was, &now, scope, &Facts::new(), None)
        })?;
        match across {
            Built(across) => Ok(Some(
                pf!(self.b; scope, stored, wanted, proof, across, "mpbid"),
            )),
            // The two may differ by an identity element, which is filed
            // under the same form and asks the scope that what is left is a
            // number. The standard form files an equation whichever way
            // round it is written, so the one held may also be the wanted
            // turned round: `x·1 = y` is `y = x` with the element dropped
            // and the sides turned.
            Declined(_) => {
                if let Some(p) = self.tidied(&proof, stored, wanted, scope, facts)? {
                    return Ok(Some(p));
                }
                // Two holes in no order, a ≡ b (mod n) held as b ≡ a (mod n),
                // are exchanged by a lemma asking that each is a number,
                // which the facts say.
                if let Built(across) = self.same(&was, &now, scope, facts, None)? {
                    return Ok(Some(
                        pf!(self.b; scope, stored, wanted, proof, across, "mpbid"),
                    ));
                }
                let Some((turned, flip)) = self.turned_claim(wanted) else {
                    return Ok(None);
                };
                let Some(p) = self.tidied(&proof, stored, &turned, scope, facts)?
                else {
                    return Ok(None);
                };
                let Sides { left, right } = self.equation_sides(&turned);
                Ok(Some(pf!(self.b; scope, left, right, p, flip)))
            }
        }
    }

    /// A claim about three points in no order held with its points named in
    /// another order: three points form a triangle, or are collinear, in any
    /// order (`commutes any order`). Which claim `wanted` is decides the pair of
    /// lemmas that carry it (`REORDERS`).
    pub(super) fn held_reordered(
        &mut self,
        facts: &Facts,
        wanted: &Rpn,
        scope: &Rpn,
    ) -> Checked<Option<Proof>> {
        for by in &REORDERS {
            if let Some(proof) = self.held_reordered_by(facts, wanted, scope, by)? {
                return Ok(Some(proof));
            }
        }
        self.denial_reordered(facts, wanted, scope)
    }

    /// `not X` from a denial held of the same claim about the same three
    /// points named in another order, `not Y`: X implies Y by the swaps and
    /// rotations `held_reordered` makes, each lemma an implication once its
    /// points are numbers, and `mtod` turns that against `not Y`. None
    /// where `wanted` is no such denial or none is held.
    pub(super) fn denial_reordered(
        &mut self,
        facts: &Facts,
        wanted: &Rpn,
        scope: &Rpn,
    ) -> Checked<Option<Proof>> {
        let denied = self.to_term(wanted);
        if denied.label() != Some("wn") {
            return Ok(None);
        }
        let claim = self.rpn(&denied.children()[0]);
        for (said, proof) in facts.entries() {
            let said_term = self.to_term(&said);
            if said_term.label() != Some("wn") {
                continue;
            }
            let other = self.rpn(&said_term.children()[0]);
            if other == claim || !self.reorders(&claim, &other) {
                continue;
            }
            for by in &REORDERS {
                let Some(implied) =
                    self.reorder_implied(&claim, &other, scope, facts, by)?
                else {
                    continue;
                };
                return Ok(Some(self.b.ap(
                    "mtod",
                    &binds! {"ph" => scope, "ps" => &claim, "ch" => &other},
                    &[&proof, &implied],
                )));
            }
        }
        Ok(None)
    }

    /// ( scope -> ( from -> to ) ), where `to` is `from` with its three
    /// points named in another order, by as few of `by`'s swaps and
    /// rotations as reach it; None where the two are not `by`'s claim.
    pub(super) fn reorder_implied(
        &mut self,
        from: &Rpn,
        to: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        by: &Reorder,
    ) -> Checked<Option<Proof>> {
        let Some(ThreePoints {
            shape,
            letters,
            points,
        }) = self.three_points(by, &self.to_term(from))
        else {
            return Ok(None);
        };
        let named = |me: &Self, order: &[usize]| -> Rpn {
            let mut put = Binding::new();
            for (&letter, &i) in letters.iter().zip(order) {
                put.insert(letter, points[i].clone());
            }
            me.rpn(&shape.substitute(&put))
        };
        let swap = |o: &[usize]| vec![o[0], o[2], o[1]];
        let rotate = |o: &[usize]| vec![o[1], o[2], o[0]];
        let start = vec![0, 1, 2];
        let mut paths: Vec<(Vec<usize>, Vec<&str>)> = vec![(start.clone(), Vec::new())];
        let moves = loop {
            let Some((order, path)) = paths.first().cloned() else {
                return Ok(None);
            };
            paths.remove(0);
            if named(self, &order) == *to {
                break path;
            }
            if path.len() < 3 {
                for (label, next) in
                    [(by.swap, swap(&order)), (by.rotate, rotate(&order))]
                {
                    let mut longer = path.clone();
                    longer.push(label);
                    paths.push((next, longer));
                }
            }
        };
        let mut members = Vec::new();
        // A point is in ℂ by its sort, which a step rests on held.
        for point in &points {
            let member = t!(self.rpn(point), "cc", "wcel");
            let Some(proof) = self.held(facts, &member, scope)? else {
                return Ok(None);
            };
            members.push((member, proof));
        }
        let mut order = start;
        let mut chained: Option<Proof> = None;
        for label in moves {
            // The lemma's letters are the points as they stand before the
            // move, which it takes to the order after.
            let prior = order.clone();
            let before = named(self, &prior);
            order = if label == by.swap {
                swap(&order)
            } else {
                rotate(&order)
            };
            let after = named(self, &order);
            let mut put = Binding::new();
            for (&letter, &i) in letters.iter().zip(&prior) {
                put.insert(letter, points[i].clone());
            }
            let law = self.b.ap(label, &self.spelt(&put), &[]);
            // Its points are numbers, in the order its letters take them.
            let [a, b, c] =
                [&members[prior[0]], &members[prior[1]], &members[prior[2]]];
            let all = t!(a.0, b.0, c.0, "w3a");
            let numbers = self.b.ap(
                "3jca",
                &binds! {"ph" => scope, "ps" => &a.0, "ch" => &b.0, "th" => &c.0},
                &[&a.1, &b.1, &c.1],
            );
            let step = t!(before, after, "wi");
            let one = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &all, "ch" => &step},
                &[&numbers, &law],
            );
            chained = Some(match chained {
                None => one,
                Some(so_far) => self.b.ap(
                    "syld",
                    &binds! {"ph" => scope, "ps" => from, "ch" => &before, "th" => &after},
                    &[&so_far, &one],
                ),
            });
        }
        Ok(chained)
    }

    /// The claim `by` is about, read off `term`: the shape the pair's swap
    /// lemma takes, its three letters in order, and the points `term` puts
    /// at them. None where `term` is no such claim, or the pair is not in
    /// the database.
    pub(super) fn three_points(
        &mut self,
        by: &Reorder,
        term: &Term,
    ) -> Option<ThreePoints> {
        if !self.b.sigs.contains_key(by.swap) || !self.b.sigs.contains_key(by.rotate) {
            return None;
        }
        // ( the points are numbers -> ( the claim of P, Q, R -> … ) ).
        let whole = self.statement(by.swap);
        let shape = whole.children()[1].children()[0].clone();
        let mut letters: Vec<Symbol> = Vec::new();
        let mut rest = vec![shape.clone()];
        while let Some(node) = rest.pop() {
            if let Some(v) = node.variable_symbol() {
                if !letters.contains(&v) {
                    letters.push(v);
                }
                continue;
            }
            rest.extend(node.children().iter().rev().cloned());
        }
        if letters.len() != 3 {
            return None;
        }
        let at = self.fits_as(&shape, term, &names_of(&shape), None)?;
        let points = letters
            .iter()
            .map(|l| at.get(l.as_str()).cloned())
            .collect::<Option<Vec<Term>>>()?;
        Some(ThreePoints {
            shape,
            letters,
            points,
        })
    }

    /// Whether `want` is `said` with its points named in another order: a
    /// triangle or a collinearity of the same three points (`REORDERS`).
    pub fn reorders(&mut self, said: &Rpn, want: &Rpn) -> bool {
        let (said, want) = (self.to_term(said), self.to_term(want));
        for by in &REORDERS {
            let Some(one) = self.three_points(by, &said) else {
                continue;
            };
            let Some(other) = self.three_points(by, &want) else {
                continue;
            };
            if self.sorted_points(&one) == self.sorted_points(&other) {
                return true;
            }
        }
        false
    }

    /// The points of a claim about three points, spelt and sorted, so that
    /// two orders of the same three compare equal.
    pub(super) fn sorted_points(&self, claim: &ThreePoints) -> Vec<Rpn> {
        let mut spelt: Vec<Rpn> = claim.points.iter().map(|t| self.rpn(t)).collect();
        spelt.sort();
        spelt
    }

    /// `held_reordered` by one pair of lemmas: the one held is carried to
    /// the order wanted by as few swaps and rotations as reach it. None
    /// where `wanted` is not the claim the pair is about, or no order of its
    /// points is held.
    pub(super) fn held_reordered_by(
        &mut self,
        facts: &Facts,
        wanted: &Rpn,
        scope: &Rpn,
        by: &Reorder,
    ) -> Checked<Option<Proof>> {
        let Some(points) = self.three_points(by, &self.to_term(wanted)) else {
            return Ok(None);
        };
        for start in [[0, 2, 1], [1, 2, 0], [2, 0, 1], [1, 0, 2], [2, 1, 0]] {
            let said = points.named(self, &start);
            if facts.under(&self.fact_key(&said)).is_empty() {
                continue;
            }
            let Some(proof) = self.held(facts, &said, scope)? else {
                continue;
            };
            return self.moved_to(proof, &start, &points, by, scope, facts);
        }
        Ok(None)
    }

    /// `wanted`, a claim about three points as `by` reads it, from `proof`
    /// of the same claim with its points in the order `start` gives:
    /// `start[k]` is the place in `wanted` of the point it names k-th. The
    /// order comes from the record (`matching::Flip::order`), and only the
    /// moves to the order wanted are this backend's. None where `wanted` is
    /// not the claim of a notation `REORDERS` names, or `start` does not
    /// name what `proof` proves, which its caller reports.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::elab) fn reordered_from(
        &mut self,
        said: &Rpn,
        proof: Proof,
        start: &[usize],
        wanted: &Rpn,
        notation: &str,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let Some(by) = REORDERS.iter().find(|r| r.notation == notation) else {
            return Ok(None);
        };
        let Some(points) = self.three_points(by, &self.to_term(wanted)) else {
            return Ok(None);
        };
        if start.len() != 3 || points.named(self, start) != *said {
            return Ok(None);
        }
        self.moved_to(proof, start, &points, by, scope, facts)
    }

    /// From `proof` of the claim `points` reads with its points in `start`'s
    /// order, the claim in theirs, by as few swaps and rotations as reach it.
    fn moved_to(
        &mut self,
        mut proof: Proof,
        start: &[usize],
        points: &ThreePoints,
        by: &Reorder,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let (swap_label, rotate_label) = (by.swap, by.rotate);
        let swap = |o: &[usize]| vec![o[0], o[2], o[1]];
        let rotate = |o: &[usize]| vec![o[1], o[2], o[0]];
        let goal = vec![0, 1, 2];
        // The fewest moves from the order held to the order wanted.
        let mut paths: Vec<(Vec<usize>, Vec<&str>)> =
            vec![(start.to_vec(), Vec::new())];
        let moves = loop {
            let Some((order, path)) = paths.first().cloned() else {
                break None;
            };
            paths.remove(0);
            if order == goal {
                break Some(path);
            }
            if path.len() < 3 {
                for (label, next) in
                    [(swap_label, swap(&order)), (rotate_label, rotate(&order))]
                {
                    let mut longer = path.clone();
                    longer.push(label);
                    paths.push((next, longer));
                }
            }
        };
        let Some(moves) = moves else {
            return Ok(None);
        };
        let known = facts.copy();
        let mut order = start.to_vec();
        for label in moves {
            self.know(&known, points.named(self, &order), proof);
            order = if label == swap_label {
                swap(&order)
            } else {
                rotate(&order)
            };
            let next = self.to_term(&points.named(self, &order));
            let Built(made) =
                self.apply_lemma(label, &next, scope, &known, None, false, None)?
            else {
                return Ok(None);
            };
            proof = made;
        }
        Ok(Some(proof))
    }

    /// `wanted` from a fact that says it over other bound letters, under any
    /// binder and at any depth: the two are one claim, and `renaming_apart`
    /// says so, closed, by way of letters nothing holds so that no letter is
    /// caught on the way. A lemma given letters of its own (`letters_unheld`)
    /// asks its facts this way, and so does a line joined, which a `proof`
    /// block may have closed over a spare letter.
    pub fn held_rebound(
        &mut self,
        facts: &Facts,
        wanted: &Rpn,
        scope: &Rpn,
    ) -> Checked<Option<Proof>> {
        for (said, proof) in facts.entries() {
            if said == *wanted || !self.rebound(&said, wanted) {
                continue;
            }
            if let Some(across) = self.renaming_apart(&said, wanted)? {
                let turned = pf!(self.b; t!(said, wanted, "wb"), scope, across, "a1i");
                return Ok(Some(
                    pf!(self.b; scope, said, wanted, proof, turned, "mpbid"),
                ));
            }
        }
        Ok(None)
    }

    /// `claim`, proved by `proof` under `at`, among what the step's lines
    /// wrote (`Written`).
    pub fn write(&mut self, claim: Rpn, at: Rpn, proof: Proof) {
        let key = self.fact_key(&claim);
        self.written.store(claim, key, at, proof);
    }

    /// `wanted`, among what the step's lines wrote, under the scope the fact
    /// it is held by was proved under: found by standard form as `held`
    /// finds a fact.
    pub fn written_held(&mut self, wanted: &Rpn) -> Checked<Option<WrittenFact>> {
        let key = self.fact_key(wanted);
        let written = self.written.clone();
        let Some(latest) = written.facts().under(&key).last().cloned() else {
            return Ok(None);
        };
        let Some(at) = written.at(&latest).cloned() else {
            return Ok(None);
        };
        Ok(self
            .held(written.facts(), wanted, &at)?
            .map(|proof| WrittenFact { proof, at }))
    }

    /// Whether `wanted` is held among `facts` (`held`), with no proof built.
    pub fn holds(&mut self, facts: &Facts, wanted: &Rpn) -> bool {
        let key = self.fact_key(wanted);
        !facts.under(&key).is_empty()
    }

    // --- facts the text never writes ------------------------------------

    /// `wanted` from the declared lemmas, or said another way. Every lemma is
    /// tried as it is written before any is read backwards, so that a
    /// biconditional turned round never stands in for one that says what is
    /// wanted outright.
    pub(super) fn searched(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Option<Proof>> {
        for backwards in [false, true] {
            for lemma in self.declared(wanted, backwards) {
                if let Some(found) =
                    self.fits(&lemma, wanted, scope, facts, depth, backwards)?
                {
                    return Ok(Some(found));
                }
            }
        }
        self.said_otherwise(wanted, scope, facts, depth)
    }

    /// `settle`, and where that declines, the claim with its identity
    /// elements dropped settled and carried back to it (`tidied`): k·N + 0 = A
    /// from a line saying k·N = A (`SYNTAX.md`, "An identity element goes
    /// without saying").
    pub fn settle_or_bare(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        lines: Option<&Lines>,
    ) -> Checked<Route<Proof>> {
        let settled = self.settle(wanted, scope, facts, 3, step, lines)?;
        if !settled.is_declined() {
            return Ok(settled);
        }
        let (want, bare) = (self.rpn(wanted), self.without_identities(wanted));
        let bare_rpn = self.rpn(&bare);
        if bare_rpn == want {
            return Ok(settled);
        }
        let Built(p) = self.settle(&bare, scope, facts, 3, step, lines)? else {
            return Ok(settled);
        };
        Ok(match self.tidied(&p, &bare_rpn, &want, scope, facts)? {
            Some(p) => Built(p),
            None => settled,
        })
    }

    /// A proof of something a step needs and the text does not write.
    ///
    /// `depth` bounds how many declared lemmas a chain applies one on top of
    /// another, and three is the deepest chain in the corpus. That a term is
    /// a set is not searched for and spends none of it, and neither does
    /// splitting a conjunction.
    ///
    /// What is offered is only what the proof being built may rest on
    /// (`resting_on`). A step is passed only where one is there to have
    /// cited a witness, which is what lets an existential be proved at all.
    pub fn settle(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
        step: Option<&Step>,
        lines: Option<&Lines>,
    ) -> Checked<Route<Proof>> {
        // A membership the page says once. It comes before what is held, and
        // is read behind what the step may rest on (`in_hand`). A numeral's
        // is worked out below, and `numeral_within` comes back here for it.
        let numeral = wanted.label() == Some("wcel")
            && wanted.children().len() == 2
            && self
                .rpn(&wanted.children()[0])
                .tokens()
                .iter()
                .all(|t| rules::numeric(t.as_str()));
        if !numeral {
            if let Built(p) = self.said_once_proof(wanted, scope, facts)? {
                return Ok(Built(p));
            }
        }
        let rpn = self.rpn(wanted);
        if let Some(p) = self.held(facts, &rpn, scope)? {
            return Ok(Built(p));
        }
        // No label where the wanted claim is a letter, which no route below
        // that asks what it is built from reads.
        let label = wanted.label();
        let kids = wanted.children();
        // Truth, the body of a "there is" that says nothing of what it names.
        if label == Some("wtru") {
            return Ok(Built(pf!(self.b; rpn, scope, self.step("tru"), "a1i")));
        }
        // An equation whose two sides are one term but for the order of a
        // pair in no order, |AB| = |BA|, holds as x = x does: the checker
        // reads the two sides as one, and the lemma exchanging the pair
        // carries the one to the other (`same`).
        if label == Some("wceq") && kids.len() == 2 {
            let (one, other) = (kids[0].clone(), kids[1].clone());
            let (a, b) = (self.pairs_in_order(&one), self.pairs_in_order(&other));
            if self.rpn(&one) != self.rpn(&other) && self.rpn(&a) == self.rpn(&b) {
                if let Built(p) = self.same(&one, &other, scope, facts, None)? {
                    return Ok(Built(p));
                }
            }
        }
        // A map is a function on the domain it writes, said once
        // (`SYNTAX.md`, a map), where each value its rule gives is a set
        // (`mptfng`), as a define's function is (`define_on`).
        if label == Some("wfn") && kids.len() == 2 && kids[0].label() == Some("cmpt") {
            let map = &kids[0];
            let (letter, over, rule) = (
                self.rpn(&map.children()[0]),
                self.rpn(&map.children()[1]),
                self.rpn(&map.children()[2]),
            );
            if over == self.rpn(&kids[1]) {
                let every = t!(t!(rule, "cvv", "wcel"), letter, over, "wral");
                let sets = take!(self.settle(
                    &self.to_term(&every),
                    scope,
                    facts,
                    depth,
                    step,
                    lines
                )?);
                let map_rpn = self.rpn(map);
                let on = self.b.ap(
                    "mptfng",
                    &binds! {"F" => &map_rpn, "x" => &letter, "A" => &over, "B" => &rule},
                    &[&self.b.ap("eqid", &binds! {"A" => &map_rpn}, &[])],
                );
                return Ok(Built(self.b.ap(
                    "sylib",
                    &binds! {"ph" => scope, "ps" => &every, "ch" => &rpn},
                    &[&sets, &on],
                )));
            }
        }
        // A term equals itself, which no line need write.
        if label == Some("wceq")
            && kids.len() == 2
            && self.rpn(&kids[0]) == self.rpn(&kids[1])
        {
            let a = self.rpn(&kids[0]);
            return Ok(Built(self.b.ap(
                "eqidd",
                &binds! {"ph" => scope, "A" => &a},
                &[],
            )));
        }
        // A number's membership of a number system is worked out from the
        // numeral, not searched for, and spends none of the depth.
        if label == Some("wcel")
            && kids.len() == 2
            && kids[1]
                .label()
                .is_some_and(|l| lookup(rules::SYSTEMS, l).is_some())
            && self
                .rpn(&kids[0])
                .tokens()
                .iter()
                .all(|t| rules::numeric(t.as_str()))
        {
            // Inside the search that works out one number, the numbers it is
            // built from are looked up and not searched for again.
            let number = if !self.numbering.is_empty() {
                self.digit_within(wanted, scope, facts)?
            } else {
                self.numeral_within(wanted, scope, facts)?
            };
            if !number.is_declined() {
                return Ok(number);
            }
        }
        // A number spelt in numerals is prime as `inspection` decides it, a
        // closed fact a lemma at a numeral asks, as `2 ∈ Prime` is of
        // `euclemma` at 2, and not searched for.
        if label == Some("wcel")
            && kids.len() == 2
            && kids[1].label() == Some("cprime")
            && self
                .rpn(&kids[0])
                .tokens()
                .iter()
                .all(|t| rules::numeric(t.as_str()))
        {
            let decided = self.prime_decided(&kids[0], false, scope, facts)?;
            if !decided.is_declined() {
                return Ok(decided);
            }
        }
        // Whether a term is a set is read off its structure, not searched
        // for.
        if label == Some("wcel")
            && kids.len() == 2
            && self.rpn(&kids[1]).alone() == Some("cvv")
        {
            let made = self.made_a_set(wanted, scope, facts)?;
            if !made.is_declined() {
                return Ok(made);
            }
        }
        // A membership a requires line wrote in another number system is the
        // one to carry, before the lemmas below are tried in their order.
        if label == Some("wcel") && kids.len() == 2 {
            let (s, sys) = (self.rpn(&kids[0]), self.rpn(&kids[1]));
            if let Some(found) = self.bridged(&s, &sys, scope, facts)? {
                return Ok(Built(found));
            }
            // A function's value at a point of its domain, from the
            // function's type, spending none of the depth.
            if lookup(rules::SYSTEMS, sys.alone().unwrap_or_default()).is_some() {
                if let Some(found) = self.function_value(&s, &sys, scope, facts)? {
                    return Ok(Built(found));
                }
                // A finite sum is a number because its terms are, spending
                // none of the depth (`summed`).
                if kids[0].variable().is_none() && kids[0].label() == Some("csu") {
                    if let Built(found) =
                        self.summed(&kids[0], &sys, scope, facts, None)?
                    {
                        return Ok(Built(found));
                    }
                }
            } else if let Some(found) =
                self.function_value_by_map(&s, &sys, scope, facts)?
            {
                return Ok(Built(found));
            }
        }
        // A sum, difference, product, power or negation is in a number
        // system because its parts are, spending none of the depth.
        if label == Some("wcel")
            && kids.len() == 2
            && kids[1]
                .label()
                .is_some_and(|l| lookup(rules::SYSTEMS, l).is_some())
        {
            let made = self.closed_under(wanted, scope, facts, depth)?;
            if !made.is_declined() {
                return Ok(made);
            }
        }
        if label.is_some_and(|l| lookup(rules::BOUND, l).is_some()) {
            // A `define` and a `proof` block may write the same letter, and one of
            // them is renamed so that they do not collide: the same line.
            for (said, proof) in facts.entries() {
                if let Some(spelt) = self.respelt(&proof, &said, &rpn, scope)? {
                    return Ok(Built(spelt));
                }
            }
        }
        if let Some(p) = self.held_rebound(facts, &rpn, scope)? {
            return Ok(Built(p));
        }
        if depth > 0 {
            let joined = self.conjoined(wanted, scope, &mut |me, one| {
                me.settle(one, scope, facts, depth, step, lines)
            })?;
            if let Some(joined) = joined {
                return Ok(joined);
            }
            if label == Some("wrex") {
                if let Some(step) = step {
                    let lines = lines.cloned().unwrap_or_default();
                    return self.witnessed(step, wanted, scope, facts, &lines);
                }
            }
            if label == Some("wral") {
                // A side condition may be asked of every member at once. The
                // name is fixed, the condition settled of it, and the claim
                // generalised; going under the binder spends no depth.
                let (body, variable, over) =
                    (kids[0].clone(), kids[1].clone(), kids[2].clone());
                self.in_family += 1;
                let made = self.for_every(
                    scope,
                    facts,
                    &body,
                    &variable,
                    &over,
                    &mut |me, said, inner, lifted| {
                        me.settle(said, inner, lifted, depth, None, None)
                    },
                    false,
                );
                self.in_family -= 1;
                let made = made?;
                if !made.is_declined() {
                    return Ok(made);
                }
                // A line may say it whole over another letter.
                let respelt = self.fact_respelt(wanted, scope, facts)?;
                return Ok(match respelt {
                    Some(p) => Built(p),
                    None => made,
                });
            }
            if label == Some("wf") && !self.map_types_off {
                if let Some(found) = self.map_into(wanted, scope, facts, depth)? {
                    return Ok(Built(found));
                }
            }
            if let Some(found) = self.searched(wanted, scope, facts, depth)? {
                return Ok(Built(found));
            }
            let found = self.rewritten(wanted, scope, facts, depth)?;
            if !found.is_declined() {
                return Ok(found);
            }
        }
        if let Some(found) = self.instance_of_universal(&rpn, scope, facts)? {
            return Ok(Built(found));
        }
        if depth > 0 {
            if let Some(found) = self.instance_at_a_term(wanted, scope, facts, depth)? {
                return Ok(Built(found));
            }
        }
        if let Some(found) = self.held_turned_inside(&rpn, scope, facts)? {
            return Ok(Built(found));
        }
        // A map applied to a value is its rule at the value (`applied_body`):
        // what a line says of s(i) settles what a lemma asks of F(i) at F the
        // map sending n ∈ ℕ to s(n). Settled as read, and carried back.
        if depth > 0 {
            let read = self.maps_read(wanted);
            if self.rpn(&read) != rpn {
                if let Built(said) =
                    self.settle(&read, scope, facts, depth - 1, None, None)?
                {
                    if let Built(alike) =
                        self.same(&read, wanted, scope, facts, None)?
                    {
                        let was = self.rpn(&read);
                        return Ok(Built(
                            pf!(self.b; scope, was, rpn, said, alike, "mpbid"),
                        ));
                    }
                }
            }
        }
        Ok(self.no("cannot settle {}", &[&rpn]))
    }

    /// `wanted` from a fact that says it with an equation inside it written
    /// the other way round, `P ↔ b = a` for `P ↔ a = b`, as the checker reads
    /// an equation from either side wherever it stands: the two are one
    /// claim by `same`, and `mpbid` carries the fact across. Only a fact
    /// that is `wanted` once every equation in both faces one way is tried.
    pub(super) fn held_turned_inside(
        &mut self,
        wanted: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let goal = self.to_term(wanted);
        let faced = self.equations_faced(&goal);
        for (said, proof) in facts.entries() {
            if said == *wanted {
                continue;
            }
            let held = self.to_term(&said);
            if self.equations_faced(&held) != faced {
                continue;
            }
            // Each carried to its spelling without identity elements, where
            // the two differ only in which way their equations face.
            let held_bare = self.without_identities(&held);
            let goal_bare = self.without_identities(&goal);
            let (said_bare, wanted_bare) = (self.rpn(&held_bare), self.rpn(&goal_bare));
            let Some(bare) = self.tidied(&proof, &said, &said_bare, scope, facts)?
            else {
                continue;
            };
            let Built(alike) = self.same(&held_bare, &goal_bare, scope, facts, None)?
            else {
                continue;
            };
            let turned =
                pf!(self.b; scope, said_bare, wanted_bare, bare, alike, "mpbid");
            if let Some(found) =
                self.tidied(&turned, &wanted_bare, wanted, scope, facts)?
            {
                return Ok(Some(found));
            }
        }
        Ok(None)
    }

    /// `term` spelt with each equation in it facing one way, its sides in
    /// the order of their spelling, and without the identity elements it
    /// writes: two claims that differ only in which way their equations face
    /// and in an identity written or left out (`SYNTAX.md`) are spelt alike.
    pub(super) fn equations_faced(&self, term: &Term) -> Rpn {
        let term = self.without_identities(term);
        fn faced(me: &Elaborator<'_>, term: &Term) -> Term {
            let kids: Vec<Term> =
                term.children().iter().map(|k| faced(me, k)).collect();
            let Some(label) = term.label() else {
                return term.clone();
            };
            let mut kids = kids;
            if label == "wceq" && kids.len() == 2 && me.rpn(&kids[1]) < me.rpn(&kids[0])
            {
                kids.swap(0, 1);
            }
            Term::apply(label, kids)
        }
        self.rpn(&faced(self, &term))
    }
}
