//! Writing, congruences and values within a domain.

use super::*;

impl<'a> Elaborator<'a> {
    /// Run `f` with what the step's requires lines made offered to the
    /// membership lookup and the one-lemma bridge, which read these before
    /// any search, and which a search never does. `keep` lays these over
    /// what is already offered rather than in its place.
    pub fn writing<T>(
        &mut self,
        scope: &Rpn,
        known: &Facts,
        keep: bool,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let kept = self.written.clone();
        if !keep {
            self.written = Written::new();
        }
        for (k, v) in known.entries() {
            if from_requires(&v) {
                self.write(k, scope.clone(), v);
            }
        }
        let out = f(self);
        self.written = kept;
        out
    }

    /// `said ∈ system` searched for, at the depth the caller gives.
    pub fn within(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Route<Proof>> {
        let wanted = self.to_term(&t!(said, system, "wcel"));
        self.settle(&wanted, scope, facts, depth, None, None)
    }

    /// ( scope -> given = want ), or `<->` for statements, where the walk
    /// would go under a binder whose letter the scope spells: the lemma that
    /// carries a change under a binder keeps its letter apart from the
    /// scope. Each side's letter at `place` is moved to one nothing holds,
    /// closed (`renaming` for a statement, `class_alpha` for a class), the
    /// two are walked there, and the result is moved back.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn over_spare_letter(
        &mut self,
        given: &Term,
        want: &Term,
        place: usize,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        leaf: &Leaf,
    ) -> Checked<Route<Proof>> {
        // Looked at, not taken: the letter stands inside this one statement
        // and nowhere else.
        let Some(fresh) = self.unheld(&[&self.to_term(scope), given, want]) else {
            return Ok(Route::no("no letter left to walk under this binder by"));
        };
        let moved_to = |term: &Term| moved_letter(term, place, &fresh);
        let (Some(moved), Some(moved_want)) = (moved_to(given), moved_to(want)) else {
            return Ok(Route::no("the binder binds no letter to walk under it by"));
        };
        // The new letter is bound where the old one was, and a standard form
        // reads a bound letter as a blank (`order_key`): the walk puts a
        // pair in the order it would have under the old letter.
        let added = fresh.variable_symbol().filter(|_| {
            [given, want].iter().any(|t| {
                t.children()[place]
                    .variable_symbol()
                    .is_some_and(|v| self.binding.contains(&v))
            })
        });
        let fresh_bound = added.is_some_and(|v| self.binding.insert(v));
        let walked = self.congruence(&moved, &moved_want, scope, facts, step, leaf);
        if let (true, Some(v)) = (fresh_bound, added) {
            self.binding.remove(&v);
        }
        let walked = take!(walked?);
        let wff = self.is_wff(given);
        let (there, back) = if wff {
            (
                self.renaming(given, &moved)?,
                self.renaming(&moved_want, want)?,
            )
        } else {
            (
                self.class_alpha(given, &moved)?,
                self.class_alpha(&moved_want, want)?,
            )
        };
        let (Some(there), Some(back)) = (there, back) else {
            return Ok(Route::no("the binder is not renamed apart from the scope"));
        };
        let join = if wff { "wb" } else { "wceq" };
        let (a, b) = (self.rpn(given), self.rpn(&moved));
        let (c, d) = (self.rpn(&moved_want), self.rpn(want));
        let first = pf!(self.b; t!(a, b, join), scope, there, "a1i");
        let last = pf!(self.b; t!(c, d, join), scope, back, "a1i");
        Ok(Built(self.chained(
            scope,
            &[
                ChainLink {
                    from: given.clone(),
                    to: moved.clone(),
                    proof: first,
                },
                ChainLink {
                    from: moved,
                    to: moved_want.clone(),
                    proof: walked,
                },
                ChainLink {
                    from: moved_want,
                    to: want.clone(),
                    proof: last,
                },
            ],
        )))
    }

    /// Carry one change up to the whole term it sits in.
    ///
    /// Two terms that differ in one place are walked in step, and the lemma
    /// that lifts each level is the one the tree names. What counts as the
    /// change, and what proves it there, is the caller's `leaf`. What it
    /// refuses is a route declining and not a defect, however it was
    /// reached.
    pub fn congruence(
        &mut self,
        given: &Term,
        want: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        leaf: &Leaf,
    ) -> Checked<Route<Proof>> {
        if let Some(found) = self.leaf(leaf, given, want, scope, facts)? {
            return Ok(found);
        }
        if given.label() != want.label()
            || given.children().len() != want.children().len()
        {
            return Ok(self.no(
                "{} and {} differ by more than the change being carried",
                &[&self.rpn(given), &self.rpn(want)],
            ));
        }
        let Some(label) = given.label().map(str::to_string) else {
            return Ok(
                self.no("{} is a letter, and carries nothing", &[&self.rpn(given)])
            );
        };
        let g: Vec<Rpn> = given.children().iter().map(|c| self.rpn(c)).collect();
        let w: Vec<Rpn> = want.children().iter().map(|c| self.rpn(c)).collect();
        // Only the body is carried under the binder here, with the letter's
        // membership of the domain in hand: a defined name in the body read
        // at the letter is its rule only inside the define's domain. A
        // domain that changes with the body kept is the branch for domains
        // below.
        let under_member = match label.as_str() {
            "wrex" => Some("rexbidva"),
            "wral" => Some("ralbidva"),
            _ => None,
        };
        if let Some(lemma) = under_member.filter(|_| w[1..] == g[1..]) {
            let kids = given.children();
            let (body, name, runs) = (&kids[0], g[1].clone(), g[2].clone());
            // The lemma keeps its letter apart from the scope it carries.
            if name.alone().is_some_and(|n| scope.has(n)) {
                return self
                    .over_spare_letter(given, want, 1, scope, facts, step, leaf);
            }
            let member = t!(name, "cv", runs, "wcel");
            let other = want.children()[0].clone();
            let made = self.frames_kept(|me| {
                let (inner, lifted) = me.widen(scope, facts, &member, None);
                me.congruence(body, &other, &inner, &lifted, step, leaf)
            })?;
            let made = take!(made);
            return Ok(Built(
                pf!(self.b; scope, self.rpn(body), self.rpn(&other), name, runs, made, lemma),
            ));
        }
        // A sum's summand, or a product's factor, is carried the same way,
        // under its index's range.
        let indexed = lookup(rules::INDEXED_BODY, &label);
        if let Some((body_lemma, _)) =
            indexed.filter(|_| g[0] == w[0] && g[2] == w[2] && g[1] != w[1])
        {
            let kids = given.children();
            let (runs, body, name) = (g[0].clone(), &kids[1], g[2].clone());
            if name.alone().is_some_and(|n| scope.has(n)) {
                return self
                    .over_spare_letter(given, want, 2, scope, facts, step, leaf);
            }
            let member = t!(name, "cv", runs, "wcel");
            let other = want.children()[1].clone();
            let made = self.frames_kept(|me| {
                let (inner, lifted) = me.widen(scope, facts, &member, None);
                me.congruence(body, &other, &inner, &lifted, step, leaf)
            })?;
            let made = take!(made);
            return Ok(Built(self.b.ap(
                body_lemma,
                &binds! {"ph" => scope, "A" => &runs, "B" => self.rpn(body), "C" => self.rpn(&other), "k" => &name},
                &[&made],
            )));
        }
        // A sum whose range and summand both change, as Σ(k = 0 to m) C(m, k)
        // read at m := n: the range carried as it stands, and the summand
        // under the index's membership of the range it had (`sumeq12dv`).
        if let Some((_, both_lemma)) =
            indexed.filter(|_| g[2] == w[2] && g[0] != w[0] && g[1] != w[1])
        {
            let kids = given.children();
            let (runs, body, name) = (g[0].clone(), &kids[1], g[2].clone());
            if name.alone().is_some_and(|n| scope.has(n)) {
                return self
                    .over_spare_letter(given, want, 2, scope, facts, step, leaf);
            }
            let moved = take!(self.congruence(
                &kids[0],
                &want.children()[0],
                scope,
                facts,
                step,
                leaf
            )?);
            let member = t!(name, "cv", runs, "wcel");
            let other = want.children()[1].clone();
            let made = self.frames_kept(|me| {
                let (inner, lifted) = me.widen(scope, facts, &member, None);
                me.congruence(body, &other, &inner, &lifted, step, leaf)
            })?;
            let made = take!(made);
            return Ok(Built(self.b.ap(
                both_lemma,
                &binds! {"ph" => scope, "A" => &runs, "B" => &w[0], "C" => self.rpn(body),
                "D" => self.rpn(&other), "k" => &name},
                &[&moved, &made],
            )));
        }
        // An integral's integrand is carried under its letter's membership
        // of [a, b], the integral running forward (`gditgeq3d`): the
        // integral sees its integrand only between its ends, and a define
        // read at the letter is its rule only inside its domain.
        if label == "cdit" && g[..3] == w[..3] && g[3] != w[3] {
            let kids = given.children();
            let (name, low, high, body) =
                (g[0].clone(), g[1].clone(), g[2].clone(), &kids[3]);
            if name.alone().is_some_and(|n| scope.has(n)) {
                return self
                    .over_spare_letter(given, want, 0, scope, facts, step, leaf);
            }
            let forward = t!(low, high, "cle", "wbr");
            let ordered = match self.held(facts, &forward, scope)? {
                Some(p) => p,
                None => take!(self.prove_numeral(&forward, scope, facts)?),
            };
            let member = t!(name, "cv", t!(low, high, "cicc", "co"), "wcel");
            let other = want.children()[3].clone();
            let made = self.frames_kept(|me| {
                let (inner, lifted) = me.widen(scope, facts, &member, None);
                me.congruence(body, &other, &inner, &lifted, step, leaf)
            })?;
            let made = take!(made);
            return Ok(Built(self.b.ap(
                "gditgeq3d",
                &binds! {"ph" => scope, "A" => &low, "B" => &high, "S" => self.rpn(body),
                "T" => self.rpn(&other), "x" => &name},
                &[&ordered, &made],
            )));
        }
        // A set-builder's condition is carried the same way, under its
        // letter's membership of the domain.
        if label == "crab" && g[1] == w[1] && g[2] == w[2] && g[0] != w[0] {
            let kids = given.children();
            let (body, name, runs) = (&kids[0], g[1].clone(), g[2].clone());
            if name.alone().is_some_and(|n| scope.has(n)) {
                // The scope holds D's own equation, which binds this letter,
                // so the condition is carried over a spare the scope does not
                // spell and the builder renamed to it and back.
                return self
                    .over_spare_letter(given, want, 1, scope, facts, step, leaf);
            }
            let member = t!(name, "cv", runs, "wcel");
            let other = want.children()[0].clone();
            let made = self.frames_kept(|me| {
                let (inner, lifted) = me.widen(scope, facts, &member, None);
                me.congruence(body, &other, &inner, &lifted, step, leaf)
            })?;
            let made = take!(made);
            return Ok(Built(self.b.ap(
                "rabbidva",
                &binds! {"ph" => scope, "ps" => self.rpn(body), "ch" => self.rpn(&other), "x" => &name, "A" => &runs},
                &[&made],
            )));
        }
        // A map's rule is carried the same way, under its letter's
        // membership of the domain (`mpteq2dva`): a map applied inside a
        // map, (n ∈ ℕ ↦ x(n)) at x the map sending j ∈ ℕ to s(j), is read
        // as s(n) only where n is in ℕ.
        if label == "cmpt" && g[0] == w[0] && g[1] == w[1] && g[2] != w[2] {
            let kids = given.children();
            let (name, runs, body) = (g[0].clone(), g[1].clone(), &kids[2]);
            if name.alone().is_some_and(|n| scope.has(n)) {
                return self
                    .over_spare_letter(given, want, 0, scope, facts, step, leaf);
            }
            let member = t!(name, "cv", runs, "wcel");
            let other = want.children()[2].clone();
            let made = self.frames_kept(|me| {
                let (inner, lifted) = me.widen(scope, facts, &member, None);
                me.congruence(body, &other, &inner, &lifted, step, leaf)
            })?;
            let made = take!(made);
            return Ok(Built(self.b.ap(
                "mpteq2dva",
                &binds! {"ph" => scope, "x" => &name, "A" => &runs, "B" => self.rpn(body), "C" => self.rpn(&other)},
                &[&made],
            )));
        }
        // A "for all", a "there is" or a set-builder whose domain changes,
        // its letter and its body kept.
        if (label == "wral" || label == "wrex" || label == "crab")
            && g[0] == w[0]
            && g[1] == w[1]
            && g[2] != w[2]
        {
            // The lemma keeps its letter apart from both domains, which may
            // spell it bound inside, as a defined set read as its rule does.
            if g[1]
                .alone()
                .is_some_and(|n| scope.has(n) || g[2].has(n) || w[2].has(n))
            {
                return self
                    .over_spare_letter(given, want, 1, scope, facts, step, leaf);
            }
            let kids = given.children().to_vec();
            let moved = take!(self.congruence(
                &kids[2],
                &want.children()[2],
                scope,
                facts,
                step,
                leaf
            )?);
            let lemma =
                rules::congruence(&label, &[2]).expect("a congruence for a domain");
            return Ok(Built(self.b.ap(
                lemma,
                &binds! {"ph" => scope, "ps" => &g[0], "x" => &g[1], "A" => &g[2], "B" => &w[2]},
                &[&moved],
            )));
        }
        // And its domain and body together, as a set-builder's change
        // together where a define's argument stands in both.
        if (label == "wral" || label == "wrex" || label == "crab")
            && g[1] == w[1]
            && g[0] != w[0]
            && g[2] != w[2]
        {
            let kids = given.children().to_vec();
            if g[1]
                .alone()
                .is_some_and(|n| scope.has(n) || g[2].has(n) || w[2].has(n))
            {
                return self
                    .over_spare_letter(given, want, 1, scope, facts, step, leaf);
            }
            let over = take!(self.congruence(
                &kids[2],
                &want.children()[2],
                scope,
                facts,
                step,
                leaf
            )?);
            let said = take!(self.congruence(
                &kids[0],
                &want.children()[0],
                scope,
                facts,
                step,
                leaf
            )?);
            let lemma = rules::congruence(&label, &[0, 2])
                .expect("a congruence for a domain and a body");
            return Ok(Built(self.b.ap(
                lemma,
                &binds! {"ph" => scope, "ps" => &g[0], "ch" => &w[0], "x" => &g[1], "A" => &g[2], "B" => &w[2]},
                &[&over, &said],
            )));
        }
        // A map whose domain changes, its letter and its rule kept.
        if (label == "cmpt" || label == "ciun")
            && g[0] == w[0]
            && g[2] == w[2]
            && g[1] != w[1]
        {
            let kids = given.children().to_vec();
            let moved = take!(self.congruence(
                &kids[1],
                &want.children()[1],
                scope,
                facts,
                step,
                leaf
            )?);
            if let Some(wider) = self.domain_holding(given, want, scope, &moved) {
                return Ok(Built(wider));
            }
            let lemma = rules::congruence(&label, &[1])
                .expect("a congruence for a map's domain");
            return Ok(Built(self.b.ap(
                lemma,
                &binds! {"ph" => scope, "x" => &g[0], "A" => &g[1], "B" => &w[1], "C" => &g[2]},
                &[&moved],
            )));
        }
        // The operation or relation a term wraps stays as it is; a function
        // applied changes where a lemma says it may, as q(x) is r(x) when q
        // is r (`fveq1d`).
        let wrapped = rules::WRAPS.contains(&label.as_str())
            && (g[g.len() - 1] == w[w.len() - 1]
                || rules::congruence(&label, &[g.len() - 1]).is_none());
        let n = if wrapped { g.len() - 1 } else { g.len() };
        let kids: Vec<Term> = given.children()[..n].to_vec();
        let wants: Vec<Term> = want.children()[..n].to_vec();
        let (spelt, other) = (&g[..n], &w[..n]);
        let slots: Vec<usize> = (0..n).filter(|&i| spelt[i] != other[i]).collect();
        if slots.is_empty() {
            return Ok(Route::no("nothing changed under this term"));
        }
        // A rule by cases changes in its condition and its two values at
        // once, and `ifbieq12d` takes both old values before the new ones,
        // so it is given its parts by name; a part that stays the same is
        // carried by `biidd` or `eqidd`.
        if label == "cif" {
            let mut parts = Vec::new();
            for i in 0..3 {
                let one = if slots.contains(&i) {
                    take!(
                        self.congruence(&kids[i], &wants[i], scope, facts, step, leaf)?
                    )
                } else if i == 0 {
                    self.b
                        .ap("biidd", &binds! {"ph" => scope, "ps" => &spelt[0]}, &[])
                } else {
                    self.b
                        .ap("eqidd", &binds! {"ph" => scope, "A" => &spelt[i]}, &[])
                };
                parts.push(one);
            }
            return Ok(Built(self.b.ap(
                "ifbieq12d",
                &binds! {"ph" => scope, "ps" => &spelt[0], "ch" => &other[0], "A" => &spelt[1],
                "B" => &spelt[2], "C" => &other[1], "D" => &other[2]},
                &[&parts[0], &parts[1], &parts[2]],
            )));
        }
        // A function spelt as its define's name against the map it names:
        // `feq1d`, and `f1oeq1d` for one-to-one and onto, both deduction
        // forms (`rules::CONGRUENCE`), and for one-to-one or onto alone the
        // closed `f1eq1` or `foeq1` after the equation by `syl`
        // (`rules::FUNCTION_LAWS`). A function's type whose domain or codomain
        // changes, the function too or not: `feq123d` and `f1eq123d` take
        // the three equations, a part that stays the same carried by
        // `eqidd`.
        if matches!(label.as_str(), "wf" | "wf1") && slots != [2] {
            let mut equal = Vec::new();
            for i in [2, 0, 1] {
                let one = if slots.contains(&i) {
                    take!(
                        self.congruence(&kids[i], &wants[i], scope, facts, step, leaf)?
                    )
                } else {
                    self.b
                        .ap("eqidd", &binds! {"ph" => scope, "A" => &spelt[i]}, &[])
                };
                equal.push(one);
            }
            let lemma = if label == "wf" { "feq123d" } else { "f1eq123d" };
            return Ok(Built(self.b.ap(
                lemma,
                &binds! {"ph" => scope, "A" => &spelt[0], "B" => &other[0],
                "C" => &spelt[1], "D" => &other[1], "F" => &spelt[2], "G" => &other[2]},
                &[&equal[0], &equal[1], &equal[2]],
            )));
        }
        let typed = matches!(label.as_str(), "wf" | "wf1" | "wfo" | "wf1o");
        let deduced = rules::congruence(&label, &slots).filter(|_| typed);
        let closed = rules::function_law(&label, &slots);
        if deduced.is_some() || closed.is_some() {
            let moved =
                take!(self.congruence(&kids[2], &wants[2], scope, facts, step, leaf)?);
            let parts = binds! {"A" => &spelt[0], "B" => &spelt[1], "F" => &spelt[2], "G" => &other[2]};
            if let Some(lemma) = deduced {
                let mut all = parts.clone();
                all.insert("ph".to_string(), scope.clone());
                return Ok(Built(self.b.ap(lemma, &all, &[&moved])));
            }
            let law = self.b.ap(closed.expect("one of the two"), &parts, &[]);
            return Ok(Built(self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => t!(spelt[2], other[2], "wceq"),
                "ch" => t!(self.rpn(given), self.rpn(want), "wb")},
                &[&moved, &law],
            )));
        }
        // What lifts the change is the lemma for this constructor and these
        // places, and the operation it lifts under must be the same one.
        let lifting = rules::congruence(&label, &slots);
        let Some(lifting) =
            lifting.filter(|_| !(wrapped && g[g.len() - 1] != w[w.len() - 1]))
        else {
            return Ok(Route::no("no lemma carries this change up"));
        };
        // The lemmas that carry a change under a binder keep its letter
        // apart from the scope.
        if lookup(rules::BOUND, &label).is_some()
            && g.len() >= 2
            && g[1].alone().is_some_and(|n| scope.has(n))
        {
            return self.over_spare_letter(given, want, 1, scope, facts, step, leaf);
        }
        let mut under = Vec::new();
        for &i in &slots {
            under.push(self.congruence(&kids[i], &wants[i], scope, facts, step, leaf)?);
        }
        let mut proofs = Vec::new();
        for one in under {
            match one {
                Built(p) => proofs.push(p),
                Declined(d) => {
                    // The body of a "for all" may change only for a member
                    // of its domain, so it is carried again under that
                    // membership, as a "there is" is.
                    if label == "wral" && slots == [0] {
                        return self
                            .under_member(given, want, scope, facts, step, leaf, d);
                    }
                    return Ok(Declined(d));
                }
            }
        }
        // The lemma's letters are read off its conclusion fitted to what it
        // lifts, ( scope -> given = want ), or <-> for a statement, so the
        // order set.mm declares them in does not matter: an integral's
        // letter x is declared before every class, a sum's k after.
        let is_class = given.label().is_some_and(|l| self.typecode(l) == "class");
        let lifted = if is_class {
            t!(self.rpn(given), self.rpn(want), "wceq")
        } else {
            t!(self.rpn(given), self.rpn(want), "wb")
        };
        let target = self.to_term(&t!(scope, lifted, "wi"));
        let says = self.statement(lifting);
        let variables = names_of(&says);
        let Some(binding) = fit(&says, &target, &Binding::new(), &variables) else {
            return Ok(Route::no(
                "the lemma that carries this change up says otherwise",
            ));
        };
        let proofs: Vec<&Proof> = proofs.iter().collect();
        Ok(Built(self.b.ap(lifting, &self.spelt(&binding), &proofs)))
    }

    /// ( scope -> given = want ), a map whose domain changes to one spelling
    /// its letter, by `mpteq12dv` with its rule kept; None where neither
    /// domain spells the letter.
    pub fn domain_holding(
        &self,
        given: &Term,
        want: &Term,
        scope: &Rpn,
        moved: &Proof,
    ) -> Option<Proof> {
        if given.label() != Some("cmpt") {
            return None;
        }
        let kids: Vec<Rpn> = given.children().iter().map(|c| self.rpn(c)).collect();
        let (letter, over, rule) = (&kids[0], &kids[1], &kids[2]);
        let new = self.rpn(&want.children()[1]);
        let spells = |t: &Rpn| letter.alone().is_some_and(|l| t.has(l));
        if !spells(over) && !spells(&new) {
            return None;
        }
        let kept = self
            .b
            .ap("eqidd", &binds! {"ph" => scope, "A" => rule}, &[]);
        Some(self.b.ap(
            "mpteq12dv",
            &binds! {"ph" => scope, "x" => letter, "A" => over, "B" => rule, "C" => &new, "D" => rule},
            &[moved, &kept],
        ))
    }

    /// ( scope -> ( A. x e. A ph <-> A. x e. A ps ) ), the body carried with
    /// x ∈ A in scope (`ralbidva`); `why` where that fails too.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn under_member(
        &mut self,
        given: &Term,
        want: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        leaf: &Leaf,
        why: crate::outcome::Decline,
    ) -> Checked<Route<Proof>> {
        let kids = given.children().to_vec();
        let (body, variable, over) = (&kids[0], &kids[1], &kids[2]);
        let (name, runs) = (self.rpn(variable), self.rpn(over));
        if name.alone().is_some_and(|n| scope.has(n)) {
            // `ralbidva` keeps its letter apart from the scope, so where the
            // scope spells it the two are carried over a spare and renamed
            // back.
            let Some(fresh) = self.unheld(&[&self.to_term(scope), given, want]) else {
                return Ok(Declined(why));
            };
            let Some(letter) = variable.variable() else {
                return Ok(Declined(why));
            };
            let mut put = Binding::new();
            put.insert(Symbol::of(letter), fresh);
            let moved = given.substitute(&put);
            let moved_want = want.substitute(&put);
            let walked = self.under_member(
                &moved,
                &moved_want,
                scope,
                facts,
                step,
                leaf,
                why.clone(),
            )?;
            let there = self.renamed_apart(given, &moved)?;
            let back = self.renamed_apart(&moved_want, want)?;
            let (Built(walked), Some(there), Some(back)) = (walked, there, back) else {
                return Ok(Declined(why));
            };
            let (a, b) = (self.rpn(given), self.rpn(&moved));
            let (c, d) = (self.rpn(&moved_want), self.rpn(want));
            let first = pf!(self.b; t!(a, b, "wb"), scope, there, "a1i");
            let last = pf!(self.b; t!(c, d, "wb"), scope, back, "a1i");
            let middle = self.b.ap(
                "bitrd",
                &binds! {"ph" => scope, "ps" => &a, "ch" => &b, "th" => &c},
                &[&first, &walked],
            );
            return Ok(Built(self.b.ap(
                "bitrd",
                &binds! {"ph" => scope, "ps" => &a, "ch" => &c, "th" => &d},
                &[&middle, &last],
            )));
        }
        let member = t!(name, "cv", runs, "wcel");
        let other = want.children()[0].clone();
        let made = self.frames_kept(|me| {
            let (inner, lifted) = me.widen(scope, facts, &member, None);
            me.congruence(body, &other, &inner, &lifted, step, leaf)
        })?;
        let Built(made) = made else {
            return Ok(Declined(why));
        };
        Ok(Built(
            pf!(self.b; scope, self.rpn(body), self.rpn(&other), name, runs, made, "ralbidva"),
        ))
    }

    /// ( scope -> t e. S ), for a term built from numerals alone: a digit
    /// set.mm names in the system is its label, and anything else built only
    /// from numerals is settled from the declared closure lemmas, which is
    /// working it out and not searching.
    pub fn numeral_within(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let named = self.digit_within(goal, scope, facts)?;
        if !named.is_declined() {
            return Ok(named);
        }
        if goal.children()[1].label() == Some("cq") {
            let rational = self.rational_within(&goal.children()[0], scope, facts)?;
            if !rational.is_declined() {
                return Ok(rational);
            }
        }
        let said = self.rpn(&goal.children()[0]);
        if said.tokens().iter().any(|t| !rules::numeric(t.as_str())) {
            // A closed term that binds a letter of its own, a product over
            // a range of numerals, is worked to its numeral, and the
            // membership is the numeral's, carried back by `eqeltrrd`.
            let labels = self.b.flabel.clone();
            let Some((value, is)) =
                super::super::numerals::worked(&self.b, &goal.children()[0], &labels)
            else {
                return Ok(named);
            };
            let spelt = super::super::numerals::spell(value);
            let system = self.rpn(&goal.children()[1]);
            let at = self.to_term(&t!(&spelt, &system, "wcel"));
            let held = take!(self.numeral_within(&at, scope, facts)?);
            let back =
                self.b
                    .ap("eqcomi", &binds! {"A" => &said, "B" => &spelt}, &[&is]);
            let back = pf!(self.b; t!(&spelt, &said, "wceq"), scope, back, "a1i");
            return Ok(Built(self.b.ap(
                "eqeltrrd",
                &binds! {"ph" => scope, "A" => &spelt, "B" => &said, "C" => &system},
                &[&back, &held],
            )));
        }
        // One level deeper than `settle`'s default. Nothing in it is a
        // proof's own, so what it comes to is the same wherever it is asked
        // under this scope, and is worked out once — only where it rests on
        // nothing on the page.
        let want = self.rpn(goal);
        let key = (want.clone(), scope.clone());
        if let Some(found) = self.numbers.get(&key) {
            return Ok(found.clone());
        }
        // A membership asked again while it is being worked out, as the
        // search for 1/2 ∈ ℤ asked 1/2 ∈ ℤ of a lemma's hypothesis, would
        // start the search again at full depth, and never stop.
        if self.numbering.contains(&want) {
            return Ok(Route::no("asked again while it is being worked out"));
        }
        self.numbering.insert(want.clone());
        let found = (|| -> Checked<Route<Proof>> {
            // A power to an exponent below 0 is no atom the closure lemmas
            // reach, and is worked to its value.
            if super::super::calculators::negative_power(&goal.children()[0]) {
                return self.within_by_value(goal, scope, facts);
            }
            let found = self.settle(goal, scope, &Facts::new(), 4, None, None)?;
            if !found.is_declined() {
                return Ok(found);
            }
            let found = self.by_value(goal, scope)?;
            if !found.is_declined() {
                return Ok(found);
            }
            self.within_by_value(goal, scope, facts)
        })();
        self.numbering.shift_remove(&want);
        let found = found?;
        let keep = match &found {
            Declined(_) => true,
            Built(p) => p.origin.is_empty(),
        };
        if keep {
            self.numbers.insert(key, found.clone());
        }
        Ok(found)
    }

    /// ( scope -> x e. S ) for a closed x, through its value: a value
    /// written plainly, a negation or a fraction, is in ℝ and ℂ by way of ℚ
    /// (`qre`, `qcn`); any other closed term is in S as its value is
    /// (`closed_valued`), carried back by `eleq1d`.
    pub(super) fn within_by_value(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let x = &goal.children()[0];
        let (sx, system) = (self.rpn(x), self.rpn(&goal.children()[1]));
        let (_, canon, is) = take!(self.closed_valued(x, scope, facts)?);
        if canon != sx {
            let at = self.to_term(&t!(&canon, &system, "wcel"));
            let held = take!(self.numeral_within(&at, scope, facts)?);
            let iff = self.b.ap(
                "eleq1d",
                &binds! {"ph" => scope, "A" => &sx, "B" => &canon, "C" => &system},
                &[&is],
            );
            let at = Revalued {
                said: t!(&sx, &system, "wcel"),
                valued: t!(&canon, &system, "wcel"),
                iff,
            };
            return Ok(Built(self.carried_back(&at, &held, scope)));
        }
        let law = match goal.children()[1].label() {
            Some("cr") => "qre",
            Some("cc") => "qcn",
            _ => return Ok(Route::no("a system other than ℝ and ℂ")),
        };
        let rational = take!(self.rational_within(x, scope, facts)?);
        let law = self.b.ap(law, &binds! {"A" => &sx}, &[]);
        Ok(Built(
            pf!(self.b; scope, t!(&sx, "cq", "wcel"), t!(&sx, &system, "wcel"), rational, law, "syl"),
        ))
    }

    /// ( scope -> x e. QQ ) for a value written plainly: a whole number by
    /// way of ℤ (`zq`), a fraction of a whole number by one of ℕ (`znq`), and
    /// a negation as what it negates (`qnegcl`).
    pub(super) fn rational_within(
        &mut self,
        x: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let within = |me: &mut Self, t: &Term, system: &str| {
            let goal = me.to_term(&t!(me.rpn(t), system, "wcel"));
            me.numeral_within(&goal, scope, facts)
        };
        let sx = self.rpn(x);
        let kids = x.children().to_vec();
        Ok(match (x.label(), kids.as_slice()) {
            (Some("cneg"), [y]) => {
                let held = take!(within(self, y, "cq")?);
                let sy = self.rpn(y);
                let law = self.b.ap("qnegcl", &binds! {"A" => &sy}, &[]);
                Built(
                    pf!(self.b; scope, t!(&sy, "cq", "wcel"), t!(&sx, "cq", "wcel"), held, law, "syl"),
                )
            }
            (Some("co"), [n, m, op]) if op.label() == Some("cdiv") => {
                let whole = take!(within(self, n, "cz")?);
                let natural = take!(within(self, m, "cn")?);
                let (sn, sm) = (self.rpn(n), self.rpn(m));
                let law = self.b.ap("znq", &binds! {"A" => &sn, "B" => &sm}, &[]);
                Built(self.b.ap(
                    "syl2anc",
                    &binds! {"ph" => scope, "ps" => t!(&sn, "cz", "wcel"), "ch" => t!(&sm, "cn", "wcel"),
                    "th" => t!(&sx, "cq", "wcel")},
                    &[&whole, &natural, &law],
                ))
            }
            _ => {
                let whole = take!(within(self, x, "cz")?);
                let law = self.b.ap("zq", &binds! {"A" => &sx}, &[]);
                Built(
                    pf!(self.b; scope, t!(&sx, "cz", "wcel"), t!(&sx, "cq", "wcel"), whole, law, "syl"),
                )
            }
        })
    }

    /// ( scope -> t e. S ) for a closed t, through the digit it comes to: the
    /// equation is worked out as `arithmetic` works one out, and the
    /// membership is the digit's, carried across it by `eqeltrd`.
    pub(super) fn by_value(
        &mut self,
        goal: &Term,
        scope: &Rpn,
    ) -> Checked<Route<Proof>> {
        let (said, system) = (goal.children()[0].clone(), goal.children()[1].clone());
        let value = take!(field::closed_value(&said));
        let digit = match value {
            Value::Exact(v)
                if v.is_integer() && v >= field::q(0) && v <= field::q(9) =>
            {
                v.to_integer().to_u32().unwrap_or(0)
            }
            _ => return Ok(Route::no("it does not come to a digit")),
        };
        let digit = numeral_label(digit).expect("a digit");
        if self.rpn(&said).alone() == Some(digit) {
            return Ok(Route::no("it is a digit already"));
        }
        let member_goal = self.to_term(&t!(digit, self.rpn(&system), "wcel"));
        let member = take!(self.digit_within(&member_goal, scope, &Facts::new())?);
        let lines = Lines::new();
        let same = take!(self.prove_field(
            None,
            &t!(self.rpn(&said), digit, "wceq"),
            scope,
            &Facts::new(),
            &lines
        )?);
        Ok(Built(self.b.ap(
            "eqeltrd",
            &binds! {"ph" => scope, "A" => self.rpn(&said), "B" => digit, "C" => self.rpn(&system)},
            &[&same, &member],
        )))
    }

    /// ( scope -> ; A B e. S ), for a numeral of more than one digit, built
    /// from the digits' labels and brought into the scope once.
    pub(super) fn decimal_within(
        &mut self,
        goal: &Term,
        scope: &Rpn,
    ) -> Checked<Route<Proof>> {
        let (said, system) = (goal.children()[0].clone(), goal.children()[1].clone());
        // In ℕ by its digits (`numerals::nn`), as 10 is by `decnncl2`: a
        // decimal is never zero, since its digits before the last are not.
        if system.label() == Some("cn") {
            let Some(value) =
                super::super::numerals::value(&said).filter(|v| !v.is_zero())
            else {
                return Ok(Route::no("not a numeral other than zero"));
            };
            let closed = super::super::numerals::nn(&self.b, value);
            return Ok(Built(pf!(self.b; self.rpn(goal), scope, closed, "a1i")));
        }
        let Some(lift) = system.label().and_then(|l| lookup(rules::FROM_NN0, l)) else {
            return Ok(Route::no("a decimal is placed in ℕ, ℕ₀, ℤ, ℝ and ℂ only"));
        };
        fn whole(me: &Elaborator, term: &Term) -> Route<Proof> {
            if let Some(d) = term.label().and_then(rules::digit_of) {
                if term.children().is_empty() {
                    return Built(me.step(&format!("{d}nn0")));
                }
            }
            if term.label() != Some("cdc") {
                return Route::no("not a numeral");
            }
            let (upper, last) = (&term.children()[0], &term.children()[1]);
            let parts = [whole(me, upper), whole(me, last)];
            if let Some(d) = parts.iter().find(|p| p.is_declined()) {
                return d.clone();
            }
            let [Built(a), Built(b)] = parts else {
                unreachable!("both parts are built")
            };
            Built(me.b.ap(
                "deccl",
                &binds! {"A" => me.rpn(upper), "B" => me.rpn(last)},
                &[&a, &b],
            ))
        }
        let mut closed = take!(whole(self, &said));
        if let Some(lift) = lift {
            let s = self.rpn(&said);
            closed = self.b.ap(lift, &binds! {"A" => &s, "N" => &s}, &[&closed]);
        }
        Ok(Built(pf!(self.b; self.rpn(goal), scope, closed, "a1i")))
    }

    /// ( scope -> d e. S ), for a digit and a system set.mm names it in.
    ///
    /// `ax-1cn` is the one place the library spells such a label otherwise,
    /// and where it names none the fact is one it does not state.
    pub fn digit_within(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let _ = facts;
        let (said, system) = (goal.children()[0].clone(), goal.children()[1].clone());
        let suffix = system.label().and_then(|l| lookup(rules::SYSTEMS, l));
        let Some(suffix) = suffix.filter(|_| system.children().is_empty()) else {
            return Ok(Route::no("not a number system set.mm names digits in"));
        };
        if said.label() == Some("cdc") {
            return self.decimal_within(goal, scope);
        }
        let value = linear::numeral(&said, self.flabel());
        let digit = match value {
            Some(v) if v.is_integer() && v >= field::q(0) && v <= field::q(9) => {
                v.to_integer().to_u32().unwrap_or(0)
            }
            _ => return Ok(Route::no("what belongs is not a single digit")),
        };
        // The side must *be* its digit. One that only works out to it is a
        // computation, and this is not the method that does computations.
        let numeral = numeral_label(digit).expect("a digit");
        if self.rpn(&said).alone() != Some(numeral) {
            return Ok(Route::no(
                "a side works out to a digit but is one only after working out",
            ));
        }
        let Some(system_label) = system.label().map(str::to_string) else {
            return Ok(Route::no("the set the digit is in is a letter"));
        };
        let mut label = format!("{digit}{suffix}");
        if !self.b.sigs.contains_key(&label) {
            label = format!("ax-{label}");
        }
        if !self.b.sigs.contains_key(&label)
            && suffix == "z"
            && self.b.sigs.contains_key(&format!("{digit}nn0"))
        {
            // set.mm names every digit in ℕ₀ and only some in ℤ.
            let whole = self.step(&format!("{digit}nn0"));
            let closed = self.b.ap("nn0zi", &binds! {"N" => numeral}, &[&whole]);
            return Ok(Built(
                pf!(self.b; t!(numeral, system_label, "wcel"), scope, closed, "a1i"),
            ));
        }
        if !self.b.sigs.contains_key(&label) {
            return Ok(self.no("set.mm does not state {}", &[&self.rpn(goal)]));
        }
        let held = self.step(&label);
        Ok(Built(self.b.ap(
            "a1i",
            &binds! {"ph" => t!(numeral, system_label, "wcel"), "ps" => scope},
            &[&held],
        )))
    }
}
