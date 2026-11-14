//! Lemmas reached over letters, existentials and respelling.

use super::*;

impl<'a> Elaborator<'a> {
    /// An existence claim its item's lemmas together give: each is proved at
    /// what the `with` target says it is about, and the claim introduced at
    /// the terms they turn out to be about.
    pub fn by_lemmas(
        &mut self,
        labels: &[String],
        goal: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        step: &Step,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let Some(seed) = seed.filter(|s| !labels.is_empty() && !s.is_empty()) else {
            return Ok(Route::no(
                "no `with` in the metamath-proof says what the lemmas are about",
            ));
        };
        let want = self.to_term(goal);
        if want.label() != Some("wrex") {
            return Ok(Route::no("the claim is not \"there is\""));
        }
        if labels.iter().any(|l| !self.b.sigs.contains_key(l)) {
            return Ok(Route::no(format!(
                "{} are not all in the library",
                labels.join(", ")
            )));
        }
        let theirs: BTreeSet<String> = labels
            .iter()
            .flat_map(|l| {
                self.sig(l)
                    .push()
                    .into_iter()
                    .map(String::from)
                    .collect::<Vec<_>>()
            })
            .collect();
        let witness: Vec<Symbol> = seed
            .keys()
            .filter(|n| !theirs.contains(n.as_str()))
            .copied()
            .collect();
        if !witness.is_empty() {
            return self.at_witness(labels, &want, seed, &witness, scope, facts, step);
        }
        let known = facts.copy();
        for label in labels {
            let mut reads = self.statement(label);
            while reads.label() == Some("wi") {
                reads = reads.children()[1].clone();
            }
            if reads.names().iter().any(|n| !seed.contains_key(&**n)) {
                return Ok(Route::no(format!(
                    "the metamath-proof does not say what {label} is about"
                )));
            }
            let said = self.rpn(&reads.substitute(seed));
            let proof = take!(self.apply_lemma(
                label,
                &self.to_term(&said),
                scope,
                facts,
                Some(step),
                false,
                Some(seed)
            )?);
            self.know(&known, said.clone(), proof.clone());
            self.unpack_all(&said, &proof, scope, &known);
        }
        self.introduced(&want, scope, &known)
    }

    /// An existence claim at the thing a `with` target names for it: the
    /// witness is put in for the binder, each part of what the claim then
    /// says is proved by the first lemma that reaches it, and the claim is
    /// introduced at the witness.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn at_witness(
        &mut self,
        labels: &[String],
        want: &Term,
        seed: &Binding,
        witness: &[Symbol],
        scope: &Rpn,
        facts: &Facts,
        step: &Step,
    ) -> Checked<Route<Proof>> {
        if witness.len() != 1 {
            return Ok(Route::no(format!(
                "the metamath-proof names {} witnesses and the claim is read one binder at a time",
                witness.len()
            )));
        }
        let (body, variable, over) = (
            want.children()[0].clone(),
            want.children()[1].clone(),
            want.children()[2].clone(),
        );
        let stood = seed[&witness[0]].clone();
        let member = t!(self.rpn(&stood), self.rpn(&over), "wcel");
        let said = self.replaced(&body, &t!(self.rpn(&variable), "cv"), &stood);
        let mut by_lemmas = |me: &mut Self, one: &Term| -> Checked<Route<Proof>> {
            let mut refused = Vec::new();
            for label in labels {
                let made =
                    me.apply_lemma(label, one, scope, facts, Some(step), true, None)?;
                match made {
                    Built(p) => return Ok(Built(p)),
                    Declined(d) => refused.push(format!("{label}: {}", me.say(&d))),
                }
            }
            Ok(Route::no(refused.join("; ")))
        };
        let known = facts.copy();
        for part in [self.to_term(&member), said] {
            let made = match self.conjoined(&part, scope, &mut by_lemmas)? {
                Some(made) => made,
                None => by_lemmas(self, &part)?,
            };
            let made = take!(made);
            let key = self.rpn(&part);
            self.know(&known, key.clone(), made.clone());
            self.unpack_all(&key, &made, scope, &known);
        }
        self.introduced(want, scope, &known)
    }

    /// An existential claim at witnesses the scope already names: which of
    /// them stands for which binder is read off the body, one part of the
    /// claim matched against one fact in scope. A witness may be a term and
    /// not a name, so the binder is matched as the class it stands for.
    pub(super) fn introduced(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut marks: Vec<String> = Vec::new();
        let mut rest = goal.clone();
        while rest.label() == Some("wrex") {
            let Some(letter) = rest.children()[1].variable() else {
                return Ok(Route::no("the claim's \"there is\" binds no letter"));
            };
            marks.push(letter.to_string());
            rest = rest.children()[0].clone();
        }
        let mark_set: BTreeSet<String> = marks.iter().cloned().collect();
        let mut found: Option<Binding> = None;
        let keys = facts.keys();
        'parts: for piece in self.parts(&self.rpn(&rest)) {
            let shape = as_class(&self.to_term(&piece), &mark_set);
            for said in &keys {
                if let Some(fits) =
                    fit(&shape, &self.to_term(said), &Binding::new(), &mark_set)
                {
                    if fits.len() == marks.len() {
                        found = Some(fits);
                        break 'parts;
                    }
                }
            }
        }
        let Some(found) = found else {
            return Ok(Route::no("no fact in scope names what the claim binds"));
        };
        // What each binder stands for, as `rspcev` wants it: a class.
        let mut stood: IndexMap<String, Rpn> = IndexMap::new();
        for (name, term) in &found {
            let said = self.rpn(term);
            stood.insert(
                name.to_string(),
                if term.variable().is_some() {
                    t!(said, "cv")
                } else {
                    said
                },
            );
        }
        let mut layers: Vec<(Term, String, Rpn)> = Vec::new();
        let mut rest = goal.clone();
        while rest.label() == Some("wrex") {
            let kids = rest.children().to_vec();
            let Some(letter) = kids[1].variable() else {
                return Ok(Route::no("the claim's \"there is\" binds no letter"));
            };
            layers.push((kids[0].clone(), letter.to_string(), self.rpn(&kids[2])));
            rest = kids[0].clone();
        }
        let mut proof: Option<Proof> = None;
        for i in (0..layers.len()).rev() {
            let (body, name, over) = layers[i].clone();
            // The body with every binder outside this one already standing
            // at its witness, and then with this one too.
            let var = self.float_of(&name);
            let mut held = body;
            for (_, n, _) in &layers[..i] {
                held = self.restated(&held, &t!(self.float_of(n), "cv"), &stood[n]);
            }
            let here = self.restated(&held, &t!(var, "cv"), &stood[&name]);
            let (ph, ps) = (self.rpn(&held), self.rpn(&here));
            if proof.is_none() {
                proof = Some(take!(self.settle(&here, scope, facts, 3, None, None)?));
            }
            let witness = stood[&name].clone();
            let tie = self.to_term(&t!(
                t!(var, "cv", witness, "wceq"),
                t!(ph, ps, "wb"),
                "wi"
            ));
            let instance = take!(self.prove_essential(&tie, scope, facts)?);
            let member = t!(witness, over, "wcel");
            let stands = take!(self.settle(
                &self.to_term(&member),
                scope,
                facts,
                3,
                None,
                None
            )?);
            let inner = proof.take().unwrap();
            let both = pf!(self.b; scope, member, ps, stands, inner, "jca");
            proof = Some(
                pf!(self.b; scope, t!(member, ps, "wa"), t!(ph, var, over, "wrex"), both,
                ph, ps, var, witness, over, instance, "rspcev", "syl"),
            );
        }
        Ok(Built(proof.expect("an existential of one binder at least")))
    }

    /// A lemma said of every such name: the name is fixed, the lemma applied
    /// to it, and the claim generalised (`for_every`).
    pub(super) fn as_generalised(
        &mut self,
        label: &str,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        if goal.label() != Some("wral") {
            return Ok(Route::no("the claim is not \"for all\""));
        }
        let (body, variable, over) = (
            goal.children()[0].clone(),
            goal.children()[1].clone(),
            goal.children()[2].clone(),
        );
        self.for_every(
            scope,
            facts,
            &body,
            &variable,
            &over,
            &mut |me, said, inner, lifted| {
                me.apply_lemma(label, said, inner, lifted, step, false, seed)
            },
            false,
        )
    }

    /// One half of what a lemma concludes: the half the claim is fixes the
    /// lemma, and `simpld` or `simprd` takes it. A half and the claim are
    /// compared in the page's spelling of a disequality (`page_spelling`),
    /// since a lemma may write `T =/= R` where the page reads `-. T = R`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn as_conjunct(
        &mut self,
        label: &str,
        whole: &Term,
        reads: &Term,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        if reads.label() != Some("wa") || reads.children().len() != 2 {
            return Ok(Route::no(format!(
                "{label} does not conclude a conjunction"
            )));
        }
        let mut asks = Vec::new();
        let mut walk = whole.clone();
        while matches!(walk.label(), Some("wi") | Some("wb"))
            && !walk.same_object(reads)
        {
            asks.push(walk.children()[0].clone());
            walk = walk.children()[1].clone();
        }
        let variables = names_of(whole);
        let keys = facts.keys();
        let start = seed.cloned().unwrap_or_default();
        let want = page_spelling(goal);
        for (i, part) in reads.children().iter().enumerate() {
            let Some(mut bound) = fit(&page_spelling(part), &want, &start, &variables)
            else {
                continue;
            };
            // A half need not name everything the lemma does, and what is
            // left open is what the step cited a line for.
            for slot in &asks {
                if reads.names().iter().all(|n| bound.contains_key(&**n)) {
                    break;
                }
                for held in &keys {
                    if let Some(filled) =
                        fit(slot, &self.to_term(held), &bound, &variables)
                    {
                        bound = filled;
                        break;
                    }
                }
            }
            if reads.names().iter().any(|n| !bound.contains_key(&**n)) {
                continue;
            }
            let said = reads.substitute(&bound);
            let Built(proof) = self.apply_lemma(
                label,
                &said,
                scope,
                facts,
                step,
                false,
                Some(&bound),
            )?
            else {
                continue;
            };
            let (a, b) = (self.rpn(&said.children()[0]), self.rpn(&said.children()[1]));
            let pick = if i == 0 { "simpld" } else { "simprd" };
            let half = pf!(self.b; scope, a, b, proof, pick);
            let (taken, wanted) = (self.rpn(&said.children()[i]), self.rpn(goal));
            if taken == wanted {
                return Ok(Built(half));
            }
            // The half is the claim in set.mm's spelling: it is carried
            // across.
            let Built(back) =
                self.same(&said.children()[i], goal, scope, facts, step)?
            else {
                continue;
            };
            return Ok(Built(
                pf!(self.b; scope, taken, wanted, half, back, "mpbid"),
            ));
        }
        Ok(Route::no(format!(
            "neither half of what {label} concludes is the claim"
        )))
    }

    /// A lemma whose `with` target already says what it concludes: where the
    /// seed fixes every variable there is nothing left for the claim to fix,
    /// and the two need not be spelt the same.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn as_seeded(
        &mut self,
        label: &str,
        reads: &Term,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let full =
            seed.is_some_and(|s| reads.names().iter().all(|n| s.contains_key(&**n)));
        if !full {
            return Ok(Route::no(format!(
                "the metamath-proof does not fix every variable of {label}"
            )));
        }
        let seed = seed.unwrap();
        let said = reads.substitute(seed);
        if self.rpn(&said) == self.rpn(goal) {
            return Ok(Route::no(format!(
                "{label} at its seed is the claim as written"
            )));
        }
        let proof = take!(self.apply_lemma(
            label,
            &said,
            scope,
            facts,
            step,
            false,
            Some(seed)
        )?);
        // No bridge means the lemma is not this claim said otherwise.
        let across = match self.bridging(&said, goal, scope, facts, step)? {
            Built(p) => Some(p),
            Declined(_) => self.by_equation(&said, goal, scope, facts, step)?,
        };
        let Some(across) = across else {
            return Ok(Route::no(format!(
                "nothing carries what {label} gives to the claim"
            )));
        };
        Ok(Built(
            pf!(self.b; scope, self.rpn(&said), self.rpn(goal), proof, across, "mpbid"),
        ))
    }

    /// A lemma's conclusion carried to the claim by an equation proved: each
    /// place the two terms differ is one equation, and it is settled where it
    /// stands.
    pub(super) fn by_equation(
        &mut self,
        said: &Term,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
    ) -> Checked<Option<Proof>> {
        let proved = Leaf::Rows(vec![Row::Held]);
        if let Built(straight) =
            self.congruence(said, goal, scope, facts, step, &proved)?
        {
            return Ok(Some(straight));
        }
        if goal.label() != Some("wceq") || goal.children().len() != 2 {
            return Ok(None);
        }
        // An equation is the same equation written the other way round.
        let turned = Term::apply(
            "wceq",
            vec![goal.children()[1].clone(), goal.children()[0].clone()],
        );
        let Built(across) =
            self.congruence(said, &turned, scope, facts, step, &proved)?
        else {
            return Ok(None);
        };
        let Built(back) = self.same(&turned, goal, scope, facts, step)? else {
            return Ok(None);
        };
        Ok(Some(self.chained(
            scope,
            &[
                ChainLink {
                    from: said.clone(),
                    to: turned.clone(),
                    proof: across,
                },
                ChainLink {
                    from: turned,
                    to: goal.clone(),
                    proof: back,
                },
            ],
        )))
    }

    /// A lemma reaching a claim it says in other words: both are read through
    /// the rules of `rules::STANDARD` and matched again, which fixes what the
    /// lemma's variables stand for, and `same` carries it to the claim.
    /// What the lemma concludes is tried first, then the near side of each
    /// biconditional it states, and last each biconditional whole.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn in_other_words(
        &mut self,
        label: &str,
        whole: &Term,
        reads: &Term,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let variables = names_of(whole);
        let mut sides = vec![reads.clone()];
        let mut wholes = Vec::new();
        let mut rest = whole.clone();
        while matches!(rest.label(), Some("wi") | Some("wb")) {
            if rest.label() == Some("wb") {
                sides.push(rest.children()[0].clone());
                wholes.push(rest.clone());
            }
            rest = rest.children()[1].clone();
        }
        sides.extend(wholes);
        let theirs = self.read_through(goal, true, None);
        let mut found: Route<Proof> = Route::no(format!(
            "{label} does not conclude the claim in any words the rules read"
        ));
        // The seed as written first, and then read the way the claim is.
        let mut seeds = vec![seed.cloned().unwrap_or_default()];
        if let Some(seed) = seed.filter(|s| !s.is_empty()) {
            let mut read = Binding::new();
            for (name, value) in seed {
                read.insert(*name, self.read_through(value, true, None));
            }
            seeds.push(read);
        }
        // The claim read as it is, and with each letter it binds respelt by
        // what its binder says, so that two parts the lemma asks be one, its
        // A in {x ∈ A : φ} ⊆ A, are one where they differ only in the
        // letters they bind.
        let mut readings = vec![theirs.clone()];
        if let Some(by_content) = self.letters_by_content(&theirs) {
            if self.rpn(&by_content) != self.rpn(&theirs) {
                readings.push(by_content);
            }
        }
        for (side, theirs) in sides
            .iter()
            .flat_map(|s| readings.iter().map(move |r| (s, r)))
        {
            for sown in &seeds {
                // A map the seed gives is read at what the lemma applies it
                // to, F(n) at F the map sending p ∈ ℕ to 1/p being 1/n, and
                // the lemma's other letters fitted to the claim from there.
                let fitted = match self.fit_read(side, theirs, sown, &variables) {
                    Some(b) => Some(b),
                    None => {
                        let applied = self.maps_read(&side.substitute(sown));
                        self.fit_read(&applied, theirs, sown, &variables)
                    }
                };
                let Some(binding) = fitted else {
                    continue;
                };
                if side.names().iter().any(|n| !binding.contains_key(&**n)) {
                    continue;
                }
                let binding = self.refolded(binding, goal);
                let instance = side.substitute(&binding);
                if self.rpn(&instance) == self.rpn(goal) {
                    continue;
                }
                found = self.apply_lemma(
                    label,
                    &instance,
                    scope,
                    facts,
                    step,
                    false,
                    Some(&binding),
                )?;
                let Built(made) = found.clone() else {
                    continue;
                };
                // What carries the instance to the claim asks as a lemma
                // does, from what the step names.
                let held = match step {
                    None => facts.clone(),
                    Some(step) => {
                        let supplied = self.supplied(Some(step), scope, facts)?;
                        self.with_cited(Some(step), scope, &supplied, None)?
                    }
                };
                let across =
                    self.same_through_names(&instance, goal, scope, &held, step)?;
                let Built(across) = across else {
                    found = across;
                    continue;
                };
                return Ok(Built(
                    pf!(self.b; scope, self.rpn(&instance), self.rpn(goal), made, across, "mpbid"),
                ));
            }
        }
        Ok(found)
    }

    /// `same`, and where it declines, the two compared through `want` with
    /// its defined names read as what they name (`read_out`): a lemma's
    /// instance fitted as the standard form reads the claim differs from
    /// the claim in a define's rule, which may hold more to close than the
    /// rule alone, as G(m, 0) read as its rule writes m + 0.
    pub fn same_through_names(
        &mut self,
        given: &Term,
        want: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        let direct = self.same(given, want, scope, facts, step)?;
        if let Built(p) = direct {
            return Ok(Built(p));
        }
        let read = self.read_out(want);
        if self.rpn(&read) == self.rpn(want) {
            return Ok(direct);
        }
        // The rule may bind other letters than `given` does at the same
        // places: it is spelt with `given`'s letters first, so that what is
        // left to close between the two is what is not a renaming.
        let like = self
            .respelt_like(&read, given)
            .unwrap_or_else(|| read.clone());
        let mut links = Vec::new();
        let mut at = given.clone();
        for next in [like, read, want.clone()] {
            if self.rpn(&next) == self.rpn(&at) {
                continue;
            }
            let proof = take!(self.same(&at, &next, scope, facts, step)?);
            links.push(ChainLink {
                from: at.clone(),
                to: next.clone(),
                proof,
            });
            at = next;
        }
        Ok(Built(self.chained(scope, &links)))
    }

    /// `term` with each letter a set-builder, a "for all", a "there is" or a
    /// map binds respelt as `like` binds the letter in the same place, where
    /// the two are built alike that far; None where a letter of `like` is
    /// one `term` spells, which the respelling could capture.
    pub(super) fn respelt_like(&self, term: &Term, like: &Term) -> Option<Term> {
        let spelt = self.rpn(term);
        let mut out = term.clone();
        self.respelt_into(&mut out, like, &spelt)?;
        Some(out)
    }

    pub(super) fn respelt_into(
        &self,
        term: &mut Term,
        like: &Term,
        spelt: &Rpn,
    ) -> Option<()> {
        if term.variable().is_some()
            || term.label() != like.label()
            || term.children().len() != like.children().len()
        {
            return Some(());
        }
        let Some(label) = term.label().map(str::to_string) else {
            return Some(());
        };
        let mut kids = term.children().to_vec();
        let layout = match label.as_str() {
            "crab" | "wral" | "wrex" => Some((1, 2)),
            "cmpt" => Some((0, 1)),
            _ => None,
        };
        if let Some((at, domain)) = layout {
            let (ours, theirs) = (&kids[at], &like.children()[at]);
            if let (Some(letter), Some(new)) =
                (ours.variable_symbol(), theirs.variable())
            {
                if ours.variable() != theirs.variable() {
                    if spelt.has(new) {
                        return None;
                    }
                    let mut put = Binding::new();
                    put.insert(letter, theirs.clone());
                    for (i, k) in kids.iter_mut().enumerate() {
                        if i != domain {
                            *k = k.substitute(&put);
                        }
                    }
                }
            }
        }
        for (k, l) in kids.iter_mut().zip(like.children()) {
            self.respelt_into(k, l, spelt)?;
        }
        *term = Term::apply(&label, kids);
        Some(())
    }

    /// `term` with each letter a set-builder, a "for all", a "there is" or a
    /// map binds respelt by what the binder says: two binders that say the
    /// same, their letters apart, bind one letter wherever they stand, and
    /// two that say different things bind different letters, so a binder
    /// never shares its letter with one inside its domain. Two parts that
    /// differ only in the letters they bind are then spelt alike. For
    /// fitting a lemma alone (`in_other_words`), which `same` then carries
    /// to the claim as written. None where too few letters are spare.
    pub(super) fn letters_by_content(&self, term: &Term) -> Option<Term> {
        let mut given: IndexMap<Rpn, Term> = IndexMap::new();
        self.respelt_by_content(term, term, &mut given)
    }

    /// `letters_by_content` of a part of `whole`, `given` the letter each
    /// binder's content has been given so far, the content read with its
    /// letters spelt by depth (`respelt_by_depth`).
    pub(super) fn respelt_by_content(
        &self,
        term: &Term,
        whole: &Term,
        given: &mut IndexMap<Rpn, Term>,
    ) -> Option<Term> {
        if term.variable().is_some() || term.children().is_empty() {
            return Some(term.clone());
        }
        let Some(label) = term.label() else {
            return Some(term.clone());
        };
        let kids = term.children();
        let layout = match label {
            "crab" | "wral" | "wrex" => Some((1, 2)),
            "cmpt" => Some((0, 1)),
            _ => None,
        };
        let letter = layout.and_then(|(at, _)| kids[at].variable_symbol());
        let (Some((at, _)), Some(letter)) = (layout, letter) else {
            let out: Option<Vec<Term>> = kids
                .iter()
                .map(|k| self.respelt_by_content(k, whole, given))
                .collect();
            return Some(Term::apply(label, out?));
        };
        let content = {
            let mut letters: Vec<Term> = Vec::new();
            self.rpn(&self.respelt_by_depth(term, 0, &mut letters, whole)?)
        };
        let fresh = match given.get(&content) {
            Some(f) => f.clone(),
            None => {
                let mut seen: Vec<&Term> = vec![whole];
                seen.extend(given.values());
                let f = self.unheld(&seen)?;
                given.insert(content, f.clone());
                f
            }
        };
        let mut put = Binding::new();
        put.insert(letter, fresh.clone());
        let domain_at = layout.map(|(_, d)| d);
        let mut out = Vec::new();
        for (i, k) in kids.iter().enumerate() {
            out.push(if i == at {
                fresh.clone()
            } else if Some(i) == domain_at {
                self.respelt_by_content(k, whole, given)?
            } else {
                self.respelt_by_content(&k.substitute(&put), whole, given)?
            });
        }
        Some(Term::apply(label, out))
    }

    /// `letters_by_depth` of a part of `whole` standing under `depth`
    /// binders, `letters` the letter of each depth so far.
    pub(super) fn respelt_by_depth(
        &self,
        term: &Term,
        depth: usize,
        letters: &mut Vec<Term>,
        whole: &Term,
    ) -> Option<Term> {
        if term.variable().is_some() || term.children().is_empty() {
            return Some(term.clone());
        }
        let Some(label) = term.label() else {
            return Some(term.clone());
        };
        let kids = term.children();
        // Where each binder holds its letter and its domain.
        let layout = match label {
            "crab" | "wral" | "wrex" => Some((1, 2)),
            "cmpt" => Some((0, 1)),
            _ => None,
        };
        let letter = layout.and_then(|(at, _)| kids[at].variable_symbol());
        let (Some((at, domain)), Some(letter)) = (layout, letter) else {
            let out: Option<Vec<Term>> = kids
                .iter()
                .map(|k| self.respelt_by_depth(k, depth, letters, whole))
                .collect();
            return Some(Term::apply(label, out?));
        };
        while letters.len() <= depth {
            let mut seen: Vec<&Term> = vec![whole];
            seen.extend(letters.iter());
            let fresh = self.unheld(&seen)?;
            letters.push(fresh);
        }
        let fresh = letters[depth].clone();
        let mut put = Binding::new();
        put.insert(letter, fresh.clone());
        let mut out = Vec::new();
        for (i, k) in kids.iter().enumerate() {
            out.push(if i == at {
                fresh.clone()
            } else if i == domain {
                self.respelt_by_depth(k, depth, letters, whole)?
            } else {
                self.respelt_by_depth(&k.substitute(&put), depth + 1, letters, whole)?
            });
        }
        Some(Term::apply(label, out))
    }

    /// What a lemma's variables stand for where its `pattern` is `term`: as
    /// written, or else with both read in standard form (`read_through`);
    /// None where neither fits.
    ///
    /// A define's name the seed gives a variable stays a name in `term`, as
    /// it stands in the pattern the seed fills: `F ` z` with F given as k
    /// fits k(x), which k's rule at x would not (`read_holding`).
    pub fn fits_as(
        &mut self,
        pattern: &Term,
        term: &Term,
        variables: &Vars,
        seed: Option<&Binding>,
    ) -> Option<Binding> {
        let start = seed.cloned().unwrap_or_default();
        if let Some(binding) = fit(pattern, term, &start, variables) {
            return Some(binding);
        }
        let held: Vars = start
            .values()
            .filter_map(|given| self.defined_name(given))
            .collect();
        let t = self.read_holding(term, &held);
        let binding = self.fit_read(pattern, &t, &start, variables)?;
        Some(self.refolded(binding, term))
    }

    /// The letter a define gave, where `term` is that name standing alone;
    /// else None.
    pub(super) fn defined_name(&self, term: &Term) -> Option<Symbol> {
        if term.variable().is_some() || term.label() != Some("cv") {
            return None;
        }
        let letter = term.children().first()?;
        let said = self.rpn(letter);
        let defined = self.definitions.contains_key(said.alone()?);
        defined.then(|| letter.variable_symbol()).flatten()
    }

    /// `read_through` with defined names, but for the defines whose letters
    /// are `held`, which stay names and their values stay applied.
    pub(super) fn read_holding(&mut self, term: &Term, held: &Vars) -> Term {
        let mut letters: Vars = self.letters_bound(term).iter().cloned().collect();
        letters.extend(held.iter().cloned());
        let kept = self.binding.clone();
        self.binding.extend(held.iter().cloned());
        let read = self.read_through(term, true, Some(&letters));
        self.binding = kept;
        read
    }

    /// What a lemma's variables stand for where its `pattern`, read in
    /// standard form, is `read`, a term already read so: the two are fitted
    /// with `read`'s bound letters spelt as the pattern binds them
    /// (`respelt_as`). What is fitted is the lemma's instance, which says what
    /// `read` says over other bound letters at most, and the caller carries
    /// it to the claim by `same`.
    pub(super) fn fit_read(
        &mut self,
        pattern: &Term,
        read: &Term,
        seed: &Binding,
        variables: &Vars,
    ) -> Option<Binding> {
        let p = self.read_through(pattern, false, None);
        let t = self.respelt_as(&p, read, variables);
        let fitting = Fitting {
            variables,
            turned: &|term| self.pair_turned(term),
            pairs_only: false,
        };
        fit_either_way(&p, &t, seed, &fitting)
    }

    /// An antecedent fitted whole to one of the lines `known` holds, as
    /// `fit_respelt_in_no_order` fits it: to the line as written, or to a
    /// triangle or a collinearity it says with its three points in another
    /// order (`REORDERS`), which `settle` then carries to the order asked.
    /// None where no line fits.
    /// Every way a line of `known` says `slot` whole, in the order of the
    /// lines, and of one line every order of its points that fits: with
    /// one letter fixed, a triangle held as Q, K, S fits A, B, C at K both
    /// as K, Q, S and as K, S, Q, and only the rest of the antecedent says
    /// which (`fit_answering_rest`).
    pub(super) fn fits_whole(
        &mut self,
        slot: &Term,
        known: &[Rpn],
        binding: &Binding,
        variables: &Vars,
        fresh: &Binding,
    ) -> Vec<Binding> {
        let mut out = Vec::new();
        for held in known {
            let held = self.to_term(held);
            for said in self.in_every_order(&held) {
                if let Some(filled) =
                    self.fit_respelt_in_no_order(slot, &said, binding, variables, fresh)
                {
                    out.push(filled);
                }
            }
        }
        out
    }

    /// Of the ways a conjunct fits the lines the step has, the first under
    /// which every antecedent still to be matched that it decides whole is
    /// one of those lines; the first way where none is. A conjunct with a
    /// letter open can fit several lines: `X is on line AB` fits each line X
    /// is on, and only one of them makes `not (Y is on line AB)` a line the
    /// step has.
    pub(super) fn fit_answering_rest(
        &mut self,
        fits: Vec<Binding>,
        pending: &[&Term],
        before: &Binding,
        known: &[Rpn],
        variables: &Vars,
        fresh: &Binding,
    ) -> Option<Binding> {
        let first = fits.first().cloned();
        for filled in fits {
            if self.answers_decided(pending, before, &filled, known, variables, fresh) {
                return Some(filled);
            }
        }
        first
    }

    /// Whether each antecedent of `pending` that `filled` decides whole,
    /// and `before` did not, is answered conjunct by conjunct by a line of
    /// `known`.
    pub(super) fn answers_decided(
        &mut self,
        pending: &[&Term],
        before: &Binding,
        filled: &Binding,
        known: &[Rpn],
        variables: &Vars,
        fresh: &Binding,
    ) -> bool {
        for slot in pending {
            if slot.variable().is_some()
                || decides(slot, before)
                || !decides(slot, filled)
            {
                continue;
            }
            for piece in conjuncts_of(slot) {
                // Answered as the line is written or as the standard form
                // reads it: a step may say A ≠ B as `-. A = B`.
                let answered = known.iter().any(|held| {
                    let held = self.to_term(held);
                    self.fit_respelt_in_no_order(
                        &piece, &held, filled, variables, fresh,
                    )
                    .is_some()
                        || self
                            .fits_as(&piece, &held, variables, Some(filled))
                            .is_some()
                });
                if !answered {
                    return false;
                }
            }
        }
        true
    }

    /// The conjuncts of an antecedent no line says whole, taken apart only
    /// as far as they must be. A part that is itself a conjunction with a
    /// letter still open is answered whole where a line says it, which
    /// fixes its letters together, as `fits_whole` does for the antecedent:
    /// taken apart, a triangle's `-. B = C` would be fitted in no order
    /// against `-. A = B` and take C from A.
    pub(super) fn open_pieces(
        &mut self,
        slot: &Term,
        pending: &[&Term],
        known: &[Rpn],
        binding: &mut Binding,
        variables: &Vars,
        fresh: &Binding,
    ) -> Vec<Term> {
        let mut pieces = Vec::new();
        let mut parts: Vec<Term> = slot.children().iter().rev().cloned().collect();
        if !is_conjunction(slot) {
            parts = vec![slot.clone()];
        }
        while let Some(part) = parts.pop() {
            if !is_conjunction(&part) {
                pieces.push(part);
                continue;
            }
            let open = part.names().iter().any(|n| !binding.contains_key(&**n));
            if open {
                // A line that says the part whole answers it only where what
                // it decides of the rest is answered too: `( A =/= B /\ C =/=
                // D )` is said by any two disequalities.
                let rest: Vec<&Term> =
                    parts.iter().chain(pending.iter().copied()).collect();
                let wholes = self.fits_whole(&part, known, binding, variables, fresh);
                let answering = wholes.into_iter().find(|filled| {
                    self.answers_decided(
                        &rest, binding, filled, known, variables, fresh,
                    )
                });
                if let Some(filled) = answering {
                    *binding = filled;
                    continue;
                }
            }
            parts.extend(part.children().iter().rev().cloned());
        }
        pieces
    }
}
