//! Applying a lemma, in stages.

use super::*;

impl<'a> Elaborator<'a> {
    /// `term`, and where it is a claim about three points in no order
    /// (`REORDERS`), the same claim with its points in each other order.
    pub(super) fn in_every_order(&mut self, term: &Term) -> Vec<Term> {
        let mut out = vec![term.clone()];
        for by in &REORDERS {
            let Some(ThreePoints {
                shape,
                letters,
                points,
            }) = self.three_points(by, term)
            else {
                continue;
            };
            for order in [[0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] {
                let mut put = Binding::new();
                for (&letter, &i) in letters.iter().zip(&order) {
                    put.insert(letter, points[i].clone());
                }
                out.push(shape.substitute(&put));
            }
        }
        out
    }

    /// `fit_respelt`, where a notation's two holes in no order meet the
    /// line's either way round, as `same` carries the one order to the
    /// other: what a lemma asks, |AO| = |BO|, fitted to a line saying
    /// |QA| = |QB| binds O to Q. Everything else is fitted as written.
    pub(crate) fn fit_respelt_in_no_order(
        &self,
        pattern: &Term,
        ground: &Term,
        binding: &Binding,
        variables: &Vars,
        fresh: &Binding,
    ) -> Option<Binding> {
        // A fit as written is the fit in no order wherever there is one,
        // since each pair is tried as written first; it is the cheaper.
        if let Some(found) = fit_respelt(pattern, ground, binding, variables, fresh) {
            return Some(found);
        }
        let mut open = binding.clone();
        for k in fresh.keys() {
            open.shift_remove(k);
        }
        let fitting = Fitting {
            variables,
            turned: &|term| self.pair_turned(term),
            pairs_only: true,
        };
        let filled = fit_either_way(pattern, ground, &open, &fitting)?;
        let mut out = binding.clone();
        for (k, v) in filled {
            if !fresh.contains_key(&k) {
                out.entry(k).or_insert(v);
            }
        }
        Some(out)
    }

    /// `term` with its bound letters respelt so that each letter `pattern`
    /// binds is met in one spelling. A lemma may bind one letter at two
    /// binders, as `count-shift` binds i on both sides, while the claim spells
    /// the two apart: a define's body binds a letter of its own (`apart`), so
    /// a claim naming it reads one set over that letter and the other over
    /// the page's. The two spellings are one claim by a renaming, but a fit
    /// reads the lemma's letter off the first binder and finds the second
    /// different. Where the pattern binds one of its `variables` and has met
    /// it before, the term's letter at that binder is renamed to the one met,
    /// throughout the binder's part and only where that letter appears
    /// nowhere in it, so the result says what `term` says. A binder is a
    /// constructor other than `cv` with a set variable directly under it, as
    /// `letters_bound` reads them.
    pub(super) fn respelt_as(
        &self,
        pattern: &Term,
        term: &Term,
        variables: &Vars,
    ) -> Term {
        let mut met = IndexMap::new();
        self.respelt_within(pattern, term, variables, &mut met)
    }

    /// `respelt_as` at one part, `met` holding the spelling each pattern
    /// letter was met in so far.
    pub(super) fn respelt_within(
        &self,
        pattern: &Term,
        term: &Term,
        variables: &Vars,
        met: &mut IndexMap<String, String>,
    ) -> Term {
        if pattern.variable().is_some()
            || term.variable().is_some()
            || pattern.label() != term.label()
            || pattern.children().len() != term.children().len()
        {
            return term.clone();
        }
        let mut term = term.clone();
        if pattern.label() != Some("cv") {
            for (k, p) in pattern.children().iter().enumerate() {
                let (Some(p), Some(w)) = (p.variable(), term.children()[k].variable())
                else {
                    continue;
                };
                if !variables.contains(p)
                    || !self.is_setvar(&self.float_of(p))
                    || !self.is_setvar(&self.float_of(w))
                {
                    continue;
                }
                let Some(u) = met.get(p).cloned() else {
                    met.insert(p.to_string(), w.to_string());
                    continue;
                };
                if u != w && !term.names().contains(u.as_str()) {
                    let mut to = Binding::new();
                    to.insert(Symbol::of(w), Term::var(&u));
                    term = term.substitute(&to);
                }
            }
        }
        let kids: Vec<Term> = pattern
            .children()
            .iter()
            .zip(term.children())
            .map(|(p, t)| self.respelt_within(p, t, variables, met))
            .collect();
        term.with_children(kids)
    }

    /// `binding` with each value the reading wrote out put back as `term`
    /// writes it. The reading is for finding what the lemma's letters stand
    /// for, and its conditional rules hold only where their conditions do:
    /// |A − B| for two points read as A − B by `nn0absid` is a value no
    /// instance of the lemma can be carried back from to the claim.
    pub(super) fn refolded(&mut self, binding: Binding, term: &Term) -> Binding {
        // A part behind a defined name is written as the define writes it:
        // a ∈ C, C the set {m ∈ ℝ : |m| = r}, has |m| = r as a part, and the
        // reading's conditional rules take it to m = r.
        let named = self.names_read(term, None);
        let mut written: IndexMap<Rpn, Term> = IndexMap::new();
        // A value `term` writes as it stands is left as it is: x in
        // x ≠ 0 ↔ |x| > 0 is x, though |x| reads as x by `nn0absid`.
        let mut as_written: BTreeSet<Rpn> = BTreeSet::new();
        self.written_unpeeled(term, &mut as_written);
        self.written_unpeeled(&named, &mut as_written);
        for sub in subterms(term).into_iter().chain(subterms(&named)) {
            let read = self.read_through(&sub, true, None);
            written.entry(self.rpn(&read)).or_insert(sub);
        }
        let mut out = binding.clone();
        for (name, value) in &binding {
            let said = self.rpn(value);
            if as_written.contains(&said) {
                continue;
            }
            if let Some(w) = written.get(&said) {
                if self.rpn(w) != said {
                    out.insert(*name, w.clone());
                }
            }
        }
        out
    }

    /// Each part of `term` as it is written, into `out`, leaving out a part
    /// that is written only inside a whole the reading takes to it: A − B in
    /// |A − B|, which `nn0absid` reads as A − B, is not written as it stands.
    pub(super) fn written_unpeeled(&mut self, term: &Term, out: &mut BTreeSet<Rpn>) {
        out.insert(self.rpn(term));
        if term.variable().is_some() {
            return;
        }
        let read = self.read_through(term, true, None);
        let read = self.rpn(&read);
        let whole = self.rpn(term);
        for child in term.children() {
            if read != whole && self.rpn(child) == read {
                continue;
            }
            self.written_unpeeled(child, out);
        }
    }

    /// A term with every one-way rule of the standard form applied, parts
    /// first, and nothing put in order: for finding what a lemma's variables
    /// stand for, and nothing else. A defined name is read as what it names
    /// only where `named`.
    pub fn read_through(
        &mut self,
        term: &Term,
        named: bool,
        letters: Option<&Vars>,
    ) -> Term {
        let owned;
        let letters = match letters {
            Some(l) => l,
            None => {
                owned = self.letters_bound(term);
                &owned
            }
        };
        if named {
            if let Some(body) = self.named_body(term, letters) {
                return self.read_through(&body, named, Some(letters));
            }
        }
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        let kids: Vec<Term> = term
            .children()
            .iter()
            .map(|c| self.read_through(c, named, Some(letters)))
            .collect();
        let term = term.with_children(kids);
        if named {
            if let Some(applied) = self.applied_body(&term) {
                return self.read_through(&applied, named, Some(letters));
            }
        }
        for conditional in [false, true] {
            for rule in self.rewrites(conditional).iter() {
                if let Some(bound) =
                    fit(&rule.given, &term, &Binding::new(), &rule.names)
                {
                    if rule.gives.names().iter().all(|n| bound.contains_key(&**n)) {
                        return self.read_through(
                            &rule.gives.substitute(&bound),
                            named,
                            Some(letters),
                        );
                    }
                }
            }
        }
        term
    }

    /// A term with each defined name standing free read as what it names,
    /// and nothing else rewritten: a function applied is left applied.
    pub fn names_read(&self, term: &Term, letters: Option<&Vars>) -> Term {
        let owned;
        let letters = match letters {
            Some(l) => l,
            None => {
                owned = self.letters_bound(term);
                &owned
            }
        };
        if let Some(body) = self.named_body(term, letters) {
            return self.names_read(&body, Some(letters));
        }
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        let n = term.children().len();
        let kids: Vec<Term> = term
            .children()
            .iter()
            .enumerate()
            .map(|(i, c)| {
                if term.label() == Some("cfv") && i == n - 1 {
                    c.clone()
                } else {
                    self.names_read(c, Some(letters))
                }
            })
            .collect();
        term.with_children(kids)
    }

    /// `fit_respelt` of a hypothesis to a line, where a letter the binding
    /// already fixes may come out as the same formula over other bound
    /// letters. A claim made where its bound letter is a fixed name binds
    /// another: inside a block that lets x, "for all x ∈ V, …" is spelt over a
    /// spare letter, and the induction hypothesis it is the consequent of is
    /// not. The line is fitted with the fixed letters left open, and each
    /// must come out the formula it has, or that formula over other bound
    /// letters, which `held_rebound` carries across when the hypothesis is
    /// proved.
    pub(super) fn fit_over_bound(
        &self,
        pattern: &Term,
        held: &Term,
        binding: &Binding,
        variables: &Vars,
        fresh: &Binding,
    ) -> Option<Binding> {
        let filled = self.fit_respelt_in_no_order(
            pattern,
            held,
            &Binding::new(),
            variables,
            fresh,
        )?;
        let agrees = filled.iter().all(|(k, v)| match binding.get(k) {
            Some(had) => {
                let (had, v) = (self.rpn(had), self.rpn(v));
                had == v || self.rebound(&had, &v)
            }
            None => true,
        });
        if !agrees {
            return None;
        }
        let mut out = binding.clone();
        for (k, v) in filled {
            out.entry(k).or_insert(v);
        }
        Some(out)
    }

    /// A lemma reaching a claim written without an identity element its
    /// conclusion has (`SYNTAX.md`, the literal-instance rule): the
    /// conclusion is fitted reading x + 0 as x where the claim has x
    /// (`fit_tidied`), the lemma is applied to that literal instance, and
    /// the instance is carried to the claim (`tidied`).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn as_tidied(
        &mut self,
        label: &str,
        reads: &Term,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let variables = names_of(&self.statement(label));
        let start = seed.cloned().unwrap_or_default();
        let Some(binding) = self.fit_tidied(reads, goal, &start, &variables) else {
            return Ok(Route::no(format!("{label} does not conclude the claim")));
        };
        // A variable a hypothesis decides is taken at that value, which may
        // hold an identity element the claim leaves out: `fsum1p`'s first
        // term is its summand at the bottom of the range.
        let sig = self.sig(label).clone();
        let binding = self.read_off(&sig, binding, &variables);
        let settled = self.instanced(&sig, binding);
        let literal = reads.substitute(&settled);
        let (said, want) = (self.rpn(&literal), self.rpn(goal));
        if said == want {
            return Ok(Route::no(format!("{label} does not conclude the claim")));
        }
        let made =
            take!(self.apply_lemma(label, &literal, scope, facts, step, true, seed)?);
        Ok(match self.tidied(&made, &said, &want, scope, facts)? {
            Some(p) => Built(p),
            None => self.no(
                format!(
                    "{label} concludes {{}} and nothing drops its identity elements"
                ),
                &[&said],
            ),
        })
    }

    /// `fit`, where a pattern's operation may stand with its identity
    /// element in a hole the notation record allows it and the other hole
    /// matched against the term: ( A + C ) against 1 with A := 0.
    pub(super) fn fit_tidied(
        &self,
        pattern: &Term,
        term: &Term,
        binding: &Binding,
        variables: &Vars,
    ) -> Option<Binding> {
        if let Some(found) = fit(pattern, term, binding, variables) {
            return Some(found);
        }
        if pattern.variable().is_some() {
            return None;
        }
        if pattern.label() == term.label()
            && pattern.children().len() == term.children().len()
        {
            let mut at = binding.clone();
            let all = pattern
                .children()
                .iter()
                .zip(term.children())
                .all(|(p, t)| match self.fit_tidied(p, t, &at, variables) {
                    Some(next) => {
                        at = next;
                        true
                    }
                    None => false,
                });
            if all {
                return Some(at);
            }
        }
        for law in &self.identities {
            if pattern.label() != Some(law.constructor.as_str())
                || pattern.children().len() != law.fixed.len() + 2
                || law.fixed.iter().any(|(k, token)| {
                    self.rpn(&pattern.children()[*k]).alone() != Some(token.as_str())
                })
            {
                continue;
            }
            let element = self.to_term(&super::super::field::numeral(law.element));
            for &hole in &law.holes {
                let (unit, kept) = if hole == 0 {
                    (law.places.0, law.places.1)
                } else {
                    (law.places.1, law.places.0)
                };
                // The element is one the instance has, a variable already
                // fixed as it: none is made up to read x as 0 + x.
                let unit = &pattern.children()[unit];
                if unit
                    .names()
                    .iter()
                    .any(|n| variables.contains(n) && !binding.contains_key(&**n))
                {
                    continue;
                }
                let Some(at) = self.fit_tidied(unit, &element, binding, variables)
                else {
                    continue;
                };
                if let Some(found) =
                    self.fit_tidied(&pattern.children()[kept], term, &at, variables)
                {
                    return Some(found);
                }
            }
        }
        None
    }

    /// Whether some part of `term` binds a set variable of its own.
    pub(super) fn binds_a_letter(&self, term: &Term) -> bool {
        if term.variable().is_some() {
            return false;
        }
        let here = term.label() != Some("cv")
            && term.children().iter().any(|c| {
                c.variable()
                    .is_some_and(|v| self.is_setvar(&self.float_of(v)))
            });
        here || term.children().iter().any(|c| self.binds_a_letter(c))
    }

    /// Whether a lemma is in deduction form: it states ( ph -> … ) with ph a
    /// letter, and asks at least one hypothesis, every one of them
    /// ( ph -> … ) under the same ph.
    pub(super) fn in_deduction_form(&self, sig: &Signature, whole: &Term) -> bool {
        if whole.label() != Some("wi") || sig.essentials.is_empty() {
            return false;
        }
        let Some(context) = whole.children()[0].variable() else {
            return false;
        };
        sig.essentials.iter().all(|e| {
            let asked = self.essential(e);
            asked.label() == Some("wi")
                && asked.children()[0].variable() == Some(context)
        })
    }

    /// A claim reached from a lemma that does not conclude it as it stands,
    /// by whichever way fits first: through an existential, as the seed
    /// says, as one conjunct, generalised, in other words, or tidied.
    #[allow(clippy::too_many_arguments)]
    fn reached_across(
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
        let through =
            self.through_existential(label, reads, goal, scope, facts, step, seed)?;
        if !through.is_declined() {
            return Ok(through);
        }
        let seeded = self.as_seeded(label, reads, goal, scope, facts, step, seed)?;
        if !seeded.is_declined() {
            return Ok(seeded);
        }
        let part =
            self.as_conjunct(label, whole, reads, goal, scope, facts, step, seed)?;
        if !part.is_declined() {
            return Ok(part);
        }
        let every = self.as_generalised(label, goal, scope, facts, step, seed)?;
        if !every.is_declined() {
            return Ok(every);
        }
        let other =
            self.in_other_words(label, whole, reads, goal, scope, facts, step, seed)?;
        if !other.is_declined() {
            return Ok(other);
        }
        let tidy = self.as_tidied(label, reads, goal, scope, facts, step, seed)?;
        Ok(if tidy.is_declined() { other } else { tidy })
    }

    /// Apply one set.mm lemma to reach a claim, side conditions and all.
    ///
    /// What a lemma states before the claim it reaches may be an implication
    /// or a biconditional; both are peeled, and which one each was decides
    /// how it is discharged. `seed` is what a `with` target said the lemma's
    /// variables stand for.
    #[allow(clippy::too_many_arguments)]
    pub fn apply_lemma(
        &mut self,
        label: &str,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        crossing: bool,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let sig = self.sig(label).clone();
        let whole = self.statement(label);
        let variables = names_of(&whole);
        let start = seed.cloned().unwrap_or_default();
        let mut antecedents: Vec<Term> = Vec::new();
        let mut joins: Vec<Join> = Vec::new();
        let mut reads = whole.clone();
        // A lemma in deduction form, `mpd`'s ( ph -> ch ) with every
        // hypothesis under ph, assumes ph as the scope it is used in. Its
        // statement is not the claim even where the claim is an "if": ph is
        // the scope, and what the claim says is ch.
        let mut under_context = self.in_deduction_form(&sig, &whole);
        let binding = loop {
            if !std::mem::take(&mut under_context) {
                if let Some(b) = fit(&reads, goal, &start, &variables) {
                    break b;
                }
            }
            if !matches!(reads.label(), Some("wi") | Some("wb")) {
                if crossing {
                    return self.reached_across(
                        label, &whole, &reads, goal, scope, facts, step, seed,
                    );
                }
                return Ok(Route::no(format!("{label} does not conclude the claim")));
            }
            // A biconditional says one thing and reaching it either way is
            // reaching it; tried only where the forward read has already
            // failed, and with the seed, as the forward read is.
            if reads.label() == Some("wb") {
                // Where both sides fit, the claim is the side that says more
                // of it: `A <_ B` fits any inequality, `( C x. A ) <_ ( C x.
                // B )` only a product's. On a tie it is the near side.
                let (near, far) = (&reads.children()[0], &reads.children()[1]);
                if let Some(forward) = fit(far, goal, &start, &variables).filter(|_| {
                    fit(near, goal, &start, &variables).is_none()
                        || constructors(far) > constructors(near)
                }) {
                    antecedents.push(reads.children()[0].clone());
                    joins.push(Join::Iff);
                    reads = reads.children()[1].clone();
                    break forward;
                }
                if let Some(turned) =
                    fit(&reads.children()[0], goal, &start, &variables)
                {
                    antecedents.push(reads.children()[1].clone());
                    joins.push(Join::Turned);
                    reads = reads.children()[0].clone();
                    break turned;
                }
                // The near side may be the claim said differently, and only a
                // full seed can tell.
                if crossing {
                    let near = reads.children()[0].clone();
                    let seeded =
                        self.as_seeded(label, &near, goal, scope, facts, step, seed)?;
                    if !seeded.is_declined() {
                        return Ok(seeded);
                    }
                    // Either side may be the claim written without an
                    // identity element it has (`SYNTAX.md`, "An identity
                    // element goes without saying"): a limit's
                    // |x − c| < δ at c := 0, which the page writes |x| < δ,
                    // reached at the literal instance and carried to the
                    // claim (`as_tidied`).
                    for side in [reads.children()[1].clone(), near] {
                        let tidy = self
                            .as_tidied(label, &side, goal, scope, facts, step, seed)?;
                        if !tidy.is_declined() {
                            return Ok(tidy);
                        }
                    }
                }
                // One way of the biconditional may be the claim.
                if goal.label() == Some("wi") {
                    let taken = self.one_direction(
                        label, &reads, goal, &variables, scope, facts, step, crossing,
                        seed,
                    )?;
                    if !taken.is_declined() {
                        return Ok(taken);
                    }
                }
            }
            antecedents.push(reads.children()[0].clone());
            joins.push(if reads.label() == Some("wb") {
                Join::Iff
            } else {
                Join::Implies
            });
            reads = reads.children()[1].clone();
        };
        let _ = &reads;

        let fitted = self.fit_variables(VariablesAsked {
            label,
            sig: &sig,
            goal,
            scope,
            facts,
            step,
            crossing,
            seed,
            variables: &variables,
            binding,
        })?;
        let Fitted { binding, fresh } = match fitted {
            Staged::Onward(fitted) => fitted,
            Staged::Settled(route) => return Ok(route),
        };
        let scoped = self.scope_of(ScopeAsked {
            label,
            sig: &sig,
            goal,
            scope,
            facts,
            step,
            crossing,
            seed,
            antecedents: &antecedents,
            variables: &variables,
            fresh: &fresh,
            binding,
        })?;
        let Scope {
            binding,
            where_,
            frame,
            known,
        } = match scoped {
            Scoped::In(scope) => scope,
            Scoped::Settled(route) => return Ok(route),
        };
        let binding = self.fit_open_antecedents(OpenAntecedents {
            antecedents: &antecedents,
            binding,
            variables: &variables,
            fresh: &fresh,
            where_: &where_,
            known: &known,
        });
        self.proof_from_lemma(Reached {
            label,
            sig: &sig,
            goal,
            binding,
            antecedents,
            joins,
            where_,
            frame,
            known,
            scope,
            step,
            facts,
        })
    }

    /// What each of a lemma's variables stands for once the lemma's own
    /// hypotheses, the lines the step cites and the letters the claim leaves
    /// free have said what they can; or, where the claim is not what the
    /// lemma concludes at those values, the claim reached some other way.
    pub(super) fn fit_variables(
        &mut self,
        asked: VariablesAsked<'_>,
    ) -> Checked<Staged<Fitted>> {
        let VariablesAsked {
            label,
            sig,
            goal,
            scope,
            facts,
            step,
            crossing,
            seed,
            variables,
            mut binding,
        } = asked;
        // A lemma whose hypothesis says what one of its variables is has
        // already decided it. Where the two disagree the claim is not what
        // the lemma concludes, so the lemma is proved at its own value
        // instead.
        binding = self.read_off(sig, binding, variables);
        let settled = self.instanced(sig, binding.clone());
        if binding
            .iter()
            .any(|(name, stood)| self.rpn(&settled[name]) != self.rpn(stood))
        {
            return self
                .at_its_own_value(label, sig, goal, scope, facts, step, &settled)
                .map(Staged::Settled);
        }
        binding = settled;
        // Two letters the lemma binds and keeps apart, which the claim spells
        // alike, cannot both be the claim's.
        let kinds: IndexMap<&str, &str> = sig
            .floats
            .iter()
            .map(|(t, v)| (v.as_str(), t.as_str()))
            .collect();
        if sig.disjoint.iter().any(|(a, b)| {
            kinds.get(a.as_str()) == Some(&"setvar")
                && kinds.get(b.as_str()) == Some(&"setvar")
                && binding.contains_key(a)
                && binding.contains_key(b)
                && self.rpn(&binding[a]) == self.rpn(&binding[b])
        }) {
            return self
                .letters_apart(label, goal, scope, facts, step, crossing, seed)
                .map(Staged::Settled);
        }
        // A letter the lemma binds and keeps apart from its scope, which the
        // claim never fixes, is given one nothing holds before anything else
        // could lend it one. What the lemma's other variables stand for is
        // still read off the facts, whose letters are their own
        // (`fit_respelt`).
        let before = binding.clone();
        binding = self.letters_unheld(sig, binding);
        // A substitution the lemma asks over one of those letters was worked
        // out above in the lemma's own spelling of it: `gcntshift` asks
        // ( i = j -> ( ps <-> th ) ), and th is ps at j. It is worked out
        // again at the letter j now stands for.
        binding = self.instanced(sig, binding);
        let fresh: Binding = binding
            .iter()
            .filter(|(k, _)| !before.contains_key(*k))
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        // A deduction's hypothesis may bind letters its conclusion never
        // names, each its own: each is the letter the line the step cites for
        // that hypothesis binds. A hypothesis that is a bare letter under the
        // context, as `mpbid` asks ( ph -> ps ), would fit any line, so it is
        // fitted to none and is fixed by the hypotheses that give it a shape.
        // A cited line of several sentences supplies each of them, and a
        // requires line of the step is a line it names as surely, so what
        // it says is offered too: `If b = 0 then c = 0` as a requires line
        // fixes modus ponens's P as it does cited.
        let mut cited: Vec<Term> = match step {
            Some(step) => step
                .just
                .refs
                .iter()
                .filter_map(|r| self.line_written(r, &self.lines))
                .flat_map(|l| conjuncts_of(&self.to_term(&l.claim)))
                .collect(),
            None => Vec::new(),
        };
        if let Some(step) = step {
            for r in &step.requires {
                let node = self.read_one(&r.fact)?;
                let said = self.term(&node)?;
                cited.extend(conjuncts_of(&self.to_term(&said)));
            }
        }
        for text in &sig.essentials {
            let said = self.essential(text);
            if said.label() != Some("wi") || said.children()[0].variable().is_none() {
                continue;
            }
            let said = said.children()[1].clone();
            if said.variable().is_some()
                || said.names().iter().all(|n| binding.contains_key(&**n))
            {
                continue;
            }
            let mut vars = variables.clone();
            vars.extend(said.names().iter().cloned());
            // The hypothesis and each cited line are fitted as the checker
            // reads them, with their identity elements dropped: `2·k·x = x`
            // and `2·k·x = 1·x` both answer ( A x. C ) = ( B x. C ) at
            // B := 1 (SYNTAX.md, "An identity element goes without
            // saying"). Only a letter bound to an identity element is put in
            // the hypothesis, since a letter of the proof may share a name
            // with one of the lemma's.
            let at_identity: Binding = binding
                .iter()
                .filter(|(_, v)| self.is_identity_element(v))
                .map(|(k, v)| (*k, v.clone()))
                .collect();
            let said = self.without_identities(&said.substitute(&at_identity));
            for held in &cited {
                let held = self.without_identities(held);
                if let Some(filled) =
                    self.fit_over_bound(&said, &held, &binding, &vars, &fresh)
                {
                    binding = filled;
                    break;
                }
            }
        }
        Ok(Staged::Onward(Fitted { binding, fresh }))
    }

    /// The scope a lemma is used in, and what the proof being built may rest
    /// on there; or, where no scope is allowed or an outer frame is the only
    /// one, the claim reached some other way.
    pub(super) fn scope_of(&mut self, asked: ScopeAsked<'_>) -> Checked<Scoped> {
        let ScopeAsked {
            label,
            sig,
            goal,
            scope,
            facts,
            step,
            crossing,
            seed,
            antecedents,
            variables,
            fresh,
            mut binding,
        } = asked;
        // The scope is where a lemma's disjointness conditions can forbid it,
        // so it is chosen before anything is built.
        let (mut where_, mut frame) = self.allowed(sig, &binding);
        if where_.is_declined() {
            // Which scope is allowed depends on what the variables stand
            // for, so what the facts decide is read and the question asked
            // again — only here, because binding early changes which fact
            // answers an antecedent.
            let keys = facts.keys();
            for slot in antecedents {
                if slot.variable().is_some()
                    || slot.names().iter().all(|n| binding.contains_key(&**n))
                {
                    continue;
                }
                for held in &keys {
                    if let Some(filled) = fit_respelt(
                        slot,
                        &self.to_term(held),
                        &binding,
                        variables,
                        fresh,
                    ) {
                        binding = filled;
                        break;
                    }
                }
            }
            (where_, frame) = self.allowed(sig, &binding);
            if let Declined(why) = where_ {
                // The claim's own bound letter may be what every frame
                // spells.
                return self
                    .over_other_letters(
                        label, goal, scope, facts, step, crossing, seed, why,
                    )
                    .map(Scoped::Settled);
            }
        }
        // An outer frame knows less than the step does: lines written inside
        // the inner one are not there. Where the claim's own bound letter is
        // what the inner scope spells, the lemma is tried there over another
        // letter first, and the outer frame is the way taken only if that
        // does not reach the claim.
        if frame.is_some_and(|f| f + 1 < self.frames.len()) {
            let why = Decline::new("an inner scope spells the claim's letter");
            let moved = self.over_other_letters(
                label, goal, scope, facts, step, crossing, seed, why,
            )?;
            if !moved.is_declined() {
                return Ok(Scoped::Settled(moved));
            }
        }
        let Built(where_) = where_ else {
            unreachable!("an allowed scope")
        };
        let frame = frame.expect("the frame of an allowed scope");
        let at_frame = self.frames_facts(frame, facts);
        let known = self.known_implied(step, &where_, &at_frame)?;
        Ok(Scoped::In(Scope {
            binding,
            where_,
            frame,
            known,
        }))
    }

    /// The binding once each antecedent the claim leaves open is matched
    /// against what the proof being built may rest on, the one whose letters
    /// are most fixed first.
    pub(super) fn fit_open_antecedents(
        &mut self,
        asked: OpenAntecedents<'_>,
    ) -> Binding {
        let OpenAntecedents {
            antecedents,
            mut binding,
            variables,
            fresh,
            where_,
            known,
        } = asked;
        // A bare `Z e. B` with Z open is answered by any line putting
        // anything in B, so every such conjunct is matched after the rest.
        let loose: Vec<Term> = antecedents
            .iter()
            .filter(|s| s.variable().is_none())
            .flat_map(conjuncts_of)
            .filter(|p| {
                p.label() == Some("wcel")
                    && p.children()[0]
                        .variable()
                        .is_some_and(|v| !binding.contains_key(v))
            })
            .collect();
        // What fills an antecedent is only what the proof being built may
        // rest on (`frames_facts`): a line the step does not name cannot
        // decide a class the lemma leaves open.
        let known_keys = known.keys();
        // Each antecedent is matched in turn, the one whose letters are most
        // fixed already first: with ph fixed by the claim, `orel2`'s
        // ( ph \/ ps ) is answered by one line where ( -. ps ) is answered
        // by any negation. The loose conjuncts come last.
        let mut pending: Vec<&Term> = antecedents.iter().collect();
        let mut loose_done = false;
        loop {
            let slot = match most_fixed(&mut pending, &binding) {
                Some(s) => Some(s),
                None if !loose_done => {
                    loose_done = true;
                    None
                }
                None => break,
            };
            let pieces: Vec<Term> = match slot {
                None => loose.clone(),
                Some(s) if s.names().iter().all(|n| binding.contains_key(&**n)) => {
                    continue
                }
                Some(s) if s.variable().is_some() => {
                    binding.insert(s.variable_symbol().unwrap(), self.to_term(where_));
                    continue;
                }
                // An antecedent a line the step has says whole is answered by
                // that line, which fixes its open letters together. Matched a
                // conjunct at a time, a triangle's `-. Q = R` takes R from
                // whichever disequality of Q comes first.
                Some(s) => {
                    let wholes =
                        self.fits_whole(s, &known_keys, &binding, variables, fresh);
                    let whole = self.fit_answering_rest(
                        wholes,
                        &pending,
                        &binding,
                        &known_keys,
                        variables,
                        fresh,
                    );
                    match whole {
                        Some(filled) => {
                            binding = filled;
                            Vec::new()
                        }
                        None => self
                            .open_pieces(
                                s,
                                &pending,
                                &known_keys,
                                &mut binding,
                                variables,
                                fresh,
                            )
                            .into_iter()
                            .filter(|p| !loose.iter().any(|one| one.same_object(p)))
                            .collect(),
                    }
                }
            };
            // What the lemma concludes need not fix everything it asks, so an
            // antecedent that is still open is matched against something the
            // step already has, one conjunct at a time.
            for (i, piece) in pieces.iter().enumerate() {
                if piece.names().iter().all(|n| binding.contains_key(&**n)) {
                    continue;
                }
                // What is still to be matched: the pieces after this one and
                // the antecedents after this one.
                let rest: Vec<&Term> = pieces[i + 1..]
                    .iter()
                    .chain(pending.iter().copied())
                    .collect();
                let mut fits: Vec<Binding> = Vec::new();
                for held in &known_keys {
                    if let Some(filled) = self.fit_respelt_in_no_order(
                        piece,
                        &self.to_term(held),
                        &binding,
                        variables,
                        fresh,
                    ) {
                        fits.push(filled);
                    }
                }
                let filled_any = !fits.is_empty();
                if let Some(chosen) = self.fit_answering_rest(
                    fits,
                    &rest,
                    &binding,
                    &known_keys,
                    variables,
                    fresh,
                ) {
                    binding = chosen;
                }
                if !filled_any {
                    // Or as the standard form reads the line.
                    let mut read: Vec<Binding> = Vec::new();
                    for held in &known_keys {
                        let fact = self.to_term(held);
                        if let Some(filled) =
                            self.fits_as(piece, &fact, variables, Some(&binding))
                        {
                            read.push(filled);
                        }
                    }
                    if let Some(chosen) = self.fit_answering_rest(
                        read,
                        &rest,
                        &binding,
                        &known_keys,
                        variables,
                        fresh,
                    ) {
                        binding = chosen;
                    }
                }
            }
            if let Some(slot) = slot {
                for open in sethood(slot, &binding) {
                    binding.insert(open, self.to_term(&t!("cvv")));
                }
            }
        }
        binding
    }

    /// The proof of a claim from a lemma whose antecedents are fitted: each
    /// essential hypothesis proved, the lemma applied at the binding, and
    /// each antecedent discharged in turn from the claim outward.
    pub(super) fn proof_from_lemma(
        &mut self,
        reached: Reached<'_>,
    ) -> Checked<Route<Proof>> {
        let Reached {
            label,
            sig,
            goal,
            binding,
            antecedents,
            joins,
            where_,
            frame,
            known,
            scope,
            step,
            facts,
        } = reached;
        let mut asked_all = Vec::new();
        for e in &sig.essentials {
            let asked = self.essential(e).substitute(&binding);
            asked_all.push(self.prove_essential(&asked, &where_, &known)?);
        }
        let mut essentials = Vec::new();
        for one in asked_all {
            essentials.push(take!(one));
        }
        let mut proof = self.b.ap(
            label,
            &self.spelt(&binding),
            &essentials.iter().collect::<Vec<_>>(),
        );
        let goal_rpn = self.rpn(goal);
        if antecedents.is_empty() {
            // The lemma asks nothing, so it states the claim outright and has
            // to be brought into the scope the step sits in.
            let carried = pf!(self.b; goal_rpn, where_, proof, "a1i");
            return Ok(Built(self.carry(carried, &goal_rpn, frame)));
        }
        let (mut where_, mut frame, mut known) = (where_, frame, known);
        let mut carried = false;
        let mut stood_under = false;
        for (i, slot) in antecedents.iter().enumerate() {
            let asks = slot.substitute(&binding);
            let asks_rpn = self.rpn(&asks);
            let mut is_scope = asks_rpn == where_;
            // Standing under a scope rests on every line it is made of. Where
            // the step does not name them all, as where a letter's membership
            // is said once and its line not cited, the formula is settled a
            // part at a time like any other.
            if is_scope && slot.variable().is_none() {
                if let Some(resting) = self.resting.clone() {
                    let more = self.scope_origin(&where_, &known)?;
                    if !more.iter().all(|o| may_rest_on(&resting, o)) {
                        is_scope = false;
                    }
                }
            }
            // A variable slot is the context a deduction-form lemma is stated
            // in, and uses nothing; a formula the scope happens to be is what
            // the lemma asks, and uses all of it.
            stood_under = stood_under || (is_scope && slot.variable().is_none());
            // Only a first slot the lemma implies from is the scope's own
            // place, so that the lemma then reads `scope -> claim` as it
            // stands; one it states a biconditional with, or asks after
            // another, is discharged as any is, by the scope itself (`id`).
            if is_scope && i == 0 && joins[i] == Join::Implies {
                carried = true;
                continue; // the deduction slot
            }
            let mut rest = goal_rpn.clone();
            for (later, join) in antecedents[i + 1..].iter().zip(&joins[i + 1..]).rev()
            {
                let said = self.rpn(&later.substitute(&binding));
                if said != where_ {
                    // A biconditional crossed the other way puts the claim on
                    // the left.
                    rest = if *join == Join::Turned {
                        t!(rest, said, "wb")
                    } else {
                        t!(said, rest, join_token(*join))
                    };
                }
            }
            // What decides the fold is whether what has been built so far
            // states its claim outright or states it under the scope.
            let mut first = proof.last() == label && !carried;
            let (mut x, mut y) = if joins[i] == Join::Turned && !first {
                (rest.clone(), asks_rpn.clone())
            } else {
                (asks_rpn.clone(), rest.clone())
            };
            // A "there is" the lemma asks can be given by an instance a line
            // the step cites names; only then is the step passed.
            let instanced = self
                .parts(&asks_rpn)
                .iter()
                .any(|p| self.to_term(p).label() == Some("wrex"));
            // A hypothesis of the cited record, by the fact the checker
            // recorded as supplying it (`hypotheses_given`).
            let recorded = match self.hypotheses_given.clone() {
                Some(given) if where_ == *scope => {
                    self.held(&given, &asks_rpn, &where_)?
                }
                _ => None,
            };
            let mut under = if is_scope {
                Built(pf!(self.b; where_, "id"))
            } else if let Some(p) = recorded {
                Built(p)
            } else if instanced && step.is_some() {
                let lines = self.lines.clone();
                self.settle(&asks, &where_, &known, 3, step, Some(&lines))?
            } else {
                self.settle(&asks, &where_, &known, 3, None, None)?
            };
            // An antecedent the lemma's frame does not hold may be one an
            // inner assumption gives, as a case that a sum is 0 gives a lemma
            // that keeps the sum's letter out of its scope: what is built so
            // far is carried in, and this antecedent and the rest are
            // discharged there.
            if under.is_declined() && frame + 1 < self.frames.len() {
                let mut remaining = goal_rpn.clone();
                for (later, join) in antecedents[i..].iter().zip(&joins[i..]).rev() {
                    let said = self.rpn(&later.substitute(&binding));
                    if said != where_ {
                        remaining = if *join == Join::Turned {
                            t!(remaining, said, "wb")
                        } else {
                            t!(said, remaining, join_token(*join))
                        };
                    }
                }
                let under_frame = if first {
                    pf!(self.b; remaining, where_, proof, "a1i")
                } else {
                    proof.clone()
                };
                proof = self.carry(under_frame, &remaining, frame);
                frame = self.frames.len() - 1;
                where_ = self.frames[frame].scope.clone();
                known = self.known_implied(step, &where_, facts)?;
                carried = true;
                first = false;
                (x, y) = if joins[i] == Join::Turned {
                    (rest.clone(), asks_rpn.clone())
                } else {
                    (asks_rpn.clone(), rest.clone())
                };
                under = self.settle(&asks, &where_, &known, 3, None, None)?;
            }
            let under = take!(under);
            proof = pf!(self.b; where_, x, y, under, proof, discharge(joins[i], first));
        }
        if stood_under {
            // An antecedent that is the scope is supplied by standing under
            // it, not by a fact looked up, so it rests on everything the scope
            // says.
            let more = self.scope_origin(&where_, &known)?;
            proof = proof.resting(more);
        }
        Ok(Built(self.carry(proof, &goal_rpn, frame)))
    }

    /// A lemma proved at the value its own hypothesis gives it, and the
    /// claim settled from that, where the theorem's own facts are in scope.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn at_its_own_value(
        &mut self,
        label: &str,
        sig: &Signature,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        settled: &Binding,
    ) -> Checked<Route<Proof>> {
        let _ = sig;
        let mut reads = self.statement(label);
        while reads.label() == Some("wi") {
            reads = reads.children()[1].clone();
        }
        let said = reads.substitute(settled);
        let proof =
            take!(self.apply_lemma(label, &said, scope, facts, step, false, None)?);
        let known = facts.copy();
        let said = self.rpn(&said);
        self.know(&known, said.clone(), proof.clone());
        let settled = self.settle(goal, scope, &known, 3, None, None)?;
        if !settled.is_declined() {
            return Ok(settled);
        }
        // The value may hold an identity element the claim leaves out: fsum1's
        // one term, the summand at k := 0, has x^(0 − 0) where the claim
        // writes x^0 (`SYNTAX.md`, the literal-instance rule).
        let want = self.rpn(goal);
        Ok(match self.tidied(&proof, &said, &want, scope, facts)? {
            Some(p) => Built(p),
            None => settled,
        })
    }

    /// One hypothesis a lemma states in full rather than asking for.
    pub fn prove_essential(
        &mut self,
        want: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let kids = want.children();
        if want.label() == Some("wceq")
            && kids.len() == 2
            && self.rpn(&kids[0]) == self.rpn(&kids[1])
        {
            // A lemma that names a thing asks for the naming as it stands
            // rather than under the scope.
            return Ok(Built(pf!(self.b; self.rpn(&kids[0]), "eqid")));
        }
        // And the very map spelt over another letter: the same naming,
        // closed.
        if want.label() == Some("wceq") && kids.len() == 2 && !self.is_wff(&kids[0]) {
            if let Some(renamed) = self.class_alpha(&kids[0], &kids[1])? {
                return Ok(Built(renamed));
            }
        }
        if want.label() != Some("wi") {
            return self.settle(want, scope, facts, 3, None, None);
        }
        let (left, right) = (&kids[0], &kids[1]);
        let under = self.rpn(left);
        if under == self.rpn(right) {
            return Ok(Built(pf!(self.b; under, "id")));
        }
        // Two sides alike say one thing whatever is assumed: a renaming whose
        // body does not hold the letter it renames asks this.
        let sides = right.children();
        if sides.len() == 2 && self.rpn(&sides[0]) == self.rpn(&sides[1]) {
            let one = self.rpn(&sides[0]);
            let alike = match right.label() {
                Some("wb") => Some(self.b.ap("biid", &binds! {"ph" => &one}, &[])),
                Some("wceq") => Some(self.b.ap("eqid", &binds! {"A" => &one}, &[])),
                _ => None,
            };
            if let Some(alike) = alike {
                return Ok(Built(pf!(self.b; self.rpn(right), under, alike, "a1i")));
            }
        }
        // A lemma may state its instance rather than ask for it, and wants
        // the body before and after tied together: the walk between them is
        // the same for terms and for formulas.
        if left.label() == Some("wceq")
            && matches!(right.label(), Some("wb") | Some("wceq"))
            && left.children()[0].label() == Some("cv")
        {
            let was = self.rpn(&left.children()[0]);
            let now = self.rpn(&left.children()[1]);
            let held = Facts::new();
            let id = pf!(self.b; under, "id");
            self.know(&held, under.clone(), id);
            let leaf = Leaf::Rows(vec![Row::Assumed {
                was,
                now,
                under: under.clone(),
            }]);
            return self.congruence(
                &right.children()[0],
                &right.children()[1],
                &under,
                &held,
                None,
                &leaf,
            );
        }
        if under == *scope {
            return self.settle(right, scope, facts, 3, None, None);
        }
        if left.label() == Some("wa") && self.rpn(&left.children()[0]) == *scope {
            let extra = self.rpn(&left.children()[1]);
            let weaken = pf!(self.b; scope, extra, "simpl");
            let wider = Facts::new();
            for (k, v) in facts.entries() {
                let carried = pf!(self.b; under, scope, k, weaken, v, "syl");
                self.know(&wider, k, carried);
            }
            let simpr = pf!(self.b; scope, extra, "simpr");
            self.know(&wider, extra.clone(), simpr);
            // A line said of every index may be a requires line of the step,
            // read here and not by the search below.
            let named = wider.copy();
            for (claim, w) in self.written.entries() {
                if let Some(lifted) = self.lifted_to(&claim, &w.proof, &w.at, scope) {
                    if !self.holds(&named, &claim) {
                        let carried =
                            pf!(self.b; under, scope, claim, weaken, lifted, "syl");
                        self.know(&named, claim, carried);
                    }
                }
            }
            if let Some(taken) =
                self.at_the_index(&left.children()[1], right, &under, &named)?
            {
                return Ok(Built(taken));
            }
            // One level deeper than `settle`'s default: what is asked of an
            // index is asked through the range it runs over.
            return self.settle(right, &under, &wider, 4, None, None);
        }
        self.settle(right, &under, &Facts::new(), 3, None, None)
    }

    /// What a lemma asks of each index, from a line saying it of all: that is
    /// the line read at k, once k is in the range, which `rspcv` does. None
    /// where no such line is in hand, which is not a decline: the caller
    /// settles what is asked another way.
    pub(super) fn at_the_index(
        &mut self,
        member: &Term,
        right: &Term,
        under: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        if member.label() != Some("wcel") || member.children()[0].label() != Some("cv")
        {
            return Ok(None);
        }
        let index = member.children()[0].clone();
        let want = self.rpn(right);
        for (said, proof) in facts.entries() {
            let line = self.to_term(&said);
            if line.label() != Some("wral") || line.children()[1].variable().is_none() {
                continue;
            }
            let (body, letter, over) = (
                line.children()[0].clone(),
                line.children()[1].clone(),
                line.children()[2].clone(),
            );
            let mut put = Binding::new();
            put.insert(
                letter.variable_symbol().unwrap(),
                index.children()[0].clone(),
            );
            if self.rpn(&body.substitute(&put)) != want {
                continue;
            }
            let inside = t!(self.rpn(&index), self.rpn(&over), "wcel");
            let Built(there) =
                self.settle(&self.to_term(&inside), under, facts, 3, None, None)?
            else {
                continue;
            };
            let reads = self.to_term(&t!(
                t!(self.rpn(&letter), "cv", self.rpn(&index), "wceq"),
                t!(self.rpn(&body), want, "wb"),
                "wi"
            ));
            // The line may bind the index's own letter, and then the body at
            // the index is the body: `rsp` reads it there.
            let read = if self.rpn(&body) == want {
                let rsp = self.b.ap(
                    "rsp",
                    &binds! {"ph" => &want, "x" => self.rpn(&letter), "A" => self.rpn(&over)},
                    &[],
                );
                self.b.ap(
                    "com12",
                    &binds! {"ph" => &said, "ps" => &inside, "ch" => &want},
                    &[&rsp],
                )
            } else {
                let Built(tied) = self.prove_essential(&reads, under, facts)? else {
                    continue;
                };
                self.b.ap(
                    "rspcv",
                    &binds! {"ph" => self.rpn(&body), "ps" => &want, "x" => self.rpn(&letter),
                    "A" => self.rpn(&index), "B" => self.rpn(&over)},
                    &[&tied],
                )
            };
            let carried =
                pf!(self.b; under, inside, t!(said, want, "wi"), there, read, "syl");
            return Ok(Some(pf!(self.b; under, said, want, proof, carried, "mpd")));
        }
        Ok(None)
    }

    /// A claim `P → Q` from a lemma saying `Q ↔ P`, or `P ↔ Q`: the
    /// biconditional is proved at what the claim fixes, and the way the
    /// claim goes is taken.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn one_direction(
        &mut self,
        label: &str,
        reads: &Term,
        goal: &Term,
        variables: &Vars,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        crossing: bool,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let (left, right) = (reads.children()[0].clone(), reads.children()[1].clone());
        let start = seed.cloned().unwrap_or_default();
        for ((first, then), fold) in [
            ((&left, &right), rules::ONE_WAY.0),
            ((&right, &left), rules::ONE_WAY.1),
        ] {
            let Some(fixed) = fit(
                &Term::apply("wi", vec![first.clone(), then.clone()]),
                goal,
                &start,
                variables,
            ) else {
                continue;
            };
            let said = reads.substitute(&fixed);
            let both = take!(self.apply_lemma(
                label,
                &said,
                scope,
                facts,
                step,
                crossing,
                Some(&fixed)
            )?);
            let (l, r) = (
                self.rpn(&left.substitute(&fixed)),
                self.rpn(&right.substitute(&fixed)),
            );
            return Ok(Built(pf!(self.b; scope, l, r, both, fold)));
        }
        Ok(Route::no(format!("neither way of {label} is the claim")))
    }
}
