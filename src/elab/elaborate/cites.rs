//! Citing a claim's reasons.

use super::*;

impl<'a> Elaborator<'a> {
    /// An existence claim shown by naming something that answers it: the
    /// witness is the value the checker read the step as showing, and the
    /// lines the step cites say the claim's body of it.
    pub(super) fn exhibit(
        &mut self,
        step: &Step,
        node: &Node,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let whole = self.to_term(term);
        if whole.label() != Some("wrex") {
            return Err(
                self.unreached(step.line, "an exhibit that claims no existence")
            );
        }
        // A claim may quantify over more than one name, and exhibiting a
        // witness for each is what `exhibited` does.
        if whole.children()[0].label() == Some("wrex") {
            let supplied = self.supplied(Some(step), scope, facts)?;
            self.cited_parts(step, scope, &supplied, lines)?;
            return self.exhibited(step, &whole, scope, &supplied, lines);
        }
        let (mut body, domain) =
            (whole.children()[0].clone(), whole.children()[2].clone());
        // The name the text quantifies under and the variable it stands for
        // are two different things.
        let said = node.children[0].text;
        let mut stands = t!(self.binder_var(&said)?, "cv");
        // The witness is the value the checker read the step as showing.
        let values = self.exhibited_here(step)?;
        let Some(witness) = values.get(&stands).cloned() else {
            return Err(self.unreached(
                step.line,
                "the checker reads no value for the letter this exhibit binds",
            ));
        };
        // The witness may be the very letter the claim binds, so the claim is
        // exhibited under a letter nothing holds and renamed back.
        let binder = self.binder_var(&said)?;
        let mut apart = None;
        let mut renamed = None;
        if witness.has(&binder) {
            let Some(letter) = self.unheld(&[&whole, &self.to_term(&witness)]) else {
                return Err(
                    self.defect(step.line, "no letter left to exhibit the witness by")
                );
            };
            let spare = self.rpn(&letter).to_string();
            stands = t!(spare, "cv");
            let Some(bound) = whole.children()[1].variable() else {
                return Err(self.unreached(
                    step.line,
                    "the \"there is\" this exhibit claims binds no letter",
                ));
            };
            let mut put = Binding::new();
            put.insert(Symbol::of(bound), letter.clone());
            body = body.substitute(&put);
            renamed = Some(Term::apply(
                "wrex",
                vec![body.clone(), letter, domain.clone()],
            ));
            apart = Some(spare);
        }
        let at = t!(stands, witness, "wceq");
        // `there is s ∈ S` says nothing of s: its body is true, and true of
        // any witness.
        let (here, instance) = if let [_, _, said_of] = node.children.as_slice() {
            let shape = self.names_kept(|me| -> Checked<Node> {
                me.names.insert(said.to_string(), stands.clone());
                me.freeze(said_of)
            })?;
            let identity = pf!(self.b; at, "id");
            match self.rewrite(&shape, &stands, &witness, &at, &identity)? {
                Built(made) => made,
                Declined(d) => {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "the witness stands nowhere in the claim: {}",
                            self.say(&d)
                        ),
                    ));
                }
            }
        } else {
            let truth = self.rpn(&body);
            let same = self
                .b
                .ap("biidd", &binds! {"ph" => &at, "ps" => &truth}, &[]);
            (truth, same)
        };
        let known = self.supplied(Some(step), scope, facts)?;
        self.cited_parts(step, scope, &known, lines)?;
        let member = t!(witness, self.rpn(&domain), "wcel");
        // What is left is that the witness lies in the domain and that the
        // body holds of it, and both are the text's to supply.
        let mut shown = Vec::new();
        for want in [&member, &here] {
            // The body at the witness may hold an identity element the line
            // naming the witness leaves out, and is that line carried to it.
            match self.settle_or_bare(&self.to_term(want), scope, &known, None, None)? {
                Built(p) => shown.push(p),
                Declined(d) => {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "exhibiting that witness wants {}, which step {} does not supply: {}",
                            self.render(want),
                            step.number,
                            self.say(&d)
                        ),
                    ));
                }
            }
        }
        let spare = apart.clone().unwrap_or(binder);
        let claimed = match &renamed {
            Some(r) => self.rpn(r),
            None => term.clone(),
        };
        let both = pf!(self.b; scope, member, here, shown[0], shown[1], "jca");
        let made = pf!(self.b; scope, t!(member, here, "wa"), claimed, both,
            self.rpn(&body), here, spare, witness, self.rpn(&domain), instance, "rspcev", "syl");
        let Some(renamed) = renamed else {
            return Ok(Built(made));
        };
        let Some(back) = self.renaming(&renamed, &whole)? else {
            return Err(self.defect(
                step.line,
                "the renamed claim does not read back as the claim",
            ));
        };
        Ok(Built(self.b.ap(
            "sylib",
            &binds! {"ph" => scope, "ps" => &claimed, "ch" => term},
            &[&made, &back],
        )))
    }

    /// An existence claim with the equation under its quantifiers turned
    /// round, where a definition's lemma writes it the other way from the
    /// page (`targets::unfolding`).
    pub(super) fn body_turned(term: &Term) -> Term {
        if term.label() == Some("wrex") {
            let mut kids = term.children().to_vec();
            kids[0] = Self::body_turned(&kids[0]);
            return Term::apply("wrex", kids);
        }
        if term.label() == Some("wceq") && term.children().len() == 2 {
            return Term::apply(
                "wceq",
                vec![term.children()[1].clone(), term.children()[0].clone()],
            );
        }
        term.clone()
    }

    /// A definition used the other way: its right side, an existence claim
    /// with as many witnesses as it quantifies over, is proved from the lines
    /// the step names as `exhibit` proves one (`witnessed`), and the
    /// definition folds it into the claim.
    pub(super) fn conclude(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let head = step.just.head.to_string();
        // The values are read in the proof's names, before any letter of
        // the definition is given one: `n := d, d := a` gives n the proof's
        // d, not the definition's.
        let values = self.instantiated(&step.just)?;
        let subject = self.subject_given(&head, &values, step.line)?;
        let Item::Record(cited) = self.item_cited(&head)? else {
            panic!("{head} is a definition of the database");
        };
        // Each letter of the definition is what the citation makes it,
        // `matched_here`: the g of `u ∈ gH` is the element the step's claim
        // writes there, whatever the proof calls it.
        let mut matched = Vec::new();
        // A letter the citation makes a rule, E := n ↦ 2n in set-image, has
        // no term of its own: the right side is read with the rule applied
        // where it applies the letter (`citing::filled`).
        let mut rules = crate::matching::Binding::new();
        for (name, node) in self.matched_here(step, cited)? {
            if node.notation() == crate::notations::PROPERTY_OF {
                rules.insert(name, node);
            } else {
                matched.push((name, self.term(&node)?));
            }
        }
        let read_as: IndexMap<String, Rpn> = matched
            .iter()
            .map(|(name, term)| (name.to_string(), term.clone()))
            .collect();
        let (lemma, flipped, right, letter) =
            self.names_kept(|me| -> Checked<(String, bool, Rpn, String)> {
                for (name, term) in matched {
                    me.names.insert(name.to_string(), term);
                }
                // A definition may name more than the thing it is about.
                for (name, term) in values {
                    me.names.insert(name, term);
                }
                let item = cited;
                let (lemma, flipped) = targets::unfolding(item);
                let Some(lemma) = lemma else {
                    return Err(
                        me.defect(me.at, format!("{head} has no metamath-proof field"))
                    );
                };
                let node = me.in_its_names(Item::Record(item), |me| {
                    me.read_one(&item.stated()[0])
                })?;
                let left = node.children[0].clone();
                let right = crate::citing::filled(
                    &node.children[1],
                    &rules,
                    &me.item_library().ctx,
                );
                me.names
                    .insert(left.leftmost().text.to_string(), subject.clone());
                // Each name the right side binds is a letter nothing in the
                // proof holds and the subject does not spell (`unheld_for`, as
                // the renaming rule gives one), given for this reading only.
                let mut bound = Vec::new();
                let mut rest = vec![right.clone()];
                while let Some(node) = rest.pop() {
                    if let Some(held) = me.binders.get(&node.notation()) {
                        for &at in held {
                            if node.children[at].is_name() {
                                bound.push(node.children[at].text);
                            }
                        }
                    }
                    rest.extend(node.children.iter().cloned());
                }
                let Some(letters) = me.unheld_for(bound, &[&me.to_term(&subject)])
                else {
                    return Err(me.defect(
                        step.line,
                        "no letter left to read the definition by",
                    ));
                };
                let kept = me.bound_as.clone();
                for (name, letter) in &letters {
                    me.bound_as
                        .insert(name.to_string(), me.rpn(letter).to_string());
                }
                let read = me.term(&right);
                me.bound_as = kept;
                Ok((lemma, flipped, read?, left.leftmost().text.to_string()))
            })?;
        // Its equation faces the way the lemma writes it.
        let mut whole = self.to_term(&right);
        if flipped {
            whole = Self::body_turned(&whole);
        }
        let ex = self.rpn(&whole);
        // The witnesses are the checker's, read of what its citation makes
        // the subject; folded of another, no line the step cites names one.
        if let Some(was) = read_as.get(&letter).filter(|was| **was != subject) {
            return Err(self.defect(
                step.line,
                format!(
                    "no cited line names a witness for {}: {head} is folded of {}, and the lines say it of {}",
                    self.render(&ex),
                    self.render(&subject),
                    self.render(was)
                ),
            ));
        }
        let (var, over) = (
            self.rpn(&whole.children()[1]).to_string(),
            self.rpn(&whole.children()[2]),
        );
        let supplied = self.supplied(Some(step), scope, facts)?;
        let p_ex = take!(self.witnessed(step, &whole, scope, &supplied, lines)?);
        let (made, _) = take!(self.unfolding(
            step,
            &lemma,
            term,
            Some(&ex),
            Some(&var),
            Some(&over),
            scope,
            facts,
            None
        )?);
        Ok(Built(pf!(self.b; scope, term, ex, p_ex, made, "mpbird")))
    }

    /// `by_clause`, with an equation one claim either way round, as the
    /// checker reads an item's conclusion (`citing::either_way`): `b = a` is
    /// what an item concluding `a = b` gives, turned. A "there is" the
    /// clauses give together at the witness the `with` target names is
    /// assembled as `cite_item` assembles it for an obtain: completeness's
    /// "there is c ∈ ℝ with c is a least upper bound of S" from suprcl,
    /// suprub and suprleub at sup S.
    pub(super) fn by_clause_either_way(
        &mut self,
        labels: &[String],
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        step: &Step,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let found = self.by_clause(labels, term, scope, facts, step, seed)?;
        if !found.is_declined() {
            return Ok(found);
        }
        if let Built(p) = self.by_lemmas(labels, term, scope, facts, step, seed)? {
            return Ok(Built(p));
        }
        let Some((turned, flip)) = self.turned_claim(term) else {
            return Ok(found);
        };
        match self.by_clause(labels, &turned, scope, facts, step, seed)? {
            Built(p) => {
                let Sides { left, right } = self.equation_sides(&turned);
                Ok(Built(pf!(self.b; scope, left, right, p, flip)))
            }
            Declined(_) => Ok(found),
        }
    }

    /// `by_clause_either_way`, and where no clause reaches the claim, the
    /// instance of the item the checker compared it with: a claim that
    /// leaves out an identity element the instance has is that instance
    /// (`SYNTAX.md`, "An identity element goes without saying"), so the
    /// instance is reached and carried to the claim with its identity
    /// elements dropped (`tidied`). `q·N = A` from mod-remainder at r := 0,
    /// whose instance is q·N + 0 = A.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn by_clause_or_instance(
        &mut self,
        item: &'a Record,
        labels: &[String],
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        step: &Step,
        seed: &Binding,
    ) -> Checked<Route<Proof>> {
        let found =
            self.by_clause_either_way(labels, term, scope, facts, step, Some(seed))?;
        if !found.is_declined() {
            return Ok(found);
        }
        let bare =
            |me: &Self, rpn: &Rpn| me.rpn(&me.without_identities(&me.to_term(rpn)));
        let goal = bare(self, term);
        // A biconditional is reached a side at a time, as a step citing it
        // claims one side from the other.
        let mut instances = Vec::new();
        for said in self.concluded_here(step, item)? {
            let whole = self.to_term(&said);
            if whole.label() == Some("wb") {
                instances.extend(whole.children().iter().map(|side| self.rpn(side)));
            }
            instances.push(said);
        }
        for instance in instances {
            let bare_instance = bare(self, &instance);
            if instance == *term
                || (bare_instance != goal
                    && !self.rebound(&bare_instance, &goal)
                    && !self.reorders(&instance, term)
                    && !self.one_with_names_read(&instance, term)
                    && !self.one_with_names_read(&bare_instance, &goal)
                    && !self.one_read_through(&instance, term))
            {
                continue;
            }
            let Built(reached) = self.by_clause_either_way(
                labels,
                &instance,
                scope,
                facts,
                step,
                Some(seed),
            )?
            else {
                continue;
            };
            if let Some(p) = self.reached(&reached, &instance, term, scope, facts)? {
                return Ok(Built(p));
            }
        }
        Ok(found)
    }

    /// An equation or disequation with its sides the other way round, and
    /// the lemma that turns a proof of it back: `B = A` and `eqcomd`, `B ≠ A`
    /// and `necomd`, or `¬ B = A`, as the page's ≠ is read, and `neqcomd`.
    /// None for any other claim.
    pub(crate) fn turned_claim(&self, term: &Rpn) -> Option<(Rpn, &'static str)> {
        let whole = self.to_term(term);
        let flip = match whole.label() {
            Some("wceq") => "eqcomd",
            Some("wne") => "necomd",
            Some("wn") if whole.children()[0].label() == Some("wceq") => "neqcomd",
            _ => return None,
        };
        let Sides { left, right } = self.equation_sides(term);
        Some(match whole.label()? {
            "wn" => t!(t!(right, left, "wceq"), "wn"),
            label => t!(right, left, label),
        })
        .map(|turned| (turned, flip))
    }

    /// The two sides of an equation or a disequation, as the lemma that
    /// turns it takes them: of a negated equation, the equation's.
    pub(crate) fn equation_sides(&self, claim: &Rpn) -> Sides {
        let mut whole = self.to_term(claim);
        if whole.label() == Some("wn") {
            whole = whole.children()[0].clone();
        }
        Sides {
            left: self.rpn(&whole.children()[0]),
            right: self.rpn(&whole.children()[1]),
        }
    }

    /// A theorem cited: either set.mm supplies it or this corpus does.
    pub(super) fn cite(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let _ = lines;
        match self.item_cited(&step.just.head.to_string())? {
            Item::Theorem(t) => {
                self.cite_corpus(step, term, scope, facts, t).map(Built)
            }
            Item::Record(r) => self.cite_library(step, term, scope, facts, r),
        }
    }

    /// Apply the set.mm theorem the item's `target` names, its variables read
    /// off matching its conclusion against the claim, or given by the item's
    /// `with` where the conclusion is the claim said differently.
    pub(super) fn cite_library(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        item: &'a Record,
    ) -> Checked<Route<Proof>> {
        if self.target_labels(step, item)?.is_empty() {
            return Err(self.untargeted(step, item));
        }
        let labels = self.cited_labels(step, item)?;
        let seed = self.filling(step, item)?;
        let facts = &self.with_reflexive(step, item, scope, facts)?;
        let facts = &self.with_defined_types(step, item, scope, facts)?;
        match self
            .by_clause_or_instance(item, &labels, term, scope, facts, step, &seed)?
        {
            Built(p) => Ok(Built(p)),
            Declined(d) => Err(self.defect(
                step.line,
                format!(
                    "no clause of {} reaches what step {} claims: {}",
                    step.just.head,
                    step.number,
                    self.say(&d)
                ),
            )),
        }
    }

    /// `facts` with each hypothesis of `item` that is an equation whose two
    /// sides are one under the citation, t = t, which needs no line
    /// (`SYNTAX.md`, "An identity element goes without saying"), proved as
    /// it stands: |X| = m at X := A and m := |A|, which the lemma's own
    /// hypotheses may then be settled from as from a line.
    pub(super) fn with_reflexive(
        &mut self,
        step: &Step,
        item: &'a Record,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Facts> {
        let out = facts.copy();
        let written: NodeBinding = self
            .cited_here(step, &item.qualified())?
            .written
            .into_iter()
            .collect();
        let library = self.item_library();
        let Some(groups) = library.groups(&item.qualified()) else {
            return Ok(out);
        };
        let none = IndexMap::new();
        for group in groups.iter() {
            for tree in group.asked() {
                let said = filled(tree, &written, &library.ctx);
                let [left, right] = said.children.as_slice() else {
                    continue;
                };
                if !library.ctx.equations.contains(&said.notation())
                    || !crate::matching::alike(left, right, &library.ctx, &none, &none)
                {
                    continue;
                }
                let Ok(side) =
                    self.in_its_names(Item::Record(item), |me| me.term(left))
                else {
                    continue;
                };
                let equation = t!(side, side, "wceq");
                let proof =
                    self.b
                        .ap("eqidd", &binds! {"ph" => scope, "A" => &side}, &[]);
                self.know(&out, equation, proof);
            }
        }
        Ok(out)
    }

    /// `facts` with each type `f : X → Y` that `item` asks of a function
    /// the citation fills with a define's, where the page says it once: the
    /// define's rule is in Y at every point of X (`map_into`, `SYNTAX.md`, "A
    /// define with a parameter also states what its function is on"). It is
    /// proved here, where the define's line is in hand, so that the lemma's
    /// own hypotheses, a value f(a) ∈ ℂ, may be settled from it as from a
    /// line.
    pub(super) fn with_defined_types(
        &mut self,
        step: &Step,
        item: &'a Record,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Facts> {
        let out = facts.copy();
        let written: NodeBinding = self
            .cited_here(step, &item.qualified())?
            .written
            .into_iter()
            .collect();
        let library = self.item_library();
        for tree in library.function_types(&item.qualified()) {
            // A type whose sets the citation leaves to the match, as
            // `product-termwise` leaves its functions' domains, names no
            // define's domain to prove it over.
            let unfilled = tree
                .walk()
                .iter()
                .any(|n| n.is_name() && !written.contains_key(&n.text));
            if unfilled {
                continue;
            }
            let said = filled(&tree, &written, &library.ctx);
            let typed = self.in_its_names(Item::Record(item), |me| me.term(&said))?;
            if let Some(proof) =
                self.map_into(&self.to_term(&typed), scope, facts, 3)?
            {
                self.know(&out, typed, proof);
            }
        }
        Ok(out)
    }

    /// What one clause of an item gives, or what several give together, one
    /// to a sentence of the claim.
    pub(super) fn by_clause(
        &mut self,
        labels: &[String],
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        step: &Step,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        // Why each clause did not reach the claim, said in order, so that a
        // message names what the clause that came closest lacked.
        let mut why: Vec<String> = Vec::new();
        for label in labels {
            let found = self.apply_lemma(
                label,
                &self.to_term(term),
                scope,
                facts,
                Some(step),
                true,
                seed,
            )?;
            match found {
                Declined(d) => why.push(self.say(&d)),
                built => return Ok(built),
            }
        }
        for label in labels {
            if let Built(p) = self.by_conjunct(label, term, scope, facts, step, seed)? {
                return Ok(Built(p));
            }
        }
        let node = self.to_term(term);
        if node.label() != Some("wa") {
            return Ok(Route::no(why.join("; ")));
        }
        let halves: Vec<Rpn> = node.children().iter().map(|c| self.rpn(c)).collect();
        // Each sentence is reached as a whole claim is, an equation either
        // way round.
        let mut made = Vec::new();
        for one in &halves {
            made.push(
                self.by_clause_either_way(labels, one, scope, facts, step, seed)?,
            );
        }
        let mut proofs = Vec::new();
        for one in made {
            proofs.push(take!(one));
        }
        Ok(Built(
            pf!(self.b; scope, halves[0], halves[1], proofs[0], proofs[1], "jca"),
        ))
    }

    /// One of the things a lemma concludes together, as a record of several
    /// sentences states them: the claim fixes the lemma's variables by the
    /// conjunct it is, the lemma is applied at that instance of its whole
    /// conclusion, and the conjunct taken out of it. `∡PQR ≤ π` from a lemma
    /// concluding ∡PQR ∈ ℝ, −π < ∡PQR and ∡PQR ≤ π.
    pub(super) fn by_conjunct(
        &mut self,
        label: &str,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        step: &Step,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let statement = self.statement(label);
        let variables = names_of(&statement);
        let mut concluded = statement;
        while concluded.label() == Some("wi") {
            concluded = concluded.children()[1].clone();
        }
        if !matches!(concluded.label(), Some("wa") | Some("w3a")) {
            return Ok(Route::no(format!("{label} concludes one thing")));
        }
        let goal = self.to_term(term);
        let start = seed.cloned().unwrap_or_default();
        for piece in conjuncts_of(&concluded) {
            let Some(binding) = fit(&piece, &goal, &start, &variables) else {
                continue;
            };
            let instance = concluded.substitute(&binding);
            let Built(proof) = self.apply_lemma(
                label,
                &instance,
                scope,
                facts,
                Some(step),
                true,
                seed,
            )?
            else {
                continue;
            };
            let whole = self.rpn(&instance);
            let parts = Facts::new();
            self.know(&parts, whole.clone(), proof.clone());
            self.unpack_all(&whole, &proof, scope, &parts);
            if let Some(p) = self.held(&parts, term, scope)? {
                return Ok(Built(p));
            }
        }
        Ok(Route::no(format!(
            "no conjunct of what {label} concludes is the claim"
        )))
    }

    /// What a `with` target says the lemma's variables stand for, read under
    /// the citation's instantiation.
    pub(super) fn filling(
        &mut self,
        step: &Step,
        item: &'a Record,
    ) -> Checked<Binding> {
        let (label, fills) = targets::lemma(item);
        if fills.is_empty() {
            return Ok(Binding::new());
        }
        // A fill is written in the record's letters, each replaced by what it
        // stands for in the proof's names: a letter the step gives a value is
        // that value as the step writes it, and any other is what the
        // citation makes it (`matched_here`), never what the proof calls by
        // the same letter.
        let given = self.instantiated_nodes(&step.just)?;
        let matched: NodeBinding = self.matched_here(step, item)?.into_iter().collect();
        let mut bound: NodeBinding = matched
            .iter()
            .filter(|(name, _)| !given.iter().any(|v| v.name == name.as_str()))
            .map(|(name, value)| (*name, value.clone()))
            .collect();
        // A value the step gives as a name its citation reads as what the
        // name names, a define the step cites, is that, as the checker
        // matched it (`SYNTAX.md`, a defined name and the term it names are
        // one formula), so a map the fill builds over it runs over the set
        // the claim writes out.
        for v in given {
            let value = match matched.get(&Symbol::of(&v.name)) {
                Some(m) if v.value.is_name() && !m.is_name() => m.clone(),
                _ => v.value,
            };
            bound.insert(Symbol::of(&v.name), value);
        }
        let library = self.item_library();
        // A class a fill puts in may bind a letter of its own that the lemma
        // keeps apart from the variable it fills: a lemma about a sequence
        // may keep n apart from F, and F be the map sending n ∈ ℕ to s(n). Such a letter is
        // spelt with one the lemma uses nowhere.
        let theirs: BTreeSet<String> =
            match label.as_deref().and_then(|l| self.b.sigs.get(l)) {
                Some(sig) => sig
                    .statement
                    .iter()
                    .chain(sig.essentials.iter().flatten())
                    .map(|t| t.to_string())
                    .collect(),
                None => BTreeSet::new(),
            };
        let mut out = Binding::new();
        for (name, formula) in &fills {
            let fill = Written::new(formula, &item.path, item.line);
            let node =
                self.in_its_names(Item::Record(item), |me| me.read_one(&fill))?;
            let node = filled(&node, &bound, &library.ctx);
            let term = self.term(&node)?;
            let term = self.bound_apart_from(&self.to_term(&term), &theirs)?;
            out.insert(Symbol::of(name), term);
        }
        Ok(out)
    }

    /// `term` with each set variable a part of it binds that is one of
    /// `theirs` moved to a spare letter, one no name of the proof or the
    /// page holds (`spare_var`), in that part.
    pub(super) fn bound_apart_from(
        &mut self,
        term: &Term,
        theirs: &BTreeSet<String>,
    ) -> Checked<Term> {
        if term.variable().is_some() {
            return Ok(term.clone());
        }
        let mut term = term.clone();
        if term.label() != Some("cv") {
            let caught: Vec<String> = term
                .children()
                .iter()
                .filter_map(|c| c.variable())
                .filter(|v| theirs.contains(*v) && self.is_setvar(&self.float_of(v)))
                .map(str::to_string)
                .collect();
            for letter in caught {
                let spare = self.spare_var()?;
                let mut put = Binding::new();
                put.insert(Symbol::of(&letter), self.var_of(&spare));
                term = term.substitute(&put);
            }
        }
        let kids = term
            .children()
            .iter()
            .map(|c| self.bound_apart_from(c, theirs))
            .collect::<Checked<Vec<Term>>>()?;
        Ok(term.with_children(kids))
    }

    /// What a citation pushes, in the order the cited theorem's own statement
    /// declares, and that statement over its own variables in that order.
    /// Each of its variables is what it stands at in `applied`, the
    /// statement as this proof applies it: a variable is told by where it
    /// stands, so a bound letter of any binder is found as a class is.
    pub(super) fn cited_pushes(
        &self,
        step: &Step,
        name: &str,
        applied: &Rpn,
    ) -> Checked<Pushed> {
        let said = (self.statements)(name).ok_or_else(|| {
            self.defect(
                step.line,
                format!(
                    "{name}, which this step cites, has no built file under corpus/elaboration/: build it first, or build everything with `parley build metamath`"
                ),
            )
        })?;
        let words: Vec<&str> = said.split_whitespace().skip(1).collect();
        let pattern = self.b.syntax().parse(&words, "wff")?;
        let mut theirs: Vec<Symbol> = Vec::new();
        for token in words.iter().copied() {
            if let Some(label) = self.b.flabel.get(token) {
                if !theirs.contains(&label) {
                    theirs.push(label);
                }
            }
        }
        theirs.sort_by_key(|label| self.b.float_order(label).unwrap_or(usize::MAX));
        let variables: BTreeSet<Symbol> =
            theirs.iter().map(|l| self.sig(l).statement[1]).collect();
        let Some(binding) = fit(
            &pattern,
            &self.to_term(applied),
            &Binding::new(),
            &variables,
        ) else {
            return Err(self.defect(
                step.line,
                format!(
                    "{name} states {}, which is not what this step applies",
                    self.render(&self.rpn(&pattern))
                ),
            ));
        };
        let values = theirs
            .iter()
            .map(|l| self.rpn(&binding[self.sig(l).statement[1].as_str()]))
            .collect();
        let floats = theirs
            .iter()
            .map(|l| {
                let float = &self.sig(l).statement;
                (float[0], float[1])
            })
            .collect();
        Ok(Pushed {
            values,
            statement: said.split_whitespace().map(Symbol::of).collect(),
            floats,
        })
    }

    /// What each letter of a cited corpus theorem stands for where the
    /// citation's match fixes it, as a term in the step's own names: the
    /// binding the checker reads the citation with (`cited_here`). An
    /// obtain's is read off the lines it cites, as `obtain B:
    /// thm:convergent-bounded, from 1.1` finds x in 1.1.
    pub(in crate::elab) fn corpus_matched(
        &mut self,
        step: &Step,
        other: &'a Theorem,
    ) -> Checked<IndexMap<String, Rpn>> {
        let mut out = IndexMap::new();
        let obtain = step.just.head.is(crate::corpus::Method::Obtain);
        let taken = self.cited_here(step, &other.qualified())?;
        // A name the citation writes a value for takes that value, and a
        // name the match gives itself, as a library function's C in C(m, k)
        // is, stands as it already does.
        let written: BTreeSet<String> = self
            .instantiated_nodes(&step.just)?
            .into_iter()
            .map(|v| v.name)
            .collect();
        for (name, node) in &taken.binding {
            if written.contains(name.as_str()) || (node.is_name() && node.text == *name)
            {
                continue;
            }
            // An obtain reads a letter the proof names by the same word as
            // that name, as it reads the item's sentence; only a letter the
            // proof has no name for is taken from the lines.
            if obtain && self.names.contains_key(name.as_str()) {
                continue;
            }
            // A function letter the match makes a rule, t := x ↦ x·c, stands
            // for the map the rule is over the letter's domain, as a
            // function a define gives by a rule is read where it is written
            // alone.
            if node.notation() == crate::notations::PROPERTY_OF {
                if let Some(map) =
                    self.rule_as_map(other, name, node, &taken.binding)?
                {
                    out.insert(name.to_string(), self.term(&map)?);
                    continue;
                }
            }
            out.insert(name.to_string(), self.term(node)?);
        }
        Ok(out)
    }

    /// The map a rule bound to a cited theorem's function letter is, over
    /// the domain the theorem's `let` gives the letter, put in the step's
    /// names: t := x ↦ x·c, of `let t : X → ℤ`, is the map sending x ∈ X to
    /// x·c. None where no `let` of the theorem types the letter.
    pub(super) fn rule_as_map(
        &mut self,
        other: &'a Theorem,
        name: &str,
        rule: &Node,
        binding: &NodeBinding,
    ) -> Checked<Option<Node>> {
        // A rule holds its letter as its text and its body as its one part.
        let [body] = rule.children.as_slice() else {
            return Ok(None);
        };
        for h in other.hypotheses.iter().filter(|h| h.kind == Intro::Let) {
            let typed = self.in_its_names(Item::Theorem(other), |me| {
                me.hypothesis_node(Intro::Let, &h.body(&other.path))
            })?;
            let (crate::notations::FUNCTION_TYPE, [f, domain, _]) =
                (typed.notation(), typed.children.as_slice())
            else {
                continue;
            };
            if !(f.is_name() && f.text == name) {
                continue;
            }
            let domain = crate::matching::substitute_apart_by(
                domain,
                binding,
                &self.g.binders(),
            );
            // The map binds a letter of its own, apart from every letter the
            // step holds, the domain and the body write: where the map is
            // applied at the bound letter of a sum or product over the
            // domain, the two are kept apart (`fvmptd3`).
            let used: BTreeSet<String> = body
                .names()
                .into_iter()
                .chain(domain.names())
                .chain(self.names.keys().cloned())
                .collect();
            let Some(fresh) = MAP_LETTERS.iter().find(|l| !used.contains(**l)) else {
                return Ok(None);
            };
            let sort = body
                .walk()
                .into_iter()
                .find(|n| n.is_name() && n.text == rule.text)
                .map(|n| n.sort.clone())
                .or_else(|| domain.sort.held())
                .unwrap_or_else(crate::formula::Sort::unknown);
            let letter = Node::name(sort, fresh);
            let mut put = NodeBinding::new();
            put.insert(rule.text, letter.clone());
            let body =
                crate::matching::substitute_apart_by(body, &put, &self.g.binders());
            return Ok(crate::formula::page::made_as(
                self.g,
                "the map sending _ ∈ _ to _",
                vec![letter, domain, body],
            ));
        }
        Ok(None)
    }
}
