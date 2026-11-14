//! Citing items and substituting.

use super::*;

impl<'a> Elaborator<'a> {
    /// What an item states, however the database says it is supplied.
    ///
    /// An item with no target is assumed: nothing in the library has its
    /// shape, and the file says so at its head. An item that has one and
    /// whose every clause misses is an error: the field says where the claim
    /// lands, and it does not land there.
    pub fn cite_item(
        &mut self,
        step: &Step,
        goal: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        item: Item<'a>,
    ) -> Checked<Route<Proof>> {
        // An item this corpus proves is applied the way a cited one is,
        // however the step reaches it.
        if let Item::Theorem(t) = item {
            return self.cite_corpus(step, goal, scope, facts, t).map(Built);
        }
        let Item::Record(record) = item else {
            unreachable!()
        };
        let labels = self.cited_labels(step, record)?;
        let seed = self.filling(step, record)?;
        // The facts the checker recorded as supplying the item's hypotheses,
        // which discharge the lemma's antecedents that are those hypotheses.
        let given = self.recorded_hypotheses(step, record, scope, facts)?;
        let kept = self.hypotheses_given.replace(given);
        for label in &labels {
            let found = self.apply_lemma(
                label,
                &self.to_term(goal),
                scope,
                facts,
                Some(step),
                true,
                Some(&seed),
            );
            let found = match found {
                Ok(f) => f,
                Err(e) => {
                    self.hypotheses_given = kept;
                    return Err(e);
                }
            };
            if !found.is_declined() {
                self.hypotheses_given = kept;
                return Ok(found);
            }
        }
        self.hypotheses_given = kept;
        let assembled =
            self.by_lemmas(&labels, goal, scope, facts, step, Some(&seed))?;
        if !assembled.is_declined() {
            return Ok(assembled);
        }
        if !labels.is_empty() {
            // The item names itself, and what its labels did not reach is
            // said as it stands.
            let wanted = if step.just.head.to_string() == "obtain" {
                format!("what step {} obtains", step.number)
            } else {
                self.render(&self.rpn(&self.to_term(goal)))
            };
            return Err(self.defect(
                step.line,
                format!(
                    "{}:{}'s metamath-proof names {}, and none of them reaches {wanted}",
                    item_kind(item),
                    record.qualified(),
                    labels.join(", ")
                ),
            ));
        }
        Err(self.untargeted(step, record))
    }

    /// An item the database gives no target for: nothing builds what it
    /// says, and the build takes nothing as stated, so citing it stops here.
    /// The lemmas an item's target names, each one the library this build
    /// read holds. A building of one theorem reads `proved.mm` as it was
    /// last written, so a lemma added to `corpus/metamath-bridges/` since is not there
    /// until a whole build writes it.
    pub(super) fn target_labels(
        &self,
        step: &Step,
        item: &Record,
    ) -> Checked<Vec<String>> {
        let labels = targets::clauses(item);
        if let Some(missing) = labels.iter().find(|l| !self.b.sigs.contains_key(l)) {
            return Err(self.defect(
                step.line,
                format!(
                    "{}:{}'s metamath-proof names {missing}, which neither set.mm nor proved.mm as built holds: a lemma of corpus/metamath-bridges/ reaches proved.mm when everything is built with `parley build metamath`",
                    item_kind(Item::Record(item)),
                    item.qualified()
                ),
            ));
        }
        Ok(labels)
    }

    /// The lemmas that prove what the step's citation of `item` takes: the
    /// lemma of each sentence the checker read the claim as taking
    /// (`Cited::sentences`), or of each sentence of the group an obtain
    /// takes whole. An item whose target names fewer lemmas than it has
    /// sentences proves several with one lemma (gcd: "four sentences from
    /// three lemmas"), and which one is set.mm's to say: every lemma is
    /// offered.
    pub(super) fn cited_labels(
        &self,
        step: &Step,
        item: &Record,
    ) -> Checked<Vec<String>> {
        let labels = self.target_labels(step, item)?;
        let library = self.item_library();
        let Some(groups) = library.groups(&item.qualified()) else {
            return Ok(labels);
        };
        let sentences: usize = groups.iter().map(|g| g.gives.len()).sum();
        if labels.len() != sentences {
            return Ok(labels);
        }
        let cited = self.cited_here(step, &item.qualified())?;
        let taken: Vec<usize> = if cited.concluded.is_empty() {
            let before: usize =
                groups[..cited.group].iter().map(|g| g.gives.len()).sum();
            (before..before + groups[cited.group].gives.len()).collect()
        } else {
            cited.concluded.iter().map(|c| c.sentence).collect()
        };
        Ok(taken.into_iter().map(|s| labels[s].clone()).collect())
    }

    pub(super) fn untargeted(&self, step: &Step, item: &Record) -> Problem {
        self.defect(
            step.line,
            format!(
                "step {} cites {}:{}, which the database gives no metamath-proof for, and nothing is taken as stated",
                step.number,
                item_kind(Item::Record(item)),
                item.qualified()
            ),
        )
    }

    /// A sentence of an item, read in the item's own names and then said at
    /// this step: each name the step's citation fixes (`citing::obtained`) is
    /// what it stands for, and a function letter standing for a rule is that
    /// rule where the sentence applies it. `x(n) ≤ B` of
    /// `convergent-bounded`, with x the partial sums of 1/k, is
    /// Σ(k = 1 to n) 1/k ≤ B.
    ///
    /// The citation is read as the checker reads it: the lines the step
    /// names, its requires lines, and the values its justification gives.
    /// An item that gives no "there is" from them is a defect, which the
    /// checker reports of the same step.
    pub(crate) fn item_sentence_here(
        &mut self,
        step: &Step,
        item: &'a Record,
        said: &Written,
    ) -> Checked<Node> {
        let binding = self.matched_here(step, item)?;
        let library = self.item_library();
        let node = self.in_its_names(Item::Record(item), |me| me.read_one(said))?;
        Ok(filled(&node, &binding, &library.ctx))
    }

    /// What each letter of a record a step cites stands for at that step,
    /// as the checker reads the citation (`citing`): the values its
    /// justification gives, and what the step's lines, its requires lines and,
    /// where it does not obtain, its claim fix. A letter is the record's own
    /// whatever the proof calls its letters, so a record's `k` is what the
    /// citation makes it and never the proof's `k`.
    ///
    /// A step that obtains takes the record's "there is" (`obtained`), and a
    /// record that gives none from what the step names is a defect, which the
    /// checker reports of the same step. Any other step concludes what it
    /// claims (`taken`); where no clause does, the binding is what the step
    /// writes, and the step fails further on, where it can say why.
    pub(crate) fn matched_here(
        &mut self,
        step: &Step,
        item: &'a Record,
    ) -> Checked<NodeBinding> {
        let cited = self.cited_here(step, &item.qualified())?;
        Ok(cited.binding.into_iter().collect())
    }

    /// The checker's reading of the citation of `item`, by its full name,
    /// that `step` makes (`CheckedTheorem::cited`): a step's own, or a
    /// requires line's read as the step it would be. The build refuses what
    /// the checker refuses, so a citation it builds is one the checker read.
    /// The values the checker read an exhibit as showing, for the sentence
    /// the build proves, its last: what each letter of its "there is" is
    /// put to, by the variable the letter stands for
    /// (`CheckedTheorem::exhibited`).
    pub(in crate::elab) fn exhibited_here(
        &mut self,
        step: &Step,
    ) -> Checked<IndexMap<Rpn, Rpn>> {
        let values = self
            .checked
            .exhibited
            .get(&step.just.line)
            .and_then(|v| v.last())
            .cloned()
            .flatten()
            .map(|e| e.values);
        let Some(values) = values else {
            return Err(self.unreached(
                step.line,
                "the checker reads no value this exhibit shows",
            ));
        };
        let mut out = IndexMap::new();
        for (letter, value) in &values {
            let mark = t!(self.binder_var(letter)?, "cv");
            let value = self.term(value)?;
            out.insert(mark, value);
        }
        Ok(out)
    }

    /// The checker's reading of the citation `step` makes, whatever it
    /// cites: a step's own, or a requires line's read as the step it would
    /// be. None where it cites no item.
    pub(in crate::elab) fn citation_read(&self, step: &Step) -> Option<&Cited> {
        match self.thm.steps.iter().position(|s| s.line == step.line) {
            Some(i) => self.checked.cited[i].as_ref(),
            None => self.checked.cited_requires.get(&step.line),
        }
    }

    pub(super) fn cited_here(&self, step: &Step, item: &str) -> Checked<Cited> {
        match self.citation_read(step) {
            Some(cited) if cited.item == item => Ok(cited.clone()),
            _ => Err(self.defect(
                step.line,
                format!("the checker reads no citation of {item} on this line"),
            )),
        }
    }

    /// What the clause a step's citation takes concludes there, each
    /// sentence a term with every letter the citation fixes put in: the
    /// instance the checker compared the claim with (`cited_here`). Empty
    /// for an obtain, which claims the witness and no conclusion of the item.
    pub(super) fn concluded_here(
        &mut self,
        step: &Step,
        item: &'a Record,
    ) -> Checked<Vec<Rpn>> {
        if step.just.head.is(crate::corpus::Method::Obtain) {
            return Ok(Vec::new());
        }
        let taken = self.cited_here(step, &item.qualified())?;
        let library = self.item_library();
        let Some(groups) = library.groups(&item.qualified()) else {
            return Ok(Vec::new());
        };
        let binding: NodeBinding = taken.binding.into_iter().collect();
        let mut out = Vec::new();
        // The instance holds the proof's values, so it is a term in the
        // proof's names, as a `with` fill is (`filling`): read in the item's,
        // a value's letters lose the sorts the proof gives them, and |PQ| of
        // two points is no longer a distance.
        for node in &groups[taken.group].gives {
            let instance = filled(node, &binding, &library.ctx);
            out.push(self.term(&instance)?);
        }
        Ok(out)
    }

    /// The values a citation gives its item's letters, `name := value`, as
    /// kernel terms, each read in the names as they stand before any is
    /// given (`instantiated_nodes`).
    pub(crate) fn instantiated(
        &mut self,
        just: &Justification,
    ) -> Checked<Vec<(String, Rpn)>> {
        let mut out = Vec::new();
        for v in self.instantiated_nodes(just)? {
            out.push((v.name, self.term(&v.value)?));
        }
        Ok(out)
    }

    /// The values a citation gives, as trees in the page's notation, read
    /// together where the elaborator has got to: values are simultaneous,
    /// so `a := b/k, b := a/k` swaps the two (`Values`). Each is read as
    /// its letter's place in the cited item wants it (`Values::read_wanted`).
    pub(crate) fn instantiated_nodes(
        &self,
        just: &Justification,
    ) -> Checked<Vec<Value>> {
        let library = self.item_library();
        let letters = just
            .cited_item()
            .and_then(|item| library.item_sorts(&just.item(&item)));
        let reader = |value: &Written| self.read_one(value);
        just.values.read_wanted_by(&reader, self.g, letters)
    }

    /// A universal used at one term: `instantiate s := a in line 10` takes a
    /// line claiming something of every s and claims it of one of them.
    pub(super) fn instantiate(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let where_ = step.just.target.clone().unwrap_or_default();
        if self.line_written(&where_, lines).is_none() {
            return Err(self.unreached(
                step.line,
                format!("instantiate names no line or label {}", repr(&where_)),
            ));
        }
        // A line may say several things at once, and the `for all` is
        // rarely the first of them. Taken apart on its own.
        let known = self.line_supplies(&where_, scope, facts, lines)?;
        // What the lines the step names say gives t ∈ X, a subset's members
        // at a block's letter among it; and what each of those says besides,
        // as the checker reads a cited line: n ∈ ℕ gives 1 ≤ n, the
        // condition of a "for all i ≥ 1" at n.
        let from_lines = self.with_cited(Some(step), scope, facts, None)?;
        for cite in &step.just.refs {
            let says = self.line_says(cite, scope, facts, lines)?;
            for (said, given) in says.entries() {
                if !self.holds(&from_lines, &said) {
                    self.know(&from_lines, said, given);
                }
            }
        }
        let universals: Vec<Rpn> = self
            .line_writes(&where_, lines)
            .into_iter()
            .filter(|p| matches!(self.to_term(p).label(), Some("wral") | Some("wal")))
            .collect();
        let pairs = self.instantiated_nodes(&step.just)?;
        // The sentence, or the part of one, the checker instantiated
        // (`CheckedTheorem::instantiated`), which the checker records of
        // every instantiate it accepts.
        let Some(at) = self
            .checked
            .instantiated
            .get(&step.just.line)
            .map(|r| r.at.clone())
        else {
            return Err(self.defect(
                step.line,
                format!("the checker recorded no instance of {where_} on this line"),
            ));
        };
        // The line as elaborated may bind another letter than the sentence
        // read afresh: one claim with its bound variable renamed
        // (`renaming`), a set.mm question.
        let recorded = self.recorded_statement(&at)?;
        let mut found = None;
        for p in &universals {
            let same = *p == recorded
                || self
                    .renaming(&self.to_term(&recorded), &self.to_term(p))?
                    .is_some();
            if same {
                found = Some(p.clone());
                break;
            }
        }
        let Some(said) = found else {
            return Err(self.defect(
                step.line,
                format!(
                    "the checker instantiated {} of {where_}, which says no for all there",
                    at.line
                ),
            ));
        };
        let mut proof = self
            .held(&known, &said, scope)?
            .expect("a part of the line, taken apart above");
        let mut whole = self.to_term(&said);
        // Each value is the one written for the name the line quantifies at
        // that level, whatever its place in the list.
        let by_name: IndexMap<String, Node> = pairs
            .iter()
            .map(|v| (v.name.clone(), v.value.clone()))
            .collect();
        for _ in 0..pairs.len() {
            let label = whole.label().map(str::to_string);
            let found = label
                .as_deref()
                .and_then(|label| rules::INSTANCES.iter().find(|(k, _)| *k == label));
            let (Some(label), Some(instance)) =
                (label, found.map(|(_, i)| (i.lemma, i.domain_var, i.domain)))
            else {
                return Err(self.unreached(
                    step.line,
                    "more names instantiated than are quantified",
                ));
            };
            let (lemma, slot, domain) = instance;
            let (body, variable) =
                (whole.children()[0].clone(), whole.children()[1].clone());
            let domain = match domain {
                Some(d) => t!(d),
                None => self.rpn(&whole.children()[2]),
            };
            let letter = self.rpn(&variable).to_string();
            let named = self
                .written_as
                .get(&letter)
                .cloned()
                .unwrap_or(letter.clone());
            let Some(value) = by_name.get(&named).cloned() else {
                return Err(self.unreached(
                    step.line,
                    format!("{where_} quantifies a name the step gives no value, before the ones it does"),
                ));
            };
            let mark = t!(letter, "cv");
            let at = self.term(&value)?;
            // A value that spells the bound letter inside it, ε/2 for "for
            // all ε" read in the block letting ε, is put in once the line is
            // read over a letter nothing holds: `rspcv` keeps the letter
            // apart from what is put in.
            let mut variable = variable;
            let mut letter = letter;
            let mut mark = mark;
            let mut body = body;
            let spelt_in = variable
                .variable()
                .is_some_and(|v| at != mark && self.to_term(&at).names().contains(v));
            if spelt_in {
                let Some(fresh) = self.unheld(&[&whole, &self.to_term(&at)]) else {
                    return Err(self.defect(
                        step.line,
                        format!("no letter is left to read {where_} over apart from the value"),
                    ));
                };
                let mut moved = Binding::new();
                moved.insert(variable.variable_symbol().unwrap(), fresh);
                let respelt = whole.substitute(&moved);
                let Some(renamed) = self.renaming(&whole, &respelt)? else {
                    return Err(self.defect(
                        step.line,
                        format!("{where_} cannot be read over a letter apart from the value"),
                    ));
                };
                let w = self.rpn(&whole);
                let r = self.rpn(&respelt);
                proof = pf!(self.b; scope, w, r, proof, renamed, "sylib");
                whole = respelt;
                (body, variable) =
                    (whole.children()[0].clone(), whole.children()[1].clone());
                letter = self.rpn(&variable).to_string();
                mark = t!(letter, "cv");
            }
            let w = self.rpn(&whole);
            if at == mark {
                // The value is the bound letter itself, as where a block
                // lets x and its line says "for all x" over the same kernel
                // letter: there is nothing to put in, and `rsp` or `sp` reads
                // the body as it stands, where `rspcv` would ask the letter
                // to be apart from itself.
                let ph = self.rpn(&body);
                proof = if label == "wral" {
                    let member = t!(at, domain, "wcel");
                    let read = self.b.ap(
                        "rsp",
                        &binds! {"ph" => &ph, "x" => &letter, "A" => &domain},
                        &[],
                    );
                    let turned = pf!(self.b; w, member, ph, read, "com12");
                    let required = self.required(step, &member, scope, &from_lines)?;
                    let carried = pf!(self.b; scope, member, t!(w, ph, "wi"), required, turned, "syl");
                    pf!(self.b; scope, w, ph, proof, carried, "mpd")
                } else {
                    let read =
                        self.b.ap("sp", &binds! {"ph" => &ph, "x" => &letter}, &[]);
                    pf!(self.b; scope, w, ph, proof, read, "syl")
                };
                whole = body;
                continue;
            }
            let instance = self.restated(&body, &mark, &at);
            let (ph, ps) = (self.rpn(&body), self.rpn(&instance));
            let member = t!(at, domain, "wcel");
            let tie = self.to_term(&t!(t!(mark, at, "wceq"), t!(ph, ps, "wb"), "wi"));
            let asked = match self.prove_essential(&tie, scope, facts)? {
                Built(p) => p,
                Declined(d) => {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "{lemma} cannot tie the line to its instance: {}",
                            self.say(&d)
                        ),
                    ));
                }
            };
            let mut binds =
                binds! {"ph" => &ph, "ps" => &ps, "x" => &letter, "A" => &at};
            binds.insert(slot.to_string(), domain.clone());
            let applied = self.b.ap(lemma, &binds, &[&asked]);
            let required = self.required(step, &member, scope, &from_lines)?;
            let carried =
                pf!(self.b; scope, member, t!(w, ps, "wi"), required, applied, "syl");
            proof = pf!(self.b; scope, w, ps, proof, carried, "mpd");
            whole = instance;
        }
        // What a universal says of one name is often a conditional, and the
        // step claims what it concludes: each thing asked on the way is a
        // line the step cites.
        let mut reached = self.rpn(&whole);
        while reached != *term {
            let reads = self.to_term(&reached);
            // What the universal says may be the claim in other words.
            if let Built(alike) =
                self.same(&reads, &self.to_term(term), scope, facts, None)?
            {
                return Ok(Built(
                    pf!(self.b; scope, reached, term, proof, alike, "mpbid"),
                ));
            }
            // Or the claim with its identity elements dropped, as the checker
            // compares the two (`SYNTAX.md`, "An identity element goes without
            // saying"): the line at k := 0 says F(0 + 2), and the step F(2).
            if let Some(tidy) = self.tidied(&proof, &reached, term, scope, facts)? {
                return Ok(Built(tidy));
            }
            // Or both: the instance with its identity elements dropped, and
            // that the claim in other words, as a(1) = a(0) + 2 is the step's
            // a(0) + 2 = a(1).
            let bare = self.rpn(&self.without_identities(&reads));
            if bare != reached {
                if let Some(dropped) =
                    self.tidied(&proof, &reached, &bare, scope, facts)?
                {
                    if let Built(alike) = self.same(
                        &self.to_term(&bare),
                        &self.to_term(term),
                        scope,
                        facts,
                        None,
                    )? {
                        return Ok(Built(
                            pf!(self.b; scope, bare, term, dropped, alike, "mpbid"),
                        ));
                    }
                }
            }
            if reads.label() != Some("wi") {
                return Err(self.defect(
                    step.line,
                    format!(
                        "{where_} at those terms says {}, and the step claims {}",
                        self.render(&reached),
                        self.render(term)
                    ),
                ));
            }
            let (asks, rest) = (
                self.rpn(&reads.children()[0]),
                self.rpn(&reads.children()[1]),
            );
            // An `instantiate` is the head of a step, so what the universal
            // asks at this term is the text's to supply: a requires line of
            // the step, as `0 < 1/2` for "for all ε > 0" at 1/2, or a line
            // it cites.
            let written = self
                .written
                .entries()
                .into_iter()
                .find(|(said, _)| *said == asks)
                .and_then(|(said, w)| self.lifted_to(&said, &w.proof, &w.at, scope));
            if let Some(supplied) = written {
                proof = pf!(self.b; scope, asks, rest, supplied, proof, "mpd");
                reached = rest;
                continue;
            }
            // A line the step cites supplies each part of a conjunction it
            // says, as `from_lines` holds them.
            let supplied = match self.settle(
                &self.to_term(&asks),
                scope,
                &from_lines,
                3,
                None,
                None,
            )? {
                Built(p) => p,
                Declined(d) => {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "instantiating at that term wants {}, which step {} does not supply: {}",
                            self.render(&asks),
                            step.number,
                            self.say(&d)
                        ),
                    ));
                }
            };
            proof = pf!(self.b; scope, asks, rest, supplied, proof, "mpd");
            reached = rest;
        }
        Ok(Built(proof))
    }

    /// One equation put into one claim, at the place the tree names: the
    /// step's own claim, or a line `into` names.
    /// An equation as a substitution offers it: either side may be put for
    /// the other, `substitute K = a/2 (D3) into H6` putting K where H6
    /// writes a/2, so it is held both ways round and nothing else is.
    pub(super) fn equation_facts(
        &mut self,
        old: &Rpn,
        new: &Rpn,
        facing: Proof,
        scope: &Rpn,
    ) -> Facts {
        let equation = Facts::new();
        let back = pf!(self.b; scope, old, new, facing, "eqcomd");
        self.know(&equation, t!(old, new, "wceq"), facing);
        self.know(&equation, t!(new, old, "wceq"), back);
        equation
    }

    /// A substitution with no line to put its equation into claims `t = t′`,
    /// t′ being t with one side of the equation put for the other at some
    /// of the places it stands, every place or fewer: where the two differ,
    /// the equation says they are equal, and nothing else is asked
    /// (`congruence` over the equation alone). None where the equation does
    /// not make the claim.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn claim_rewritten(
        &mut self,
        step: &Step,
        node: &Node,
        old: &Rpn,
        new: &Rpn,
        equation: &Facts,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let (start, other) =
            (self.term(&node.children[0])?, self.term(&node.children[1])?);
        let alike = self.congruence(
            &self.to_term(&start),
            &self.to_term(&other),
            scope,
            equation,
            Some(step),
            &substitution_leaf(),
        )?;
        if let Built(p) = alike {
            if start != other {
                return Ok(Some(p));
            }
        }
        if let Some(p) = self
            .replaced_tidied(&start, &other, old, new, scope, equation, facts, step)?
        {
            return Ok(Some(p));
        }
        // The claim is t = t′ either way round: t′ = t, its right side the
        // one the equation is put into.
        Ok(self
            .replaced_tidied(&other, &start, old, new, scope, equation, facts, step)?
            .map(|p| pf!(self.b; scope, other, start, p, "eqcomd")))
    }

    /// A `substitute` step's rows (`substitute_rows`): the first is what the
    /// line it cites says, and each after it is the row above with one term
    /// put for another, by the equation its reason proves, as a requires
    /// line is proved (`as_a_step`), and nothing else (`congruence` over
    /// that equation alone). The last row is the claim.
    pub(super) fn substitute_by_rows(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let Some(Ok(rows)) = substitute_rows(&step.just, &self.thm.path) else {
            return Err(self.unreached(step.line, "rows that do not cut"));
        };
        let Some(first) = rows.first() else {
            return Err(self.unreached(step.line, "a substitute with no rows"));
        };
        let mut reached = self.term(&self.read_one(&first.formula)?)?;
        // Each row's reason rests on the step's requires lines, as a step
        // giving that reason would (`supplied`).
        let supplied = self.supplied(Some(step), scope, facts)?;
        let Some(mut proof) =
            self.said_by(&first.cite, &reached, scope, facts, lines)?
        else {
            return Err(self.defect(
                first.line,
                format!("{} does not say {}", first.cite, first.formula),
            ));
        };
        for row in &rows[1..] {
            let Some(req) = &row.reason else {
                return Err(
                    self.unreached(row.line, "a row after the first with no reason")
                );
            };
            let what = format!("a row of step {} writes {}", step.number, row.formula);
            let change = match self.as_a_step(step, req, &what, scope, &supplied)? {
                Built(p) => p,
                Declined(d) => {
                    return Err(self.defect(
                        row.line,
                        format!(
                            "{what}, which {} does not give: {}",
                            req.how,
                            self.say(&d)
                        ),
                    ));
                }
            };
            let changed = self.read_one(&req.fact)?;
            let changed = self.term(&changed)?;
            let said = self.to_term(&changed);
            let (was, now) =
                (self.rpn(&said.children()[0]), self.rpn(&said.children()[1]));
            let equation = self.equation_facts(&was, &now, change, scope);
            let below = self.term(&self.read_one(&row.formula)?)?;
            let alike = match self.congruence(
                &self.to_term(&reached),
                &self.to_term(&below),
                scope,
                &equation,
                Some(step),
                &substitution_leaf(),
            )? {
                Built(p) => p,
                Declined(d) => {
                    return Err(self.defect(
                        row.line,
                        format!(
                            "{what}, which its change does not make: {}",
                            self.say(&d)
                        ),
                    ));
                }
            };
            proof = pf!(self.b; scope, reached, below, proof, alike, "mpbid");
            reached = below;
        }
        if reached == *term {
            return Ok(Built(proof));
        }
        // The last row may write the claim in its other form, carried back
        // (`rules::OTHER_FORMS`), as the checker reads it.
        if self.other_form(&reached).is_some() {
            let carried = self.implied(&reached, &proof, scope, facts)?;
            if let Some(p) = self.held(&carried, term, scope)? {
                return Ok(Built(p));
            }
        }
        let alike = take!(self.same(
            &self.to_term(&reached),
            &self.to_term(term),
            scope,
            facts,
            Some(step)
        )?);
        Ok(Built(
            pf!(self.b; scope, reached, term, proof, alike, "mpbid"),
        ))
    }

    /// What the line `cite` says that is `wanted`, as a cited line gives it:
    /// the line's claim, or one of the things it says (`line_says`). None
    /// where it says no such thing.
    pub(super) fn said_by(
        &mut self,
        cite: &str,
        wanted: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Option<Proof>> {
        let Some(line) = self.line_written(cite, lines) else {
            return Err(self.unreached(self.thm.line, format!("no line {cite} cited")));
        };
        if line.claim == *wanted {
            return Ok(Some(self.carried(cite, facts, lines)));
        }
        let known = self.line_says(cite, scope, facts, lines)?;
        Ok(known
            .entries()
            .into_iter()
            .find(|(said, _)| said == wanted)
            .map(|(_, held)| held))
    }

    /// `substitute line L`, which writes no equation: the claim, `t = t′`
    /// as a chain's line claims it, is one side of an equation L says put
    /// for the other in t (`skeleton::substitute`). The checker has held the
    /// claim to one of them; each is offered in the order L says it.
    pub(super) fn substitute_line(
        &mut self,
        step: &Step,
        node: &Node,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let Some(source) = step.just.source.as_ref().map(|s| s.named().to_string())
        else {
            return Err(self.unreached(step.line, "a substitute that names no source"));
        };
        let said = self.line_says(&source, scope, facts, lines)?;
        for (said_as, held) in said.entries() {
            let equation = self.to_term(&said_as);
            if equation.label() != Some("wceq") {
                continue;
            }
            let (old, new) = (
                self.rpn(&equation.children()[0]),
                self.rpn(&equation.children()[1]),
            );
            let offered = self.equation_facts(&old, &new, held, scope);
            if let Some(p) =
                self.claim_rewritten(step, node, &old, &new, &offered, scope, facts)?
            {
                return Ok(Built(p));
            }
        }
        Err(self.defect(
            step.line,
            format!("no equation {source} says makes the claim"),
        ))
    }

    pub(super) fn substitute(
        &mut self,
        step: &Step,
        node: &Node,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if !step.just.rows.is_empty() {
            return self.substitute_by_rows(step, term, scope, facts, lines);
        }
        let Some(source) = &step.just.source else {
            return Err(self.unreached(step.line, "a substitute that names no source"));
        };
        let Some(written) = &step.just.equation else {
            return self.substitute_line(step, node, scope, facts, lines);
        };
        let equation = self.read_one(written)?;
        let (left, right) =
            (equation.children[0].clone(), equation.children[1].clone());
        let (old, new) = (self.term(&left)?, self.term(&right)?);
        // Which way the equation faces in the kernel is the lemma's choice,
        // not the text's, so either is accepted and turned if it has to be.
        let mut facing = self.held(facts, &t!(old, new, "wceq"), scope)?;
        if *source == crate::corpus::Source::Arithmetic {
            let what = format!("step {} substitutes {written}", step.number);
            facing = Some(self.closed_fact(
                &t!(old, new, "wceq"),
                scope,
                facts,
                &what,
                Some(step),
            )?);
        }
        if *source == crate::corpus::Source::RealArithmetic {
            let what = format!("step {} substitutes {written}", step.number);
            facing =
                Some(self.real_fact(&t!(old, new, "wceq"), scope, facts, &what)?);
        }
        // A define says the equation between its name and what it names
        // (`SYNTAX.md`, substitute), which no line in scope holds.
        let by_define = source.named().to_string();
        if facing.is_none() && self.defined_by.values().any(|l| *l == by_define) {
            let (a, b) = (self.to_term(&old), self.to_term(&new));
            if let Built(p) = self.equation_by_define(step, &a, &b, scope, facts)? {
                facing = Some(p);
            }
        }
        let facing = match facing {
            Some(f) => f,
            None => {
                let Some(held) = self.held(facts, &t!(new, old, "wceq"), scope)? else {
                    return Err(self.defect(
                        step.line,
                        format!("no equation {old} = {new} in scope"),
                    ));
                };
                pf!(self.b; scope, new, old, held, "eqcomd")
            }
        };
        let equation = self.equation_facts(&old, &new, facing, scope);
        let leaf = substitution_leaf();
        let into = step.just.into.as_ref().map(|p| p.named().to_string());
        let Some(where_) = into else {
            return match self
                .claim_rewritten(step, node, &old, &new, &equation, scope, facts)?
            {
                Some(p) => Ok(Built(p)),
                None => {
                    Err(self.defect(step.line, "the substitution misses the claim"))
                }
            };
        };
        let into = self
            .line_written(&where_, lines)
            .unwrap_or_else(|| panic!("no line {where_} to substitute into"));
        let sentences = self.line_sentences(&where_, lines);
        if sentences.is_empty() {
            return Err(
                self.unreached(step.line, format!("{where_} is not a line to rewrite"))
            );
        }
        // A line may say several things and the substitution land in one of
        // them, so each sentence is offered with a proof of itself; and the
        // line as a whole is offered, which a claim of as many sentences
        // rewrites (`SYNTAX.md`: the equation is replaced inside the line).
        let known = self.line_says(&where_, scope, facts, lines)?;
        // A sentence joined by `and` is its parts as surely as a line of two
        // sentences is, so each is offered.
        let mut offered = Vec::new();
        let mut work: std::collections::VecDeque<Node> =
            sentences.into_iter().collect();
        while let Some(one) = work.pop_front() {
            offered.push(one.clone());
            if !one.children.is_empty() {
                let said = self.term(&one)?;
                if self.to_term(&said).label() == Some("wa") {
                    work.extend(one.children.iter().cloned());
                }
            }
        }
        let mut starts: Vec<Rpn> = vec![into.claim.clone()];
        for one in &offered {
            let start = self.term(one)?;
            if !starts.contains(&start) {
                starts.push(start);
            }
        }
        for start in &starts {
            if !self.holds(&known, start) {
                if let Some(p) = self.held(facts, start, scope)? {
                    self.know(&known, start.clone(), p);
                }
            }
        }
        // After what the line writes, everything else it says (`line_says`):
        // a "for all" read at a block's letter, a chain's equations, a
        // congruence turned round, a bound or a part of a set said otherwise.
        for (said, _) in known.entries() {
            if !starts.contains(&said) {
                starts.push(said);
            }
        }
        // The claim as written, and an equation's the other way round: what
        // the substitution makes may face either way (`turned_claim`). A
        // claim in one of two forms is made by making the other and carrying
        // it back (`rules::OTHER_FORMS`), as the checker reads it.
        let mut aims: Vec<(Rpn, Toward)> = vec![(term.clone(), Toward::Claim)];
        if let Some((turned, flip)) = self.turned_claim(term) {
            aims.push((turned, Toward::Turned(flip)));
        }
        if let Some(other) = self.other_form(term) {
            aims.push((self.rpn(&other.reached), Toward::OtherForm));
        }
        for (aim, toward) in &aims {
            for start in &starts {
                if start == aim {
                    continue;
                }
                let Some(given) = self.held(&known, start, scope)? else {
                    continue;
                };
                let walked = self.congruence(
                    &self.to_term(start),
                    &self.to_term(aim),
                    scope,
                    &equation,
                    Some(step),
                    &leaf,
                )?;
                let made = match walked {
                    Built(alike) => {
                        pf!(self.b; scope, start, aim, given, alike, "mpbid")
                    }
                    Declined(_) => {
                        let tidy = self.substituted_tidied(
                            start, aim, &given, &old, &new, scope, &equation, facts,
                            step,
                        )?;
                        let Some(made) = tidy else {
                            continue;
                        };
                        made
                    }
                };
                match toward {
                    Toward::Claim => return Ok(Built(made)),
                    Toward::Turned(flip) => {
                        let Sides { left, right } = self.equation_sides(aim);
                        return Ok(Built(pf!(self.b; scope, left, right, made, *flip)));
                    }
                    Toward::OtherForm => {
                        let carried = self.implied(aim, &made, scope, facts)?;
                        if let Some(p) = self.held(&carried, term, scope)? {
                            return Ok(Built(p));
                        }
                    }
                }
            }
        }
        Err(self.defect(step.line, "the substitution misses the claim"))
    }
}
