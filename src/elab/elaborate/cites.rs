//! Citing a claim's reasons.

use super::*;
use crate::checker::record::Supplied;
use crate::corpus::records::{LemmaReading, Side};
use crate::formula::{page, Sort};
use crate::matching;
use crate::notations::PROPERTY_OF;

/// Whether a lemma's ask is one only set.mm makes, which an item never lists
/// (`DATABASE.md`, `metamath-hypotheses`): each part of it a membership of
/// ℂ, as a point is one, or of the class of all sets.
fn asked_by_setmm_alone(ask: &Term) -> bool {
    conjuncts_of(ask).iter().all(|part| {
        part.label() == Some("wcel")
            && matches!(
                part.children().get(1).and_then(Term::label),
                Some("cc" | "cvv")
            )
    })
}

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
        // body holds of it, each from what the checker recorded as showing
        // it (`Exhibit::shown`): the membership, then the body's parts.
        let read = self.exhibit_read(step)?;
        let values: NodeBinding = read.values.into_iter().collect();
        let recorded = read.shown;
        let Some((first, rest)) = recorded.split_first() else {
            return Err(self.unreached(
                step.line,
                "the checker recorded nothing showing the witness in its domain",
            ));
        };
        let in_domain =
            self.shown_proof(step, first, &values, &member, scope, &known)?;
        let said = self.shown_body(
            step,
            &self.to_term(&here),
            rest,
            &values,
            false,
            scope,
            &known,
        )?;
        let shown = [in_domain, said];
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
    /// with as many witnesses as it quantifies over, is shown at the
    /// witnesses the checker recorded it unfolded at (`folded_at_witness`),
    /// and the definition folds it into the claim.
    pub(super) fn conclude(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
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
        let mut rules = matching::Binding::new();
        for (name, node) in self.matched_here(step, cited)? {
            if node.notation() == PROPERTY_OF {
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
                let right =
                    citing::filled(&node.children[1], &rules, &me.item_library().ctx);
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
        let p_ex =
            take!(self.folded_at_witness(step, &whole, flipped, scope, &supplied)?);
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
        // The facts the checker recorded as supplying the item's hypotheses,
        // which discharge the lemma's antecedents that are those hypotheses.
        let given = self.recorded_hypotheses(step, scope, facts)?;
        // The facts carried to the hypotheses are the step's own, which a
        // lemma asking one under its own context, `( ph /\ k e. A ) -> B = C`
        // of a sum's term, settles from as from a line.
        let facts = &facts.with(&given);
        let kept = self.hypotheses_given.replace(given);
        // The claim as the record reads it, and where the record names a
        // witness the item's lemmas build together, as they build it.
        let found = match self.recorded_library(step, term, scope, facts, item, &seed) {
            Ok(Some(p)) => Ok(Built(p)),
            Ok(None) => self.by_lemmas(&labels, term, scope, facts, step, Some(&seed)),
            Err(e) => Err(e),
        };
        self.hypotheses_given = kept;
        match found? {
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
                    || !matching::alike(left, right, &library.ctx, &none, &none)
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

    /// The part of its lemma's conclusion a sentence read `way` is, through
    /// the side its `metamath-reads` names (`LemmaSide`), the two sides
    /// swapped where it says `turned`.
    fn side_of(
        &self,
        step: &Step,
        way: citing::Way,
        reading: LemmaReading,
    ) -> Checked<LemmaSide> {
        let side = match (way, reading.side) {
            (citing::Way::AsWritten, None) => LemmaSide::Whole,
            (citing::Way::AsWritten, Some(Side::Left)) => LemmaSide::Left,
            (citing::Way::AsWritten, Some(Side::Right)) => LemmaSide::Right,
            (citing::Way::Forward, None) => LemmaSide::Right,
            (citing::Way::Backward, None) => LemmaSide::Left,
            (_, Some(_)) => {
                return Err(self.unreached(
                    step.line,
                    "the checker read through a sentence the record says is a side of its lemma",
                ))
            }
        };
        Ok(match (side, reading.turned) {
            (LemmaSide::Left, true) => LemmaSide::Right,
            (LemmaSide::Right, true) => LemmaSide::Left,
            (side, _) => side,
        })
    }

    /// A step citing a record, read as the checker recorded it: for each
    /// conclusion the record names (`Cited::concluded`), the item's sentence
    /// read the recorded way at the citation's values (`sentence_read`),
    /// proved by the lemma the record pairs it with (`sentence_lemmas`), at
    /// the side and the part its `metamath-reads` names (`lemma_instance`);
    /// and the claim made of those as `claim_from_readings` makes it, each
    /// part of it carried as the record says it meets the claim. None where
    /// the record names a witness the lemmas build together, which is read
    /// otherwise (`by_lemmas`).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn recorded_library(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        item: &'a Record,
        seed: &Binding,
    ) -> Checked<Option<Proof>> {
        let Some(cited) = self.citation_read(step).cloned() else {
            return Err(self.unreached(
                step.line,
                "the checker recorded no reading of this citation",
            ));
        };
        let paired = targets::sentence_lemmas(item)
            .map_err(|why| self.defect(step.line, format!("{}: {why}", cited.item)))?;
        // Each concluded sentence is applied at the record's reading of it,
        // in the item's letters; `claim_from_readings` carries the readings
        // to the claim as the record's meetings say they meet.
        let mut readings = Vec::new();
        for (k, concluded) in cited.concluded.iter().enumerate() {
            let Some(paired) = paired.get(concluded.sentence) else {
                return Err(self.unreached(
                    step.line,
                    "the checker concluded a sentence the record pairs with no lemma",
                ));
            };
            if paired.reading.witness {
                return Ok(None);
            }
            let side = self.side_of(step, concluded.way, paired.reading)?;
            self.premise_given(step, &cited, k, scope, facts)?;
            let instance = self.sentence_read(
                step,
                &cited,
                concluded.sentence,
                concluded.way,
                LemmaReading::default(),
            )?;
            let label = paired.labels[0].clone();
            let proof = self.lemma_instance(
                &label,
                &instance,
                side,
                paired.reading.part,
                scope,
                facts,
                step,
                seed,
            )?;
            let proof = match proof {
                Built(p) => p,
                Declined(d) => {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "{label}, which {} names, does not give {}: {}",
                            cited.item,
                            self.render(&self.rpn(&instance)),
                            self.say(&d)
                        ),
                    ));
                }
            };
            readings.push((self.rpn(&instance), proof));
        }
        self.claim_from_readings(step, term, &cited, readings, scope, facts)
            .map(Some)
    }

    /// For the `k`th concluded sentence read through its `↔` or "if", the
    /// side it is read from, proved from where the checker recorded its
    /// parts stand (`firsts_proof`), and given to the lemma as a recorded
    /// hypothesis is (`hypotheses_given`). Nothing for a sentence read as
    /// written.
    fn premise_given(
        &mut self,
        step: &Step,
        cited: &Cited,
        k: usize,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<()> {
        let concluded = &cited.concluded[k];
        if concluded.way == citing::Way::AsWritten {
            return Ok(());
        }
        let firsts = cited.firsts.get(k).map_or(&[][..], Vec::as_slice);
        let whole = self.sentence_read(
            step,
            cited,
            concluded.sentence,
            citing::Way::AsWritten,
            LemmaReading::default(),
        )?;
        let [a, b] = whole.children() else {
            return Err(self.unreached(
                step.line,
                "the checker read a sentence through, which is no ↔ or if",
            ));
        };
        let premise = match concluded.way {
            citing::Way::Backward => self.rpn(b),
            _ => self.rpn(a),
        };
        // The step's requires lines, each proved with the ones above it, as
        // a recorded hypothesis is carried from them (`recorded_hypotheses`).
        let facts = &facts.with(&self.supplied(Some(step), scope, facts)?);
        let Some(proof) = self.firsts_proof(step, firsts, &premise, scope, facts)?
        else {
            return Err(self.defect(
                step.line,
                format!(
                    "{} gives what step {} claims where {} holds, and the line the checker read that from does not give it",
                    step.just.head,
                    step.number,
                    self.render(&premise)
                ),
            ));
        };
        let given = self.hypotheses_given.get_or_insert_with(Facts::new);
        let given = given.clone();
        self.know(&given, premise, proof);
        Ok(())
    }

    /// ( scope -> goal ) for an obtain citing a record: the sentence the
    /// checker obtains from (`Cited::obtained`), taken whole, proved by the
    /// lemma the record pairs it with (`sentence_lemmas`) at the side and
    /// the part its `metamath-reads` names (`lemma_instance`), as a citation
    /// proves a sentence it concludes. None where the record names a witness
    /// the item's lemmas build together (`by_lemmas`).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn obtained_library(
        &mut self,
        step: &Step,
        goal: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        item: &'a Record,
        seed: &Binding,
    ) -> Checked<Option<Proof>> {
        let Some(cited) = self.citation_read(step).cloned() else {
            return Err(self.unreached(
                step.line,
                "the checker recorded no reading of this citation",
            ));
        };
        let paired = targets::sentence_lemmas(item)
            .map_err(|why| self.defect(step.line, format!("{}: {why}", cited.item)))?;
        let Some(paired) = cited.obtained.and_then(|i| paired.get(i)) else {
            return Err(self.unreached(
                step.line,
                "the checker obtains from a sentence the record pairs with no lemma",
            ));
        };
        if paired.reading.witness {
            return Ok(None);
        }
        let side = self.side_of(step, citing::Way::AsWritten, paired.reading)?;
        let label = paired.labels[0].clone();
        let goal_term = self.to_term(goal);
        let proof = self.lemma_instance(
            &label,
            &goal_term,
            side,
            paired.reading.part,
            scope,
            facts,
            step,
            seed,
        )?;
        match proof {
            Built(p) => Ok(Some(p)),
            Declined(d) => Err(self.defect(
                step.line,
                format!(
                    "{label}, which {} names, does not give what step {} obtains from: {}",
                    cited.item,
                    step.number,
                    self.say(&d)
                ),
            )),
        }
    }

    /// ( scope -> instance ) by `label`: the lemma applied at the side of
    /// its conclusion `side` names, or, where its conclusion is an "and"
    /// the sentence is part `part` of (`metamath-reads part N`), applied at
    /// the whole that part fits and the part taken out of it.
    #[allow(clippy::too_many_arguments)]
    fn lemma_instance(
        &mut self,
        label: &str,
        instance: &Term,
        side: LemmaSide,
        part: Option<usize>,
        scope: &Rpn,
        facts: &Facts,
        step: &Step,
        seed: &Binding,
    ) -> Checked<Route<Proof>> {
        let Some(q) = part else {
            self.lemma_side = Some(side);
            return self.apply_lemma(
                label,
                instance,
                scope,
                facts,
                Some(step),
                true,
                Some(seed),
            );
        };
        let statement = self.statement(label);
        let variables = names_of(&statement);
        let mut concluded = statement;
        while concluded.label() == Some("wi") {
            concluded = concluded.children()[1].clone();
        }
        let whole = match (side, concluded.label()) {
            (LemmaSide::Left, Some("wb")) => concluded.children()[0].clone(),
            (LemmaSide::Right, Some("wb")) => concluded.children()[1].clone(),
            _ => concluded,
        };
        let Some(piece) = conjuncts_of(&whole).get(q).cloned() else {
            return Ok(Route::no(format!("{label} concludes no part {}", q + 1)));
        };
        let Some(mut binding) = self.fits_as(&piece, instance, &variables, Some(seed))
        else {
            return Ok(Route::no(format!(
                "part {} of {label} is not the sentence",
                q + 1
            )));
        };
        // A part need not name every variable of the whole: what is left
        // open is what the item's hypotheses say at the citation's values,
        // each the lemma's ask in the order the record says it asks them
        // (`metamath-hypotheses`, the item's order by default).
        if names_of(&whole).iter().any(|v| !binding.contains_key(v)) {
            let asks = self.lemma_asks(label, side);
            let hypotheses = self.item_hypotheses_read(step)?;
            if asks.len() != hypotheses.len() {
                return Ok(Route::no(format!(
                    "{label} asks {} facts the item lists, and the item lists {}",
                    asks.len(),
                    hypotheses.len()
                )));
            }
            for (ask, said) in asks.iter().zip(&hypotheses) {
                let Some(filled) = fit(ask, said, &binding, &variables) else {
                    return Ok(self.no(
                        format!("{label} asks {{}} where the item says {{}}"),
                        &[&self.rpn(ask), &self.rpn(said)],
                    ));
                };
                binding = filled;
            }
        }
        let at = whole.substitute(&binding);
        self.lemma_side = Some(side);
        let proved = take!(self.apply_lemma(
            label,
            &at,
            scope,
            facts,
            Some(step),
            true,
            Some(seed)
        )?);
        // The part by its place, carried to the sentence where set.mm spells
        // it otherwise, x =/= y for the page's x ≠ y.
        let at = self.rpn(&at);
        let Some((taken, proof)) =
            self.conjuncts_proved(&at, proved, scope).get(q).cloned()
        else {
            return Ok(Route::no(format!("{label} concludes no part {}", q + 1)));
        };
        let target = self.rpn(instance);
        Ok(
            match self.same_carried(&taken, proof, &target, scope, facts)? {
                Some(p) => Built(p),
                None => {
                    Route::no(format!("part {} of {label} is not the sentence", q + 1))
                }
            },
        )
    }

    /// What the lemma `label` asks that an item lists, in order: each
    /// antecedent whole, as a hypothesis set.mm writes as several facts
    /// joined (between, as three) is one the item lists; then, where the
    /// sentence is one side of its `↔` (`side`), the other side, which it is
    /// read from. A fact only set.mm asks, points in ℂ or a class a set, is
    /// not listed (`DATABASE.md`, `metamath-hypotheses`), and is left out.
    fn lemma_asks(&self, label: &str, side: LemmaSide) -> Vec<Term> {
        let mut asks = Vec::new();
        let mut walk = self.statement(label);
        while walk.label() == Some("wi") {
            asks.push(walk.children()[0].clone());
            walk = walk.children()[1].clone();
        }
        if walk.label() == Some("wb") {
            match side {
                LemmaSide::Left => asks.push(walk.children()[1].clone()),
                LemmaSide::Right => asks.push(walk.children()[0].clone()),
                LemmaSide::Whole => {}
            }
        }
        asks.into_iter()
            .filter(|a| !asked_by_setmm_alone(a))
            .collect()
    }

    /// What each hypothesis of the item a step cites says at the citation's
    /// values (`Cited::supplied`, `binding_with_written`), as terms in the
    /// step's names, in the order its lemma asks them: the record's
    /// `metamath-hypotheses`, and the item's order where it says nothing.
    fn item_hypotheses_read(&mut self, step: &Step) -> Checked<Vec<Term>> {
        let Some(cited) = self.citation_read(step).cloned() else {
            return Ok(Vec::new());
        };
        let order = match self.items.get(&cited.item) {
            Some(Item::Record(r)) => {
                let labels = r.metamath_hypotheses().map_err(|why| {
                    self.defect(step.line, format!("{}: {why}", cited.item))
                })?;
                labels
                    .iter()
                    .filter_map(|l| {
                        r.hypotheses
                            .iter()
                            .position(|h| h.label.as_deref() == Some(l))
                    })
                    .collect()
            }
            _ => Vec::new(),
        };
        let mut listed: Vec<&Supplied> =
            cited.supplied.iter().filter(|s| s.at.is_some()).collect();
        if !order.is_empty() {
            listed.sort_by_key(|s| {
                let at = s.at.map_or(usize::MAX, |a| a.line);
                order.iter().position(|o| *o == at).unwrap_or(usize::MAX)
            });
        }
        let library = self.item_library();
        let binding: NodeBinding = cited.binding_with_written().into_iter().collect();
        let mut out = Vec::new();
        for supplied in listed {
            let at = filled(&supplied.want, &binding, &library.ctx);
            let read = self.term(&at)?;
            out.push(self.to_term(&read));
        }
        Ok(out)
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
        let mut names = Vec::new();
        let mut terms = Vec::new();
        for (name, formula) in &fills {
            let fill = Written::new(formula, &item.path, item.line);
            let node =
                self.in_its_names(Item::Record(item), |me| me.read_one(&fill))?;
            let node = filled(&node, &bound, &library.ctx);
            let term = self.term(&node)?;
            names.push(Symbol::of(name));
            terms.push(self.to_term(&term));
        }
        let Some(apart) = self.put_apart(&terms, &Binding::new(), &theirs) else {
            return Err(self.defect(
                step.line,
                "no letter is left to keep a fill's bound letters apart from the lemma's",
            ));
        };
        Ok(names.into_iter().zip(apart).collect())
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
    /// citation fixes it, as a term in the step's own names, each read in
    /// the names as they stand before any is given, as the checker read the
    /// citation (`cited_here`): first what the citation's own pairs give as
    /// the page writes them (`Cited::written`), `a := b/k, b := a/k` swapping
    /// the two, a define they name kept by its name, then what
    /// its match gives the rest (`Cited::binding`). An obtain's is read off
    /// the lines it cites, as `obtain B: thm:convergent-bounded, from 1.1`
    /// finds x in 1.1.
    pub(in crate::elab) fn corpus_matched(
        &mut self,
        step: &Step,
        other: &'a Theorem,
    ) -> Checked<IndexMap<String, Rpn>> {
        let mut out = IndexMap::new();
        let obtain = step.just.head.is(Method::Obtain);
        let taken = self.cited_here(step, &other.qualified())?;
        for (name, node) in &taken.written {
            let value = self.matched_value(other, name, node, &taken.binding)?;
            out.insert(name.to_string(), value);
        }
        // A name the match gives itself, as a library function's C in
        // C(m, k) is, stands as it already does.
        for (name, node) in &taken.binding {
            if out.contains_key(name.as_str()) || (node.is_name() && node.text == *name)
            {
                continue;
            }
            // An obtain reads a letter the proof names by the same word as
            // that name, as it reads the item's sentence; only a letter the
            // proof has no name for is taken from the lines.
            if obtain && self.names.contains_key(name.as_str()) {
                continue;
            }
            let value = self.matched_value(other, name, node, &taken.binding)?;
            out.insert(name.to_string(), value);
        }
        Ok(out)
    }

    /// A letter of the cited corpus theorem `other` at its value `node`, as
    /// a term in the step's names. A function letter given a rule, t := x ↦
    /// x·c, by the match or by the citation's own pair where the define it
    /// names is read out, stands for the map the rule is over the letter's
    /// domain, as a function a define gives by a rule is read where it is
    /// written alone (`rule_as_map`).
    fn matched_value(
        &mut self,
        other: &'a Theorem,
        name: &Symbol,
        node: &Node,
        binding: &NodeBinding,
    ) -> Checked<Rpn> {
        if node.notation() == PROPERTY_OF {
            if let Some(map) = self.rule_as_map(other, name, node, binding)? {
                return self.term(&map);
            }
        }
        self.term(node)
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
            let (FUNCTION_TYPE, [f, domain, _]) =
                (typed.notation(), typed.children.as_slice())
            else {
                continue;
            };
            if !(f.is_name() && f.text == name) {
                continue;
            }
            let domain =
                matching::substitute_apart_by(domain, binding, &self.g.binders());
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
                .unwrap_or_else(Sort::unknown);
            let letter = Node::name(sort, fresh);
            let mut put = NodeBinding::new();
            put.insert(rule.text, letter.clone());
            let body = matching::substitute_apart_by(body, &put, &self.g.binders());
            return Ok(page::made_as(
                self.g,
                "the map sending _ ∈ _ to _",
                vec![letter, domain, body],
            ));
        }
        Ok(None)
    }
}
