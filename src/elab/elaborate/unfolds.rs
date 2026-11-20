//! Unfolding definitions and hypotheses.

use super::*;

/// The side of a substitution's equation put for the other, the term that
/// stands in the line and the term put in its place
/// (`SubstitutionPlaces::turned`).
#[derive(Clone, Copy)]
pub(super) struct PutFor<'t> {
    pub(super) was: &'t Rpn,
    pub(super) now: &'t Rpn,
}

impl<'a> Elaborator<'a> {
    /// A hypothesis of the theorem as its one sentence reads in the proof,
    /// carried from the hypothesis as it is held. Where the theorem is
    /// stated over a define, the hypothesis is held written out, as the
    /// statement says it, while the steps speak of the name (`ELABORATION.md`,
    /// a definition from outside the theorem); `same` carries one to the
    /// other, reading the name as its rule where the facts put each argument
    /// in the define's domain. The step reads the defines the hypothesis
    /// names without citing them, as a step citing a theorem stated over them
    /// does (`sorts::stated_over`), and rests on them so (`named`). A decline
    /// where the two are one term, the line says several sentences, or the
    /// facts do not carry it.
    pub(super) fn hypothesis_by_its_names(
        &mut self,
        label: &str,
        lines: &Lines,
        held: &Proof,
        scope: &Rpn,
        facts: &Facts,
        step: &Step,
    ) -> Checked<Route<Line>> {
        let (Some(line), Some(as_held)) =
            (lines.get(label), self.line_written(label, lines))
        else {
            return Ok(Route::no("the label names no line"));
        };
        let sentences = self.line_sentences(label, lines);
        let [sentence] = sentences.as_slice() else {
            return Ok(Route::no("the line says several sentences"));
        };
        let named = self.term(sentence)?;
        if named == as_held.claim {
            return Ok(Route::no("the line is held as it reads"));
        }
        // The domains are the step's requires lines' to say, laid over the
        // scope's facts as an identity law's operand is (`identity_law`).
        let written = Facts::new();
        for (k, w) in self.written.entries() {
            if let Some(lifted) = self.lifted_to(&k, &w.proof, &w.at, scope) {
                self.know(&written, k, lifted);
            }
        }
        let offered = facts.with(&written);
        let kept = self.resting.clone();
        let over = self.hypothesis_defines(label);
        if let Some(allowed) = &mut self.resting {
            allowed.extend(over);
        }
        let offered = self.in_hand(&offered);
        let alike = self.same(
            &self.to_term(&as_held.claim),
            &self.to_term(&named),
            scope,
            &offered,
            Some(step),
        );
        self.resting = kept;
        let alike = take!(alike?);
        let proof = pf!(self.b; scope, as_held.claim, named, held, alike, "mpbid");
        Ok(Built(line.restated(named, proof)))
    }

    /// ( scope -> start = other ), where `other` is `start` with the
    /// equation put in and an identity element it makes left out:
    /// C(0, 0)·x^0 with C(0, 0) = 1 put in is 1·x^0, written x^0
    /// (`substituted_tidied` for a line put into).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn replaced_tidied(
        &mut self,
        start: &Rpn,
        other: &Rpn,
        put: PutFor<'_>,
        scope: &Rpn,
        equation: &Facts,
        facts: &Facts,
        step: &Step,
    ) -> Checked<Option<Proof>> {
        let bare =
            |me: &Self, rpn: &Rpn| me.rpn(&me.without_identities(&me.to_term(rpn)));
        let goal = bare(self, other);
        let now_term = self.to_term(put.now);
        let made = self.replaced(&self.to_term(start), put.was, &now_term);
        let literal = self.rpn(&made);
        if literal == *start || bare(self, &literal) != goal {
            return Ok(None);
        }
        let Built(put) = self.congruence(
            &self.to_term(start),
            &made,
            scope,
            equation,
            Some(step),
            &Leaf::Rows(vec![super::super::tables::Row::Held]),
        )?
        else {
            return Ok(None);
        };
        let Built(across) = self.congruence(
            &made,
            &self.to_term(other),
            scope,
            facts,
            None,
            &Leaf::Rows(vec![super::super::tables::Row::Identity]),
        )?
        else {
            return Ok(None);
        };
        Ok(Some(self.chained(
            scope,
            &[
                ChainLink {
                    from: self.to_term(start),
                    to: made.clone(),
                    proof: put,
                },
                ChainLink {
                    from: made,
                    to: self.to_term(other),
                    proof: across,
                },
            ],
        )))
    }

    /// A substitution whose claim leaves out an identity element it makes
    /// (`SYNTAX.md`): p(a) = 0 put into p(x) = (x − a)·q(x) + p(a) makes
    /// p(x) = (x − a)·q(x) + 0, and the claim says p(x) = (x − a)·q(x). The
    /// equation is put in at every place, that line is reached by the
    /// equation alone as any substitution is, and it is carried to the claim
    /// by dropping its identity elements (`tidied`). None where the two
    /// differ in anything else.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn substituted_tidied(
        &mut self,
        start: &Rpn,
        aim: &Rpn,
        given: &Proof,
        put: PutFor<'_>,
        scope: &Rpn,
        equation: &Facts,
        facts: &Facts,
        step: &Step,
    ) -> Checked<Option<Proof>> {
        let bare =
            |me: &Self, rpn: &Rpn| me.rpn(&me.without_identities(&me.to_term(rpn)));
        let goal = bare(self, aim);
        let now_term = self.to_term(put.now);
        let made = self.replaced(&self.to_term(start), put.was, &now_term);
        let literal = self.rpn(&made);
        if literal == *start || bare(self, &literal) != goal {
            return Ok(None);
        }
        let Built(alike) = self.congruence(
            &self.to_term(start),
            &made,
            scope,
            equation,
            Some(step),
            &Leaf::Rows(vec![super::super::tables::Row::Held]),
        )?
        else {
            return Ok(None);
        };
        let reached = pf!(self.b; scope, start, literal, given, alike, "mpbid");
        self.tidied(&reached, &literal, aim, scope, facts)
    }

    /// A definition whose right side is not an existence claim, read the way
    /// the text reads it: right to left.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn one_equivalent(
        &mut self,
        lemma: &str,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let refs = &step.just.refs;
        // A claim the lemma's left side fits only as the standard form reads
        // it is reached at the lemma's own instance and carried by `same`.
        let mut whole = self.statement(lemma);
        while whole.label() == Some("wi") {
            whole = whole.children()[1].clone();
        }
        let binding = if whole.label() == Some("wb") {
            let variables = names_of(&whole);
            self.fits_as(&whole.children()[0], &self.to_term(term), &variables, None)
        } else {
            None
        };
        let instance = match &binding {
            Some(b) => self.rpn(&whole.children()[0].substitute(b)),
            None => term.clone(),
        };
        if instance != *term {
            let made = take!(
                self.one_equivalent(lemma, step, &instance, scope, facts, lines)?
            );
            let held = self.known_implied(Some(step), scope, facts)?;
            let alike = take!(self.same_through_names(
                &self.to_term(&instance),
                &self.to_term(term),
                scope,
                &held,
                None,
            )?);
            return Ok(Built(
                pf!(self.b; scope, instance, term, made, alike, "mpbid"),
            ));
        }
        // What a lemma's right side says beyond what its left fixes can only
        // come from the lines the step cites, in the order it writes them.
        let said: Vec<Rpn> = refs
            .iter()
            .filter_map(|r| self.line_written(r, lines).map(|l| l.claim))
            .collect();
        let mut hint = said.first().cloned();
        for extra in said.iter().skip(1) {
            hint = Some(t!(hint.unwrap(), extra, "wa"));
        }
        // The right side is what the step supplies, and not whatever the
        // scope would give; and what the lemma asks is asked of the same,
        // its requires lines included, as where a definition unfolds.
        let known = self.known_implied(Some(step), scope, facts)?;
        let (says, right) = take!(self.unfolding(
            step,
            lemma,
            term,
            None,
            None,
            None,
            scope,
            &known,
            hint.as_ref()
        )?);
        // The right side is settled as the checker reads the lines that
        // answer it, with identity elements dropped (`settle_or_bare`).
        let under = take!(self.settle_or_bare(
            &self.to_term(&right),
            scope,
            &known,
            Some(step),
            Some(lines)
        )?);
        Ok(Built(
            pf!(self.b; scope, term, right, under, says, "mpbird"),
        ))
    }

    /// `(binding, proof of the left side at it)` from one of the things a
    /// cited line says: matched as written, with only defined names read,
    /// and as the standard form reads it; no one of the three covers the
    /// others.
    pub(super) fn unfolds_from(
        &mut self,
        left: &Term,
        held: &Facts,
        variables: &Vars,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<(Binding, Proof)>> {
        let entries = held.entries();
        for (said, shown) in &entries {
            if let Some(binding) =
                fit(left, &self.to_term(said), &Binding::new(), variables)
            {
                if !binding.is_empty() {
                    return Ok(Built((binding, shown.clone())));
                }
            }
        }
        // Then with only the defined names read as what they name, and then
        // with a defined function read where it is applied as well: u ∈ I(k),
        // I a define, says u is in what I's rule gives at k.
        let mut readings: Vec<(Rpn, Proof, Term)> = Vec::new();
        for (said, shown) in &entries {
            let read = self.names_read(&self.to_term(said), None);
            readings.push((said.clone(), shown.clone(), read));
        }
        for (said, shown) in &entries {
            let read = self.read_through(&self.to_term(said), true, None);
            readings.push((said.clone(), shown.clone(), read));
        }
        for (said, shown, read) in &readings {
            let read_rpn = self.rpn(read);
            if read_rpn == *said {
                continue;
            }
            let Some(binding) =
                fit(left, read, &Binding::new(), variables).filter(|b| !b.is_empty())
            else {
                continue;
            };
            if let Built(alike) =
                self.same(&self.to_term(said), read, scope, facts, None)?
            {
                return Ok(Built((
                    binding,
                    pf!(self.b; scope, said, read_rpn, shown, alike, "mpbid"),
                )));
            }
        }
        for (said, shown) in &entries {
            let Some(binding) = self
                .fits_as(left, &self.to_term(said), variables, None)
                .filter(|b| !b.is_empty())
            else {
                continue;
            };
            let instance = left.substitute(&binding);
            if let Built(alike) =
                self.same(&self.to_term(said), &instance, scope, facts, None)?
            {
                let i = self.rpn(&instance);
                return Ok(Built((
                    binding,
                    pf!(self.b; scope, said, i, shown, alike, "mpbid"),
                )));
            }
        }
        // Then with a defined function applied read as its rule at what it
        // is applied to, as `c ∈ G(m, n)` is a member of G's rule at m, n.
        for (said, shown) in &entries {
            let read = self.read_out(&self.to_term(said));
            let read_rpn = self.rpn(&read);
            if read_rpn == *said {
                continue;
            }
            let Some(binding) =
                fit(left, &read, &Binding::new(), variables).filter(|b| !b.is_empty())
            else {
                continue;
            };
            if let Built(alike) =
                self.same(&self.to_term(said), &read, scope, facts, None)?
            {
                return Ok(Built((
                    binding,
                    pf!(self.b; scope, said, read_rpn, shown, alike, "mpbid"),
                )));
            }
        }
        Ok(Route::no("nothing the line says is what the lemma unfolds"))
    }

    /// Where the checker read the step's citation of a record as taken from
    /// (`Cited::firsts`): the cited line, or the sentence of one, a
    /// definition is unfolded from.
    pub(super) fn firsts_here(&self, step: &Step) -> Checked<Vec<FirstAt>> {
        let Some(cited) = step.just.cited_item() else {
            return Ok(Vec::new());
        };
        let name = self.thm.names.full(&cited);
        let Some(Item::Record(item)) = self.items.get(&name).copied() else {
            return Ok(Vec::new());
        };
        Ok(self
            .cited_here(step, &item.qualified())?
            .firsts
            .into_iter()
            .filter_map(|by| match by {
                SuppliedBy::Line(at) => Some(at),
                _ => None,
            })
            .collect())
    }

    /// What the line `at` names says there, as the checker read it
    /// (`FirstAt::written`): the sentence, the part of one, or a "for all"
    /// of it read at a block's letter.
    pub(in crate::elab) fn recorded_statement(&mut self, at: &FirstAt) -> Checked<Rpn> {
        self.term(&at.written)
    }

    /// Each hypothesis of the step's citation of `item`, in set.mm at the
    /// citation's values, with the proof of the fact the checker recorded
    /// as supplying it (`Cited::supplied`, `recorded_fact`): the fact as it
    /// stands where it is the hypothesis, and carried by `same` where the
    /// line says it otherwise. A hypothesis the record gives no line for,
    /// said once or unstated, is not among them.
    pub(in crate::elab) fn recorded_hypotheses(
        &mut self,
        step: &Step,
        item: &'a Record,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Facts> {
        let given = Facts::new();
        let Some(cited) = self.citation_read(step).cloned() else {
            return Ok(given);
        };
        let binding = self.matched_here(step, item)?;
        let library = self.item_library();
        let lines = self.lines.clone();
        for supplied in &cited.supplied {
            let Some((said, proof)) =
                self.recorded_fact(step, &supplied.by, scope, facts, &lines)?
            else {
                continue;
            };
            let node = filled(&supplied.want, &binding, &library.ctx);
            let wanted = self.term(&node)?;
            if said == wanted {
                self.know(&given, wanted, proof);
                continue;
            }
            let (from, to) = (self.to_term(&said), self.to_term(&wanted));
            if let Built(alike) = self.same(&from, &to, scope, facts, Some(step))? {
                let carried = pf!(self.b; scope, said, wanted, proof, alike, "mpbid");
                self.know(&given, wanted, carried);
            }
        }
        Ok(given)
    }

    /// The fact the checker recorded as supplied by `by`, as the line says
    /// it in set.mm, with its proof: in a line the step names, the
    /// statement the checker found it in (`recorded_statement`), matched to
    /// what the line says up to a renamed bound variable; in one of the
    /// step's requires lines, its claim. None for a fact said once or
    /// unstated, or one a line implies without writing it, which the
    /// backend works out (`settle`); and for a line saying nothing the
    /// checker read there.
    pub(in crate::elab) fn recorded_fact(
        &mut self,
        step: &Step,
        by: &SuppliedBy,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Option<(Rpn, Proof)>> {
        match by {
            SuppliedBy::Line(at) => self.line_fact(at, scope, facts, lines),
            SuppliedBy::Requires {
                line,
                implied: None,
            } => {
                let Some(r) = step.requires.get(*line) else {
                    return Ok(None);
                };
                let said = self.claim_of(&r.fact)?;
                Ok(self.held(facts, &said, scope)?.map(|p| (said, p)))
            }
            _ => Ok(None),
        }
    }

    /// The fact a line states where the checker placed it (`FirstAt`), as the
    /// line says it in set.mm up to a renamed bound variable, with its proof;
    /// None for a fact the line implies without writing it, and where the
    /// line says nothing the checker read there.
    pub(in crate::elab) fn line_fact(
        &mut self,
        at: &FirstAt,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Option<(Rpn, Proof)>> {
        if at.implied.is_some() {
            return Ok(None);
        }
        let recorded = self.recorded_statement(at)?;
        let says = self.line_says(&at.line, scope, facts, lines)?;
        for (said, held) in says.entries() {
            let same = said == recorded
                || self
                    .renaming(&self.to_term(&recorded), &self.to_term(&said))?
                    .is_some();
            if same {
                return Ok(Some((said, held)));
            }
        }
        Ok(None)
    }

    /// ( scope -> term ) from the line the checker placed it in (`at`): as
    /// `held` holds it, the line's claim or a conjunct of it, written so or
    /// over other bound letters; that line's statement there, carried by
    /// `same` where the line spells it otherwise, or with an identity
    /// element the claim leaves out, K divides M for K divides M^1, by
    /// `tidied`; a fact the line implies without writing it, `k ≥ 1` of
    /// `k ∈ ℕ`, worked out from what is held (`settle`). None where none
    /// of these gives it.
    pub(in crate::elab) fn placed_proof(
        &mut self,
        at: &FirstAt,
        term: &Rpn,
        held: &Facts,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        if let Some(p) = self.held(held, term, scope)? {
            return Ok(Some(p));
        }
        if let Some(p) = self.held_rebound(held, term, scope)? {
            return Ok(Some(p));
        }
        let lines = self.lines.clone();
        if let Some((said, proof)) = self.line_fact(at, scope, facts, &lines)? {
            if said == *term {
                return Ok(Some(proof));
            }
            if let Built(alike) = self.same(
                &self.to_term(&said),
                &self.to_term(term),
                scope,
                facts,
                None,
            )? {
                return Ok(Some(pf!(self.b; scope, said, term, proof, alike, "mpbid")));
            }
            return self.tidied(&proof, &said, term, scope, facts);
        }
        // What the line says implies it: `k ∈ {1, …, n}` says 1 ≤ k, and
        // `C ∈ 𝒫A` says C ⊆ A, the other spelling of a part of a set.
        for (said, proof) in held.entries() {
            let more = self.implied(&said, &proof, scope, facts)?;
            if let Some(p) = self.held(&more, term, scope)? {
                return Ok(Some(p));
            }
        }
        if at.implied.is_none() {
            return Ok(None);
        }
        Ok(
            match self.settle(&self.to_term(term), scope, facts, 3, None, None)? {
                Built(p) => Some(p),
                Declined(_) => None,
            },
        )
    }

    /// What the line `at` names says there, with its proof and the parts of
    /// it: the sentence `at` names, or the whole line.
    pub(super) fn stated_at(
        &mut self,
        at: &FirstAt,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Facts> {
        let held = Facts::new();
        let Some(cited) = self.line_written(&at.line, lines) else {
            return Ok(held);
        };
        // A sentence past the line's own is a "for all" of it read at a
        // block's letter, which the line inside the block says with the
        // rest (`know_in_scope_at_letters`).
        let sentences = self.line_sentences(&at.line, lines);
        let own = sentences.len();
        let sentence = match at.sentence {
            Some(i) => sentences.get(i),
            None if own == 1 => sentences.first(),
            None => None,
        };
        let said = match at.sentence {
            Some(i) if i < own => Some(self.term(&sentences[i])?),
            Some(i) => self
                .at_letters_of
                .get(&cited.claim)
                .and_then(|at| at.get(i - own))
                .cloned(),
            None => None,
        };
        let (said, proof) = match said {
            Some(said) => {
                let Some(proof) = self.held(facts, &said, scope)? else {
                    return Ok(held);
                };
                (said, proof)
            }
            None => (cited.claim.clone(), self.carried(&at.line, facts, lines)),
        };
        self.know(&held, said.clone(), proof.clone());
        self.unpack_all(&said, &proof, scope, &held);
        let Some(j) = at.part else {
            return Ok(held);
        };
        let parts = match sentence {
            Some(node) => parts_along(node, &self.to_term(&said)),
            None => conjunction_parts(&self.to_term(&said)),
        };
        let Some(part) = parts.get(j).map(|p| self.rpn(p)) else {
            return Ok(Facts::new());
        };
        let one = Facts::new();
        if let Some(proof) = self.held(&held, &part, scope)? {
            self.know(&one, part, proof);
        }
        Ok(one)
    }

    /// What a substitution hypothesis says its property half is, where the
    /// claim already put one of that half's conjuncts in the slot: `elrab`'s
    /// ψ is the whole of "k ∈ S and for all p ∈ S, …" at the element, and a
    /// claim taking "k ∈ T" from it took a part (`citing`, a claim taking a
    /// conjunct of a property). None where the slot is empty, where the
    /// hypothesis is no substitution, or where what it says is no
    /// conjunction.
    pub(super) fn property_whole(
        &self,
        asked: &Term,
        binding: &Binding,
    ) -> Option<Binding> {
        let iff = asked.children().get(1)?;
        let slot = iff.children().get(1)?.variable_symbol()?;
        binding.get(&slot)?;
        let mut without = binding.clone();
        without.shift_remove(&slot);
        let more = self.substituted_slot(asked, &without)?;
        let said = more.get(&slot)?;
        (conjuncts_of(said).len() > 1).then_some(more)
    }

    /// A definition unfolded to reach one part of what it says: read left to
    /// right, from what the checker read it as taken from, and what it gives
    /// taken apart.
    #[allow(clippy::too_many_arguments)]
    pub fn one_unfolded(
        &mut self,
        lemma: &str,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let sig = self.sig(lemma).clone();
        let whole = self.statement(lemma);
        let variables = names_of(&whole);
        let mut reads = whole.clone();
        while reads.label() == Some("wi") {
            reads = reads.children()[1].clone();
        }
        if reads.label() != Some("wb") {
            return Ok(Route::no(format!("{lemma} states no biconditional")));
        }
        // What the step names, requires lines included: what the unfolding
        // asks, as a defined function's argument in its domain where a
        // cited line applies one, comes from these.
        let supplied = self.supplied(Some(step), scope, facts)?;
        let named = self.with_cited(Some(step), scope, &supplied, None)?;
        // A line may say several things at once, and what the definition
        // unfolds is the one the checker took the reading from (`firsts_here`).
        let mut chosen = None;
        for at in self.firsts_here(step)? {
            let held = self.stated_at(&at, scope, facts, lines)?;
            if let Built(found) = self.unfolds_from(
                &reads.children()[0],
                &held,
                &variables,
                scope,
                &named,
            )? {
                chosen = Some(found);
                break;
            }
        }
        // A step said of every member unfolds the membership its claim's
        // "for all" gives, as it would a cited line saying it.
        if chosen.is_none() {
            if let Some(member) = self.member.clone() {
                if let Some(p) = self.held(facts, &member, scope)? {
                    let held = Facts::new();
                    self.know(&held, member, p);
                    if let Built(found) = self.unfolds_from(
                        &reads.children()[0],
                        &held,
                        &variables,
                        scope,
                        facts,
                    )? {
                        chosen = Some(found);
                    }
                }
            }
        }
        // A letter's membership in the set its `let` names is said once and
        // never cited (`SYNTAX.md`, "A membership in a number system is said
        // once"), and a definition unfolds it as it would a cited line saying
        // it: `let A ∈ ℚ` unfolds by the definition of a rational. The letter
        // is one the claim speaks of.
        if chosen.is_none() {
            let claimed = self.rpn(&self.to_term(term));
            let introduced: Vec<(Rpn, Rpn)> = self
                .sets
                .iter()
                .filter_map(|(letter, set)| {
                    let said = self.names.get(letter)?;
                    let spoken = !said.is_empty()
                        && claimed
                            .tokens()
                            .windows(said.len())
                            .any(|w| w == said.tokens());
                    spoken.then(|| (said.clone(), set.clone()))
                })
                .collect();
            for (said, set) in introduced {
                let member = t!(said, set, "wcel");
                let Built(p) =
                    self.said_once_proof(&self.to_term(&member), scope, facts)?
                else {
                    continue;
                };
                let held = Facts::new();
                self.know(&held, member, p);
                if let Built(found) = self.unfolds_from(
                    &reads.children()[0],
                    &held,
                    &variables,
                    scope,
                    facts,
                )? {
                    chosen = Some(found);
                    break;
                }
            }
        }
        let Some((mut binding, given)) = chosen else {
            return Ok(Route::no(format!("no cited line is what {lemma} unfolds")));
        };
        // What the left side fixes need not be everything the right side
        // holds: the rest is what the claim says there, fitted as written and
        // then as the standard form reads the two, as `unfolding` fits its
        // hint (the page's ε > 0 is set.mm's ε ∈ ℝ⁺).
        let target = self.to_term(term);
        // A claim of the whole right side, its bound letters spelt apart, is
        // what the left side and the lemma's own hypotheses fix, and no part
        // of it is fitted to the claim alone.
        let mut whole_fixed = binding.clone();
        for essential in &sig.essentials {
            let asked = self.essential(essential);
            if let Some(more) = self.substituted_slot(&asked, &whole_fixed) {
                whole_fixed.extend(more);
            }
        }
        let right_side = &reads.children()[1];
        let whole_claimed = names_of(right_side)
            .iter()
            .all(|v| whole_fixed.contains_key(v))
            && !self
                .same(
                    &right_side.substitute(&whole_fixed),
                    &target,
                    scope,
                    &named,
                    None,
                )?
                .is_declined();
        if whole_claimed {
            binding = whole_fixed;
        }
        for part in self.parts(&self.rpn(&reads.children()[1])) {
            if whole_claimed {
                break;
            }
            let part = self.to_term(&part);
            // A part the left side has already fixed whole is the claim
            // where the two are one claim, its bound letters spelt apart:
            // the rest of the right side is then left to the lemma's own
            // hypothesis, and fitted to nothing.
            if names_of(&part).iter().all(|v| binding.contains_key(v))
                && !self
                    .same(&part.substitute(&binding), &target, scope, facts, None)?
                    .is_declined()
            {
                break;
            }
            // As written, in the standard form, and with identity elements
            // dropped, as `unfolding` fits its hint: the page's |x| < δ is a
            // limit's |x − c| < δ at c := 0.
            let filled = fit(&part, &target, &binding, &variables)
                .or_else(|| self.fits_as(&part, &target, &variables, Some(&binding)))
                .or_else(|| {
                    let bare = self.identities_dropped(&part, &binding);
                    let held = self.without_identities(&target);
                    fit(&bare, &held, &binding, &variables).or_else(|| {
                        self.fits_as(&bare, &held, &variables, Some(&binding))
                    })
                });
            if let Some(filled) = filled {
                binding = filled;
                break;
            }
        }
        // The claim of the membership half leaves the property half
        // standing as the lemma's own name, and `elrab`'s hypothesis is what
        // says what that half is.
        for essential in &sig.essentials {
            let asked = self.essential(essential);
            let more = self
                .substituted_slot(&asked, &binding)
                .or_else(|| self.property_whole(&asked, &binding));
            if let Some(more) = more {
                for (k, v) in more {
                    binding.insert(k, v);
                }
            }
        }
        // A letter the lemma binds is kept apart from every letter the
        // values spell: `divides` binds n, and unfolding "m + n is even"
        // under it would capture the step's own n. Where one meets, it takes
        // a letter nothing holds, as `applied_body` moves a rule's letter.
        let values: Vec<Term> = binding.values().cloned().collect();
        let spelt: BTreeSet<String> = values
            .iter()
            .flat_map(|v| {
                self.rpn(v)
                    .tokens()
                    .iter()
                    .map(|t| String::from(*t))
                    .collect::<Vec<_>>()
            })
            .collect();
        let meeting: Vec<Symbol> = self
            .letters_bound(&reads)
            .iter()
            .filter(|v| !binding.contains_key(*v) && spelt.contains(&self.float_of(v)))
            .copied()
            .collect();
        if !meeting.is_empty() {
            let seen: Vec<&Term> = values.iter().collect();
            if let Some(moved) = self.unheld_for(meeting, &seen) {
                binding.extend(moved);
            }
        }
        let left = self.rpn(&reads.children()[0].substitute(&binding));
        let right = self.rpn(&reads.children()[1].substitute(&binding));
        // What carries the unfolding to the claim asks from what the step
        // names, requires lines included.
        let facts = named;
        let (made, _) = take!(self.unfolding(
            step,
            lemma,
            &left,
            Some(&right),
            None,
            None,
            scope,
            &facts,
            None
        )?);
        let proof = pf!(self.b; scope, left, right, given, made, "mpbid");
        let known = Facts::new();
        self.know(&known, right.clone(), proof.clone());
        self.unpack_all(&right, &proof, scope, &known);
        if let Some(p) = self.held(&known, term, scope)? {
            return Ok(Built(p));
        }
        // Or it is, once what the lemma says is put in the page's words, or
        // once its identity elements are dropped, as the checker reads it.
        for (said, shown) in known.entries() {
            if let Built(alike) =
                self.same(&self.to_term(&said), &target, scope, &facts, None)?
            {
                return Ok(Built(
                    pf!(self.b; scope, said, term, shown, alike, "mpbid"),
                ));
            }
            if let Some(tidy) = self.tidied(&shown, &said, term, scope, &facts)? {
                return Ok(Built(tidy));
            }
            // Both at once: the identity elements dropped first, and what is
            // left put in the page's words, `-. x = 0` for `x =/= 0` and the
            // page's own bound letters.
            let bare = self.rpn(&self.without_identities(&self.to_term(&said)));
            if bare != said {
                if let Some(tidy) = self.tidied(&shown, &said, &bare, scope, &facts)? {
                    if let Built(alike) =
                        self.same(&self.to_term(&bare), &target, scope, &facts, None)?
                    {
                        return Ok(Built(
                            pf!(self.b; scope, bare, term, tidy, alike, "mpbid"),
                        ));
                    }
                }
            }
        }
        // What the unfolding says and how the readable line spells it are
        // allowed to differ, so long as set.mm says they are the same claim.
        let offered = facts.with(&known);
        match self.settle(&target, scope, &offered, 3, Some(step), Some(lines))? {
            Built(p) => Ok(Built(p)),
            Declined(d) => {
                let inner = self.say(&d);
                Ok(self.no(format!("{lemma} does not say {{}}: {inner}"), &[term]))
            }
        }
    }
}
