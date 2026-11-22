//! Unfolding definitions and hypotheses.

use super::*;
use crate::checker::record::Supplied;
use crate::citing::HypothesisAt;
use crate::corpus::records::LemmaReading;
use crate::elab::provenance::rests_on_only;
use crate::elab::tables::Row;
use crate::matching::{standard, Meeting, Tree};
use crate::notations::{FOR_ALL, PROPERTY_OF};

/// What the checker recorded as supplying a fact (`Supplied`), with the
/// values its hypothesis is read at: the citation's (`binding_with_written`)
/// or an exhibit's. The hypothesis at those values and the line's fact are
/// the two trees its meeting is of (`Supplied::meeting`), whose places a
/// carry follows.
#[derive(Clone, Copy)]
pub(in crate::elab) struct RecordedSupply<'r> {
    pub supplied: &'r Supplied,
    pub values: &'r NodeBinding,
}

/// The two trees a recorded meeting is of, as the record gives them: the
/// one `said`, the fact a proof is in hand for, is the meeting's `said_in`
/// tree, and `wanted` is the other (`carried_at_places`).
pub(in crate::elab) struct PlacedTrees {
    pub(in crate::elab) said: Node,
    pub(in crate::elab) wanted: Node,
    pub(in crate::elab) said_in: Tree,
}

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

    /// How the cited item's definition is written in its lemma, as its
    /// record says (`metamath-reads`): a definition says one sentence. As
    /// stated where the record says nothing.
    fn lemma_reading(&self, cited: &Cited) -> LemmaReading {
        let Some(Item::Record(record)) = self.items.get(&cited.item) else {
            return LemmaReading::default();
        };
        match record.metamath_reads() {
            Ok(all) => all.first().copied().unwrap_or_default(),
            Err(_) => LemmaReading::default(),
        }
    }

    /// The fact a definition is unfolded from, as the checker recorded it
    /// (`Cited::firsts`), with the binding of the lemma's left side `left`
    /// to it and its proof: the line, or the sentence of one, it stands in,
    /// or the membership a `let` says once (`supplied_proof`); or the membership
    /// a step said of every member is proved at (`Elaborator::member`).
    /// The lemma's left side is fitted to the fact as set.mm writes it, or,
    /// where the checker met the two with the line's defined names read out
    /// (`Cited::firsts_meetings`), to the fact read through them, a defined
    /// function where it is applied read as its rule there (`read_out`),
    /// carried there by `same`: u ∈
    /// I(k), I a define, says u is in what I's rule gives at k, which is
    /// set.mm's spelling and none of the page's. Declined where the left side is
    /// not the fact, as a clause of a definition by cases is not.
    fn unfolded_from(
        &mut self,
        step: &Step,
        left: &Term,
        variables: &Vars,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<(Binding, Proof)>> {
        let Some(cited) = self.citation_read(step).cloned() else {
            return Err(self.unreached(
                step.line,
                "the checker recorded no reading of this citation",
            ));
        };
        let Some(first) = cited.firsts.first() else {
            return Err(self.unreached(
                step.line,
                "the checker recorded nothing the definition is unfolded from",
            ));
        };
        let found = match first {
            SuppliedBy::Line(at) | SuppliedBy::SaidOnce(at) => {
                let said = self.recorded_statement(at)?;
                self.supplied_proof(step, first, None, &said, scope, facts)?
                    .map(|p| (said, p))
            }
            SuppliedBy::Bound { .. } => match self.member.clone() {
                Some(member) => self.held(facts, &member, scope)?.map(|p| (member, p)),
                None => None,
            },
            _ => None,
        };
        let Some((said, shown)) = found else {
            return Err(self.unreached(
                step.line,
                "the fact the checker recorded the definition as unfolded from is not in hand",
            ));
        };
        // The line met the definition's side with each define the record
        // places read out there (`Meeting::unfolded`); the member a claim's
        // "for all" gives is read as the claim is, through them.
        let met = cited.firsts_meetings.first().and_then(Option::as_ref);
        let read = match (first, met) {
            (SuppliedBy::Bound { .. }, _) => {
                let written = self.to_term(&said);
                self.read_out(&written)
            }
            (SuppliedBy::Line(at) | SuppliedBy::SaidOnce(at), Some(met))
                if !met.unfolded.is_empty() =>
            {
                let ctx = &self.item_library().ctx;
                let Some(node) =
                    met.with_unfolded(&standard(&at.written, ctx), Tree::Second)
                else {
                    return Err(self.unreached(
                        step.line,
                        "the checker placed a define read out where the line has none",
                    ));
                };
                // A letter the define's body binds that a name of the
                // proof holds is read apart from it (`read_apart`).
                self.read_apart(step, &node)?
            }
            _ => self.to_term(&said),
        };
        let Some(binding) =
            fit(left, &read, &Binding::new(), variables).filter(|b| !b.is_empty())
        else {
            return Ok(Route::no(format!(
                "{} is not what the lemma unfolds",
                self.render(&said)
            )));
        };
        let read_rpn = self.rpn(&read);
        if read_rpn == said {
            return Ok(Built((binding, shown)));
        }
        match self.same(&self.to_term(&said), &read, scope, facts, None)? {
            Built(alike) => Ok(Built((
                binding,
                pf!(self.b; scope, said, read_rpn, shown, alike, "mpbid"),
            ))),
            Declined(_) => Err(self.unreached(
                step.line,
                "the fact read through its defined names is not the fact",
            )),
        }
    }

    /// ( scope -> wanted ), a function's membership in a set of maps, from
    /// its type as the line `at` the checker recorded writes it, held among
    /// the facts as each step types its functions: a function from A to B
    /// is a member of the functions from A to B (`elmapg`), A and B being
    /// sets, carried to `wanted` where that spells the sets otherwise
    /// (`same_carried`). None where `wanted` is no membership in a set of
    /// maps, or the line writes no type that is held.
    fn member_of_maps(
        &mut self,
        at: &FirstAt,
        wanted: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let whole = self.to_term(wanted);
        let (Some("wcel"), [_, maps]) = (whole.label(), whole.children()) else {
            return Ok(None);
        };
        if !self.rpn(maps).ends_with(&["cmap", "co"]) {
            return Ok(None);
        }
        let typed = self.recorded_statement(at)?;
        let said = self.to_term(&typed);
        let (Some("wf"), [domain, codomain, f]) = (said.label(), said.children())
        else {
            return Ok(None);
        };
        let (domain, codomain, f) = (self.rpn(domain), self.rpn(codomain), self.rpn(f));
        let Some(type_proof) = self.held(facts, &typed, scope)? else {
            return Ok(None);
        };
        let member = t!(f, t!(codomain, domain, "cmap", "co"), "wcel");
        let mut sets = Vec::new();
        for set in [&codomain, &domain] {
            let said = t!(set, "cvv", "wcel");
            let proof = match self.held(facts, &said, scope)? {
                Some(p) => p,
                None => match self.made_a_set(&self.to_term(&said), scope, facts)? {
                    Built(p) => p,
                    Declined(_) => return Ok(None),
                },
            };
            sets.push((said, proof));
        }
        let [(set_b, proof_b), (set_a, proof_a)] = [sets[0].clone(), sets[1].clone()];
        let both = pf!(self.b; scope, set_b, set_a, proof_b, proof_a, "jca");
        let law = self.b.ap(
            "elmapg",
            &binds! {"A" => &codomain, "B" => &domain, "C" => &f, "V" => "cvv", "W" => "cvv"},
            &[],
        );
        let iff = pf!(self.b; scope, t!(set_b, set_a, "wa"), t!(member, typed, "wb"), both, law, "syl");
        let made = pf!(self.b; scope, member, typed, type_proof, iff, "mpbird");
        self.same_carried(&member, made, wanted, scope, facts)
    }

    /// ( scope -> wanted ) for a hypothesis of a cited item, from what the
    /// checker recorded as supplying it (`SuppliedBy`): a line, as the
    /// record places the fact in it (`placed_proof`), or a "for all" of it
    /// over a wider set; one of the step's requires lines; a membership
    /// said once or walked to; one a function's type or a subset carries;
    /// the membership the claim's "for all" gives; an identity, or a fact
    /// the values make true, which hold by the values alone; an "and",
    /// part by part. `meeting` is how the line's fact met the hypothesis
    /// (`Supplied::meeting`). None where what the record names does not
    /// give it.
    pub(in crate::elab) fn supplied_proof(
        &mut self,
        step: &Step,
        by: &SuppliedBy,
        recorded: Option<RecordedSupply>,
        wanted: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let meeting = recorded.and_then(|r| r.supplied.meeting.as_ref());
        let lines = self.lines.clone();
        // A function's type the line or the `let` writes is kept among the
        // step's facts, as each step types its functions, and not in the
        // line's claim.
        let typed = self.to_term(wanted).label() == Some("wf");
        if typed && matches!(by, SuppliedBy::Line(_) | SuppliedBy::SaidOnce(_)) {
            return self.held(facts, wanted, scope);
        }
        // set.mm asks a function's membership in the set of maps where the
        // page writes its type: "there is g : {1, …, n} → ℕ" is a "there
        // is" over ℕ ↑m (1 ... n).
        if let SuppliedBy::Line(at) = by {
            if let Some(member) = self.member_of_maps(at, wanted, scope, facts)? {
                return Ok(Some(member));
            }
        }
        match by {
            SuppliedBy::Line(at) => {
                // What the line says, and what rests on it alone: the domain
                // an obtain on it put in the scope, and the membership of a
                // point or a function it obtains, which rests on the line's
                // sort (`{line}∈`) as a `let` does.
                let held = self.line_supplies(&at.line, scope, facts, &lines)?;
                let sort = format!("{}∈", at.line);
                for (said, proof) in facts.entries() {
                    if rests_on_only(&proof, &at.line) || rests_on_only(&proof, &sort) {
                        self.know_default(&held, said, proof);
                    }
                }
                // The identity elements the record says the line or the
                // hypothesis leaves out, |x| for |x − 0|, are dropped where
                // it places them (`met_at_places`); places it says the line
                // swaps, the ends of a segment between, are turned by the
                // notation's own swap (`met_as`).
                if let (Some(r), Some(met)) = (recorded, meeting) {
                    if !met.flips.is_empty() || !met.identities.is_empty() {
                        if let Some((said, proof)) =
                            self.line_fact(at, scope, facts, &lines)?
                        {
                            if met.identities.is_empty() {
                                return self.met_as(
                                    &said,
                                    proof,
                                    wanted,
                                    met,
                                    Tree::Second,
                                    scope,
                                    facts,
                                );
                            }
                            return self.met_at_places(
                                step, &said, proof, wanted, at, r, scope, facts,
                            );
                        }
                    }
                }
                if let Some(p) = self.placed_proof(at, wanted, &held, scope, facts)? {
                    return Ok(Some(p));
                }
                let narrowed = recorded.is_some_and(|r| r.supplied.narrowed.is_some());
                Ok(self
                    .line_for_all(&at.line, wanted, narrowed, scope, facts)?
                    .and_then(Route::built))
            }
            SuppliedBy::Requires { line, implied } => {
                let owner = match step.requires.is_empty() {
                    true => self.step_now.and_then(|i| self.thm.steps.get(i)),
                    false => Some(step),
                };
                let Some(r) = owner.and_then(|s| s.requires.get(*line)) else {
                    return Ok(None);
                };
                let said = self.claim_of(&r.fact)?;
                let Some(proof) = self.held(facts, &said, scope)? else {
                    return Ok(None);
                };
                if said == *wanted {
                    return Ok(Some(proof));
                }
                if implied.is_none() {
                    return self.carried_to(
                        step, &said, &proof, wanted, meeting, scope, facts,
                    );
                }
                // What the line implies: read off it where the reading
                // gives it, and otherwise worked out from it (`settle`).
                let more = self.implied(&said, &proof, scope, facts)?;
                if let Some(p) = self.held(&more, wanted, scope)? {
                    return Ok(Some(p));
                }
                let held = facts.copy();
                self.know(&held, said, proof);
                Ok(self
                    .settle(&self.to_term(wanted), scope, &held, 3, None, None)?
                    .built())
            }
            SuppliedBy::SaidOnce(_) | SuppliedBy::Walked(_) => Ok(self
                .said_once_proof(&self.to_term(wanted), scope, facts)?
                .built()),
            SuppliedBy::Through { carrier, member } => Ok(self
                .through_proof(carrier, member, wanted, scope, facts)?
                .and_then(Route::built)),
            SuppliedBy::Bound { .. } => self.held(facts, wanted, scope),
            SuppliedBy::Identity(met) => self.identity_proof(wanted, met, scope, facts),
            SuppliedBy::Unstated => Ok(self
                .settle_or_bare(&self.to_term(wanted), scope, facts, None, None)?
                .built()),
            SuppliedBy::Parts(parts) => {
                // A chain is its equations joined, besides itself.
                let asked: Vec<Rpn> = self
                    .parts(wanted)
                    .into_iter()
                    .filter(|p| p != wanted)
                    .collect();
                if asked.len() != parts.len() {
                    return Ok(None);
                }
                let mut joined: Option<(Rpn, Proof)> = None;
                for (part, by) in asked.iter().zip(parts) {
                    let Some(p) =
                        self.supplied_proof(step, by, None, part, scope, facts)?
                    else {
                        return Ok(None);
                    };
                    joined = Some(match joined {
                        None => (part.clone(), p),
                        Some((left, q)) => (
                            t!(left, part, "wa"),
                            pf!(self.b; scope, left, part, q, p, "jca"),
                        ),
                    });
                }
                let Some((made, proof)) = joined else {
                    return Ok(None);
                };
                if made == *wanted {
                    return Ok(Some(proof));
                }
                self.carried_to(step, &made, &proof, wanted, meeting, scope, facts)
            }
        }
    }

    /// ( scope -> wanted ) for an equation whose two sides are one at the
    /// citation's values (`SuppliedBy::Identity`): its left side equal to
    /// itself (`eqidd`), carried to the equation as the record says the
    /// two sides met (`met_as`), `1 · P = P` with the identity element
    /// dropped. None where `wanted` is no equation.
    fn identity_proof(
        &mut self,
        wanted: &Rpn,
        met: &Meeting,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let whole = self.to_term(wanted);
        let (Some("wceq"), [left, _]) = (whole.label(), whole.children()) else {
            return Ok(None);
        };
        let left = self.rpn(left);
        let same = t!(left, left, "wceq");
        let proof = self
            .b
            .ap("eqidd", &binds! {"ph" => scope, "A" => &left}, &[]);
        self.met_as(&same, proof, wanted, met, Tree::First, scope, facts)
    }

    /// ( scope -> wanted ) from `proof` of `said`, the fact the line `at`
    /// writes, through the two trees its meeting is of (`RecordedSupply`):
    /// the line's fact, the second, and the hypothesis at the citation's
    /// values, the first (`carried_at_places`).
    #[allow(clippy::too_many_arguments)]
    fn met_at_places(
        &mut self,
        step: &Step,
        said: &Rpn,
        proof: Proof,
        wanted: &Rpn,
        at: &FirstAt,
        recorded: RecordedSupply,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let Some(met) = recorded.supplied.meeting.as_ref() else {
            return self.same_carried(said, proof, wanted, scope, facts);
        };
        let library = self.item_library();
        let ctx = &library.ctx;
        let asked = filled(&recorded.supplied.want, recorded.values, ctx);
        // A line narrowed to the set asked is met over that set, as the
        // checker met it (`Supplied::narrowed`).
        let written =
            match (&recorded.supplied.narrowed, at.written.children.as_slice()) {
                (Some(n), [letter, _, body]) if at.written.notation() == FOR_ALL => at
                    .written
                    .with_children(vec![letter.clone(), n.to.clone(), body.clone()]),
                _ => at.written.clone(),
            };
        let trees = PlacedTrees {
            said: written,
            wanted: asked,
            said_in: Tree::Second,
        };
        self.carried_at_places(step, said, proof, wanted, &trees, met, scope, facts)
    }

    /// ( scope -> wanted ) from `proof` of `said`, through the two trees
    /// `met` is a meeting of (`PlacedTrees`), each in its standard form and
    /// with the identity elements the record drops from it taken out where
    /// it places them (`Meeting::with_identities_dropped`). `said` is
    /// carried to its tree, its elements are dropped (`tidied`), what is
    /// left meets the other tree's as the rest of the meeting says
    /// (`met_as`), that tree's elements are put back (`tidied`), and that
    /// is carried to `wanted`. None where a step does not carry.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::elab) fn carried_at_places(
        &mut self,
        step: &Step,
        said: &Rpn,
        proof: Proof,
        wanted: &Rpn,
        trees: &PlacedTrees,
        met: &Meeting,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let library = self.item_library();
        let ctx = &library.ctx;
        let wanted_in = match trees.said_in {
            Tree::First => Tree::Second,
            Tree::Second => Tree::First,
        };
        // Each define the record reads out is put as what it reads as, at
        // its place (`Meeting::with_unfolded`), before the identities go.
        let (Some(said_tree), Some(wanted_tree)) = (
            met.with_unfolded(&standard(&trees.said, ctx), trees.said_in),
            met.with_unfolded(&standard(&trees.wanted, ctx), wanted_in),
        ) else {
            return Err(self.unreached(
                step.line,
                "the checker placed a define read out where one of the two it met has none",
            ));
        };
        let (Some(said_bare), Some(wanted_bare)) = (
            met.with_identities_dropped(&said_tree, trees.said_in),
            met.with_identities_dropped(&wanted_tree, wanted_in),
        ) else {
            return Err(self.unreached(
                step.line,
                "the checker placed an identity element where one of the two it met has none",
            ));
        };
        let said_tree = self.term(&said_tree)?;
        let said_bare = self.term(&said_bare)?;
        let wanted_bare = self.term(&wanted_bare)?;
        let wanted_tree = self.term(&wanted_tree)?;
        let Some(p) = self.same_carried(said, proof, &said_tree, scope, facts)? else {
            return Ok(None);
        };
        let Some(p) = self.tidied(&p, &said_tree, &said_bare, scope, facts)? else {
            return Ok(None);
        };
        let rest = Meeting {
            identities: Vec::new(),
            ..met.clone()
        };
        let Some(p) = self.met_as(
            &said_bare,
            p,
            &wanted_bare,
            &rest,
            trees.said_in,
            scope,
            facts,
        )?
        else {
            return Ok(None);
        };
        let Some(p) = self.tidied(&p, &wanted_bare, &wanted_tree, scope, facts)? else {
            return Ok(None);
        };
        self.same_carried(&wanted_tree, p, wanted, scope, facts)
    }

    /// ( scope -> wanted ) from `proof` of `said`, the fact a line writes,
    /// where the two are one fact spelt otherwise (`same`) or with an
    /// identity element dropped (`tidied`); where the record says the two
    /// met with their members in another order (`Meeting::permuted`), a
    /// triangle's points, worked out from it (`settle`).
    #[allow(clippy::too_many_arguments)]
    fn carried_to(
        &mut self,
        step: &Step,
        said: &Rpn,
        proof: &Proof,
        wanted: &Rpn,
        meeting: Option<&Meeting>,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        // The hypothesis is at the checker's values, which read out a
        // define the step cites where the line names it, `g : S → T` for
        // S's set: each place the two differ is one spelling of a term, or
        // one an equation the step cites makes equal (`Row::Held`).
        let supplied = self.supplied(Some(step), scope, facts)?;
        let held = self.with_cited(Some(step), scope, &supplied, None)?;
        if let Built(alike) = self.congruence(
            &self.to_term(said),
            &self.to_term(wanted),
            scope,
            &held,
            None,
            &Leaf::Rows(vec![Row::Standard, Row::Held]),
        )? {
            return Ok(Some(
                pf!(self.b; scope, said, wanted, proof, alike, "mpbid"),
            ));
        }
        if !meeting.is_some_and(|m| m.permuted) {
            return self.tidied(proof, said, wanted, scope, facts);
        }
        let held = facts.copy();
        self.know(&held, said.clone(), proof.clone());
        Ok(self
            .settle(&self.to_term(wanted), scope, &held, 3, None, None)?
            .built())
    }

    /// What the line `at` names says there, as the checker read it
    /// (`FirstAt::written`): the sentence, the part of one, or a "for all"
    /// of it read at a block's letter.
    pub(in crate::elab) fn recorded_statement(&mut self, at: &FirstAt) -> Checked<Rpn> {
        self.term(&at.written)
    }

    /// Each hypothesis of the step's citation of `item`, in set.mm at the
    /// citation's values, with the proof of the fact the checker recorded
    /// as supplying it (`Cited::supplied`, `supplied_proof`), carried to the
    /// hypothesis the way the record says the two met (`Supplied::meeting`).
    /// Only a fact a line or a requires line writes is among them, and not
    /// one what the record names does not give.
    pub(in crate::elab) fn recorded_hypotheses(
        &mut self,
        step: &Step,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Facts> {
        let given = Facts::new();
        let Some(cited) = self.citation_read(step).cloned() else {
            return Ok(given);
        };
        // The values the checker read each hypothesis at, the citation's
        // own pairs among them (`citations::with_seed`).
        let binding = cited.binding_with_written();
        let library = self.item_library();
        // A function's type, and a finite group's `let`, are held among
        // the step's facts, as each step types its functions, and the
        // group the binding is read from leaves out the letters only they
        // name.
        let typed: Vec<HypothesisAt> = library
            .function_type_lines(&cited.item)
            .into_iter()
            .chain(library.group_assertion_lines(&cited.item))
            .map(|w| w.at)
            .collect();
        // The step's requires lines, each proved with the ones above it
        // (`supplied`), which a hypothesis the record places in one is
        // carried from.
        let facts = &facts.with(&self.supplied(Some(step), scope, facts)?);
        for supplied in &cited.supplied {
            let node = filled(&supplied.want, &binding, &library.ctx);
            // A function's type, or a finite group's, is the one the step
            // holds, as each step types its functions; it is given as it is
            // held, and not carried from a line. One naming a letter the
            // binding leaves out, the W of `f : X → W`, or binds to a rule,
            // which stands for no term alone, says nothing at the values
            // (`citing::asked`).
            if supplied.at.is_some_and(|at| typed.contains(&at)) {
                let unfixed = supplied.want.names().iter().any(|n| {
                    let fixed = binding
                        .get(n.as_str())
                        .is_some_and(|v| v.notation() != PROPERTY_OF);
                    !fixed && !library.env.g.functions.contains_key(n)
                });
                if unfixed {
                    continue;
                }
                let wanted = self.term(&node)?;
                if let Some(proof) = self.held(facts, &wanted, scope)? {
                    self.know(&given, wanted, proof);
                }
                continue;
            }
            // A fact said once, walked to or unstated is settled where the
            // lemma asks it, and only a fact a line writes is carried here.
            if !matches!(
                supplied.by,
                SuppliedBy::Line(_) | SuppliedBy::Requires { implied: None, .. }
            ) {
                continue;
            }
            // Read as the reading the lemma is applied at is (`read_apart`),
            // so that a value's bound letter is spelt alike in both.
            let wanted = self.read_apart(step, &node)?;
            let wanted = self.rpn(&wanted);
            let recorded = RecordedSupply {
                supplied,
                values: &binding,
            };
            let carried = self.supplied_proof(
                step,
                &supplied.by,
                Some(recorded),
                &wanted,
                scope,
                facts,
            )?;
            if let Some(proof) = carried {
                self.know(&given, wanted, proof);
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
        self.said_on_line(&recorded, &says)
    }

    /// What the line says that is `recorded`, as written or over other
    /// bound letters, with its proof; None where it says no such thing.
    fn said_on_line(
        &mut self,
        recorded: &Rpn,
        says: &Facts,
    ) -> Checked<Option<(Rpn, Proof)>> {
        for (said, held) in says.entries() {
            let same = said == *recorded
                || self
                    .renaming(&self.to_term(recorded), &self.to_term(&said))?
                    .is_some();
            if same {
                return Ok(Some((said, held)));
            }
        }
        Ok(None)
    }

    /// `recorded`, an "and" of what the line says, each part found on the
    /// line (`said_on_line`) and the two sides of each "and" joined by
    /// `jca`; None where a part is not on it.
    fn joined_on_line(
        &mut self,
        recorded: &Rpn,
        says: &Facts,
        scope: &Rpn,
    ) -> Checked<Option<(Rpn, Proof)>> {
        if let Some(found) = self.said_on_line(recorded, says)? {
            return Ok(Some(found));
        }
        let whole = self.to_term(recorded);
        let (Some("wa"), [left, right]) = (whole.label(), whole.children()) else {
            return Ok(None);
        };
        let (left, right) = (self.rpn(left), self.rpn(right));
        let Some((l, lp)) = self.joined_on_line(&left, says, scope)? else {
            return Ok(None);
        };
        let Some((r, rp)) = self.joined_on_line(&right, says, scope)? else {
            return Ok(None);
        };
        Ok(Some((
            t!(l, r, "wa"),
            pf!(self.b; scope, l, r, lp, rp, "jca"),
        )))
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
        // The line's sentences together, which a line held sentence by
        // sentence, an obtain's, does not hold joined: each part as the
        // line gives it, its letter's membership among them, joined as the
        // record's statement joins them (`joined_on_line`).
        if at.sentence.is_none() {
            let recorded = self.recorded_statement(at)?;
            if let Some((said, proof)) = self.joined_on_line(&recorded, held, scope)? {
                if said == *term {
                    return Ok(Some(proof));
                }
            }
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
    pub fn one_unfolded(
        &mut self,
        lemma: &str,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
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
        let chosen = take!(self.unfolded_from(
            step,
            &reads.children()[0],
            &variables,
            scope,
            &named
        )?);
        let (mut binding, given) = chosen;
        // What the left side fixes need not be everything the right side
        // holds: what the lemma's own hypotheses say fixes more
        // (`substituted_slot`), and a variable still open is what the item's
        // sentence the checker read the claim from says there
        // (`concluded_reading`), put in the lemma's spelling as the record
        // says it differs (`lemma_spelt`) and fitted as written and then as
        // the standard form reads the two (`fits_as`): the page's ε > 0 is
        // set.mm's ε ∈ ℝ⁺.
        for essential in &sig.essentials {
            let asked = self.essential(essential);
            if let Some(more) = self.substituted_slot(&asked, &binding) {
                binding.extend(more);
            }
        }
        let right_side = &reads.children()[1];
        // A letter the lemma binds needs no fitting: one left open is moved
        // apart from what the values spell below. Where a class or formula
        // is open too, the two are fitted together, a body its letter is
        // free in.
        let binds = self.letters_bound(right_side);
        let open = names_of(right_side)
            .iter()
            .any(|v| !binding.contains_key(v) && !binds.contains(v));
        if open {
            let Some(cited) = self.citation_read(step).cloned() else {
                return Err(self.unreached(
                    step.line,
                    "the checker recorded no reading of this citation",
                ));
            };
            let spelt = self.lemma_reading(&cited);
            let read = self.concluded_reading(step, &cited, spelt)?;
            match self.fits_as(right_side, &read, &variables, Some(&binding)) {
                Some(fitted) => binding = fitted,
                None => {
                    return Err(self.unreached(
                        step.line,
                        format!(
                            "{lemma}'s right side is not {}, which the record says it states",
                            self.render(&self.rpn(&read))
                        ),
                    ))
                }
            }
        }
        // The claim of the membership half leaves the property half
        // standing as the lemma's own name, and `elrab`'s hypothesis is what
        // says what that half is; where the record says the claim is one
        // part of what the property gives (`Cited::within`), it is that
        // whole property (`property_whole`).
        let within = self
            .citation_read(step)
            .is_some_and(|c| c.within.iter().any(Option::is_some));
        for essential in &sig.essentials {
            let asked = self.essential(essential);
            let more = match within {
                true => self.property_whole(&asked, &binding),
                false => self.substituted_slot(&asked, &binding),
            };
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
            // Apart from the lemma's own letters too, so that no two of its
            // binders come to bind one letter.
            let mut seen: Vec<&Term> = values.iter().collect();
            seen.push(&reads);
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
        self.unfolded_to_claim(step, &right, proof, term, scope, &facts)
    }

    /// ( scope -> term ) from a proof of `right`, the right side a
    /// definition unfolds to, as the checker recorded the citation reads it
    /// (`claim_from_readings`): each part of the claim the right side, or
    /// the part of it the record names, carried as the record says the two
    /// meet. An obtain records no conclusion, and takes the right side's
    /// "there is" whole, over the letters the step obtains: the right side
    /// where it is one, or its one part that is.
    fn unfolded_to_claim(
        &mut self,
        step: &Step,
        right: &Rpn,
        proof: Proof,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        if right == term {
            return Ok(Built(proof));
        }
        let Some(cited) = self.citation_read(step).cloned() else {
            return Err(self.unreached(
                step.line,
                "the checker recorded no reading of this citation",
            ));
        };
        if !cited.concluded.is_empty() {
            let readings = vec![(right.clone(), proof); cited.concluded.len()];
            return self
                .claim_from_readings(step, term, &cited, readings, scope, facts)
                .map(Built);
        }
        let parts = self.conjuncts_proved(right, proof, scope);
        let there_is: Vec<(Rpn, Proof)> = parts
            .into_iter()
            .filter(|(p, _)| self.to_term(p).label() == Some("wrex"))
            .collect();
        let [(there, shown)] = there_is.as_slice() else {
            return Err(self.unreached(
                step.line,
                format!(
                    "the definition's right side {} has no one \"there is\" to obtain from",
                    self.render(right)
                ),
            ));
        };
        let renamed = Meeting {
            renamed: true,
            ..Meeting::default()
        };
        match self.met_as(
            there,
            shown.clone(),
            term,
            &renamed,
            Tree::First,
            scope,
            facts,
        )? {
            Some(p) => Ok(Built(p)),
            None => Err(self.unreached(
                step.line,
                format!(
                    "the \"there is\" the checker obtains from says {}, and the step obtains {}",
                    self.render(there),
                    self.render(term)
                ),
            )),
        }
    }
}
