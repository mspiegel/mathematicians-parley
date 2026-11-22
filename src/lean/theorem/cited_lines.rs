//! Proof methods: lines cited and met with a claim.

use std::collections::{BTreeMap, BTreeSet};

use super::super::doc::forms::Meets;
use super::super::doc::CountForm::{Extended, Natural};
use super::super::doc::{
    forms, BoundForm, CountForm, LeanType, PrefixMark, Quant, Source, TermKind,
};
use super::super::templates::Num;
use super::super::{doc, tactics as t};
use super::*;
use crate::checker::record::{
    AppliedDomain, BodyPart, ChainTerms, DomainSaid, Instantiated, ObtainedPart,
    Restated,
};
use crate::citing::{claimed_member, Implication};
use crate::formula::node::Sort;
use crate::formula::page;
use crate::matching::{Binding, Meeting};
use crate::notations::{EQUALS, FOR_ALL, INTEGER_RANGE};
use crate::rules::RANGE_BOUNDS;
use crate::{matching, rules};

impl<'a> Proof<'a> {
    /// A claim "for all j ∈ S" proved by a header function's equation at
    /// the member, `intro j h_j; simp only [hD1 j h]`, worked out after as
    /// the checker met the sides (`define_links`). `h` puts the member in
    /// the function's domain as the record says (`define_domains`): a line,
    /// or the member's own fact, which is the domain's fact itself where S
    /// is the domain, and the range's lower bound where S is a range inside
    /// it, `1 ≤ j` being `0 < j` in ℤ.
    pub(super) fn for_all_by_header(
        &self,
        hyp: &str,
        node: &Node,
        line: usize,
    ) -> Route<super::super::doc::Proof> {
        let (Some(said), Some(met)) = (
            self.rec
                .define_domains
                .get(&line)
                .and_then(|applied| applied.first())
                .map(|first| &first.said),
            self.rec.define_links.get(&line),
        ) else {
            return Route::no("a claim \"for all\" with no domain or meeting recorded");
        };
        let Some((member, _)) = claimed_member(node, self.writer.grammar) else {
            return Route::no("a claim \"for all\" over no set");
        };
        let (intros, body, writer) = self.peel(node);
        let ([letter, h], false) = (intros.as_slice(), body.notation() == FOR_ALL)
        else {
            return Route::no("a claim \"for all\" of more than one letter");
        };
        // The member's own fact as the domain's: the domain's fact itself
        // where the set is the domain, the range's lower bound where it is a
        // range inside it.
        let member_fact = match member.children[1].notation() {
            INTEGER_RANGE => {
                let says = match writer.formula(&member) {
                    Route::Built(s) => s,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match range_bounds(&says, &t::hyp(h)).into_iter().next() {
                    Some((proof, _)) => proof,
                    None => return Route::no("a range member Lean writes otherwise"),
                }
            }
            _ => t::hyp(h),
        };
        let domain = match self.domain_proof(said, Some(member_fact)) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let equation = hyp_applied(hyp, vec![t::hyp(letter), domain]);
        let alone = met.as_ref().is_some_and(unfolds_alone);
        Route::Built(super::super::doc::Proof::By(Tactic::Seq(vec![
            Tactic::Intro(intros.clone()),
            simp_unfolded(vec![t::forwards(equation)], alone, false),
        ])))
    }

    /// The proof of a claim the checker found a line states
    /// (`CheckedTheorem::restated`): the line, its sentence or part, read at
    /// a block's letter where the line says it for all, or what it implies
    /// (`line_says`), met with the claim as Lean states it (`proof_meeting`).
    /// None where the record has no place, or Lean states the two apart.
    pub(super) fn restated_proof(
        &self,
        line: usize,
        node: &Node,
    ) -> Option<super::super::doc::Proof> {
        // A line that states it, alone or under the claim's "for all"; Lean
        // proves a narrowed "for all" or what lines give together its own
        // way.
        let (at, meeting) = match self.rec.restated.get(&line)? {
            Restated::Stated { at, meeting }
            | Restated::UnderClaim { at, meeting, .. } => (at, meeting.as_ref()),
            Restated::Narrowed { .. } | Restated::Lines(_) => return None,
        };
        let (proof, says) = self.line_says(at).built()?;
        // A limit of a function the header lets, S(n) → K, restated with the
        // function's rule, at a sequence's index (`DomainSaid::LimitIndex`):
        // the line's sequence is the claim's from where the domain starts.
        if let Some(limit) = self.limit_restated(line, &proof) {
            return Some(limit);
        }
        let claim = self.claim_as_stated(line, node)?;
        if !super::super::doc::forms::relation_types_agree(&says, &claim) {
            return None;
        }
        // The line met otherwise than as written, as the record says:
        // turned, identities dropped (`Restated::Stated`, `met_proof`).
        let proved = match meeting {
            Some(met) => self.met_proof(proof, &says, &claim, met),
            None => self.proof_meeting(proof, &says, &claim),
        };
        proved.map(|p| super::super::doc::Proof::By(p.closer()))
    }

    /// A limit restated with a function the header lets written out at the
    /// sequence's index (`applied_domains`, `DomainSaid::LimitIndex`):
    /// `proof`, the line's limit, taken to the claim's by `congr'`, the two
    /// sequences one from n = 1 on, where the index is in the domain, by the
    /// function's equation there: `hH3.congr' (Filter.eventually_atTop.mpr
    /// ⟨1, by intro n hn; rw [hD2 n (by omega)]⟩)`. None where the step
    /// applies no such function at one index.
    fn limit_restated(
        &self,
        line: usize,
        proof: &Printed,
    ) -> Option<super::super::doc::Proof> {
        let at: Vec<&AppliedDomain> = self
            .rec
            .applied_domains
            .get(&line)?
            .iter()
            .filter(|a| matches!(a.said, DomainSaid::LimitIndex))
            .collect();
        let [applied] = at.as_slice() else {
            return None;
        };
        let hyp = self.header_function_named(&applied.label)?;
        let guarded = matches!(
            self.header_equations.get(&hyp).map(|s| &bare_term(s).kind),
            Some(TermKind::Quantified { guard: Some(_), .. })
        );
        let n = super::super::names::letter(&applied.arg.text);
        let mut args = vec![t::hyp(&n)];
        if guarded {
            args.push(t::by_term(doc::Proof::By(t::call("omega", vec![]))));
        }
        let equation = super::terms::hyp_applied(&hyp, args);
        let agree = t::by_term(doc::Proof::By(Tactic::Seq(vec![
            Tactic::Intro(vec![n.clone(), "hn".to_string()]),
            t::call("rw", vec![TacticArg::Rules(vec![t::forwards(equation)])]),
        ])));
        let eventually = Printed::applied(
            "Filter.eventually_atTop.mpr",
            Source::Mathlib,
            vec![super::super::expr::anonymous(vec![
                Printed::numeral("1", LeanType::Num(super::super::templates::Num::Int)),
                agree,
            ])],
            LeanType::Prop,
        );
        let congr = Printed {
            kind: TermKind::App {
                head: Box::new(Printed {
                    kind: TermKind::Field {
                        inner: Box::new(t::bracket(proof.clone())),
                        field: "congr'".to_string(),
                    },
                    ty: None,
                }),
                args: vec![super::super::doc::Arg::Explicit(eventually)],
                explicit: false,
            },
            ty: Some(LeanType::Prop),
        };
        Some(doc::Proof::By(Tactic::Exact(congr)))
    }

    /// The proof of `wrapped`, a requires fact under the claim's "for all",
    /// from the part of a line's own "for all" body the record found it to
    /// be (`restated_under_claim`): the line at each member, that part taken,
    /// `intro x; exact (s4 x).1`.
    pub(super) fn body_part_proof(
        &self,
        line: usize,
        wrapped: &Node,
        part: BodyPart,
    ) -> Route<super::super::doc::Proof> {
        let Some(Restated::UnderClaim { at, .. }) = self.rec.restated.get(&line) else {
            return Route::no("a requires line under the claim no line was found for");
        };
        let found = match self.line_part(at) {
            Route::Built(f) => f,
            Route::Declined(d) => return Route::Declined(d),
        };
        let (intros, _, _) = self.peel(wrapped);
        let applied = Printed {
            kind: super::super::doc::TermKind::App {
                head: Box::new(found.proof),
                args: intros
                    .iter()
                    .map(|i| {
                        super::super::doc::Arg::Explicit(super::super::tactics::hyp(i))
                    })
                    .collect(),
                explicit: false,
            },
            ty: None,
        };
        let taken = fields(
            super::super::tactics::bracket(applied),
            &projection_path(part.part, part.of),
        );
        Route::Built(after_intros(
            &intros,
            super::super::doc::Proof::By(Tactic::Exact(taken)),
        ))
    }

    /// The proof that a define's argument is in its domain, as the record
    /// says (`define_domains`): the line's sentence or part that says it, or,
    /// of a claim said of every member, the member's own fact, `member`,
    /// where the claim's step has one. Declined of a fact a line implies
    /// without writing it.
    pub(super) fn domain_proof(
        &self,
        said: &DomainSaid,
        member: Option<Printed>,
    ) -> Route<Printed> {
        match (said, member) {
            (DomainSaid::Line(at), _) if at.implied.is_none() => {
                self.line_part(at).map(|found| found.proof)
            }
            (DomainSaid::Line(_), _) => Route::no("a domain a line implies"),
            (
                DomainSaid::Member | DomainSaid::SumRange | DomainSaid::LimitIndex,
                Some(fact),
            ) => Route::Built(fact),
            (DomainSaid::LimitIndex, None) => {
                Route::no("a domain a sequence's index gives, outside its limit")
            }
            (DomainSaid::Member, None) => {
                Route::no("a domain the claim's member says, of a claim not peeled")
            }
            (DomainSaid::SumRange, None) => {
                Route::no("a domain a sum's range gives, outside the sum")
            }
        }
    }

    /// The sentence or part of a line `at` names, as the page writes it, with
    /// the term that proves it; of an implied fact, what implies it.
    pub(super) fn line_part(
        &self,
        at: &FirstAt,
    ) -> Route<super::super::algebra::Cited> {
        let line = &at.line;
        let Some(sentences) = self.trees.get(line) else {
            return Route::no(format!("line {line}, which no name in Lean holds"));
        };
        let own = self.written_sentences(line);
        let found = match (at.sentence, sentences.as_slice()) {
            (None, [one]) => Some(one.cited()),
            // The sentences together, which Lean names apart: `⟨s2_4a,
            // s2_4b⟩`, saying the "and" of what each says.
            (None, many) => {
                let parts: Vec<super::super::algebra::Cited> =
                    many.iter().map(LineSentence::cited).collect();
                let mut says = Vec::new();
                for part in &parts {
                    match self.line_statement(part) {
                        Route::Built(s) => says.push(s),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                let Some(node) = page::conjoined(
                    self.writer.grammar,
                    parts.iter().map(|p| p.node.clone()).collect(),
                ) else {
                    return Route::no(format!(
                        "the sentences of line {line}, which join by no \"and\""
                    ));
                };
                let said = says.into_iter().rev().reduce(|right, left| Printed {
                    kind: super::super::doc::TermKind::Infix {
                        op: super::super::doc::Op::AND,
                        lhs: Box::new(left),
                        rhs: Box::new(right),
                    },
                    ty: Some(super::super::doc::LeanType::Prop),
                });
                Some(super::super::algebra::Cited {
                    node,
                    proof: super::super::expr::anonymous(
                        parts.into_iter().map(|p| p.proof).collect(),
                    ),
                    says: said,
                })
            }
            (Some(k), _) if k < own => sentences
                .iter()
                .find(|s| s.at == k)
                .map(LineSentence::cited),
            (Some(k), _) => {
                let letters: BTreeSet<String> =
                    at.written.names().into_iter().collect();
                sentences
                    .iter()
                    .filter_map(|s| self.at_recorded_letter(&s.cited(), &letters))
                    .nth(k - own)
            }
        };
        let Some(found) = found else {
            return Route::no(format!(
                "sentence {:?} of line {line}, which Lean has no line for",
                at.sentence
            ));
        };
        // The equation between two terms of the chain the sentence is
        // (`FirstAt::pair`): the links between them joined, `Eq.trans`.
        if let Some(pair) = at.pair {
            return self.chain_pair(&found, pair, &at.written);
        }
        // A part of a chain is its link from that term to the next, `|MA| =
        // |MC|` of `|MA| = |MC| = |MB|`.
        if let Some(j) = at.part {
            if page::chain_links(self.writer.grammar, &found.node).is_some() {
                let link = ChainTerms { from: j, to: j + 1 };
                return self.chain_pair(&found, link, &at.written);
            }
        }
        match at.part {
            None => Route::Built(found),
            // The part as the page writes it (`FirstAt::written`), found in
            // the line's "and"s with Lean's statement taken apart alike: a
            // phrase the tree holds written out is the one part the checker
            // counts it as, `d is a common divisor of a and b` of H4.
            Some(j) => match part_written(
                &found.node,
                found.proof,
                found.says,
                &at.written,
                &self.writer,
                self.sources.ctx,
            ) {
                Some(part) => Route::Built(part),
                None => Route::no(format!(
                    "part {j} of what line {line} says, which Lean does not join by \"and\""
                )),
            },
        }
    }

    /// The equation between the terms at `pair` of the chain `chain` says,
    /// `written` as the page writes it, x = w of x = y = z = w: the links
    /// between the two, each the projection the writer joins it as (`a = b
    /// ∧ b = c`, the first by `.1`, the last by `.2`), joined by `Eq.trans`.
    pub(super) fn chain_pair(
        &self,
        chain: &super::super::algebra::Cited,
        pair: ChainTerms,
        written: &Node,
    ) -> Route<super::super::algebra::Cited> {
        let Some(links) = page::chain_links(self.writer.grammar, &chain.node) else {
            return Route::no("a pair of a chain from a sentence that is no chain");
        };
        if pair.from >= pair.to || pair.to > links.len() {
            return Route::no("a pair of a chain's terms the chain does not have");
        }
        let last = links.len() - 1;
        let link = |k: usize| {
            let mut path = vec!["2"; k];
            if k < last {
                path.push("1");
            }
            super::headers::fields(chain.proof.clone(), &path)
        };
        let mut proof = link(pair.from);
        for k in pair.from + 1..pair.to {
            proof = Printed::applied(
                "Eq.trans",
                super::super::doc::Source::Core,
                vec![super::super::tactics::bracket(proof), link(k)],
                super::super::doc::LeanType::Prop,
            );
        }
        let says = match self.writer.formula(written) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        Route::Built(super::super::algebra::Cited {
            node: written.clone(),
            proof,
            says: Some(says),
        })
    }

    /// Whether Lean writes the membership `node` as a bound, `0 < x` or
    /// `0 ≤ x`.
    pub(super) fn written_as_bound(&self, node: &Node) -> bool {
        written_as_bound(node, &self.writer)
    }
}

/// Whether `writer` writes the membership `node` as a bound, `0 < x` or `0
/// ≤ x`.
pub(super) fn written_as_bound(node: &Node, writer: &Writer) -> bool {
    match writer.formula(node) {
        Route::Built(says) => matches!(
            &says.kind,
            super::super::doc::TermKind::Infix { op, .. } if op.symbol == "<" || op.symbol == "≤"
        ),
        Route::Declined(_) => false,
    }
}

impl<'a> Proof<'a> {
    /// The proof of what `found`, a sentence or part of a line, implies by
    /// `rule` (`FirstAt::implied`), from how Lean writes `found`: a range
    /// membership is `x ∈ Finset.Icc a b`, whose bounds `Finset.mem_Icc`
    /// gives; a membership of ℕ or ℕ₀ is the bound `0 < x` or `0 ≤ x`
    /// itself, which is also `x ≥ 1` in ℤ. `target` is what it implies as
    /// Lean writes it.
    pub(super) fn implied_proof(
        &self,
        found: &super::super::algebra::Cited,
        rule: Implication,
        target: &Printed,
    ) -> Route<Printed> {
        match rule {
            // A membership of a wider number system: of one Lean's type
            // already holds, `True`; of ℕ₀ from ℕ, `le_of_lt` of the bound
            // `0 < x`, which Lean writes `0 ≤ x`.
            Implication::WiderSystem if target.is_truth() => Route::Built(Printed::constant(
                "True.intro",
                super::super::doc::Source::Core,
                super::super::doc::LeanType::Prop,
            )),
            Implication::WiderSystem => {
                let at_most = matches!(
                    &target.kind,
                    super::super::doc::TermKind::Infix { op, .. } if op.symbol == "≤"
                );
                let positive = matches!(
                    membership_of_whole(&found.node),
                    Some((_, rules::System::N))
                );
                match (at_most, positive && self.written_as_bound(&found.node)) {
                    (true, true) => Route::Built(nonneg_of(
                        rules::System::N,
                        found.proof.clone(),
                    )),
                    _ => Route::no(format!(
                        "a membership of a wider system, {}, which Lean writes otherwise",
                        target.text()
                    )),
                }
            }
            Implication::RangeBound { lemma } => {
                let says = match self.line_statement(found) {
                    Route::Built(s) => s,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let side = RANGE_BOUNDS
                    .iter()
                    .position(|(_, l)| *l == lemma);
                match side.and_then(|k| range_bounds(&says, &found.proof).into_iter().nth(k)) {
                    Some((proof, _)) => Route::Built(proof),
                    None => Route::no(format!(
                        "the bound {lemma} of {}, which Lean does not write as a range",
                        says.text()
                    )),
                }
            }
            // Lean writes a letter's membership as its bound, and a term's
            // as a whole number equal to it, `∃ m₀, 0 < m₀ ∧ ↑m₀ = 3 ^ m`.
            // A term's membership Lean writes as a whole number equal to it,
            // `∃ m₀ : ℤ, 0 < m₀ ∧ (m₀ : ℚ) = 3 ^ m`: the number taken out,
            // put in for the term, and the bound taken from the number's own,
            // `by obtain ⟨w, hw, ew⟩ := s6; rw [← ew]; exact_mod_cast hw`
            // (in ℤ, `0 < w` is `0 + 1 ≤ w`, so it gives `1 ≤ w` too).
            Implication::SystemFact { lemma } if !self.written_as_bound(&found.node) => {
                let whole = match self.line_statement(found) {
                    Route::Built(s) => matches!(
                        s.kind,
                        super::super::doc::TermKind::Quantified {
                            quant: super::super::doc::Quant::Exists,
                            ..
                        }
                    ),
                    Route::Declined(d) => return Route::Declined(d),
                };
                let field = match (whole, system_fact_field(lemma)) {
                    (true, Some(field)) => field,
                    _ => {
                        return Route::no(format!(
                            "what {lemma} gives of a membership Lean writes as a whole number"
                        ))
                    }
                };
                let steps = vec![
                    Tactic::Obtain {
                        names: vec!["w".to_string(), "hw".to_string(), "ew".to_string()],
                        says: None,
                        from: found.proof.clone(),
                    },
                    t::call("rw", vec![TacticArg::Rules(vec![t::backwards(t::hyp("ew"))])]),
                    // The bound, or what the lemma's field takes from it,
                    // `hw.ne'` of nnne0.
                    t::exact_mod_cast(match field {
                        None => t::hyp("hw"),
                        Some(f) => fields(t::hyp("hw"), &[f]),
                    }),
                ];
                Route::Built(t::bracket(shown(
                    target.clone(),
                    super::super::doc::Proof::By(Tactic::Seq(steps)),
                )))
            }
            Implication::SystemFact { lemma } => match system_fact_field(lemma) {
                Some(None) => Route::Built(found.proof.clone()),
                Some(Some(field)) => Route::Built(fields(found.proof.clone(), &[field])),
                None => Route::no(format!(
                    "what {lemma} gives of a membership, which Lean's bound does not"
                )),
            },
            // `X ∈ 𝒫S` is `X ∈ Set.powerset S`, which is `X ⊆ S` by
            // definition: the line's proof is a proof of either.
            Implication::OtherForm {
                lemma: "gsspw" | "elpwi",
            } => Route::Built(found.proof.clone()),
            // `P is on line AB` is `P ∈ line AB` as Lean writes the notation,
            // and `∉` is `¬ ∈`: either form's proof is the other's
            // (`rules::ON_LINE`).
            Implication::OtherForm {
                lemma: "glineel" | "glineon" | "glinenel" | "glinenon",
            } => Route::Built(found.proof.clone()),
            // A sentence about a function, which Lean writes with the
            // function's type first, `Set.MapsTo f A B ∧ Set.InjOn f A`
            // (`sets::map_claim_parts`): that first part.
            Implication::FunctionType { .. } => {
                let says = match self.line_statement(found) {
                    Route::Built(s) => s,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match &unparenthesized(&says).kind {
                    super::super::doc::TermKind::Infix { op, lhs, .. }
                        if op.symbol == "∧" && is_maps_to(lhs) =>
                    {
                        Route::Built(fields(found.proof.clone(), &["1"]))
                    }
                    _ => Route::no(format!(
                        "a function's type Lean does not write first in {}",
                        says.text()
                    )),
                }
            }
            // The three differences a triangle opens with, `P ≠ Q`, `Q ≠ R`
            // and `P ≠ R` of `P, Q, R form a triangle`: the first three parts
            // of Lean's `Triangle`, by the two vertices the checker recorded.
            Implication::TriangleApart { first, second } => {
                let path: &[&str] = match (first, second) {
                    (0, 1) => &["1"],
                    (1, 2) => &["2", "1"],
                    (0, 2) => &["2", "2", "1"],
                    _ => return Route::no("a triangle's difference in another order"),
                };
                Route::Built(fields(found.proof.clone(), path))
            }
            other => Route::no(format!(
                "a fact a line implies by {other:?}, which the Lean build does not prove yet"
            )),
        }
    }

    /// Whether the two sides of an equation, as Lean writes them, are left
    /// apart in casts once the defines' equations are put in, which
    /// `push_cast` then moves in. `simp only [hD]` puts each `set` letter's
    /// value where the letter stood, and closes a goal that is then `x = x`
    /// itself: where the two sides are alike with each such letter read as
    /// its value (`forms::alike_once_set`), nothing is left. Where Lean
    /// casts such a letter to a type its value is not in, `(S 1 : ℚ)` of an
    /// S in ℤ, the cast stands around the value once it is put in, to be
    /// pushed into it. A define no `set` names, a header's function, is put
    /// in by its own equation, `(f a : ℝ) = …`, which states the claim's
    /// side as the claim casts it, and leaves no cast.
    pub(super) fn unfolds_to_casts(&self, one: &Printed, other: &Printed) -> bool {
        let values = self.set_values();
        !forms::alike_once_set(one, other, &values)
            && (forms::casts_set_letter(one, &values)
                || forms::casts_set_letter(other, &values))
    }

    /// How many sentences the line `line` writes, by the reference that
    /// cites it: a step's claim, a hypothesis, a block's opening line; one
    /// for any other line the writer names, a define or a requires line.
    pub(super) fn written_sentences(&self, line: &str) -> usize {
        let thm = self.thm;
        let count = |w: Written| w.sentences().len();
        if let Some(step) = thm
            .steps
            .iter()
            .find(|s| s.number.number().is_some_and(|n| n.to_string() == line))
        {
            return step.claim.sentences().len();
        }
        for (i, h) in thm.hypotheses.iter().enumerate() {
            let label = h.label.clone().unwrap_or_else(|| format!("H{}", i + 1));
            if label == line {
                return count(h.body(&thm.path));
            }
        }
        for o in thm.steps.iter().flat_map(|s| &s.openers) {
            if o.label == line {
                return count(o.body(&thm.path));
            }
        }
        1
    }

    /// How `proof`, a line that says `says`, proves `wanted` as Lean has it
    /// (`forms::meets`): as it is, turned round, or by a tactic that moves
    /// the one to the other; None where the two differ in more.
    pub(super) fn proof_meeting(
        &self,
        proof: Printed,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<Proved> {
        let meets = forms::meets(says, wanted, &self.set_values())?;
        // A count is taken from ℕ to ℕ∞ or ℤ only as `forms_converted`
        // takes it: a line counting one way meets one counting another not
        // by its casts. The other meetings compare the two read alike, so
        // their counts are in one form.
        let counts = |t: &Printed| t.has_count(Natural) || t.has_count(Extended);
        if (counts(says) || counts(wanted)) && matches!(meets, Meets::Casts { .. }) {
            return None;
        }
        Some(match meets {
            Meets::Same | Meets::Unfolded => Proved::Term(proof),
            Meets::Turned { negated: false } => {
                Proved::Term(super::super::tactics::symm(proof))
            }
            Meets::Turned { negated: true } => Proved::Term(Printed::applied(
                "Ne.symm",
                super::super::doc::Source::Core,
                vec![proof],
                super::super::doc::LeanType::Prop,
            )),
            Meets::Identities(rules) => Proved::Simplified { rules, line: proof },
            // A range Lean writes as a finite set beside one written as a
            // set, and a member of a set-builder beside what it says of
            // the member, `Set.mem_ofPred_eq`, as `forms::meets` reads them.
            Meets::Ranges => {
                let mut rules = vec!["Finset.mem_Icc", "Set.mem_Icc"];
                if has_set_builder(says) || has_set_builder(wanted) {
                    rules.push("Set.mem_ofPred_eq");
                }
                Proved::Simplified { rules, line: proof }
            }
            // The whole of a type read away, each `set` letter named by its
            // equation first.
            Meets::Universe { rules, through } => {
                let mut by: Vec<Printed> = through.iter().map(|e| t::hyp(e)).collect();
                by.extend(rules.into_iter().map(t::lemma));
                Proved::Term(t::by_term(super::super::doc::Proof::By(t::call(
                    "simpa",
                    vec![
                        super::super::doc::TacticArg::Only,
                        t::rules(by),
                        super::super::doc::TacticArg::Using(proof),
                    ],
                ))))
            }
            // Two "for all"s apart in casts are met under their binders
            // (`casts_under`), where a relation of ℚ is taken to ℝ.
            Meets::Casts { .. } => {
                match self.casts_under(proof.clone(), says, wanted) {
                    Some(met) => Proved::Term(met),
                    None => match self.casts_apart(says, wanted) {
                        Some(apart) => cast_proved(apart, proof, says, wanted)?,
                        None => Proved::Term(proof),
                    },
                }
            }
        })
    }

    /// How `says` and `wanted` are apart in casts (`forms::casts_differ`),
    /// each side's `set` letters to be rewritten by their equations, but
    /// for those a citation has already put into the goal
    /// (`defines_in_goal`).
    pub(super) fn casts_apart(
        &self,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<super::super::doc::forms::CastsApart> {
        let mut apart =
            super::super::doc::forms::casts_differ(says, wanted, &self.set_values())?;
        let in_goal = self.defines_in_goal.borrow();
        apart.at_line.retain(|e| !in_goal.contains(e));
        Some(apart)
    }

    /// The proof that closes the claim `node`, which Lean writes as `claim`,
    /// from `term`, which says `says` where that is known: one tactic where
    /// the two meet as Lean has them (`proof_meeting`); the alternatives of
    /// `closers` where they do not.
    /// A part of a cited item's sentence at the citation's values, as a
    /// tree: the values put into it, a function or property given as a value
    /// applied where the sentence applies it.
    pub(super) fn at_values(&self, part: &Node, binding: &Binding) -> Node {
        let read =
            read_at_values(part, binding, &self.sources.checked.grammar.binders());
        matching::standard(
            &matching::substitute_apart(&read, binding, self.sources.ctx),
            self.sources.ctx,
        )
    }

    /// A part of a cited item's sentence at the citation's values, written as
    /// the step's lines are: the values put into its tree, a function or
    /// property given as a value applied where the sentence applies it, by
    /// the theorem's writer, in the calculation's type where it is a row of
    /// one. None where the writer cannot write it.
    pub(super) fn written_at_values(
        &self,
        part: &Node,
        binding: &Binding,
    ) -> Option<Printed> {
        let at_values = self.at_values(part, binding);
        match self.worked_in.get() {
            Some(at)
                if at_values.notation() == EQUALITY
                    || at_values.notation() == ORDER =>
            {
                self.writer.closed_formula(&at_values, at).built()
            }
            _ => self.writer.formula(&at_values).built(),
        }
    }

    /// The claim from a cited item, or an instance of a line, read in the
    /// step's spelling (`docs/LEAN.md`, a citation): `term` proves Lean's
    /// statement of the item's part, `said`, which the step's lines write as
    /// `written`; `cited` is the citation, None for a line's instance; the
    /// item is read as `written` (`spelling::read_as_written`), or is it where the two
    /// are one statement, and the claim follows as the two meet: as written,
    /// turned round, or by the identities the meeting names. None where the
    /// bridge has no fact to read the item by, or the meeting gives no one
    /// way.
    /// The proof of `written`, the cited item as the citing step spells it,
    /// from `term`, the item as Lean states it, `said`, where the two differ
    /// only in how they spell the parts of a finite Y with j elements: the
    /// item counts a part as some natural number, `{S ∈ 𝒫 Y | ∃ m : ℕ,
    /// S.encard = m ∧ m = j}`, its Y being any set, and the step counts it
    /// in ℕ, `{S ∈ 𝒫 Y | S.ncard = j}`, its Y finite. Each such Y is the
    /// value the citation gives a letter, shown finite by the record
    /// (`shown_finite`), and the bridge `builder_count_spelt` takes the one
    /// form to the other. None where no set is so spelt, or the two differ
    /// otherwise too.
    fn parts_respelt(
        &self,
        cited: Option<&Cited>,
        term: &Printed,
        said: &Printed,
        written: &Printed,
    ) -> Option<super::super::doc::Proof> {
        let cited = cited?;
        let mut rules = Vec::new();
        let mut respelt = said.clone();
        let mut found = Vec::new();
        parts_counted_extended(said, &mut found);
        for y in &found {
            let value = cited.binding.values().find(|v| {
                self.writer
                    .set_term(v)
                    .built()
                    .is_some_and(|p| p.untyped() == y.untyped())
            })?;
            let finite = self.shown_finite(value)?;
            rules.push(t::forwards(Printed::applied(
                "LeanBridges.Counting.builder_count_spelt",
                super::super::doc::Source::Bridge(
                    super::super::doc::bridges::BridgeModule::Counting,
                ),
                vec![y.clone(), t::bracket(finite.proof)],
                super::super::doc::LeanType::Prop,
            )));
        }
        if rules.is_empty() {
            return None;
        }
        parts_counted_natural(&mut respelt);
        if !super::super::doc::forms::written_alike(&respelt, written) {
            return None;
        }
        Some(super::super::doc::Proof::By(t::on_h(
            term,
            vec![
                t::simp_only(false, None, rules, Some(t::at_h(true))),
                Tactic::Exact(t::hyp("h")),
            ],
        )))
    }

    pub(super) fn read_in_spelling(
        &self,
        cited: Option<&Cited>,
        term: &Printed,
        said: &Printed,
        written: &Printed,
        claim: StepClaim<'_>,
    ) -> Option<super::super::doc::Proof> {
        let StepClaim {
            printed: claim,
            stated: claim_stated,
        } = claim;
        // Not of a fact Lean's types make true, which says nothing to read;
        // nor in a step that works through numbers lines or the step name,
        // whose goal those numbers' equations rewrite before the step's
        // proof (`specs_in`), so that it is not the claim as written; nor a
        // claim that counts a set printed afresh, whose line may count in
        // ℕ∞, which the claim so printed does not show (as `closer` holds).
        // A claim as the step's `have` states it (`claim_stated`) shows the
        // form its counts are in.
        let through_named =
            !self.named_specs.is_empty() || !self.said_used.borrow().is_empty();
        // An integer power under a binder is read across only where the two
        // write it alike: taken to `toNat` on one side alone, its exponent's
        // fact holds only under the binder, where `omega` is not asked.
        let binder_powers_apart =
            integer_powers_under_binders(written) != integer_powers_under_binders(said);
        // An item that counts a set in ℕ∞ at a value in ℕ₀ for a claim that
        // counts it in ℤ is no other spelling of the claim: the two are met
        // by the count's definition (`count_value_met`).
        let count_value = super::orders::count_value_shape(said, claim).is_some();
        if written.is_truth()
            || through_named
            || (item_counts(claim) && !claim_stated)
            || binder_powers_apart
            || count_value
        {
            return None;
        }
        // The item and the step apart only in how they count the parts of
        // a finite set (`parts_respelt`).
        if let Some(respelt) = self.parts_respelt(cited, term, said, written) {
            return Some(respelt);
        }
        // Of an item in a wider type: not a value given it that is a numeral
        // alone, `Complex.cos 0`, which stands at the wider type with no cast
        // to move; nor a complex exponent; nor a fact of numerals alone,
        // `(abs 0 : ℤ) = 0` for a row in ℝ, which `norm_cast` works out to
        // `True` and takes nothing across, so it is worked out where it is
        // asked (as `forms::meets` holds). An item in ℝ at a step in ℚ
        // lifts the step instead (`rify`) and leaves the item as it is.
        let letters = cited.map(|c| c.item_letters.as_slice()).unwrap_or_default();
        // Only where the item applies a function to a numeral: in
        // arithmetic, `(2 : ℚ) ^ n`, `norm_cast` reads the numeral as the
        // cast of the claim's.
        let bare_widened = function_of_numeral(said)
            && letters.iter().any(|l| {
                matches!(
                    (l.item_system, l.value_system),
                    (Some(rules::System::C | rules::System::R), Some(v))
                        if Some(v) != l.item_system
                ) && cited
                    .and_then(|c| c.binding.get(&l.letter))
                    .is_some_and(|v| v.names().is_empty())
            });
        let lettered = said
            .walk()
            .iter()
            .any(|n| matches!(n.kind, super::super::doc::TermKind::Letter(_)));
        let fields = super::super::spelling::InstanceFields::of(said, written);
        if fields == super::super::spelling::InstanceFields::Wider
            && (bare_widened || complex_exponent(said) || !lettered)
        {
            return None;
        }
        let met = self.proof_meeting(
            match one_statement(written, said) {
                true => term.clone(),
                false => t::hyp("hI"),
            },
            written,
            claim,
        )?;
        Some(match one_statement(written, said) {
            true => doc::Proof::By(met.closer()),
            false => doc::Proof::Block(vec![
                Tactic::Have {
                    name: "hI".to_string(),
                    says: written.clone(),
                    proof: Box::new(doc::Proof::By(
                        super::super::spelling::read_as_written(
                            &t::bracket(term.clone()),
                            said,
                            written,
                            fields,
                            &self.set_values(),
                            letters.iter().any(|l| {
                                matches!((l.item_system, l.value_system),
                                    (Some(item), Some(value)) if item != value)
                            }),
                        ),
                    )),
                },
                met.closer(),
            ]),
        })
    }

    pub(super) fn closer(
        &self,
        node: &Node,
        claim: Option<StepClaim<'_>>,
        term: Printed,
        says: Option<&Printed>,
        met: HowMet<'_>,
        bridge: Option<CitedBridge>,
    ) -> Route<super::super::doc::Proof> {
        let HowMet { facing, meeting } = met;
        let claim_stated = claim.is_some_and(|c| c.stated);
        let claim = claim.map(|c| c.printed);
        // A claim Lean's types make true says nothing a term is met with; one
        // in another type than the term's is not known to be its; and one
        // that counts a set, printed afresh, stands where a calculation of
        // counts may take its rows in ℕ∞, which the claim so printed does not
        // show. One as the step's `have` states it (`claim_stated`) shows
        // the form its counts are in.
        let counts_unknown = |c: &Printed| item_counts(c) && !claim_stated;
        let unstated = match claim {
            Some(c) if c.is_truth() => ListReason::CitedClaimTruth,
            Some(c) if counts_unknown(c) => ListReason::CitedClaimCounts,
            _ => ListReason::CitedUnstated,
        };
        let claim = claim.filter(|c| !c.is_truth() && !counts_unknown(c));
        if let (Some(claim), Some(says)) = (claim, says) {
            // The item met with the claim only with the parts of a notation
            // that stands in no order in another order (`Cited::meetings`,
            // `Meeting::flips`): turned by the notation's lemmas.
            if let Some(met) = meeting.filter(|m| {
                !m.flips.is_empty()
                    && m.identities.is_empty()
                    && m.flips
                        .iter()
                        .all(|f| super::terms::turns_notation(&f.notation))
            }) {
                if let Some(Proved::Term(t)) =
                    self.met_proof(term.clone(), says, claim, met)
                {
                    return Route::Built(super::super::doc::Proof::Term(t));
                }
            }
            let agree = super::super::doc::forms::relation_types_agree(says, claim);
            // Where the two are alike but for the types of their terms, or
            // apart only in casts, and `norm_cast` moves every cast in both
            // to the letters and numerals (`casts::norm_cast_moves_all`), it
            // brings the two to one form, and `exact_mod_cast` closes the one
            // by the other. It relates them only through the casts they hold:
            // two stated in different types, an item in ℝ for a claim in ℚ,
            // with no cast from the one to the other, have no form in common.
            let one_type = !super::super::doc::forms::relation_types_apart(says, claim);
            let by_norm_cast = one_type
                && super::super::casts::norm_cast_moves_all(says)
                && super::super::casts::norm_cast_moves_all(claim);
            match self.proof_meeting(term.clone(), says, claim) {
                Some(Proved::Term(t)) if agree => {
                    return Route::Built(super::super::doc::Proof::Term(t))
                }
                Some(Proved::Term(_) | Proved::Cast { .. }) if by_norm_cast => {
                    return Route::Built(super::super::doc::Proof::By(
                        super::super::tactics::exact_mod_cast(term),
                    ))
                }
                // Identity elements dropped, or a cast `norm_cast` does not
                // move, are no fact a tactic is known to take the one to the
                // other by.
                Some(
                    Proved::Term(_)
                    | Proved::Cast { .. }
                    | Proved::Simplified { .. }
                    | Proved::Unsettled { .. },
                )
                | None => {}
            }
            // Statements the writer's comparison does not meet, `0 ≤ ‖(C : ℂ)‖`
            // beside `|C| ≥ 0`, whose forms as `norm_cast` leaves them are
            // alike (`casts::norm_cast_form`): `exact_mod_cast`.
            let values = self.set_values();
            let formed = super::super::doc::forms::alike_once_set(
                &super::super::casts::norm_cast_form(says),
                &super::super::casts::norm_cast_form(claim),
                &values,
            );
            if by_norm_cast && formed {
                return Route::Built(super::super::doc::Proof::By(
                    super::super::tactics::exact_mod_cast(term),
                ));
            }
            // Two stated in different types that the checker met as they
            // stand (`Cited::meetings`: no identity dropped, nothing spelt
            // otherwise), Lean's statements of them apart in no form the
            // writer chose (`forms::differences`), where `norm_cast` moves
            // every cast of both: `exact_mod_cast` takes the one up to the
            // other. Not a fact of numerals alone, with no letter or
            // function, which `norm_cast` does not take across every order;
            // nor one alike only by a library function read at another type,
            // `Real.exp` as `Complex.exp` of the cast, which `norm_cast` does
            // not take either: no function is widened here.
            let widen = |_: &str, _| None;
            let met_as_written =
                meeting.is_some_and(|m| m.identities.is_empty() && !m.respelled);
            let lifted = met_as_written
                && super::super::doc::forms::differences(says, claim, &widen)
                    .is_empty()
                && (says.lettered() || claim.lettered());
            if !one_type
                && lifted
                && super::super::casts::norm_cast_moves_all(says)
                && super::super::casts::norm_cast_moves_all(claim)
            {
                return Route::Built(super::super::doc::Proof::By(
                    super::super::tactics::exact_mod_cast(term),
                ));
            }
            // The checker paired the parts of a notation whose parts stand in
            // any order out of their places, and took nothing else to meet
            // the two (`Cited::meetings`, `permuted`): where the claim lists a
            // set's members, Lean's `{w, u}` beside the item's `{u, w}`, the
            // item taken in the claim's order.
            let listed = claim.walk().iter().any(|n| {
                matches!(
                    n.kind,
                    super::super::doc::TermKind::Listed {
                        brackets: super::super::doc::Brackets::Brace,
                        ..
                    }
                )
            });
            let only_permuted = meeting.is_some_and(|m| {
                m.permuted_only() && super::terms::permuted_only_listed(m)
            });
            if listed && only_permuted {
                return Route::Built(super::super::doc::Proof::By(reordered(
                    &term,
                    node.notation() == EQUALITY,
                )));
            }
            // An item worked in a wider field than the claim's, ℂ for a claim
            // in ℝ, taken down to it by the writer's own conversion, as an
            // instance is (`instance_closed`).
            if let Some(down) = read_down(&term, says, claim) {
                return Route::Built(super::super::doc::Proof::By(down));
            }
            // The checker met the item's conclusion at its values with the
            // claim, so in one type the two differ only in spelling and
            // casts: an equation of numbers whose casts `push_cast` all moves
            // is the item's once pushed in and put by the ring's laws,
            // `linear_combination`, its casts pushed in first; an order
            // with the item's casts is it over
            // the same atoms, `linarith`. `linear_combination e` checks that
            // the claim's left side less its right, less e's, is 0, so an e
            // Lean states turned round is given as `e.symm`. A `toNat` the
            // writer put on one side only, `2 ^ (n.toNat - 1)` beside
            // `2 ^ (n - 1)`, is another atom to `ring1` and to `linarith`,
            // and no cast moves it.
            // The item's statement as `simp` reads it, its functions given
            // as rules applied, `(fun k => 1 / k) 1` as `1 / 1`
            // (`forms::beta_reduced`): `push_cast` reads it so.
            let reduced = super::super::doc::forms::beta_reduced(says);
            let of_numbers = node.children.iter().all(|c| c.sort.is("number"));
            let pushed = super::super::casts::push_cast_moves_all_in_sides(&reduced)
                && super::super::casts::push_cast_moves_all_in_sides(claim);
            let same_to_nat = to_nat_texts(&reduced) == to_nat_texts(claim);
            let atoms = same_ring_atoms(&reduced, claim, &values);
            // An item that counts a set in ℕ∞ at a value in ℕ₀, for a claim
            // that counts it finite (`count_value_met`).
            if let (false, [_, value]) = (
                matches!(facing, Some(Facing::Turned)),
                node.children.as_slice(),
            ) {
                if let Some(met) = self.count_value_met(value, &term, &reduced, claim) {
                    return Route::Built(met);
                }
            }
            match node.notation() {
                EQUALITY
                    if one_type && of_numbers && pushed && same_to_nat && atoms =>
                {
                    // Which way the item faces the claim, as the checker met
                    // them (`Cited::facings`); where it records none, the
                    // step is declined.
                    let turned = matches!(facing, Some(Facing::Turned));
                    let facing = match facing {
                        Some(facing) => faced(term, facing),
                        None => return several_ways(ListReason::CitedFacingUnknown),
                    };
                    let says = match turned {
                        false => reduced.clone(),
                        true => super::super::doc::forms::turned_statement(&reduced),
                    };
                    // Counts in ℕ∞, which is no ring for `linear_combination`
                    // to work in, differ only by casts: `exact_mod_cast`.
                    if in_extended(claim) {
                        return Route::Built(super::super::doc::Proof::By(
                            super::super::tactics::exact_mod_cast(facing),
                        ));
                    }
                    return Route::Built(super::super::doc::Proof::By(
                        ring_combination(&facing, &says, claim),
                    ));
                }
                ORDER
                    if one_type
                        && same_to_nat
                        && atoms
                        && cast_texts(&reduced) == cast_texts(claim) =>
                {
                    return Route::Built(super::super::doc::Proof::By(
                        super::super::tactics::call(
                            "linarith",
                            vec![super::super::tactics::rules(vec![term])],
                        ),
                    ))
                }
                _ => {}
            }
            // An item stated over more than its values are in, as the record
            // says (`cited_bridge`): the Lean facts that read it as the claim.
            let turned_term = || match facing {
                Some(facing) => faced(term.clone(), facing),
                None => term.clone(),
            };
            match bridge {
                Some(CitedBridge::Rules(rules)) => {
                    return Route::Built(super::super::doc::Proof::By(
                        super::super::tactics::simpa_only(rules, turned_term()),
                    ))
                }
                Some(CitedBridge::Cast) => {
                    return Route::Built(super::super::doc::Proof::By(
                        super::super::tactics::exact_mod_cast(turned_term()),
                    ))
                }
                None => {}
            }
            // The checker met the item with the claim as written
            // (`Cited::meetings`), and the step's proof first puts each term
            // the citation gave as a named number as the cast of that number
            // (`specs_in`, `proof_of`): what is left is the item's relation
            // with each side cast up, which `norm_cast` takes back to the
            // item where the cast table says it moves a cast through the
            // relation (`casts::norm_cast_lifts_relation`).
            let as_written = meeting.is_some_and(Meeting::renamed_only);
            let through_named =
                !self.specs_in(node, &self.said_used.borrow()).is_empty();
            if as_written && through_named {
                match node.notation() {
                    // An equation the way the checker found it faces, or an
                    // order: `exact_mod_cast` of the item, of a relation in
                    // the claim's type, its casts within the sides, or one
                    // `norm_cast` lifts to it.
                    EQUALITY | ORDER
                        if super::super::doc::forms::relation_type(claim)
                            .is_some_and(|to| {
                                super::super::doc::forms::relation_type(says).as_ref()
                                    == Some(&to)
                                    || super::super::casts::norm_cast_lifts_relation(
                                        says, &to,
                                    )
                            }) =>
                    {
                        let faced_term = match (node.notation(), facing) {
                            (ORDER, _) => Some(term.clone()),
                            (_, Some(f)) => Some(faced(term.clone(), f)),
                            (_, None) => None,
                        };
                        if let Some(t) = faced_term {
                            return Route::Built(super::super::doc::Proof::By(
                                super::super::tactics::exact_mod_cast(t),
                            ));
                        }
                    }
                    // A range member Lean writes as the integer that is it
                    // (`wide_range_member`): that integer, the named number,
                    // its equation `rfl`, and the item's membership.
                    _ if wide_range_member(&self.writer, node) => {
                        let rfl = Printed::constant(
                            "rfl",
                            super::super::doc::Source::Core,
                            super::super::doc::LeanType::Prop,
                        );
                        return Route::Built(super::super::doc::Proof::By(
                            Tactic::Exact(range_member_made(rfl, term.clone())),
                        ));
                    }
                    // A claim joined by "and": part by part (`parts_closed`).
                    _ => {
                        if let Some(proof) =
                            parts_closed(node, claim, says, &term, &self.writer)
                        {
                            return Route::Built(proof);
                        }
                    }
                }
            }
            return several_ways(apart(node, &reduced, claim, &values, facing));
        }
        // A claim Lean's types make true, `True`, is closed as it stands.
        if unstated == ListReason::CitedClaimTruth {
            return Route::Built(super::super::doc::Proof::By(
                super::super::tactics::call("trivial", vec![]),
            ));
        }
        several_ways(unstated)
    }

    /// The proof of the side a forward reading of `statement`, an item's
    /// sentence at the citation's values, starts from: the line the checker
    /// read it from (`Cited::firsts`), met with that side as Lean has it;
    /// None where no line the citation names says it.
    /// `wanted`, a "there is" with no condition on its letter, `∃ u, P u`,
    /// read as `Witnessed` where `says` is P of a term it names, `P b`: the
    /// term of the line that, put for u, makes P meet the line as Lean has
    /// them (`forms::meets`). None where no term of the line does.
    pub(super) fn witness_in_line(
        &self,
        wanted: &Printed,
        says: &Printed,
    ) -> Option<Witnessed> {
        let TermKind::Quantified {
            quant: Quant::Exists,
            letter,
            guard: None,
            body,
            ..
        } = &bare_term(wanted).kind
        else {
            return None;
        };
        let values = self.set_values();
        says.walk().into_iter().find_map(|candidate| {
            let witness = candidate.clone();
            let asked =
                body.substituted(&BTreeMap::from([(letter.clone(), witness.clone())]));
            super::super::doc::forms::meets(&asked, says, &values)
                .is_some()
                .then_some(Witnessed { witness, asked })
        })
    }

    /// The proof of a definition's left side, which a citation that
    /// concludes its right side takes as its premise, from the line the
    /// checker read it from (`first_proof`); None where none says it.
    pub(super) fn premise(
        &self,
        cited: &Cited,
        statement: &Printed,
    ) -> Option<Printed> {
        left_side(statement).and_then(|wanted| self.first_proof(cited, &wanted))
    }

    /// What proves a fact a definition's right side asks, `wanted` as Lean
    /// has it: the line the checker read it from. None where none says it,
    /// or a witness's facts must be put in scope first (`known`).
    pub(super) fn shown_by_line(
        &self,
        cited: &Cited,
        wanted: Option<&Printed>,
        known: &[Tactic],
    ) -> Option<Printed> {
        match (known.is_empty(), wanted) {
            (true, Some(w)) => self.first_proof(cited, w),
            _ => None,
        }
    }

    /// The proof of `wanted` from a line the checker read the citation's
    /// reading from (`Cited::firsts`), met as Lean has it as any line that
    /// supplies a fact is (`supplied_proof`); None where none says it.
    pub(super) fn first_proof(
        &self,
        cited: &Cited,
        wanted: &Printed,
    ) -> Option<Printed> {
        if cited.firsts.is_empty() {
            return lean_truth(wanted);
        }
        // An "and" read from two lines, one-to-one-onto from a one-to-one
        // line and an onto line: each side from its line, in the order the
        // checker read them (`⟨p, q⟩`).
        if let ([left_at, right_at], Some((left, right))) =
            (cited.firsts.as_slice(), and_sides(wanted))
        {
            let side = |k: usize, by: &SuppliedBy, w: &Printed| {
                let met = cited.firsts_meetings.get(k).and_then(Option::as_ref);
                self.supplied_proof(by, w, met).built()
            };
            return Some(super::super::expr::anonymous(vec![
                side(0, left_at, &left)?,
                side(1, right_at, &right)?,
            ]));
        }
        cited.firsts.iter().enumerate().find_map(|(k, by)| {
            let met = cited.firsts_meetings.get(k).and_then(Option::as_ref);
            self.supplied_proof(by, wanted, met).built()
        })
    }

    /// The part of a "there is"'s body as Lean states it, `stated` taken
    /// apart at every "and", that the record's part `owed` is: the one at
    /// its place; a phrase whose meaning Lean writes as several parts, `W
    /// is a clique of size at least 1` as `1 ≤ |W| ∧ ∀ Y …`, those parts
    /// from its place, joined; or, where the parts from its place on,
    /// joined, meet it and that one alone does not, those, as Lean's
    /// pattern gives them to the name that takes the rest. None where the
    /// writer does not write the record's part, or the statement has too
    /// few parts for it.
    pub(super) fn stated_part(
        &self,
        stated: &[Printed],
        owed: &ObtainedPart,
    ) -> Option<Printed> {
        let single = stated.get(owed.owed)?;
        let written = self.writer.formula(&owed.owed_written).built()?;
        let joined = |parts: &[Printed]| {
            parts.iter().cloned().rev().reduce(|right, left| Printed {
                kind: super::super::doc::TermKind::Infix {
                    op: super::super::doc::Op::AND,
                    lhs: Box::new(left),
                    rhs: Box::new(right),
                },
                ty: Some(super::super::doc::LeanType::Prop),
            })
        };
        let several = super::conversions::conjoined_parts(&written).len();
        if several > 1 {
            return joined(stated.get(owed.owed..owed.owed + several)?);
        }
        let values = self.set_values();
        let meets = |p: &Printed| {
            super::super::doc::forms::meets(p, &written, &values).is_some()
        };
        match joined(&stated[owed.owed..]) {
            Some(rest) if !meets(single) && meets(&rest) => Some(rest),
            _ => Some(single.clone()),
        }
    }

    /// The line in scope whose proof is `h` read as a line naming a whole
    /// number (`SaidLine`), by what it says besides its equation, as Lean
    /// states it: `∃ m, 0 ≤ m ∧ ↑m = t`, its order; `∃ m, ↑m = t ∧ m ∈ …`, its
    /// range; `∃ m, ↑m = t`, nothing. None where no line in scope has that
    /// proof, or it says no "there is".
    pub(super) fn said_line_of(&self, h: &Printed) -> Option<SaidLine> {
        let says = self
            .trees
            .values()
            .flatten()
            .find(|s| s.proof.untyped() == h.untyped())?
            .says
            .clone()?;
        let TermKind::Quantified {
            quant: Quant::Exists,
            guard,
            body,
            ..
        } = &bare_term(&says).kind
        else {
            return None;
        };
        let beside = match (guard, and_sides(body)) {
            (Some(_), _) => Beside::Order,
            (None, Some((first, _))) if relation_symbol(&first) == Some("=") => {
                Beside::Range
            }
            (None, Some(_)) => Beside::Order,
            (None, None) => Beside::Nothing,
        };
        Some(SaidLine {
            proof: h.clone(),
            beside,
        })
    }

    /// The term the number a line in scope names is, the `t` of its
    /// `∃ m, 0 < m ∧ ↑m = t` whose proof is `h`; None where no line in scope
    /// has that proof or it says no such equation.
    fn term_named_by(&self, h: &Printed) -> Option<Printed> {
        let says = self
            .trees
            .values()
            .flatten()
            .find(|s| s.proof.untyped() == h.untyped())?
            .says
            .clone()?;
        let TermKind::Quantified {
            quant: Quant::Exists,
            letter,
            guard,
            body,
            ..
        } = &bare_term(&says).kind
        else {
            return None;
        };
        let mut parts: Vec<Printed> = guard.iter().map(|g| (**g).clone()).collect();
        match and_sides(body) {
            Some((first, second)) => parts.extend([first, second]),
            None => parts.push((**body).clone()),
        }
        parts.iter().find_map(|p| witness_equation(p, letter))
    }

    /// The term the number `h` names stands for, as the line `line` writes
    /// it, and the number's equation with it: of a line naming it, `a/k ∈
    /// ℕ`, what that line says (`term_named_by`, `SaidLine::equation`); of a
    /// number the step names (`name_wholes`), `Classical.choose_spec h`, and
    /// its term found in `line`'s tree and written as the writer writes it
    /// with no number named. None where `h` is neither, or the line writes
    /// no such term.
    fn number_named(&self, h: &Printed, line: &Printed) -> Option<NumberNamed> {
        if let (Some(said), Some(term)) = (self.said_line_of(h), self.term_named_by(h))
        {
            return Some(NumberNamed {
                term,
                equation: said.equation(),
            });
        }
        let named = self
            .writer
            .integers
            .iter()
            .find(|i| i.value.is_none() && i.proof.untyped() == h.untyped())?;
        let node = self
            .trees
            .values()
            .flatten()
            .find(|s| s.proof.untyped() == line.untyped())?
            .node
            .walk()
            .into_iter()
            .find(|n| self.writer.grammar.print(n) == named.term)?;
        let mut plain = self.writer.with_letters(self.writer.letters.clone());
        plain.integers.retain(|i| i.proof.untyped() != h.untyped());
        let at = plain.carrier(&node).built()?;
        Some(NumberNamed {
            term: plain.number(&node, at).built()?,
            equation: spec_of(named),
        })
    }

    /// `wanted`, said of numbers lines name for terms, `Classical.choose
    /// s1b ^ 2 + … = Classical.choose s1d ^ 2`, from a line `says` of those
    /// terms, `(a/k)² + (b/k)² = (c/k)²`: the line with each number put for
    /// its term by the equation of the line naming it, then cast down,
    /// `rw [← (Classical.choose_spec s1b).2, …] at h; exact_mod_cast h`.
    /// None where `wanted` names no such number, the line is one that names
    /// one, or a number's term is not in the line as Lean writes it.
    fn line_at_named(
        &self,
        proof: &Printed,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<Printed> {
        let chosen = chosen_witnesses(wanted);
        if chosen.is_empty() || chosen.iter().any(|h| h.untyped() == proof.untyped()) {
            return None;
        }
        let parts: Vec<Printed> = says.walk().iter().map(|n| n.untyped()).collect();
        let mut rules = Vec::new();
        for h in &chosen {
            let named = self.number_named(h, proof)?;
            if !parts.contains(&named.term.untyped()) {
                return None;
            }
            rules.push(t::backwards(named.equation));
        }
        let at = TacticArg::At(vec![super::super::doc::Location::Hypothesis(
            "h".to_string(),
        )]);
        Some(t::by_term(super::super::doc::Proof::By(t::on_h(
            proof,
            vec![
                t::call("rw", vec![TacticArg::Rules(rules), at]),
                t::exact_mod_cast(t::hyp("h")),
            ],
        ))))
    }

    /// A line Lean states of the whole number a term is
    /// (`Writer::slot_witness`), `∃ m : ℤ, (m : ℚ) = a/k ∧ …`, where what is
    /// asked of it is said of a number a line names for that term,
    /// `Classical.choose s1b` of `a/k ∈ ℕ`: the line at that number
    /// (`parley_witness_at`), once for each such term it opens with, and what
    /// it then says. None where it opens with no such term, or with one no
    /// number `wanted` holds is named for.
    fn at_named_numbers(
        &self,
        proof: &Printed,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<LineAtNumbers> {
        let chosen = chosen_witnesses(wanted);
        let mut proof = proof.clone();
        let mut says = bare_term(says).clone();
        let mut opened = false;
        while let TermKind::Quantified {
            quant: Quant::Exists,
            letter,
            letter_ty: LeanType::Num(ty @ (Num::Int | Num::Nat)),
            guard: Some(guard),
            body,
            ..
        } = &says.kind
        {
            let Some(term) = witness_equation(guard, letter) else {
                break;
            };
            let h = chosen.iter().find(|h| {
                self.term_named_by(h)
                    .is_some_and(|t| t.untyped() == term.untyped())
            })?;
            let line = self.said_line_of(h)?;
            let lemma = match ty {
                Num::Nat => "parley_witness_at_nat",
                _ => "parley_witness_at",
            };
            let number = line.chosen(*ty);
            proof = Printed {
                kind: TermKind::App {
                    head: Box::new(super::super::tactics::bridge_lemma(
                        lemma,
                        BridgeModule::PowerTactics,
                    )),
                    args: [proof, number.clone(), line.equation()]
                        .into_iter()
                        .map(super::super::doc::Arg::Explicit)
                        .collect(),
                    explicit: false,
                },
                ty: Some(LeanType::Prop),
            };
            let values = BTreeMap::from([(letter.clone(), number)]);
            let next = super::super::doc::forms::substituted_all(body, &values);
            says = bare_term(&next).clone();
            opened = true;
        }
        opened.then_some(LineAtNumbers { proof, says })
    }

    /// The proof of the line `by` names and what it says in Lean: a line or
    /// sentence the step names, a `let` line that says it once, or the
    /// step's requires line as written. Declined for anything else.
    pub(super) fn line_proof(&self, by: &SuppliedBy) -> Route<(Printed, Printed)> {
        match by {
            SuppliedBy::Line(at) | SuppliedBy::SaidOnce(at) => self.line_says(at),
            SuppliedBy::Requires {
                line,
                implied: None,
            } => {
                let (name, said) = match self.requires_line(*line) {
                    Route::Built(r) => r,
                    Route::Declined(d) => return Route::Declined(d),
                };
                self.line_statement(&said)
                    .map(|s| (super::super::tactics::hyp(&name), s))
            }
            _ => Route::no("a fact no one line says"),
        }
    }

    /// The step's requires line `line`, counted from 0: its Lean name and its
    /// sentence. Declined outside a step, or for a line of several sentences.
    pub(super) fn requires_line(
        &self,
        line: usize,
    ) -> Route<(String, super::super::algebra::Cited)> {
        let Some(step) = self.step_now.get() else {
            return Route::no("a requires line outside a step");
        };
        let name = format!("r{}_{}", self.thm.steps[step].line, line + 1);
        match self.trees.get(&name).map(Vec::as_slice) {
            Some([said]) => Route::Built((name, said.cited())),
            _ => Route::no("a requires line not one sentence"),
        }
    }

    /// The proof of a hypothesis of a cited item from where the checker
    /// found it supplied (`Cited::supplied`): the line, the sentence or
    /// the part of one the citation names or the `let` line that says it
    /// once, or the step's requires line, or what one of those implies,
    /// meeting `wanted`, the hypothesis as Lean asks it at the citation's
    /// values. Declined where no line supplies it, or the line says it
    /// otherwise than Lean asks.
    pub(super) fn supplied_proof(
        &self,
        by: &SuppliedBy,
        wanted: &Printed,
        meeting: Option<&Meeting>,
    ) -> Route<Printed> {
        // What Lean proves as it stands, whatever line supplies it.
        if let Some(p) = lean_truth(wanted) {
            return Route::Built(p);
        }
        let (proof, says) = match by {
            SuppliedBy::Line(_)
            | SuppliedBy::SaidOnce(_)
            | SuppliedBy::Requires { implied: None, .. } => match self.line_proof(by) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            },
            // What the line implies is what the checker found `wanted` to
            // be.
            SuppliedBy::Requires {
                line,
                implied: Some(rule),
            } => {
                let said = match self.requires_line(*line) {
                    Route::Built((_, said)) => said,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match self.implied_proof(&said, *rule, wanted) {
                    Route::Built(p) => (p, wanted.clone()),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            SuppliedBy::Walked(walked) => return self.walked_proof(walked, wanted),
            // A membership a function's type or a subset carries: the one
            // applied to the other, `hH4 s8_1a`, as Mathlib's `Set.MapsTo`
            // and `⊆` each take a membership to one.
            // A "for all" line takes the member itself first, `hH6 x h_x`.
            SuppliedBy::Through { carrier, member } => {
                let (c, says) = match self.line_proof(carrier) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let (m, m_says) = match &**member {
                    SuppliedBy::Bound { letter } => (bound_proof(letter), None),
                    other => match self.line_proof(other) {
                        Route::Built((m, s)) => (m, Some(s)),
                        Route::Declined(d) => return Route::Declined(d),
                    },
                };
                // A range Lean writes as a `Finset` where it is counted over
                // and as a `Set` in a subset: a membership crosses between
                // the two by `Finset.mem_Icc`, each the bounds alike.
                let crossed = |p: Printed,
                               from: Option<&Printed>,
                               to: Option<&Printed>| {
                    let way = match (from.and_then(range_head), to.and_then(range_head))
                    {
                        (Some("Finset.Icc"), Some("Set.Icc")) => "mp",
                        (Some("Set.Icc"), Some("Finset.Icc")) => "mpr",
                        _ => return p,
                    };
                    applied_to(
                        fields(super::super::tactics::lemma("Finset.mem_Icc"), &[way]),
                        p,
                    )
                };
                let (small, big) = subset_sides(&says).unzip();
                let m = crossed(m, m_says.as_ref(), small.as_ref());
                let c = match small {
                    Some(_) => {
                        return Route::Built(crossed(
                            applied_to(c, m),
                            big.as_ref(),
                            Some(wanted),
                        ))
                    }
                    None => c,
                };
                return match &bare_term(&says).kind {
                    super::super::doc::TermKind::Quantified {
                        quant: super::super::doc::Quant::ForAll,
                        letter_ty,
                        ..
                    } => {
                        let SuppliedBy::Bound { letter } = &**member else {
                            return Route::no(
                                "a \"for all\" line at a member a line names",
                            );
                        };
                        let x = Printed::letter(
                            super::super::names::letter(letter),
                            letter_ty.clone(),
                        );
                        Route::Built(applied_to(applied_to(c, x), m))
                    }
                    _ => Route::Built(applied_to(c, m)),
                };
            }
            // The membership the claim's own "for all" gives, which Lean
            // introduces with the letter (`peel`).
            SuppliedBy::Bound { letter } => return Route::Built(bound_proof(letter)),
            // An equation the same on both sides once the identity elements
            // the checker dropped are dropped (`identity_lemma`).
            SuppliedBy::Identity(met) if !met.unfolded.is_empty() => {
                // Its two sides one once the defines the checker read out
                // are (`Meeting::unfolded`), `s = (a + b)/2` of s := (a +
                // b)/2: each rewritten by the equation its `set` gives, then
                // each flip as below, after which the two are one.
                if !met.identities.is_empty() {
                    return Route::no(
                        "an equation met through a define with an identity element dropped",
                    );
                }
                let values = self.set_values();
                let mut names: Vec<String> = Vec::new();
                for u in &met.unfolded {
                    let Some(v) = values.get(&super::super::names::letter(&u.name))
                    else {
                        return Route::no(
                            "an equation met through a define the proof does not set",
                        );
                    };
                    if !names.contains(&v.equation) {
                        names.push(v.equation.clone());
                    }
                }
                let Some(flips) = super::terms::flip_rewrites(
                    &self.writer,
                    &met.flips,
                    super::terms::Toward::FromFirst,
                ) else {
                    return Route::no(
                        "an equation met through a define in an order no lemma turns",
                    );
                };
                let rules = names
                    .iter()
                    .map(|n| t::hyp(n))
                    .chain(flips)
                    .map(t::forwards)
                    .collect();
                return Route::Built(t::by_term(super::super::doc::Proof::By(
                    t::call("rw", vec![TacticArg::Rules(rules)]),
                )));
            }
            SuppliedBy::Identity(met) => {
                // Its two sides alike but for the order of the parts of a
                // notation that stands in no order, |CA| beside |AC|: the
                // left side turned to the right's by exact instances of the
                // notation's swap lemmas, after which the two are one.
                let turned = met
                    .flips
                    .iter()
                    .any(|f| super::terms::turns_notation(&f.notation));
                if met.identities.is_empty() && turned {
                    if let super::super::doc::TermKind::Infix { op, .. } =
                        &unparenthesized(wanted).kind
                    {
                        // The checker met the left side with the right
                        // (`Known::alike_how`), so each flip's term is the
                        // left side's, which the rewrite takes to the right's.
                        let rewrites = super::terms::flip_rewrites(
                            &self.writer,
                            &met.flips,
                            super::terms::Toward::FromFirst,
                        )
                        .unwrap_or_default();
                        if op.symbol == "=" && !rewrites.is_empty() {
                            return Route::Built(t::by_term(
                                super::super::doc::Proof::By(t::call(
                                    "rw",
                                    vec![TacticArg::Rules(
                                        rewrites.into_iter().map(t::forwards).collect(),
                                    )],
                                )),
                            ));
                        }
                    }
                }
                if met.identities.is_empty() {
                    return Route::Built(Printed::constant(
                        "rfl",
                        super::super::doc::Source::Core,
                        super::super::doc::LeanType::Prop,
                    ));
                }
                let mut rules: Vec<&'static str> = Vec::new();
                for d in &met.identities {
                    let Some(rule) = identity_lemma(d) else {
                        return Route::no(
                            "an identity element dropped that no lemma names",
                        );
                    };
                    if !rules.contains(&rule) {
                        rules.push(rule);
                    }
                }
                return Route::Built(super::super::tactics::by_term(
                    super::super::doc::Proof::By(super::super::tactics::simp_only(
                        false,
                        None,
                        rules
                            .into_iter()
                            .map(|r| {
                                super::super::tactics::forwards(
                                    super::super::tactics::lemma(r),
                                )
                            })
                            .collect(),
                        None,
                    )),
                ));
            }
            // An "and" part by part, each from where it stands.
            SuppliedBy::Parts(parts) => {
                let asked = conjoined_parts(wanted);
                if asked.len() != parts.len() {
                    return Route::no("an \"and\" Lean joins otherwise than the page");
                }
                let mut proofs = Vec::new();
                for (part, by) in asked.iter().zip(parts) {
                    match self.supplied_proof(by, part, None) {
                        Route::Built(p) => proofs.push(p),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                return Route::Built(super::super::expr::anonymous(proofs));
            }
            SuppliedBy::Unstated => return Route::no("no line states it"),
        };
        self.said_proof(proof, says, wanted, meeting)
    }

    /// `⟨left, right⟩`, each side of `wanted`, an "and", from that side of
    /// `says` (`said_proof`), where some part of the two stands in another
    /// type. None where either is no "and", their parts differ in number,
    /// or every part is in one type with its own.
    pub(super) fn parts_apart(
        &self,
        proof: &Printed,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<Printed> {
        let (said, asked) = (conjoined_parts(says), conjoined_parts(wanted));
        if said.len() < 2
            || said.len() != asked.len()
            || !said
                .iter()
                .zip(&asked)
                .any(|(s, a)| forms::relation_types_apart(s, a))
        {
            return None;
        }
        let ((sl, sr), (wl, wr)) = (and_sides(says)?, and_sides(wanted)?);
        // A proof listed part by part, `⟨h1, h2, h3⟩`, gives its first and
        // the rest; any other, its projections.
        let (pl, pr) = match &unparenthesized(proof).kind {
            TermKind::Listed { items, .. } if items.len() == said.len() => {
                let rest = match &items[1..] {
                    [one] => one.clone(),
                    more => super::super::expr::anonymous(more.to_vec()),
                };
                (items[0].clone(), rest)
            }
            _ => (fields(proof.clone(), &["1"]), fields(proof.clone(), &["2"])),
        };
        let left = self.said_proof(pl, sl, &wl, None).built()?;
        let right = self.said_proof(pr, sr, &wr, None).built()?;
        Some(super::super::expr::anonymous(vec![left, right]))
    }

    /// The proof of `wanted` from `proof` of `says`, the line that supplies
    /// it, met as the checker met them (`meeting`). An "and" whose parts
    /// stand in different types, `1 + 1/(N : ℚ) ≠ 1 ∧ |1 + 1/(N : ℝ) − 1| <
    /// p` for the same in ℝ, is met part by part.
    pub(super) fn said_proof(
        &self,
        proof: Printed,
        says: Printed,
        wanted: &Printed,
        meeting: Option<&Meeting>,
    ) -> Route<Printed> {
        if let Some(p) = self.parts_apart(&proof, &says, wanted) {
            return Route::Built(p);
        }
        // A line of numerals and functions of them alone for a statement of
        // the same in another type or turned, `(0 ^ 2 : ℤ) = 0` for `0 ^ 2
        // = 0` in ℝ, `abs (0 − 1) < 1/2`: the line put in the goal and the
        // whole worked out, which holds whether the line is true or, in a
        // contradiction, false. Only where Lean meets the two no other way
        // (`forms::meets`): a line it reads as the statement, turned, or
        // across a cast is cited so.
        let met = super::super::doc::forms::meets(&says, wanted, &self.set_values())
            .is_some();
        if no_letter(&says) && no_letter(wanted) && !met {
            return Route::Built(t::by_term(super::super::doc::Proof::By(t::on_h(
                &proof,
                vec![
                    t::call("revert", vec![TacticArg::Term(t::hyp("h"))]),
                    t::call("norm_num", vec![]),
                ],
            ))));
        }
        // How the line met the hypothesis, where the checker met them
        // otherwise than as written (`Supplied::meeting`): a listed set's
        // members in another order (`reordered`); the sides turned, the
        // identity elements dropped (`met_proof`).
        if let Some(met) =
            meeting.filter(|m| m.permuted || m.turned || !m.identities.is_empty())
        {
            if met.permuted_only() && super::terms::permuted_only_listed(met) {
                let equation = relation_symbol(wanted) == Some("=");
                return Route::Built(super::super::tactics::by_term(
                    super::super::doc::Proof::By(reordered(&proof, equation)),
                ));
            }
            return match self.met_proof(proof, &says, wanted, met) {
                Some(p) => Route::Built(p.term()),
                None => Route::no("a line met otherwise than one tactic takes"),
            };
        }
        // A "there is" a line says with its map applied worked out and its
        // letter renamed, `∃ x ∈ S, t = x.ncard` for `∃ s ∈ S, t = (fun x =>
        // x.ncard) s`, which Lean takes as one statement
        // (`forms::one_term_once_set`): the line itself.
        if wanted.walk().iter().any(|n| {
            matches!(
                n.kind,
                super::super::doc::TermKind::Quantified {
                    quant: super::super::doc::Quant::Exists,
                    ..
                }
            )
        }) && super::super::doc::forms::one_term_once_set(
            &says,
            wanted,
            &self.set_values(),
        ) {
            return Route::Built(proof);
        }
        // A membership Lean writes as the number it is with what the
        // number system asks of it, `∃ m : ℤ, 0 ≤ m ∧ (m : ℤ) = N` of N ∈
        // ℕ₀, from a line saying what is asked, `0 ≤ N`: `⟨N, h, rfl⟩`.
        if let (Some(member), None) = (number_member(wanted), number_member(&says)) {
            return match self.proof_meeting(proof, &says, &member.asked) {
                Some(p) => Route::Built(super::super::expr::anonymous(vec![
                    member.witness,
                    p.term(),
                    Printed::constant(
                        "rfl",
                        super::super::doc::Source::Core,
                        super::super::doc::LeanType::Prop,
                    ),
                ])),
                None => Route::no("a line that does not say what a membership asks"),
            };
        }
        // A set with a member, which Lean writes `∃ s ∈ S, True`, from a
        // line naming one, `a ∈ S`: `⟨a, h, trivial⟩`.
        if let Some(member) = member_named(wanted, &says) {
            return match self.proof_meeting(proof, &says, &member.asked) {
                Some(p) => Route::Built(super::super::expr::anonymous(vec![
                    member.witness,
                    p.term(),
                    Printed::constant(
                        "trivial",
                        super::super::doc::Source::Core,
                        super::super::doc::LeanType::Prop,
                    ),
                ])),
                None => Route::no("a line naming a member of another set"),
            };
        }
        // A "there is" the line says of one term, `∃ u, ∀ s ∈ S, s ≤ u` of
        // a line `∀ s ∈ S, s ≤ b`: `⟨b, h⟩`.
        if let Some(witness) = self.witness_in_line(wanted, &says) {
            if let Some(p) = self.proof_meeting(proof.clone(), &says, &witness.asked) {
                return Route::Built(super::super::expr::anonymous(vec![
                    witness.witness,
                    p.term(),
                ]));
            }
        }
        // A line of the whole numbers terms are, asked of the numbers lines
        // name for them: the line at those numbers, met as any line is.
        if let Some(at) = self.at_named_numbers(&proof, &says, wanted) {
            return self.said_proof(at.proof, at.says, wanted, meeting);
        }
        // A named number's order, from a line putting its term in ℕ or ℕ₀.
        if let Some(order) = self.named_number_order(&proof, &says, wanted) {
            return Route::Built(order);
        }
        // A line of the terms lines name numbers for, asked of those
        // numbers where no claim's proof has put it in terms of them.
        if !self.line_put_in_numbers(&proof, wanted) {
            if let Some(p) = self.line_at_named(&proof, &says, wanted) {
                return Route::Built(p);
            }
        }
        // A number a line names, `Classical.choose r29_1` of `∃ m : ℤ, 0 ≤ m
        // ∧ (m : ℝ) = k^(n − 1) mod n`, asked of that line itself: what it
        // says of the number besides its equation, `0 ≤ m` or `m ∈
        // Finset.Icc a b`, its spec's other part.
        let chosen = chosen_witnesses(wanted);
        if let Some(h) = chosen.iter().find(|h| h.untyped() == proof.untyped()) {
            return match self.said_line_of(h).and_then(|l| l.besides()) {
                Some(p) => Route::Built(p),
                None => Route::no("a number's own line asked for more than it says"),
            };
        }
        // A differentiability Lean asks over a domain that is all of its
        // type, `∀ y ∈ Set.univ, Set.univ ∈ nhds y ∧ DifferentiableAt ℝ f y`,
        // of a line that says the derivative alone, as of f between number
        // systems: the whole type about each point taken as true, then the
        // line.
        if super::super::spelling::whole_about_a_point(wanted)
            && !super::super::spelling::whole_about_a_point(&says)
        {
            return Route::Built(t::by_term(super::super::doc::Proof::By(
                Tactic::Seq(vec![
                    t::simp_only(
                        false,
                        None,
                        vec![
                            t::forwards(t::lemma("Filter.univ_mem")),
                            t::forwards(t::lemma("true_and")),
                        ],
                        None,
                    ),
                    Tactic::Exact(proof),
                ]),
            )));
        }
        // A line in another type than Lean asks, `(10^(k + 1) : ℤ) > 0` for
        // `0 < (10^(k + 1) : ℚ)`, is taken across by `exact_mod_cast`, where
        // the cast table says `norm_cast` moves a cast of the two types
        // through the relation, every cast of what Lean asks moves, and the
        // two are alike but for their casts. `exact_mod_cast` compares the
        // relations as written, so a line saying `>` where Lean asks `<` is
        // turned first (`gt_iff_lt`). A fact of ℚ is taken to ℝ by ℚ's cast
        // lemmas (`rat_to_real`), whatever its relation: `exact_mod_cast`
        // writes a power of a numeral as a cast of ℕ, `3 ^ k.toNat`, and
        // then leaves the fact in ℚ and the goal in ℝ, and does not take a
        // fact of numerals across, `(0 : ℚ) ≤ 3^m` for `(0 : ℝ) ≤ 3^m`. A
        // fact of numerals alone never gets here (`lean_truth`).
        if forms::relation_types_apart(&says, wanted) {
            let by_norm_cast = forms::relation_type(wanted).is_some_and(|to| {
                super::super::casts::norm_cast_lifts_relation(&says, &to)
            }) && super::super::casts::norm_cast_moves_all(wanted);
            let rational_to_real = forms::relation_type(&says)
                == Some(LeanType::Num(Num::Rat))
                && forms::relation_type(wanted) == Some(LeanType::Num(Num::Real));
            let lifts = rational_to_real || by_norm_cast;
            // A cited line the step's proof puts in terms of the numbers
            // lines name before the citation (`proof_of`), 5.5.2's
            // `mod(a^(p − 2), p) < p` in ℝ as `c < p`, says what is asked
            // of that number once its casts are moved.
            if !lifts && self.line_put_in_numbers(&proof, wanted) {
                return Route::Built(super::super::tactics::by_term(
                    super::super::doc::Proof::By(
                        super::super::tactics::exact_mod_cast(proof),
                    ),
                ));
            }
            // A line in a wider type, `e = 2 * (b : ℝ)` with e a `set` of
            // `(a : ℝ) + 1`, for `a + 1 = 2 * b` in ℤ: alike but for casts
            // once each `set` letter is its value (`Meets::Casts`), taken
            // down by `exact_mod_cast` after those values are put in.
            let narrower = matches!(
                (forms::relation_type(&says), forms::relation_type(wanted)),
                (Some(LeanType::Num(from)), Some(LeanType::Num(to))) if to < from
            );
            if !lifts && narrower {
                if let Some(forms::Meets::Casts { through, .. }) =
                    forms::meets(&says, wanted, &self.set_values())
                {
                    let mut steps = Vec::new();
                    if !through.is_empty() {
                        steps.push(t::simp_only(
                            false,
                            None,
                            through.iter().map(|e| t::forwards(t::hyp(e))).collect(),
                            Some(t::at_h(false)),
                        ));
                    }
                    steps.push(t::exact_mod_cast(t::hyp("h")));
                    return Route::Built(t::by_term(super::super::doc::Proof::By(
                        t::on_h(&proof, steps),
                    )));
                }
            }
            // A membership of a listed set, `(1 : ℤ) ∈ {1, 2}` for `(1 : ℝ) ∈
            // {1, 2}`: both read as the members' equations they say, which
            // `exact_mod_cast` takes across.
            if !lifts && listed_membership(&says) && listed_membership(wanted) {
                let lemmas = || {
                    vec![
                        t::forwards(t::lemma("Set.mem_insert_iff")),
                        t::forwards(t::lemma("Set.mem_singleton_iff")),
                    ]
                };
                return Route::Built(t::by_term(super::super::doc::Proof::By(
                    t::on_h(
                        &proof,
                        vec![
                            t::simp_only(false, None, lemmas(), Some(t::at_h(true))),
                            t::exact_mod_cast(t::hyp("h")),
                        ],
                    ),
                )));
            }
            // Two pairs equal in other types, `((a, b) : ℝ × ℝ) = (c, d)` for
            // the pairs in ℂ × ℂ: each taken apart into its coordinates'
            // equations, which `exact_mod_cast` takes across; `norm_cast`
            // moves no cast through a pair. A line of a `set` map whose
            // values are pairs, `f i = f j` of f's rule `fun i => (L i, M
            // i)`, is that map's equation put in first (`maps_opened`).
            let opened = forms::maps_opened(&says, &self.set_values())
                .filter(|o| pair_equation(&o.says));
            if (pair_equation(&says) || opened.is_some()) && pair_equation(wanted) {
                let mut rules: Vec<_> = opened
                    .iter()
                    .flat_map(|o| o.equations.iter().map(|e| t::forwards(t::hyp(e))))
                    .collect();
                rules.push(t::forwards(t::lemma("Prod.mk.injEq")));
                let apart =
                    || t::simp_only(false, None, rules.clone(), Some(t::at_h(true)));
                return Route::Built(t::by_term(super::super::doc::Proof::By(
                    t::on_h(&proof, vec![apart(), t::exact_mod_cast(t::hyp("h"))]),
                )));
            }
            if !lifts {
                return Route::no("a line in another type no cast takes across");
            }
            let turn = order_turn(&says, wanted);
            let faced = turn.as_ref().map_or(says.clone(), |t| t.faced.clone());
            if forms::meets(&faced, wanted, &self.set_values()).is_none() {
                return Route::no("a line in another type that does not meet it");
            }
            let proof = match turn {
                Some(t) => turned_order(t.lemma, proof),
                None => proof,
            };
            // ℚ's order is taken to ℝ's by ℚ's own cast lemmas
            // (`rat_to_real`), which `norm_cast` does not do.
            if rational_to_real {
                return match rat_to_real(proof, &faced, wanted.clone()) {
                    Some(p) => Route::Built(p),
                    None => Route::no("a relation of ℚ with no cast lemma to ℝ"),
                };
            }
            return Route::Built(super::super::tactics::by_term(
                super::super::doc::Proof::By(super::super::tactics::exact_mod_cast(
                    proof,
                )),
            ));
        }
        // One whose type is known on one side alone is not known to meet it.
        if !forms::relation_types_agree(&says, wanted) {
            return Route::no("a line whose type is known on one side alone");
        }
        match self.proof_meeting(proof.clone(), &says, wanted) {
            Some(p) => Route::Built(p.term()),
            None => match self.for_all_converted(proof.clone(), &says, wanted) {
                Some(p) => Route::Built(p),
                None => match self
                    .named_put_back(proof.clone(), &says, wanted)
                    .or_else(|| self.to_nat_met(proof, &says, wanted))
                {
                    Some(p) => Route::Built(p),
                    None => Route::no("a line that does not meet it"),
                },
            },
        }
    }

    /// The proof of `wanted`, which holds a number the step names as an
    /// integer's `toNat`, cast back, `((2^p − 1).toNat : ℤ)`, from `proof`
    /// of `says`, which writes the integer, `2^p − 1`: each such number put
    /// back by its name's own equation (`SaidInteger::back`), and the line
    /// meeting what is left. None where `wanted` holds no such number, or
    /// what is left does not meet the line.
    pub(super) fn named_put_back(
        &self,
        proof: Printed,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<Printed> {
        let back = self.put_back(wanted)?;
        let met = self.proof_meeting(proof, says, &back.left)?.term();
        Some(back.then(met))
    }

    /// The proof of `wanted` from `proof` of `says`, the same once each
    /// natural number cast to ℤ and taken back is read as that number
    /// (`naturals_read`), σ of `((a : ℤ) * (b : ℤ)).toNat` as σ of `a * b`:
    /// `exact_mod_cast proof`, which reads it so (`Int.toNat_natCast`).
    /// None where they differ in more, or in nothing such.
    pub(super) fn to_nat_met(
        &self,
        proof: Printed,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<Printed> {
        let read = naturals_read(wanted);
        let met = read != *wanted
            && super::super::doc::forms::alike_once_set(
                &naturals_read(says),
                &read,
                &self.set_values(),
            );
        met.then(|| {
            super::super::tactics::by_term(super::super::doc::Proof::By(
                super::super::tactics::exact_mod_cast(proof),
            ))
        })
    }

    /// `wanted` with each number the step names as an integer's `toNat`,
    /// cast back, written as the integer, and the rewrites by the names'
    /// own equations that turn the one into the other (`SaidInteger::back`).
    /// None where `wanted` holds no such number, or one the step does not
    /// name so.
    pub(super) fn put_back(&self, wanted: &Printed) -> Option<PutBack> {
        let mut integers = Vec::new();
        let left = to_nat_casts_removed(wanted, &mut integers);
        if integers.is_empty() {
            return None;
        }
        let mut rules = Vec::new();
        for u in &integers {
            let back = self.writer.integers.iter().find_map(|s| {
                let value = s.value.as_ref()?;
                let super::super::doc::TermKind::ToNat(inner) =
                    &unparenthesized(value).kind
                else {
                    return None;
                };
                (bare_term(inner).untyped() == bare_term(u).untyped())
                    .then(|| s.back.clone())
                    .flatten()
            })?;
            rules.push(super::super::tactics::forwards(back));
        }
        Some(PutBack { left, rules })
    }

    /// Whether the line `proof` proves is one the step's proof rewrites in
    /// terms of the numbers lines name before it writes the citation
    /// (`proof_of`): the claim being written has a term such a line names
    /// (`specs_in`), `wanted` asks of that number, and the line is not
    /// one that gives a number, which is left as it is.
    pub(super) fn line_put_in_numbers(
        &self,
        proof: &Printed,
        wanted: &Printed,
    ) -> bool {
        let claim = self.claim_now.borrow();
        let Some(claim) = claim.as_ref() else {
            return false;
        };
        let used = self.said_used.borrow();
        if self.specs_in(claim, &used).is_empty() {
            return false;
        }
        let chosen = chosen_witnesses(wanted);
        let asks_named = used
            .iter()
            .any(|u| chosen.iter().any(|h| h.untyped() == u.line.proof.untyped()));
        let gives = used
            .iter()
            .any(|u| u.line.proof.untyped() == proof.untyped());
        asks_named && !gives
    }

    /// The proof of `wanted` from `proof` of `says` where the two open with
    /// the same "for all"s and "if"s, the conditions alike, and the last
    /// statements differ only by casts (`forms::meets`, `Meets::Casts`):
    /// `intro k h_1; exact_mod_cast h k h_1`. None for any other two.
    pub(super) fn casts_under(
        &self,
        proof: Printed,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<Printed> {
        let values = self.set_values();
        let mut intros: Vec<String> = Vec::new();
        let mut applied = proof;
        let (mut w, mut s) = (bare_term(wanted).clone(), bare_term(says).clone());
        loop {
            let next = match (&w.kind, &s.kind) {
                (
                    TermKind::Quantified {
                        quant: Quant::ForAll,
                        letter,
                        letter_ty,
                        guard,
                        body,
                        ..
                    },
                    TermKind::Quantified {
                        quant: Quant::ForAll,
                        letter: theirs,
                        guard: their_guard,
                        body: their_body,
                        ..
                    },
                ) => {
                    let x = Printed::letter(letter, letter_ty.clone());
                    let at = BTreeMap::from([(theirs.clone(), x.clone())]);
                    intros.push(letter.clone());
                    applied = applied_to(applied, x);
                    // The same condition on the letter, or none on either.
                    match (guard, their_guard) {
                        (None, None) => {}
                        (Some(g), Some(their_g))
                            if forms::meets(&their_g.substituted(&at), g, &values)
                                .is_some_and(|m| {
                                    matches!(
                                        m,
                                        forms::Meets::Same | forms::Meets::Unfolded
                                    )
                                }) =>
                        {
                            let h = format!("h_{letter}");
                            intros.push(h.clone());
                            applied = applied_to(applied, t::hyp(&h));
                        }
                        _ => break,
                    }
                    ((**body).clone(), their_body.substituted(&at))
                }
                (
                    TermKind::Infix { op, lhs, rhs },
                    TermKind::Infix {
                        op: their_op,
                        lhs: their_lhs,
                        rhs: their_rhs,
                    },
                ) if op.symbol == "→"
                    && their_op.symbol == "→"
                    && forms::meets(their_lhs, lhs, &values).is_some_and(|m| {
                        matches!(m, forms::Meets::Same | forms::Meets::Unfolded)
                    }) =>
                {
                    let h = format!("h_{}", intros.len() + 1);
                    intros.push(h.clone());
                    applied = applied_to(applied, t::hyp(&h));
                    ((**rhs).clone(), (**their_rhs).clone())
                }
                _ => break,
            };
            (w, s) = (bare_term(&next.0).clone(), bare_term(&next.1).clone());
        }
        let cast = matches!(
            forms::meets(&s, &w, &values),
            Some(forms::Meets::Casts { .. })
        );
        if intros.is_empty() || !cast {
            return None;
        }
        // A relation of ℚ for the same of ℝ, which `norm_cast` does not take
        // up, the line holding no cast to ℝ: by the relation's lemma at ℝ,
        // ℚ's casts pushed down to the letters and numerals, and the two
        // then met by pushing the casts left in both alike.
        if rat_crossing(&s, &w) {
            let lifted = rat_lifted(applied, &s)?;
            return Some(t::by_term(super::super::doc::Proof::By(Tactic::Seq(vec![
                Tactic::Intro(intros),
                Tactic::Exact(lifted),
            ]))));
        }
        Some(t::by_term(super::super::doc::Proof::By(Tactic::Seq(vec![
            Tactic::Intro(intros),
            t::exact_mod_cast(applied),
        ]))))
    }

    /// The proof of `wanted`, a "for all" over a set, from `proof` of
    /// `says`, a "for all" whose body meets it where Lean writes the two
    /// apart: over all of a type, `∀ x : ℝ, P x` for `∀ x ∈ Set.univ, P x`
    /// (`intro x _; exact h x`); and with what a set of ℝ around each of
    /// its points says of it, `Set.univ ∈ nhds x`, which Lean writes into a
    /// differentiability on ℝ and the line does not
    /// (`⟨Filter.univ_mem, h x hx⟩`). Any other "for all" is met under its
    /// binders by its casts (`casts_under`). None for any other two.
    pub(super) fn for_all_converted(
        &self,
        proof: Printed,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<Printed> {
        let TermKind::Quantified {
            quant: Quant::ForAll,
            letter,
            letter_ty,
            guard: Some(guard),
            body,
            ..
        } = &bare_term(wanted).kind
        else {
            return self.casts_under(proof, says, wanted);
        };
        let TermKind::Quantified {
            quant: Quant::ForAll,
            letter: theirs,
            guard: their_guard,
            body: their_body,
            ..
        } = &bare_term(says).kind
        else {
            return None;
        };
        // The line's body in the letter Lean asks it of.
        let x = Printed::letter(letter, letter_ty.clone());
        let their_body =
            their_body.substituted(&BTreeMap::from([(theirs.clone(), x.clone())]));
        let meets =
            |a: &Printed, b: &Printed| forms::meets(a, b, &self.set_values()).is_some();
        let hx = "hx".to_string();
        let at_x = || applied_to(proof.clone(), x.clone());
        let shown = match (&bare_term(guard).kind, their_guard) {
            // Over all of a type, each "for all" in turn: `∀ s ∈ Set.univ,
            // ∀ t ∈ Set.univ, …` of a line `∀ s, ∀ t, …`, `intro s _ t _`.
            (TermKind::Infix { op, rhs, .. }, None)
                if op.symbol == "∈" && is_constant(rhs, "Set.univ") =>
            {
                let mut intros = vec![letter.clone(), "_".to_string()];
                let mut applied = at_x();
                let (mut ours, mut theirs) = ((**body).clone(), their_body.clone());
                while let (
                    TermKind::Quantified {
                        quant: Quant::ForAll,
                        letter: next,
                        letter_ty: next_ty,
                        guard: Some(g),
                        body: b,
                        ..
                    },
                    TermKind::Quantified {
                        quant: Quant::ForAll,
                        letter: their_next,
                        guard: None,
                        body: tb,
                        ..
                    },
                ) = (&bare_term(&ours).kind, &bare_term(&theirs).kind)
                {
                    let univ = matches!(&bare_term(g).kind,
                        TermKind::Infix { op, rhs, .. } if op.symbol == "∈" && is_constant(rhs, "Set.univ"));
                    if !univ {
                        break;
                    }
                    let y = Printed::letter(next, next_ty.clone());
                    intros.extend([next.clone(), "_".to_string()]);
                    applied = applied_to(applied, y.clone());
                    let tb = tb.substituted(&BTreeMap::from([(their_next.clone(), y)]));
                    (ours, theirs) = ((**b).clone(), tb);
                }
                if !meets(&theirs, &ours) {
                    return self.casts_under(proof.clone(), says, wanted);
                }
                vec![Tactic::Intro(intros), Tactic::Exact(applied)]
            }
            // The same set, with `Set.univ ∈ nhds x` before the line's body.
            (_, Some(g)) if g.untyped() == guard.untyped() => {
                let TermKind::Infix { op, lhs, rhs } = &bare_term(body).kind else {
                    return self.casts_under(proof.clone(), says, wanted);
                };
                let around = matches!(&bare_term(lhs).kind, TermKind::Infix { op: m, lhs: u, .. }
                    if m.symbol == "∈" && is_constant(u, "Set.univ"));
                if op.symbol != "∧" || !around || !meets(&their_body, rhs) {
                    return self.casts_under(proof.clone(), says, wanted);
                }
                let part = applied_to(at_x(), Printed::letter(&hx, LeanType::Prop));
                vec![
                    Tactic::Intro(vec![letter.clone(), hx.clone()]),
                    Tactic::Exact(super::super::expr::anonymous(vec![
                        Printed::constant(
                            "Filter.univ_mem",
                            super::super::doc::Source::Mathlib,
                            LeanType::Prop,
                        ),
                        part,
                    ])),
                ]
            }
            _ => return self.casts_under(proof.clone(), says, wanted),
        };
        Some(t::by_term(super::super::doc::Proof::By(Tactic::Seq(shown))))
    }

    /// The proof that the value an instantiation gives `letter` is in its
    /// domain, from where the checker found that supplied
    /// (`Instantiated::guards`), the membership as Lean writes it; None
    /// where no line supplies it, or the line says it otherwise than Lean
    /// asks.
    pub(super) fn value_guard(
        &self,
        recorded: &Instantiated,
        letter: &str,
    ) -> Option<Printed> {
        let g = recorded.guards.iter().find(|g| g.letter == letter)?;
        // The claim's own membership, whatever Lean writes it as.
        if let SuppliedBy::Bound { letter } = &g.by {
            return Some(bound_proof(letter));
        }
        let wanted = self.writer.formula(&g.written).built()?;
        self.supplied_proof(&g.by, &wanted, None).built()
    }

    /// Puts what ends a block, a part or a theorem at `depth`: its last
    /// step's proof in place of the step's `have`, where the step says what
    /// is owed as written and its `have` is the last line there; else the
    /// closing tactic, `exact` of that step's name among them.
    pub(super) fn close(
        &mut self,
        depth: usize,
        closing: Closing,
        page_line: usize,
        spot: Spot,
    ) {
        match closing {
            Closing::Closed => {}
            Closing::Last(name) => {
                if !self.last_proves_goal(depth, &name) {
                    self.push_at(
                        depth,
                        Tactic::Exact(super::super::tactics::hyp(&name)),
                        page_line,
                        spot,
                    );
                }
            }
            Closing::Tactic(t) => self.push_at(depth, *t, page_line, spot),
        }
    }

    /// Where the last line at `depth` is the `have` naming `name`, its proof
    /// put in its place as what proves the goal: a term by `exact`, a
    /// tactic as it is, and the lines of a block one level out. False where
    /// that line is anything else.
    pub(super) fn last_proves_goal(&mut self, depth: usize, name: &str) -> bool {
        let Some(k) = self.lines.iter().rposition(|l| l.depth <= depth) else {
            return false;
        };
        if self.lines[k].depth != depth {
            return false;
        }
        let Tactic::Have {
            name: had, proof, ..
        } = &self.lines[k].tactic
        else {
            return false;
        };
        if had != name {
            return false;
        }
        let origin = self.lines[k].origin.clone();
        let proof = (**proof).clone();
        match proof {
            super::super::doc::Proof::Term(t) => {
                self.lines[k].tactic = Tactic::Exact(t)
            }
            super::super::doc::Proof::By(t) => self.lines[k].tactic = t,
            super::super::doc::Proof::Block(ts) => {
                for l in &mut self.lines[k + 1..] {
                    l.depth -= 1;
                }
                let inline = ts.into_iter().map(|tactic| ProofLine {
                    depth,
                    tactic,
                    origin: origin.clone(),
                });
                self.lines.splice(k..=k, inline);
            }
        }
        true
    }

    /// A define's name given its value, `set b : G := a⁻¹ with hD1`: the
    /// letter of its type, and the line's equation, b = a⁻¹, by its label.
    pub(super) fn name_value(
        &mut self,
        d: usize,
        name: &str,
        ty: LetterType,
        value: Printed,
        body: Node,
        depth: usize,
    ) {
        let line = &self.thm.defines[d];
        let label = line_name(&line.label);
        let (at, page_label) = (line.line, line.label.clone());
        let letter_name = super::super::names::letter(name);
        let is_set = matches!(ty.lean_type(), super::super::doc::LeanType::Set(_));
        self.push_at(
            depth,
            Tactic::Set {
                name: letter_name.clone(),
                ty: ty.lean_type(),
                value,
                with: label.clone(),
            },
            at,
            Spot::Statement,
        );
        // A set the define names that is finite, U of a set-builder within
        // 𝒫{1, …, n}, is said finite at once, with the proof why it is gives
        // (`finite_proof`): Lean's tactics see the letter and not its value.
        let made_finite = match is_set {
            true => self.finite_proof(&body),
            false => None,
        };
        if let Some(made_finite) = made_finite {
            let says = Printed {
                kind: super::super::doc::TermKind::Field {
                    inner: Box::new(t::hyp(&letter_name)),
                    field: "Finite".to_string(),
                },
                ty: Some(super::super::doc::LeanType::Prop),
            };
            let proof = super::super::doc::Proof::By(Tactic::Seq(vec![
                t::call("rw", vec![t::rules(vec![t::hyp(&label)])]),
                Tactic::Exact(made_finite),
            ]));
            let finite = format!("{label}_finite");
            self.finite_defined.insert(name.to_string(), finite.clone());
            self.push_at(
                depth,
                Tactic::Have {
                    name: finite,
                    says,
                    proof: Box::new(proof),
                },
                at,
                Spot::Statement,
            );
        }
        self.writer.letters.insert(name.to_string(), ty);
        let letter = Node::name(body.sort.clone(), name);
        let equation = Node::of(EQUALS, Sort::of("formula"), vec![letter, body]);
        self.named.insert(page_label.clone(), vec![label.clone()]);
        self.trees
            .insert(page_label, vec![LineSentence::only(equation, label)]);
    }

    /// The fact a define of a kind says of its value, `gcd(t, w) ∈ ℕ` of
    /// `let n = gcd(t, w), a positive integer`, as Lean writes it, and its
    /// proof by the define's reason; `trivial` where Lean's types give it,
    /// `True` of `let x = a(j + 1), a real number`.
    pub(super) fn kind_shown(&self, d: usize) -> Route<KindShown> {
        let (fact, says) = match self.kind_fact(d) {
            Route::Built(f) => f,
            Route::Declined(why) => return Route::Declined(why),
        };
        let proof = match says.is_truth() {
            true => super::super::doc::Proof::Term(Printed::constant(
                "trivial",
                super::super::doc::Source::Core,
                super::super::doc::LeanType::Prop,
            )),
            false => match self.kind_proof(d, &fact) {
                Route::Built(p) => p,
                Route::Declined(why) => return Route::Declined(why),
            },
        };
        Route::Built(KindShown { fact, says, proof })
    }

    /// The fact a define of a kind says of its value, as the page and as
    /// Lean write it.
    pub(super) fn kind_fact(&self, d: usize) -> Route<(Node, Printed)> {
        let line = &self.thm.defines[d];
        let members = &self.sources.checked.grammar.members;
        let kinded = match line.kinded(&self.thm.path, members) {
            Ok(Some(k)) => k,
            Ok(None) => return Route::no("a define of a kind with no reason"),
            Err(p) => return Route::no(p.to_string()),
        };
        let fact = match self.tree(&kinded.shown.fact) {
            Route::Built(n) => n,
            Route::Declined(why) => return Route::Declined(why),
        };
        self.writer.formula(&fact).map(|says| (fact, says))
    }
}

/// Of a set of the parts of Y with j elements counted as some natural
/// number, `{S ∈ 𝒫 Y | ∃ m : ℕ, S.encard = m ∧ (m : ℤ) = j}`: Y, and j.
/// None for any other term.
fn parts_counted(p: &Printed) -> Option<(&Printed, &Printed)> {
    let TermKind::Bound {
        form: BoundForm::SetOfMember { set },
        letter,
        body,
        ..
    } = &p.kind
    else {
        return None;
    };
    let TermKind::Prefix {
        mark: PrefixMark::Powerset,
        inner: y,
    } = &set.kind
    else {
        return None;
    };
    let TermKind::Quantified {
        quant: Quant::Exists,
        letter: m,
        guard: Some(guard),
        body: said,
        ..
    } = &body.kind
    else {
        return None;
    };
    let (g_left, g_right) = super::orders::equation_sides(guard)?;
    let (b_left, j) = super::orders::equation_sides(said)?;
    let counts_letter = matches!(&g_left.kind, TermKind::Count { set, form: CountForm::Extended }
        if matches!(&set.kind, TermKind::Letter(l) if l == letter));
    let is_m = |t: &Printed| {
        let mut at = t;
        while let TermKind::Cast { inner, .. } = &at.kind {
            at = inner;
        }
        matches!(&at.kind, TermKind::Letter(l) if l == m)
    };
    (counts_letter && is_m(g_right) && is_m(b_left)).then_some((&**y, j))
}

/// Each Y of a set of the parts of Y with j elements a term counts as some
/// natural number (`parts_counted`), into `out`.
fn parts_counted_extended(p: &Printed, out: &mut Vec<Printed>) {
    if let Some((y, _)) = parts_counted(p) {
        if !out.iter().any(|o| o.untyped() == y.untyped()) {
            out.push(y.clone());
        }
    }
    for child in p.children() {
        parts_counted_extended(child, out);
    }
}

/// The term with each set of parts counted as some natural number
/// (`parts_counted`) counted in ℕ instead, `{S ∈ 𝒫 Y | (S.ncard : ℤ) = j}`:
/// what `builder_count_spelt` rewrites it to.
fn parts_counted_natural(p: &mut Printed) {
    let natural = parts_counted(p).map(|(_, j)| j.clone());
    if let (Some(j), TermKind::Bound { letter, body, .. }) = (natural, &mut p.kind) {
        let count = Printed::of(
            TermKind::Count {
                set: Box::new(Printed::letter(letter.clone(), LeanType::Num(Num::Int))),
                form: CountForm::Natural,
            },
            LeanType::Num(Num::Nat),
        );
        if let Route::Built(eq) = super::super::expr::relation_of(
            "=",
            Printed::cast(count, LeanType::Num(Num::Int)),
            j,
        ) {
            **body = eq;
        }
        return;
    }
    for child in p.children_mut() {
        parts_counted_natural(child);
    }
}
