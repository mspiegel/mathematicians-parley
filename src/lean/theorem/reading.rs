//! Proof methods: steps read: names, claims, what a step holds.

use std::collections::BTreeSet;
use std::{mem, ptr};

use super::super::algebra::{NotZero, NotZeroBy};
use super::super::doc::{LeanType, Location, Op, Quant, Tactic, TacticArg, TermKind};
use super::super::templates::Num;
use super::super::{doc, expr, tactics as t};
use super::*;
use crate::checker::record::{HeldByLines, NonzeroBy, Restated, Shown, ShownBy};
use crate::citing::{
    bounds, finite, reason_within, speaks_of_claim_letter, under_claim_binders,
    Introduced, OnceReason,
};
use crate::corpus::DefineParts;
use crate::formula::{page, Sort};
use crate::methods::membership;
use crate::notations::{
    CARDINALITY, DISJUNCTION, FUNCTION_TYPE, LOGICAL_NOT, MEMBERSHIP, PI, POWER,
    SQUARE_ROOT, SUBSET,
};
use crate::rules::WHOLE;
use crate::{corpus, matching, rules};

impl<'a> Proof<'a> {
    /// `intro a b` as a line of the proof at a depth of its blocks.
    pub(super) fn intro(
        &mut self,
        depth: usize,
        names: Vec<String>,
        page_line: usize,
        spot: &Spot,
    ) {
        self.push_at(depth, Tactic::Intro(names), page_line, spot.clone());
    }

    /// A tactic as a line of the proof at a depth of its blocks.
    pub(super) fn push_at(
        &mut self,
        depth: usize,
        tactic: Tactic,
        page_line: usize,
        spot: Spot,
    ) {
        self.lines.push(ProofLine {
            depth,
            tactic,
            origin: Origin {
                line: 0,
                page_line,
                spot,
            },
        });
    }

    pub(super) fn step_spot(step: &Step) -> Spot {
        Spot::Step(match step.number.number() {
            Some(n) => n.to_string(),
            None => "the theorem".to_string(),
        })
    }

    /// The steps, in order, each at the depth given.
    pub(super) fn steps(&mut self, indices: &[usize], depth: usize) -> Route<()> {
        for &i in indices {
            if let Route::Declined(d) = self.step(i, depth) {
                // Named by the innermost step it comes from: a block's
                // decline already names the step inside it.
                let reason = d.reason();
                if reason.starts_with("step ") {
                    return Route::Declined(d);
                }
                let number = &self.thm.steps[i].number;
                return Route::Declined(d.reworded(format!("step {number}: {reason}")));
            }
        }
        Route::Built(())
    }

    /// A step's claim: each sentence, read, with its Lean text; a
    /// membership Lean's types already give is left out, since nothing
    /// needs saying.
    pub(super) fn claim(&self, step: &Step) -> Route<Vec<(Node, Printed)>> {
        self.claimed(step).map(|c| {
            c.into_iter()
                .map(|(_, node, printed)| (node, printed))
                .collect()
        })
    }

    /// The sentences of a step's claim Lean has a line for, `claimed`, each
    /// by its place on the page and under its name of `names`, in order. A
    /// truth Lean's types give has no line, so its place is kept by none.
    pub(super) fn claim_sentences(
        claimed: &[(usize, Node, Printed)],
        names: &[String],
    ) -> Vec<LineSentence> {
        // Each with what its `have` states, the line's own statement.
        claimed
            .iter()
            .zip(names)
            .map(|((at, node, printed), name)| LineSentence {
                says: Some(printed.clone()),
                ..LineSentence::named(*at, node.clone(), name.clone())
            })
            .collect()
    }

    /// A claim's sentences as `claimed` gives them, without their places.
    pub(super) fn without_places(
        claimed: &[(usize, Node, Printed)],
    ) -> Vec<(Node, Printed)> {
        claimed
            .iter()
            .map(|(_, node, printed)| (node.clone(), printed.clone()))
            .collect()
    }

    /// `claim`, each sentence with its place among the page's: a sentence
    /// Lean's types already give, √x ∈ ℝ, is left out, and a citation is
    /// read at the place the checker counted.
    pub(super) fn claimed(&self, step: &Step) -> Route<Vec<(usize, Node, Printed)>> {
        self.claimed_all(step).map(|all| {
            all.into_iter()
                .filter(|(_, _, printed)| !printed.is_truth())
                .collect()
        })
    }

    /// Every sentence of a step's claim with its place and its Lean text,
    /// those Lean's types already give among them, as `True`.
    pub(super) fn claimed_all(
        &self,
        step: &Step,
    ) -> Route<Vec<(usize, Node, Printed)>> {
        let mut out = Vec::new();
        let sentences: Vec<Option<&Node>> = step
            .claim
            .sentences()
            .iter()
            .map(|s| self.rec.page.get(s))
            .collect();
        for (at, s) in step.claim.sentences().into_iter().enumerate() {
            let Some(node) = self.rec.page.get(&s) else {
                return Route::no(format!(
                    "{}, which the checker did not read",
                    s.text()
                ));
            };
            // A set the claim's other sentences say is finite counts as one
            // here, W of "W is finite and |W| ≥ k", by the one reading of
            // what lines make finite (`citing::finite::finite_sets`); and one
            // the sentence says of itself, a count given as a number at least
            // 1, by the step's bounds as the checker recorded them
            // (`CheckedTheorem::bounds`). A count that may be 0 does not
            // vouch for itself.
            let others: Vec<&Node> = sentences
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != at)
                .filter_map(|(_, o)| *o)
                .collect();
            let positive =
                |n: &Node| bounds::least(&self.writer, n).is_some_and(|l| l >= 1);
            let mut writer = self.writer.with_letters(self.writer.letters.clone());
            let by_others = finite::finite_sets(others, &positive);
            let by_itself = finite::finite_sets_vouched([node], &positive);
            for (set, why) in by_others.into_iter().chain(by_itself) {
                writer.finite.entry(set).or_insert(why);
            }
            // A claim of numerals alone is written in the type of the lines
            // it is reached from, where any are cited.
            let printed = if node.names().is_empty() {
                let mut floor = super::super::templates::Num::Int;
                for c in self.cited_parts(&step.just.refs) {
                    for side in
                        c.node.children.iter().filter(|s| self.writer.is_number(s))
                    {
                        if let Route::Built(n) = self.writer.carrier(side) {
                            floor = floor.max(n);
                        }
                    }
                }
                // ℂ has no order: a line of points or complex numbers, P = R
                // of a contradiction's supposition, gives an order of
                // numerals the widest type that has one.
                if node.notation() == ORDER {
                    floor = floor.min(super::super::templates::Num::Real);
                }
                writer.closed_formula(node, floor)
            } else {
                writer.formula(node)
            };
            let printed = match printed {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            out.push((at, node.clone(), printed));
        }
        Route::Built(out)
    }

    /// The Lean names of a step's sentences: `s2` for one, `s2a`, `s2b` for
    /// several.
    pub(super) fn names_of(step: &Step, count: usize) -> Vec<String> {
        let base = match step.number.number() {
            Some(n) => line_name(&n.to_string()),
            None => "sThm".to_string(),
        };
        if count == 1 {
            return vec![base];
        }
        (0..count)
            .map(|i| format!("{base}{}", part_suffix(i)))
            .collect()
    }

    /// The letters a step's claim introduces, `k ∈ ℤ`, added to those in
    /// scope. A claim of a letter already in scope introduces nothing: it
    /// says something of the letter, a fact a later step may use.
    pub(super) fn introduce(&mut self, step: &Step) {
        for s in step.claim.sentences() {
            if let Some(node) = self.rec.page.get(&s) {
                let letter = introduces(node)
                    .map(|(l, _)| l)
                    .or_else(|| super::super::statement::range_letter(node));
                let known = letter
                    .is_some_and(|l| self.writer.letters.contains_key(l.as_str()));
                if known {
                    continue;
                }
                if let Some((letter, system)) = introduces(node) {
                    self.writer.introduce(&letter, system);
                } else if let Some(letter) = super::super::statement::range_letter(node)
                {
                    // In ℕ or ℕ₀ where the range starts at 1 or 0, as the
                    // page says once (`citing::range_system`).
                    let system = match node.children.get(1) {
                        Some(range) => super::super::expr::range_letter_system(range),
                        None => super::super::expr::System::Type(
                            super::super::templates::Num::Int,
                        ),
                    };
                    self.writer.introduce(&letter, system);
                } else if let Some((letter, members)) = self.set_member_said(node) {
                    self.writer.letters.insert(letter, members.letter());
                } else if let Some((letter, members)) = self.part_said(node) {
                    self.writer.letters.insert(letter, LetterType::Set(members));
                } else if let Some((letter, ty)) = self.function_said(node) {
                    self.writer.letters.insert(letter, ty);
                } else if let Some(letter) =
                    super::super::statement::introduces_polynomial(node)
                {
                    self.writer.letters.insert(
                        letter,
                        LetterType::Function {
                            from: super::super::templates::Num::Complex,
                            to: super::super::templates::Num::Complex,
                        },
                    );
                }
            }
        }
    }

    /// The letter a line says is a function between sets, `g : {1, …, j} →
    /// ℕ`, where the letter is new, with the type `Writer::function_between`
    /// gives it.
    pub(super) fn function_said(&self, node: &Node) -> Option<(String, LetterType)> {
        let [g, from, to] = node.children.as_slice() else {
            return None;
        };
        let new = node.notation() == FUNCTION_TYPE
            && g.is_name()
            && !self.writer.letters.contains_key(g.text.as_str());
        new.then(|| self.writer.function_between(from, to))
            .flatten()
            .map(|ty| (g.text.to_string(), ty))
    }

    /// The letter a line says is a part of a set, `W ⊆ X`, where the letter
    /// is new and the writer has a type for X's members: a set of those,
    /// numbers among them, T ⊆ {1, …, N} a set of integers.
    pub(super) fn part_said(
        &self,
        node: &Node,
    ) -> Option<(String, super::super::expr::Members)> {
        let [w, set] = node.children.as_slice() else {
            return None;
        };
        let new = node.notation() == SUBSET
            && w.is_name()
            && !self.writer.letters.contains_key(w.text.as_str());
        new.then(|| self.writer.set_members(set))
            .flatten()
            .map(|m| (w.text.to_string(), m))
    }

    /// The letter a line says is a member of a set, `x ∈ A`, where the
    /// letter is new and the writer has a type for A's members.
    pub(super) fn set_member_said(
        &self,
        node: &Node,
    ) -> Option<(String, super::super::expr::Members)> {
        let [x, set] = node.children.as_slice() else {
            return None;
        };
        let new = node.notation() == MEMBERSHIP
            && x.is_name()
            && !self.writer.letters.contains_key(x.text.as_str());
        new.then(|| self.writer.members_of(set))
            .flatten()
            .map(|m| (x.text.to_string(), m))
    }

    pub(super) fn step(&mut self, i: usize, depth: usize) -> Route<()> {
        let step = &self.thm.steps[i];
        // A function the header lets by its value is its equation for every
        // x (`header_function`), which a step citing the define or
        // substituting from it puts in, and a calculation's rows citing it;
        // a step of another method citing it, an algebra from D1, does not.
        // A membership needs no value of it: q(x) ∈ ℝ of q into ℝ is what
        // Lean's type of q says. An order step adds its equation at the
        // argument it applies it to, a citation of an item or an algebra
        // rewrites the goal by it, and a restated limit is the line's from
        // where the domain starts (`applied_domains`).
        let through = !matches!(
            step.just.head,
            Head::Define
                | Head::Item { .. }
                | Head::Method(
                    Method::Substitute
                        | Method::Calculation
                        | Method::Membership
                        | Method::Transitivity
                        | Method::Inequalities
                        | Method::Algebra
                        | Method::Restate
                )
        );
        if through
            && step
                .just
                .refs
                .iter()
                .any(|r| self.header_function_named(r).is_some())
        {
            return Route::no(
                "a step cites a function the header lets through a method, which its equation for every x is not put in by",
            );
        }
        // A square root of y − 3 is Mathlib's real one once a line in scope
        // says y − 3 ≥ 0 (`Writer::principal_is_real`), as the check read
        // the lines in scope (`CheckedTheorem::bounds`).
        if let Some(said) = self.rec.bounds.get(i) {
            self.writer.bounds = said.clone();
        }
        // A set a line in scope says is finite, W of a step "W is finite"
        // above, is counted as a natural number from there on, as one the
        // hypotheses make finite is (`CheckedTheorem::finite_at`).
        self.writer.finite = self.rec.said_finite.sets.clone();
        // Of a set both give a reason for, the step's own, from the lines in
        // scope there: R ⊆ X of a finite X, where the theorem has only that R
        // is bound over sets of finite sets, which names no line to prove it
        // from.
        if let Some(said) = self.rec.finite_at.get(i) {
            for (set, why) in said {
                self.writer.finite.insert(set.clone(), why.clone());
            }
        }
        // The defines written above this step in its block, where the
        // checker opens them.
        let due: Vec<usize> = (0..self.thm.defines.len())
            .filter(|&d| {
                !self.defined.contains(&d)
                    && self.thm.defines[d].line < step.line
                    && self.thm.defines[d].line > self.thm.conclusion_line
                    && self.rec.defines.get(d).copied().flatten() == self.rec.places[i]
            })
            .collect();
        for d in due {
            if let Route::Declined(why) = self.define(d, depth) {
                return Route::Declined(why);
            }
        }
        let spot = Self::step_spot(step);
        self.push_at(
            depth,
            Tactic::Comment(format!("{}. {}", step.number, step.just.text.trim())),
            step.line,
            spot.clone(),
        );
        // The claim's first sentence as the page reads it, whose leading
        // "for all" binds letters its requires lines may speak of.
        let claimed = step
            .claim
            .sentences()
            .first()
            .and_then(|s| self.rec.page.get(s))
            .cloned();
        // A requires line is the step's, and the citation on one reads the
        // step's requires lines above it by the step's names.
        self.step_now.set(Some(i));
        let mut above: Vec<Node> = Vec::new();
        for (k, r) in step.requires.iter().enumerate() {
            let node = match self.tree(&r.fact) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            // What the requires lines above make finite, "X is finite" of
            // the set this one counts, it counts as a natural number, as the
            // check reads them (`Step::requires_above`).
            let positive =
                |n: &Node| bounds::least(&self.writer, n).is_some_and(|l| l >= 1);
            let made: Vec<_> = finite::finite_sets(above.iter(), &positive)
                .into_iter()
                .collect();
            for (set, why) in made {
                self.writer.finite.entry(set).or_insert(why);
            }
            above.push(node.clone());
            // A requires line of a letter the claim says "for all" of, x²
            // ≥ 0 of every x ∈ [0, 1], is said under the claim's binders and
            // proved with its letters given.
            let under = claimed
                .as_ref()
                .filter(|c| speaks_of_claim_letter(c, &node))
                .map(|c| under_claim_binders(c, &node));
            let stated = under.clone().unwrap_or_else(|| node.clone());
            let fact = match self.writer.formula(&stated) {
                Route::Built(f) => f,
                Route::Declined(d) => return Route::Declined(d),
            };
            // A fact Lean's types give, said under the claim's "for all"s
            // or not, `∀ x ∈ Set.Icc a b, True` of f(x) ∈ ℝ.
            if under_for_alls(&fact).is_truth() {
                continue;
            }
            let Ok(just) = &r.by else {
                return Route::no("a requires line whose reason does not read");
            };
            let reason = Reason {
                just,
                cited: self.rec.cited_requires.get(&r.line),
            };
            *self.named_now.borrow_mut() = Some(just.refs.iter().cloned().collect());
            *self.held_now.borrow_mut() = self.held_at(just.line);
            let proof = match &under {
                // Its whole numbers named from the lines its own reason
                // cites, p^(a′ − a) ∈ ℤ from 3.3.
                None => {
                    let facts = self.cited_parts(&just.refs);
                    self.proof_named_from(reason, 0, &node, i, &facts)
                }
                // A line that says it of every member, the claim's "for all"
                // and all (`Restated::UnderClaim`): that line; or a part of
                // its "for all"'s body, taken at each member, `(h x).1`.
                Some(wrapped)
                    if matches!(
                        self.rec.restated.get(&just.line),
                        Some(Restated::UnderClaim { .. })
                    ) =>
                {
                    let part = match self.rec.restated.get(&just.line) {
                        Some(Restated::UnderClaim { part, .. }) => *part,
                        _ => None,
                    };
                    match part {
                        None => match self.restated_proof(just.line, wrapped) {
                            Some(p) => Route::Built(p),
                            None => Route::no(
                                "a requires line its line says otherwise for all",
                            ),
                        },
                        Some(part) => self.body_part_proof(just.line, wrapped, part),
                    }
                }
                Some(wrapped) => {
                    let (intros, _, inner) = self.peel(wrapped);
                    let outer = mem::replace(&mut self.writer, inner);
                    *self.intros_now.borrow_mut() = intros.clone();
                    let proof = self.proof_of(reason, 0, &node);
                    self.intros_now.borrow_mut().clear();
                    self.writer = outer;
                    proof.map(|p| after_intros(&intros, p))
                }
            };
            let proof = match proof {
                Route::Built(t) => t,
                Route::Declined(d) => return Route::Declined(d),
            };
            let name = format!("r{}_{}", step.line, k + 1);
            // A requires line is a line in scope from here, as a step's
            // claim is: what names an integer it says one is. It says what
            // its `have` states, whatever writer later reads it: under the
            // claim's binders where it is said so, `∀ x ∈ ℚ, denom(x) ∈ ℕ`,
            // which says nothing of a later x.
            let mut line = LineSentence::only(stated.clone(), name.clone());
            line.says = Some(fact.clone());
            self.trees.insert(name.clone(), vec![line]);
            self.push_at(
                depth,
                Tactic::Have {
                    name,
                    says: fact.clone(),
                    proof: Box::new(proof),
                },
                r.line,
                spot.clone(),
            );
        }
        let mut named: BTreeSet<String> =
            step_cited_refs(step, &self.thm.path).into_iter().collect();
        named.extend(
            (0..step.requires.len()).map(|k| format!("r{}_{}", step.line, k + 1)),
        );
        *self.named_now.borrow_mut() = Some(named);
        *self.held_now.borrow_mut() = self.held_at(step.just.line);
        self.step_now.set(Some(i));
        if let Head::Method(Method::Obtain) = step.just.head {
            return self.obtain(i, depth);
        }
        self.introduce(step);
        let claimed = match self.claimed(step) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let claim = Self::without_places(&claimed);
        let names = Self::names_of(step, claim.len());
        if let Some(n) = step.number.number() {
            self.named.insert(n.to_string(), names.clone());
            let said = Self::claim_sentences(&claimed, &names);
            self.store(n.to_string(), said);
        }
        if let Head::Method(m) = step.just.head {
            // A calculation's lines are its proof, written as Lean's calc;
            // every other block's steps stand in it.
            if m.takes_block() && m != Method::Calculation {
                // The lines inside a block are out of scope after it, and
                // the claim the block proves is no line in scope inside it.
                let own = step.number.number().map(|n| n.to_string());
                let claimed = own.as_ref().and_then(|n| self.trees.shift_remove(n));
                let visible: BTreeSet<String> = self.trees.keys().cloned().collect();
                let written = self.block(i, m, &claim, &names, depth);
                self.trees.retain(|k, _| visible.contains(k));
                self.narrowings_ended(depth);
                if let (Some(n), Some(said)) = (own, claimed) {
                    self.store(n, said);
                }
                if let Route::Built(()) = written {
                    let said: Vec<(String, Printed)> = names
                        .iter()
                        .cloned()
                        .zip(claim.iter().map(|(_, prop)| prop.clone()))
                        .collect();
                    self.narrow_at_step(i, &said, step.line, depth);
                }
                return written;
            }
        }
        let reason = Reason {
            just: &step.just,
            cited: self.rec.cited[i].as_ref(),
        };
        let places: Vec<usize> = match self.claimed(step) {
            Route::Built(c) => c.into_iter().map(|(at, _, _)| at).collect(),
            Route::Declined(d) => return Route::Declined(d),
        };
        for (k, (node, prop)) in claim.iter().enumerate() {
            // A citation for a claim said "for all k ∈ …" the checker read at
            // a member (`CheckedTheorem::at_member`): the item cited at that
            // k, given as a method takes it (`peel`). An item that says the
            // "for all" itself is cited whole.
            let cites_for_all = matches!(reason.just.head, Head::Item { .. })
                && self.rec.at_member.contains_key(&reason.just.line);
            let proof = if cites_for_all {
                let (intros, body, inner) = self.peel(node);
                let outer = mem::replace(&mut self.writer, inner);
                let proof = self.proof_of(reason, places[k], body);
                self.writer = outer;
                proof.map(|p| match intros.is_empty() {
                    true => p,
                    false => after_intros(&intros, p),
                })
            } else {
                self.proof_with_named(reason, places[k], node, i)
            };
            let proof = match proof {
                Route::Built(t) => t,
                Route::Declined(d) => return Route::Declined(d),
            };
            // An algebra, inequalities or transitivity reason reads |AB| and
            // |BA| of its lines as one term; Lean's two are not.
            let proof = match step.just.head {
                Head::Method(
                    Method::Algebra | Method::Inequalities | Method::Transitivity,
                ) => {
                    self.with_commuted(step.just.line, &self.step_facts(i), prop, proof)
                }
                _ => proof,
            };
            self.push_at(
                depth,
                Tactic::Have {
                    name: names[k].clone(),
                    says: prop.clone(),
                    proof: Box::new(proof),
                },
                step.line,
                spot.clone(),
            );
        }
        // A define's function whose values this step puts among narrower
        // numbers, declared of those from here (`narrow_at_step`).
        let said: Vec<(String, Printed)> = names
            .iter()
            .cloned()
            .zip(claim.iter().map(|(_, prop)| prop.clone()))
            .collect();
        self.narrow_at_step(i, &said, step.line, depth);
        if step.impossible {
            // A line of roots or of π, ln, exp, sin or cos, √2 − 1 = 0, is
            // shown false by real arithmetic; any other by `norm_num`.
            let real = claim.iter().any(|(node, _)| {
                node.walk().iter().any(|n| {
                    matches!(n.notation(), SQUARE_ROOT | PI)
                        || n.children.first().is_some_and(|f| {
                            matches!(&*f.text, "cos" | "sin" | "exp" | "ln" | "tan")
                        })
                })
            });
            if let (Some(last), Some((node, prop))) = (names.last(), claim.last()) {
                // Real arithmetic shows the line false as a fact of its own,
                // `hn : ¬ line`; `norm_num` any other line.
                let refuted = match real {
                    true => {
                        let proof = match super::super::reals::real_refuted(
                            &self.writer,
                            self.sources.targets,
                            node,
                        ) {
                            Route::Built(p) => p,
                            Route::Declined(d) => return Route::Declined(d),
                        };
                        let not = Printed {
                            kind: super::super::doc::TermKind::Not(Box::new(
                                t::bracket(prop.clone()),
                            )),
                            ty: Some(super::super::doc::LeanType::Prop),
                        };
                        self.push_at(
                            depth,
                            Tactic::Have {
                                name: "hn".to_string(),
                                says: not,
                                proof: Box::new(proof),
                            },
                            step.line,
                            spot.clone(),
                        );
                        t::hyp("hn")
                    }
                    false => super::super::tactics::by_term(
                        super::super::doc::Proof::By(t::call("norm_num", vec![])),
                    ),
                };
                let absurd = Printed::applied(
                    "absurd",
                    super::super::doc::Source::Core,
                    vec![t::hyp(last), refuted],
                    super::super::doc::LeanType::Prop,
                );
                self.push_at(depth, Tactic::Exact(absurd), step.line, spot.clone());
            }
        }
        Route::Built(())
    }

    /// A sentence of the page as the checker read it.
    pub(super) fn tree(&self, written: &Written) -> Route<Node> {
        match written
            .sentences()
            .first()
            .and_then(|s| self.rec.page.get(s))
        {
            Some(node) => Route::Built(node.clone()),
            None => Route::no(format!(
                "{}, which the checker did not read",
                written.text()
            )),
        }
    }

    /// The widest fixed type a hole of the claim takes where what fills it
    /// holds one of `values`, ℝ of ⌊A/B⌋ cited with x := A/B, which a term
    /// in that hole is computed in; ℤ where there is none. A hole holding
    /// none of them, F(p/q) of |F(p/q)| cited with y := q^N·|F(p/q)|, is
    /// computed apart from them.
    pub(super) fn held_in(
        &self,
        claim: &Node,
        values: &[&Node],
    ) -> super::super::templates::Num {
        let holds = |filled: &Node| {
            filled
                .walk()
                .iter()
                .any(|m| values.iter().any(|v| m.spelt_alike(v)))
        };
        claim
            .walk()
            .iter()
            .filter_map(|n| {
                let t = self.writer.template(n).built()?;
                Some(t.holes.clone().into_iter().zip(n.children.clone()))
            })
            .flatten()
            .filter_map(|(slot, filled)| match slot {
                super::super::templates::Slot::Fixed(n) if holds(&filled) => Some(n),
                _ => None,
            })
            .fold(super::super::templates::Num::Int, Ord::max)
    }

    /// The proof of sentence `k` of step `i`'s claim, where the claim puts
    /// a term Lean does not compute as a whole number in a slot for one,
    /// "2^p − 1 divides 2^(p − 1)·2", written `∃ m : ℤ, (m : ℚ) = … ∧ …`
    /// (`Writer::slot_witness`): the whole number it is, named from the
    /// lines the step names as Metamath proves its membership from them
    /// (`name_wholes`), given as the witness, and the reason proving the
    /// claim of it. Of any other claim, `proof_of`.
    pub(super) fn proof_with_named(
        &mut self,
        reason: Reason,
        k: usize,
        node: &Node,
        i: usize,
    ) -> Route<super::super::doc::Proof> {
        let facts = self.step_facts(i);
        self.proof_named_from(reason, k, node, i, &facts)
    }

    /// Whether the checker found the reason on `line` to read a notation
    /// whose parts stand in no order written in more than one order among
    /// its claim and lines (`CheckedTheorem::commuted_by_lines`), one the
    /// writer turns.
    pub(super) fn commuted_here(&self, line: usize) -> bool {
        self.rec
            .commuted_by_lines
            .get(&line)
            .is_some_and(|ns| ns.iter().any(|n| super::terms::turns_notation(n)))
    }

    /// The proof of the reason on `line`, of a step or a calculation's row,
    /// with its claim `goal` and the lines it cites `cited`, where the
    /// reason reads |AB| and |BA| of its lines as one term
    /// (`commuted_here`): the goal and each line it cites taken to one order
    /// of the parts of such notations, each by exact instances of the
    /// notation's swap lemmas (`turning_rewrites`); the proof, whose
    /// coefficients the algebra writes in that order too, follows.
    pub(super) fn with_commuted(
        &self,
        line: usize,
        cited: &[super::super::algebra::Cited],
        goal: &Printed,
        proof: super::super::doc::Proof,
    ) -> super::super::doc::Proof {
        if !self.commuted_here(line) {
            return proof;
        }
        let rewrite = |rewrites: Vec<Printed>, at: Option<String>| {
            let mut args = vec![TacticArg::Rules(
                rewrites.into_iter().map(t::forwards).collect(),
            )];
            args.extend(at.map(|name| TacticArg::At(vec![Location::Hypothesis(name)])));
            t::call("rw", args)
        };
        let mut steps: Vec<Tactic> = Vec::new();
        for cited in cited {
            let (Some(says), name) = (&cited.says, cited.proof.text()) else {
                continue;
            };
            // A line that is a hypothesis by its name; a part of one, `H3.1`,
            // is not rewritten in place.
            if name.contains(|c: char| !(c.is_alphanumeric() || c == '_')) {
                continue;
            }
            let rewrites = super::terms::turning_rewrites(says, &says.in_one_order());
            if !rewrites.is_empty() {
                steps.push(rewrite(rewrites, Some(name)));
            }
        }
        // A define's equation, which the proof may write out (`simp only
        // [hD1]`), taken to the same order, so that what it brings in is
        // in it too.
        for (name, value) in self.set_values() {
            let says = Printed::infix(
                super::super::doc::Op::EQUALS,
                Printed::letter(
                    name.clone(),
                    value
                        .value
                        .ty
                        .clone()
                        .unwrap_or(super::super::doc::LeanType::Prop),
                ),
                value.value.clone(),
                super::super::doc::LeanType::Prop,
            );
            let rewrites = super::terms::turning_rewrites(&says, &says.in_one_order());
            if !rewrites.is_empty() {
                steps.push(rewrite(rewrites, Some(value.equation.clone())));
            }
        }
        let ordered = goal.in_one_order();
        let rewrites = super::terms::turning_rewrites(goal, &ordered);
        if !rewrites.is_empty() {
            steps.push(rewrite(rewrites, None));
            // An equation whose sides are one term once in that order,
            // `|QR|` beside `|RQ|`: `rw` closes it by reflexivity.
            if let super::super::doc::TermKind::Infix { op, lhs, rhs } = &ordered.kind {
                if op.symbol == "=" && lhs.text() == rhs.text() {
                    return doc::Proof::Block(steps);
                }
            }
        }
        if steps.is_empty() {
            return proof;
        }
        steps.push(Tactic::Exact(t::bracket(t::by_term(proof))));
        doc::Proof::Block(steps)
    }

    /// `proof_with_named`, its numbers named from `facts`: a step's lines,
    /// or those a requires line's own reason cites.
    pub(super) fn proof_named_from(
        &mut self,
        reason: Reason,
        k: usize,
        node: &Node,
        i: usize,
        facts: &[super::super::algebra::Cited],
    ) -> Route<super::super::doc::Proof> {
        let Some(letters) = self.rec.introduced.get(i).cloned() else {
            return Route::no("a step the checker's record has no letters for");
        };
        // A claim that a term Lean does not compute as a whole number is
        // one, p^(a′ − a) ∈ ℕ, written `∃ m : ℤ, 0 < m ∧ (m : ℚ) = …`
        // (`Writer::in_system`): the number the step's lines name is the
        // witness, and of ℕ or ℕ₀ its order the step's reason, said of it.
        if let Some((term, whole, ordered)) = self.wide_member(node) {
            let mut atoms = Vec::new();
            // Where the step's lines name no such number, the membership is
            // what the lines in scope give (`member_by_integers`).
            if self
                .name_wholes(&term, &letters, whole, facts, &mut atoms)
                .built()
                .is_none()
            {
                // Beside an equation, as the check found it.
                if !ordered {
                    let line = reason.just.line;
                    if let Some(p) =
                        self.member_beside(line, &term, node, &letters, facts)
                    {
                        return Route::Built(p);
                    }
                }
                return self.proof_of(reason, k, node);
            }
            let mut inner = self.writer.with_letters(self.writer.letters.clone());
            inner.integers.extend(atoms.iter().map(|a| a.said.clone()));
            let int = match inner.number_fixed(&term, super::super::templates::Num::Int)
            {
                Route::Built(p) => whole_term(p),
                Route::Declined(d) => return Route::Declined(d),
            };
            let specs: Vec<Printed> = atoms.iter().map(|a| spec_of(&a.said)).collect();
            let equal = specs_equal_of(&term, &specs);
            let mut haves: Vec<Tactic> = atoms.iter().map(|a| a.have.clone()).collect();
            if !ordered {
                let shown =
                    Tactic::Exact(super::super::expr::anonymous(vec![int, equal]));
                return Route::Built(haves_then(haves, doc::Proof::By(shown)));
            }
            let outer = mem::replace(&mut self.writer, inner);
            let proof = self.proof_of(reason, k, node);
            self.writer = outer;
            let proof = match proof {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            haves.push(refine(vec![
                int,
                Printed::of(
                    super::super::doc::TermKind::Open,
                    super::super::doc::LeanType::Prop,
                ),
                equal,
            ]));
            haves.push(tactic_of(&proof));
            return Route::Built(doc::Proof::Block(haves));
        }
        // A count in ℕ∞ of a set not known finite is no whole number a line
        // names: the claim says it is some natural number, `∃ m : ℕ,
        // S.encard = m ∧ …`, and is proved as it states it.
        let claimed: Vec<WideTerm> = self
            .leaf_wides(node)
            .into_iter()
            .filter(|w| {
                !(w.term.notation() == CARDINALITY && self.writer.counts(&w.term))
            })
            .collect();
        // A term the cited item itself puts in a whole-number slot,
        // gcd(a/k, b/k) of gcd(a/gcd(a, b), b/gcd(a, b)) = 1, is one its
        // statement names as a whole number: the item's witness is the
        // claim's, and no line need name it.
        if !claimed.is_empty() && self.item_states_whole(reason, k) {
            return self.proof_of(reason, k, node);
        }
        // A claim joined by "or" or "and" names each part's such terms as a
        // claim of that part alone would.
        let parted = match claimed.is_empty() {
            false => Vec::new(),
            true => self.wide_in_parts(node),
        };
        // The lines the step cites that say something of a whole number a
        // term is, `∃ m : ℤ, (m : ℚ) = 2 ^ (p − 1) ∧ …`, or that none is,
        // `¬ ∃ m : ℤ, …`, by the name they stand under, which a
        // restatement of them takes.
        let cited: Vec<CitedWitness> = self
            .cited_parts(&step_cited_refs(&self.thm.steps[i], &self.thm.path))
            .into_iter()
            .filter(|c| matches!(c.proof.kind, super::super::doc::TermKind::Letter(_)))
            .filter_map(|c| {
                let (said, negated) =
                    match (c.node.notation(), c.node.children.as_slice()) {
                        (LOGICAL_NOT, [inner]) => (inner, true),
                        _ => (&c.node, false),
                    };
                let terms = self.leaf_wides(said);
                (!terms.is_empty()).then(|| CitedWitness {
                    name: c.proof.text(),
                    terms,
                    negated,
                })
            })
            .collect();
        if claimed.is_empty() && cited.is_empty() && parted.is_empty() {
            return self.proof_of(reason, k, node);
        }
        let mut atoms = Vec::new();
        for w in claimed.iter().chain(&parted) {
            if let Route::Declined(d) =
                self.name_wholes(&w.term, &letters, w.whole, facts, &mut atoms)
            {
                return Route::Declined(d);
            }
        }
        // A cited line with a term no line the step names makes whole is
        // left as it is: the step may not need it so.
        let cited: Vec<_> = cited
            .into_iter()
            .filter(|c| {
                let before = atoms.len();
                let named = c.terms.iter().all(|w| {
                    self.name_wholes(&w.term, &letters, w.whole, facts, &mut atoms)
                        .built()
                        .is_some()
                });
                if !named {
                    atoms.truncate(before);
                }
                named
            })
            .collect();
        let mut inner = self.writer.with_letters(self.writer.letters.clone());
        inner.integers.extend(atoms.iter().map(|a| a.said.clone()));
        // The step proves its claim of the numbers it names only where the
        // claim as stated is reached from that: a term the claim gives a
        // witness, each part's of an "or" or an "and". A claim that holds
        // such a term inside a "there is" or another connective of its own,
        // "there is k ∈ ℕ with gcd(a/k, b/k) = 1", states it otherwise than
        // the numbers would write it, and is proved as stated, of its lines
        // as they are.
        if claimed.is_empty() && parted.is_empty() {
            let stated = self.writer.formula(node).built().map(|p| p.untyped());
            let named = inner.formula(node).built().map(|p| p.untyped());
            if stated != named {
                return self.proof_of(reason, k, node);
            }
        }
        // Each named number's equation with its term: the one a step proves
        // of a power written out, the line's witness's for one it gives.
        let specs: Vec<Printed> = atoms.iter().map(|a| spec_of(&a.said)).collect();
        let equal = specs_equal(&specs);
        let mut haves: Vec<Tactic> = atoms.iter().map(|a| a.have.clone()).collect();
        // Each such cited line, said of the number the step names, so within
        // the step's proof alone: its restatement is a `have` there.
        let mut restated: Vec<RestatedInStep> = Vec::new();
        for c in &cited {
            // The line at each term's number in turn, the outermost first:
            // what is left of the line at one is the witness form of the
            // next.
            let mut at = super::super::tactics::hyp(&c.name);
            for w in &c.terms {
                let int = match inner.number_fixed(&w.term, w.whole) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let lemma = match (w.whole, c.negated) {
                    (super::super::templates::Num::Nat, false) => {
                        "parley_witness_at_nat"
                    }
                    (super::super::templates::Num::Nat, true) => {
                        "parley_witness_not_at_nat"
                    }
                    (_, false) => "parley_witness_at",
                    (_, true) => "parley_witness_not_at",
                };
                at = Printed {
                    kind: super::super::doc::TermKind::App {
                        head: Box::new(super::super::tactics::bridge_lemma(
                            lemma,
                            BridgeModule::PowerTactics,
                        )),
                        args: [whole_term(at), int, equal.clone()]
                            .into_iter()
                            .map(super::super::doc::Arg::Explicit)
                            .collect(),
                        explicit: false,
                    },
                    ty: Some(super::super::doc::LeanType::Prop),
                };
            }
            haves.push(Tactic::Name {
                name: c.name.clone(),
                term: at,
            });
            // The line, restated under its own name, says from here on what
            // it says of the numbers it was restated through, written of the
            // numbers the step names in those terms, 2^(p − 1) and 2^p − 1 of
            // their product, and of no other the step names:
            // `parley_witness_at` puts those alone (`store`).
            let parts: Vec<String> = c
                .terms
                .iter()
                .flat_map(|w| w.term.walk())
                .map(|n| self.writer.grammar.print(&n))
                .collect();
            let mut through = self.writer.with_letters(self.writer.letters.clone());
            through.integers.extend(
                atoms
                    .iter()
                    .filter(|a| parts.contains(&a.said.term))
                    .map(|a| a.said.clone()),
            );
            for (line, sentences) in self.trees.iter_mut() {
                for (place, s) in sentences.iter_mut().enumerate() {
                    if s.name.as_deref() == Some(c.name.as_str()) {
                        let says = through.formula(&s.node).built();
                        restated.push(RestatedInStep {
                            line: line.clone(),
                            place,
                            before: mem::replace(&mut s.says, says),
                        });
                    }
                }
            }
        }
        // Each other line the step cites is put in terms of the numbers the
        // step names as well, and cast down to them: 5.7.7's f(a) =
        // (a^(p − 2)) mod p, of reals, as f a = c % p of integers, which a
        // substitution then puts into the restated 5.7.6.
        let mut terms: Vec<Node> = Vec::new();
        for w in claimed
            .iter()
            .chain(&parted)
            .chain(cited.iter().flat_map(|c| &c.terms))
        {
            terms.extend(w.term.walk());
        }
        let mut rules = Vec::new();
        for a in atoms.iter().filter(|a| a.said.value.is_none()) {
            let Some(term) = terms
                .iter()
                .find(|n| self.writer.grammar.print(n) == a.said.term)
            else {
                continue;
            };
            let line = SaidLine {
                proof: a.said.proof.clone(),
                beside: Beside::Nothing,
            };
            if let Some(rule) = self.spec_at_real(&line, line.equation(), term) {
                rules.push(NumberRule {
                    term: a.said.term.clone(),
                    lean: self
                        .writer
                        .number_fixed(term, super::super::templates::Num::Real)
                        .built(),
                    rule: super::super::tactics::backwards(rule),
                });
            }
        }
        let witnesses: Vec<String> = cited.iter().map(|c| c.name.clone()).collect();
        let refs: Vec<&String> = self.thm.steps[i].just.refs.iter().collect();
        haves.extend(self.put_numbers_in_lines(&refs, &witnesses, &rules));
        // Each term's named number, the witness the claim gives it.
        let mut ints = Vec::new();
        for w in &claimed {
            match inner.number_fixed(&w.term, w.whole) {
                Route::Built(p) => ints.push(whole_term(p)),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // Of a claim joined by "or" or "and": the claim of the named numbers,
        // and the claim as stated given from it.
        let given = match parted.is_empty() {
            true => None,
            false => {
                let says = match inner.formula(node) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let name = "named_claim";
                let stated = match self.witnessed_parts(
                    &inner,
                    node,
                    super::super::tactics::hyp(name),
                    &specs,
                ) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                Some((name, says, stated))
            }
        };
        let outer = mem::replace(&mut self.writer, inner);
        self.named_specs = specs.clone();
        self.in_witness.set(!ints.is_empty());
        let proof = self.proof_of(reason, k, node);
        self.in_witness.set(false);
        self.named_specs.clear();
        self.writer = outer;
        for r in restated {
            if let Some(s) =
                self.trees.get_mut(&r.line).and_then(|l| l.get_mut(r.place))
            {
                s.says = r.before;
            }
        }
        let proof = match proof {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        if let Some((name, says, stated)) = given {
            haves.push(Tactic::Have {
                name: name.to_string(),
                says,
                proof: Box::new(proof),
            });
            haves.push(Tactic::Exact(stated));
            return Route::Built(doc::Proof::Block(haves));
        }
        if ints.is_empty() {
            return Route::Built(haves_then(haves, proof));
        }
        // `⟨m, equation, m₀, equation, ?_⟩`, each witness as the claim nests
        // them.
        let mut parts: Vec<Printed> = Vec::new();
        for int in ints {
            parts.extend([int, equal.clone()]);
        }
        parts.push(Printed::of(
            super::super::doc::TermKind::Open,
            super::super::doc::LeanType::Prop,
        ));
        haves.push(refine(parts));
        haves.push(tactic_of(&proof));
        Route::Built(doc::Proof::Block(haves))
    }

    /// Of a claim that a term Lean computes in ℚ or wider is a whole number,
    /// p^(a′ − a) ∈ ℕ, the term, the type its parts are named in (ℤ, the
    /// page's ℕ being integers), and whether the claim orders it, 0 < m or
    /// 0 ≤ m beside the integer m it is; None for any other claim, one of a
    /// letter among them.
    pub(super) fn wide_member(
        &self,
        node: &Node,
    ) -> Option<(Node, super::super::templates::Num, bool)> {
        let [term, set] = node.children.as_slice() else {
            return None;
        };
        if node.notation() != MEMBERSHIP || term.is_name() {
            return None;
        }
        let (whole, ordered) = match super::super::expr::system_of(set)? {
            expr::System::Positive | expr::System::NonNegative => (Num::Int, true),
            expr::System::Type(Num::Int) => (Num::Int, false),
            _ => return None,
        };
        let wide = self.writer.carrier(term).built()? > Num::Int;
        wide.then(|| (term.clone(), whole, ordered))
    }

    /// The lines step `i` names, by which it names whole numbers: its
    /// requires lines and the lines it cites, each with its Lean name.
    pub(super) fn step_facts(&self, i: usize) -> Vec<super::super::algebra::Cited> {
        let step = &self.thm.steps[i];
        let mut facts = Vec::new();
        // A requires line said under the claim's "for all"s is, inside the
        // step, the fact at the claim's letters, which the step's proof
        // introduces as `peel` names them: `r101_3 x`.
        let claimed = step
            .claim
            .sentences()
            .first()
            .and_then(|s| self.rec.page.get(s))
            .cloned();
        for (k, r) in step.requires.iter().enumerate() {
            if let Route::Built(node) = self.tree(&r.fact) {
                let mut proof =
                    super::super::tactics::hyp(&format!("r{}_{}", step.line, k + 1));
                let under = claimed
                    .as_ref()
                    .filter(|c| speaks_of_claim_letter(c, &node))
                    .map(|c| under_claim_binders(c, &node));
                if let Some(wrapped) = under {
                    let (intros, _, _) = self.peel(&wrapped);
                    for name in intros {
                        proof = applied_to(proof, super::super::tactics::hyp(&name));
                    }
                }
                facts.push(super::super::algebra::Cited {
                    node,
                    proof,
                    says: None,
                });
            }
        }
        let cited = self.cited_parts(&step.just.refs);
        // A "for all" line is read at the block's letter the claim names, as
        // the checker reads it: 5.6's "for all a ∈ {2, …, p − 2}, f(a) ∈ ℤ"
        // says f(a) ∈ ℤ at the block's a.
        let mut names = BTreeSet::new();
        for s in step.claim.sentences() {
            if let Some(n) = self.rec.page.get(&s) {
                names.extend(n.names());
            }
        }
        for c in &cited {
            if let Some(at) = self.at_recorded_letter(c, &names) {
                conjuncts(&at.node, at.proof, at.says, &mut facts, &self.writer);
            }
        }
        facts.extend(cited);
        let beside = self.shown_beside(i, &facts);
        facts.extend(beside);
        facts
    }

    /// The memberships the checker found step `i` shows by an equation
    /// (`ShownBy::Beside`), each as a line Lean has: the line putting the
    /// equation's other side in its system, rewritten by the equation,
    /// `(by simpa only [← e] using h : ∃ m : ℤ, ↑m = a * f a)`; or, where
    /// the other side is said once and Lean computes it as an integer, that
    /// integer with the equation, `⟨p ^ 2 + q ^ 2, by exact_mod_cast e⟩`.
    /// The facts are the step's, which hold both lines; a membership whose
    /// lines Lean does not hold as the checker read them is left out.
    pub(super) fn shown_beside(
        &self,
        i: usize,
        facts: &[super::super::algebra::Cited],
    ) -> Vec<super::super::algebra::Cited> {
        let ctx = self.sources.ctx;
        let mut out = Vec::new();
        for shown in self.rec.places_shown.get(i).into_iter().flatten() {
            let ShownBy::Beside(beside) = &shown.by else {
                continue;
            };
            let other = &beside.other;
            let Some(e) = facts
                .iter()
                .find(|f| matching::alike_top(&f.node, &beside.equation, ctx))
            else {
                continue;
            };
            // e is term = other, or other = term where it faces turned.
            let term_first = beside.facing == Facing::Straight;
            // The line the checker found states the other side's membership.
            let held = beside.other_stated.as_ref().and_then(|stated| {
                facts
                    .iter()
                    .find(|f| matching::alike_top(&f.node, stated, ctx))
            });
            let (node, proved) = match held {
                // A line puts the other side in the system: it, rewritten by
                // the equation, which turns the other side into the term.
                Some(h) => {
                    let node = h.node.with_children(vec![
                        shown.term.clone(),
                        h.node.children[1].clone(),
                    ]);
                    let rule = match term_first {
                        true => t::backwards(e.proof.clone()),
                        false => t::forwards(e.proof.clone()),
                    };
                    let simpa = t::call(
                        "simpa",
                        vec![
                            TacticArg::Only,
                            TacticArg::Rules(vec![rule]),
                            TacticArg::Using(h.proof.clone()),
                        ],
                    );
                    (node, t::by_term(doc::Proof::By(simpa)))
                }
                // The other side is said once, an integer Lean computes as
                // one, p² + q² of integers: that integer, and the equation
                // cast down.
                None if shown.system == rules::System::Z
                    && beside.other_beside.is_none() =>
                {
                    let int = super::super::templates::Num::Int;
                    let lean_whole =
                        self.writer.carrier(other).built().is_some_and(|c| c <= int);
                    let Some(number) = self.writer.number_fixed(other, int).built()
                    else {
                        continue;
                    };
                    if !lean_whole {
                        continue;
                    }
                    let Some(set) =
                        page::made_as(&self.sources.checked.grammar, "ℤ", vec![])
                    else {
                        continue;
                    };
                    let node = page::made_as(
                        &self.sources.checked.grammar,
                        "_ ∈ _",
                        vec![shown.term.clone(), set],
                    );
                    let Some(node) = node else {
                        continue;
                    };
                    let equal = match term_first {
                        true => t::symm(e.proof.clone()),
                        false => e.proof.clone(),
                    };
                    let cast = t::by_term(doc::Proof::By(t::exact_mod_cast(equal)));
                    (node, super::super::expr::anonymous(vec![number, cast]))
                }
                None => continue,
            };
            let Route::Built(says) = self.writer.formula(&node) else {
                continue;
            };
            let proof = ascribed(proved, says.clone());
            out.push(super::super::algebra::Cited {
                node,
                proof,
                says: Some(says),
            });
        }
        out
    }

    /// Whether the item `reason` cites for the claim's sentence `k` is
    /// stated in Lean of the whole number it puts in a slot, as
    /// `Writer::slot_witness` writes it: gcd(a/gcd(a, b), …) = 1 as
    /// `∃ m : ℤ, (m : ℚ) = a / gcd(a, b) ∧ …`. A citation of it then gives
    /// the claim's witness. An item whose own lines make the term whole,
    /// `Even (2 ^ n.toNat)`, is stated of the term, and its citing step
    /// names the whole number as any does.
    fn item_states_whole(&self, reason: Reason, k: usize) -> bool {
        let Route::Built((item, cited)) = self.cited_item(reason) else {
            return false;
        };
        let Some(sentence) = cited
            .concluded
            .get(k)
            .and_then(|c| item.sentences.get(c.sentence))
        else {
            return false;
        };
        let TermKind::Quantified {
            quant: Quant::Exists,
            letter_ty: LeanType::Num(_),
            guard: Some(guard),
            ..
        } = &sentence.prop.kind
        else {
            return false;
        };
        matches!(&guard.kind, TermKind::Infix { op, .. } if *op == Op::EQUALS)
    }

    /// Of a claim joined by "or" or "and", the term each part puts in a
    /// whole-number slot that Lean does not compute as one, as a claim of
    /// one part alone takes it (`Writer::wide_in_slot`): "a/k is even or
    /// b/k is even" gives a/k and b/k. Empty of any other claim.
    fn wide_in_parts(&self, node: &Node) -> Vec<WideTerm> {
        let w = &self.writer;
        if let Some((l, r)) = w.and_sides(node) {
            return [l, r].iter().flat_map(|p| self.part_wides(p)).collect();
        }
        match (node.notation(), node.children.as_slice()) {
            (DISJUNCTION, [l, r]) => {
                [l, r].iter().flat_map(|p| self.part_wides(p)).collect()
            }
            _ => Vec::new(),
        }
    }

    /// `wide_in_parts` of one part: its parts where it is itself joined,
    /// else its own terms.
    fn part_wides(&self, part: &Node) -> Vec<WideTerm> {
        let joined = self.writer.is_and(part) || part.notation() == DISJUNCTION;
        match joined {
            true => self.wide_in_parts(part),
            false => self.leaf_wides(part),
        }
    }

    /// Each term a claim joined by no connective puts in a whole-number
    /// slot that Lean does not compute as one, in the order
    /// `Writer::slot_witness` gives them their witnesses, the first
    /// outermost: gcd(b/k, a/k) = gcd(a/k, b/k) gives b/k, then a/k.
    fn leaf_wides(&self, node: &Node) -> Vec<WideTerm> {
        let mut out = Vec::new();
        let mut w = self.writer.with_letters(self.writer.letters.clone());
        let mut at = node.clone();
        while let Some((term, whole)) = w.wide_in_slot(&at) {
            let m = super::super::expr::witness_letter(&at);
            w.letters.insert(m.clone(), LetterType::Number(whole));
            let named = Node::name(Sort::of("number"), &m);
            at = super::super::expr::put_for(&at, &term, &named);
            out.push(WideTerm { term, whole });
        }
        out
    }

    /// The claim as the step states it, each part's term given as some
    /// whole number (`Writer::slot_witness`), from `h`, a proof of the claim
    /// as `inner` writes it of the numbers the step names: each part with
    /// such a term is `⟨m, equation, h⟩` of the number m named for it, an
    /// "or" each side so by `Or.imp`, an "and" each from its projection.
    /// Declined of a part that holds such a term inside a connective of its
    /// own, a "not" or a quantifier, which the two write apart.
    fn witnessed_parts(
        &self,
        inner: &super::super::expr::Writer,
        node: &Node,
        h: Printed,
        specs: &[Printed],
    ) -> Route<Printed> {
        let w = &self.writer;
        if let Some((l, r)) = w.and_sides(node) {
            let left = match self.witnessed_parts(
                inner,
                l,
                projected(h.clone(), &["1"]),
                specs,
            ) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            let right =
                match self.witnessed_parts(inner, r, projected(h, &["2"]), specs) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
            return Route::Built(super::super::expr::anonymous(vec![left, right]));
        }
        if let (DISJUNCTION, [l, r]) = (node.notation(), node.children.as_slice()) {
            let mut sides = Vec::new();
            for side in [l, r] {
                let body = match self.witnessed_parts(
                    inner,
                    side,
                    super::super::tactics::hyp("h"),
                    specs,
                ) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                sides.push(Printed {
                    kind: super::super::doc::TermKind::Lambda {
                        letters: vec!["h".to_string()],
                        body: Box::new(body),
                    },
                    ty: None,
                });
            }
            sides.push(h);
            return Route::Built(Printed::applied(
                "Or.imp",
                super::super::doc::Source::Core,
                sides,
                super::super::doc::LeanType::Prop,
            ));
        }
        let wides = self.leaf_wides(node);
        if wides.is_empty() {
            return match node.walk().iter().any(|n| w.wide_arg(n).is_some()) {
                true => Route::no(
                    "a part of a claim holding a term in a whole-number slot inside a \
                     connective of its own",
                ),
                false => Route::Built(h),
            };
        }
        // `⟨m, equation, m₀, equation, h⟩`, each witness as the part nests
        // them.
        let mut parts = Vec::new();
        for w in &wides {
            match inner.number_fixed(&w.term, w.whole) {
                Route::Built(p) => parts.push(whole_term(p)),
                Route::Declined(d) => return Route::Declined(d),
            }
            parts.push(specs_equal_of(&w.term, specs));
        }
        parts.push(h);
        Route::Built(super::super::expr::anonymous(parts))
    }

    /// The whole numbers a term is made of that Lean does not compute as
    /// whole numbers, each named from a line step `i` names, by the said-once
    /// walk both backends read memberships with (`citing::reason_within`,
    /// over the checker's letters), each part the walk does not take apart
    /// held as the check found it (`held_reason`): 2^(p − 1) from the
    /// requires line `p − 1
    /// ∈ ℕ₀`, as `⟨2 ^ (p − 1).toNat, …⟩`; a term a line says is in ℤ, ℕ₀ or
    /// ℕ, from that line. A term made of such by +, − and · is written of
    /// them (`Writer::number`), so it keeps one form. Declined where no line
    /// the step names makes the term a whole number.
    pub(super) fn name_wholes(
        &self,
        term: &Node,
        letters: &Introduced,
        whole: super::super::templates::Num,
        facts: &[super::super::algebra::Cited],
        out: &mut Vec<NamedAtom>,
    ) -> Route<()> {
        let system = match whole {
            super::super::templates::Num::Nat => rules::System::N0,
            _ => rules::System::Z,
        };
        let said = |t: &Node, s: rules::System| self.held_reason(t, s, letters, facts);
        let given = self.writer.said_once_given();
        let nonzero = |d: &Node| membership::nonzero(d, &given);
        let Some(reason) = reason_within(term, system, letters, &nonzero, &said) else {
            return Route::no(format!(
                "{}, put where a whole number is asked, is one by no line the step names",
                self.writer.grammar.print(term)
            ));
        };
        let top = match self.writer.carrier(term) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        };
        match self.atoms_of(term, &reason, whole, top, facts, out) {
            true => Route::Built(()),
            false => Route::no(format!(
                "{} is a whole number Lean is not shown, by the lines the step names",
                self.writer.grammar.print(term)
            )),
        }
    }

    /// The parts the reason on `line` divides by, with how Lean is shown
    /// each is not zero (`CheckedTheorem::divided_by`). Of a part a line
    /// says is not zero, or says is in ℕ, the line it is read from, among
    /// those the step names, with the step's `defines` written out in it
    /// as the checker reads it (`line_nonzero`). A positive integer of
    /// letters and numerals alone is `positivity`'s, and numerals are left
    /// to `field_simp`, which works them out.
    pub(super) fn divisors_at(
        &self,
        line: usize,
        defines: &[CitedDefine],
    ) -> Route<Vec<super::super::algebra::NotZero>> {
        let named: Vec<String> =
            self.named_now.borrow().iter().flatten().cloned().collect();
        let mut facts = self.cited_parts(&named);
        for f in &mut facts {
            for d in defines {
                f.node = self.put_define(&f.node, d);
            }
        }
        let mut out = Vec::new();
        for part in self.rec.divided_by.get(&line).into_iter().flatten() {
            let by = match &part.by {
                NonzeroBy::Numerals => continue,
                NonzeroBy::Positive { shown } => match shown.as_held() {
                    // A line says it is in ℕ, which Lean states as 0 < d.
                    Shown::Stated { line } => match self.line_nonzero(line, &facts) {
                        Route::Built(by) => by,
                        Route::Declined(d) => return Route::Declined(d),
                    },
                    // The walk over letters and numerals alone, whose
                    // bounds Lean holds as hypotheses.
                    Shown::Walked { taken, .. } if taken.is_empty() => {
                        NotZeroBy::Positive
                    }
                    _ => {
                        return Route::no(format!(
                        "{}, a positive integer by a derivation Lean writes no ≠ 0 of",
                        self.writer.grammar.print(&part.term)
                    ))
                    }
                },
                NonzeroBy::Stated { from, .. } => match self.line_nonzero(from, &facts)
                {
                    Route::Built(by) => by,
                    Route::Declined(d) => return Route::Declined(d),
                },
            };
            out.push(NotZero {
                term: part.term.clone(),
                by,
            });
        }
        Route::Built(out)
    }

    /// How Lean is shown a divisor is not zero by the line `from` the
    /// checker read it from, among `facts`, those the step names, turned to
    /// say `d ≠ 0` by what its Lean statement says (`nonzero_turned`):
    /// `d ∈ ℕ` is `0 < d` in Lean, so `h.ne'`.
    fn line_nonzero(
        &self,
        from: &Node,
        facts: &[super::super::algebra::Cited],
    ) -> Route<NotZeroBy> {
        let ctx = self.sources.ctx;
        let standard = |n: &Node| matching::standard(n, ctx);
        let from = standard(from);
        let said = facts
            .iter()
            .find(|f| matching::alike_top(&standard(&f.node), &from, ctx))
            .and_then(|f| {
                let says = f
                    .says
                    .clone()
                    .or_else(|| self.writer.formula(&f.node).built())?;
                Some((f, says))
            });
        let Some((fact, says)) = said else {
            return Route::no(format!(
                "a divisor's ≠ 0 the checker read from {}, which no line the step names says in Lean",
                self.writer.grammar.print(&from)
            ));
        };
        let witnessed = || {
            natural_witnessed(&fact.node, &self.writer)
                .then(|| unwitnessed_nonzero(&fact.proof))
        };
        let Some(proof) = nonzero_turned(&fact.proof, &says).or_else(witnessed) else {
            return Route::no(format!(
                "a divisor's ≠ 0 read from {}, which Lean states as {}, no sign or ≠ 0",
                self.writer.grammar.print(&from),
                says.text()
            ));
        };
        let stated = match super::super::doc::forms::relation_type(&says) {
            Some(super::super::doc::LeanType::Num(n)) => Some(n),
            _ => None,
        };
        Route::Built(NotZeroBy::Line { proof, stated })
    }

    /// The record's parts held by the lines of the reason on `line`
    /// (`CheckedTheorem::held_by_lines`); none for a line it has none of.
    pub(super) fn held_at(&self, line: usize) -> Vec<HeldByLines> {
        self.rec
            .held_by_lines
            .get(&line)
            .cloned()
            .unwrap_or_default()
    }

    /// How the lines of the reason being written hold `term` in `system`, as
    /// the check found it; None where they do not.
    pub(super) fn held(&self, term: &Node, system: rules::System) -> Option<Shown> {
        let ctx = self.sources.ctx;
        let standard = |n: &Node| matching::standard(n, ctx);
        let term = standard(term);
        self.held_now
            .borrow()
            .iter()
            .find(|h| {
                h.system == system
                    && matching::alike_top(&standard(&h.term), &term, ctx)
            })
            .map(|h| h.shown.clone())
    }

    /// Why a part the said-once walk does not take apart is in `system`, as
    /// the check found it (`held`): a line among `facts` stating it, or an
    /// operation the closure table names
    /// (`rules::WHOLE`), x mod n in ℕ₀ where x ∈ ℤ and n ∈ ℕ, built from
    /// its parts the same way. Of an operation whose parts are not the
    /// term's own children, a library function's value, none.
    pub(super) fn held_reason(
        &self,
        term: &Node,
        system: rules::System,
        letters: &Introduced,
        facts: &[super::super::algebra::Cited],
    ) -> Option<OnceReason> {
        // How the check found the part held, of the lines the reason names;
        // a line stating it, or one the equation it stands beside makes
        // (`shown_beside`), is among `facts` under its Lean name.
        // A row of the closure is built from its parts below; of the rows,
        // only a whole number's is a Lean term the parts build.
        if let Shown::Stated { .. } | Shown::Beside { .. } = self.held(term, system)? {
            return named_line(facts, term, system, self.sources.ctx)
                .map(|_| OnceReason::Stated);
        }
        let op = self.sources.targets.operation(term)?;
        let w = WHOLE.iter().find(|w| w.op == op.label)?;
        let (Some(left_in), Some(right_in)) = (
            rules::System::of_label(w.left.1),
            rules::System::of_label(w.right.1),
        ) else {
            return None;
        };
        let own = op.parts.len() == term.children.len()
            && op
                .parts
                .iter()
                .zip(&term.children)
                .all(|(p, c)| ptr::eq(*p, c));
        if !own || !rules::System::N0.within(system) {
            return None;
        }
        let said = |t: &Node, s: rules::System| self.held_reason(t, s, letters, facts);
        let given = self.writer.said_once_given();
        let nonzero = |d: &Node| membership::nonzero(d, &given);
        let mut parts = Vec::new();
        for (part, within) in op.parts.iter().zip([left_in, right_in]) {
            parts.push(reason_within(part, within, letters, &nonzero, &said)?);
        }
        Some(OnceReason::Built(parts))
    }

    /// A membership `t ∈ ℤ` the check found beside an equation, by the line
    /// its reason is on (`CheckedTheorem::members_shown`): the equation's
    /// other side named whole from `facts` (`whole_witness`), and the
    /// equation, among them, turning the goal's t into it, `have other :
    /// ∃ m : ℤ, ↑m = a ^ (p − 2) * a := …; rw [s5_7_4]; exact other`. None
    /// where the check found t otherwise, or the lines do not give it so.
    pub(super) fn member_beside(
        &self,
        line: usize,
        term: &Node,
        node: &Node,
        letters: &Introduced,
        facts: &[super::super::algebra::Cited],
    ) -> Option<super::super::doc::Proof> {
        let ctx = self.sources.ctx;
        let shown = self.rec.members_shown.get(&line)?;
        let ShownBy::Beside(beside) = &shown.by else {
            return None;
        };
        let other = &beside.other;
        if !matching::alike_top(&shown.term, term, ctx) {
            return None;
        }
        let e = facts
            .iter()
            .find(|f| matching::alike_top(&f.node, &beside.equation, ctx))?;
        let set = node.children.get(1)?.clone();
        let says = self
            .writer
            .formula(&node.with_children(vec![other.clone(), set]))
            .built()?;
        // Of another side Lean already computes whole, k of (N − 1)/2 = k,
        // the equation gives the witness itself (`member_by_equation`).
        if says.is_truth() {
            return None;
        }
        let named = self.whole_witness(other, letters, facts).built()?;
        // Which side the term is (`Besides::facing`).
        let rule = match beside.facing {
            Facing::Straight => t::forwards(e.proof.clone()),
            Facing::Turned => t::backwards(e.proof.clone()),
        };
        // One tactic to a line: the have's own proof may take several.
        Some(doc::Proof::Block(vec![
            Tactic::Have {
                name: "other".to_string(),
                says,
                proof: Box::new(named),
            },
            t::call("rw", vec![TacticArg::Rules(vec![rule])]),
            Tactic::Exact(t::hyp("other")),
        ]))
    }

    /// `∃ m : ℤ, ↑m = t` of a term Lean computes wider, proved as a step
    /// proves its membership (`proof_named_from`): the whole number it is
    /// named from `facts` with `letters` (`name_wholes`), each named number's
    /// have, then `exact ⟨n, equal⟩`.
    pub(super) fn whole_witness(
        &self,
        term: &Node,
        letters: &Introduced,
        facts: &[super::super::algebra::Cited],
    ) -> Route<super::super::doc::Proof> {
        let mut atoms = Vec::new();
        let int = super::super::templates::Num::Int;
        if let Route::Declined(d) =
            self.name_wholes(term, letters, int, facts, &mut atoms)
        {
            return Route::Declined(d);
        }
        let mut inner = self.writer.with_letters(self.writer.letters.clone());
        inner.integers.extend(atoms.iter().map(|a| a.said.clone()));
        let number = match inner.number_fixed(term, int) {
            Route::Built(p) => whole_term(p),
            Route::Declined(d) => return Route::Declined(d),
        };
        let specs: Vec<Printed> = atoms.iter().map(|a| spec_of(&a.said)).collect();
        let equal = specs_equal_of(term, &specs);
        let haves: Vec<Tactic> = atoms.iter().map(|a| a.have.clone()).collect();
        let shown = Tactic::Exact(super::super::expr::anonymous(vec![number, equal]));
        Route::Built(haves_then(haves, doc::Proof::By(shown)))
    }

    /// `name_wholes` of one part, whose reason is `reason`, named in
    /// `whole`, ℤ or ℕ: false where a part is none the walk can name.
    pub(super) fn atoms_of(
        &self,
        term: &Node,
        reason: &OnceReason,
        whole: super::super::templates::Num,
        top: super::super::templates::Num,
        facts: &[super::super::algebra::Cited],
        out: &mut Vec<NamedAtom>,
    ) -> bool {
        let Some(own) = self.writer.carrier(term).built() else {
            return false;
        };
        // Each equation is stated in the type of the whole term the part is
        // in, ℚ of 2^(p − 1)·(2^p − 1), where it is put into that term's.
        let at = own.max(top);
        let already = match whole {
            Num::Nat => {
                self.writer.natural_form(term)
                    != super::super::expr::NaturalForm::Integer
            }
            _ => own <= Num::Int,
        };
        if already {
            return true;
        }
        let printed = self.writer.grammar.print(term);
        if out.iter().any(|a| a.said.term == printed) {
            return true;
        }
        let Some(value) = self.writer.number_fixed(term, at).built() else {
            return false;
        };
        let name = format!("whole{}", out.len() + 1);
        let ty = self.writer.num_type(at);
        let (have, written) = match (reason, term.notation(), term.children.as_slice())
        {
            // A term a line the step names puts in ℕ, ℕ₀ or ℤ: that line's
            // witness, of ℕ where a natural number is asked.
            (OnceReason::Stated, _, _) => {
                let asked = match whole {
                    Num::Nat => rules::System::N0,
                    _ => rules::System::Z,
                };
                let Some(NamedLine { name: line, system }) =
                    named_line(facts, term, asked, self.sources.ctx)
                else {
                    return false;
                };
                // Of an integer, the line is an order, 0 < 2^p − 1 for ∈ ℕ:
                // the natural number is the integer's `toNat`, written out as
                // σ of an integer takes it, and its equation with the term.
                if own <= Num::Int {
                    let Some(int) = self.writer.number_fixed(term, Num::Int).built()
                    else {
                        return false;
                    };
                    let written = Printed::of(
                        super::super::doc::TermKind::ToNat(Box::new(t::bracket(int))),
                        LeanType::Num(Num::Nat),
                    );
                    let as_nat =
                        Printed::cast(written.clone(), LeanType::Num(Num::Nat));
                    let says = Printed::infix(
                        Op::EQUALS,
                        Printed::cast(as_nat, ty.clone()),
                        value,
                        LeanType::Prop,
                    );
                    let nonneg = nonneg_of(system, line);
                    out.push(NamedAtom {
                        have: Tactic::Have {
                            name: name.clone(),
                            says,
                            proof: Box::new(doc::Proof::By(t::exact_mod_cast(
                                to_nat_of(nonneg.clone()),
                            ))),
                        },
                        said: super::super::expr::SaidInteger {
                            term: printed,
                            proof: t::hyp(&name),
                            ty: whole,
                            value: Some(written),
                            slot_only: true,
                            back: Some(to_nat_of(nonneg)),
                        },
                    });
                    return true;
                }
                // Of a wider term, the line is a witness: `∃ m : ℤ, 0 ≤ m ∧
                // ↑m = t` for ℕ₀, `0 < m` for ℕ, `↑m = t` for ℤ. A natural
                // number asked is that integer's `toNat`, by its order. The
                // witness's letter is one the term does not write, m₀ of a
                // term in m (`witness_letter`).
                let letter = super::super::expr::witness_letter(term);
                let m = || t::hyp(&letter);
                let (letter_ty, names, witness) = match (system, whole) {
                    (rules::System::N | rules::System::N0, Num::Nat) => {
                        let m_nat = Printed::of(
                            super::super::doc::TermKind::ToNat(Box::new(m())),
                            LeanType::Num(Num::Nat),
                        );
                        let same = Printed::infix(
                            Op::EQUALS,
                            Printed::cast(
                                Printed::cast(m_nat.clone(), LeanType::Num(Num::Nat)),
                                ty.clone(),
                            ),
                            Printed::cast(
                                Printed::cast(m(), LeanType::Num(Num::Int)),
                                ty.clone(),
                            ),
                            LeanType::Prop,
                        );
                        let same_by = doc::Proof::By(t::exact_mod_cast(to_nat_of(
                            nonneg_of(system, t::hyp("h0")),
                        )));
                        let rewritten = doc::Proof::By(Tactic::Seq(vec![
                            t::call(
                                "rw",
                                vec![TacticArg::Rules(vec![t::forwards(shown(
                                    same, same_by,
                                ))])],
                            ),
                            t::exact_mod_cast(t::hyp("hm")),
                        ]));
                        (
                            Num::Nat,
                            vec![letter.as_str(), "h0", "hm"],
                            vec![m_nat, super::super::tactics::by_term(rewritten)],
                        )
                    }
                    (rules::System::N | rules::System::N0, _) => (
                        Num::Int,
                        vec![letter.as_str(), "_", "hm"],
                        vec![
                            m(),
                            super::super::tactics::by_term(cast_carried(
                                t::hyp("hm"),
                                own,
                                at,
                            )),
                        ],
                    ),
                    _ => (
                        whole,
                        vec![letter.as_str(), "hm"],
                        vec![
                            m(),
                            super::super::tactics::by_term(cast_carried(
                                t::hyp("hm"),
                                own,
                                at,
                            )),
                        ],
                    ),
                };
                let says = Printed::of(
                    super::super::doc::TermKind::Quantified {
                        quant: super::super::doc::Quant::Exists,
                        letter: letter.clone(),
                        letter_ty: LeanType::Num(letter_ty),
                        guard: None,
                        body: Box::new(Printed::infix(
                            Op::EQUALS,
                            Printed::cast(m(), ty.clone()),
                            value,
                            LeanType::Prop,
                        )),
                        bounded: false,
                    },
                    LeanType::Prop,
                );
                let proof = doc::Proof::By(Tactic::Seq(vec![
                    Tactic::Obtain {
                        names: names.iter().map(|n| n.to_string()).collect(),
                        says: None,
                        from: line,
                    },
                    Tactic::Exact(super::super::expr::anonymous(witness)),
                ]));
                let have = Tactic::Have {
                    name: name.clone(),
                    says,
                    proof: Box::new(proof),
                };
                (have, None)
            }
            // A power to an exponent a line the step names puts in ℕ₀: the
            // base to that exponent's `toNat`, written out, and its equation
            // with the power, from that line.
            (OnceReason::Built(parts), POWER, [base, exponent]) => {
                let [base_reason] = parts.as_slice() else {
                    return false;
                };
                if self.writer.natural_form(exponent)
                    != super::super::expr::NaturalForm::Integer
                {
                    return self.atoms_of(base, base_reason, whole, top, facts, out);
                }
                let Some(NamedLine { name: line, system }) =
                    named_line(facts, exponent, rules::System::N0, self.sources.ctx)
                else {
                    return false;
                };
                let (Some(b), Some(e), Some(cast_base)) = (
                    self.writer.number_fixed(base, whole).built(),
                    self.writer.number_fixed(exponent, Num::Int).built(),
                    self.writer.number_fixed(base, at).built(),
                ) else {
                    return false;
                };
                let power = Op::POWER;
                let e_nat = Printed::of(
                    super::super::doc::TermKind::ToNat(Box::new(t::bracket(e))),
                    LeanType::Num(Num::Nat),
                );
                let written =
                    Printed::infix(power, b, e_nat.clone(), LeanType::Num(whole));
                let says = Printed::infix(
                    Op::EQUALS,
                    Printed::infix(
                        power,
                        Printed::cast(cast_base, ty.clone()),
                        e_nat,
                        ty.clone(),
                    ),
                    value,
                    LeanType::Prop,
                );
                let rules = vec![
                    t::backwards(t::lemma("zpow_natCast")),
                    t::forwards(to_nat_of(nonneg_of(system, line))),
                ];
                let have = Tactic::Have {
                    name: name.clone(),
                    says,
                    proof: Box::new(doc::Proof::By(t::call(
                        "rw",
                        vec![TacticArg::Rules(rules)],
                    ))),
                };
                (have, Some(written))
            }
            (OnceReason::Built(parts), _, kids) if parts.len() == kids.len() => {
                return kids.iter().zip(parts).all(|(kid, part)| {
                    self.atoms_of(kid, part, whole, top, facts, out)
                });
            }
            _ => return false,
        };
        out.push(NamedAtom {
            have,
            said: super::super::expr::SaidInteger {
                term: printed,
                proof: t::hyp(&name),
                ty: whole,
                value: written,
                slot_only: true,
                back: None,
            },
        });
        true
    }

    /// `0 ≤ t` of a term the said-once walk puts in ℕ₀ at the step being
    /// written (`said_bound`): `abs_nonneg` of |A| of an A in ℤ.
    pub(super) fn said_nonneg(&self, term: &Node) -> Option<Printed> {
        self.said_bound(term, rules::System::N0, &[])
    }

    /// The bound a membership of ℕ₀ or ℕ is in Lean, `0 ≤ t` or `0 < t`, of
    /// a term the said-once walk puts there at the step being written, by
    /// the walk's reason (`citing::reason_within`, over the checker's
    /// letters, each part held as the check found it), as `name_wholes`
    /// reads it: `nonneg_by`, `positive_by`. None outside a step, of
    /// another system, or where the walk gives no reason or no proof.
    pub(super) fn said_bound(
        &self,
        term: &Node,
        system: rules::System,
        refs: &[String],
    ) -> Option<Printed> {
        self.said_bound_in(term, system, refs, &self.writer)
    }

    /// `said_bound`, the step's lines read as `writer` writes them: the
    /// writer inside a claim's "for all", where its letter has a type.
    pub(super) fn said_bound_in(
        &self,
        term: &Node,
        system: rules::System,
        refs: &[String],
        writer: &Writer,
    ) -> Option<Printed> {
        let i = self.step_now.get()?;
        let letters = self.rec.introduced.get(i)?;
        // The step's lines, and those the reason itself names, a requires
        // line's `from 5.13`.
        let mut facts = self.step_facts(i);
        facts.extend(self.cited_parts(refs));
        let said = |t: &Node, s: rules::System| self.held_reason(t, s, letters, &facts);
        let given = self.writer.said_once_given();
        let nonzero = |d: &Node| membership::nonzero(d, &given);
        let reason = reason_within(term, system, letters, &nonzero, &said);
        let reason = reason?;
        match system {
            rules::System::N0 => {
                self.nonneg_by(term, &reason, &self.wholes_among_in(&facts, writer))
            }
            rules::System::N => self.positive_by(term, &reason, &facts),
            _ => None,
        }
    }

    /// The proof of sentence `k` of a claim, by its reason.
    pub(super) fn proof_of(
        &self,
        reason: Reason,
        k: usize,
        node: &Node,
    ) -> Route<super::super::doc::Proof> {
        if let Some(witness) = self.member_by_integers(node) {
            return Route::Built(witness);
        }
        self.said_used.borrow_mut().clear();
        let outer = self.claim_now.replace(Some(node.clone()));
        let proof = self.proof_by_reason(reason, k, node);
        self.claim_now.replace(outer);
        let proof = match proof {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A citation given a line's number, ⌊m⌋ = m for the m of `A/B ∈
        // ℤ`, meets a goal that has the line's term, ⌊A/B⌋: the goal is put
        // in terms of the number first.
        let used = mem::take(&mut *self.said_used.borrow_mut());
        let by_term = self.number_rules(node, &used);
        if by_term.is_empty() {
            return Route::Built(proof);
        }
        let specs: Vec<super::super::doc::Rule> =
            by_term.iter().map(|r| r.rule.clone()).collect();
        let terms: Vec<String> = by_term.iter().map(|r| r.term.clone()).collect();
        let mut steps = vec![t::call("rw", vec![TacticArg::Rules(specs)])];
        // A remainder of the named numbers, now of integers cast to ℝ, is
        // put as their `%`, which a cited item of integers states.
        if self.remainder_of_integers(node, &terms) {
            steps.push(t::call(
                "rw",
                vec![TacticArg::Rules(vec![t::forwards(mod_int_cast())])],
            ));
        }
        // What the citation asks of a named number is said of it: the order
        // a line of ℕ or ℕ₀ gives beside its equation, or the range a line
        // of a range does, and each line the step cites, put in terms of the
        // numbers as the goal is and cast down to them, 5.5.2's mod(a^(p −
        // 2), p) < p as c < p.
        for u in &used {
            if let Some(beside) = u.line.besides() {
                steps.push(Tactic::Fact(beside));
            }
        }
        // A line that gives a number is left as it is: the number is chosen
        // from it, and a rewritten copy would be another line.
        let giving: Vec<String> = used.iter().map(|u| u.line.proof.text()).collect();
        let refs: Vec<&String> = reason.just.refs.iter().collect();
        steps.extend(self.put_numbers_in_lines(&refs, &giving, &by_term));
        steps.push(tactic_of(&proof));
        Route::Built(doc::Proof::By(Tactic::Seq(steps)))
    }

    /// The hypothesis of a function the theorem's header lets by its value,
    /// which a step cites by its label; None for any other citation.
    pub(super) fn header_function_cited(&self, just: &Justification) -> Option<String> {
        self.header_function_named(just.defined.as_deref()?)
    }

    /// The hypothesis of a function the theorem's header lets by its value,
    /// by its label; None for any other label.
    pub(super) fn header_function_named(&self, label: &str) -> Option<String> {
        let d = self
            .thm
            .defines
            .iter()
            .find(|d| d.label == label && d.line < self.thm.conclusion_line)?;
        match corpus::define_parts(&d.text) {
            // One of several arguments is written out where it is applied
            // (`checker::written`), and has no hypothesis to name.
            Route::Built(DefineParts::One(one)) if one.params.len() == 1 => {
                Some(line_name(&d.label))
            }
            _ => None,
        }
    }
}
