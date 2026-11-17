//! Proof methods: obtaining, blocks and inductions.

use super::*;
use crate::notations::{POWERSET, SUBSET, THERE_IS_SOME};

impl<'a> Proof<'a> {
    pub(super) fn obtain(&mut self, i: usize, depth: usize) -> Route<()> {
        self.said_used.borrow_mut().clear();
        let source = match self.obtained_from(i) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        let used = std::mem::take(&mut *self.said_used.borrow_mut());
        let step = &self.thm.steps[i];
        self.introduce(step);
        let claimed = match self.claimed(step) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let claim = Self::without_places(&claimed);
        let names = Self::names_of(step, claim.len());
        if let Some(n) = step.number.number() {
            self.named.insert(n.to_string(), names.clone());
            // Lean states each part as it takes it from the item, not as the
            // writer writes the page's claim: a part's statement is kept
            // below, where it is the item's (`lean_body_parts`).
            let said = Self::claim_sentences(&claimed, &names)
                .into_iter()
                .map(|s| LineSentence { says: None, ..s })
                .collect();
            self.store(n.to_string(), said);
        }
        // Lean nests a "there is" as the page does: each letter, then the
        // fact its range gives where Lean's type does not, then what is said
        // of them all. The claim's sentence about each letter's range is
        // that fact; its other sentences are what is said.
        let mut guards: IndexMap<String, String> = IndexMap::new();
        let mut body: Vec<String> = Vec::new();
        for ((node, _), name) in claim.iter().zip(&names) {
            // A letter's fact of being in a set, x ∈ A, as of a range, or
            // of being a part of one, W ⊆ X.
            let in_set = match node.children.as_slice() {
                [x, set]
                    if (node.notation() == crate::notations::MEMBERSHIP
                        || node.notation() == SUBSET)
                        && x.is_name()
                        && self.writer.members_of(set).is_some() =>
                {
                    Some(x.text.to_string())
                }
                _ => None,
            };
            // A function's fact of mapping one set into another, g : A → B,
            // the `Set.MapsTo` a "there is g : A → B" gives beside g.
            let maps = match node.children.as_slice() {
                [g, _, _]
                    if node.notation() == crate::notations::FUNCTION_TYPE
                        && g.is_name() =>
                {
                    Some(g.text.to_string())
                }
                _ => None,
            };
            let letter = introduces(node)
                .map(|(l, _)| l)
                .or_else(|| super::super::statement::range_letter(node))
                .or(in_set)
                .or(maps)
                .or_else(|| super::super::statement::introduces_polynomial(node));
            match letter.filter(|l| step.just.obtained.contains(l)) {
                Some(l) => {
                    guards.insert(l, name.clone());
                }
                None => body.push(name.clone()),
            }
        }
        // there is a ∈ X with nothing said, `∃ a ∈ X, True`: the letter, the
        // fact that it is in X, and nothing.
        if let (THERE_IS_SOME, [obtained]) =
            (source.says.notation(), step.just.obtained.as_slice())
        {
            let guard = guards
                .get(obtained)
                .cloned()
                .unwrap_or_else(|| "_".to_string());
            self.push_at(
                depth,
                Tactic::Obtain {
                    names: vec![
                        super::super::names::letter(obtained),
                        guard,
                        "_".to_string(),
                    ],
                    says: None,
                    from: source.term.clone(),
                },
                step.line,
                Self::step_spot(step),
            );
            return Route::Built(());
        }
        let mut pattern = Vec::new();
        let mut said = &source.says;
        // A "there is" the sentence says after an "and", u ∈ X and (there
        // are m, n with …): what comes before it, unnamed, and then it.
        while let Some((_, right)) = self.writer.and_sides(said) {
            if right.notation() != crate::notations::THERE_IS {
                break;
            }
            pattern.push("_".to_string());
            said = right;
        }
        // Each letter the item's "there is" binds, as the step names it.
        let mut renamed = crate::matching::Binding::new();
        for obtained in &step.just.obtained {
            let [bound, set, inner] = said.children.as_slice() else {
                return Route::no(
                    "an obtain of more letters than its \"there is\" binds",
                );
            };
            if said.notation() != crate::notations::THERE_IS {
                return Route::no(
                    "an obtain of more letters than its \"there is\" binds",
                );
            }
            pattern.push(super::super::names::letter(obtained));
            renamed.insert(
                crate::formula::symbol::Symbol::of(&bound.text),
                Node::name(bound.sort.clone(), obtained),
            );
            // Lean writes "there is s ∈ S" with the membership beside s
            // for every S but a number system its type gives, ℤ, ℚ, ℝ or
            // ℂ; the page's ℕ and ℕ₀ add that the integer s is above 0 or
            // at least 0. The set as the citation gives it, Y := ℕ.
            let given = match set.is_name() {
                true => source.binding.get(&set.text).unwrap_or(set),
                false => set,
            };
            let whole = matches!(
                super::super::expr::system_of(given),
                Some(
                    super::super::expr::System::Positive
                        | super::super::expr::System::NonNegative
                )
            );
            let guarded = set.notation() == crate::notations::INTEGER_RANGE
                || whole
                || super::super::expr::system_of(set).is_none();
            if guarded {
                // A member of the page's ℕ or ℕ₀ keeps its fact named.
                let unnamed = match whole {
                    true => format!("{}_pos", super::super::names::letter(obtained)),
                    false => "_".to_string(),
                };
                let guard = guards.get(obtained).cloned().unwrap_or(unnamed);
                pattern.push(guard);
            }
            said = inner;
        }
        // What is said of the letters, taken apart as Lean nests its "and":
        // ((d > 1 ∧ d ∣ p) ∧ d ∣ q) is ⟨⟨a, b⟩, c⟩.
        // A part Lean states otherwise than the page's sentence, q·N + 0 = A
        // for q·N = A, is obtained under a name of its own, and the sentence
        // is stated from it after, so that each line's name says what the
        // page says.
        let mut restated = Vec::new();
        // The names that hold their part as Lean states it from the item,
        // with that statement: what a step citing the line reads.
        let mut as_stated: Vec<(String, Printed)> = Vec::new();
        if !body.is_empty() {
            if body.len() > conjunct_count(said, &self.writer) {
                return Route::no(
                    "an obtain whose sentences are not the parts of its \"there is\"",
                );
            }
            let said = crate::matching::substitute_apart_by(
                said,
                &renamed,
                &self.sources.checked.grammar.binders(),
            );
            let parts = shaped_parts(&said, body.len(), &self.writer);
            // The parts as Lean states them, from the item's statement of
            // the "there is" (`Obtained::lean`), where it takes apart into
            // as many parts as the page's.
            let stated: Vec<Printed> = source
                .lean
                .as_ref()
                .map(|s| lean_body_parts(s, &step.just.obtained))
                .filter(|p| p.len() == conjunct_count(&said, &self.writer))
                .unwrap_or_default();
            let values = self.set_values();
            let mut lean_names = Vec::new();
            for (name, part) in body.iter().zip(&parts) {
                let at = claimed.iter().zip(&names).find(|(_, n)| *n == name);
                let page = at.map(|((_, _, p), _)| p.clone());
                // The part of the "there is" the checker found the sentence
                // to be (`ObtainedPart::owed`), as Lean states it.
                let owed = at.and_then(|((place, _, _), _)| {
                    let found: Vec<&crate::checker::record::ObtainedPart> = self
                        .rec
                        .obtained_parts
                        .get(&step.just.line)
                        .into_iter()
                        .flatten()
                        .filter(|p| p.sentence == *place)
                        .collect();
                    match found.as_slice() {
                        [one] if one.part == 0 => self.stated_part(&stated, one),
                        _ => None,
                    }
                });
                // How the checker met the sentence's parts with those of
                // the "there is" (`CheckedTheorem::obtained_parts`), and
                // where the writer placed casts on the one and not the
                // other.
                let met = at.map(|((place, _, _), _)| {
                    self.rec
                        .obtained_parts
                        .get(&step.just.line)
                        .into_iter()
                        .flatten()
                        .filter(|p| p.sentence == *place)
                        .any(|p| {
                            p.meeting.turned
                                || p.meeting.permuted
                                || !p.meeting.identities.is_empty()
                        })
                });
                let lean = match &owed {
                    Some(stated) => Some(stated.clone()),
                    None => self.writer.formula(part).built(),
                };
                let differs = match (&page, &lean, met) {
                    (Some(says), Some(lean), Some(met)) => {
                        met || super::super::doc::forms::casts_differ(
                            lean, says, &values,
                        )
                        .is_some()
                    }
                    _ => false,
                };
                match (differs, page, lean) {
                    (true, Some(says), Some(lean)) => {
                        let as_obtained = format!("{name}_obtained");
                        lean_names.push(as_obtained.clone());
                        restated.push(Restated {
                            name: name.clone(),
                            says,
                            from: as_obtained,
                            lean,
                        });
                    }
                    _ => {
                        lean_names.push(name.clone());
                        if let Some(stated) = owed {
                            as_stated.push((name.clone(), stated));
                        }
                    }
                }
            }
            pattern.push(shaped_pattern(&said, &lean_names, &self.writer));
        }
        self.push_at(
            depth,
            Tactic::Obtain {
                names: pattern,
                says: None,
                from: source.term.clone(),
            },
            step.line,
            Self::step_spot(step),
        );
        for r in restated {
            let Some(proved) = self.proof_meeting(
                super::super::tactics::hyp(&r.from),
                &r.lean,
                &r.says,
            ) else {
                return Route::no(format!(
                    "an obtain whose part Lean states as {}, and the page as {}",
                    r.lean.text(),
                    r.says.text()
                ));
            };
            self.push_at(
                depth,
                Tactic::Have {
                    name: r.name,
                    says: r.says,
                    proof: Box::new(super::super::doc::Proof::Term(proved.term())),
                },
                step.line,
                Self::step_spot(step),
            );
        }
        // An item given a line's number, x := the rational of `√2 ∈ ℚ`,
        // gives its facts of that number; a sentence the page says of the
        // line's term, √2 = p/q, is that fact with the goal put in terms of
        // the number. It replaces the fact of the number, which a tactic
        // over every hypothesis, `qify at *`, would otherwise rewrite and so
        // bring back over it under the same name.
        for ((node, prop), name) in claim.iter().zip(&names) {
            let specs = self.specs_in(node, &used);
            if specs.is_empty() {
                continue;
            }
            as_stated.retain(|(n, _)| n != name);
            self.push_at(
                depth,
                Tactic::Replace {
                    name: name.clone(),
                    says: prop.clone(),
                    proof: Box::new(super::super::doc::Proof::By(Tactic::Seq(vec![
                        super::super::tactics::call(
                            "rw",
                            vec![TacticArg::Rules(specs)],
                        ),
                        super::super::tactics::exact_mod_cast(
                            super::super::tactics::hyp(name),
                        ),
                    ]))),
                },
                step.line,
                Self::step_spot(step),
            );
        }
        if let Some(line) = step
            .number
            .number()
            .and_then(|n| self.trees.get_mut(&n.to_string()))
        {
            for (name, stated) in as_stated {
                for s in line
                    .iter_mut()
                    .filter(|s| s.name.as_deref() == Some(name.as_str()))
                {
                    s.says = Some(stated.clone());
                }
            }
        }
        Route::Built(())
    }

    /// The rewrites that put a claim in terms of the numbers lines give,
    /// `← Classical.choose_spec hS` for each line used whose term the claim
    /// has, to rewrite by; none where it has none.
    pub(super) fn specs_in(
        &self,
        claim: &Node,
        used: &[SaidUsed],
    ) -> Vec<super::super::doc::Rule> {
        self.number_rules(claim, used)
            .into_iter()
            .map(|r| r.rule)
            .collect()
    }

    /// `specs_in`, each rewrite with the term it puts the number for.
    pub(super) fn number_rules(
        &self,
        claim: &Node,
        used: &[SaidUsed],
    ) -> Vec<NumberRule> {
        let parts: Vec<String> = claim
            .walk()
            .iter()
            .map(|n| self.writer.grammar.print(n))
            .collect();
        // A term standing where the Lean form of its notation reads it at ℝ,
        // the a^(p − 2) of (a^(p − 2)) mod p, is there at ℝ whatever type
        // the line naming its number says it in.
        let mut real: Vec<(String, Node)> = Vec::new();
        for n in claim.walk() {
            let mut at_real: Vec<&Node> = self.writer.always_real_args(&n);
            if let Route::Built(t) = self.writer.template(&n) {
                let fixed = super::super::templates::Slot::Fixed(
                    super::super::templates::Num::Real,
                );
                at_real.extend(
                    n.children
                        .iter()
                        .zip(&t.holes)
                        .filter(|(_, hole)| **hole == fixed)
                        .map(|(child, _)| child),
                );
            }
            for arg in at_real {
                real.push((self.writer.grammar.print(arg), arg.clone()));
            }
        }
        let mut lines: Vec<&Printed> = Vec::new();
        let mut out = Vec::new();
        for u in used {
            if !parts.contains(&u.term) || lines.contains(&&u.line.proof) {
                continue;
            }
            lines.push(&u.line.proof);
            let spec = u.line.equation();
            let at_real = real
                .iter()
                .find(|(printed, _)| *printed == u.term)
                .and_then(|(_, node)| {
                    let rule = self.spec_at_real(&u.line, spec.clone(), node)?;
                    let lean = self
                        .writer
                        .number_fixed(node, super::super::templates::Num::Real);
                    Some((rule, lean.built()))
                });
            // The term in its own type, as the line naming it states it.
            let (rule, lean) = match at_real {
                Some(found) => found,
                None => {
                    let own = claim
                        .walk()
                        .into_iter()
                        .find(|n| self.writer.grammar.print(n) == u.term)
                        .and_then(|n| {
                            let at = self.writer.carrier(&n).built()?;
                            self.writer.number(&n, at).built()
                        });
                    (spec, own)
                }
            };
            out.push(NumberRule {
                term: u.term.clone(),
                lean,
                rule: super::super::tactics::backwards(rule),
            });
        }
        out
    }

    /// The equation a line naming a whole number gives, `Classical.choose_spec
    /// h`, restated at ℝ, where its term stands at ℝ: `(by exact_mod_cast
    /// Classical.choose_spec h : ((Classical.choose h : ℤ) : ℝ) = t)`. None
    /// where the term is not written at ℝ.
    pub(super) fn spec_at_real(
        &self,
        line: &SaidLine,
        spec: Printed,
        term: &Node,
    ) -> Option<Printed> {
        use super::super::doc::LeanType;
        use super::super::templates::Num;
        let value = self.writer.number_fixed(term, Num::Real).built()?;
        let chosen = line.chosen(Num::Int);
        let says = Printed::infix(
            super::super::doc::Op::EQUALS,
            Printed::cast(
                Printed::cast(chosen, LeanType::Num(Num::Int)),
                LeanType::Num(Num::Real),
            ),
            value,
            LeanType::Prop,
        );
        // The line states its equation in the term's own type.
        let own = self.writer.carrier(term).built()?;
        let proof = super::super::tactics::by_term(cast_carried(spec, own, Num::Real));
        Some(ascribed(proof, says))
    }

    /// A step that owns a block: its claim proved by the block's steps,
    /// opened by its lines.
    pub(super) fn block(
        &mut self,
        i: usize,
        method: Method,
        claim: &[(Node, Printed)],
        names: &[String],
        depth: usize,
    ) -> Route<()> {
        let step = &self.thm.steps[i];
        let spot = Self::step_spot(step);
        // A claim Lean's types already make true needs no proof, and what
        // the block shows inside it is cited nowhere outside it.
        if claim.is_empty() {
            self.push_at(
                depth,
                Tactic::Comment("what this block shows, Lean's types give".to_string()),
                step.line,
                spot,
            );
            return Route::Built(());
        }
        // A claim of several sentences is proved as their "and", and taken
        // apart after into each sentence's name.
        let Some((claimed, _)) = claim.first() else {
            return Route::no("a block with no claim");
        };
        if claim.len() > 1 && method == Method::Induction {
            return Route::no("an induction whose claim is several sentences");
        }
        let (whole, prop) = match claim {
            [(_, prop)] => (names[0].clone(), prop.clone()),
            _ => {
                let parts = claim.iter().map(|(_, p)| p.clone()).collect();
                let Some(all) =
                    super::super::expr::joined(super::super::doc::Op::AND, parts, 36)
                else {
                    return Route::no("a claim of no sentences");
                };
                (format!("{}_all", names[0]), all)
            }
        };
        let Some(block_at) = self.rec.blocks.iter().position(|b| b.owner == i) else {
            return Route::no("a block the checker did not record");
        };
        let block = self.rec.blocks[block_at].clone();
        self.push_at(
            depth,
            Tactic::Have {
                name: whole.clone(),
                says: prop.clone(),
                proof: Box::new(super::super::doc::Proof::Block(Vec::new())),
            },
            step.line,
            spot.clone(),
        );
        let kept = self.writer.letters.clone();
        let kept_wholes = self.writer.wholes.clone();
        // The lines in scope as the block opens: a line one case or
        // direction says is no line of the next.
        let kept_lines = self.trees.clone();
        let parts: Vec<Option<usize>> = if step.parts.is_empty() {
            vec![None]
        } else {
            (0..step.parts.len()).map(Some).collect()
        };
        match method {
            Method::Proof | Method::Contradiction => {
                // A proof block opens the claim itself; a contradiction
                // opens by its supposition, which `by_contra` takes.
                self.opening_goal = (method == Method::Proof).then(|| OpeningGoal {
                    goal: prop.clone(),
                    from: self.lines.len(),
                    depth: depth + 1,
                });
                let opened = self.open(step, None, depth + 1);
                self.opening_goal = None;
                if let Route::Declined(d) = opened {
                    return Route::Declined(d);
                }
                let children: Vec<usize> = block.children.clone();
                if let Route::Declined(d) = self.steps(&children, depth + 1) {
                    return Route::Declined(d);
                }
                let closing = match self.closing(
                    children.last().copied(),
                    Owing::Written(block.ends_written(None)),
                ) {
                    Route::Built(c) => c,
                    Route::Declined(d) => return Route::Declined(d),
                };
                self.close(depth + 1, closing, step.line, spot.clone());
            }
            Method::Cases => {
                // The sentence, or the part of one, of the lines named that
                // says "or".
                // A "for all" line is read at the letters the cases assume,
                // as the checker reads it.
                let mut letters = std::collections::BTreeSet::new();
                for o in &step.openers {
                    for s in o.body(&self.thm.path).sentences() {
                        if let Some(n) = self.rec.page.get(&s) {
                            letters.extend(n.names());
                        }
                    }
                }
                let Some(said) = self
                    .cited_parts(&step.just.from)
                    .into_iter()
                    .map(|c| self.at_recorded_letter(&c, &letters).unwrap_or(c))
                    .find(|c| c.node.notation() == crate::notations::DISJUNCTION)
                else {
                    return Route::no("cases from no line that says \"or\"");
                };
                let source = said.proof.clone();
                let labels: Vec<String> = parts
                    .iter()
                    .map(|part| {
                        step.openers
                            .iter()
                            .find(|o| o.part == *part)
                            .map(|o| line_name(&o.label))
                            .unwrap_or_else(|| "_".to_string())
                    })
                    .collect();
                // The pattern follows the "or" as the page groups it: a ∨ b
                // ∨ c read from the left is (a ∨ b) ∨ c.
                // Cases that group the "or" otherwise, a ∨ b as one case of
                // a ∨ b ∨ c ∨ d, take it restated as the cases say it, each
                // case a part of an "or" read from the right.
                let mut names = labels.iter();
                let pattern = or_pattern(&said.node, &mut names);
                let line = if disjuncts(&said.node) == labels.len() {
                    Tactic::Rcases {
                        from: source.clone(),
                        pattern,
                    }
                } else {
                    let mut says = Vec::new();
                    for part in &parts {
                        let node =
                            step.openers.iter().find(|o| o.part == *part).and_then(
                                |o| {
                                    o.body(&self.thm.path)
                                        .sentences()
                                        .first()
                                        .and_then(|s| self.rec.page.get(s))
                                        .cloned()
                                },
                            );
                        let Some(node) = node else {
                            return Route::no("a case that assumes nothing");
                        };
                        match self.writer.formula(&node) {
                            Route::Built(p) => says.push(p),
                            Route::Declined(d) => return Route::Declined(d),
                        }
                    }
                    let restated = Tactic::Seq(vec![
                        Tactic::Fact(source.clone()),
                        super::super::tactics::call("tauto", vec![]),
                    ]);
                    Tactic::Rcases {
                        from: super::super::tactics::bracket(shown(
                            cases_said(says),
                            super::super::doc::Proof::By(restated),
                        )),
                        pattern: cases_pattern(&labels),
                    }
                };
                self.push_at(depth + 1, line, step.line, spot.clone());
                for (part, label) in parts.iter().zip(&labels) {
                    // Each case starts from the letters as the block found
                    // them: a letter one case lets is none of the next's.
                    self.writer.letters = kept.clone();
                    self.writer.wholes = kept_wholes.clone();
                    self.trees = kept_lines.clone();
                    self.named.insert(label.clone(), vec![label.clone()]);
                    // What the case assumes, for a step that cites it.
                    if let Some(o) = step.openers.iter().find(|o| o.part == *part) {
                        let nodes: Vec<Node> = o
                            .body(&self.thm.path)
                            .sentences()
                            .iter()
                            .filter_map(|s| self.rec.page.get(s).cloned())
                            .collect();
                        if let [node] = nodes.as_slice() {
                            let said = self.stated_here(node.clone(), label.clone());
                            self.store(o.label.clone(), vec![said]);
                        }
                    }
                    let children: Vec<usize> = block
                        .children
                        .iter()
                        .copied()
                        .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                        .collect();
                    self.push_at(
                        depth + 1,
                        Tactic::Bullet(Box::new(super::super::tactics::call(
                            "skip",
                            vec![],
                        ))),
                        step.line,
                        spot.clone(),
                    );
                    // The lines after the case's `by` line open its method's
                    // block: a supposition, or a proof block's lets.
                    let inner: Vec<crate::corpus::Opener> =
                        step.opening(*part).inner.into_iter().cloned().collect();
                    if let Route::Declined(d) = self.open_lines(step, &inner, depth + 2)
                    {
                        return Route::Declined(d);
                    }
                    if let Route::Declined(d) = self.steps(&children, depth + 2) {
                        return Route::Declined(d);
                    }
                    // A case that says it is the claim assumes what is owed,
                    // and has no steps.
                    let claimed =
                        step.openers.iter().any(|o| o.part == *part && o.is_claim);
                    let closing = match children.is_empty() && claimed {
                        true => Closing::Tactic(Box::new(Tactic::Exact(
                            super::super::tactics::hyp(label),
                        ))),
                        false => match self.closing(
                            children.last().copied(),
                            Owing::Written(block.ends_written(*part)),
                        ) {
                            Route::Built(c) => c,
                            Route::Declined(d) => return Route::Declined(d),
                        },
                    };
                    self.close(depth + 2, closing, step.line, spot.clone());
                }
            }
            Method::Induction => {
                if let Route::Declined(d) =
                    self.induction(step, &block, claimed, &parts, depth + 1)
                {
                    return Route::Declined(d);
                }
            }
            Method::BothDirections => {
                self.push_at(
                    depth + 1,
                    super::super::tactics::call("constructor", vec![]),
                    step.line,
                    spot.clone(),
                );
                // The goal of each direction, `A → B` of the claim `A ↔ B`
                // and then `B → A`, as `constructor` makes them.
                let directions = match &bare_term(&prop).kind {
                    super::super::doc::TermKind::Infix { op, lhs, rhs }
                        if op.symbol == "↔" =>
                    {
                        let implies = |a: &Printed, b: &Printed| {
                            Some(Printed::infix(
                                super::super::doc::Op::of("→")?,
                                a.clone(),
                                b.clone(),
                                super::super::doc::LeanType::Prop,
                            ))
                        };
                        implies(lhs, rhs)
                            .zip(implies(rhs, lhs))
                            .map(|(a, b)| [a, b])
                    }
                    _ => None,
                };
                for (k, part) in parts.iter().enumerate() {
                    self.trees = kept_lines.clone();
                    self.push_at(
                        depth + 1,
                        Tactic::Bullet(Box::new(super::super::tactics::call(
                            "skip",
                            vec![],
                        ))),
                        step.line,
                        spot.clone(),
                    );
                    self.opening_goal = directions.as_ref().and_then(|d| {
                        Some(OpeningGoal {
                            goal: d.get(k)?.clone(),
                            from: self.lines.len(),
                            depth: depth + 2,
                        })
                    });
                    let opened = self.open(step, *part, depth + 2);
                    self.opening_goal = None;
                    if let Route::Declined(d) = opened {
                        return Route::Declined(d);
                    }
                    let children: Vec<usize> = block
                        .children
                        .iter()
                        .copied()
                        .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                        .collect();
                    if let Route::Declined(d) = self.steps(&children, depth + 2) {
                        return Route::Declined(d);
                    }
                    let closing = match self.closing(
                        children.last().copied(),
                        Owing::Written(block.ends_written(*part)),
                    ) {
                        Route::Built(c) => c,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    self.close(depth + 2, closing, step.line, spot.clone());
                }
            }
            other => {
                return Route::no(format!(
                    "the method {} is not written in Lean yet",
                    other.as_str()
                ))
            }
        }
        self.writer.letters = kept;
        self.writer.wholes = kept_wholes;
        // A label the block gave again, its own `assume … (J)` beside the
        // block around it's, is that block's again once it closes, as the
        // checker reads the page (`tests/elaborator/a-label-given-again-
        // inside-a-block.proof`).
        for (label, said) in kept_lines {
            self.trees.insert(label, said);
        }
        if claim.len() > 1 {
            self.push_at(
                depth,
                Tactic::Obtain {
                    names: names.to_vec(),
                    says: None,
                    from: super::super::tactics::hyp(&whole),
                },
                step.line,
                spot,
            );
        }
        Route::Built(())
    }

    /// `induction`: "for all k ∈ ℕ₀" from 0 and "for all k ∈ ℕ" from 1 are
    /// `LeanBridges.Functions.le_induction` from 0 or 1 of the integer k; the step part's
    /// induction hypothesis keeps the page's label.
    pub(super) fn induction(
        &mut self,
        step: &Step,
        block: &crate::checker::record::Block,
        claimed: &Node,
        parts: &[Option<usize>],
        depth: usize,
    ) -> Route<()> {
        let spot = Self::step_spot(step);
        let [letter, set, body] = claimed.children.as_slice() else {
            return Route::no("an induction whose claim says no \"for all\"");
        };
        if claimed.notation() != crate::notations::FOR_ALL || !letter.is_name() {
            return Route::no("an induction whose claim says no \"for all\"");
        }
        let name = super::super::names::letter(&letter.text);
        let start = step.just.start.as_deref().unwrap_or("");
        if start == "∅" {
            return self.subset_induction(step, block, claimed, parts, depth);
        }
        let from_one = match (super::super::expr::system_of(set), start) {
            (Some(super::super::expr::System::NonNegative), "0") => false,
            (Some(super::super::expr::System::Positive), "1") => true,
            _ => return Route::no("an induction from other than the start of ℕ or ℕ₀"),
        };
        let system = match from_one {
            true => super::super::expr::System::Positive,
            false => super::super::expr::System::NonNegative,
        };
        self.writer.introduce(&letter.text, system);
        // The letter is an integer and its guard 0 < k or 0 ≤ k; the guard
        // put as `le_induction` reads it, 1 ≤ k or 0 ≤ k, in its place, so
        // that the induction hypothesis does not ask it again.
        let start = if from_one { 1 } else { 0 };
        let guard = format!("h_{name}");
        let int = super::super::doc::LeanType::Num(super::super::templates::Num::Int);
        let from = match super::super::expr::relation_of(
            "≤",
            Printed::numeral(start.to_string(), int.clone()),
            Printed::letter(name.clone(), int),
        ) {
            Route::Built(r) => r,
            Route::Declined(d) => return Route::Declined(d),
        };
        let lines = [
            Tactic::Intro(vec![name.clone(), guard.clone()]),
            Tactic::Replace {
                name: guard.clone(),
                says: from,
                proof: Box::new(super::super::doc::Proof::By(
                    super::super::tactics::call("omega", vec![]),
                )),
            },
            Tactic::Induction {
                on: vec![name.clone(), guard],
                using: super::super::tactics::bridge_lemma(
                    "LeanBridges.Functions.le_induction",
                    BridgeModule::Functions,
                ),
            },
        ];
        for line in lines {
            self.push_at(depth, line, step.line, spot.clone());
        }
        // The claim's body as the induction states it, written once: what a
        // part's lines teach the writer, a set they show finite, is no part
        // of the motive Lean made before them.
        let motive = match self.writer.formula(body) {
            Route::Built(m) => m,
            Route::Declined(d) => return Route::Declined(d),
        };
        // Each part starts from the lines in scope as the induction found
        // them: a line one part opens is no line of the next.
        let kept_lines = self.trees.clone();
        for part in parts {
            self.trees = kept_lines.clone();
            let marker = part
                .and_then(|k| step.parts.get(k))
                .map(|(m, _)| m.as_str())
                .unwrap_or("");
            let openers: Vec<&crate::corpus::Opener> =
                step.openers.iter().filter(|o| o.part == *part).collect();
            match marker {
                "base" => {
                    self.push_at(
                        depth,
                        Tactic::Alternative("base".to_string()),
                        step.line,
                        spot.clone(),
                    );
                }
                "step" => {
                    let hypothesis = openers
                        .iter()
                        .find(|o| o.is_hypothesis)
                        .map(|o| line_name(&o.label))
                        .unwrap_or_else(|| "IH".to_string());
                    if let Some(o) = openers.iter().find(|o| o.is_hypothesis) {
                        self.named.insert(o.label.clone(), vec![hypothesis.clone()]);
                        let said = self.stated_here(body.clone(), hypothesis.clone());
                        self.store(o.label.clone(), vec![said]);
                    }
                    let letter_line = openers
                        .iter()
                        .find(|o| !o.is_hypothesis && o.kind == Intro::Let);
                    let guard = letter_line
                        .map(|o| line_name(&o.label))
                        .unwrap_or_else(|| format!("h_{name}"));
                    // The letter's line, `j ∈ ℕ` or `j ∈ ℕ₀`, which Lean
                    // writes `0 < j` or `0 ≤ j`, from the case's guard,
                    // `1 ≤ j` or `0 ≤ j`.
                    if let Some(o) = letter_line {
                        if let Some(node) = self.opener_node(o) {
                            let h = super::super::tactics::hyp(&guard);
                            let proof = match from_one {
                                true => Printed::applied(
                                    "lt_of_lt_of_le",
                                    super::super::doc::Source::Mathlib,
                                    vec![
                                        Printed::constant(
                                            "zero_lt_one",
                                            super::super::doc::Source::Mathlib,
                                            super::super::doc::LeanType::Prop,
                                        ),
                                        h,
                                    ],
                                    super::super::doc::LeanType::Prop,
                                ),
                                false => h,
                            };
                            self.store(
                                o.label.clone(),
                                vec![LineSentence {
                                    at: 0,
                                    node,
                                    name: None,
                                    proof,
                                    says: None,
                                }],
                            );
                        }
                    }
                    let case = format!("succ {name} {guard} {hypothesis}");
                    self.push_at(
                        depth,
                        Tactic::Alternative(case),
                        step.line,
                        spot.clone(),
                    );
                }
                other => return Route::no(format!("an induction part {other:?}")),
            }
            // A case proved by its own `proof` block: its lines, other than
            // the induction's letter and hypothesis, are opened as a
            // `proof` block's are.
            let own: Vec<crate::corpus::Opener> = openers
                .iter()
                .filter(|o| !o.is_hypothesis)
                .filter(|o| !self.introduces_letter(o, &letter.text))
                .map(|o| (*o).clone())
                .collect();
            // The part's goal is the motive Lean makes at the start or at
            // k + 1, the cast of the letter a cast of that value, `↑(k + 1)`;
            // its own lines open it (`opening_goal`) and take off it what
            // their intros take.
            let int =
                super::super::doc::LeanType::Num(super::super::templates::Num::Int);
            let at = match marker {
                "base" => Printed::numeral(start.to_string(), int),
                _ => Printed::infix(
                    super::super::doc::Op::PLUS,
                    Printed::letter(name.clone(), int.clone()),
                    Printed::numeral("1".to_string(), int.clone()),
                    int,
                ),
            };
            let goal = super::super::doc::forms::substituted(&motive, &name, &at);
            let opened_from = self.lines.len();
            self.opening_goal = Some(OpeningGoal {
                goal: goal.clone(),
                from: opened_from,
                depth: depth + 1,
            });
            let opened = self.open_lines(step, &own, depth + 1);
            self.opening_goal = None;
            if let Route::Declined(d) = opened {
                return Route::Declined(d);
            }
            // The binders the part's own lines took off its goal.
            let introduced: usize = self.lines[opened_from..]
                .iter()
                .filter(|l| l.depth == depth + 1)
                .map(|l| match &l.tactic {
                    Tactic::Intro(names) => names.len(),
                    _ => 0,
                })
                .sum();
            let children: Vec<usize> = block
                .children
                .iter()
                .copied()
                .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                .collect();
            if let Route::Declined(d) = self.steps(&children, depth + 1) {
                return Route::Declined(d);
            }
            let Some(goal) = goal_after_intros(&goal, introduced) else {
                return Route::no(format!(
                    "an induction part whose lines take off its goal what Lean does not, {}",
                    goal.text()
                ));
            };
            let owing = Owing::Lean {
                nodes: block.ends_written(*part),
                goal: vec![goal],
            };
            let closing = match self.closing(children.last().copied(), owing) {
                Route::Built(c) => c,
                Route::Declined(d) => return Route::Declined(d),
            };
            self.close(depth + 1, closing, step.line, spot.clone());
        }
        Route::Built(())
    }

    /// `induction on Y starting at ∅` of "for all Y ⊆ X": the parts of a
    /// finite X, `LeanBridges.Sets.subset_induction`, X's finiteness from
    /// why it is (`finite_proof`). The base is ∅; the step lets Y ⊆ X,
    /// assumes the claim of Y under the page's label, and opens its own
    /// lines, a ∈ X ∖ Y, before proving it of Y ∪ {a}.
    pub(super) fn subset_induction(
        &mut self,
        step: &Step,
        block: &crate::checker::record::Block,
        claimed: &Node,
        parts: &[Option<usize>],
        depth: usize,
    ) -> Route<()> {
        use super::super::tactics as t;
        let spot = Self::step_spot(step);
        let ([letter, set, body], crate::notations::FOR_ALL) =
            (claimed.children.as_slice(), claimed.notation())
        else {
            return Route::no("an induction on a set whose claim says no \"for all\"");
        };
        let (POWERSET, [whole]) = (set.notation(), set.children.as_slice()) else {
            return Route::no("an induction on a set of other than the parts of a set");
        };
        let Some(members) = self.writer.members_of(whole) else {
            return Route::no("an induction on the parts of a set of no Lean type");
        };
        let name = super::super::names::letter(&letter.text);
        self.writer
            .letters
            .insert(letter.text.to_string(), LetterType::Set(members));
        let open = || {
            Printed::of(
                super::super::doc::TermKind::Open,
                super::super::doc::LeanType::Prop,
            )
        };
        // X's finiteness from why the checker says it is (`finite_proof`).
        let Some(finite) = self.finite_proof(whole) else {
            return Route::no("an induction on the parts of a set not shown finite");
        };
        let induction = Printed::applied(
            "LeanBridges.Sets.subset_induction",
            super::super::doc::Source::Bridge(BridgeModule::Sets),
            vec![finite, open(), open()],
            super::super::doc::LeanType::Prop,
        );
        self.push_at(
            depth,
            t::call("refine", vec![TacticArg::Term(induction)]),
            step.line,
            spot.clone(),
        );
        // Each part starts from the lines in scope as the induction found
        // them, as `induction`'s parts do.
        let kept_lines = self.trees.clone();
        for part in parts {
            self.trees = kept_lines.clone();
            let marker = part
                .and_then(|k| step.parts.get(k))
                .map(|(m, _)| m.as_str())
                .unwrap_or("");
            let openers: Vec<crate::corpus::Opener> = step
                .openers
                .iter()
                .filter(|o| o.part == *part)
                .cloned()
                .collect();
            let first = match marker {
                "base" => t::call("skip", vec![]),
                "step" => {
                    let guard = openers
                        .iter()
                        .find(|o| self.lets_part_letter(o, &letter.text))
                        .cloned();
                    let hypothesis = openers.iter().find(|o| o.is_hypothesis).cloned();
                    let (Some(guard), Some(hypothesis)) = (guard, hypothesis) else {
                        return Route::no(
                            "an induction step on a set with no letter or hypothesis",
                        );
                    };
                    let (guard_name, ih_name) =
                        (line_name(&guard.label), line_name(&hypothesis.label));
                    if let Some(n) = self.opener_node(&guard) {
                        self.named
                            .insert(guard.label.clone(), vec![guard_name.clone()]);
                        let said = self.stated_here(n, guard_name.clone());
                        self.store(guard.label.clone(), vec![said]);
                    }
                    self.named
                        .insert(hypothesis.label.clone(), vec![ih_name.clone()]);
                    let said = self.stated_here(body.clone(), ih_name.clone());
                    self.store(hypothesis.label.clone(), vec![said]);
                    Tactic::Intro(vec![name.clone(), guard_name, ih_name])
                }
                other => return Route::no(format!("an induction part {other:?}")),
            };
            self.push_at(
                depth,
                Tactic::Bullet(Box::new(first)),
                step.line,
                spot.clone(),
            );
            let own: Vec<crate::corpus::Opener> = openers
                .into_iter()
                .filter(|o| !o.is_hypothesis && !self.lets_part_letter(o, &letter.text))
                .collect();
            if let Route::Declined(d) = self.open_lines(step, &own, depth + 1) {
                return Route::Declined(d);
            }
            let children: Vec<usize> = block
                .children
                .iter()
                .copied()
                .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                .collect();
            // The base's ∅ is the part of X the letter was: a set of what
            // X holds, ∏(x ∈ ∅) c of members of X.
            let empty_was = self.writer.empty_of.clone();
            if marker == "base" {
                self.writer.empty_of = self.writer.members_of(whole);
            }
            let written = self.steps(&children, depth + 1);
            self.writer.empty_of = empty_was;
            if let Route::Declined(d) = written {
                return Route::Declined(d);
            }
            let closing = match self.closing(
                children.last().copied(),
                Owing::Written(block.ends_written(*part)),
            ) {
                Route::Built(c) => c,
                Route::Declined(d) => return Route::Declined(d),
            };
            self.close(depth + 1, closing, step.line, spot.clone());
        }
        Route::Built(())
    }

    /// Whether an opening line lets the letter of an induction on parts,
    /// `Y ⊆ X`.
    pub(super) fn lets_part_letter(
        &self,
        o: &crate::corpus::Opener,
        letter: &str,
    ) -> bool {
        !o.is_hypothesis
            && self.opener_node(o).is_some_and(|n| {
                n.notation() == SUBSET
                    && n.children.first().is_some_and(|y| &*y.text == letter)
            })
    }

    /// A function or map given a letter of "for all f : X → Y": the value
    /// as Lean writes it, where it is of the type the quantifier gives f.
    pub(super) fn function_given(
        &self,
        writer: &Writer,
        value: &Node,
        from: &Node,
        to: &Node,
    ) -> Route<Printed> {
        match writer.function_between(from, to) {
            Some(LetterType::Function { from, to }) => {
                match writer.function_type(value) {
                    Route::Built(t) if t == (from, to) => {
                        writer.function_printed(value)
                    }
                    Route::Built(_) => {
                        Route::no("a function given for one of other types")
                    }
                    Route::Declined(d) => Route::Declined(d),
                }
            }
            Some(wanted @ LetterType::Map { .. }) => {
                match writer.letters.get(&*value.text) {
                    Some(ty) if value.is_name() && *ty == wanted => {
                        Route::Built(Printed::letter(
                            super::super::names::letter(&value.text),
                            ty.lean_type(),
                        ))
                    }
                    _ => Route::no("a map given for one of other types"),
                }
            }
            _ => Route::no("a function given between sets of no Lean type"),
        }
    }

    /// What an opening line says, as the checker read it.
    pub(super) fn opener_node(&self, o: &crate::corpus::Opener) -> Option<Node> {
        o.body(&self.thm.path)
            .sentences()
            .first()
            .and_then(|s| self.rec.page.get(s))
            .cloned()
    }

    /// Whether an opening line is the `let` of a letter, the induction's.
    pub(super) fn introduces_letter(
        &self,
        o: &crate::corpus::Opener,
        letter: &str,
    ) -> bool {
        o.kind == Intro::Let
            && o.body(&self.thm.path)
                .sentences()
                .iter()
                .filter_map(|s| self.rec.page.get(s))
                .any(|n| introduces(n).is_some_and(|(l, _)| l == letter))
    }

    /// The lines that open a `proof` or `contradiction` block: each `let`
    /// introduces its letter, each `assume` its fact, and a `suppose` the
    /// opposite of the claim.
    pub(super) fn open(
        &mut self,
        step: &Step,
        part: Option<usize>,
        depth: usize,
    ) -> Route<()> {
        let openers: Vec<crate::corpus::Opener> = step
            .openers
            .iter()
            .filter(|o| o.part == part)
            .cloned()
            .collect();
        self.open_lines(step, &openers, depth)
    }

    /// The opening lines given, each introduced as `open` introduces it.
    pub(super) fn open_lines(
        &mut self,
        step: &Step,
        openers: &[crate::corpus::Opener],
        depth: usize,
    ) -> Route<()> {
        let spot = Self::step_spot(step);
        for o in openers {
            let label = line_name(&o.label);
            self.named.insert(o.label.clone(), vec![label.clone()]);
            let body = o.body(&self.thm.path);
            let mut nodes: Vec<Node> = body
                .sentences()
                .iter()
                .filter_map(|s| self.rec.page.get(s).cloned())
                .collect();
            // A `let` the page does not read as a formula, `let X ⊆ A`, says
            // what the checker reads it to assert.
            if nodes.is_empty() {
                nodes = self
                    .rec
                    .opener_asserted
                    .get(&o.line)
                    .cloned()
                    .unwrap_or_default();
            }
            // `let X be a set`, which asserts nothing: the letter, typed by
            // its sort as a theorem's own `let X be a set` is
            // (`set_letter_type`), as "for all sets X" gives it.
            if o.kind == Intro::Let && nodes.is_empty() {
                use crate::sorts::introduction::{Form, Introduction};
                let Form::Set(name) = Introduction::read(body.clone()).form else {
                    return Route::no("a let that is no formula and lets no set");
                };
                let Some(ty) = super::super::sets::set_type_in(
                    Some(&self.rec.sorts),
                    &self.rec.thing_types,
                    &name,
                ) else {
                    return Route::no(format!("{name}, a set whose sort is no set's"));
                };
                self.writer.letters.insert(name.clone(), ty);
                self.intro(
                    depth,
                    vec![super::super::names::letter(&name)],
                    o.line,
                    &spot,
                );
                continue;
            }
            match o.kind {
                Intro::Let => {
                    for node in &nodes {
                        if let Some(letter) =
                            super::super::statement::range_letter(node)
                        {
                            // In ℕ or ℕ₀ where the range starts at 1 or 0.
                            let system = match node.children.get(1) {
                                Some(range) => {
                                    super::super::expr::range_letter_system(range)
                                }
                                None => super::super::expr::System::Type(
                                    super::super::templates::Num::Int,
                                ),
                            };
                            self.writer.introduce(&letter, system);
                            let letter = super::super::names::letter(&letter);
                            // The range the goal's "for all" puts the letter
                            // in, as Lean states it.
                            let in_range = self.next_guard().is_some_and(|g| {
                                g.walk().iter().any(|c| {
                                    matches!(&c.kind, super::super::doc::TermKind::Const(k)
                                        if k.name == "Finset.Icc")
                                })
                            });
                            self.store(
                                o.label.clone(),
                                vec![LineSentence::only(node.clone(), label.clone())],
                            );
                            self.intro(
                                depth,
                                vec![letter.clone(), label.clone()],
                                o.line,
                                &spot,
                            );
                            // The range's bounds beside it, which linear
                            // arithmetic reads, the membership kept for the
                            // items given it: where the goal puts the letter
                            // in a range, not where it states the bounds.
                            if in_range {
                                let bounds = Printed::applied(
                                    "Finset.mem_Icc.mp",
                                    super::super::doc::Source::Mathlib,
                                    vec![super::super::tactics::hyp(&label)],
                                    super::super::doc::LeanType::Prop,
                                );
                                self.push_at(
                                    depth,
                                    Tactic::Name {
                                        name: format!("{label}_bounds"),
                                        term: bounds,
                                    },
                                    o.line,
                                    spot.clone(),
                                );
                            }
                            continue;
                        }
                        if let Some((letter, ty)) =
                            super::super::statement::introduces_function(
                                &self.writer,
                                node,
                            )
                        {
                            self.writer.letters.insert(letter.clone(), ty);
                            super::super::statement::record_domain(
                                &mut self.writer,
                                node,
                            );
                            self.intro(
                                depth,
                                vec![super::super::names::letter(&letter)],
                                o.line,
                                &spot,
                            );
                            continue;
                        }
                        // `let f : X → Y` between sets: the map and the fact
                        // that it maps X into Y, as "for all f : X → Y" gives
                        // them (`quantified_over_functions`).
                        if let (crate::notations::FUNCTION_TYPE, [f, from, to]) =
                            (node.notation(), node.children.as_slice())
                        {
                            if let (true, Some(ty)) =
                                (f.is_name(), self.writer.function_between(from, to))
                            {
                                self.writer.letters.insert(f.text.to_string(), ty);
                                self.store(
                                    o.label.clone(),
                                    vec![LineSentence::only(
                                        node.clone(),
                                        label.clone(),
                                    )],
                                );
                                self.intro(
                                    depth,
                                    vec![
                                        super::super::names::letter(&f.text),
                                        label.clone(),
                                    ],
                                    o.line,
                                    &spot,
                                );
                                continue;
                            }
                        }
                        // `let t ∈ S` of a set S: the member and the fact
                        // that it is one, as "for all t ∈ S" gives them.
                        // `let X ⊆ A` likewise gives a set and the fact.
                        if let [t, set] = node.children.as_slice() {
                            let member = node.notation()
                                == crate::notations::MEMBERSHIP
                                && t.is_name();
                            let part = node.notation() == SUBSET && t.is_name();
                            let ty = match (member, part) {
                                (true, _) => {
                                    self.writer.members_of(set).map(|m| m.letter())
                                }
                                (_, true) => {
                                    self.writer.set_members(set).map(LetterType::Set)
                                }
                                _ => None,
                            };
                            if let Some(ty) = ty {
                                self.writer.letters.insert(t.text.to_string(), ty);
                                self.store(
                                    o.label.clone(),
                                    vec![LineSentence::only(
                                        node.clone(),
                                        label.clone(),
                                    )],
                                );
                                self.intro(
                                    depth,
                                    vec![
                                        super::super::names::letter(&t.text),
                                        label.clone(),
                                    ],
                                    o.line,
                                    &spot,
                                );
                                continue;
                            }
                        }
                        let Some((letter, system)) = introduces(node) else {
                            return Route::no(
                                "a let that introduces no letter of a number system",
                            );
                        };
                        self.writer.introduce(&letter, system);
                        let letter = super::super::names::letter(&letter);
                        if !matches!(system, super::super::expr::System::Type(_)) {
                            self.store(
                                o.label.clone(),
                                vec![LineSentence::only(node.clone(), label.clone())],
                            );
                            self.intro(
                                depth,
                                vec![letter.clone(), label.clone()],
                                o.line,
                                &spot,
                            );
                        } else {
                            self.intro(depth, vec![letter.clone()], o.line, &spot);
                        }
                    }
                }
                Intro::Assume => {
                    // A line of several sentences is the "and" of them,
                    // each sentence taken by its projection. One sentence
                    // says what the goal the part opens assumes there, as
                    // Lean states it (`assumed_here`).
                    let n = nodes.len();
                    let side = self.assumed_here().filter(|_| n == 1);
                    let said = nodes
                        .iter()
                        .enumerate()
                        .map(|(k, node)| LineSentence {
                            at: k,
                            node: node.clone(),
                            name: None,
                            proof: fields(
                                super::super::tactics::hyp(&label),
                                &projection_path(k, n),
                            ),
                            says: side.clone(),
                        })
                        .collect();
                    self.store(o.label.clone(), said);
                    self.intro(depth, vec![label.clone()], o.line, &spot);
                }
                Intro::Suppose => {
                    let Some(node) = nodes.first() else {
                        return Route::no("a suppose the checker did not read");
                    };
                    let says = match self.writer.formula(node) {
                        Route::Built(s) => s,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    let said = LineSentence {
                        says: Some(says.clone()),
                        ..LineSentence::only(node.clone(), label.clone())
                    };
                    self.store(o.label.clone(), vec![said]);
                    if let Route::Declined(d) =
                        self.suppose(&label, says, o.line, &spot, depth)
                    {
                        return Route::Declined(d);
                    }
                }
            }
        }
        Route::Built(())
    }

    /// A contradiction's `suppose` line, named `label`: the claim denied,
    /// `by_contra`, where the supposition is the claim negated, and the
    /// negation's body taken, `intro`, where the claim is the supposition
    /// negated. The hypothesis is the supposition as the page writes it:
    /// named as it comes where Lean writes the two alike, ascribed where
    /// they differ by a `≠` read as `¬ =`, and turned round where the page
    /// writes its equation the other way.
    pub(super) fn suppose(
        &mut self,
        label: &str,
        says: Printed,
        line: usize,
        spot: &Spot,
        depth: usize,
    ) -> Route<()> {
        use super::super::doc::forms::{self, Meets};
        use super::super::doc::LeanType;
        let Some(supposition) = self.rec.supposed.get(&line) else {
            return Route::no("a supposition the checker relates to no claim");
        };
        let shown = match self.writer.formula(&supposition.against) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let (open, given) = match supposition.shape {
            Supposed::ClaimDenied => ("by_contra", Some(forms::negation(&shown))),
            Supposed::Denial => ("intro", forms::denied(&shown)),
        };
        let Some(given) = given else {
            return Route::no(format!(
                "a claim that denies its supposition, which Lean writes as no negation, {}",
                shown.text()
            ));
        };
        let opening = |name: Printed| {
            super::super::tactics::call(open, vec![TacticArg::Term(name)])
        };
        // How the supposition meets what the block denies is the checker's
        // (`Supposition::meeting`); Lean's own writing of the two decides
        // only whether the hypothesis is ascribed the page's words.
        let met = &supposition.meeting;
        if met.permuted || !met.identities.is_empty() {
            return Route::no(format!(
                "the supposition {}, met with what `{open}` gives, {}, as {met:?}",
                says.text(),
                given.text()
            ));
        }
        let shape = match (met.turned, forms::written_alike(&given, &says)) {
            (true, _) => Some(Meets::Turned {
                negated: forms::denies_equation(&given),
            }),
            (false, true) => Some(Meets::Same),
            (false, false) => Some(Meets::Unfolded),
        };
        match shape {
            Some(Meets::Same) => {
                self.push_at(
                    depth,
                    opening(super::super::tactics::hyp(label)),
                    line,
                    spot.clone(),
                );
            }
            Some(Meets::Unfolded) => {
                let given = ascribed(super::super::tactics::hyp(label), says);
                self.push_at(depth, opening(given), line, spot.clone());
            }
            Some(Meets::Turned { negated }) => {
                let given_name = format!("h_{label}");
                let given = super::super::tactics::hyp(&given_name);
                let turned = match negated {
                    false => super::super::tactics::symm(given),
                    true => Printed::applied(
                        "Ne.symm",
                        super::super::doc::Source::Core,
                        vec![given],
                        LeanType::Prop,
                    ),
                };
                self.push_at(
                    depth,
                    opening(super::super::tactics::hyp(&given_name)),
                    line,
                    spot.clone(),
                );
                self.push_at(
                    depth,
                    Tactic::Have {
                        name: label.to_string(),
                        says,
                        proof: Box::new(super::super::doc::Proof::Term(turned)),
                    },
                    line,
                    spot.clone(),
                );
            }
            Some(
                Meets::Identities(_)
                | Meets::Ranges
                | Meets::Universe { .. }
                | Meets::Casts { .. },
            )
            | None => {
                return Route::no(format!(
                    "the supposition {}, which is not what `{open}` gives, {}",
                    says.text(),
                    given.text()
                ))
            }
        }
        Route::Built(())
    }
}
