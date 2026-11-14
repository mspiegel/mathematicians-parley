//! Defines, recursion values and indexed values.

use super::*;

impl<'a> Elaborator<'a> {
    /// The proof of one link of a chain, from what it cites.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn link_held(
        &mut self,
        step: &Step,
        line: &ChainLine,
        claim: &Term,
        written: &str,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        defines: &BTreeSet<String>,
    ) -> Checked<Proof> {
        let cite = line.cite.as_str();
        let link_line = line.line;
        let what = format!("a link of step {} claims {written}", step.number);
        // A line giving a reason of its own proves its link as the step it
        // would be, resting on the calculation's requires lines, as a
        // requires line is proved (`as_a_step`).
        if let Some(req) = &line.reason {
            let supplied = self.supplied(Some(step), scope, facts)?;
            let held = match self.as_a_step(step, req, &what, scope, &supplied)? {
                Built(p) => p,
                Declined(d) => {
                    return Err(self.defect(
                        line.line,
                        format!(
                            "{written} does not follow by {cite}: {}",
                            self.say(&d)
                        ),
                    ));
                }
            };
            let node = self.read_one(&req.fact)?;
            let proved = self.term(&node)?;
            let wanted = self.rpn(claim);
            if proved == wanted {
                return Ok(held);
            }
            // A chain going down is built going up (`Chain::upward`), so
            // the reason proves an equation of it the other way round from
            // the link built.
            let said = self.to_term(&proved);
            if said.label() == Some("wceq") {
                let (was, now) =
                    (self.rpn(&said.children()[0]), self.rpn(&said.children()[1]));
                if t!(now, was, "wceq") == wanted {
                    return Ok(pf!(self.b; scope, was, now, held, "eqcomd"));
                }
            }
            return Err(self.unreached(
                line.line,
                format!("the reason of {written} proves a formula other than the link"),
            ));
        }
        // A link of numerals alone may name `arithmetic` rather than a line,
        // and is worked out whole where arithmetic works out everything in
        // it. One holding an operation it does not work out, 2! = (1 + 1)!,
        // is read as a link with letters is, a piece at a time.
        let pieces =
            claim.label() == Some("wceq") && field::decide_closed(claim).is_declined();
        if cite == "arithmetic" && claim.names().is_empty() && !pieces {
            return self.closed_fact(&self.rpn(claim), scope, facts, &what, Some(step));
        }
        // A closed link naming `real arithmetic` is worked out whole; one
        // whose terms have letters changes closed pieces alone, which the
        // checker holds it to, each worked out where it stands.
        if cite == "real arithmetic" {
            if claim.names().is_empty() {
                return self.real_fact(&self.rpn(claim), scope, facts, &what);
            }
            if claim.label() != Some("wceq") {
                return Err(self.unreached(
                    step.line,
                    format!("{written} relates terms with letters in them, which real arithmetic does not"),
                ));
            }
            let leaf = Leaf::RealArithmetic { what };
            return match self.congruence(
                &claim.children()[0],
                &claim.children()[1],
                scope,
                facts,
                Some(step),
                &leaf,
            )? {
                Built(p) => Ok(p),
                Declined(d) => Err(self.defect(
                    step.line,
                    format!(
                        "{written} changes more than closed pieces: {}",
                        self.say(&d)
                    ),
                )),
            };
        }
        // One whose terms have letters in them may too, where only pieces of
        // numerals alone change.
        if cite == "arithmetic" {
            if claim.label() != Some("wceq") {
                return Err(self.unreached(
                    step.line,
                    format!("{written} relates terms with letters in them, which arithmetic does not"),
                ));
            }
            let leaf = Leaf::Arithmetic {
                what,
                step: Box::new(step.clone()),
            };
            return match self.congruence(
                &claim.children()[0],
                &claim.children()[1],
                scope,
                facts,
                Some(step),
                &leaf,
            )? {
                Built(p) => Ok(p),
                Declined(d) => Err(self.defect(
                    step.line,
                    format!("{written} changes more than numerals: {}", self.say(&d)),
                )),
            };
        }
        let line = self
            .line_written(cite, lines)
            .unwrap_or_else(|| panic!("no line {cite} cited"));
        let wanted = self.rpn(claim);
        // A define says what its name is, and a link citing it says what that
        // comes to somewhere: the standard form reads the name as its rule.
        if defines.contains(cite) && line.claim != wanted {
            return match self.define_makes(step, &wanted, scope, facts)? {
                Built(p) => Ok(p),
                Declined(d) => Err(self.defect(
                    step.line,
                    format!("{written} is not what {cite} makes it: {}", self.say(&d)),
                )),
            };
        }
        let proof = self.carried(cite, facts, lines);
        if line.claim == wanted {
            return Ok(proof);
        }
        // A line may say several things, and the link be one of them
        // (`line_says`): the one the checker found it in
        // (`CheckedTheorem::link_places`), matched to what the line says in
        // set.mm up to a renamed bound variable.
        let says = self.line_says(cite, scope, facts, lines)?;
        let Some(at) = self.checked.link_places.get(&link_line).cloned() else {
            return Err(self.defect(
                step.line,
                format!("the checker recorded no place in {cite} for {written}"),
            ));
        };
        let recorded = self.recorded_statement(&at)?;
        let known = Facts::new();
        for (said_as, held) in says.entries() {
            let same = said_as == recorded
                || self
                    .renaming(&self.to_term(&recorded), &self.to_term(&said_as))?
                    .is_some();
            if same {
                self.know(&known, said_as, held);
            }
        }
        if known.entries().is_empty() {
            return Err(self.defect(
                step.line,
                format!(
                    "the checker found {written} in {cite}, which says nothing it read there"
                ),
            ));
        }
        for (said_as, held) in known.entries() {
            if said_as == wanted {
                return Ok(held);
            }
            let said = self.to_term(&said_as);
            if said.label() == Some("wceq") {
                let (was, now) =
                    (self.rpn(&said.children()[0]), self.rpn(&said.children()[1]));
                if t!(now, was, "wceq") == wanted {
                    return Ok(pf!(self.b; scope, was, now, held, "eqcomd"));
                }
            }
        }
        // Or one of them with an identity element written that the link
        // leaves out, or the other way about (`SYNTAX.md`).
        let bare =
            |me: &Self, rpn: &Rpn| me.rpn(&me.without_identities(&me.to_term(rpn)));
        let goal = bare(self, &wanted);
        let turned = self.turned_claim(&wanted);
        for (said_as, held) in known.entries() {
            if bare(self, &said_as) == goal {
                if let Some(p) = self.tidied(&held, &said_as, &wanted, scope, facts)? {
                    return Ok(p);
                }
            }
            let Some((turned, flip)) = &turned else {
                continue;
            };
            if bare(self, &said_as) == bare(self, turned) {
                if let Some(p) = self.tidied(&held, &said_as, turned, scope, facts)? {
                    let Sides { left, right } = self.equation_sides(turned);
                    return Ok(pf!(self.b; scope, left, right, p, *flip));
                }
            }
        }
        // Or one of them with two sides its notation puts in no order the
        // other way round: c ≡ b (mod n) for a link from b to c. The lemma
        // that exchanges them asks that each side is a number, which the
        // step's requires lines may be what say.
        let offered = facts.with(&self.supplied(Some(step), scope, facts)?);
        for (said_as, held) in known.entries() {
            let alike = self.same(
                &self.to_term(&said_as),
                &self.to_term(&wanted),
                scope,
                &offered,
                Some(step),
            )?;
            if let Built(alike) = alike {
                return Ok(pf!(self.b; scope, said_as, wanted, held, alike, "mpbid"));
            }
        }
        Err(self.defect(step.line, format!("{cite} does not say {written}")))
    }

    /// An equation a define the step cites makes, `wanted`, as a link
    /// citing the define reads it (`SYNTAX.md`, a step may cite a define):
    /// the define's own equation, either way round and over another bound
    /// letter, as a define of a count read its index before the step's lines
    /// took theirs; or two sides the standard form reads as one, the name
    /// read as its rule.
    pub(super) fn define_makes(
        &mut self,
        step: &Step,
        wanted: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let supplied = self.supplied(Some(step), scope, facts)?;
        let known = self.with_cited(Some(step), scope, &supplied, None)?;
        if let Some(p) = self.held_rebound(&known, wanted, scope)? {
            return Ok(Built(p));
        }
        if let Some((turned, flip)) = self.turned_claim(wanted) {
            if let Some(p) = self.held_rebound(&known, &turned, scope)? {
                let Sides { left, right } = self.equation_sides(&turned);
                return Ok(Built(pf!(self.b; scope, left, right, p, flip)));
            }
        }
        let claim = self.to_term(wanted);
        let offered = facts.with(&known);
        self.same(
            &claim.children()[0],
            &claim.children()[1],
            scope,
            &offered,
            Some(step),
        )
    }

    /// A step citing a define: the name, applied or not, is its value, and
    /// where that is a rule by cases the lines the step cites say which case.
    pub(super) fn by_define(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let whole = self.to_term(term);
        if whole.label() == Some("wfn") {
            let supplied = self.supplied(Some(step), scope, facts)?;
            let held = self.with_cited(Some(step), scope, &supplied, None)?;
            return self.define_on(&whole, scope, &held);
        }
        if whole.label() != Some("wceq") {
            return Err(self.unreached(
                step.line,
                format!(
                    "{} is cited for a claim that is no equation",
                    step.just
                        .defined
                        .clone()
                        .unwrap_or_else(|| "None".to_string())
                ),
            ));
        }
        let (a, b) = (whole.children()[0].clone(), whole.children()[1].clone());
        // A define standing inside a side, as ∫(0 to 1) p(t) dt holds p, is
        // read where it stands, as a calculation's link citing it is.
        if !self.names_define_at_head(&a) && !self.names_define_at_head(&b) {
            return self.define_makes(step, term, scope, facts);
        }
        let supplied = self.supplied(Some(step), scope, facts)?;
        let held = self.with_cited(Some(step), scope, &supplied, None)?;
        self.equation_by_define(step, &a, &b, scope, &held)
    }

    /// Whether `one` is a defined name or a defined function applied, which
    /// `define_value` reads.
    pub(super) fn names_define_at_head(&mut self, one: &Term) -> bool {
        let letters = self.letters_bound(one);
        let kept = std::mem::replace(&mut self.binding, letters);
        let head = self.standard_step(one);
        self.binding = kept;
        head.is_some_and(|(h, _)| {
            matches!(
                h,
                super::super::matcher::How::Defined
                    | super::super::matcher::How::Applied
            )
        })
    }

    /// ( scope -> a = b ) where one side is a defined name, applied or not,
    /// and the other its value, as the define says it; a decline where
    /// neither side names a define whose value is the other.
    pub(super) fn equation_by_define(
        &mut self,
        step: &Step,
        a: &Term,
        b: &Term,
        scope: &Rpn,
        held: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut why: Option<crate::outcome::Decline> = None;
        for (one, other, turned) in [(a, b, false), (b, a, true)] {
            let reached = self.define_value(one, scope, held)?;
            let (value, mut proof) = match reached {
                Built(r) => r,
                Declined(d) => {
                    // What the side naming a define says, over the other's.
                    if why.as_ref().is_none_or(|w| w.reason() == NAMES_NO_DEFINE) {
                        why = Some(d);
                    }
                    continue;
                }
            };
            if self.rpn(&value) != self.rpn(other) {
                match self.same(&value, other, scope, held, Some(step))? {
                    Declined(d) => {
                        why = Some(d);
                        continue;
                    }
                    Built(alike) => {
                        proof = self.b.ap(
                            "eqtrd",
                            &binds! {"ph" => scope, "A" => self.rpn(one), "B" => self.rpn(&value), "C" => self.rpn(other)},
                            &[&proof, &alike],
                        );
                    }
                }
            }
            if !turned {
                return Ok(Built(proof));
            }
            return Ok(Built(self.b.ap(
                "eqcomd",
                &binds! {"ph" => scope, "A" => self.rpn(one), "B" => self.rpn(other)},
                &[&proof],
            )));
        }
        Ok(Declined(
            why.expect("a reason one of the two sides declined"),
        ))
    }

    /// ( scope -> t Fn A ) for a function a define gives on A: the map is a
    /// function on its domain where each value its rule gives is a set
    /// (`mptfng`), and the define's equation carries that to its name
    /// (`fneq1d`), for a step citing the define and for a `requires` line
    /// resting on it. `ELABORATION.md`, "A defined function is a map".
    pub fn define_on(
        &mut self,
        whole: &Term,
        scope: &Rpn,
        held: &Facts,
    ) -> Checked<Route<Proof>> {
        let name = whole.children()[0].clone();
        let (map, is_map) = take!(self.define_value(&name, scope, held)?);
        if map.label() != Some("cmpt") || map.children().len() != 3 {
            return Ok(Route::no(
                "what is claimed a function is no function a define gives",
            ));
        }
        let (letter, over, rule) = (
            self.rpn(&map.children()[0]),
            self.rpn(&map.children()[1]),
            self.rpn(&map.children()[2]),
        );
        let every = t!(t!(rule, "cvv", "wcel"), letter, over, "wral");
        let sets =
            take!(self.settle(&self.to_term(&every), scope, held, 3, None, None)?);
        let map_rpn = self.rpn(&map);
        let on = self.b.ap(
            "mptfng",
            &binds! {"F" => &map_rpn, "x" => &letter, "A" => &over, "B" => &rule},
            &[&self.b.ap("eqid", &binds! {"A" => &map_rpn}, &[])],
        );
        let map_on = t!(map_rpn, over, "wfn");
        let mapped = self.b.ap(
            "sylib",
            &binds! {"ph" => scope, "ps" => &every, "ch" => &map_on},
            &[&sets, &on],
        );
        let name_rpn = self.rpn(&name);
        let carried = self.b.ap(
            "fneq1d",
            &binds! {"ph" => scope, "F" => &name_rpn, "G" => &map_rpn, "A" => &over},
            &[&is_map],
        );
        let on_over = t!(name_rpn, over, "wfn");
        let named = self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &on_over, "ch" => &map_on},
            &[&mapped, &carried],
        );
        // A domain the claim names by a define is the set the define's body
        // holds written out, and the two are one in standard form.
        let claimed = self.rpn(whole);
        if claimed == on_over {
            return Ok(Built(named));
        }
        let alike =
            take!(self.same(&self.to_term(&on_over), whole, scope, held, None)?);
        Ok(Built(
            pf!(self.b; scope, on_over, claimed, named, alike, "mpbid"),
        ))
    }

    /// (value, ( scope -> one = value )) where `one` is a defined name or a
    /// defined function applied, read once and taken into the case the facts
    /// say; a decline otherwise.
    pub(super) fn define_value(
        &mut self,
        one: &Term,
        scope: &Rpn,
        held: &Facts,
    ) -> Checked<Route<(Term, Proof)>> {
        let letters = self.letters_bound(one);
        let kept = std::mem::replace(&mut self.binding, letters);
        let head = self.standard_step(one);
        self.binding = kept;
        let Some((how, value)) = head.filter(|(h, _)| {
            matches!(
                h,
                super::super::matcher::How::Defined
                    | super::super::matcher::How::Applied
            )
        }) else {
            return Ok(Route::no(NAMES_NO_DEFINE));
        };
        let proof = take!(self.standard_proof(one, &how, &value, scope, held)?);
        let (mut value, mut proof) =
            take!(self.recursion_value(one, &value, proof, scope, held)?);
        // Each case in turn: the condition held takes its value, the
        // condition refuted goes on to the rest.
        while value.label() == Some("cif") && value.children().len() == 3 {
            let (condition, first, rest) = (
                value.children()[0].clone(),
                value.children()[1].clone(),
                value.children()[2].clone(),
            );
            let cond = self.rpn(&condition);
            let parts =
                binds! {"ph" => &cond, "A" => self.rpn(&first), "B" => self.rpn(&rest)};
            let holds = self.settle(&condition, scope, held, 3, None, None)?;
            let fails = if holds.is_declined() {
                self.settle(&self.to_term(&t!(cond, "wn")), scope, held, 3, None, None)?
            } else {
                holds.clone()
            };
            let (taken, lemma, why) = match (holds, fails) {
                (Built(h), _) => (first, "iftrue", h),
                (_, Built(f)) => (rest, "iffalse", f),
                _ => return Ok(Route::no("no line the step cites says which case")),
            };
            let said = t!(self.rpn(&value), self.rpn(&taken), "wceq");
            let asked = if lemma == "iftrue" {
                cond.clone()
            } else {
                t!(cond, "wn")
            };
            let law = self.b.ap(lemma, &parts, &[]);
            let stepped = pf!(self.b; scope, asked, said, why, law, "syl");
            proof = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => self.rpn(one), "B" => self.rpn(&value), "C" => self.rpn(&taken)},
                &[&proof, &stepped],
            );
            value = taken;
        }
        Ok(Built((value, proof)))
    }

    /// (value, ( scope -> one = value )) taken one step further where `value`
    /// is a sequence's part of a recursion's value at 0 or at J + 1: at 0 the
    /// part of the start (`algr0`), at J + 1 the part of the step applied to
    /// the value at J (`algrp1`). Any other value is as it was.
    pub(super) fn recursion_value(
        &mut self,
        one: &Term,
        value: &Term,
        proof: Proof,
        scope: &Rpn,
        held: &Facts,
    ) -> Checked<Route<(Term, Proof)>> {
        let mut path = Vec::new();
        let mut core = value.clone();
        while core.label() == Some("cfv")
            && matches!(core.children()[1].label(), Some("c1st") | Some("c2nd"))
        {
            path.push(core.children()[1].label().unwrap().to_string());
            core = core.children()[0].clone();
        }
        if core.label() != Some("cfv")
            || !self.recursions.contains_key(&self.rpn(&core.children()[1]))
        {
            return Ok(Built((value.clone(), proof)));
        }
        let (at, made) = (core.children()[0].clone(), core.children()[1].clone());
        // At 1 the value is the step's at 0, 1 being 0 + 1 with its 0
        // dropped (`SYNTAX.md`, "An identity element goes without saying"),
        // as the checker reads F(1) by the rule at k + 1: the value is
        // restated at 0 + 1, carried across by `tidied`, and read there.
        if self.rpn(&at).alone() == Some("c1") {
            let padded_at = self.to_term(&t!("cc0", "c1", "caddc", "co"));
            let mut padded = t!(self.rpn(&padded_at), self.rpn(&made), "cfv");
            for part in path.iter().rev() {
                padded = t!(padded, part, "cfv");
            }
            let padded = self.to_term(&padded);
            let (said, want) = (
                t!(self.rpn(one), self.rpn(value), "wceq"),
                t!(self.rpn(one), self.rpn(&padded), "wceq"),
            );
            let Some(moved) = self.tidied(&proof, &said, &want, scope, held)? else {
                return Ok(Built((value.clone(), proof)));
            };
            return self.recursion_value(one, &padded, moved, scope, held);
        }
        let recursion = self.rpn(&made);
        let super::super::state::Recurrence {
            step,
            start,
            count,
            input,
        } = self.recursions[&recursion].clone();
        let where_ = self.rpn(&at);
        if let Some(input) = &input {
            let Some((state, moved)) = take!(
                self.indexed_value(&at, &recursion, &step, &start, input, scope, held)?
            ) else {
                return Ok(Built((value.clone(), proof)));
            };
            return self.part_of_state(
                one,
                value,
                proof,
                &path,
                state,
                moved,
                &where_,
                &recursion,
                count + 1,
                scope,
                held,
            );
        }
        let common = binds! {"ph" => scope, "A" => &start, "R" => &recursion, "S" => "cvv", "F" => &step, "M" => "cc0", "Z" => "cn0"};
        let start_set = take!(self.settle(
            &self.to_term(&t!(start, "cvv", "wcel")),
            scope,
            held,
            3,
            None,
            None
        )?);
        let asked = [
            self.step("nn0uz"),
            pf!(self.b; recursion, "eqid"),
            self.b.ap("0zd", &binds! {"ph" => scope}, &[]),
            start_set,
        ];
        let (state, moved);
        if where_.alone() == Some("cc0") {
            state = start.clone();
            moved = self
                .b
                .ap("algr0", &common, &asked.iter().collect::<Vec<_>>());
        } else if at.label() == Some("co")
            && at.children()[1].label() == Some("c1")
            && at.children()[2].label() == Some("caddc")
        {
            let before = self.rpn(&at.children()[0]);
            let index_in = take!(self.settle(
                &self.to_term(&t!(before, "cn0", "wcel")),
                scope,
                held,
                3,
                None,
                None
            )?);
            let map = self.to_term(&step);
            let (var, rule) = (map.children()[0].clone(), map.children()[2].clone());
            let x = self.rpn(&var);
            let a_set = take!(self.a_set_under(&x, &rule));
            let r = self.rpn(&rule);
            let into = self.b.ap(
                "fmpti",
                &binds! {"x" => &x, "A" => "cvv", "B" => "cvv", "C" => &r, "F" => &step},
                &[&pf!(self.b; step, "eqid"), &a_set],
            );
            let maps = pf!(self.b; t!("cvv", "cvv", step, "wf"), scope, into, "a1i");
            let prior = t!(before, recursion, "cfv");
            let mut with_k = common.clone();
            with_k.insert("K".to_string(), before.clone());
            let mut all: Vec<&Proof> = asked.iter().collect();
            all.push(&maps);
            let rp1 = self.b.ap("algrp1", &with_k, &all);
            let stepped = self.b.ap(
                "mpdan",
                &binds! {"ph" => scope, "ps" => t!(before, "cn0", "wcel"),
                "ch" => t!(t!(where_, recursion, "cfv"), t!(prior, step, "cfv"), "wceq")},
                &[&index_in, &rp1],
            );
            state = self.rpn(&self.restated(&rule, &t!(x, "cv"), &prior));
            // The step is taken at its value over a letter of its own.
            let y = self.spare_var()?;
            let fresh = self.rpn(&self.restated(&rule, &t!(x, "cv"), &t!(y, "cv")));
            let tie = self.to_term(&t!(
                t!(x, "cv", y, "cv", "wceq"),
                t!(r, fresh, "wceq"),
                "wi"
            ));
            let renaming =
                take!(self.prove_essential(&tie, &Rpn::default(), &Facts::new())?);
            let respelt = self.b.ap(
                "cbvmptv",
                &binds! {"x" => &x, "y" => &y, "A" => "cvv", "B" => &r, "C" => &fresh},
                &[&renaming],
            );
            let tie = self.to_term(&t!(
                t!(y, "cv", prior, "wceq"),
                t!(fresh, state, "wceq"),
                "wi"
            ));
            let instance =
                take!(self.prove_essential(&tie, &Rpn::default(), &Facts::new())?);
            let state_set = take!(self.settle(
                &self.to_term(&t!(state, "cvv", "wcel")),
                scope,
                held,
                3,
                None,
                None
            )?);
            let fvex =
                self.b
                    .ap("fvex", &binds! {"A" => &before, "F" => &recursion}, &[]);
            let prior_set = pf!(self.b; t!(prior, "cvv", "wcel"), scope, fvex, "a1i");
            let applied = self.b.ap(
                "fvmptd3",
                &binds! {"ph" => scope, "x" => &y, "A" => &prior, "B" => &fresh, "C" => &state, "D" => "cvv", "F" => &step, "V" => "cvv"},
                &[&respelt, &instance, &prior_set, &state_set],
            );
            moved = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => t!(where_, recursion, "cfv"), "B" => t!(prior, step, "cfv"), "C" => &state},
                &[&stepped, &applied],
            );
        } else {
            return Ok(Built((value.clone(), proof)));
        }
        self.part_of_state(
            one, value, proof, &path, state, moved, &where_, &recursion, count, scope,
            held,
        )
    }

    /// (state, ( scope -> R(at) = state )) for a recursion whose rules name
    /// the index (`recursion_terms`), the state being ⟨at, the values⟩;
    /// None where `at` is neither 0 nor J + 1.
    ///
    /// At 0, `seq1` says R(0) is G(0), which is ⟨0, start⟩. At J + 1,
    /// `seqp1d` says R(J + 1) is F(R(J), G(J + 1)), and `ovmpog` takes F at
    /// the two over letters of its own (`cbvmpov`), since R(J) holds F and
    /// with it F's letters. What F gives names the index as 1st(G(J + 1)),
    /// and k as that less one, which `op1stg` and `pncand` make J + 1 and J.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn indexed_value(
        &mut self,
        at: &Term,
        recursion: &Rpn,
        step: &Rpn,
        start: &Rpn,
        input: &Rpn,
        scope: &Rpn,
        held: &Facts,
    ) -> Checked<Route<Option<(Rpn, Proof)>>> {
        let where_ = self.rpn(at);
        let at_zero = where_.alone() == Some("cc0");
        let at_next = at.label() == Some("co")
            && at.children()[1].label() == Some("c1")
            && at.children()[2].label() == Some("caddc");
        if !at_zero && !at_next {
            return Ok(Built(None));
        }
        let index_in = if at_zero {
            pf!(self.b; t!("cc0", "cn0", "wcel"), scope, "0nn0", "a1i")
        } else {
            take!(self.settle(
                &self.to_term(&t!(where_, "cn0", "wcel")),
                scope,
                held,
                3,
                None,
                None
            )?)
        };
        // G at the index: ⟨index, start⟩ (`fvmptd3`).
        let g = self.to_term(input);
        let letter = self.rpn(&g.children()[0]);
        let body = self.rpn(&g.children()[2]);
        let given = t!(where_, start, "cop");
        let tie = self.to_term(&t!(
            t!(letter, "cv", where_, "wceq"),
            t!(body, given, "wceq"),
            "wi"
        ));
        let instance =
            take!(self.prove_essential(&tie, &Rpn::default(), &Facts::new())?);
        let given_set = pf!(self.b; t!(given, "cvv", "wcel"), scope,
            self.b.ap("opex", &binds! {"A" => &where_, "B" => start}, &[]), "a1i");
        let given_is = self.b.ap(
            "fvmptd3",
            &binds! {"ph" => scope, "x" => &letter, "A" => &where_, "B" => &body, "C" => &given, "D" => "cn0", "F" => input, "V" => "cvv"},
            &[&pf!(self.b; input, "eqid"), &instance, &index_in, &given_set],
        );
        let at_r = t!(where_, recursion, "cfv");
        let at_g = t!(where_, input, "cfv");
        if at_zero {
            let law = self.b.ap(
                "seq1",
                &binds! {"M" => "cc0", ".+" => step, "F" => input},
                &[],
            );
            let first = self.b.ap(
                "ax-mp",
                &binds! {"ph" => t!("cc0", "cz", "wcel"), "ps" => t!(at_r, at_g, "wceq")},
                &[&self.step("0z"), &law],
            );
            let first = pf!(self.b; t!(at_r, at_g, "wceq"), scope, first, "a1i");
            let moved = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &at_r, "B" => &at_g, "C" => &given},
                &[&first, &given_is],
            );
            return Ok(Built(Some((given, moved))));
        }
        let before = self.rpn(&at.children()[0]);
        let before_in = take!(self.settle(
            &self.to_term(&t!(before, "cn0", "wcel")),
            scope,
            held,
            3,
            None,
            None
        )?);
        let prior = t!(before, recursion, "cfv");
        let applied = t!(prior, given, step, "co");
        let stepped = self.b.ap(
            "seqp1d",
            &binds! {"ph" => scope, "Z" => "cn0", "M" => "cc0", "N" => &before, "K" => &where_,
            ".+" => step, "F" => input, "A" => &prior, "B" => &given},
            &[
                &self.step("nn0uz"),
                &before_in,
                &pf!(self.b; where_, "eqid"),
                &self.b.ap("eqidd", &binds! {"ph" => scope, "A" => &prior}, &[]),
                &given_is,
            ],
        );
        // F taken at R(J) and G(J + 1), over letters R(J) does not hold.
        let map = self.to_term(step);
        let (z, w) = (self.rpn(&map.children()[0]), self.rpn(&map.children()[1]));
        let rule = map.children()[4].clone();
        let (x, y) = (self.spare_var()?, self.spare_var()?);
        let (zc, wc, xc, yc) = (t!(z, "cv"), t!(w, "cv"), t!(x, "cv"), t!(y, "cv"));
        let r = self.rpn(&rule);
        let half = self.rpn(&self.restated(&rule, &zc, &xc));
        let fresh = self.rpn(&self.restated(&self.to_term(&half), &wc, &yc));
        let mut ties = Vec::new();
        for (from, to, was, now) in [(&zc, &xc, &r, &half), (&wc, &yc, &half, &fresh)] {
            let tie =
                self.to_term(&t!(t!(from, to, "wceq"), t!(was, now, "wceq"), "wi"));
            ties.push(take!(self.prove_essential(
                &tie,
                &Rpn::default(),
                &Facts::new()
            )?));
        }
        let respelt = self.b.ap(
            "cbvmpov",
            &binds! {"x" => &z, "y" => &w, "z" => &x, "w" => &y, "A" => "cvv", "B" => "cvv",
            "C" => &r, "E" => &half, "D" => &fresh},
            &[&ties[0], &ties[1]],
        );
        let once = self.rpn(&self.restated(&self.to_term(&fresh), &xc, &prior));
        let taken = self.rpn(&self.restated(&self.to_term(&once), &yc, &given));
        let mut ties = Vec::new();
        for (from, to, was, now) in
            [(&xc, &prior, &fresh, &once), (&yc, &given, &once, &taken)]
        {
            let tie =
                self.to_term(&t!(t!(from, to, "wceq"), t!(was, now, "wceq"), "wi"));
            ties.push(take!(self.prove_essential(
                &tie,
                &Rpn::default(),
                &Facts::new()
            )?));
        }
        let law = self.b.ap(
            "ovmpog",
            &binds! {"x" => &x, "y" => &y, "A" => &prior, "B" => &given, "C" => "cvv", "D" => "cvv",
            "R" => &fresh, "G" => &once, "S" => &taken, "F" => step, "H" => "cvv"},
            &[&ties[0], &ties[1], &respelt],
        );
        let pair = self.to_term(&taken);
        let mut sets = Vec::new();
        for (term, made) in [
            (&prior, self.b.ap("fvex", &binds! {"A" => &before, "F" => recursion}, &[])),
            (&given, self.b.ap("opex", &binds! {"A" => &where_, "B" => start}, &[])),
            (
                &taken,
                self.b.ap(
                    "opex",
                    &binds! {"A" => self.rpn(&pair.children()[0]), "B" => self.rpn(&pair.children()[1])},
                    &[],
                ),
            ),
        ] {
            sets.push(pf!(self.b; t!(term, "cvv", "wcel"), scope, made, "a1i"));
        }
        let evaluated = self.b.ap(
            "syl3anc",
            &binds! {"ph" => scope, "ps" => t!(prior, "cvv", "wcel"), "ch" => t!(given, "cvv", "wcel"),
            "th" => t!(taken, "cvv", "wcel"), "ta" => t!(applied, taken, "wceq")},
            &[&sets[0], &sets[1], &sets[2], &law],
        );
        // 1st(G(J + 1)) is J + 1 (`op1stg`), and that less one is J (`pncand`).
        let first_of = t!(given, "c1st", "cfv");
        let mut parts_set = Vec::new();
        for c in [&where_, start] {
            parts_set.push(take!(self.settle(
                &self.to_term(&t!(c, "cvv", "wcel")),
                scope,
                held,
                3,
                None,
                None
            )?));
        }
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(where_, "cvv", "wcel"), "ch" => t!(start, "cvv", "wcel")},
            &[&parts_set[0], &parts_set[1]],
        );
        let law = self.b.ap(
            "op1stg",
            &binds! {"A" => &where_, "B" => start, "V" => "cvv", "W" => "cvv"},
            &[],
        );
        let index_is = pf!(self.b; scope,
            t!(t!(where_, "cvv", "wcel"), t!(start, "cvv", "wcel"), "wa"),
            t!(first_of, where_, "wceq"), both, law, "syl");
        let less_one = t!(first_of, "c1", "cmin", "co");
        let shifted = self.b.ap(
            "oveq1d",
            &binds! {"ph" => scope, "A" => &first_of, "B" => &where_, "C" => "c1", "F" => "cmin"},
            &[&index_is],
        );
        let before_cc = self.b.ap(
            "nn0cnd",
            &binds! {"ph" => scope, "A" => &before},
            &[&before_in],
        );
        let one_cc = self.b.ap("1cnd", &binds! {"ph" => scope}, &[]);
        let cancelled = self.b.ap(
            "pncand",
            &binds! {"ph" => scope, "A" => &before, "B" => "c1"},
            &[&before_cc, &one_cc],
        );
        let k_is = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &less_one, "B" => t!(where_, "c1", "cmin", "co"), "C" => &before},
            &[&shifted, &cancelled],
        );
        let known = Facts::new();
        self.know(&known, t!(first_of, where_, "wceq"), index_is);
        self.know(&known, t!(less_one, before, "wceq"), k_is);
        let state = {
            let read = self.restated(&pair, &less_one, &before);
            self.rpn(&self.restated(&read, &first_of, &where_))
        };
        let tidied = take!(self.congruence(
            &pair,
            &self.to_term(&state),
            scope,
            &known,
            None,
            &Leaf::Rows(vec![super::super::tables::Row::Held])
        )?);
        let mut moved = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &at_r, "B" => &applied, "C" => &taken},
            &[&stepped, &evaluated],
        );
        moved = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &at_r, "B" => &taken, "C" => &state},
            &[&moved, &tidied],
        );
        Ok(Built(Some((state, moved))))
    }

    /// (part, ( scope -> one = part )) from ( scope -> R(where) = state ):
    /// the part `path` names, taken out of the state from the inside with
    /// `op1stg` and `op2ndg`. `parts` is how many components the state
    /// holds, so a state of one is never taken apart.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn part_of_state(
        &mut self,
        one: &Term,
        value: &Term,
        proof: Proof,
        path: &[String],
        mut state: Rpn,
        mut moved: Proof,
        where_: &Rpn,
        recursion: &Rpn,
        parts: usize,
        scope: &Rpn,
        held: &Facts,
    ) -> Checked<Route<(Term, Proof)>> {
        let mut held_at = t!(where_, recursion, "cfv");
        for label in path.iter().rev() {
            let pair = self.to_term(&state);
            if pair.label() != Some("cop") || parts < 2 {
                return Ok(Route::no("the recursion's state is not a pair here"));
            }
            let (first, rest) =
                (self.rpn(&pair.children()[0]), self.rpn(&pair.children()[1]));
            let mut sets = Vec::new();
            for c in [&first, &rest] {
                sets.push(self.settle(
                    &self.to_term(&t!(c, "cvv", "wcel")),
                    scope,
                    held,
                    3,
                    None,
                    None,
                )?);
            }
            let mut set_proofs = Vec::new();
            for s in sets {
                set_proofs.push(take!(s));
            }
            let both = self.b.ap(
                "jca",
                &binds! {"ph" => scope, "ps" => t!(first, "cvv", "wcel"), "ch" => t!(rest, "cvv", "wcel")},
                &[&set_proofs[0], &set_proofs[1]],
            );
            let (lemma, part) = if label == "c1st" {
                ("op1stg", first.clone())
            } else {
                ("op2ndg", rest.clone())
            };
            let taken = t!(t!(first, "cvv", "wcel"), t!(rest, "cvv", "wcel"), "wa");
            let out = t!(t!(state, label, "cfv"), part, "wceq");
            let law = self.b.ap(
                lemma,
                &binds! {"A" => &first, "B" => &rest, "V" => "cvv", "W" => "cvv"},
                &[],
            );
            let parted = pf!(self.b; scope, taken, out, both, law, "syl");
            let lifted = self.b.ap(
                "fveq2d",
                &binds! {"ph" => scope, "A" => &held_at, "B" => &state, "F" => label},
                &[&moved],
            );
            moved = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => t!(held_at, label, "cfv"), "B" => t!(state, label, "cfv"), "C" => &part},
                &[&lifted, &parted],
            );
            held_at = t!(held_at, label, "cfv");
            state = part;
        }
        let whole = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => self.rpn(one), "B" => self.rpn(value), "C" => &state},
            &[&proof, &moved],
        );
        Ok(Built((self.to_term(&state), whole)))
    }

    /// ( x e. _V -> rule e. _V ): the state a step gives is a set with nothing
    /// assumed (`closed_set`), so it is one wherever x is.
    pub(super) fn a_set_under(&self, x: &Rpn, rule: &Term) -> Route<Proof> {
        let made = match self.closed_set(rule) {
            Built(p) => p,
            Declined(d) => return Declined(d),
        };
        Built(
            pf!(self.b; t!(self.rpn(rule), "cvv", "wcel"), t!(x, "cv", "cvv", "wcel"), made, "a1i"),
        )
    }

    /// |- term e. _V from the lemmas `rules::CLOSED_SETHOOD` names, each asked
    /// of the parts it asks for; a decline naming a head none covers.
    pub(super) fn closed_set(&self, term: &Term) -> Route<Proof> {
        let label = if term.variable().is_none() {
            term.label().and_then(|l| lookup(rules::CLOSED_SETHOOD, l))
        } else {
            None
        };
        let Some(label) = label else {
            return Route::no(format!(
                "nothing says a {} is a set",
                term.label().unwrap_or("None")
            ));
        };
        let sig = self.sig(label);
        let binds: crate::mm::spell::Binds = sig
            .floats
            .iter()
            .zip(term.children())
            .map(|((_, name), child)| (name.to_string(), self.rpn(child)))
            .collect();
        let mut asked = Vec::new();
        for said in &sig.essentials {
            match self.closed_set(&self.to_term(&binds[said[1].as_str()])) {
                Built(p) => asked.push(p),
                Declined(d) => return Declined(d),
            }
        }
        Built(self.b.ap(label, &binds, &asked.iter().collect::<Vec<_>>()))
    }

    /// Each part of every line `step` cites, known apart in `known`: "A. B"
    /// and "A and B" are one claim, and a cited line supplies each of its
    /// parts separately (`SYNTAX.md`, the conventions at every citation).
    pub(super) fn cited_parts(
        &mut self,
        step: &Step,
        scope: &Rpn,
        known: &Facts,
        lines: &Lines,
    ) -> Checked<()> {
        for r in &step.just.refs {
            let Some(line) = self.line_written(r, lines) else {
                continue;
            };
            let term = line.claim;
            if let Some(p) = self.held(known, &term, scope)? {
                self.unpack_all(&term, &p, scope, known);
            }
        }
        Ok(())
    }
}
