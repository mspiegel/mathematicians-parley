//! Bounds, antisymmetry and differences.

use super::*;

impl<'a> Elaborator<'a> {
    /// An equation from the two bounds that close on it: a number neither
    /// greater nor smaller than another is that number (`letri3`).
    pub(super) fn by_antisymmetry(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let Some((a, b, how)) = order_sides(goal) else {
            return Ok(None);
        };
        if how != "=" {
            return Ok(None);
        }
        let (a, b) = (self.rpn(&a), self.rpn(&b));
        let (up, down) = (t!(a, b, "cle", "wbr"), t!(b, a, "cle", "wbr"));
        let (Some(pu), Some(pd)) = (
            self.held(facts, &up, scope)?,
            self.held(facts, &down, scope)?,
        ) else {
            return Ok(None);
        };
        self.joined_bounds(&a, &b, pu, pd, goal, scope, facts)
            .map(Some)
    }

    /// An equation claim that is a split of its own: the claim denied is
    /// two terms differing, so it is shown as the two bounds it is made of,
    /// each held or proved by the method from what the step cites, and
    /// joined by `letri3`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn both_bounds(
        &mut self,
        refs: &[String],
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        let goal = self.to_term(term);
        let Some((a, b, how)) = order_sides(&goal) else {
            return Ok(Route::no("the claim states no relation"));
        };
        if how != "=" {
            return Ok(Route::no("what splits is the claim, and it is no equation"));
        }
        let (a, b) = (self.rpn(&a), self.rpn(&b));
        let mut halves = Vec::new();
        for half in [t!(a, b, "cle", "wbr"), t!(b, a, "cle", "wbr")] {
            halves.push(match self.held(facts, &half, scope)? {
                Some(p) => p,
                None => {
                    take!(self.prove_order(refs, &half, scope, facts, lines, skip)?)
                }
            });
        }
        let pd = halves.pop().expect("two halves");
        let pu = halves.pop().expect("two halves");
        self.joined_bounds(&a, &b, pu, pd, &goal, scope, facts)
            .map(Built)
    }

    /// ( scope -> a = b ) from ( scope -> a <_ b ) and ( scope -> b <_ a ).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn joined_bounds(
        &mut self,
        a: &Rpn,
        b: &Rpn,
        pu: Proof,
        pd: Proof,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let (up, down) = (t!(a, b, "cle", "wbr"), t!(b, a, "cle", "wbr"));
        let both = t!(up, down, "wa");
        let paired = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => &up, "ch" => &down},
            &[&pu, &pd],
        );
        let ra = self.membership(a, "cr", scope, facts)?;
        let rb = self.membership(b, "cr", scope, facts)?;
        let law = self.b.ap("letri3", &binds! {"A" => a, "B" => b}, &[]);
        let g = self.rpn(goal);
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(a, "cr", "wcel"), "ch" => t!(b, "cr", "wcel"), "th" => t!(g, both, "wb")},
            &[&ra, &rb, &law],
        );
        Ok(self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &g, "ch" => &both},
            &[&paired, &turn],
        ))
    }

    /// A claim denying a relation, as the relation that holds instead,
    /// proved first and turned round by `ltnle` or `lenlt`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn negated_order(
        &mut self,
        goal: &Term,
        refs: &[String],
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        let Some((a, b, how)) =
            order_sides(&goal.children()[0]).filter(|s| s.2 == "<" || s.2 == "<=")
        else {
            return Ok(Route::no("what is denied states no relation"));
        };
        let (a, b) = (self.rpn(&a), self.rpn(&b));
        let (turns, rel) = if how == "<=" {
            ("ltnle", "clt")
        } else {
            ("lenlt", "cle")
        };
        let instead = t!(b, a, rel, "wbr");
        let held = match self.held(facts, &instead, scope)? {
            Some(p) => p,
            None => take!(self.prove_order(refs, &instead, scope, facts, lines, skip)?),
        };
        let rb = self.membership(&b, "cr", scope, facts)?;
        let ra = self.membership(&a, "cr", scope, facts)?;
        let law = self.b.ap(turns, &binds! {"A" => &b, "B" => &a}, &[]);
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(b, "cr", "wcel"), "ch" => t!(a, "cr", "wcel"), "th" => t!(instead, term, "wb")},
            &[&rb, &ra, &law],
        );
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => &instead, "ch" => term},
            &[&held, &turn],
        )))
    }

    /// A claim proved twice, once each side of a cited disequality: each side
    /// is the same claim at a scope one wider, with the side's bound standing
    /// as a line of its own, and `mpjaodan` puts the two back together.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn either_way(
        &mut self,
        found: &Certificate,
        refs: &[String],
        where_: &[(String, Term)],
        given: &[linear::Fact],
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        let Certificate::Either { at: which, .. } = found else {
            unreachable!("a certificate that splits");
        };
        if *which >= given.len() {
            return self.both_bounds(refs, term, scope, facts, lines, skip);
        }
        let (r, said) = where_[*which].clone();
        if said.variable().is_some()
            || said.label() != Some("wn")
            || said.children()[0].label() != Some("wceq")
        {
            return Ok(Route::no("what splits is not a denied equation"));
        }
        let pair = said.children()[0].clone();
        let (a, b) = (self.rpn(&pair.children()[0]), self.rpn(&pair.children()[1]));
        let (below, above) = (t!(a, b, "clt", "wbr"), t!(b, a, "clt", "wbr"));
        let given_fact = take!(self.cited_fact(&r, &said, scope, facts, lines)?);
        let turned = self.b.ap(
            "neqned",
            &binds! {"ph" => scope, "A" => &a, "B" => &b},
            &[&given_fact],
        );
        let ra = self.membership(&a, "cr", scope, facts)?;
        let rb = self.membership(&b, "cr", scope, facts)?;
        let law = self.b.ap("lttri2", &binds! {"A" => &a, "B" => &b}, &[]);
        let split = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(a, "cr", "wcel"), "ch" => t!(b, "cr", "wcel"),
            "th" => t!(t!(a, b, "wne"), t!(below, above, "wo"), "wb")},
            &[&ra, &rb, &law],
        );
        let whether = self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(a, b, "wne"), "ch" => t!(below, above, "wo")},
            &[&turned, &split],
        );
        let said_rpn = self.rpn(&said);
        let sides = self.frames_kept(|me| -> Checked<Route<Vec<Proof>>> {
            let mut sides = Vec::new();
            for bound in [&below, &above] {
                let (inner, lifted) = me.widen(scope, facts, bound, None);
                let proof = me
                    .held(&lifted, bound, &inner)?
                    .expect("the bound just laid down");
                // The bound stands as a line named by its own text.
                let name = bound.to_string();
                let held = lines.copy();
                held.set(name.clone(), Line::new(bound.clone(), proof, Vec::new()));
                let mut more = refs.to_vec();
                more.push(name);
                let mut skipped = skip.to_vec();
                skipped.push(said_rpn.clone());
                let side = take!(
                    me.one_way(bound, term, &inner, &lifted, &held, &more, &skipped)?
                );
                sides.push(side);
            }
            Ok(Built(sides))
        })?;
        let sides = take!(sides);
        Ok(Built(self.b.ap(
            "mpjaodan",
            &binds! {"ph" => scope, "ps" => &below, "ch" => term, "th" => &above},
            &[&sides[0], &sides[1], &whether],
        )))
    }

    /// One side of a split, at the scope that side opened: the side's own
    /// bound may be the claim, the claim may follow from the bound and what
    /// is cited, or the bound may contradict what is cited.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn one_way(
        &mut self,
        bound: &Rpn,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        refs: &[String],
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        if let Some(p) = self.held(facts, term, scope)? {
            return Ok(Built(p));
        }
        let found = self.prove_order(refs, term, scope, facts, lines, skip)?;
        if !found.is_declined() {
            return Ok(found);
        }
        self.impossible(bound, term, scope, facts, lines, refs, skip)
    }

    /// The claim, because the bound this scope opened cannot hold: `lenlt`
    /// says a ≤ b and b < a deny each other, and what denies the bound is
    /// held already or follows from what the step cites.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn impossible(
        &mut self,
        bound: &Rpn,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        refs: &[String],
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        let node = self.to_term(bound);
        let Some((low, high, _)) = order_sides(&node).filter(|s| s.2 == "<") else {
            return Ok(Route::no("the bound states no strict order"));
        };
        let (low, high) = (self.rpn(&low), self.rpn(&high));
        let denies = t!(high, low, "cle", "wbr");
        let held = match self.held(facts, &denies, scope)? {
            Some(p) => p,
            None => {
                // The bound's line is named by its text (`either_way`).
                let name = bound.to_string();
                let cited: Vec<String> =
                    refs.iter().filter(|r| **r != name).cloned().collect();
                take!(self.prove_order(&cited, &denies, scope, facts, lines, skip)?)
            }
        };
        let rh = self.membership(&high, "cr", scope, facts)?;
        let rl = self.membership(&low, "cr", scope, facts)?;
        let law = self.b.ap("lenlt", &binds! {"A" => &high, "B" => &low}, &[]);
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(high, "cr", "wcel"), "ch" => t!(low, "cr", "wcel"),
            "th" => t!(denies, t!(bound, "wn"), "wb")},
            &[&rh, &rl, &law],
        );
        let refuted = self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => &denies, "ch" => t!(bound, "wn")},
            &[&held, &turn],
        );
        let supposed = self
            .held(facts, bound, scope)?
            .expect("the bound this scope opened");
        Ok(Built(self.b.ap(
            "pm2.21dd",
            &binds! {"ph" => scope, "ps" => bound, "ch" => term},
            &[&supposed, &refuted],
        )))
    }

    /// Two things the step says are not equal, because one is below: where
    /// the contradiction is with a single strict bound between the very two
    /// the claim names, the whole argument is `ltne`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn stays_apart(
        &mut self,
        used: &[usize],
        given: &[linear::Fact],
        where_: &[(String, Term)],
        claim: &linear::Fact,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if used.len() != 1 || given[used[0]].how != How::Lt {
            return Ok(Route::no("not one strict bound"));
        }
        let (r, said) = where_[used[0]].clone();
        let Some(_) = order_sides(&said).filter(|s| s.2 == "<") else {
            return Ok(Route::no("the cited bound is not stated as one"));
        };
        let below: Vec<Rpn> =
            said.children()[..2].iter().map(|c| self.rpn(c)).collect();
        // The claim must be about the two the bound is about, and no more.
        let left_over = claim.side.minus(&given[used[0]].side.scaled(&q(-1)));
        if !left_over.atoms().is_empty() || !left_over.constant.is_zero() {
            return Ok(Route::no("the claim is not that bound turned"));
        }
        // And written as the two of them: `b − a ≠ 0` is the same bound
        // turned, and another statement, which the order proves.
        if self.rpn(goal) != t!(t!(below[1], below[0], "wceq"), "wn") {
            return Ok(Route::no("the claim is not the two the bound names"));
        }
        let bound = take!(self.cited_fact(&r, &said, scope, facts, lines)?);
        let real = self.membership(&below[0], "cr", scope, facts)?;
        let law = self
            .b
            .ap("ltne", &binds! {"A" => &below[0], "B" => &below[1]}, &[]);
        let apart = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(below[0], "cr", "wcel"), "ch" => t!(below[0], below[1], "clt", "wbr"),
            "th" => t!(below[1], below[0], "wne")},
            &[&real, &bound, &law],
        );
        Ok(Built(self.b.ap(
            "neneqd",
            &binds! {"ph" => scope, "A" => &below[1], "B" => &below[0]},
            &[&apart],
        )))
    }

    /// One cited fact, scaled, as a term that is at most zero: an equation is
    /// at most zero because it is zero exactly; an inequality already is,
    /// and scaling it by something positive leaves it so.
    pub(super) fn at_most_zero(
        &mut self,
        w: &mut Work,
        said: &Term,
        times: &Q,
        given: Proof,
        facts: &Facts,
    ) -> Checked<Route<(Rpn, Proof, Proof)>> {
        let scope = w.spec.scope.clone();
        let (mut said, mut given) = (said.clone(), given);
        if said.variable().is_none()
            && said.label() == Some("wn")
            && said.children().len() == 1
        {
            let (turned, proof) =
                take!(self.unnegated(&scope, &said.children()[0], &given, facts)?);
            said = turned;
            given = proof;
        }
        let Some((_, _, rel)) = order_sides(&said) else {
            return Ok(Route::no("a cited fact states no relation"));
        };
        let was: Vec<Rpn> = said.children()[..2].iter().map(|c| self.rpn(c)).collect();
        let gap = t!(was[0], was[1], "cmin", "co");
        let r0 = self.membership(&was[0], "cr", &scope, facts)?;
        let r1 = self.membership(&was[1], "cr", &scope, facts)?;
        let law = self
            .b
            .ap("resubcl", &binds! {"A" => &was[0], "B" => &was[1]}, &[]);
        let real = self.b.ap(
            "syl2anc",
            &binds! {"ph" => &scope, "ps" => t!(was[0], "cr", "wcel"), "ch" => t!(was[1], "cr", "wcel"), "th" => t!(gap, "cr", "wcel")},
            &[&r0, &r1, &law],
        );
        let Some(numeral) = field::spell_coefficient(times) else {
            return Ok(Route::no(format!(
                "{} is not a whole number",
                super::super::normal::show(times)
            )));
        };
        let scaled = t!(numeral, gap, "cmul", "co");
        let rn = self.real_numeral(&scope, times);
        let law = self
            .b
            .ap("remulcl", &binds! {"A" => &numeral, "B" => &gap}, &[]);
        let scaled_real = self.b.ap(
            "syl2anc",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cr", "wcel"), "ch" => t!(gap, "cr", "wcel"), "th" => t!(scaled, "cr", "wcel")},
            &[&rn, &real, &law],
        );
        let at_zero = t!(numeral, "cc0", "cmul", "co");
        if rel == "=" {
            let zeroed = self.difference_zero(w, &was, &given)?;
            let lifted = self.b.ap(
                "oveq2d",
                &binds! {"ph" => &scope, "A" => &gap, "B" => "cc0", "C" => &numeral, "F" => "cmul"},
                &[&zeroed],
            );
            let c = w.e.coefficient(&self.ask(&w.spec), times);
            let law = self.b.ap("mul01", &binds! {"A" => &numeral}, &[]);
            let naught = self.b.ap(
                "syl",
                &binds! {"ph" => &scope, "ps" => t!(numeral, "cc", "wcel"), "ch" => t!(at_zero, "cc0", "wceq")},
                &[&c, &law],
            );
            let vanishes = w.e.chain(
                &self.ask(&w.spec),
                &lifted,
                &naught,
                &scaled,
                &at_zero,
                &t!("cc0"),
            );
            let below = self.b.ap(
                "eqled",
                &binds! {"ph" => &scope, "A" => &scaled, "B" => "cc0"},
                &[&scaled_real, &vanishes],
            );
            return Ok(Built((scaled, below, scaled_real)));
        }
        if rel == "<" {
            // A sum that lands on `at most` has no use for the strictness, so
            // it is given up here and the one case below serves both.
            let r0 = self.membership(&was[0], "cr", &scope, facts)?;
            let r1 = self.membership(&was[1], "cr", &scope, facts)?;
            given = self.b.ap(
                "ltled",
                &binds! {"ph" => &scope, "A" => &was[0], "B" => &was[1]},
                &[&r0, &r1, &given],
            );
        } else if rel != "<=" {
            return Ok(Route::no(format!("a cited {rel} is not written")));
        }
        let bound = self.difference_le(&scope, &was, &given, facts)?;
        if times.is_one() {
            return Ok(Built((gap, bound, real)));
        }
        if !times.is_positive() {
            return Ok(Route::no("a bound may only be scaled upward"));
        }
        let zero = self.closed_law(&t!("cc0", "cr", "wcel"), "0re", &scope);
        let rn = self.real_numeral(&scope, times);
        let pos = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", numeral, "clt", "wbr"), "ps" => &scope},
            &[&numerals::pos(&self.b, times.numer().magnitude().clone())],
        );
        let positive = self.b.ap(
            "jca",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cr", "wcel"), "ch" => t!("cc0", numeral, "clt", "wbr")},
            &[&rn, &pos],
        );
        let law = self.b.ap(
            "lemul2",
            &binds! {"A" => &gap, "B" => "cc0", "C" => &numeral},
            &[],
        );
        let turn = self.b.ap(
            "syl3anc",
            &binds! {"ph" => &scope, "ps" => t!(gap, "cr", "wcel"), "ch" => t!("cc0", "cr", "wcel"),
            "th" => t!(t!(numeral, "cr", "wcel"), t!("cc0", numeral, "clt", "wbr"), "wa"),
            "ta" => t!(t!(gap, "cc0", "cle", "wbr"), t!(scaled, at_zero, "cle", "wbr"), "wb")},
            &[&real, &zero, &positive, &law],
        );
        let moved = self.b.ap(
            "mpbid",
            &binds! {"ph" => &scope, "ps" => t!(gap, "cc0", "cle", "wbr"), "ch" => t!(scaled, at_zero, "cle", "wbr")},
            &[&bound, &turn],
        );
        let c = w.e.coefficient(&self.ask(&w.spec), times);
        let law = self.b.ap("mul01", &binds! {"A" => &numeral}, &[]);
        let naught = self.b.ap(
            "syl",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cc", "wcel"), "ch" => t!(at_zero, "cc0", "wceq")},
            &[&c, &law],
        );
        let below = self.b.ap(
            "breqtrd",
            &binds! {"ph" => &scope, "A" => &scaled, "B" => &at_zero, "C" => "cc0", "R" => "cle"},
            &[&moved, &naught],
        );
        Ok(Built((scaled, below, scaled_real)))
    }

    /// A cited fact stated as a denial, said the other way round: `lenlt`
    /// and `ltnle` say a denied `<` or `≤` is the other relation turned.
    pub(super) fn unnegated(
        &mut self,
        scope: &Rpn,
        inner: &Term,
        given: &Proof,
        facts: &Facts,
    ) -> Checked<Route<(Term, Proof)>> {
        let found =
            order_sides(inner).and_then(|s| lookup(rules::DENIED, s.2).map(|d| (s, d)));
        let Some((_sides, (denied, said, lemma))) = found else {
            return Ok(Route::no("only a denied `<` or `≤` is turned round"));
        };
        let was: Vec<Rpn> = inner.children()[..2].iter().map(|c| self.rpn(c)).collect();
        let turned = self.to_term(&t!(was[1], was[0], said, "wbr"));
        let r1 = self.membership(&was[1], "cr", scope, facts)?;
        let r0 = self.membership(&was[0], "cr", scope, facts)?;
        let law = self
            .b
            .ap(lemma, &binds! {"A" => &was[1], "B" => &was[0]}, &[]);
        let holds = t!(was[1], was[0], said, "wbr");
        let not_held = t!(t!(was[0], was[1], denied, "wbr"), "wn");
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(was[1], "cr", "wcel"), "ch" => t!(was[0], "cr", "wcel"),
            "th" => t!(holds, not_held, "wb")},
            &[&r1, &r0, &law],
        );
        Ok(Built((
            turned,
            self.b.ap(
                "mpbird",
                &binds! {"ph" => scope, "ps" => &holds, "ch" => &not_held},
                &[given, &turn],
            ),
        )))
    }

    /// The proof of one fact a cited line states: a line may say several
    /// things at once, and what the step uses is one of them.
    pub fn cited_fact(
        &mut self,
        r: &str,
        said: &Term,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let want = self.rpn(said);
        let held = self.carried(r, facts, lines);
        let term = self
            .line_written(r, lines)
            .map(|l| l.claim)
            .unwrap_or_default();
        if term == want {
            return Ok(Built(held));
        }
        let known = facts.copy();
        self.unpack_all(&term, &held, scope, &known);
        if let Some(p) = self.held(&known, &want, scope)? {
            return Ok(Built(p));
        }
        // A bound the line's membership implies, read off what the line
        // states and nothing else in scope.
        for (s, proof) in self.stated_by(r, scope, &known, lines)? {
            let proof = if s == term { Some(held.clone()) } else { proof };
            let Some(proof) = proof else {
                continue;
            };
            let more = self.implied(&s, &proof, scope, &known)?;
            if let Some(p) = self.held(&more, &want, scope)? {
                return Ok(Built(p));
            }
        }
        Ok(Route::no("that line does not reach the fact"))
    }

    /// ( scope -> ( A - B ) <_ 0 ) from a cited A <_ B.
    pub(super) fn difference_le(
        &mut self,
        scope: &Rpn,
        was: &[Rpn],
        given: &Proof,
        facts: &Facts,
    ) -> Checked<Proof> {
        let gap = t!(was[0], was[1], "cmin", "co");
        let r0 = self.membership(&was[0], "cr", scope, facts)?;
        let r1 = self.membership(&was[1], "cr", scope, facts)?;
        let law = self
            .b
            .ap("suble0", &binds! {"A" => &was[0], "B" => &was[1]}, &[]);
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(was[0], "cr", "wcel"), "ch" => t!(was[1], "cr", "wcel"),
            "th" => t!(t!(gap, "cc0", "cle", "wbr"), t!(was[0], was[1], "cle", "wbr"), "wb")},
            &[&r0, &r1, &law],
        );
        Ok(self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => t!(gap, "cc0", "cle", "wbr"), "ch" => t!(was[0], was[1], "cle", "wbr")},
            &[given, &turn],
        ))
    }

    /// The claim as one cited equation, scaled: an equation may be
    /// multiplied by anything, which is what lets one cited equation carry a
    /// claim on its own.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn one_equation_scaled(
        &mut self,
        cited: &(String, Term),
        times: &Q,
        left: &Rpn,
        right: &Rpn,
        how: &str,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let (r, said) = cited;
        let Some(_) = order_sides(said).filter(|s| s.2 == "=") else {
            return Ok(Route::no("the cited fact is not an equation"));
        };
        let Some(numeral) = field::spell_coefficient(times) else {
            return Ok(Route::no(format!(
                "{} is not a whole number",
                super::super::normal::show(times)
            )));
        };
        let mut w = Work::plain(scope, facts);
        let was: Vec<Rpn> = said.children().iter().map(|c| self.rpn(c)).collect();
        let gap = t!(was[0], was[1], "cmin", "co");
        let scaled = t!(numeral, gap, "cmul", "co");
        let span = t!(left, right, "cmin", "co");
        let alike = self.same_polynomial(&mut w, &span, &scaled)?;
        let stated = self.cited_fact(r, said, scope, facts, lines)?;
        let (alike, stated) = (take!(alike), take!(stated));
        let zeroed = self.difference_zero(&mut w, &was, &stated)?;
        let lifted = self.b.ap(
            "oveq2d",
            &binds! {"ph" => scope, "A" => &gap, "B" => "cc0", "C" => &numeral, "F" => "cmul"},
            &[&zeroed],
        );
        let c = w.e.coefficient(&self.ask(&w.spec), times);
        let law = self.b.ap("mul01", &binds! {"A" => &numeral}, &[]);
        let at_zero = t!(numeral, "cc0", "cmul", "co");
        let naught = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(numeral, "cc", "wcel"), "ch" => t!(at_zero, "cc0", "wceq")},
            &[&c, &law],
        );
        let inner = w.e.chain(
            &self.ask(&w.spec),
            &lifted,
            &naught,
            &scaled,
            &at_zero,
            &t!("cc0"),
        );
        let reached = w.e.chain(
            &self.ask(&w.spec),
            &alike,
            &inner,
            &span,
            &scaled,
            &t!("cc0"),
        );
        if how == "=" {
            let cl = self.membership(left, "cc", scope, facts)?;
            let cr = self.membership(right, "cc", scope, facts)?;
            let law = self
                .b
                .ap("subeq0", &binds! {"A" => left, "B" => right}, &[]);
            let turn = self.b.ap(
                "syl2anc",
                &binds! {"ph" => scope, "ps" => t!(left, "cc", "wcel"), "ch" => t!(right, "cc", "wcel"),
                "th" => t!(t!(span, "cc0", "wceq"), t!(left, right, "wceq"), "wb")},
                &[&cl, &cr, &law],
            );
            return Ok(Built(self.b.ap(
                "mpbid",
                &binds! {"ph" => scope, "ps" => t!(span, "cc0", "wceq"), "ch" => t!(left, right, "wceq")},
                &[&reached, &turn],
            )));
        }
        if how != "<=" {
            return Ok(Route::no(format!("a {how} conclusion is not written")));
        }
        // A difference that is zero is at most zero.
        let rl = self.membership(left, "cr", scope, facts)?;
        let rr = self.membership(right, "cr", scope, facts)?;
        let law = self
            .b
            .ap("resubcl", &binds! {"A" => left, "B" => right}, &[]);
        let real = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(left, "cr", "wcel"), "ch" => t!(right, "cr", "wcel"), "th" => t!(span, "cr", "wcel")},
            &[&rl, &rr, &law],
        );
        let at_most = self.b.ap(
            "eqled",
            &binds! {"ph" => scope, "A" => &span, "B" => "cc0"},
            &[&real, &reached],
        );
        // A difference at most zero is what `<_` says of the two sides.
        let rl = self.membership(left, "cr", scope, facts)?;
        let rr = self.membership(right, "cr", scope, facts)?;
        let law = self
            .b
            .ap("suble0", &binds! {"A" => left, "B" => right}, &[]);
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(left, "cr", "wcel"), "ch" => t!(right, "cr", "wcel"),
            "th" => t!(t!(span, "cc0", "cle", "wbr"), t!(left, right, "cle", "wbr"), "wb")},
            &[&rl, &rr, &law],
        );
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(span, "cc0", "cle", "wbr"), "ch" => t!(left, right, "cle", "wbr")},
            &[&at_most, &turn],
        )))
    }

    /// ( scope -> ( A - B ) = 0 ) from a cited A = B.
    pub(super) fn difference_zero(
        &mut self,
        w: &mut Work,
        was: &[Rpn],
        given: &Proof,
    ) -> Checked<Proof> {
        let scope = w.spec.scope.clone();
        let a0 = self.membership(&was[0], "cc", &scope, &w.spec.facts.clone())?;
        let a1 = self.membership(&was[1], "cc", &scope, &w.spec.facts.clone())?;
        let gap = t!(was[0], was[1], "cmin", "co");
        let law = self
            .b
            .ap("subeq0", &binds! {"A" => &was[0], "B" => &was[1]}, &[]);
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => &scope, "ps" => t!(was[0], "cc", "wcel"), "ch" => t!(was[1], "cc", "wcel"),
            "th" => t!(t!(gap, "cc0", "wceq"), t!(was[0], was[1], "wceq"), "wb")},
            &[&a0, &a1, &law],
        );
        Ok(self.b.ap(
            "mpbird",
            &binds! {"ph" => &scope, "ps" => t!(gap, "cc0", "wceq"), "ch" => t!(was[0], was[1], "wceq")},
            &[given, &turn],
        ))
    }
}
