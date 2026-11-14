//! Sums and combinations.

use super::*;

impl<'a> Elaborator<'a> {
    /// The scope widened by one member of `over`, and the facts with what
    /// that membership says laid beside it.
    pub(super) fn fixed(
        &mut self,
        scope: &Rpn,
        known: &Facts,
        variable: &Term,
        over: &Term,
    ) -> Checked<(Rpn, Facts)> {
        let member = t!(self.rpn(variable), "cv", self.rpn(over), "wcel");
        let (inner, lifted) = self.widen(scope, known, &member, None);
        let held = self
            .held(&lifted, &member, &inner)?
            .expect("the membership just laid down");
        let more = self.implied(&member, &held, &inner, &lifted)?;
        let out = lifted.copy();
        for (k, v) in more.entries() {
            self.know(&out, k, v);
        }
        Ok((inner, out))
    }

    /// ( scope -> said = L ) and L: a finite sum written out as linear over
    /// `spare`, the step's one letter nothing holds (`field::linear_sum`).
    /// The sum is renamed to the spare (`class_alpha`), its summand is shown
    /// at a member to be the parts added (`sumeq2dv`), the sum is split a
    /// part at a time (`fsumadd`), and each part's free factor is taken out
    /// (`fsummulc2`). The sum lemmas keep their letter apart from the scope
    /// and the range, which the spare is.
    pub fn linear_sum(
        &mut self,
        said: &Rpn,
        spare: &str,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<(Term, Proof)>> {
        let labels = self.b.flabel.clone();
        let whole = self.to_term(said);
        let Some(field::LinearSum {
            range,
            letter,
            parts,
        }) = field::linear_sum(&whole, &labels)
        else {
            return Ok(Route::no("the sum is read as one atom"));
        };
        let summand = whole.children()[1].clone();
        let range_term = whole.children()[0].clone();
        // Already as the parts write it, and nothing to do.
        if letter == spare
            && parts.len() == 1
            && parts[0].weight == q(1)
            && parts[0].free.is_empty()
            && self.rpn(&summand) == field::spell_monomial(&parts[0].bound)
        {
            return Ok(Route::no("the sum is written out already"));
        }
        let member_cv = t!(spare, "cv");
        let summand_at = if letter == spare {
            self.rpn(&summand)
        } else {
            let moved = self.restated(&summand, &t!(letter, "cv"), &member_cv);
            self.rpn(&moved)
        };
        let at_spare = t!(range, summand_at, spare, "csu");
        let renamed = if letter == spare {
            None
        } else {
            let Some(closed) = self.class_alpha(&whole, &self.to_term(&at_spare))?
            else {
                return Ok(Route::no("the sum is not renamed to the spare letter"));
            };
            Some(pf!(self.b; t!(said, at_spare, "wceq"), scope, closed, "a1i"))
        };
        // The parts, each its free factor times what holds the letter.
        let mut scaled: Vec<(Rpn, Rpn, Rpn)> = Vec::new();
        for part in &parts {
            let bound = field::respelt(&part.bound, letter, Symbol::of(spare));
            let m = field::spell_monomial(&bound);
            let c = Emitter::spell_run(&[(part.free.clone(), part.weight.clone())]);
            let t = t!(c, m, "cmul", "co");
            scaled.push((c, m, t));
        }
        let mut prefixes: Vec<Rpn> = vec![scaled[0].2.clone()];
        for one in &scaled[1..] {
            let last = prefixes.last().unwrap().clone();
            prefixes.push(t!(last, one.2, "caddc", "co"));
        }
        let added = prefixes.last().unwrap().clone();
        // At a member: the summand is the parts added, and each part and
        // each run of them is a number.
        let variable = self.var_of(spare);
        let at_member = self.frames_kept(|me| -> Checked<Route<AtMember>> {
            let (inner, lifted) = me.fixed(scope, facts, &variable, &range_term)?;
            // What the member's membership says is the step's to use there,
            // as a line it writes: the claim's sum ranges over it.
            let kept = me.written.clone();
            for (said, held) in lifted.entries() {
                if !me.holds(facts, &said) {
                    me.write(said, inner.clone(), held);
                }
            }
            let made = (|| -> Checked<Route<AtMember>> {
                let mut w = Work::plain(&inner, &lifted);
                let pointwise =
                    take!(me.same_polynomial(&mut w, &summand_at, &added)?);
                let mut runs = Vec::new();
                for p in &prefixes {
                    runs.push(me.membership(p, "cc", &inner, &lifted)?);
                }
                let mut terms = Vec::new();
                let mut bounds = Vec::new();
                for (_, m, t) in &scaled {
                    terms.push(me.membership(t, "cc", &inner, &lifted)?);
                    bounds.push(me.membership(m, "cc", &inner, &lifted)?);
                }
                Ok(Built(AtMember {
                    pointwise,
                    runs,
                    terms,
                    bounds,
                }))
            })();
            me.written = kept;
            made
        })?;
        let AtMember {
            pointwise,
            runs,
            terms,
            bounds,
        } = take!(at_member);
        let sum_of = |s: &Rpn| t!(range, s, spare, "csu");
        let finite = {
            let kids = range_term.children();
            let law = self.b.ap(
                "fzfi",
                &binds! {"M" => self.rpn(&kids[0]), "N" => self.rpn(&kids[1])},
                &[],
            );
            pf!(self.b; t!(range, "cfn", "wcel"), scope, law, "a1i")
        };
        // Each part's sum is a number, its terms being (`fsumcl`), kept for
        // when the normaliser asks.
        for (i, (_, m, _)) in scaled.iter().enumerate() {
            let p = self.b.ap(
                "fsumcl",
                &binds! {"ph" => scope, "A" => &range, "B" => m, "k" => spare},
                &[&finite, &bounds[i]],
            );
            self.sums_in_cc.insert((scope.clone(), sum_of(m)), p);
        }
        // ( scope -> sum of the summand = sum of the parts added ).
        let lifted = self.b.ap(
            "sumeq2dv",
            &binds! {"ph" => scope, "k" => spare, "A" => &range, "B" => &summand_at, "C" => &added},
            &[&pointwise],
        );
        // ( scope -> sum of the parts added = the parts' sums added ).
        let mut split: Option<Proof> = None;
        let mut sums = sum_of(&scaled[0].2);
        for i in 1..scaled.len() {
            let (before, part) = (&prefixes[i - 1], &scaled[i].2);
            let step = self.b.ap(
                "fsumadd",
                &binds! {"ph" => scope, "A" => &range, "B" => before, "C" => part, "k" => spare},
                &[&finite, &runs[i - 1], &terms[i]],
            );
            let next = t!(sums, sum_of(part), "caddc", "co");
            split = Some(match split {
                None => step,
                Some(earlier) => {
                    let carried = self.b.ap(
                        "oveq1d",
                        &binds! {"ph" => scope, "A" => sum_of(before), "B" => &sums,
                        "C" => sum_of(part), "F" => "caddc"},
                        &[&earlier],
                    );
                    self.b.ap(
                        "eqtrd",
                        &binds! {"ph" => scope, "A" => sum_of(&prefixes[i]),
                        "B" => t!(sum_of(before), sum_of(part), "caddc", "co"), "C" => &next},
                        &[&step, &carried],
                    )
                }
            });
            sums = next;
        }
        // ( scope -> the parts' sums added = each free factor times its sum ).
        let mut pulled: Option<(Proof, Rpn, Rpn)> = None;
        for (i, (c, m, t)) in scaled.iter().enumerate() {
            let free = self.membership(c, "cc", scope, facts)?;
            let out = self.b.ap(
                "fsummulc2",
                &binds! {"ph" => scope, "A" => &range, "B" => m, "C" => c, "k" => spare},
                &[&finite, &free, &bounds[i]],
            );
            let times = t!(c, sum_of(m), "cmul", "co");
            let this = self.b.ap(
                "eqcomd",
                &binds! {"ph" => scope, "A" => &times, "B" => sum_of(t)},
                &[&out],
            );
            pulled = Some(match pulled {
                None => (this, sum_of(t), times),
                Some((earlier, from, to)) => {
                    let joined = self.b.ap(
                        "oveq12d",
                        &binds! {"ph" => scope, "A" => &from, "B" => &to,
                        "C" => sum_of(t), "D" => &times, "F" => "caddc"},
                        &[&earlier, &this],
                    );
                    (
                        joined,
                        t!(from, sum_of(t), "caddc", "co"),
                        t!(to, times, "caddc", "co"),
                    )
                }
            });
        }
        let (pulled, from, linear) = pulled.expect("a sum of one part at least");
        // said = at_spare = sum of parts added = sums added = linear.
        let mut chain: Vec<(Proof, Rpn, Rpn)> = Vec::new();
        if let Some(r) = renamed {
            chain.push((r, said.clone(), at_spare.clone()));
        }
        chain.push((lifted, at_spare.clone(), sum_of(&added)));
        if let Some(s) = split {
            chain.push((s, sum_of(&added), from.clone()));
        }
        chain.push((pulled, from, linear.clone()));
        let (mut proof, first, mut last) = chain[0].clone();
        for (p, a, b) in chain.into_iter().skip(1) {
            debug_assert_eq!(a, last);
            proof = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &first, "B" => &a, "C" => &b},
                &[&proof, &p],
            );
            last = b;
        }
        let _ = last;
        Ok(Built((self.to_term(&linear), proof)))
    }

    /// A finite sum in ℝ or ℂ because each term is, for each index in its
    /// range (`fsumrecl`, `fsumcl`). Its terms are a family's values.
    pub(crate) fn summed(
        &mut self,
        whole: &Term,
        system: &Rpn,
        scope: &Rpn,
        known: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        self.in_family += 1;
        let out = self.summed_terms(whole, system, scope, known, step);
        self.in_family -= 1;
        out
    }

    pub(super) fn summed_terms(
        &mut self,
        whole: &Term,
        system: &Rpn,
        scope: &Rpn,
        known: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        let lemma = match system.alone().unwrap_or_default() {
            "cr" => Some("fsumrecl"),
            "cc" => Some("fsumcl"),
            _ => None,
        };
        let (limits, summand, index) = (
            whole.children()[0].clone(),
            whole.children()[1].clone(),
            whole.children()[2].clone(),
        );
        // A sum the checker found the page says once is a number by its
        // terms at each index, whatever they divide by
        // (`CheckedTheorem::said_sums`), over its own index or one it is
        // renamed to.
        let spelt = self.rpn(whole);
        let said_once = self
            .said_sums
            .iter()
            .any(|s| *s == spelt || self.rebound(s, &spelt));
        let Some(lemma) = lemma.filter(|_| {
            limits.variable().is_none()
                && limits.label() == Some("co")
                && self.rpn(&limits.children()[2]).alone() == Some("cfz")
        }) else {
            return Ok(Route::no(format!(
                "a sum in {system} over this range is not written"
            )));
        };
        // The lemma keeps its index out of the scope and the range. Where
        // either spells it, as an induction hypothesis about a sum over the
        // same letter does, the sum is shown over a letter nothing holds and
        // renamed back (`renaming_apart`).
        let letter = self.rpn(&index);
        let spells = |said: &Rpn| letter.alone().is_some_and(|l| said.has(l));
        if spells(scope) || spells(&self.rpn(&limits)) {
            let Some(name) = index.variable() else {
                return Ok(Route::no("a sum's index is no letter"));
            };
            let Some(fresh) = self.unheld(&[&self.to_term(scope), whole]) else {
                return Ok(Route::no("no letter is left to sum over"));
            };
            let mut put = IndexMap::new();
            put.insert(Symbol::of(name), fresh);
            let moved = whole.substitute(&put);
            let shown = take!(self.summed(&moved, system, scope, known, step)?);
            let said = t!(self.rpn(&moved), system, "wcel");
            let want = t!(self.rpn(whole), system, "wcel");
            let Some(across) = self.renaming_apart(&said, &want)? else {
                return Ok(Route::no("the sum does not rename back"));
            };
            let turned = pf!(self.b; t!(said, want, "wb"), scope, across, "a1i");
            return Ok(Built(
                pf!(self.b; scope, said, want, shown, turned, "mpbid"),
            ));
        }
        let (low, high) = (
            self.rpn(&limits.children()[0]),
            self.rpn(&limits.children()[1]),
        );
        let finite = self.b.ap(
            "fzfid",
            &binds! {"ph" => scope, "M" => &low, "N" => &high},
            &[],
        );
        let system_term = self.to_term(system);
        let each = self.frames_kept(|me| {
            let (inner, lifted) = me.fixed(scope, known, &index, &limits)?;
            let claim = Term::apply("wcel", vec![summand.clone(), system_term.clone()]);
            // A line saying the term at every index says it, whatever the
            // term; a term dividing by the index is so only by such a line
            // (`methods::membership::summed`).
            let by_line = me.said_at_every_index(&claim, &inner, &lifted)?;
            if let Built(_) = by_line {
                return Ok(by_line);
            }
            if !said_once && me.divides_by_index(&summand, &letter, &inner, &lifted)? {
                return Ok(by_line);
            }
            me.member_of(&claim, &inner, &lifted, step)
        })?;
        let each = take!(each);
        Ok(Built(self.b.ap(
            lemma,
            &binds! {"ph" => scope, "A" => self.rpn(&limits), "B" => self.rpn(&summand), "k" => self.rpn(&index)},
            &[&finite, &each],
        )))
    }

    /// Whether a sum's term divides by something holding its index that the
    /// page does not say once is a positive integer (`positive_divisor`),
    /// `letter` as a proof spells it and `scope` fixing it in its range: a
    /// divisor no line outside the sum can say is not zero (`SYNTAX.md`).
    pub(super) fn divides_by_index(
        &mut self,
        summand: &Term,
        letter: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<bool> {
        if summand.variable().is_some() {
            return Ok(false);
        }
        let kids = summand.children();
        if summand.label() == Some("co")
            && kids.len() == 3
            && self.rpn(&kids[2]).alone() == Some("cdiv")
        {
            let divisor = self.rpn(&kids[1]);
            let holds = letter.alone().is_some_and(|l| divisor.has(l));
            if holds && self.positive_divisor(&divisor, scope, facts)?.is_none() {
                return Ok(true);
            }
        }
        for k in kids {
            if self.divides_by_index(k, letter, scope, facts)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// A sum's term at its index taken from a line the step cites saying it
    /// at every point of a set holding the range (`instance_of_universal`,
    /// `instance_at_a_term`), and from nothing else: its divisor holds the
    /// index, which nothing outside the sum can say is not zero.
    pub(super) fn said_at_every_index(
        &mut self,
        claim: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let wanted = self.rpn(claim);
        if let Some(p) = self.instance_of_universal(&wanted, scope, facts)? {
            return Ok(Built(p));
        }
        if let Some(p) = self.instance_at_a_term(claim, scope, facts, 3)? {
            return Ok(Built(p));
        }
        Ok(self.no("no line the step cites says {} at every index", &[&wanted]))
    }

    /// A claim of two sentences joined by "and", each proved in turn.
    pub(super) fn both_halves(
        &mut self,
        refs: &[String],
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        let halves: Vec<Rpn> = goal.children().iter().map(|c| self.rpn(c)).collect();
        let mut made = Vec::new();
        for one in &halves {
            made.push(self.prove_order(refs, one, scope, facts, lines, skip)?);
        }
        let mut proofs = Vec::new();
        for one in made {
            proofs.push(take!(one));
        }
        Ok(Built(
            pf!(self.b; scope, halves[0], halves[1], proofs[0], proofs[1], "jca"),
        ))
    }

    /// `a ≠ b` as the strict bound between them the cited facts give.
    pub(super) fn apart_by_order(
        &mut self,
        refs: &[String],
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        if goal.variable().is_some()
            || goal.label() != Some("wn")
            || goal.children()[0].label() != Some("wceq")
        {
            return Ok(Route::no("the claim is not a disequality"));
        }
        let pair = goal.children()[0].clone();
        let (a, b) = (self.rpn(&pair.children()[0]), self.rpn(&pair.children()[1]));
        for (lo, hi, turn) in [(&b, &a, "gtned"), (&a, &b, "ltned")] {
            let Built(below) = self.prove_order(
                refs,
                &t!(lo, hi, "clt", "wbr"),
                scope,
                facts,
                lines,
                skip,
            )?
            else {
                continue;
            };
            let real = self.membership(lo, "cr", scope, facts)?;
            let apart = self.b.ap(
                turn,
                &binds! {"ph" => scope, "A" => lo, "B" => hi},
                &[&real, &below],
            );
            return Ok(Built(self.b.ap(
                "neneqd",
                &binds! {"ph" => scope, "A" => &a, "B" => &b},
                &[&apart],
            )));
        }
        Ok(Route::no(
            "the cited facts put neither side below the other",
        ))
    }

    /// Any positive combination of cited facts, and a number left over,
    /// written as the certificate stands: the weights are made whole by
    /// taking the claim's difference `W` times over, each fact is said
    /// against zero and scaled keeping its strictness, what is left over is
    /// one more fact, and the lot is added two at a time.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn combination(
        &mut self,
        parts: &[Part],
        left: &Rpn,
        right: &Rpn,
        how: &str,
        spare: &Q,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if how != "<" && how != "<=" {
            return Ok(Route::no(format!(
                "a combination reaching {how} is not written"
            )));
        }
        if parts.is_empty() && how == "<=" && spare.is_zero() && left == right {
            let real = self.membership(left, "cr", scope, facts)?;
            return Ok(Built(self.b.ap(
                "leidd",
                &binds! {"ph" => scope, "A" => left},
                &[&real],
            )));
        }
        let whole = field::common_denominator(
            std::iter::once(spare).chain(parts.iter().map(|p| &p.times)),
        );
        let whole_q = Q::from_integer(whole.clone());
        // A reciprocal atom's divisor not being zero is the page's to say, in
        // its own spelling, which `written_nonzero` reads as a polynomial.
        let known = facts.copy();
        for (claim, w) in self.written.entries() {
            if let Some(lifted) = self.lifted_to(&claim, &w.proof, &w.at, scope) {
                self.know_default(&known, claim, lifted);
            }
        }
        let mut w = Work::new(Spec {
            scope: scope.clone(),
            facts: facts.clone(),
            apart: false,
            written: Some(known),
            atoms: RefCell::default(),
            implied: Implied::default(),
        });
        let mut terms: Vec<Against> = Vec::new();
        for Part {
            cited: r,
            said,
            times,
        } in parts
        {
            let given = take!(self.cited_fact(r, said, scope, facts, lines)?);
            let one = take!(self.scaled_bound(
                &mut w,
                said,
                given,
                &(times * &whole_q),
                facts
            )?);
            terms.push(one);
        }
        let left_over = spare * &whole_q;
        if left_over.is_positive() {
            return Ok(Route::no("what is left over is above zero"));
        }
        if left_over.is_negative() {
            let one = take!(self.number_below(scope, &-left_over));
            terms.push(one);
        }
        // Sides that differ only in how they are spelt combine nothing: the
        // claim's difference is zero as a polynomial, and zero is at most
        // zero.
        if terms.is_empty() && how == "<=" {
            let below = self.closed_law(&t!("cc0", "cc0", "cle", "wbr"), "0le0", scope);
            let real = self.closed_law(&t!("cc0", "cr", "wcel"), "0re", scope);
            terms.push(Against {
                term: t!("cc0"),
                strict: false,
                below,
                real,
            });
        }
        if terms.is_empty() {
            return Ok(Route::no("nothing is combined"));
        }
        let mut total = terms[0].clone();
        for one in &terms[1..] {
            total = self.added_pair(scope, &total, one);
        }
        let Against {
            term,
            strict,
            below,
            ..
        } = total;
        if how == "<" && !strict {
            return Ok(Route::no("nothing combined is strict"));
        }
        let mut rel = if strict { "clt" } else { "cle" };
        let span = t!(left, right, "cmin", "co");
        let rl = self.membership(left, "cr", scope, facts)?;
        let rr = self.membership(right, "cr", scope, facts)?;
        let span_real = self.b.ap(
            "resubcld",
            &binds! {"ph" => scope, "A" => left, "B" => right},
            &[&rl, &rr],
        );
        let (mut times_span, mut times_real) = (span.clone(), span_real.clone());
        let numeral = numerals::spell(whole.magnitude().clone());
        if !whole.is_one() {
            times_span = t!(&numeral, span, "cmul", "co");
            let real = self.real_numeral(scope, &whole_q);
            times_real = self.b.ap(
                "remulcld",
                &binds! {"ph" => scope, "A" => &numeral, "B" => &span},
                &[&real, &span_real],
            );
        }
        let alike = take!(self.same_polynomial(&mut w, &times_span, &term)?);
        let mut reached = self.b.ap(
            "eqbrtrd",
            &binds! {"ph" => scope, "A" => &times_span, "B" => &term, "C" => "cc0", "R" => rel},
            &[&alike, &below],
        );
        if strict && how == "<=" {
            let zero = self.closed_law(&t!("cc0", "cr", "wcel"), "0re", scope);
            reached = self.b.ap(
                "ltled",
                &binds! {"ph" => scope, "A" => &times_span, "B" => "cc0"},
                &[&times_real, &zero, &reached],
            );
            rel = "cle";
        }
        if !whole.is_one() {
            reached = self
                .unscaled(&mut w, &span, &span_real, &numeral, &whole, rel, &reached);
        }
        let turn = t!(
            t!(span, "cc0", rel, "wbr"),
            t!(left, right, rel, "wbr"),
            "wb"
        );
        let rl = self.membership(left, "cr", scope, facts)?;
        let rr = self.membership(right, "cr", scope, facts)?;
        let back = if rel == "clt" {
            self.b.ap(
                "sublt0d",
                &binds! {"ph" => scope, "A" => left, "B" => right},
                &[&rl, &rr],
            )
        } else {
            let law = self
                .b
                .ap("suble0", &binds! {"A" => left, "B" => right}, &[]);
            self.b.ap(
                "syl2anc",
                &binds! {"ph" => scope, "ps" => t!(left, "cr", "wcel"), "ch" => t!(right, "cr", "wcel"), "th" => &turn},
                &[&rl, &rr, &law],
            )
        };
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(span, "cc0", rel, "wbr"), "ch" => t!(left, right, rel, "wbr")},
            &[&reached, &back],
        )))
    }

    /// One cited fact scaled by a positive whole number, against zero: an
    /// equation or a bound at most is `at_most_zero`'s; a strict bound is
    /// said as its difference below zero and scaled by `ltmul2`, which keeps
    /// it strict.
    pub(super) fn scaled_bound(
        &mut self,
        w: &mut Work,
        said: &Term,
        given: Proof,
        times: &Q,
        facts: &Facts,
    ) -> Checked<Route<Against>> {
        let scope = w.spec.scope.clone();
        if !times.is_integer() {
            return Ok(Route::no(format!(
                "a fact scaled by {} is not written",
                super::super::normal::show(times)
            )));
        }
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
        // An equation may be taken either way round; a bound only upward.
        if !times.is_positive() && rel != "=" {
            return Ok(Route::no("a bound may only be scaled upward"));
        }
        if rel != "<" {
            let (term, below, real) =
                take!(self.at_most_zero(w, &said, times, given, facts)?);
            return Ok(Built(Against {
                term,
                strict: false,
                below,
                real,
            }));
        }
        let was: Vec<Rpn> = said.children()[..2].iter().map(|c| self.rpn(c)).collect();
        let gap = t!(was[0], was[1], "cmin", "co");
        let r0 = self.membership(&was[0], "cr", &scope, facts)?;
        let r1 = self.membership(&was[1], "cr", &scope, facts)?;
        let real = self.b.ap(
            "resubcld",
            &binds! {"ph" => &scope, "A" => &was[0], "B" => &was[1]},
            &[&r0, &r1],
        );
        let r0 = self.membership(&was[0], "cr", &scope, facts)?;
        let r1 = self.membership(&was[1], "cr", &scope, facts)?;
        let turn = self.b.ap(
            "sublt0d",
            &binds! {"ph" => &scope, "A" => &was[0], "B" => &was[1]},
            &[&r0, &r1],
        );
        let below = self.b.ap(
            "mpbird",
            &binds! {"ph" => &scope, "ps" => t!(gap, "cc0", "clt", "wbr"), "ch" => t!(was[0], was[1], "clt", "wbr")},
            &[&given, &turn],
        );
        if times.is_one() {
            return Ok(Built(Against {
                term: gap,
                strict: true,
                below,
                real,
            }));
        }
        let times_n = times.to_integer();
        let numeral = numerals::spell(times_n.magnitude().clone());
        let scaled = t!(&numeral, gap, "cmul", "co");
        let rn = self.real_numeral(&scope, times);
        let scaled_real = self.b.ap(
            "remulcld",
            &binds! {"ph" => &scope, "A" => &numeral, "B" => &gap},
            &[&rn, &real],
        );
        let moved =
            self.times_positive(w, &gap, &real, &numeral, &times_n, "clt", &below);
        Ok(Built(Against {
            term: scaled,
            strict: true,
            below: moved,
            real: scaled_real,
        }))
    }

    /// ( scope -> ( n x. gap ) R 0 ) from ( scope -> gap R 0 ), n > 0.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn times_positive(
        &mut self,
        w: &mut Work,
        gap: &Rpn,
        real: &Proof,
        numeral: &Rpn,
        whole: &BigInt,
        rel: &str,
        below: &Proof,
    ) -> Proof {
        let scope = w.spec.scope.clone();
        let lemma = if rel == "clt" { "ltmul2" } else { "lemul2" };
        let scaled = t!(numeral, gap, "cmul", "co");
        let at_zero = t!(numeral, "cc0", "cmul", "co");
        let whole_q = Q::from_integer(whole.clone());
        let rn = self.real_numeral(&scope, &whole_q);
        let pos = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", numeral, "clt", "wbr"), "ps" => &scope},
            &[&numerals::pos(&self.b, whole.magnitude().clone())],
        );
        let positive = self.b.ap(
            "jca",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cr", "wcel"), "ch" => t!("cc0", numeral, "clt", "wbr")},
            &[&rn, &pos],
        );
        let zero = self.closed_law(&t!("cc0", "cr", "wcel"), "0re", &scope);
        let law = self.b.ap(
            lemma,
            &binds! {"A" => gap, "B" => "cc0", "C" => numeral},
            &[],
        );
        let turn = self.b.ap(
            "syl3anc",
            &binds! {"ph" => &scope, "ps" => t!(gap, "cr", "wcel"), "ch" => t!("cc0", "cr", "wcel"),
            "th" => t!(t!(numeral, "cr", "wcel"), t!("cc0", numeral, "clt", "wbr"), "wa"),
            "ta" => t!(t!(gap, "cc0", rel, "wbr"), t!(scaled, at_zero, rel, "wbr"), "wb")},
            &[real, &zero, &positive, &law],
        );
        let moved = self.b.ap(
            "mpbid",
            &binds! {"ph" => &scope, "ps" => t!(gap, "cc0", rel, "wbr"), "ch" => t!(scaled, at_zero, rel, "wbr")},
            &[below, &turn],
        );
        let c = w.e.coefficient(&self.ask(&w.spec), &whole_q);
        let law = self.b.ap("mul01", &binds! {"A" => numeral}, &[]);
        let zeroed = self.b.ap(
            "syl",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cc", "wcel"), "ch" => t!(at_zero, "cc0", "wceq")},
            &[&c, &law],
        );
        self.b.ap(
            "breqtrd",
            &binds! {"ph" => &scope, "A" => &scaled, "B" => &at_zero, "C" => "cc0", "R" => rel},
            &[&moved, &zeroed],
        )
    }

    /// ( scope -> span R 0 ) from ( scope -> ( n x. span ) R 0 ), n > 0.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn unscaled(
        &mut self,
        w: &mut Work,
        span: &Rpn,
        span_real: &Proof,
        numeral: &Rpn,
        whole: &BigInt,
        rel: &str,
        reached: &Proof,
    ) -> Proof {
        let scope = w.spec.scope.clone();
        let lemma = if rel == "clt" { "ltmul2" } else { "lemul2" };
        let scaled = t!(numeral, span, "cmul", "co");
        let at_zero = t!(numeral, "cc0", "cmul", "co");
        let whole_q = Q::from_integer(whole.clone());
        let rn = self.real_numeral(&scope, &whole_q);
        let pos = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", numeral, "clt", "wbr"), "ps" => &scope},
            &[&numerals::pos(&self.b, whole.magnitude().clone())],
        );
        let positive = self.b.ap(
            "jca",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cr", "wcel"), "ch" => t!("cc0", numeral, "clt", "wbr")},
            &[&rn, &pos],
        );
        let c = w.e.coefficient(&self.ask(&w.spec), &whole_q);
        let law = self.b.ap("mul01", &binds! {"A" => numeral}, &[]);
        let zeroed = self.b.ap(
            "syl",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cc", "wcel"), "ch" => t!(at_zero, "cc0", "wceq")},
            &[&c, &law],
        );
        let at = self.b.ap(
            "breqtrrd",
            &binds! {"ph" => &scope, "A" => &scaled, "B" => "cc0", "C" => &at_zero, "R" => rel},
            &[reached, &zeroed],
        );
        let zero = self.closed_law(&t!("cc0", "cr", "wcel"), "0re", &scope);
        let law = self.b.ap(
            lemma,
            &binds! {"A" => span, "B" => "cc0", "C" => numeral},
            &[],
        );
        let turn = self.b.ap(
            "syl3anc",
            &binds! {"ph" => &scope, "ps" => t!(span, "cr", "wcel"), "ch" => t!("cc0", "cr", "wcel"),
            "th" => t!(t!(numeral, "cr", "wcel"), t!("cc0", numeral, "clt", "wbr"), "wa"),
            "ta" => t!(t!(span, "cc0", rel, "wbr"), t!(scaled, at_zero, rel, "wbr"), "wb")},
            &[span_real, &zero, &positive, &law],
        );
        self.b.ap(
            "mpbird",
            &binds! {"ph" => &scope, "ps" => t!(span, "cc0", rel, "wbr"), "ch" => t!(scaled, at_zero, rel, "wbr")},
            &[&at, &turn],
        )
    }

    /// (−n, True, ( scope -> -u n < 0 ), ( scope -> -u n e. RR )), the
    /// number a combination leaves over, as a closed numeral fact.
    pub(super) fn number_below(&self, scope: &Rpn, value: &Q) -> Route<Against> {
        if !value.is_integer() || !value.is_positive() {
            return Route::no(format!(
                "{} is not a positive whole number",
                super::super::normal::show(value)
            ));
        }
        let whole = value.to_integer();
        let numeral = numerals::spell(whole.magnitude().clone());
        let numeral = &numeral;
        let real = self.real_numeral(scope, value);
        let positive = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", numeral, "clt", "wbr"), "ps" => scope},
            &[&numerals::pos(&self.b, whole.magnitude().clone())],
        );
        let negated = t!(numeral, "cneg");
        let turn = self.b.ap(
            "lt0neg2d",
            &binds! {"ph" => scope, "A" => numeral},
            &[&real],
        );
        let below = self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!("cc0", numeral, "clt", "wbr"), "ch" => t!(negated, "cc0", "clt", "wbr")},
            &[&positive, &turn],
        );
        let neg_real = self.b.ap(
            "renegcld",
            &binds! {"ph" => scope, "A" => numeral},
            &[&real],
        );
        Built(Against {
            term: negated,
            strict: true,
            below,
            real: neg_real,
        })
    }

    /// Two terms against zero added, strict where either is.
    pub(super) fn added_pair(
        &self,
        scope: &Rpn,
        one: &Against,
        other: &Against,
    ) -> Against {
        let (a, sa, pa, ra) = (&one.term, &one.strict, &one.below, &one.real);
        let (b, sb, pb, rb) = (&other.term, &other.strict, &other.below, &other.real);
        let rel_a = if *sa { "clt" } else { "cle" };
        let rel_b = if *sb { "clt" } else { "cle" };
        let lemma = rules::adding(*sa, *sb).closed;
        let rel = if *sa || *sb { "clt" } else { "cle" };
        let total = t!(a, b, "caddc", "co");
        let sum_zero = t!("cc0", "cc0", "caddc", "co");
        let zero = self.closed_law(&t!("cc0", "cr", "wcel"), "0re", scope);
        let each = t!(t!(a, "cc0", rel_a, "wbr"), t!(b, "cc0", rel_b, "wbr"), "wa");
        let reals = t!(t!(a, "cr", "wcel"), t!(b, "cr", "wcel"), "wa");
        let zeros = t!(t!("cc0", "cr", "wcel"), t!("cc0", "cr", "wcel"), "wa");
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(a, "cc0", rel_a, "wbr"), "ch" => t!(b, "cc0", rel_b, "wbr")},
            &[pa, pb],
        );
        let real_pair = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(a, "cr", "wcel"), "ch" => t!(b, "cr", "wcel")},
            &[ra, rb],
        );
        let zero_pair = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!("cc0", "cr", "wcel"), "ch" => t!("cc0", "cr", "wcel")},
            &[&zero, &zero],
        );
        let asks = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => &reals, "ch" => &zeros},
            &[&real_pair, &zero_pair],
        );
        let law = self.b.ap(
            lemma,
            &binds! {"A" => a, "B" => b, "C" => "cc0", "D" => "cc0"},
            &[],
        );
        let lifted = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(reals, zeros, "wa"), "ch" => t!(each, t!(total, sum_zero, rel, "wbr"), "wi")},
            &[&asks, &law],
        );
        let added = self.b.ap(
            "mpd",
            &binds! {"ph" => scope, "ps" => &each, "ch" => t!(total, sum_zero, rel, "wbr")},
            &[&both, &lifted],
        );
        let naught = self.closed_law(&t!(sum_zero, "cc0", "wceq"), "00id", scope);
        let below = self.b.ap(
            "breqtrd",
            &binds! {"ph" => scope, "A" => &total, "B" => &sum_zero, "C" => "cc0", "R" => rel},
            &[&added, &naught],
        );
        let real = self.b.ap(
            "readdcld",
            &binds! {"ph" => scope, "A" => a, "B" => b},
            &[ra, rb],
        );
        Against {
            term: total,
            strict: *sa || *sb,
            below,
            real,
        }
    }
}
