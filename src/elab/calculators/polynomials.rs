//! Polynomials, cancelling and closed facts.

use super::*;

impl<'a> Elaborator<'a> {
    /// Two terms driven to one canonical form, and so to each other. Where
    /// either divides, the canonical form is a numerator over a denominator,
    /// and two of those are the same when the cross product is.
    pub(in crate::elab) fn same_polynomial(
        &mut self,
        w: &mut Work,
        left: &Rpn,
        right: &Rpn,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let lt = self.to_term(left);
        let Quotiented {
            over: first_items,
            under: first_under,
            proof: first,
        } = take!(w
            .e
            .normalize_quotient(&mut self.ask(&w.spec), &lt, &labels)?);
        let rt = self.to_term(right);
        let Quotiented {
            over: second_items,
            under: second_under,
            proof: second,
        } = take!(w
            .e
            .normalize_quotient(&mut self.ask(&w.spec), &rt, &labels)?);
        if first_under.is_none() && second_under.is_none() {
            if Emitter::spell_run(&first_items) != Emitter::spell_run(&second_items) {
                return Ok(Route::no("the two are not one polynomial"));
            }
            return Ok(Built(self.b.ap(
                "eqtr4d",
                &binds! {"ph" => &w.spec.scope, "A" => left, "B" => Emitter::spell_run(&first_items), "C" => right},
                &[&first, &second],
            )));
        }
        self.cross_multiplied(
            w,
            left,
            right,
            (first_items, first_under, first),
            (second_items, second_under, second),
        )
    }

    /// Two quotients equal, because their cross product is.
    pub(super) fn cross_multiplied(
        &mut self,
        w: &mut Work,
        left: &Rpn,
        right: &Rpn,
        one: (Run, Option<Run>, Proof),
        other: (Run, Option<Run>, Proof),
    ) -> Checked<Route<Proof>> {
        let (over, under, first) =
            w.e.as_quotient(&mut self.ask(&w.spec), one.0, one.1, one.2, left)?;
        let (below, beneath, second) =
            w.e.as_quotient(&mut self.ask(&w.spec), other.0, other.1, other.2, right)?;
        let (a, b) = (Emitter::spell_run(&over), Emitter::spell_run(&under));
        let (c, d) = (Emitter::spell_run(&below), Emitter::spell_run(&beneath));
        let crossed = take!(self.same_polynomial(
            w,
            &t!(a, d, "cmul", "co"),
            &t!(c, b, "cmul", "co")
        )?);
        let p1 = w.e.pair_of(&mut self.ask(&w.spec), &beneath)?;
        let p2 = w.e.pair_of(&mut self.ask(&w.spec), &under)?;
        let (p1, p2) = (take!(p1), take!(p2));
        let u = w.spec.scope.clone();
        let rc1 = w.e.run_cc(&mut self.ask(&w.spec), &below)?;
        let rc2 = w.e.run_cc(&mut self.ask(&w.spec), &over)?;
        let pair = |x: &Rpn| t!(t!(x, "cc", "wcel"), t!(x, "cc0", "wne"), "wa");
        let turned = self.b.ap(
            "eqcomd",
            &binds! {"ph" => &u, "A" => t!(a, d, "cmul", "co"), "B" => t!(c, b, "cmul", "co")},
            &[&crossed],
        );
        let tops = self.b.ap("jca", &binds! {"ph" => &u, "ps" => t!(c, "cc", "wcel"), "ch" => t!(a, "cc", "wcel")}, &[&rc1, &rc2]);
        let bottoms = self.b.ap(
            "jca",
            &binds! {"ph" => &u, "ps" => pair(&d), "ch" => pair(&b)},
            &[&p1, &p2],
        );
        let law = self.b.ap(
            "divmuleq",
            &binds! {"A" => &c, "B" => &a, "C" => &d, "D" => &b},
            &[],
        );
        let quotients = t!(t!(c, d, "cdiv", "co"), t!(a, b, "cdiv", "co"), "wceq");
        let products = t!(t!(c, b, "cmul", "co"), t!(a, d, "cmul", "co"), "wceq");
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => &u, "ps" => t!(t!(c, "cc", "wcel"), t!(a, "cc", "wcel"), "wa"),
            "ch" => t!(pair(&d), pair(&b), "wa"), "th" => t!(quotients, products, "wb")},
            &[&tops, &bottoms, &law],
        );
        let back = self.b.ap(
            "mpbird",
            &binds! {"ph" => &u, "ps" => &quotients, "ch" => &products},
            &[&turned, &turn],
        );
        let across = self.b.ap(
            "eqtrd",
            &binds! {"ph" => &u, "A" => right, "B" => t!(c, d, "cdiv", "co"), "C" => t!(a, b, "cdiv", "co")},
            &[&second, &back],
        );
        Ok(Built(self.b.ap(
            "eqtr4d",
            &binds! {"ph" => &u, "A" => left, "B" => t!(a, b, "cdiv", "co"), "C" => right},
            &[&first, &across],
        )))
    }

    /// ( scope -> times · gap = 0 ) from ( scope -> gap = 0 ), `vanishes`:
    /// a multiple of 0 is 0 (`mul01d`), `times` a complex number by
    /// `times_cc`.
    pub(in crate::elab) fn multiple_vanishing(
        &self,
        gap: &Rpn,
        vanishes: &Proof,
        times: &Rpn,
        times_cc: &Proof,
        scope: &Rpn,
    ) -> Vanishing {
        let moved = self.b.ap(
            "oveq2d",
            &binds! {"ph" => scope, "A" => gap, "B" => "cc0", "C" => times, "F" => "cmul"},
            &[vanishes],
        );
        let zero =
            self.b
                .ap("mul01d", &binds! {"ph" => scope, "A" => times}, &[times_cc]);
        let term = t!(times, gap, "cmul", "co");
        let proof = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &term, "B" => t!(times, "cc0", "cmul", "co"), "C" => "cc0"},
            &[&moved, &zero],
        );
        Vanishing { term, proof }
    }

    /// ( scope -> t₁ + … + tₙ = 0 ), the terms added from the left, from
    /// each of them 0: 0 + 0 is 0 (`00id`). At least one term.
    pub(in crate::elab) fn vanishing_sum(
        &self,
        terms: &[Vanishing],
        scope: &Rpn,
    ) -> Vanishing {
        let naught = t!("cc0", "cc0", "caddc", "co");
        let mut sum = terms[0].clone();
        for one in &terms[1..] {
            let joined = t!(&sum.term, &one.term, "caddc", "co");
            let both = self.b.ap(
                "oveq12d",
                &binds! {"ph" => scope, "A" => &sum.term, "B" => "cc0", "C" => &one.term, "D" => "cc0", "F" => "caddc"},
                &[&sum.proof, &one.proof],
            );
            let zero = self.closed_law(&t!(&naught, "cc0", "wceq"), "00id", scope);
            sum = Vanishing {
                proof: self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &joined, "B" => &naught, "C" => "cc0"},
                    &[&both, &zero],
                ),
                term: joined,
            };
        }
        sum
    }

    /// A claim the cited equations add up to: each cited equation is a
    /// difference that is zero, multiplied by what the combination says and
    /// still zero; the sum of them is zero, and that sum is the claim's own
    /// difference, which is the normalizer's question.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn summed_from_cited(
        &mut self,
        step: &Step,
        left: &Rpn,
        right: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        w: &mut Work,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let claimed = self.to_term(&t!(left, right, "wceq"));
        let want = field::equation(&claimed, &labels);
        let mut given = Vec::new();
        let mut unders = Vec::new();
        let mut where_: Vec<(String, Term)> = Vec::new();
        // What each cited equation had divided out of it.
        let mut taken_out: Vec<Poly> = Vec::new();
        for r in &step.just.refs {
            for said in self.line_writes(r, lines) {
                let node = self.to_term(&said);
                if let Some(one) = field::equation(&node, &labels) {
                    let read = claim_says(&node, one, &labels);
                    given.push(read.says);
                    unders.push(field::exactly(
                        &denominators(&node, &labels),
                        &read.taken,
                    ));
                    taken_out.push(read.taken);
                    where_.push((r.clone(), node));
                }
            }
        }
        let Some(want) = want.filter(|_| !given.is_empty()) else {
            return Ok(Route::no("the step cites no equation"));
        };
        // The first reading of the claim the cited equations make, as the
        // decision found it (`readings`, `combination`).
        let claim_under = denominators(&claimed, &labels);
        let found = readings(&claimed, want, &labels)
            .into_iter()
            .find_map(|says| {
                combination(&given, &unders, &says, &claim_under)
                    .filter(|h| !h.is_empty())
                    .map(|how| (says, how))
            });
        let Some((says, how)) = found else {
            return Ok(Route::no("no sum of the cited equations is the claim"));
        };
        // The decision reads what the claim says (`claim_says`), and the
        // proof takes each cited equation as written: so each multiplier
        // carries its equation's denominators, and is divided by a divisor
        // of the claim's that every one carries; the claim's sides are each
        // multiplied by the divisors left, which are taken off at the end.
        let across = |node: &Term| denominators(node, &labels);
        let mut factors: Vec<Factor> = Vec::new();
        let mut written = says.taken.clone();
        for f in says.kept {
            let Some(f) = f else {
                return Ok(Route::no("a divisor that divides more than once"));
            };
            written = written.times(&field::read(f.term(), &labels).over);
            factors.push(f);
        }
        if written != across(&claimed) {
            return Ok(Route::no(
                "the divisors written are not the claim's denominators",
            ));
        }
        // A divisor every multiplier carries is divided out of them, and only
        // the rest multiply the claim's sides: (f(b) − f(a))/(b − a) from an
        // equation over b − a needs nothing multiplied.
        let mut multipliers: Vec<Poly> = Vec::new();
        for taken in &how {
            let carried = taken.multiplier().times(&across(&where_[taken.which].1));
            let Some(by) = field::exactly(&carried, &taken_out[taken.which]) else {
                return Ok(Route::no(
                    "a cited equation's divisors are not its denominators",
                ));
            };
            multipliers.push(by);
        }
        let mut multiplying: Vec<Factor> = Vec::new();
        for f in factors {
            let by = field::read(f.term(), &labels).over;
            let carried: Option<Vec<Poly>> =
                multipliers.iter().map(|p| field::exactly(p, &by)).collect();
            match carried {
                Some(divided) => multipliers = divided,
                None => multiplying.push(f),
            }
        }
        let factors = multiplying;
        // Weights with a denominator are all multiplied by the least common
        // one, which the sum then shows the claim's sides each multiplied
        // by, and which is cancelled at the end: s = t is half of
        // 2·s + 1 = 2·t + 1, and the proof doubles s = t instead.
        let common = field::common_denominator(
            multipliers.iter().flat_map(|p| p.terms.values()),
        );
        let Some(common) = common.to_i64() else {
            return Ok(Route::no("a common denominator past what a numeral writes"));
        };
        let mut pieces: Vec<Vanishing> = Vec::new();
        for (taken, by) in how.iter().zip(&multipliers) {
            let (r, node) = where_[taken.which].clone();
            let (a, b) = (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
            let gap = t!(a, b, "cmin", "co");
            let Some(times) =
                multiplier(&by.scaled(&Q::from_integer(BigInt::from(common))))
            else {
                return Ok(Route::no("a multiplier with no spelling"));
            };
            // A sum the decision read as linear is written over a placeholder
            // letter; in a proof it is the step's own (`sum_letter`).
            let times = match &self.sum_letter {
                Some(letter) => Rpn::from(
                    times
                        .tokens()
                        .iter()
                        .map(|t| if *t == "§" { Symbol::of(letter) } else { *t })
                        .collect::<Vec<_>>(),
                ),
                None if times.has("§") => {
                    return Ok(Route::no("a multiplier holding a sum read as linear"));
                }
                None => times,
            };
            let cited = self.cited_fact(&r, &node, scope, facts, lines)?;
            let a_cc = self.in_cc(&a, scope, facts)?;
            let b_cc = self.in_cc(&b, scope, facts)?;
            let (cited, a_cc, b_cc) = (take!(cited), take!(a_cc), take!(b_cc));
            let turn = self.b.ap(
                "subeq0ad",
                &binds! {"ph" => scope, "A" => &a, "B" => &b},
                &[&a_cc, &b_cc],
            );
            let vanishes = self.b.ap(
                "mpbird",
                &binds! {"ph" => scope, "ps" => t!(gap, "cc0", "wceq"), "ch" => t!(a, b, "wceq")},
                &[&cited, &turn],
            );
            let atom = self.membership(
                &times,
                "cc",
                &w.spec.scope.clone(),
                &w.spec.facts.clone(),
            )?;
            pieces.push(self.multiple_vanishing(&gap, &vanishes, &times, &atom, scope));
        }
        let Vanishing {
            term: total,
            proof: sums,
        } = self.vanishing_sum(&pieces, scope);
        // What the claim's sides are multiplied by: the common denominator of
        // the weights, then each divisor the claim writes.
        let mut spelt: Vec<Rpn> = factors.iter().map(|f| self.rpn(f.term())).collect();
        if common != 1 {
            spelt.insert(0, numerals::spell(common.unsigned_abs()));
        }
        let factor: Option<Rpn> = spelt
            .iter()
            .cloned()
            .reduce(|acc, one| t!(acc, one, "cmul", "co"));
        let sides: Vec<Rpn> = match &factor {
            None => vec![left.clone(), right.clone()],
            Some(factor) => [left, right]
                .iter()
                .map(|one| t!(factor, one, "cmul", "co"))
                .collect(),
        };
        let (l, r) = (&sides[0], &sides[1]);
        let whole = t!(l, r, "cmin", "co");
        let alike = self.same_polynomial(w, &total, &whole)?;
        let left_cc = self.in_cc(l, scope, facts)?;
        let right_cc = self.in_cc(r, scope, facts)?;
        let (alike, left_cc, right_cc) =
            (take!(alike), take!(left_cc), take!(right_cc));
        let reached = self.b.ap(
            "eqtr3d",
            &binds! {"ph" => scope, "A" => &total, "B" => &whole, "C" => "cc0"},
            &[&alike, &sums],
        );
        let turn = self.b.ap(
            "subeq0ad",
            &binds! {"ph" => scope, "A" => l, "B" => r},
            &[&left_cc, &right_cc],
        );
        let equal = self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(whole, "cc0", "wceq"), "ch" => t!(l, r, "wceq")},
            &[&reached, &turn],
        );
        let Some(factor) = factor else {
            return Ok(Built(equal));
        };
        let Built(apart) = self.factors_apart(w, common, &factors, scope, facts)?
        else {
            return Ok(Route::no("a divisor not known to be a number"));
        };
        self.cancelled_by(&factor, apart, left, right, &sides, equal, scope, facts)
            .map(Built)
    }

    /// ( scope -> ( F e. CC /\ F =/= 0 ) ) for F the numeral `common`, where
    /// it is not 1, times each of `factors` in turn: the numeral is not 0 as
    /// a numeral, and a divisor by what the page says of it, which a step
    /// that divides writes. The numerator c of a divisor c/e is not 0 by
    /// what the page says of c/e, carried to c by `divne0bd`; the −c of a
    /// divisor −(c/e) by `negated_top_apart`.
    pub(super) fn factors_apart(
        &mut self,
        w: &mut Work,
        common: i64,
        factors: &[Factor],
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut each: Vec<(Rpn, Proof, Proof)> = Vec::new();
        if common != 1 {
            let numeral = numerals::spell(common.unsigned_abs());
            let held = w.e.number(&self.ask(&w.spec), &BigInt::from(common));
            let apart = self.b.ap(
                "a1i",
                &binds! {"ph" => t!(numeral, "cc0", "wne"), "ps" => scope},
                &[&numerals::ne0(&self.b, common.unsigned_abs())],
            );
            each.push((numeral, held, apart));
        }
        for f in factors {
            let said = self.rpn(f.term());
            let held = take!(self.in_cc(&said, scope, facts)?);
            let apart = take!(self.factor_apart(f, &said, &held, scope, facts)?);
            each.push((said, held, apart));
        }
        let mut parts = each.into_iter();
        let (mut so_far, mut held, mut apart) =
            parts.next().expect("a factor at least");
        for (one, one_held, one_apart) in parts {
            let binds = binds! {"ph" => scope, "A" => &so_far, "B" => &one};
            apart =
                self.b
                    .ap("mulne0d", &binds, &[&held, &one_held, &apart, &one_apart]);
            held = self.b.ap("mulcld", &binds, &[&held, &one_held]);
            so_far = t!(so_far, one, "cmul", "co");
        }
        Ok(Built(self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(so_far, "cc", "wcel"), "ch" => t!(so_far, "cc0", "wne")},
            &[&held, &apart],
        )))
    }

    /// ( scope -> said =/= 0 ) for `said`, what the factor `f` multiplies a
    /// claim's sides by, held in ℂ by `held`: a divisor by what the page
    /// says of it; the numerator c of a divisor c/e by what the page says of
    /// c/e, carried to c by `divne0bd`; the −c of a divisor −(c/e) by
    /// `negated_top_apart`; and the product of a divisor X·Y's two parts'
    /// by each part's, joined by `mulne0d`.
    pub(super) fn factor_apart(
        &mut self,
        f: &Factor,
        said: &Rpn,
        held: &Proof,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        Ok(Built(match f {
            Factor::Divisor(_) => self.not_zero(scope, facts, said)?,
            Factor::Numerator { divisor, below, .. } => {
                let (whole, under) = (self.rpn(divisor), self.rpn(below));
                let whole_apart = self.not_zero(scope, facts, &whole)?;
                let under_apart = self.not_zero(scope, facts, &under)?;
                let under_cc = take!(self.in_cc(&under, scope, facts)?);
                let iff = self.b.ap(
                    "divne0bd",
                    &binds! {"ph" => scope, "A" => said, "B" => &under},
                    &[held, &under_cc, &under_apart],
                );
                self.b.ap(
                    "mpbird",
                    &binds! {"ph" => scope, "ps" => t!(said, "cc0", "wne"),
                    "ch" => t!(whole, "cc0", "wne")},
                    &[&whole_apart, &iff],
                )
            }
            Factor::NegatedNumerator {
                divisor,
                quotient,
                top,
                below,
                ..
            } => {
                let parts = NegatedQuotient {
                    divisor: self.rpn(divisor),
                    quotient: self.rpn(quotient),
                    top: self.rpn(top),
                    below: self.rpn(below),
                };
                take!(self.negated_top_apart(&parts, scope, facts)?)
            }
            Factor::Product { left, right, .. } => {
                let (x, y) = (self.rpn(left.term()), self.rpn(right.term()));
                let x_cc = take!(self.in_cc(&x, scope, facts)?);
                let y_cc = take!(self.in_cc(&y, scope, facts)?);
                let x_apart = take!(self.factor_apart(left, &x, &x_cc, scope, facts)?);
                let y_apart = take!(self.factor_apart(right, &y, &y_cc, scope, facts)?);
                self.b.ap(
                    "mulne0d",
                    &binds! {"ph" => scope, "A" => &x, "B" => &y},
                    &[&x_cc, &y_cc, &x_apart, &y_apart],
                )
            }
        }))
    }

    /// ( scope -> -u c =/= 0 ) for a divisor −(c/e) the page says is not 0:
    /// c/e is not 0 as its negation is not, c as c/e is not (`divne0bd`),
    /// and −c as c is not (`negne0bd` each way).
    pub(super) fn negated_top_apart(
        &mut self,
        parts: &NegatedQuotient,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let NegatedQuotient {
            divisor,
            quotient,
            top,
            below,
        } = parts;
        let ne0 = |t: &Rpn| t!(t, "cc0", "wne");
        let whole_apart = self.not_zero(scope, facts, divisor)?;
        let quotient_cc = take!(self.in_cc(quotient, scope, facts)?);
        let top_cc = take!(self.in_cc(top, scope, facts)?);
        let below_cc = take!(self.in_cc(below, scope, facts)?);
        let below_apart = self.not_zero(scope, facts, below)?;
        let quotient_turn = self.b.ap(
            "negne0bd",
            &binds! {"ph" => scope, "A" => quotient},
            &[&quotient_cc],
        );
        let quotient_apart = self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => ne0(quotient), "ch" => ne0(divisor)},
            &[&whole_apart, &quotient_turn],
        );
        let divided = self.b.ap(
            "divne0bd",
            &binds! {"ph" => scope, "A" => top, "B" => below},
            &[&top_cc, &below_cc, &below_apart],
        );
        let top_apart = self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => ne0(top), "ch" => ne0(quotient)},
            &[&quotient_apart, &divided],
        );
        let top_turn =
            self.b
                .ap("negne0bd", &binds! {"ph" => scope, "A" => top}, &[&top_cc]);
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => ne0(top), "ch" => ne0(&t!(top, "cneg"))},
            &[&top_apart, &top_turn],
        )))
    }

    /// ( scope -> said e. CC ), for a term of the step's own depth: built by
    /// `part` first, from the step's own lines, and searched for where that
    /// cannot, to the depth every side condition is searched to.
    pub(in crate::elab) fn in_cc(
        &mut self,
        said: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let found = self.part(said, &t!("cc"), scope, facts)?;
        if !found.is_declined() {
            return Ok(found);
        }
        self.within(said, &t!("cc"), scope, facts, 3)
    }

    /// A claim a cited equation is a whole multiple of: proving each side is
    /// that multiple is the polynomial case again, and what is left is
    /// cancelling the multiplier.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn scaled_from_cited(
        &mut self,
        step: &Step,
        left: &Rpn,
        right: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        w: &mut Work,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let want = field::equation(&self.to_term(&t!(left, right, "wceq")), &labels);
        for r in &step.just.refs {
            let Some(held) = self.line_written(r, lines) else {
                continue;
            };
            let cited = self.to_term(&held.claim);
            if cited.variable().is_some() || cited.label() != Some("wceq") {
                continue;
            }
            let times = whole_multiple(
                field::equation(&cited, &labels).as_ref(),
                want.as_ref(),
            );
            let Some(times) = times else {
                continue;
            };
            let numeral = numerals::spell(times.unsigned_abs());
            let scaled: Vec<Rpn> = [left, right]
                .iter()
                .map(|one| t!(numeral, one, "cmul", "co"))
                .collect();
            let was: Vec<Rpn> = cited.children().iter().map(|c| self.rpn(c)).collect();
            let mut sides = Vec::new();
            for (x, y) in was.iter().zip(&scaled) {
                sides.push(self.same_polynomial(w, x, y)?);
            }
            if sides.iter().any(|s| s.is_declined()) {
                continue;
            }
            let sides: Vec<Proof> =
                sides.into_iter().filter_map(|s| s.built()).collect();
            let given = self.carried(r, facts, lines);
            return self
                .cancel_multiple(
                    w, times, left, right, &scaled, &sides, given, &cited, scope, facts,
                )
                .map(Built);
        }
        Ok(Route::no("no cited equation is a multiple of the claim"))
    }

    /// The multiplier taken off both sides, which is `mulcan`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn cancel_multiple(
        &mut self,
        w: &mut Work,
        times: i64,
        left: &Rpn,
        right: &Rpn,
        scaled: &[Rpn],
        sides: &[Proof],
        given: Proof,
        cited: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let matched = self.b.ap(
            "3eqtr3d",
            &binds! {"ph" => scope, "A" => self.rpn(&cited.children()[0]), "B" => self.rpn(&cited.children()[1]),
            "C" => &scaled[0], "D" => &scaled[1]},
            &[&given, &sides[0], &sides[1]],
        );
        let Built(both) = self.factors_apart(w, times, &[], scope, facts)? else {
            unreachable!("a numeral is a number and not 0");
        };
        let numeral = numerals::spell(times.unsigned_abs());
        self.cancelled_by(&numeral, both, left, right, scaled, matched, scope, facts)
    }

    /// ( scope -> left = right ) from `matched`, which proves the two sides
    /// `scaled`, each `factor` times its own side, and `both`, which says
    /// `factor` is a number and not 0: `mulcan` takes it off.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn cancelled_by(
        &mut self,
        factor: &Rpn,
        both: Proof,
        left: &Rpn,
        right: &Rpn,
        scaled: &[Rpn],
        matched: Proof,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let ml = self.membership(left, "cc", scope, facts)?;
        let mr = self.membership(right, "cc", scope, facts)?;
        let law = self.b.ap(
            "mulcan",
            &binds! {"A" => left, "B" => right, "C" => factor},
            &[],
        );
        let turn = self.b.ap(
            "syl3anc",
            &binds! {"ph" => scope, "ps" => t!(left, "cc", "wcel"), "ch" => t!(right, "cc", "wcel"),
            "th" => t!(t!(factor, "cc", "wcel"), t!(factor, "cc0", "wne"), "wa"),
            "ta" => t!(t!(scaled[0], scaled[1], "wceq"), t!(left, right, "wceq"), "wb")},
            &[&ml, &mr, &both, &law],
        );
        Ok(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(scaled[0], scaled[1], "wceq"), "ch" => t!(left, right, "wceq")},
            &[&matched, &turn],
        ))
    }

    /// Closed numerals, worked out and then said. Nothing is taken as
    /// stated: the claim is worked out first, so what cannot be proved is
    /// reported as what it is.
    pub fn arithmetic(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let what = format!("step {} claims {}", step.number, step.claim.text());
        self.closed_fact(term, scope, facts, &what, Some(step))
            .map(Built)
    }

    /// A fact about closed numerals, worked out and then proved, wherever it
    /// stands; `what` says where it was asked, as the page writes it.
    pub fn closed_fact(
        &mut self,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        what: &str,
        step: Option<&Step>,
    ) -> Checked<Proof> {
        let said = self.to_term(term);
        // A claim of several sentences, `2 + 2 = 4. 3 + 3 = 6.`, is each of
        // them worked out, as the checker decides each.
        let parts = self.conjoined(&said, scope, &mut |me, one| {
            let one = me.rpn(one);
            me.closed_fact(&one, scope, facts, what, step).map(Built)
        })?;
        if let Some(Built(p)) = parts {
            return Ok(p);
        }
        if let Some(pairs) = pairs::relation(&said) {
            return self.closed_pairs(&pairs, term, scope, facts, what, step);
        }
        if let Built(p) = self.prove_numeral(term, scope, facts)? {
            return Ok(p);
        }
        // A remainder or a product over a range is no atom of the normaliser's:
        // a claim holding one is said of its sides' values.
        if !self.normaliser_opaque(&said) {
            if let Built(p) =
                self.prove_field(step, term, scope, facts, &Lines::new())?
            {
                return Ok(p);
            }
        }
        if let Built(p) = self.by_values(term, scope, facts)? {
            return Ok(p);
        }
        Err(self.unshown(term, what))
    }

    /// Two pairs of closed terms, compared coordinate by coordinate
    /// (`METHODS.md`, Pairs): both coordinates' equations, or the
    /// difference at the first coordinate whose equation is false.
    pub(super) fn closed_pairs(
        &mut self,
        pairs: &PairRelation,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        what: &str,
        step: Option<&Step>,
    ) -> Checked<Proof> {
        if !pairs.apart {
            let mut proved = Vec::new();
            for at in Coordinate::BOTH {
                let equation = self.rpn(&pairs.equation(at));
                proved.push(self.closed_fact(&equation, scope, facts, what, step)?);
            }
            return Ok(self.pairs_equal(pairs, scope, &proved[0], &proved[1]));
        }
        let Some(at) = pairs.apart_at(&mut closed_equal) else {
            return Err(self.unshown(term, what));
        };
        let denial = self.rpn(&pairs.denial(at));
        let apart = self.closed_fact(&denial, scope, facts, what, step)?;
        let members = self.number_members(pairs, scope, facts)?;
        Ok(self.pairs_apart(pairs, scope, at, &apart, &members))
    }

    /// Whether a term holds what the normaliser holds as an atom where
    /// `arithmetic` works it out: a remainder, a product over a range, or a
    /// power to an exponent below 0.
    pub(in crate::elab) fn normaliser_opaque(&self, t: &Term) -> bool {
        let said = self.rpn(t);
        said.has("cmo") || said.has("cprod") || negative_power(t)
    }
}
