//! Normalising, quotients and cancelling.

use super::*;

impl Emitter {
    /// (items, ( under -> term = spell_run(items) )).
    ///
    /// Recursion on the term, not a search: at each node the children are
    /// already canonical and what remains is one of the operations above. A
    /// subterm this does not recognise is an atom, and the oracle is asked
    /// once for its membership.
    pub fn normalize(
        &mut self,
        o: &mut dyn Oracle,
        term: &Term,
        labels: &FloatLabels,
    ) -> Checked<Route<(Run, Proof)>> {
        let said = term.rpn(labels);
        if term.variable().is_none() {
            if let Some(value) = numerals::value(term) {
                let value = BigInt::from(value);
                if value.is_zero() {
                    // The empty run, not a term of weight zero: a canonical
                    // form holds no such term, and one left in it would be
                    // carried through every sum it took part in.
                    return Ok(Built((Vec::new(), self.same(o, &n(0)))));
                }
                if value == big(1) {
                    return Ok(Built((vec![(Vec::new(), q(1))], self.one_as_term(o))));
                }
                let product = self.positive_product(o, &value, &big(1));
                let p = o.b().ap(
                    "eqcomd",
                    &binds! {"ph" => &self.under, "A" => op(&spelt(&value), &n(1), MUL),
                    "B" => spelt(&value)},
                    &[&product],
                );
                return Ok(Built((vec![(Vec::new(), Q::from_integer(value))], p)));
            }
        }
        if term.variable().is_none()
            && term.label() == Some("cneg")
            && term.children().len() == 1
        {
            let (items, proof) =
                take!(self.normalize(o, &term.children()[0], labels)?);
            let inner = term.children()[0].rpn(labels);
            return self.negated(o, &inner, &items, proof, &said);
        }
        // A finite sum is linear: it is written out as its parts' sums, each
        // scaled by what is free of its letter, and that is normalised.
        if term.variable().is_none() && term.label() == Some("csu") {
            if let Built((linear, written)) = o.linear_sum(&said)? {
                let spelt = linear.rpn(labels);
                let (items, proof) = take!(self.normalize(o, &linear, labels)?);
                let p = self.chain(
                    o,
                    &written,
                    &proof,
                    &said,
                    &spelt,
                    &Self::spell_run(&items),
                );
                return Ok(Built((items, p)));
            }
        }
        if let Some(how) = Op::applied(term) {
            let (left, right) = (&term.children()[0], &term.children()[1]);
            if matches!(how, Op::Add | Op::Sub | Op::Mul) {
                return self.binary(o, how, left, right, labels, &said);
            }
            if how == Op::Exp {
                // The exponent rule, as `field` states it where the same
                // claim is decided: a numeral exponent is expanded, and any
                // other, or a power past what may be multiplied out, leaves
                // the whole power an atom.
                if let field::Power::Expanded { by: times, .. } =
                    field::power_of(left, right, labels)
                {
                    let (inner, proof) = take!(self.normalize(o, left, labels)?);
                    let (out, raised) = take!(self.power(o, &inner, times)?);
                    let moved = o.b().ap(
                        "oveq1d",
                        &binds! {"ph" => &self.under, "A" => left.rpn(labels),
                        "B" => Self::spell_run(&inner), "C" => n(times), "F" => EXP},
                        &[&proof],
                    );
                    let p = self.chain(
                        o,
                        &moved,
                        &raised,
                        &said,
                        &op(&Self::spell_run(&inner), &n(times), EXP),
                        &Self::spell_run(&out),
                    );
                    return Ok(Built((out, p)));
                }
                // An exponent that is one atom alone is that atom, as
                // `field` reads it: 2^(d·1) is 2^d.
                if let Some(name) = field::exponent_atom(right, labels) {
                    let exponent = right.rpn(labels);
                    let (run, to_run) = take!(self.normalize(o, right, labels)?);
                    let (_, from_name) = self.as_atom(o, &name)?;
                    let spelt = Self::spell_run(&run);
                    let b = o.b();
                    let is_name = b.ap(
                        "eqtr4d",
                        &binds! {"ph" => &self.under, "A" => &exponent, "B" => &spelt, "C" => &name},
                        &[&to_run, &from_name],
                    );
                    let base = left.rpn(labels);
                    let over = op(&base, &name, EXP);
                    let moved = b.ap(
                        "oveq2d",
                        &binds! {"ph" => &self.under, "A" => &exponent, "B" => &name,
                        "C" => &base, "F" => EXP},
                        &[&is_name],
                    );
                    let (out, atom) = self.as_atom(o, &over)?;
                    let p = self.chain(
                        o,
                        &moved,
                        &atom,
                        &said,
                        &over,
                        &Self::spell_run(&out),
                    );
                    return Ok(Built((out, p)));
                }
                return self.as_atom(o, &said).map(Built);
            }
            if how == Op::Div {
                return Ok(named_decline(
                    "{} divides, which is cross-multiplied",
                    &said,
                ));
            }
        }
        self.as_atom(o, &said).map(Built)
    }

    /// A subterm nothing above recognises, as `( 1 x. ( t ^ 1 ) )`.
    pub(super) fn as_atom(
        &mut self,
        o: &mut dyn Oracle,
        said: &Rpn,
    ) -> Checked<(Run, Proof)> {
        let raised = op(said, &n(1), EXP);
        let atom = o.atom(said)?;
        let name = said.clone();
        let fc = self.factor_cc(o, &name, 1)?;
        let b = o.b();
        let law = b.ap("exp1", &binds! {"A" => said}, &[]);
        let inner = b.ap(
            "syl",
            &binds! {"ph" => &self.under, "ps" => t!(said, "cc", "wcel"),
            "ch" => t!(raised, said, "wceq")},
            &[&atom, &law],
        );
        let first = b.ap(
            "eqcomd",
            &binds! {"ph" => &self.under, "A" => &raised, "B" => said},
            &[&inner],
        );
        let law = b.ap("mullid", &binds! {"A" => &raised}, &[]);
        let inner = b.ap(
            "syl",
            &binds! {"ph" => &self.under, "ps" => t!(raised, "cc", "wcel"),
            "ch" => t!(op(&n(1), &raised, MUL), raised, "wceq")},
            &[&fc, &law],
        );
        let second = b.ap(
            "eqcomd",
            &binds! {"ph" => &self.under, "A" => op(&n(1), &raised, MUL), "B" => &raised},
            &[&inner],
        );
        let p = self.chain(o, &first, &second, said, &raised, &op(&n(1), &raised, MUL));
        Ok((vec![(vec![(name, 1)], q(1))], p))
    }

    /// -u X, taken as ( -u 1 ) x. X so that `multiply` does the work. The
    /// minus one is written the way a canonical form writes a constant,
    /// `( -u 1 x. 1 )`, before `multiply` will take it, which `mulrid`
    /// supplies.
    pub(super) fn negated(
        &mut self,
        o: &mut dyn Oracle,
        inner: &Rpn,
        items: &[(Monomial, Q)],
        proof: Proof,
        said: &Rpn,
    ) -> Checked<Route<(Run, Proof)>> {
        let run = Self::spell_run(items);
        let minus: Run = vec![(Vec::new(), q(-1))];
        let bare = t!(&n(1), "cneg");
        let unit = Self::spell_run(&minus);
        let rc = self.run_cc(o, items)?;
        let inner_cc = o.b().ap(
            "eqeltrd",
            &binds! {"ph" => &self.under, "A" => inner, "B" => &run, "C" => "cc"},
            &[&proof, &rc],
        );
        let becomes = {
            let b = o.b();
            let law = b.ap("mulm1", &binds! {"A" => inner}, &[]);
            let turned = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(inner, "cc", "wcel"),
                "ch" => t!(op(&bare, inner, MUL), said, "wceq")},
                &[&inner_cc, &law],
            );
            b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => op(&bare, inner, MUL), "B" => said},
                &[&turned],
            )
        };
        let inside = o.b().ap(
            "oveq2d",
            &binds! {"ph" => &self.under, "A" => inner, "B" => &run, "C" => &bare, "F" => MUL},
            &[&proof],
        );
        let minus_cc = self.coefficient(o, &q(-1));
        let spelt = {
            let b = o.b();
            let law = b.ap("mulrid", &binds! {"A" => &bare}, &[]);
            let turned = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(bare, "cc", "wcel"),
                "ch" => t!(unit, bare, "wceq")},
                &[&minus_cc, &law],
            );
            let back = b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => &unit, "B" => &bare},
                &[&turned],
            );
            b.ap(
                "oveq1d",
                &binds! {"ph" => &self.under, "A" => &bare, "B" => &unit, "C" => &run, "F" => MUL},
                &[&back],
            )
        };
        let (out, product) = take!(self.multiply(o, &minus, items)?);
        let one = self.chain(
            o,
            &becomes,
            &inside,
            said,
            &op(&bare, inner, MUL),
            &op(&bare, &run, MUL),
        );
        let two = self.chain(
            o,
            &one,
            &spelt,
            said,
            &op(&bare, &run, MUL),
            &op(&unit, &run, MUL),
        );
        let p = self.chain(
            o,
            &two,
            &product,
            said,
            &op(&unit, &run, MUL),
            &Self::spell_run(&out),
        );
        Ok(Built((out, p)))
    }

    /// X - Y, turned into X + -u Y, which the sum side already does:
    /// `negsub` states the two as equal one way round, so it is read
    /// backwards, and the negation is then the case already written.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn subtracted(
        &mut self,
        o: &mut dyn Oracle,
        la: &Rpn,
        lb: &Rpn,
        first: &[(Monomial, Q)],
        one: Proof,
        second: &[(Monomial, Q)],
        two: Proof,
        said: &Rpn,
    ) -> Checked<Route<(Run, Proof)>> {
        let rc1 = self.run_cc(o, first)?;
        let a_cc = o.b().ap(
            "eqeltrd",
            &binds! {"ph" => &self.under, "A" => la, "B" => Self::spell_run(first), "C" => "cc"},
            &[&one, &rc1],
        );
        let rc2 = self.run_cc(o, second)?;
        let b_cc = o.b().ap(
            "eqeltrd",
            &binds! {"ph" => &self.under, "A" => lb, "B" => Self::spell_run(second), "C" => "cc"},
            &[&two, &rc2],
        );
        let minus = t!(lb, "cneg");
        let plus = op(la, &minus, ADD);
        let turned = {
            let b = o.b();
            let law = b.ap("negsub", &binds! {"A" => la, "B" => lb}, &[]);
            let inner = b.ap(
                "syl2anc",
                &binds! {"ph" => &self.under, "ps" => t!(la, "cc", "wcel"),
                "ch" => t!(lb, "cc", "wcel"), "th" => t!(plus, said, "wceq")},
                &[&a_cc, &b_cc, &law],
            );
            b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => &plus, "B" => said},
                &[&inner],
            )
        };
        let (negated, backwards) = take!(self.negated(o, lb, second, two, &minus)?);
        let joined = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => la, "B" => Self::spell_run(first),
            "C" => &minus, "D" => Self::spell_run(&negated), "F" => ADD},
            &[&one, &backwards],
        );
        let (out, combined) = take!(self.add(o, first, &negated)?);
        let middle = op(&Self::spell_run(first), &Self::spell_run(&negated), ADD);
        let head = self.chain(o, &turned, &joined, said, &plus, &middle);
        let p = self.chain(o, &head, &combined, said, &middle, &Self::spell_run(&out));
        Ok(Built((out, p)))
    }

    /// `+`, `-` or `x.` with both sides taken to canonical form first.
    pub(super) fn binary(
        &mut self,
        o: &mut dyn Oracle,
        how: Op,
        left: &Term,
        right: &Term,
        labels: &FloatLabels,
        said: &Rpn,
    ) -> Checked<Route<(Run, Proof)>> {
        let (first, one) = take!(self.normalize(o, left, labels)?);
        let (second, two) = take!(self.normalize(o, right, labels)?);
        if how == Op::Sub {
            return self.subtracted(
                o,
                &left.rpn(labels),
                &right.rpn(labels),
                &first,
                one,
                &second,
                two,
                said,
            );
        }
        let what = if how == Op::Add { ADD } else { MUL };
        let joined = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => left.rpn(labels),
            "B" => Self::spell_run(&first), "C" => right.rpn(labels),
            "D" => Self::spell_run(&second), "F" => what},
            &[&one, &two],
        );
        let made = if how == Op::Add {
            self.add(o, &first, &second)?
        } else {
            self.multiply(o, &first, &second)?
        };
        let (out, combined) = take!(made);
        let middle = op(&Self::spell_run(&first), &Self::spell_run(&second), what);
        let p =
            self.chain(o, &joined, &combined, said, &middle, &Self::spell_run(&out));
        Ok(Built((out, p)))
    }

    // --- quotients ------------------------------------------------------
    //
    // A canonical form with a denominator is a pair rather than a polynomial
    // with fractions in it. Everything above keeps working on the numerator,
    // because its coefficients stay whole; what is added here is bookkeeping
    // on a second polynomial, and the four laws that say how the two travel
    // through a sum, a product, a division and a power.

    /// The canonical term for a pair, or for a numerator on its own.
    pub fn spell_quotient(
        over: &[(Monomial, Q)],
        under: Option<&[(Monomial, Q)]>,
    ) -> Rpn {
        match under {
            None => Self::spell_run(over),
            Some(under) => op(&Self::spell_run(over), &Self::spell_run(under), DIV),
        }
    }

    /// ( under -> d e. CC ) and ( under -> d =/= 0 ) for a denominator.
    ///
    /// A denominator that is a number says for itself that it is not zero,
    /// since the canonical form of a constant is `( n x. 1 )` and the scope
    /// knows only about the `n`.
    pub(super) fn denominator(
        &mut self,
        o: &mut dyn Oracle,
        under: &[(Monomial, Q)],
    ) -> Checked<Route<(Proof, Proof)>> {
        let said = Self::spell_run(under);
        // A numeral is not zero as a numeral. Otherwise what was kept while
        // the denominator was made (`keep_nonzero`) comes first, from the
        // factors the step's own lines say are not zero, then a line the
        // step may rest on, then a denominator of one term from its atoms,
        // then any line the page writes in scope, then the oracle's search:
        // the order of `Elaborator::divisor_apart`. A page saying x·y ≠ 0
        // says nothing of x alone, nor x² ≠ 0, which makes 10·x² a
        // denominator not zero where it is made.
        if let [(monomial, weight)] = under {
            if monomial.is_empty() && weight.is_integer() && !weight.is_zero() {
                let apart = take!(self.term_apart(o, monomial, weight)?);
                let rc = self.run_cc(o, under)?;
                return Ok(Built((rc, apart)));
            }
        }
        if let Some(kept) = self.nonzero.get(&said).cloned() {
            let rc = self.run_cc(o, under)?;
            return Ok(Built((rc, kept)));
        }
        if let Some(positive) = o.positive(&said)? {
            let rc = self.run_cc(o, under)?;
            return Ok(Built((rc, positive)));
        }
        let named = if self.written { o.named(&said)? } else { None };
        if let Some(named) = named {
            let rc = self.run_cc(o, under)?;
            return Ok(Built((rc, named)));
        }
        if let [(monomial, weight)] = under {
            if weight.is_integer() && !weight.is_zero() {
                if let Built(apart) = self.term_apart(o, monomial, weight)? {
                    let rc = self.run_cc(o, under)?;
                    return Ok(Built((rc, apart)));
                }
            }
        }
        let page = if self.written {
            o.written(&said)?
        } else {
            None
        };
        if let Some(page) = page {
            let rc = self.run_cc(o, under)?;
            return Ok(Built((rc, page)));
        }
        let named = self
            .divisors
            .get(&said)
            .cloned()
            .unwrap_or_else(|| said.clone());
        if !self.apart {
            return Ok(Route::no(format!(
                "nothing says {} ≠ 0, which this step needs to divide by it",
                o.shown(&named)
            )));
        }
        let rc = self.run_cc(o, under)?;
        let apart = o.apart(&said, &named)?;
        Ok(Built((rc, apart)))
    }

    /// Keep that `run` is not zero, from `whole` not being zero and
    /// ( under -> whole = run ).
    ///
    /// A denominator the normaliser makes by multiplying two out is one the
    /// page never wrote: 2/k − 2/(k + 1) lands on k² + k. That it is not
    /// zero is known where it is made, from its factors, and not afterwards,
    /// when it is one polynomial.
    pub(super) fn keep_nonzero(
        &mut self,
        o: &dyn Oracle,
        whole: &Rpn,
        run: &[(Monomial, Q)],
        apart: &Proof,
        equal: &Proof,
    ) {
        let said = Self::spell_run(run);
        if self.nonzero.contains_key(&said) {
            return;
        }
        let b = o.b();
        let moved = b.ap(
            "neeq1d",
            &binds! {"ph" => &self.under, "A" => whole, "B" => &said, "C" => "cc0"},
            &[equal],
        );
        let kept = b.ap(
            "mpbid",
            &binds! {"ph" => &self.under, "ps" => t!(whole, "cc0", "wne"),
            "ch" => t!(said, "cc0", "wne")},
            &[apart, &moved],
        );
        self.nonzero.insert(said, kept);
    }

    /// `keep_nonzero` for a denominator that is two multiplied out.
    pub(super) fn keep_product(
        &mut self,
        o: &mut dyn Oracle,
        one: &[(Monomial, Q)],
        other: &[(Monomial, Q)],
        run: &[(Monomial, Q)],
        equal: &Proof,
    ) -> Checked<()> {
        let first = self.denominator(o, one)?;
        let second = self.denominator(o, other)?;
        let (Built((held_a, apart_a)), Built((held_b, apart_b))) = (first, second)
        else {
            return Ok(());
        };
        let (a, b) = (Self::spell_run(one), Self::spell_run(other));
        let apart = o.b().ap(
            "mulne0d",
            &binds! {"ph" => &self.under, "A" => &a, "B" => &b},
            &[&held_a, &held_b, &apart_a, &apart_b],
        );
        self.keep_nonzero(o, &op(&a, &b, MUL), run, &apart, equal);
        Ok(())
    }

    /// ( under -> ( c x. M ) =/= 0 ), for a denominator of one term.
    ///
    /// The scope knows about the atoms; the canonical form it is asked about
    /// is `( c x. ( x ^ k ) )`, which the scope has never heard of. A product
    /// is not zero when neither side is, and a power is not when what it
    /// raises is not, so the whole of it comes off the atoms the scope does
    /// know.
    pub(super) fn term_apart(
        &mut self,
        o: &mut dyn Oracle,
        monomial: &Monomial,
        weight: &Q,
    ) -> Checked<Route<Proof>> {
        let digit = coeff(weight);
        let numerator = weight.numer().clone();
        let magnitude = numerator.abs();
        let mut nonzero = self.a1i(
            o,
            &t!(spelt(&magnitude), "cc0", "wne"),
            &numerals::ne0(o.b(), magnitude.magnitude().clone()),
        );
        if numerator.is_negative() {
            let num = self.number(o, &magnitude);
            nonzero = o.b().ap(
                "negne0d",
                &binds! {"ph" => &self.under, "A" => spelt(&magnitude)},
                &[&num, &nonzero],
            );
        }
        let spelt = spell_monomial(monomial);
        let apart = take!(self.monomial_apart(o, monomial)?);
        let c = self.coefficient(o, weight);
        let m = self.monomial_cc(o, monomial)?;
        Ok(Built(o.b().ap(
            "mulne0d",
            &binds! {"ph" => &self.under, "A" => &digit, "B" => &spelt},
            &[&c, &m, &nonzero, &apart],
        )))
    }

    /// ( under -> M =/= 0 ), the empty one being one.
    pub(super) fn monomial_apart(
        &mut self,
        o: &mut dyn Oracle,
        monomial: &Monomial,
    ) -> Checked<Route<Proof>> {
        if monomial.is_empty() {
            return Ok(Built(self.a1i(
                o,
                &t!(&n(1), "cc0", "wne"),
                &numerals::ne0(o.b(), 1u32),
            )));
        }
        let mut out: Option<(Proof, Rpn, Proof)> = None;
        for (name, power) in monomial {
            let spelt = op(name, &n(*power), EXP);
            let apart = take!(o.nonzero(name, true)?);
            let atom = o.atom(name)?;
            let wi = self.whole_index(o, *power);
            let one = o.b().ap(
                "expne0d",
                &binds! {"ph" => &self.under, "A" => name, "N" => n(*power)},
                &[&atom, &apart, &wi],
            );
            let mine = self.factor_cc(o, name, *power)?;
            out = Some(match out {
                None => (one, spelt, mine),
                Some((acc, running, held)) => {
                    let b = o.b();
                    let next = b.ap(
                        "mulne0d",
                        &binds! {"ph" => &self.under, "A" => &running, "B" => &spelt},
                        &[&held, &mine, &acc, &one],
                    );
                    let held = b.ap(
                        "mulcld",
                        &binds! {"ph" => &self.under, "A" => &running, "B" => &spelt},
                        &[&held, &mine],
                    );
                    (next, op(&running, &spelt, MUL), held)
                }
            });
        }
        Ok(Built(out.expect("a monomial of one factor at least").0))
    }

    /// ( under -> k e. ZZ ), which `expne0d` asks for: k is in ℕ
    /// (`numerals::nn`), and `nnzi` carries that to ℤ; set.mm names k ∈ ℤ
    /// only up to 3.
    pub(super) fn whole_index(&self, o: &dyn Oracle, power: u32) -> Proof {
        let natural = numerals::nn(o.b(), power as u64);
        let whole = o.b().ap("nnzi", &binds! {"N" => n(power)}, &[&natural]);
        self.a1i(o, &t!(&n(power), "cz", "wcel"), &whole)
    }

    /// A numerator on its own, given the denominator of one it hides: `div1`
    /// says a term over one is the term, so it is what promotes a polynomial
    /// into the pair the laws below want.
    pub fn as_quotient(
        &mut self,
        o: &mut dyn Oracle,
        over: Run,
        under: Option<Run>,
        proof: Proof,
        said: &Rpn,
    ) -> Checked<(Run, Run, Proof)> {
        if let Some(under) = under {
            return Ok((over, under, proof));
        }
        let one: Run = vec![(Vec::new(), q(1))];
        let run = Self::spell_run(&over);
        let unit = Self::spell_run(&one);
        // One in canonical form is `( 1 x. 1 )`, so the denominator is tidied
        // to that first.
        let unit_proof = self.one_as_term(o);
        let rc = self.run_cc(o, &over)?;
        let back = {
            let b = o.b();
            let turned = b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => n(1), "B" => &unit},
                &[&unit_proof],
            );
            let first = b.ap(
                "oveq2d",
                &binds! {"ph" => &self.under, "A" => &unit, "B" => n(1), "C" => &run, "F" => DIV},
                &[&turned],
            );
            let law = b.ap("div1", &binds! {"A" => &run}, &[]);
            let second = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(run, "cc", "wcel"),
                "ch" => t!(op(&run, &n(1), DIV), run, "wceq")},
                &[&rc, &law],
            );
            self.chain(
                o,
                &first,
                &second,
                &op(&run, &unit, DIV),
                &op(&run, &n(1), DIV),
                &run,
            )
        };
        let flipped = o.b().ap(
            "eqcomd",
            &binds! {"ph" => &self.under, "A" => op(&run, &unit, DIV), "B" => &run},
            &[&back],
        );
        let p = self.chain(o, &proof, &flipped, said, &run, &op(&run, &unit, DIV));
        Ok((over, one, p))
    }

    /// (over, under, ( under -> term = over / under )).
    ///
    /// `under` is None where the term divides nothing, and the proof is then
    /// of the numerator alone: a term that divides nothing must not be made
    /// to carry a denominator of one, or every caller's output would change.
    pub fn normalize_quotient(
        &mut self,
        o: &mut dyn Oracle,
        term: &Term,
        labels: &FloatLabels,
    ) -> Checked<Route<Quotiented>> {
        let said = term.rpn(labels);
        if !divides(term) {
            let (items, proof) = take!(self.normalize(o, term, labels)?);
            return Ok(Built(Quotiented {
                over: items,
                under: None,
                proof,
            }));
        }
        if term.variable().is_none()
            && term.label() == Some("cneg")
            && term.children().len() == 1
        {
            return self.quotient_negated(o, &term.children()[0], labels, &said);
        }
        if let Some(how) = Op::applied(term) {
            let (left, right) = (&term.children()[0], &term.children()[1]);
            match how {
                Op::Div => return self.quotient_of(o, left, right, labels, &said),
                Op::Add | Op::Sub | Op::Mul => {
                    return self.quotient_joined(o, how, left, right, labels, &said)
                }
                Op::Exp => return self.quotient_raised(o, left, right, labels, &said),
            }
        }
        Ok(named_decline(
            "{} divides somewhere this does not reach",
            &said,
        ))
    }

    /// `-u x`, where x divides: x is normalised to `a / b`, `divnegd` moves
    /// the sign onto the numerator, and `-u a` is negated as a term that
    /// divides nothing is.
    pub(super) fn quotient_negated(
        &mut self,
        o: &mut dyn Oracle,
        inner: &Term,
        labels: &FloatLabels,
        said: &Rpn,
    ) -> Checked<Route<Quotiented>> {
        let Quotiented {
            over,
            under,
            proof: first,
        } = take!(self.normalize_quotient(o, inner, labels)?);
        let inner_s = inner.rpn(labels);
        let Some(under) = under else {
            let (items, p) = take!(self.negated(o, &inner_s, &over, first, said)?);
            return Ok(Built(Quotiented {
                over: items,
                under: None,
                proof: p,
            }));
        };
        let (a, b) = (Self::spell_run(&over), Self::spell_run(&under));
        let quotient = op(&a, &b, DIV);
        let moved = o.b().ap(
            "negeqd",
            &binds! {"ph" => &self.under, "A" => &inner_s, "B" => &quotient},
            &[&first],
        );
        let rc = self.run_cc(o, &over)?;
        let (held, nonzero) = take!(self.denominator(o, &under)?);
        let law = o.b().ap(
            "divnegd",
            &binds! {"ph" => &self.under, "A" => &a, "B" => &b},
            &[&rc, &held, &nonzero],
        );
        let negated_top = t!(a, "cneg");
        let signed = self.chain(
            o,
            &moved,
            &law,
            said,
            &t!(quotient, "cneg"),
            &op(&negated_top, &b, DIV),
        );
        let refl = self.same(o, &a);
        let (top, p) = take!(self.negated(o, &a, &over, refl, &negated_top)?);
        let lifted = o.b().ap(
            "oveq1d",
            &binds! {"ph" => &self.under, "A" => &negated_top,
            "B" => Self::spell_run(&top), "C" => &b, "F" => DIV},
            &[&p],
        );
        let whole = self.chain(
            o,
            &signed,
            &lifted,
            said,
            &op(&negated_top, &b, DIV),
            &op(&Self::spell_run(&top), &b, DIV),
        );
        Ok(Built(Quotiented {
            over: top,
            under: Some(under),
            proof: whole,
        }))
    }

    /// `a / b`, where what is below may divide as well: `divdiv1` is what
    /// folds a division under a division into one.
    pub(super) fn quotient_of(
        &mut self,
        o: &mut dyn Oracle,
        left: &Term,
        right: &Term,
        labels: &FloatLabels,
        said: &Rpn,
    ) -> Checked<Route<Quotiented>> {
        let Quotiented {
            over,
            under,
            proof: first,
        } = take!(self.normalize_quotient(o, left, labels)?);
        let Quotiented {
            over: below,
            under: beneath,
            proof: second,
        } = take!(self.normalize_quotient(o, right, labels)?);
        if let Some(beneath) = beneath {
            let divisor = Quotiented {
                over: below,
                under: Some(beneath),
                proof: second,
            };
            return self.divided_by_quotient(o, left, right, divisor, labels, said);
        }
        self.divisors
            .entry(Self::spell_run(&below))
            .or_insert_with(|| right.rpn(labels));
        // A divisor written as a product or a power is not zero by its
        // factors, which is known only while it is written so: multiplied
        // out, (k + 1)² is one polynomial whose factors are gone.
        if self.written {
            if let Built(apart) = self.page_apart(o, right, labels)? {
                let whole = right.rpn(labels);
                self.keep_nonzero(o, &whole, &below, &apart, &second);
            }
        }
        let joined = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => left.rpn(labels),
            "B" => Self::spell_quotient(&over, under.as_deref()),
            "C" => right.rpn(labels), "D" => Self::spell_run(&below), "F" => DIV},
            &[&first, &second],
        );
        let Some(under) = under else {
            return Ok(Built(Quotiented {
                over,
                under: Some(below),
                proof: joined,
            }));
        };
        // ( A / B ) / C is A / ( B x. C ), and the new denominator is then
        // the two of them multiplied out.
        let top = Self::spell_run(&over);
        let bottom = Self::spell_run(&under);
        let outer = Self::spell_run(&below);
        let p1 = self.pair_of(o, &under)?;
        let p2 = self.pair_of(o, &below)?;
        let (p1, p2) = (take!(p1), take!(p2));
        let rc = self.run_cc(o, &over)?;
        let folded = {
            let b = o.b();
            let law = b.ap(
                "divdiv1",
                &binds! {"A" => &top, "B" => &bottom, "C" => &outer},
                &[],
            );
            b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(top, "cc", "wcel"),
                "ch" => t!(t!(bottom, "cc", "wcel"), t!(bottom, "cc0", "wne"), "wa"),
                "th" => t!(t!(outer, "cc", "wcel"), t!(outer, "cc0", "wne"), "wa"),
                "ta" => t!(op(&op(&top, &bottom, DIV), &outer, DIV),
                           op(&top, &op(&bottom, &outer, MUL), DIV), "wceq")},
                &[&rc, &p1, &p2, &law],
            )
        };
        let (made, product) = take!(self.multiply(o, &under, &below)?);
        self.keep_product(o, &under, &below, &made, &product)?;
        let first_link = self.chain(
            o,
            &joined,
            &folded,
            said,
            &op(&op(&top, &bottom, DIV), &outer, DIV),
            &op(&top, &op(&bottom, &outer, MUL), DIV),
        );
        let second_link = o.b().ap(
            "oveq2d",
            &binds! {"ph" => &self.under, "A" => op(&bottom, &outer, MUL),
            "B" => Self::spell_run(&made), "C" => &top, "F" => DIV},
            &[&product],
        );
        let p = self.chain(
            o,
            &first_link,
            &second_link,
            said,
            &op(&top, &op(&bottom, &outer, MUL), DIV),
            &op(&top, &Self::spell_run(&made), DIV),
        );
        Ok(Built(Quotiented {
            over,
            under: Some(made),
            proof: p,
        }))
    }

    /// `a / R`, where R divides, `P / Q` once normalised (`divisor`): a / R
    /// is a / ( P / Q ) (`oveq2d`), which is ( a x. Q ) / P (`divdiv2`), and
    /// that is normalised in turn. R is not 0 by what the page says of it as
    /// written, or of the parts it is written with (`Oracle::nonzero`); P is
    /// not 0 because R is not, across R = P / Q (`divne0bd`), and is kept so
    /// for the denominator it now is; Q is not 0 as the denominator the
    /// normal form made of R.
    pub(super) fn divided_by_quotient(
        &mut self,
        o: &mut dyn Oracle,
        left: &Term,
        right: &Term,
        divisor: Quotiented,
        labels: &FloatLabels,
        said: &Rpn,
    ) -> Checked<Route<Quotiented>> {
        let Quotiented {
            over: top,
            under: Some(bottom),
            proof: equal,
        } = divisor
        else {
            return Ok(named_decline("{} divides by no quotient", said));
        };
        let (a_s, r_s) = (left.rpn(labels), right.rpn(labels));
        let (p_s, q_s) = (Self::spell_run(&top), Self::spell_run(&bottom));
        let pq = op(&p_s, &q_s, DIV);
        // A line the step names saying R is not 0 comes first, then R's
        // parts, then any line the page writes: an uncited line saying
        // 1/x ≠ 0 is not what a step naming x ≠ 0 rests on.
        let r_apart = take!(o.nonzero(&r_s, true)?);
        let p_cc = self.run_cc(o, &top)?;
        let (q_cc, q_apart) = take!(self.denominator(o, &bottom)?);
        let p_apart = {
            let b = o.b();
            let moved = b.ap(
                "neeq1d",
                &binds! {"ph" => &self.under, "A" => &r_s, "B" => &pq, "C" => "cc0"},
                &[&equal],
            );
            let pq_apart = b.ap(
                "mpbid",
                &binds! {"ph" => &self.under, "ps" => t!(r_s, "cc0", "wne"),
                "ch" => t!(pq, "cc0", "wne")},
                &[&r_apart, &moved],
            );
            let iff = b.ap(
                "divne0bd",
                &binds! {"ph" => &self.under, "A" => &p_s, "B" => &q_s},
                &[&p_cc, &q_cc, &q_apart],
            );
            b.ap(
                "mpbird",
                &binds! {"ph" => &self.under, "ps" => t!(p_s, "cc0", "wne"),
                "ch" => t!(pq, "cc0", "wne")},
                &[&pq_apart, &iff],
            )
        };
        self.nonzero
            .entry(p_s.clone())
            .or_insert_with(|| p_apart.clone());
        let across = op(&a_s, &pq, DIV);
        let flipped = op(&op(&a_s, &q_s, MUL), &p_s, DIV);
        let atom = o.atom(&a_s)?;
        let turned = {
            let b = o.b();
            let paired = |s: &Rpn, held: &Proof, apart: &Proof| {
                b.ap(
                    "jca",
                    &binds! {"ph" => &self.under, "ps" => t!(s, "cc", "wcel"),
                    "ch" => t!(s, "cc0", "wne")},
                    &[held, apart],
                )
            };
            let (p_pair, q_pair) =
                (paired(&p_s, &p_cc, &p_apart), paired(&q_s, &q_cc, &q_apart));
            let put = b.ap(
                "oveq2d",
                &binds! {"ph" => &self.under, "A" => &r_s, "B" => &pq, "C" => &a_s, "F" => DIV},
                &[&equal],
            );
            let law = b.ap(
                "divdiv2",
                &binds! {"A" => &a_s, "B" => &p_s, "C" => &q_s},
                &[],
            );
            let folded = b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(a_s, "cc", "wcel"),
                "ch" => t!(t!(p_s, "cc", "wcel"), t!(p_s, "cc0", "wne"), "wa"),
                "th" => t!(t!(q_s, "cc", "wcel"), t!(q_s, "cc0", "wne"), "wa"),
                "ta" => t!(across, flipped, "wceq")},
                &[&atom, &p_pair, &q_pair, &law],
            );
            (put, folded)
        };
        let turned = self.chain(o, &turned.0, &turned.1, said, &across, &flipped);
        let sigs = &o.b().sigs;
        let rebuilt = Term::apply(
            "co",
            vec![
                Term::apply(
                    "co",
                    vec![left.clone(), term_of(&q_s, sigs), Term::apply(MUL, vec![])],
                ),
                term_of(&p_s, sigs),
                Term::apply(DIV, vec![]),
            ],
        );
        let Quotiented { over, under, proof } =
            take!(self.normalize_quotient(o, &rebuilt, labels)?);
        let p = self.chain(
            o,
            &turned,
            &proof,
            said,
            &flipped,
            &Self::spell_quotient(&over, under.as_deref()),
        );
        Ok(Built(Quotiented {
            over,
            under,
            proof: p,
        }))
    }

    /// ( under -> term =/= 0 ) for a divisor written as a product, a
    /// negation or a power, from what the page writes of the whole or of
    /// its parts, without the search (`Oracle::nonzero`); a decline where
    /// nothing does, and for any other divisor, which `denominator` asks of
    /// the oracle.
    pub(super) fn page_apart(
        &mut self,
        o: &mut dyn Oracle,
        term: &Term,
        labels: &FloatLabels,
    ) -> Checked<Route<Proof>> {
        let compound = term.variable().is_none()
            && (term.label() == Some("cneg")
                || term.label() == Some("co")
                    && term.children().len() == 3
                    && term.children()[2]
                        .rpn(labels)
                        .alone()
                        .is_some_and(|how| [MUL, EXP].contains(&how)));
        if !compound {
            return Ok(Route::no("the divisor is no product, negation or power"));
        }
        o.nonzero(&term.rpn(labels), false)
    }

    /// ( under -> ( d e. CC /\ d =/= 0 ) ), which every law wants.
    pub fn pair_of(
        &mut self,
        o: &mut dyn Oracle,
        under: &[(Monomial, Q)],
    ) -> Checked<Route<Proof>> {
        let said = Self::spell_run(under);
        let (held, nonzero) = take!(self.denominator(o, under)?);
        Ok(Built(o.b().ap(
            "jca",
            &binds! {"ph" => &self.under, "ps" => t!(said, "cc", "wcel"), "ch" => t!(said, "cc0", "wne")},
            &[&held, &nonzero],
        )))
    }

    /// ( under -> ( a / b ) x. ( c / d ) = the same with a whole number
    /// common to one numerator and the other denominator taken out of both ):
    /// the first numerator against the second denominator (`gdivcanx`), or,
    /// `second`, the second numerator against the first denominator
    /// (`gdivcanx2`). None where nothing above one is common.
    pub(super) fn cancelled(
        &mut self,
        o: &mut dyn Oracle,
        p: &Fractions,
        second: bool,
    ) -> Checked<Option<(Fractions, Proof)>> {
        let (top, bottom) = if second {
            (&p.below, &p.under)
        } else {
            (&p.over, &p.beneath)
        };
        let (Some(t), Some(bt)) = (content(top), constant(bottom)) else {
            return Ok(None);
        };
        let g = t.gcd(&bt);
        if g <= BigInt::one() {
            return Ok(None);
        }
        let g_run: Run = vec![(Vec::new(), Q::from_integer(g.clone()))];
        let (top_left, bottom_left) = (divided(top, &g), divided(bottom, &g));
        // Each part is G times what is left of it, in canonical form.
        let Built((made_top, top_is)) = self.multiply(o, &g_run, &top_left)? else {
            return Ok(None);
        };
        let Built((made_bottom, bottom_is)) = self.multiply(o, &g_run, &bottom_left)?
        else {
            return Ok(None);
        };
        let (st, sb) = (Self::spell_run(top), Self::spell_run(bottom));
        if Self::spell_run(&made_top) != st || Self::spell_run(&made_bottom) != sb {
            return Ok(None);
        }
        let gs = Self::spell_run(&g_run);
        let (tl, bl) = (Self::spell_run(&top_left), Self::spell_run(&bottom_left));
        let (gt, gb) = (op(&gs, &tl, MUL), op(&gs, &bl, MUL));
        let (a, b) = (Self::spell_run(&p.over), Self::spell_run(&p.under));
        let (c, d) = (Self::spell_run(&p.below), Self::spell_run(&p.beneath));
        let mut next = p.clone();
        if second {
            next.below = top_left.clone();
            next.under = bottom_left.clone();
        } else {
            next.over = top_left.clone();
            next.beneath = bottom_left.clone();
        }
        let ac = self.run_cc(o, &p.over)?;
        let cc = self.run_cc(o, &p.below)?;
        let tc = self.run_cc(o, &top_left)?;
        let Built(left_pair) = self.pair_of(o, &bottom_left)? else {
            return Ok(None);
        };
        let Built(g_pair) = self.pair_of(o, &g_run)? else {
            return Ok(None);
        };
        let other = if second { &p.beneath } else { &p.under };
        let Built(other_pair) = self.pair_of(o, other)? else {
            return Ok(None);
        };
        let under = self.under.clone();
        let bb = o.b();
        let parts = |pair: &Proof, x: &Rpn| {
            let both = t!(x, "cc", "wcel");
            let apart = t!(x, "cc0", "wne");
            (
                bb.ap(
                    "simpld",
                    &binds! {"ph" => &under, "ps" => &both, "ch" => &apart},
                    &[pair],
                ),
                bb.ap(
                    "simprd",
                    &binds! {"ph" => &under, "ps" => &both, "ch" => &apart},
                    &[pair],
                ),
            )
        };
        let (left_cc, left_apart) = parts(&left_pair, &bl);
        let (g_cc, g_apart) = parts(&g_pair, &gs);
        let top_back = bb.ap(
            "eqcomd",
            &binds! {"ph" => &under, "A" => &gt, "B" => &st},
            &[&top_is],
        );
        let bottom_back = bb.ap(
            "eqcomd",
            &binds! {"ph" => &under, "A" => &gb, "B" => &sb},
            &[&bottom_is],
        );
        let (written, made) = if second {
            // ( a / b ) x. ( c / d ) = ( a / ( G x. B ) ) x. ( ( G x. C ) / d )
            let (other_cc, other_apart) = parts(&other_pair, &d);
            let first = bb.ap(
                "oveq2d",
                &binds! {"ph" => &under, "A" => &b, "B" => &gb, "C" => &a, "F" => DIV},
                &[&bottom_back],
            );
            let then = bb.ap(
                "oveq1d",
                &binds! {"ph" => &under, "A" => &c, "B" => &gt, "C" => &d, "F" => DIV},
                &[&top_back],
            );
            let written = op(&op(&a, &gb, DIV), &op(&gt, &d, DIV), MUL);
            let rewritten = bb.ap(
                "oveq12d",
                &binds! {"ph" => &under, "A" => op(&a, &b, DIV), "B" => op(&a, &gb, DIV),
                "C" => op(&c, &d, DIV), "D" => op(&gt, &d, DIV), "F" => MUL},
                &[&first, &then],
            );
            let law = bb.ap(
                "gdivcanx2",
                &binds! {"ph" => &under, "A" => &a, "B" => &bl, "C" => &tl, "D" => &d, "G" => &gs},
                &[&ac, &left_cc, &left_apart, &tc, &other_cc, &other_apart, &g_cc, &g_apart],
            );
            (written, (rewritten, law))
        } else {
            // ( a / b ) x. ( c / d ) = ( ( G x. A ) / b ) x. ( c / ( G x. D ) )
            let (other_cc, other_apart) = parts(&other_pair, &b);
            let first = bb.ap(
                "oveq1d",
                &binds! {"ph" => &under, "A" => &a, "B" => &gt, "C" => &b, "F" => DIV},
                &[&top_back],
            );
            let then = bb.ap(
                "oveq2d",
                &binds! {"ph" => &under, "A" => &d, "B" => &gb, "C" => &c, "F" => DIV},
                &[&bottom_back],
            );
            let written = op(&op(&gt, &b, DIV), &op(&c, &gb, DIV), MUL);
            let rewritten = bb.ap(
                "oveq12d",
                &binds! {"ph" => &under, "A" => op(&a, &b, DIV), "B" => op(&gt, &b, DIV),
                "C" => op(&c, &d, DIV), "D" => op(&c, &gb, DIV), "F" => MUL},
                &[&first, &then],
            );
            let law = bb.ap(
                "gdivcanx",
                &binds! {"ph" => &under, "A" => &tl, "B" => &b, "C" => &c, "D" => &bl, "G" => &gs},
                &[&tc, &other_cc, &other_apart, &cc, &left_cc, &left_apart, &g_cc, &g_apart],
            );
            (written, (rewritten, law))
        };
        let (rewritten, law) = made;
        let proof =
            self.chain(o, &rewritten, &law, &p.spelt(), &written, &next.spelt());
        Ok(Some((next, proof)))
    }

    /// `a + b`, `a - b` or `a x. b` where one of them divides: `divadddiv`,
    /// `divsubdiv` and `divmuldiv` say what the pair becomes, and the
    /// numerator and denominator they land on are then multiplied out.
    pub(super) fn quotient_joined(
        &mut self,
        o: &mut dyn Oracle,
        how: Op,
        left: &Term,
        right: &Term,
        labels: &FloatLabels,
        said: &Rpn,
    ) -> Checked<Route<Quotiented>> {
        let written_op = if how == Op::Add {
            ADD
        } else if how == Op::Sub {
            SUB
        } else {
            MUL
        };
        let mut quotients = Vec::new();
        for side in [left, right] {
            let Quotiented { over, under, proof } =
                take!(self.normalize_quotient(o, side, labels)?);
            quotients.push(self.as_quotient(
                o,
                over,
                under,
                proof,
                &side.rpn(labels),
            )?);
        }
        let (below, beneath, second) = quotients.pop().unwrap();
        let (over, under, first) = quotients.pop().unwrap();
        let (a, b) = (Self::spell_run(&over), Self::spell_run(&under));
        let (c, d) = (Self::spell_run(&below), Self::spell_run(&beneath));
        let joined = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => left.rpn(labels), "B" => op(&a, &b, DIV),
            "C" => right.rpn(labels), "D" => op(&c, &d, DIV), "F" => written_op},
            &[&first, &second],
        );
        // A whole number common to one numerator and the other denominator
        // is cancelled before anything is multiplied out, as on paper:
        // 2·365^23 times a fraction over 2·365^23 would otherwise be worked
        // out as a product of 119 digits, which the comparison after it
        // divides away again.
        let (mut over, mut under, mut below, mut beneath) =
            (over, under, below, beneath);
        let (mut a, mut b, mut c, mut d) = (a, b, c, d);
        let mut joined = joined;
        if how == Op::Mul {
            for second in [false, true] {
                let now = Fractions {
                    over: over.clone(),
                    under: under.clone(),
                    below: below.clone(),
                    beneath: beneath.clone(),
                };
                let Some((next, proof)) = self.cancelled(o, &now, second)? else {
                    continue;
                };
                joined =
                    self.chain(o, &joined, &proof, said, &now.spelt(), &next.spelt());
                Fractions {
                    over,
                    under,
                    below,
                    beneath,
                } = next;
                (a, b) = (Self::spell_run(&over), Self::spell_run(&under));
                (c, d) = (Self::spell_run(&below), Self::spell_run(&beneath));
            }
        }
        let (label, top, made, numerator);
        if how == Op::Sub {
            // The numerator a difference lands on is two products, the
            // second taken from the first, which `subtracted` does to runs.
            label = "divsubdiv";
            top = op(&op(&a, &d, MUL), &op(&c, &b, MUL), SUB);
            let (first_items, one) = take!(self.multiply(o, &over, &beneath)?);
            let (second_items, two) = take!(self.multiply(o, &below, &under)?);
            let (m, p) = take!(self.subtracted(
                o,
                &op(&a, &d, MUL),
                &op(&c, &b, MUL),
                &first_items,
                one,
                &second_items,
                two,
                &top
            )?);
            made = m;
            numerator = p;
        } else if how == Op::Add {
            // The numerator a sum lands on is two products added, so each is
            // multiplied out and then the two of them joined.
            label = "divadddiv";
            top = op(&op(&a, &d, MUL), &op(&c, &b, MUL), ADD);
            let (first_items, one) = take!(self.multiply(o, &over, &beneath)?);
            let (second_items, two) = take!(self.multiply(o, &below, &under)?);
            let (m, together) = take!(self.add(o, &first_items, &second_items)?);
            let middle = op(
                &Self::spell_run(&first_items),
                &Self::spell_run(&second_items),
                ADD,
            );
            let lifted = o.b().ap(
                "oveq12d",
                &binds! {"ph" => &self.under, "A" => op(&a, &d, MUL),
                "B" => Self::spell_run(&first_items), "C" => op(&c, &b, MUL),
                "D" => Self::spell_run(&second_items), "F" => ADD},
                &[&one, &two],
            );
            numerator =
                self.chain(o, &lifted, &together, &top, &middle, &Self::spell_run(&m));
            made = m;
        } else {
            label = "divmuldiv";
            top = op(&a, &c, MUL);
            let (m, p) = take!(self.multiply(o, &over, &below)?);
            made = m;
            numerator = p;
        }
        let bottom = op(&b, &d, MUL);
        let p1 = self.pair_of(o, &under)?;
        let p2 = self.pair_of(o, &beneath)?;
        let (p1, p2) = (take!(p1), take!(p2));
        let multiplied = take!(self.multiply(o, &under, &beneath)?);
        let rc1 = self.run_cc(o, &over)?;
        let rc2 = self.run_cc(o, &below)?;
        let spread = {
            let bb = o.b();
            let tops = bb.ap(
                "jca",
                &binds! {"ph" => &self.under, "ps" => t!(a, "cc", "wcel"), "ch" => t!(c, "cc", "wcel")},
                &[&rc1, &rc2],
            );
            let bottoms = bb.ap(
                "jca",
                &binds! {"ph" => &self.under,
                "ps" => t!(t!(b, "cc", "wcel"), t!(b, "cc0", "wne"), "wa"),
                "ch" => t!(t!(d, "cc", "wcel"), t!(d, "cc0", "wne"), "wa")},
                &[&p1, &p2],
            );
            let law = bb.ap(
                label,
                &binds! {"A" => &a, "B" => &c, "C" => &b, "D" => &d},
                &[],
            );
            bb.ap(
                "syl2anc",
                &binds! {"ph" => &self.under,
                "ps" => t!(t!(a, "cc", "wcel"), t!(c, "cc", "wcel"), "wa"),
                "ch" => t!(t!(t!(b, "cc", "wcel"), t!(b, "cc0", "wne"), "wa"),
                           t!(t!(d, "cc", "wcel"), t!(d, "cc0", "wne"), "wa"), "wa"),
                "th" => t!(op(&op(&a, &b, DIV), &op(&c, &d, DIV), written_op), op(&top, &bottom, DIV), "wceq")},
                &[&tops, &bottoms, &law],
            )
        };
        let (low, denominator) = multiplied;
        self.keep_product(o, &under, &beneath, &low, &denominator)?;
        let first_link = self.chain(
            o,
            &joined,
            &spread,
            said,
            &op(&op(&a, &b, DIV), &op(&c, &d, DIV), written_op),
            &op(&top, &bottom, DIV),
        );
        let second_link = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => &top, "B" => Self::spell_run(&made),
            "C" => &bottom, "D" => Self::spell_run(&low), "F" => DIV},
            &[&numerator, &denominator],
        );
        let p = self.chain(
            o,
            &first_link,
            &second_link,
            said,
            &op(&top, &bottom, DIV),
            &op(&Self::spell_run(&made), &Self::spell_run(&low), DIV),
        );
        Ok(Built(Quotiented {
            over: made,
            under: Some(low),
            proof: p,
        }))
    }

    /// `( a / b ) ^ k`, which `expdiv` takes apart.
    pub(super) fn quotient_raised(
        &mut self,
        o: &mut dyn Oracle,
        left: &Term,
        right: &Term,
        labels: &FloatLabels,
        said: &Rpn,
    ) -> Checked<Route<Quotiented>> {
        let field::Power::Expanded { by: times, .. } =
            field::power_of(left, right, labels)
        else {
            return Ok(named_decline("{} is not a power multiplied out", said));
        };
        let Quotiented {
            over: o1,
            under: u1,
            proof: p1,
        } = take!(self.normalize_quotient(o, left, labels)?);
        let (over, under, first) =
            self.as_quotient(o, o1, u1, p1, &left.rpn(labels))?;
        let (a, b) = (Self::spell_run(&over), Self::spell_run(&under));
        let pair = take!(self.pair_of(o, &under)?);
        let joined = o.b().ap(
            "oveq1d",
            &binds! {"ph" => &self.under, "A" => left.rpn(labels), "B" => op(&a, &b, DIV),
            "C" => n(times), "F" => EXP},
            &[&first],
        );
        let rc = self.run_cc(o, &over)?;
        let ix = self.index(o, times as i64);
        let split = op(&op(&a, &n(times), EXP), &op(&b, &n(times), EXP), DIV);
        let spread = {
            let bb = o.b();
            let law = bb.ap(
                "expdiv",
                &binds! {"A" => &a, "B" => &b, "N" => n(times)},
                &[],
            );
            bb.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(a, "cc", "wcel"),
                "ch" => t!(t!(b, "cc", "wcel"), t!(b, "cc0", "wne"), "wa"),
                "th" => t!(&n(times), "cn0", "wcel"),
                "ta" => t!(op(&op(&a, &b, DIV), &n(times), EXP), split, "wceq")},
                &[&rc, &pair, &ix, &law],
            )
        };
        let (made, numerator) = take!(self.power(o, &over, times)?);
        let (low, denominator) = take!(self.power(o, &under, times)?);
        let first_link = self.chain(
            o,
            &joined,
            &spread,
            said,
            &op(&op(&a, &b, DIV), &n(times), EXP),
            &split,
        );
        let second_link = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => op(&a, &n(times), EXP), "B" => Self::spell_run(&made),
            "C" => op(&b, &n(times), EXP), "D" => Self::spell_run(&low), "F" => DIV},
            &[&numerator, &denominator],
        );
        let p = self.chain(
            o,
            &first_link,
            &second_link,
            said,
            &split,
            &op(&Self::spell_run(&made), &Self::spell_run(&low), DIV),
        );
        Ok(Built(Quotiented {
            over: made,
            under: Some(low),
            proof: p,
        }))
    }
}
