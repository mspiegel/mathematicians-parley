//! Factors, products and powers.

use super::*;

impl Emitter {
    pub(super) fn factor_cc(
        &mut self,
        o: &mut dyn Oracle,
        name: &Rpn,
        power: u32,
    ) -> Checked<Proof> {
        let key = Made::FactorCc(name.clone(), power);
        if let Some(p) = self.made.get(&key) {
            return Ok(p.clone());
        }
        let atom = o.atom(name)?;
        let index = self.index(o, power as i64);
        let made = o.b().ap(
            "expcld",
            &binds! {"ph" => &self.under, "A" => name, "N" => n(power)},
            &[&atom, &index],
        );
        self.made.insert(key, made.clone());
        Ok(made)
    }

    pub(super) fn factors_cc(
        &mut self,
        o: &mut dyn Oracle,
        factors: &[(Rpn, u32)],
    ) -> Checked<Proof> {
        if factors.is_empty() {
            return Ok(self.number(o, &big(1)));
        }
        let mut out = self.factor_cc(o, &factors[0].0, factors[0].1)?;
        let mut running = spell_factor(&factors[0]);
        for one in &factors[1..] {
            let f = self.factor_cc(o, &one.0, one.1)?;
            out = o.b().ap(
                "mulcld",
                &binds! {"ph" => &self.under, "A" => &running, "B" => spell_factor(one)},
                &[&out, &f],
            );
            running = op(&running, &spell_factor(one), MUL);
        }
        Ok(out)
    }

    /// `mul32` for `add32`, and `mulcom` where the two are the whole.
    pub(super) fn swap_factors(
        &mut self,
        o: &mut dyn Oracle,
        factors: &[(Rpn, u32)],
        at: usize,
    ) -> Checked<Proof> {
        let head = &factors[..at];
        let a = spell_factor(&factors[at]);
        let b = spell_factor(&factors[at + 1]);
        let (before, after, step);
        if !head.is_empty() {
            let prefix = spell_monomial(&head.to_vec());
            before = op(&op(&prefix, &a, MUL), &b, MUL);
            after = op(&op(&prefix, &b, MUL), &a, MUL);
            let p0 = self.factors_cc(o, head)?;
            let p1 = self.factor_cc(o, &factors[at].0, factors[at].1)?;
            let p2 = self.factor_cc(o, &factors[at + 1].0, factors[at + 1].1)?;
            let bb = o.b();
            let law =
                bb.ap("mul32", &binds! {"A" => &prefix, "B" => &a, "C" => &b}, &[]);
            step = bb.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(prefix, "cc", "wcel"),
                "ch" => t!(a, "cc", "wcel"), "th" => t!(b, "cc", "wcel"),
                "ta" => t!(before, after, "wceq")},
                &[&p0, &p1, &p2, &law],
            );
        } else {
            before = op(&a, &b, MUL);
            after = op(&b, &a, MUL);
            let p1 = self.factor_cc(o, &factors[at].0, factors[at].1)?;
            let p2 = self.factor_cc(o, &factors[at + 1].0, factors[at + 1].1)?;
            let bb = o.b();
            let law = bb.ap("mulcom", &binds! {"A" => &a, "B" => &b}, &[]);
            step = bb.ap(
                "syl2anc",
                &binds! {"ph" => &self.under, "ps" => t!(a, "cc", "wcel"),
                "ch" => t!(b, "cc", "wcel"), "th" => t!(before, after, "wceq")},
                &[&p1, &p2, &law],
            );
        }
        let tail: Vec<Rpn> = factors[at + 2..].iter().map(spell_factor).collect();
        Ok(self.lift(o, step, &before, &after, &tail, MUL))
    }

    pub(super) fn shift_factors(
        &mut self,
        o: &mut dyn Oracle,
        factors: &[(Rpn, u32)],
        frm: usize,
        to: usize,
    ) -> Checked<(Monomial, Proof)> {
        let start = spell_monomial(&factors.to_vec());
        let mut said = start.clone();
        let mut factors = factors.to_vec();
        let mut proof: Option<Proof> = None;
        for at in (to..frm).rev() {
            let step = self.swap_factors(o, &factors, at)?;
            factors.swap(at, at + 1);
            let after = spell_monomial(&factors);
            proof = Some(match proof {
                None => step,
                Some(p) => self.chain(o, &p, &step, &start, &said, &after),
            });
            said = after;
        }
        let proof = match proof {
            Some(p) => p,
            None => self.same(o, &start),
        };
        Ok((factors, proof))
    }

    /// ( under -> ( ( x ^ j ) x. ( x ^ k ) ) = ( x ^ ( j + k ) ) ): `expadd`
    /// read backwards, which is where two powers of one atom meet, and the
    /// only place the exponents are added.
    pub(super) fn gather_factors(
        &mut self,
        o: &mut dyn Oracle,
        name: &Rpn,
        first: u32,
        second: u32,
    ) -> Checked<Route<Proof>> {
        let a = op(name, &n(first), EXP);
        let b = op(name, &n(second), EXP);
        let total = first + second;
        let exponent = op(&n(first), &n(second), ADD);
        let atom = o.atom(name)?;
        let i1 = self.index(o, first as i64);
        let i2 = self.index(o, second as i64);
        let joined = {
            let bb = o.b();
            let law = bb.ap(
                "expadd",
                &binds! {"A" => name, "M" => n(first), "N" => n(second)},
                &[],
            );
            let inner = bb.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(name, "cc", "wcel"),
                "ch" => t!(&n(first), "cn0", "wcel"), "th" => t!(&n(second), "cn0", "wcel"),
                "ta" => t!(op(name, &exponent, EXP), op(&a, &b, MUL), "wceq")},
                &[&atom, &i1, &i2, &law],
            );
            bb.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => op(name, &exponent, EXP), "B" => op(&a, &b, MUL)},
                &[&inner],
            )
        };
        let exponents =
            match self.coefficient_sum(o, &q(first as i64), &q(second as i64)) {
                Built(p) => p,
                Declined(d) => return Ok(Declined(d)),
            };
        let moved = o.b().ap(
            "oveq2d",
            &binds! {"ph" => &self.under, "A" => &exponent, "B" => n(total),
            "C" => name, "F" => EXP},
            &[&exponents],
        );
        Ok(Built(self.chain(
            o,
            &joined,
            &moved,
            &op(&a, &b, MUL),
            &op(name, &exponent, EXP),
            &op(name, &n(total), EXP),
        )))
    }

    /// One factor put where its atom's name says it goes.
    pub(super) fn insert_factor(
        &mut self,
        o: &mut dyn Oracle,
        factors: &[(Rpn, u32)],
        name: &Rpn,
        power: u32,
    ) -> Checked<Route<(Monomial, Proof)>> {
        let one = op(name, &n(power), EXP);
        if factors.is_empty() {
            let f = self.factor_cc(o, name, power)?;
            let b = o.b();
            let law = b.ap("mullid", &binds! {"A" => &one}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(one, "cc", "wcel"),
                "ch" => t!(op(&n(1), &one, MUL), one, "wceq")},
                &[&f, &law],
            );
            return Ok(Built((vec![(name.clone(), power)], p)));
        }
        let mut appended = factors.to_vec();
        appended.push((name.clone(), power));
        let start = spell_monomial(&appended);
        if let Some(at) = factors.iter().position(|(m, _)| m == name) {
            let (moved, walked) =
                self.shift_factors(o, &appended, factors.len(), at + 1)?;
            let total = moved[at].1 + moved[at + 1].1;
            let mut out = moved[..at].to_vec();
            out.push((name.clone(), total));
            out.extend(moved[at + 2..].iter().cloned());
            let gathered =
                take!(self.gather_factors(o, name, moved[at].1, moved[at + 1].1)?);
            let spread = self.spread(o, &moved, at, gathered)?;
            let p = self.chain(
                o,
                &walked,
                &spread,
                &start,
                &spell_monomial(&moved),
                &spell_monomial(&out),
            );
            return Ok(Built((out, p)));
        }
        let goes = factors.iter().filter(|(m, _)| m < name).count();
        let (out, p) = self.shift_factors(o, &appended, factors.len(), goes)?;
        Ok(Built((out, p)))
    }

    /// A rewrite of two neighbouring factors, carried to the whole.
    pub(super) fn spread(
        &mut self,
        o: &mut dyn Oracle,
        factors: &[(Rpn, u32)],
        at: usize,
        collect: Proof,
    ) -> Checked<Proof> {
        let head = &factors[..at];
        let rest = &factors[at + 2..];
        let a = spell_factor(&factors[at]);
        let b = spell_factor(&factors[at + 1]);
        let total =
            spell_factor(&(factors[at].0.clone(), factors[at].1 + factors[at + 1].1));
        let tail: Vec<Rpn> = rest.iter().map(spell_factor).collect();
        if head.is_empty() {
            return Ok(self.lift(o, collect, &op(&a, &b, MUL), &total, &tail, MUL));
        }
        let prefix = spell_monomial(&head.to_vec());
        let p0 = self.factors_cc(o, head)?;
        let p1 = self.factor_cc(o, &factors[at].0, factors[at].1)?;
        let p2 = self.factor_cc(o, &factors[at + 1].0, factors[at + 1].1)?;
        let outer = op(&op(&prefix, &a, MUL), &b, MUL);
        let inner_pair = op(&prefix, &op(&a, &b, MUL), MUL);
        let exposed = {
            let bb = o.b();
            let law = bb.ap(
                "mulass",
                &binds! {"A" => &prefix, "B" => &a, "C" => &b},
                &[],
            );
            bb.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(prefix, "cc", "wcel"),
                "ch" => t!(a, "cc", "wcel"), "th" => t!(b, "cc", "wcel"),
                "ta" => t!(outer, inner_pair, "wceq")},
                &[&p0, &p1, &p2, &law],
            )
        };
        let moved = o.b().ap(
            "oveq2d",
            &binds! {"ph" => &self.under, "A" => op(&a, &b, MUL), "B" => &total,
            "C" => &prefix, "F" => MUL},
            &[&collect],
        );
        let step = self.chain(
            o,
            &exposed,
            &moved,
            &outer,
            &inner_pair,
            &op(&prefix, &total, MUL),
        );
        Ok(self.lift(o, step, &outer, &op(&prefix, &total, MUL), &tail, MUL))
    }

    /// ( under -> ( M x. N ) = P ), two monomials merged.
    pub(super) fn multiply_monomials(
        &mut self,
        o: &mut dyn Oracle,
        left: &[(Rpn, u32)],
        right: &[(Rpn, u32)],
    ) -> Checked<Route<(Monomial, Proof)>> {
        let start = op(
            &spell_monomial(&left.to_vec()),
            &spell_monomial(&right.to_vec()),
            MUL,
        );
        if right.is_empty() {
            let keep = spell_monomial(&left.to_vec());
            let fc = self.factors_cc(o, left)?;
            let b = o.b();
            let law = b.ap("mulrid", &binds! {"A" => &keep}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(keep, "cc", "wcel"),
                "ch" => t!(op(&keep, &n(1), MUL), keep, "wceq")},
                &[&fc, &law],
            );
            return Ok(Built((left.to_vec(), p)));
        }
        if right.len() == 1 {
            return self.insert_factor(o, left, &right[0].0, right[0].1);
        }
        let (rest, last) = (&right[..right.len() - 1], &right[right.len() - 1]);
        let whole_m = spell_monomial(&right.to_vec());
        let prefix = spell_monomial(&rest.to_vec());
        let held = spell_monomial(&left.to_vec());
        let one = spell_factor(last);
        let p0 = self.factors_cc(o, left)?;
        let p1 = self.factors_cc(o, rest)?;
        let p2 = self.factor_cc(o, &last.0, last.1)?;
        let grouped = op(&op(&held, &prefix, MUL), &one, MUL);
        let peeled = {
            let b = o.b();
            let law = b.ap(
                "mulass",
                &binds! {"A" => &held, "B" => &prefix, "C" => &one},
                &[],
            );
            let inner = b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(held, "cc", "wcel"),
                "ch" => t!(prefix, "cc", "wcel"), "th" => t!(one, "cc", "wcel"),
                "ta" => t!(grouped, op(&held, &whole_m, MUL), "wceq")},
                &[&p0, &p1, &p2, &law],
            );
            b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => &grouped, "B" => op(&held, &whole_m, MUL)},
                &[&inner],
            )
        };
        let (merged, inner) = take!(self.multiply_monomials(o, left, rest)?);
        let carried = o.b().ap(
            "oveq1d",
            &binds! {"ph" => &self.under, "A" => op(&held, &prefix, MUL),
            "B" => spell_monomial(&merged), "C" => &one, "F" => MUL},
            &[&inner],
        );
        let (out, placed) = take!(self.insert_factor(o, &merged, &last.0, last.1)?);
        let middle = op(&spell_monomial(&merged), &one, MUL);
        let first = self.chain(o, &peeled, &carried, &start, &grouped, &middle);
        let p = self.chain(o, &first, &placed, &start, &middle, &spell_monomial(&out));
        Ok(Built((out, p)))
    }

    // --- multiplying ----------------------------------------------------

    /// ( under -> ( a x. b ) = c ) for two whole numbers, worked digit by
    /// digit (`numerals::product`).
    pub(super) fn positive_product(
        &mut self,
        o: &dyn Oracle,
        first: &BigInt,
        second: &BigInt,
    ) -> Proof {
        let (a, b) = (spelt(first), spelt(second));
        let claim = t!(op(&a, &b, MUL), spelt(&(first * second)), "wceq");
        let held = numerals::product(
            o.b(),
            first.magnitude().clone(),
            second.magnitude().clone(),
        );
        self.a1i(o, &claim, &held)
    }

    /// ( under -> ( c x. d ) = e ), the coefficients as `spell` has them.
    ///
    /// Signs come off first — `mulneg1`, `mulneg2` and `mul2neg` say where
    /// the minus goes — and what is left is two whole numbers, which
    /// `positive_product` multiplies.
    pub(super) fn coefficient_product(
        &mut self,
        o: &dyn Oracle,
        first: &Q,
        second: &Q,
    ) -> Route<Proof> {
        let total = first * second;
        let said = spell_coefficient(&total);
        let c = spell_coefficient(first);
        let d = spell_coefficient(second);
        let (Some(said), Some(c), Some(d)) = (said, c, d) else {
            return Route::no(format!(
                "{} x. {} is not a product of whole numbers",
                show(first),
                show(second)
            ));
        };
        let (a, b) = (whole(first), whole(second));
        if !a.is_negative() && !b.is_negative() {
            return Built(self.positive_product(o, &a, &b));
        }
        let (size_a, size_b) = (a.abs(), b.abs());
        let size = self.positive_product(o, &size_a, &size_b);
        let whole_p = op(&spelt(&a), &spelt(&b), MUL);
        if a.is_negative() && b.is_negative() {
            let paired =
                self.pair(o, "mul2neg", &size_a, &size_b, &op(&c, &d, MUL), &whole_p);
            return Built(self.chain(
                o,
                &paired,
                &size,
                &op(&c, &d, MUL),
                &whole_p,
                &said,
            ));
        }
        let label = if a.is_negative() {
            "mulneg1"
        } else {
            "mulneg2"
        };
        let paired = self.pair(
            o,
            label,
            &size_a,
            &size_b,
            &op(&c, &d, MUL),
            &t!(whole_p, "cneg"),
        );
        let negated = o.b().ap(
            "negeqd",
            &binds! {"ph" => &self.under, "A" => &whole_p, "B" => spelt(&(&a * &b))},
            &[&size],
        );
        Built(self.chain(
            o,
            &paired,
            &negated,
            &op(&c, &d, MUL),
            &t!(whole_p, "cneg"),
            &said,
        ))
    }

    /// A two-argument law of ℂ, applied to two whole numbers.
    pub(super) fn pair(
        &mut self,
        o: &dyn Oracle,
        label: &str,
        first: &BigInt,
        second: &BigInt,
        before: &Rpn,
        after: &Rpn,
    ) -> Proof {
        let (left, right) = (spelt(first), spelt(second));
        let (left, right) = (&left, &right);
        let pl = self.number(o, first);
        let pr = self.number(o, second);
        let b = o.b();
        let law = b.ap(label, &binds! {"A" => left, "B" => right}, &[]);
        b.ap(
            "syl2anc",
            &binds! {"ph" => &self.under, "ps" => t!(left, "cc", "wcel"),
            "ch" => t!(right, "cc", "wcel"), "th" => t!(before, after, "wceq")},
            &[&pl, &pr, &law],
        )
    }

    /// ( under -> ( ( c x. M ) x. ( d x. N ) ) = ( e x. P ) ): `mul4` puts
    /// the two coefficients together and the two monomials together, and
    /// then each side is its own problem.
    pub(super) fn term_times_term(
        &mut self,
        o: &mut dyn Oracle,
        one: &(Monomial, Q),
        two: &(Monomial, Q),
    ) -> Checked<Route<((Monomial, Q), Proof)>> {
        let ((first, weight), (second, other)) = (one, two);
        let c = coeff(weight);
        let d = coeff(other);
        let (m, nn) = (spell_monomial(first), spell_monomial(second));
        let (a, b) = (Self::spell_term(one), Self::spell_term(two));
        let pc = self.coefficient(o, weight);
        let pm = self.monomial_cc(o, first)?;
        let pd = self.coefficient(o, other);
        let pn = self.monomial_cc(o, second)?;
        let regrouped = {
            let bb = o.b();
            let left_pair = bb.ap(
                "jca",
                &binds! {"ph" => &self.under, "ps" => t!(c, "cc", "wcel"), "ch" => t!(m, "cc", "wcel")},
                &[&pc, &pm],
            );
            let right_pair = bb.ap(
                "jca",
                &binds! {"ph" => &self.under, "ps" => t!(d, "cc", "wcel"), "ch" => t!(nn, "cc", "wcel")},
                &[&pd, &pn],
            );
            let both = bb.ap(
                "jca",
                &binds! {"ph" => &self.under,
                "ps" => t!(t!(c, "cc", "wcel"), t!(m, "cc", "wcel"), "wa"),
                "ch" => t!(t!(d, "cc", "wcel"), t!(nn, "cc", "wcel"), "wa")},
                &[&left_pair, &right_pair],
            );
            let law = bb.ap(
                "mul4",
                &binds! {"A" => &c, "B" => &m, "C" => &d, "D" => &nn},
                &[],
            );
            bb.ap(
                "syl",
                &binds! {"ph" => &self.under,
                "ps" => t!(t!(t!(c, "cc", "wcel"), t!(m, "cc", "wcel"), "wa"),
                           t!(t!(d, "cc", "wcel"), t!(nn, "cc", "wcel"), "wa"), "wa"),
                "ch" => t!(op(&a, &b, MUL), op(&op(&c, &d, MUL), &op(&m, &nn, MUL), MUL), "wceq")},
                &[&both, &law],
            )
        };
        let fl: Monomial = first.clone();
        let sl: Monomial = second.clone();
        let (merged, monomial) = take!(self.multiply_monomials(o, &fl, &sl)?);
        let total = weight * other;
        let out = (merged.clone(), total.clone());
        let times = match self.coefficient_product(o, weight, other) {
            Built(p) => p,
            Declined(d) => return Ok(Declined(d)),
        };
        let lifted = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => op(&c, &d, MUL), "B" => coeff(&total),
            "C" => op(&m, &nn, MUL), "D" => spell_monomial(&merged), "F" => MUL},
            &[&times, &monomial],
        );
        let p = self.chain(
            o,
            &regrouped,
            &lifted,
            &op(&a, &b, MUL),
            &op(&op(&c, &d, MUL), &op(&m, &nn, MUL), MUL),
            &Self::spell_term(&out),
        );
        Ok(Built((out, p)))
    }

    /// ( under -> ( t x. spell_run(right) ) = spell_run(product) ): `adddi`
    /// takes the right-hand run apart from its end, one term at a time, and
    /// each product of two terms is `term_times_term`.
    pub(super) fn term_times_run(
        &mut self,
        o: &mut dyn Oracle,
        one: &(Monomial, Q),
        right: &[(Monomial, Q)],
    ) -> Checked<Route<(Run, Proof)>> {
        let term = Self::spell_term(one);
        let start = op(&term, &Self::spell_run(right), MUL);
        if right.is_empty() {
            let cc = self.term_cc(o, &one.0, &one.1)?;
            let b = o.b();
            let law = b.ap("mul01", &binds! {"A" => &term}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(term, "cc", "wcel"),
                "ch" => t!(op(&term, &n(0), MUL), &n(0), "wceq")},
                &[&cc, &law],
            );
            return Ok(Built((Vec::new(), p)));
        }
        if right.len() == 1 {
            let (out, proof) = take!(self.term_times_term(o, one, &right[0])?);
            return Ok(Built((vec![out], proof)));
        }
        let (rest, last) = (&right[..right.len() - 1], &right[right.len() - 1]);
        let prefix = Self::spell_run(rest);
        let tail = Self::spell_term(last);
        let p0 = self.term_cc(o, &one.0, &one.1)?;
        let p1 = self.run_cc(o, rest)?;
        let p2 = self.term_cc(o, &last.0, &last.1)?;
        let apart = op(&op(&term, &prefix, MUL), &op(&term, &tail, MUL), ADD);
        let spread = {
            let b = o.b();
            let law = b.ap(
                "adddi",
                &binds! {"A" => &term, "B" => &prefix, "C" => &tail},
                &[],
            );
            b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(term, "cc", "wcel"),
                "ch" => t!(prefix, "cc", "wcel"), "th" => t!(tail, "cc", "wcel"),
                "ta" => t!(start, apart, "wceq")},
                &[&p0, &p1, &p2, &law],
            )
        };
        let (inner, first) = take!(self.term_times_run(o, one, rest)?);
        let (single, second) = take!(self.term_times_term(o, one, last)?);
        let both = op(&Self::spell_run(&inner), &Self::spell_term(&single), ADD);
        let lifted = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => op(&term, &prefix, MUL),
            "B" => Self::spell_run(&inner), "C" => op(&term, &tail, MUL),
            "D" => Self::spell_term(&single), "F" => ADD},
            &[&first, &second],
        );
        let lined = self.chain(o, &spread, &lifted, &start, &apart, &both);
        let (out, placed) = take!(self.insert(o, &inner, &single.0, &single.1)?);
        let p = self.chain(o, &lined, &placed, &start, &both, &Self::spell_run(&out));
        Ok(Built((out, p)))
    }

    /// ( under -> ( spell_run(left) x. spell_run(right) ) = the product ):
    /// `adddir` takes the left-hand run apart, and what each of its terms
    /// does to the whole right-hand run is `term_times_run`. The pieces are
    /// then added, which is what `add` is for.
    pub fn multiply(
        &mut self,
        o: &mut dyn Oracle,
        left: &[(Monomial, Q)],
        right: &[(Monomial, Q)],
    ) -> Checked<Route<(Run, Proof)>> {
        let start = op(&Self::spell_run(left), &Self::spell_run(right), MUL);
        if left.is_empty() {
            let keep = Self::spell_run(right);
            let rc = self.run_cc(o, right)?;
            let b = o.b();
            let law = b.ap("mul02", &binds! {"A" => &keep}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(keep, "cc", "wcel"),
                "ch" => t!(op(&n(0), &keep, MUL), &n(0), "wceq")},
                &[&rc, &law],
            );
            return Ok(Built((Vec::new(), p)));
        }
        if left.len() == 1 {
            return self.term_times_run(o, &left[0], right);
        }
        let (rest, last) = (&left[..left.len() - 1], &left[left.len() - 1]);
        let prefix = Self::spell_run(rest);
        let tail = Self::spell_term(last);
        let whole_run = Self::spell_run(right);
        let p0 = self.run_cc(o, rest)?;
        let p1 = self.term_cc(o, &last.0, &last.1)?;
        let p2 = self.run_cc(o, right)?;
        let apart = op(
            &op(&prefix, &whole_run, MUL),
            &op(&tail, &whole_run, MUL),
            ADD,
        );
        let spread = {
            let b = o.b();
            let law = b.ap(
                "adddir",
                &binds! {"A" => &prefix, "B" => &tail, "C" => &whole_run},
                &[],
            );
            b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(prefix, "cc", "wcel"),
                "ch" => t!(tail, "cc", "wcel"), "th" => t!(whole_run, "cc", "wcel"),
                "ta" => t!(start, apart, "wceq")},
                &[&p0, &p1, &p2, &law],
            )
        };
        let (inner, first) = take!(self.multiply(o, rest, right)?);
        let (outer, second) = take!(self.term_times_run(o, last, right)?);
        let both = op(&Self::spell_run(&inner), &Self::spell_run(&outer), ADD);
        let lifted = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => op(&prefix, &whole_run, MUL),
            "B" => Self::spell_run(&inner), "C" => op(&tail, &whole_run, MUL),
            "D" => Self::spell_run(&outer), "F" => ADD},
            &[&first, &second],
        );
        let lined = self.chain(o, &spread, &lifted, &start, &apart, &both);
        let (out, joined) = take!(self.add(o, &inner, &outer)?);
        let p = self.chain(o, &lined, &joined, &start, &both, &Self::spell_run(&out));
        Ok(Built((out, p)))
    }

    /// ( under -> ( spell_run(items) ^ k ) = spell_run(the power) ).
    ///
    /// `expp1` peels one factor off, and it states the exponent as `N + 1`,
    /// so the numeral is rewritten that way round first.
    pub(super) fn power(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
        times: u32,
    ) -> Checked<Route<(Run, Proof)>> {
        let run = Self::spell_run(items);
        let start = op(&run, &n(times), EXP);
        let unit: Run = vec![(Vec::new(), q(1))];
        if times == 0 {
            let rc = self.run_cc(o, items)?;
            let first = {
                let b = o.b();
                let law = b.ap("exp0", &binds! {"A" => &run}, &[]);
                b.ap(
                    "syl",
                    &binds! {"ph" => &self.under, "ps" => t!(run, "cc", "wcel"),
                    "ch" => t!(start, &n(1), "wceq")},
                    &[&rc, &law],
                )
            };
            let one = self.one_as_term(o);
            let p =
                self.chain(o, &first, &one, &start, &n(1), &Self::spell_term(&unit[0]));
            return Ok(Built((unit, p)));
        }
        if times == 1 {
            let rc = self.run_cc(o, items)?;
            let b = o.b();
            let law = b.ap("exp1", &binds! {"A" => &run}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(run, "cc", "wcel"),
                "ch" => t!(start, run, "wceq")},
                &[&rc, &law],
            );
            return Ok(Built((items.to_vec(), p)));
        }
        let below = &n(times - 1);
        let stepped_from = match self.coefficient_sum(o, &q(times as i64 - 1), &q(1)) {
            Built(p) => p,
            Declined(d) => return Ok(Declined(d)),
        };
        let rc = self.run_cc(o, items)?;
        let ix = self.index(o, times as i64 - 1);
        let peeled_exponent = op(below, &n(1), ADD);
        let stepped = {
            let b = o.b();
            let turned = b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => &peeled_exponent, "B" => n(times)},
                &[&stepped_from],
            );
            let first = b.ap(
                "oveq2d",
                &binds! {"ph" => &self.under, "A" => n(times), "B" => &peeled_exponent,
                "C" => &run, "F" => EXP},
                &[&turned],
            );
            let law = b.ap("expp1", &binds! {"A" => &run, "N" => below}, &[]);
            let second = b.ap(
                "syl2anc",
                &binds! {"ph" => &self.under, "ps" => t!(run, "cc", "wcel"),
                "ch" => t!(below, "cn0", "wcel"),
                "th" => t!(op(&run, &peeled_exponent, EXP), op(&op(&run, below, EXP), &run, MUL), "wceq")},
                &[&rc, &ix, &law],
            );
            self.chain(
                o,
                &first,
                &second,
                &start,
                &op(&run, &peeled_exponent, EXP),
                &op(&op(&run, below, EXP), &run, MUL),
            )
        };
        let (inner, smaller) = take!(self.power(o, items, times - 1)?);
        let carried = o.b().ap(
            "oveq1d",
            &binds! {"ph" => &self.under, "A" => op(&run, below, EXP),
            "B" => Self::spell_run(&inner), "C" => &run, "F" => MUL},
            &[&smaller],
        );
        let (out, product) = take!(self.multiply(o, &inner, items)?);
        let middle = op(&Self::spell_run(&inner), &run, MUL);
        let first = self.chain(
            o,
            &stepped,
            &carried,
            &start,
            &op(&op(&run, below, EXP), &run, MUL),
            &middle,
        );
        let p =
            self.chain(o, &first, &product, &start, &middle, &Self::spell_run(&out));
        Ok(Built((out, p)))
    }

    /// ( under -> 1 = ( 1 x. 1 ) ), the canonical form of one.
    pub(super) fn one_as_term(&mut self, o: &dyn Oracle) -> Proof {
        let product = self.positive_product(o, &big(1), &big(1));
        o.b().ap(
            "eqcomd",
            &binds! {"ph" => &self.under, "A" => op(&n(1), &n(1), MUL), "B" => n(1)},
            &[&product],
        )
    }

    // --- the driver -----------------------------------------------------
}
