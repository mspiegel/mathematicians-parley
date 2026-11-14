//! Terms, runs, coefficients and gaps.

use super::*;

impl Emitter {
    pub fn new(under: &Rpn, apart: bool, written: bool) -> Emitter {
        Emitter {
            under: under.clone(),
            apart,
            written,
            held: IndexMap::new(),
            made: IndexMap::new(),
            nonzero: IndexMap::new(),
            divisors: IndexMap::new(),
        }
    }

    /// ( under -> what = what ).
    pub fn same(&self, o: &dyn Oracle, what: &Rpn) -> Proof {
        o.b()
            .ap("eqidd", &binds! {"ph" => &self.under, "A" => what}, &[])
    }

    /// ( under -> a = c ) from ( under -> a = b ) and ( under -> b = c ).
    pub fn chain(
        &self,
        o: &dyn Oracle,
        first: &Proof,
        second: &Proof,
        a: &Rpn,
        b: &Rpn,
        c: &Rpn,
    ) -> Proof {
        o.b().ap(
            "eqtrd",
            &binds! {"ph" => &self.under, "A" => a, "B" => b, "C" => c},
            &[first, second],
        )
    }

    // --- membership -----------------------------------------------------

    /// ( under -> n e. CC ) for a whole number the kernel spells.
    pub fn number(&mut self, o: &dyn Oracle, value: &BigInt) -> Proof {
        let key = Made::Number(value.clone());
        if let Some(p) = self.made.get(&key) {
            return p.clone();
        }
        let b = o.b();
        let made = b.ap(
            "a1i",
            &binds! {"ph" => t!(spelt(value), "cc", "wcel"), "ps" => &self.under},
            &[&numerals::cc(b, value.magnitude().clone())],
        );
        self.made.insert(key, made.clone());
        made
    }

    /// ( under -> k e. NN0 ), which an exponent has to be.
    pub fn index(&mut self, o: &dyn Oracle, value: i64) -> Proof {
        let key = Made::Index(value);
        if let Some(p) = self.made.get(&key) {
            return p.clone();
        }
        let b = o.b();
        let made = b.ap(
            "a1i",
            &binds! {"ph" => t!(&n(value as u32), "cn0", "wcel"), "ps" => &self.under},
            &[&numerals::nn0(b, value as u64)],
        );
        self.made.insert(key, made.clone());
        made
    }

    /// ( under -> c e. CC ) for a coefficient, negated where negative.
    pub fn coefficient(&mut self, o: &dyn Oracle, weight: &Q) -> Proof {
        let key = Made::Coefficient(weight.clone());
        if let Some(p) = self.made.get(&key) {
            return p.clone();
        }
        let numerator = weight.numer().clone();
        let magnitude = numerator.abs();
        let held = self.number(o, &magnitude);
        let made = if numerator.is_negative() {
            o.b().ap(
                "negcld",
                &binds! {"ph" => &self.under, "A" => spelt(&magnitude)},
                &[&held],
            )
        } else {
            held
        };
        self.made.insert(key, made.clone());
        made
    }

    /// ( under -> M e. CC ) for a monomial's canonical form.
    pub fn monomial_cc(
        &mut self,
        o: &mut dyn Oracle,
        monomial: &Monomial,
    ) -> Checked<Proof> {
        let key = Made::MonomialCc(monomial.clone());
        if let Some(p) = self.made.get(&key) {
            return Ok(p.clone());
        }
        let made = if monomial.is_empty() {
            self.number(o, &big(1))
        } else {
            let mut said: Option<Rpn> = None;
            let mut out: Option<Proof> = None;
            for (name, power) in monomial {
                let atom = o.atom(name)?;
                let index = self.index(o, *power as i64);
                let one = o.b().ap(
                    "expcld",
                    &binds! {"ph" => &self.under, "A" => name, "N" => n(*power)},
                    &[&atom, &index],
                );
                let spelt = op(name, &n(*power), EXP);
                match (&said, &out) {
                    (Some(s), Some(p)) => {
                        out = Some(o.b().ap(
                            "mulcld",
                            &binds! {"ph" => &self.under, "A" => s, "B" => &spelt},
                            &[p, &one],
                        ));
                        said = Some(op(s, &spelt, MUL));
                    }
                    _ => {
                        said = Some(spelt);
                        out = Some(one);
                    }
                }
            }
            out.expect("a monomial of one factor at least")
        };
        self.made.insert(key, made.clone());
        Ok(made)
    }

    /// ( under -> ( c x. M ) e. CC ).
    pub fn term_cc(
        &mut self,
        o: &mut dyn Oracle,
        monomial: &Monomial,
        weight: &Q,
    ) -> Checked<Proof> {
        let key = Made::TermCc(monomial.clone(), weight.clone());
        if let Some(p) = self.made.get(&key) {
            return Ok(p.clone());
        }
        let c = self.coefficient(o, weight);
        let m = self.monomial_cc(o, monomial)?;
        let made = o.b().ap(
            "mulcld",
            &binds! {"ph" => &self.under, "A" => coeff(weight), "B" => spell_monomial(monomial)},
            &[&c, &m],
        );
        self.made.insert(key, made.clone());
        Ok(made)
    }

    pub fn spell_term(item: &(Monomial, Q)) -> Rpn {
        op(&coeff(&item.1), &spell_monomial(&item.0), MUL)
    }

    /// A run of terms as one term; the empty run is zero.
    pub fn spell_run(items: &[(Monomial, Q)]) -> Rpn {
        if items.is_empty() {
            return n(0);
        }
        join(&items.iter().map(Self::spell_term).collect::<Vec<_>>(), ADD)
    }

    /// ( under -> spell_run(items) e. CC ), remembered once per run.
    pub fn run_cc(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
    ) -> Checked<Proof> {
        let said = Self::spell_run(items);
        if let Some(p) = self.held.get(&said) {
            return Ok(p.clone());
        }
        let out = if items.is_empty() {
            self.number(o, &big(0))
        } else {
            let mut out = self.term_cc(o, &items[0].0, &items[0].1)?;
            let mut running = Self::spell_term(&items[0]);
            for item in &items[1..] {
                let one = Self::spell_term(item);
                let cc = self.term_cc(o, &item.0, &item.1)?;
                out = o.b().ap(
                    "addcld",
                    &binds! {"ph" => &self.under, "A" => &running, "B" => &one},
                    &[&out, &cc],
                );
                running = op(&running, &one, ADD);
            }
            out
        };
        self.held.insert(said, out.clone());
        Ok(out)
    }

    // --- moving a term along a sum -------------------------------------

    /// Carry an equality of a prefix out to the whole run.
    ///
    /// A canonical form associates to the left, so a rewrite of the first k
    /// parts sits under one `oveq1d` for each part after them. Sums and
    /// products are the same shape, which is why this takes the operation.
    pub(super) fn lift(
        &self,
        o: &dyn Oracle,
        proof: Proof,
        left: &Rpn,
        right: &Rpn,
        tail: &[Rpn],
        what: &str,
    ) -> Proof {
        let (mut proof, mut left, mut right) = (proof, left.clone(), right.clone());
        for one in tail {
            proof = o.b().ap(
                "oveq1d",
                &binds! {"ph" => &self.under, "A" => &left, "B" => &right, "C" => one, "F" => what},
                &[&proof],
            );
            left = op(&left, one, what);
            right = op(&right, one, what);
        }
        proof
    }

    /// Two neighbours exchanged, as an equality of the whole run: `add32`
    /// where they sit at the end of a run, `addcom` where they are the whole
    /// of it, and the terms after them come along under `lift`.
    pub(super) fn swap(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
        at: usize,
    ) -> Checked<Proof> {
        let head = &items[..at];
        let a = Self::spell_term(&items[at]);
        let b = Self::spell_term(&items[at + 1]);
        let tail: Vec<Rpn> = items[at + 2..].iter().map(Self::spell_term).collect();
        let (before, after, step);
        if !head.is_empty() {
            let prefix = Self::spell_run(head);
            before = op(&op(&prefix, &a, ADD), &b, ADD);
            after = op(&op(&prefix, &b, ADD), &a, ADD);
            let p0 = self.run_cc(o, head)?;
            let p1 = self.term_cc(o, &items[at].0, &items[at].1)?;
            let p2 = self.term_cc(o, &items[at + 1].0, &items[at + 1].1)?;
            let bb = o.b();
            let law =
                bb.ap("add32", &binds! {"A" => &prefix, "B" => &a, "C" => &b}, &[]);
            step = bb.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(prefix, "cc", "wcel"),
                "ch" => t!(a, "cc", "wcel"), "th" => t!(b, "cc", "wcel"),
                "ta" => t!(before, after, "wceq")},
                &[&p0, &p1, &p2, &law],
            );
        } else {
            before = op(&a, &b, ADD);
            after = op(&b, &a, ADD);
            let p1 = self.term_cc(o, &items[at].0, &items[at].1)?;
            let p2 = self.term_cc(o, &items[at + 1].0, &items[at + 1].1)?;
            let bb = o.b();
            let law = bb.ap("addcom", &binds! {"A" => &a, "B" => &b}, &[]);
            step = bb.ap(
                "syl2anc",
                &binds! {"ph" => &self.under, "ps" => t!(a, "cc", "wcel"),
                "ch" => t!(b, "cc", "wcel"), "th" => t!(before, after, "wceq")},
                &[&p1, &p2, &law],
            );
        }
        Ok(self.lift(o, step, &before, &after, &tail, ADD))
    }

    // --- coefficients ---------------------------------------------------

    /// ( under -> claim ) from a claim that holds outright.
    pub fn a1i(&self, o: &dyn Oracle, claim: &Rpn, proof: &Proof) -> Proof {
        o.b().ap(
            "a1i",
            &binds! {"ph" => claim, "ps" => &self.under},
            &[proof],
        )
    }

    /// ( under -> ( c + d ) = e ), the coefficients as `spell` writes them.
    ///
    /// Two whole numbers are added by `numerals::sum`, digit by digit. A
    /// pair that cancels is `negidd`, and a sign is taken off first where
    /// there is one, so that what is added is two whole numbers.
    pub fn coefficient_sum(
        &mut self,
        o: &dyn Oracle,
        first: &Q,
        second: &Q,
    ) -> Route<Proof> {
        let total = first + second;
        let said = spell_coefficient(&total);
        let (c, d) = (spell_coefficient(first), spell_coefficient(second));
        let (Some(said), Some(c), Some(d)) = (said, c, d) else {
            return Route::no(format!(
                "{} + {} is not a sum of whole numbers",
                show(first),
                show(second)
            ));
        };
        let claim = t!(op(&c, &d, ADD), said, "wceq");
        let (a, bn) = (whole(first), whole(second));
        if a == -&bn && !a.is_zero() {
            let whole_n = spelt(&a);
            let num = self.number(o, &a.abs());
            let cancels = o.b().ap(
                "negidd",
                &binds! {"ph" => &self.under, "A" => whole_n},
                &[&num],
            );
            if a.is_positive() {
                return Built(cancels);
            }
            // The negative one first, so the two are commuted before they
            // cancel: `negid` states the sum only one way round.
            let pc = self.coefficient(o, first);
            let pd = self.coefficient(o, second);
            let bb = o.b();
            let law = bb.ap("addcom", &binds! {"A" => &c, "B" => &d}, &[]);
            let turned = bb.ap(
                "syl2anc",
                &binds! {"ph" => &self.under, "ps" => t!(c, "cc", "wcel"),
                "ch" => t!(d, "cc", "wcel"),
                "th" => t!(op(&c, &d, ADD), op(&d, &c, ADD), "wceq")},
                &[&pc, &pd, &law],
            );
            return Built(self.chain(
                o,
                &turned,
                &cancels,
                &op(&c, &d, ADD),
                &op(&d, &c, ADD),
                &n(0),
            ));
        }
        if a.is_negative() && bn.is_negative() {
            // -u i + -u j is -u ( i + j ), which `negdi` says read
            // backwards, and the two are then both positive.
            let w = [spelt(&a), spelt(&bn)];
            let both = match self.coefficient_sum(o, &-first, &-second) {
                Built(p) => p,
                Declined(d) => return Declined(d),
            };
            let pa = self.number(o, &-&a);
            let pb = self.number(o, &-&bn);
            let bb = o.b();
            let sum = op(&w[0], &w[1], ADD);
            let law = bb.ap("negdi", &binds! {"A" => &w[0], "B" => &w[1]}, &[]);
            let inner = bb.ap(
                "syl2anc",
                &binds! {"ph" => &self.under, "ps" => t!(w[0], "cc", "wcel"),
                "ch" => t!(w[1], "cc", "wcel"),
                "th" => t!(t!(sum, "cneg"), op(&c, &d, ADD), "wceq")},
                &[&pa, &pb, &law],
            );
            let back = bb.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => t!(sum, "cneg"), "B" => op(&c, &d, ADD)},
                &[&inner],
            );
            let negated = bb.ap(
                "negeqd",
                &binds! {"ph" => &self.under, "A" => &sum, "B" => spelt(&(&a + &bn))},
                &[&both],
            );
            return Built(self.chain(
                o,
                &back,
                &negated,
                &op(&c, &d, ADD),
                &t!(sum, "cneg"),
                &said,
            ));
        }
        if a.is_negative() || bn.is_negative() {
            if a.is_negative() {
                // The negative one second, so one case covers both.
                let swapped = match self.coefficient_sum(o, second, first) {
                    Built(p) => p,
                    Declined(d) => return Declined(d),
                };
                let pc = self.coefficient(o, first);
                let pd = self.coefficient(o, second);
                let bb = o.b();
                let law = bb.ap("addcom", &binds! {"A" => &c, "B" => &d}, &[]);
                let turned = bb.ap(
                    "syl2anc",
                    &binds! {"ph" => &self.under, "ps" => t!(c, "cc", "wcel"),
                    "ch" => t!(d, "cc", "wcel"),
                    "th" => t!(op(&c, &d, ADD), op(&d, &c, ADD), "wceq")},
                    &[&pc, &pd, &law],
                );
                return Built(self.chain(
                    o,
                    &turned,
                    &swapped,
                    &op(&c, &d, ADD),
                    &op(&d, &c, ADD),
                    &said,
                ));
            }
            return self.minus_numeral(o, &a, &-&bn, &c, &d, &said);
        }
        let held = numerals::sum(o.b(), a.magnitude().clone(), bn.magnitude().clone());
        Built(self.a1i(o, &claim, &held))
    }

    /// ( under -> ( i - j ) = k ) for whole numbers with i at least j.
    ///
    /// `subadd` says a difference is a number exactly when adding that
    /// number back gives the first, so the subtraction is answered out of
    /// the addition table and set.mm needs no second one.
    pub(super) fn gap_numeral(
        &mut self,
        o: &dyn Oracle,
        bigger: &BigInt,
        smaller: &BigInt,
    ) -> Route<Proof> {
        let gap = bigger - smaller;
        let (left, right, out) = (spelt(bigger), spelt(smaller), spelt(&gap));
        let (left, right, out) = (&left, &right, &out);
        let back = match self.coefficient_sum(
            o,
            &Q::from_integer(smaller.clone()),
            &Q::from_integer(gap.clone()),
        ) {
            Built(p) => p,
            Declined(d) => return Declined(d),
        };
        let p0 = self.number(o, bigger);
        let p1 = self.number(o, smaller);
        let p2 = self.number(o, &gap);
        let b = o.b();
        let law = b.ap(
            "subadd",
            &binds! {"A" => left, "B" => right, "C" => out},
            &[],
        );
        let turn = b.ap(
            "syl3anc",
            &binds! {"ph" => &self.under, "ps" => t!(left, "cc", "wcel"),
            "ch" => t!(right, "cc", "wcel"), "th" => t!(out, "cc", "wcel"),
            "ta" => t!(t!(op(left, right, "cmin"), out, "wceq"),
                       t!(op(right, out, ADD), left, "wceq"), "wb")},
            &[&p0, &p1, &p2, &law],
        );
        Built(b.ap(
            "mpbird",
            &binds! {"ph" => &self.under,
            "ps" => t!(op(left, right, "cmin"), out, "wceq"),
            "ch" => t!(op(right, out, ADD), left, "wceq")},
            &[&back, &turn],
        ))
    }

    /// ( under -> ( i + -u j ) = k ), the two of opposite sign: `negsub`
    /// turns the sum into a difference, and which way round the difference
    /// goes decides whether the answer carries a minus.
    pub(super) fn minus_numeral(
        &mut self,
        o: &dyn Oracle,
        first: &BigInt,
        second: &BigInt,
        c: &Rpn,
        d: &Rpn,
        said: &Rpn,
    ) -> Route<Proof> {
        let (sf, ss) = (spelt(first), spelt(second));
        let gap = op(&sf, &ss, "cmin");
        let apart = match self.same_gap(o, first, second) {
            Built(p) => p,
            Declined(d) => return Declined(d),
        };
        let p0 = self.number(o, first);
        let p1 = self.number(o, second);
        let b = o.b();
        let law = b.ap("negsub", &binds! {"A" => &sf, "B" => &ss}, &[]);
        let turned = b.ap(
            "syl2anc",
            &binds! {"ph" => &self.under, "ps" => t!(&sf, "cc", "wcel"),
            "ch" => t!(&ss, "cc", "wcel"),
            "th" => t!(op(c, d, ADD), gap, "wceq")},
            &[&p0, &p1, &law],
        );
        Built(self.chain(o, &turned, &apart, &op(c, d, ADD), &gap, said))
    }

    /// ( under -> ( i - j ) = k ), whichever way round the two are.
    pub(super) fn same_gap(
        &mut self,
        o: &dyn Oracle,
        first: &BigInt,
        second: &BigInt,
    ) -> Route<Proof> {
        if first >= second {
            return self.gap_numeral(o, first, second);
        }
        let (f, s) = (spelt(first), spelt(second));
        let (f, s) = (&f, &s);
        let gap = spelt(&(second - first));
        let other = op(s, f, "cmin");
        let back = match self.gap_numeral(o, second, first) {
            Built(p) => p,
            Declined(d) => return Declined(d),
        };
        let p0 = self.number(o, second);
        let p1 = self.number(o, first);
        let b = o.b();
        let law = b.ap("negsubdi2", &binds! {"A" => s, "B" => f}, &[]);
        let inner = b.ap(
            "syl2anc",
            &binds! {"ph" => &self.under, "ps" => t!(s, "cc", "wcel"),
            "ch" => t!(f, "cc", "wcel"),
            "th" => t!(t!(other, "cneg"), op(f, s, "cmin"), "wceq")},
            &[&p0, &p1, &law],
        );
        let turned = b.ap(
            "eqcomd",
            &binds! {"ph" => &self.under, "A" => t!(other, "cneg"), "B" => op(f, s, "cmin")},
            &[&inner],
        );
        let negated = b.ap(
            "negeqd",
            &binds! {"ph" => &self.under, "A" => &other, "B" => &gap},
            &[&back],
        );
        Built(self.chain(
            o,
            &turned,
            &negated,
            &op(f, s, "cmin"),
            &t!(other, "cneg"),
            &t!(&gap, "cneg"),
        ))
    }

    // --- putting one term into a run ------------------------------------

    /// ( under -> ( ( c x. M ) + ( d x. M ) ) = ( e x. M ) ): `adddir` read
    /// the other way collects two terms that share a monomial, which is the
    /// only place the coefficients meet.
    pub(super) fn combine(
        &mut self,
        o: &mut dyn Oracle,
        monomial: &Monomial,
        first: &Q,
        second: &Q,
    ) -> Checked<Route<Proof>> {
        let spelt = spell_monomial(monomial);
        let (c, d) = (coeff(first), coeff(second));
        let total = coeff(&(first + second));
        let pc = self.coefficient(o, first);
        let pd = self.coefficient(o, second);
        let pm = self.monomial_cc(o, monomial)?;
        let apart = op(&op(&c, &spelt, MUL), &op(&d, &spelt, MUL), ADD);
        let together = op(&op(&c, &d, ADD), &spelt, MUL);
        let gathered = {
            let b = o.b();
            let law =
                b.ap("adddir", &binds! {"A" => &c, "B" => &d, "C" => &spelt}, &[]);
            let inner = b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(c, "cc", "wcel"),
                "ch" => t!(d, "cc", "wcel"), "th" => t!(spelt, "cc", "wcel"),
                "ta" => t!(together, apart, "wceq")},
                &[&pc, &pd, &pm, &law],
            );
            b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => &together, "B" => &apart},
                &[&inner],
            )
        };
        let added = take!(self.coefficient_sum(o, first, second));
        let moved = o.b().ap(
            "oveq1d",
            &binds! {"ph" => &self.under, "A" => op(&c, &d, ADD), "B" => &total,
            "C" => &spelt, "F" => MUL},
            &[&added],
        );
        Ok(Built(self.chain(
            o,
            &gathered,
            &moved,
            &apart,
            &together,
            &op(&total, &spelt, MUL),
        )))
    }

    /// ( under -> spell_run(items) = spell_run(moved) ), one term moved.
    ///
    /// Leftward is the direction an appended term travels to reach the
    /// place its degree puts it; rightward is how a term whose coefficient
    /// has cancelled reaches the end, where it comes off. Each step is one
    /// `swap`.
    pub(super) fn shift(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
        frm: usize,
        to: usize,
    ) -> Checked<(Run, Proof)> {
        let start = Self::spell_run(items);
        let mut said = start.clone();
        let mut items: Run = items.to_vec();
        let mut proof: Option<Proof> = None;
        let steps: Vec<usize> = if to > frm {
            (frm..to).collect()
        } else {
            (to..frm).rev().collect()
        };
        for at in steps {
            let step = self.swap(o, &items, at)?;
            items.swap(at, at + 1);
            let after = Self::spell_run(&items);
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
        Ok((items, proof))
    }

    /// ( under -> spell_run(items) = spell_run(rest) ), a zero term gone.
    ///
    /// A coefficient that has cancelled leaves `( 0 x. M )`, which is zero
    /// by `mul02` and comes off the end by `addrid`. The term is walked to
    /// the end first, because that is where it can come off.
    pub(super) fn drop(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
        at: usize,
    ) -> Checked<(Run, Proof)> {
        let start = Self::spell_run(items);
        let (items, walked) = self.shift(o, items, at, items.len() - 1)?;
        let run = Self::spell_run(&items);
        let rest: Run = items[..items.len() - 1].to_vec();
        let last = &items[items.len() - 1];
        let zero = Self::spell_term(last);
        let spelt = spell_monomial(&last.0);
        let pm = self.monomial_cc(o, &last.0)?;
        let vanishes = {
            let b = o.b();
            let law = b.ap("mul02", &binds! {"A" => &spelt}, &[]);
            b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(spelt, "cc", "wcel"),
                "ch" => t!(zero, &n(0), "wceq")},
                &[&pm, &law],
            )
        };
        if rest.is_empty() {
            let p = self.chain(o, &walked, &vanishes, &start, &run, &n(0));
            return Ok((rest, p));
        }
        let keep = Self::spell_run(&rest);
        let rc = self.run_cc(o, &rest)?;
        let comes_off = {
            let b = o.b();
            let first = b.ap(
                "oveq2d",
                &binds! {"ph" => &self.under, "A" => &zero, "B" => n(0), "C" => &keep, "F" => ADD},
                &[&vanishes],
            );
            let law = b.ap("addrid", &binds! {"A" => &keep}, &[]);
            let second = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(keep, "cc", "wcel"),
                "ch" => t!(op(&keep, &n(0), ADD), keep, "wceq")},
                &[&rc, &law],
            );
            self.chain(o, &first, &second, &run, &op(&keep, &n(0), ADD), &keep)
        };
        let p = self.chain(o, &walked, &comes_off, &start, &run, &keep);
        Ok((rest, p))
    }

    /// ( under -> ( spell_run(items) + ( c x. M ) ) = spell_run(out) ).
    ///
    /// One term put where its degree says it goes. If the monomial is
    /// already there the two coefficients meet and may cancel; otherwise the
    /// term simply travels left to its place.
    pub(super) fn insert(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
        monomial: &Monomial,
        weight: &Q,
    ) -> Checked<Route<(Run, Proof)>> {
        let term = Self::spell_term(&(monomial.clone(), weight.clone()));
        if items.is_empty() {
            let cc = self.term_cc(o, monomial, weight)?;
            let b = o.b();
            let law = b.ap("addlid", &binds! {"A" => &term}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(term, "cc", "wcel"),
                "ch" => t!(op(&n(0), &term, ADD), term, "wceq")},
                &[&cc, &law],
            );
            return Ok(Built((vec![(monomial.clone(), weight.clone())], p)));
        }
        let mut appended: Run = items.to_vec();
        appended.push((monomial.clone(), weight.clone()));
        let start = Self::spell_run(&appended);
        if let Some(at) = items.iter().position(|(m, _)| m == monomial) {
            let (moved, walked) = self.shift(o, &appended, items.len(), at + 1)?;
            let total = &moved[at].1 + &moved[at + 1].1;
            let joined = take!(self.gather(o, &moved, at)?);
            let mut out: Run = moved[..at].to_vec();
            out.push((monomial.clone(), total.clone()));
            out.extend(moved[at + 2..].iter().cloned());
            let mut proof = self.chain(
                o,
                &walked,
                &joined,
                &start,
                &Self::spell_run(&moved),
                &Self::spell_run(&out),
            );
            if total.is_zero() {
                let before = Self::spell_run(&out);
                let (rest, gone) = self.drop(o, &out, at)?;
                proof = self.chain(
                    o,
                    &proof,
                    &gone,
                    &start,
                    &before,
                    &Self::spell_run(&rest),
                );
                out = rest;
            }
            return Ok(Built((out, proof)));
        }
        let mine = order(monomial);
        let goes = items.iter().filter(|(m, _)| order(m) < mine).count();
        let (out, walked) = self.shift(o, &appended, items.len(), goes)?;
        Ok(Built((out, walked)))
    }

    /// Two neighbours that share a monomial, collected into one term:
    /// `addass` exposes them as a pair where they sit at the end of a run;
    /// where they are the whole of it they are already exposed.
    pub(super) fn gather(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
        at: usize,
    ) -> Checked<Route<Proof>> {
        let head = &items[..at];
        let rest = &items[at + 2..];
        let monomial = &items[at].0;
        let a = Self::spell_term(&items[at]);
        let b = Self::spell_term(&items[at + 1]);
        let total =
            Self::spell_term(&(monomial.clone(), &items[at].1 + &items[at + 1].1));
        let collect =
            take!(self.combine(o, monomial, &items[at].1, &items[at + 1].1)?);
        let tail: Vec<Rpn> = rest.iter().map(Self::spell_term).collect();
        if head.is_empty() {
            return Ok(Built(self.lift(
                o,
                collect,
                &op(&a, &b, ADD),
                &total,
                &tail,
                ADD,
            )));
        }
        let prefix = Self::spell_run(head);
        let p0 = self.run_cc(o, head)?;
        let p1 = self.term_cc(o, &items[at].0, &items[at].1)?;
        let p2 = self.term_cc(o, &items[at + 1].0, &items[at + 1].1)?;
        let outer = op(&op(&prefix, &a, ADD), &b, ADD);
        let inner_pair = op(&prefix, &op(&a, &b, ADD), ADD);
        let exposed = {
            let bb = o.b();
            let law = bb.ap(
                "addass",
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
            &binds! {"ph" => &self.under, "A" => op(&a, &b, ADD), "B" => &total,
            "C" => &prefix, "F" => ADD},
            &[&collect],
        );
        let step = self.chain(
            o,
            &exposed,
            &moved,
            &outer,
            &inner_pair,
            &op(&prefix, &total, ADD),
        );
        Ok(Built(self.lift(
            o,
            step,
            &outer,
            &op(&prefix, &total, ADD),
            &tail,
            ADD,
        )))
    }

    /// ( under -> ( spell_run(left) + spell_run(right) ) = spell_run(sum) ).
    ///
    /// The right-hand run is taken apart from its end, one term at a time,
    /// and each is put into the left by `insert`. `addass` is what peels a
    /// term off: the run associates to the left, so its last term is
    /// already where the law can reach it.
    pub fn add(
        &mut self,
        o: &mut dyn Oracle,
        left: &[(Monomial, Q)],
        right: &[(Monomial, Q)],
    ) -> Checked<Route<(Run, Proof)>> {
        let start = op(&Self::spell_run(left), &Self::spell_run(right), ADD);
        if right.is_empty() {
            let keep = Self::spell_run(left);
            let rc = self.run_cc(o, left)?;
            let b = o.b();
            let law = b.ap("addrid", &binds! {"A" => &keep}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(keep, "cc", "wcel"),
                "ch" => t!(op(&keep, &n(0), ADD), keep, "wceq")},
                &[&rc, &law],
            );
            return Ok(Built((left.to_vec(), p)));
        }
        if right.len() == 1 {
            return self.insert(o, left, &right[0].0, &right[0].1);
        }
        let (rest, last) = (&right[..right.len() - 1], &right[right.len() - 1]);
        let whole_run = Self::spell_run(right);
        let prefix = Self::spell_run(rest);
        let held = Self::spell_run(left);
        let term = Self::spell_term(last);
        let p0 = self.run_cc(o, left)?;
        let p1 = self.run_cc(o, rest)?;
        let p2 = self.term_cc(o, &last.0, &last.1)?;
        let grouped = op(&op(&held, &prefix, ADD), &term, ADD);
        let peeled = {
            let b = o.b();
            let law = b.ap(
                "addass",
                &binds! {"A" => &held, "B" => &prefix, "C" => &term},
                &[],
            );
            let inner = b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(held, "cc", "wcel"),
                "ch" => t!(prefix, "cc", "wcel"), "th" => t!(term, "cc", "wcel"),
                "ta" => t!(grouped, op(&held, &whole_run, ADD), "wceq")},
                &[&p0, &p1, &p2, &law],
            );
            b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => &grouped, "B" => op(&held, &whole_run, ADD)},
                &[&inner],
            )
        };
        let (merged, inner) = take!(self.add(o, left, rest)?);
        let carried = o.b().ap(
            "oveq1d",
            &binds! {"ph" => &self.under, "A" => op(&held, &prefix, ADD),
            "B" => Self::spell_run(&merged), "C" => &term, "F" => ADD},
            &[&inner],
        );
        let (out, placed) = take!(self.insert(o, &merged, &last.0, &last.1)?);
        let middle = op(&Self::spell_run(&merged), &term, ADD);
        let first = self.chain(o, &peeled, &carried, &start, &grouped, &middle);
        let p = self.chain(o, &first, &placed, &start, &middle, &Self::spell_run(&out));
        Ok(Built((out, p)))
    }

    // --- monomials --------------------------------------------------------
    //
    // The same shape as the sum side, over products, and shorter for one
    // reason: a monomial holds only positive powers, so multiplying two of
    // them adds positive numbers and nothing can cancel.
}
