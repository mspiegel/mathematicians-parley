//! Positive and bounded products, roots and logarithms.

use super::*;

impl<'a> Elaborator<'a> {
    /// ( scope -> 0 < canon ) for the canon of a value above 0, shown as the
    /// decider found it (`reals::sign_of`): a rational by `arithmetic`, and
    /// any other value by its multiple by the least common denominator of
    /// its coefficients, over that denominator (`divgt0d`).
    pub(super) fn canon_positive(
        &mut self,
        canon_of: &Rpn,
        value: &Real,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let reals::Sign::Shown {
            positive: true,
            how,
        } = reals::sign_of(value)
        else {
            return Ok(Route::no("a difference not shown above 0"));
        };
        if how == reals::Shown::Rational {
            return self
                .numeral_fact(&t!("cc0", canon_of, "clt", "wbr"), scope, facts)
                .map(Built);
        }
        let common = field::common_denominator(&value.weights());
        let whole = value.times(&Real::rational(Q::from_integer(common.clone())));
        let said = whole_canon(&whole);
        let above = match how {
            reals::Shown::Bracketed { precision } => {
                take!(self.bracketed_positive(&said, &whole, precision, scope, facts)?)
            }
            _ => take!(self.logarithms_positive(&said, &whole, scope, facts)?),
        };
        if common.is_one() {
            return Ok(Built(above));
        }
        let under = numerals::spell(common.magnitude().clone());
        debug_assert_eq!(*canon_of, t!(&said, &under, "cdiv", "co"));
        let said_real = self.membership(&said, "cr", scope, facts)?;
        let under_real = self.numeral_fact(&t!(&under, "cr", "wcel"), scope, facts)?;
        let under_above =
            self.numeral_fact(&t!("cc0", &under, "clt", "wbr"), scope, facts)?;
        Ok(Built(self.b.ap(
            "divgt0d",
            &binds! {"ph" => scope, "A" => &said, "B" => &under},
            &[&said_real, &under_real, &above, &under_above],
        )))
    }

    /// ( scope -> 0 < said ) for whole multiples of logarithms of primes
    /// whose ratio r is above 1: said is ln r (an identity, and the
    /// logarithm worked out), which is above 0 (`loggt0b`).
    pub(super) fn logarithms_positive(
        &mut self,
        said: &Rpn,
        value: &Real,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let Some(reals::Logarithmic { logs, .. }) = value.logarithmic() else {
            return Ok(Route::no("a difference that is not logarithms of primes"));
        };
        let Ok(reals::LogarithmRatio { ratio, .. }) = reals::logarithm_ratio(&logs)
        else {
            return Ok(Route::no("a multiple of a logarithm too large"));
        };
        let logged = take!(self.ln_rational(&ratio, scope, facts)?);
        let is = take!(self.identity(said, &logged.expression, scope, facts)?);
        let log_r = t!(&logged.ratio, "clog", "cfv");
        let back = self.b.ap(
            "eqcomd",
            &binds! {"ph" => scope, "A" => &log_r, "B" => &logged.expression},
            &[&logged.proof],
        );
        let is_log = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => said, "B" => &logged.expression, "C" => &log_r},
            &[&is, &back],
        );
        let r_rp = self.positive(&logged.ratio, scope, facts)?;
        let past_one =
            self.numeral_fact(&t!("c1", &logged.ratio, "clt", "wbr"), scope, facts)?;
        let law = self.b.ap("loggt0b", &binds! {"A" => &logged.ratio}, &[]);
        let log_above = t!("cc0", &log_r, "clt", "wbr");
        let past = t!("c1", &logged.ratio, "clt", "wbr");
        let iff = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(&logged.ratio, "crp", "wcel"), "ch" => t!(&log_above, &past, "wb")},
            &[&r_rp, &law],
        );
        let above = self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &log_above, "ch" => &past},
            &[&past_one, &iff],
        );
        Ok(Built(self.b.ap(
            "breqtrrd",
            &binds! {"ph" => scope, "A" => "cc0", "B" => &log_r, "C" => said, "R" => "clt"},
            &[&above, &is_log],
        )))
    }

    /// ( scope -> 0 < said ) for the canon of a value with whole
    /// coefficients whose bracket at `precision` lies above 0: each part is
    /// above the closed numeral term its bracket gives (`part_above`), the
    /// sum above the sum of those (`lt2addd`, `leltaddd`), and that sum is
    /// at least 0 by `arithmetic` (`lelttrd`).
    pub(super) fn bracketed_positive(
        &mut self,
        said: &Rpn,
        value: &Real,
        precision: u32,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut sum: Option<SumBelow> = None;
        for part in canon_parts(value) {
            let next = take!(self.part_above(&part, precision, scope, facts)?);
            sum = Some(match sum {
                None => next,
                Some(held) => {
                    debug_assert!(next.strict, "a rational part comes first");
                    let law = rules::adding(held.strict, next.strict).deduction;
                    let a = self.membership(&held.low, "cr", scope, facts)?;
                    let b = self.membership(&next.low, "cr", scope, facts)?;
                    let c = self.membership(&held.said, "cr", scope, facts)?;
                    let d = self.membership(&next.said, "cr", scope, facts)?;
                    let proof = self.b.ap(
                        law,
                        &binds! {"ph" => scope, "A" => &held.low, "B" => &next.low, "C" => &held.said, "D" => &next.said},
                        &[&a, &b, &c, &d, &held.proof, &next.proof],
                    );
                    SumBelow {
                        said: t!(&held.said, &next.said, "caddc", "co"),
                        low: t!(&held.low, &next.low, "caddc", "co"),
                        proof,
                        strict: true,
                    }
                }
            });
        }
        let Some(sum) = sum.filter(|s| s.strict) else {
            return Ok(Route::no("a value with no part beyond a rational"));
        };
        debug_assert_eq!(sum.said, *said);
        let zero_real = self.numeral_fact(&t!("cc0", "cr", "wcel"), scope, facts)?;
        let low_real = self.membership(&sum.low, "cr", scope, facts)?;
        let said_real = self.membership(said, "cr", scope, facts)?;
        let at_least =
            self.numeral_fact(&t!("cc0", &sum.low, "cle", "wbr"), scope, facts)?;
        Ok(Built(self.b.ap(
            transitivity("cle", "clt"),
            &binds! {"ph" => scope, "A" => "cc0", "B" => &sum.low, "C" => said},
            &[&zero_real, &low_real, &said_real, &at_least, &sum.proof],
        )))
    }

    /// A part of a canon above a closed numeral term. A rational part is
    /// at least itself (`leidd`); c·F, F a product of factors with c above
    /// 0, is above c times F's lower end (`ltmul2dd`), and with c = −n below
    /// 0, above −n times F's upper end, n·F < n·u turned round by `ltnegd`
    /// and −(n·x) = −n·x (`mulneg1d`).
    pub(super) fn part_above(
        &mut self,
        part: &CanonPart,
        precision: u32,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<SumBelow>> {
        if part.factors.is_empty() {
            let real =
                self.numeral_fact(&t!(&part.said, "cr", "wcel"), scope, facts)?;
            let proof = self.b.ap(
                "leidd",
                &binds! {"ph" => scope, "A" => &part.said},
                &[&real],
            );
            return Ok(Built(SumBelow {
                said: part.said.clone(),
                low: part.said.clone(),
                proof,
                strict: false,
            }));
        }
        let product =
            take!(self.product_bounded(&part.factors, precision, scope, facts)?);
        let size = numerals::spell(part.weight.numer().magnitude().clone());
        let size_rp = self.positive(&size, scope, facts)?;
        let product_real = self.membership(&product.said, "cr", scope, facts)?;
        if part.weight.is_positive() {
            let low_real = self.membership(&product.low, "cr", scope, facts)?;
            let proof = self.b.ap(
                "ltmul2dd",
                &binds! {"ph" => scope, "A" => &product.low, "B" => &product.said, "C" => &size},
                &[&low_real, &product_real, &size_rp, &product.below],
            );
            return Ok(Built(SumBelow {
                said: part.said.clone(),
                low: t!(&size, &product.low, "cmul", "co"),
                proof,
                strict: true,
            }));
        }
        let high_real = self.membership(&product.high, "cr", scope, facts)?;
        let scaled = self.b.ap(
            "ltmul2dd",
            &binds! {"ph" => scope, "A" => &product.said, "B" => &product.high, "C" => &size},
            &[&product_real, &high_real, &size_rp, &product.above],
        );
        let (times_said, times_high) = (
            t!(&size, &product.said, "cmul", "co"),
            t!(&size, &product.high, "cmul", "co"),
        );
        let times_said_real = self.membership(&times_said, "cr", scope, facts)?;
        let times_high_real = self.membership(&times_high, "cr", scope, facts)?;
        let iff = self.b.ap(
            "ltnegd",
            &binds! {"ph" => scope, "A" => &times_said, "B" => &times_high},
            &[&times_said_real, &times_high_real],
        );
        let (neg_said, neg_high) = (t!(&times_said, "cneg"), t!(&times_high, "cneg"));
        let turned = self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(&times_said, &times_high, "clt", "wbr"), "ch" => t!(&neg_high, &neg_said, "clt", "wbr")},
            &[&scaled, &iff],
        );
        let minus = t!(&size, "cneg");
        let size_cc = self.numeral_fact(&t!(&size, "cc", "wcel"), scope, facts)?;
        let said_cc = take!(self.in_cc(&product.said, scope, facts)?);
        let high_cc =
            self.numeral_fact(&t!(&product.high, "cc", "wcel"), scope, facts)?;
        let said_moved = self.b.ap(
            "mulneg1d",
            &binds! {"ph" => scope, "A" => &size, "B" => &product.said},
            &[&size_cc, &said_cc],
        );
        let high_moved = self.b.ap(
            "mulneg1d",
            &binds! {"ph" => scope, "A" => &size, "B" => &product.high},
            &[&size_cc, &high_cc],
        );
        let low = t!(&minus, &product.high, "cmul", "co");
        let from_low = self.b.ap(
            "eqbrtrd",
            &binds! {"ph" => scope, "A" => &low, "B" => &neg_high, "C" => &neg_said, "R" => "clt"},
            &[&high_moved, &turned],
        );
        debug_assert_eq!(part.said, t!(&minus, &product.said, "cmul", "co"));
        let proof = self.b.ap(
            "breqtrrd",
            &binds! {"ph" => scope, "A" => &low, "B" => &neg_said, "C" => &part.said, "R" => "clt"},
            &[&from_low, &said_moved],
        );
        Ok(Built(SumBelow {
            said: part.said.clone(),
            low,
            proof,
            strict: true,
        }))
    }

    /// A product of factors, nested from the right, between the products of
    /// their ends: each step `ltmul12ad`, below with the factors' lower
    /// ends, which are at least 0, and above with the factors themselves,
    /// which are above their lower ends.
    pub(super) fn product_bounded(
        &mut self,
        factors: &[(reals::Factor, u32)],
        precision: u32,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Bounded>> {
        let Some((last, before)) = factors.split_last() else {
            return Ok(Route::no("a product of no factors"));
        };
        let mut rest = take!(self.factor_bounded(*last, precision, scope, facts)?);
        for factor in before.iter().rev() {
            let first = take!(self.factor_bounded(*factor, precision, scope, facts)?);
            let mut ends = Vec::new();
            for end in [&first.low, &rest.low] {
                ends.push(self.numeral_fact(
                    &t!("cc0", end, "cle", "wbr"),
                    scope,
                    facts,
                )?);
            }
            let below = self.product_step(
                [&first.low, &first.said, &rest.low, &rest.said],
                [&ends[0], &first.below, &ends[1], &rest.below],
                scope,
                facts,
            )?;
            let first_from = self.at_least_zero(&first, scope, facts)?;
            let rest_from = self.at_least_zero(&rest, scope, facts)?;
            let above = self.product_step(
                [&first.said, &first.high, &rest.said, &rest.high],
                [&first_from, &first.above, &rest_from, &rest.above],
                scope,
                facts,
            )?;
            rest = Bounded {
                said: t!(&first.said, &rest.said, "cmul", "co"),
                low: t!(&first.low, &rest.low, "cmul", "co"),
                high: t!(&first.high, &rest.high, "cmul", "co"),
                below,
                above,
            };
        }
        Ok(Built(rest))
    }

    /// ( scope -> ( A x. C ) < ( B x. D ) ) from 0 <_ A, A < B, 0 <_ C and
    /// C < D, given in that order (`ltmul12ad`).
    pub(super) fn product_step(
        &mut self,
        [a, b, c, d]: [&Rpn; 4],
        [a_from, a_below_b, c_from, c_below_d]: [&Proof; 4],
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let mut held = Vec::new();
        for x in [a, b, c, d] {
            held.push(self.membership(x, "cr", scope, facts)?);
        }
        Ok(self.b.ap(
            "ltmul12ad",
            &binds! {"ph" => scope, "A" => a, "B" => b, "C" => c, "D" => d},
            &[
                &held[0], &held[1], &held[2], &held[3], a_from, a_below_b, c_from,
                c_below_d,
            ],
        ))
    }

    /// ( scope -> 0 <_ x ) for a term above its lower end, which is above 0
    /// (`above_zero`, `rpge0d`).
    pub(super) fn at_least_zero(
        &mut self,
        x: &Bounded,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let positive = self.above_zero(&x.said, &x.low, &x.below, scope, facts)?;
        Ok(self.b.ap(
            "rpge0d",
            &binds! {"ph" => scope, "A" => &x.said},
            &[&positive],
        ))
    }

    /// A factor of a canon's part between its bracket's ends
    /// (`reals::factor_bracket`), and a power of one between the powers of
    /// its ends (`ltexp1dd`).
    pub(super) fn factor_bounded(
        &mut self,
        (factor, k): (reals::Factor, u32),
        precision: u32,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Bounded>> {
        let base = match factor {
            reals::Factor::Root(p) => self.root_bounded(p, precision, scope, facts)?,
            reals::Factor::Atom(Atom::Pi) => {
                let below =
                    self.closed_law(&t!("c3", "cpi", "clt", "wbr"), "pigt3", scope);
                let above = self.closed_half(
                    [t!("c2", "cpi", "clt", "wbr"), t!("cpi", "c4", "clt", "wbr")],
                    "pigt2lt4",
                    true,
                    scope,
                );
                Bounded {
                    said: t!("cpi"),
                    low: t!("c3"),
                    high: t!("c4"),
                    below,
                    above,
                }
            }
            reals::Factor::Atom(Atom::E) => {
                let [below, above] = self.e_bounds(scope);
                Bounded {
                    said: t!("ceu"),
                    low: t!("c2"),
                    high: t!("c3"),
                    below,
                    above,
                }
            }
            reals::Factor::Atom(Atom::Ln(p)) => {
                take!(self.ln_bounded(p, scope, facts)?)
            }
        };
        if k == 1 {
            return Ok(Built(base));
        }
        let power = numeral(k);
        let power_nn = self.numeral_fact(&t!(&power, "cn", "wcel"), scope, facts)?;
        let low_rp = self.positive(&base.low, scope, facts)?;
        let high_rp = self.positive(&base.high, scope, facts)?;
        let said_rp =
            self.above_zero(&base.said, &base.low, &base.below, scope, facts)?;
        let below = self.b.ap(
            "ltexp1dd",
            &binds! {"ph" => scope, "A" => &base.low, "B" => &base.said, "N" => &power},
            &[&low_rp, &said_rp, &power_nn, &base.below],
        );
        let above = self.b.ap(
            "ltexp1dd",
            &binds! {"ph" => scope, "A" => &base.said, "B" => &base.high, "N" => &power},
            &[&said_rp, &high_rp, &power_nn, &base.above],
        );
        let raised = |x: &Rpn| t!(x, &power, "cexp", "co");
        Ok(Built(Bounded {
            said: raised(&base.said),
            low: raised(&base.low),
            high: raised(&base.high),
            below,
            above,
        }))
    }

    /// ( scope -> x e. RR+ ) for x above a lower end above 0: 0 < low by
    /// `arithmetic`, and low < x (`lttrd`, `elrpd`).
    pub(super) fn above_zero(
        &mut self,
        x: &Rpn,
        low: &Rpn,
        low_below_x: &Proof,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let zero_real = self.numeral_fact(&t!("cc0", "cr", "wcel"), scope, facts)?;
        let low_real = self.numeral_fact(&t!(low, "cr", "wcel"), scope, facts)?;
        let x_real = self.membership(x, "cr", scope, facts)?;
        let low_above =
            self.numeral_fact(&t!("cc0", low, "clt", "wbr"), scope, facts)?;
        let above = self.b.ap(
            transitivity("clt", "clt"),
            &binds! {"ph" => scope, "A" => "cc0", "B" => low, "C" => x},
            &[&zero_real, &low_real, &x_real, &low_above, low_below_x],
        );
        Ok(self.b.ap(
            "elrpd",
            &binds! {"ph" => scope, "A" => x},
            &[&x_real, &above],
        ))
    }

    /// √p between the ends of its bracket at `precision`: l² < p by
    /// `arithmetic`, so √(l²) < √p (`sqrtltd`), and √(l²) is l (`sqrtsqd`);
    /// and p < u² the same way round.
    pub(super) fn root_bounded(
        &mut self,
        p: u64,
        precision: u32,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Bounded> {
        let surds::Bracket { below, above } = surds::root_bracket(p, precision);
        let (low, high) =
            (field::spell_rational(&below), field::spell_rational(&above));
        let prime = numerals::spell(p);
        let root = root_of_prime(p);
        let squared = |x: &Rpn| t!(x, "c2", "cexp", "co");
        let mut root_of_squares = Vec::new();
        for (end, small, big) in [
            (&low, squared(&low), prime.clone()),
            (&high, prime.clone(), squared(&high)),
        ] {
            let ordered =
                self.numeral_fact(&t!(&small, &big, "clt", "wbr"), scope, facts)?;
            let mut held = Vec::new();
            for x in [&small, &big] {
                held.push(self.numeral_fact(&t!(x, "cr", "wcel"), scope, facts)?);
                held.push(self.numeral_fact(
                    &t!("cc0", x, "cle", "wbr"),
                    scope,
                    facts,
                )?);
            }
            let iff = self.b.ap(
                "sqrtltd",
                &binds! {"ph" => scope, "A" => &small, "B" => &big},
                &[&held[0], &held[1], &held[2], &held[3]],
            );
            let rooted = |x: &Rpn| t!(x, "csqrt", "cfv");
            let roots = self.b.ap(
                "mpbid",
                &binds! {"ph" => scope, "ps" => t!(&small, &big, "clt", "wbr"),
                "ch" => t!(rooted(&small), rooted(&big), "clt", "wbr")},
                &[&ordered, &iff],
            );
            let end_real = self.numeral_fact(&t!(end, "cr", "wcel"), scope, facts)?;
            let end_above =
                self.numeral_fact(&t!("cc0", end, "cle", "wbr"), scope, facts)?;
            let unsquared = self.b.ap(
                "sqrtsqd",
                &binds! {"ph" => scope, "A" => end},
                &[&end_real, &end_above],
            );
            root_of_squares.push((roots, unsquared, rooted(&small), rooted(&big)));
        }
        let (roots, unsquared, root_low, _) = root_of_squares.remove(0);
        let below = self.b.ap(
            "eqbrtrrd",
            &binds! {"ph" => scope, "A" => &root_low, "B" => &low, "C" => &root, "R" => "clt"},
            &[&unsquared, &roots],
        );
        let (roots, unsquared, _, root_high) = root_of_squares.remove(0);
        let above = self.b.ap(
            "breqtrd",
            &binds! {"ph" => scope, "A" => &root, "B" => &root_high, "C" => &high, "R" => "clt"},
            &[&roots, &unsquared],
        );
        Ok(Bounded {
            said: root,
            low,
            high,
            below,
            above,
        })
    }

    /// 2 < e and e < 3, set.mm's `egt2lt3` taken apart.
    pub(super) fn e_bounds(&self, scope: &Rpn) -> [Proof; 2] {
        let halves = [t!("c2", "ceu", "clt", "wbr"), t!("ceu", "c3", "clt", "wbr")];
        [
            self.closed_half(halves.clone(), "egt2lt3", false, scope),
            self.closed_half(halves, "egt2lt3", true, scope),
        ]
    }

    /// ( scope -> one half ) of a theorem of set.mm stating `( left /\
    /// right )` with no hypothesis: the right where `right` is set, and the
    /// left otherwise (`simpri`, `simpli`).
    pub(super) fn closed_half(
        &self,
        [left, right]: [Rpn; 2],
        label: &str,
        take_right: bool,
        scope: &Rpn,
    ) -> Proof {
        let (rule, half) = if take_right {
            ("simpri", right.clone())
        } else {
            ("simpli", left.clone())
        };
        let taken = self.b.ap(
            rule,
            &binds! {"ph" => &left, "ps" => &right},
            &[&self.step(label)],
        );
        self.b
            .ap("a1i", &binds! {"ph" => &half, "ps" => scope}, &[&taken])
    }

    /// ln p between the ends of its bracket (`reals::ln_bracket`), a/b and
    /// a′/b′: eᵃ < 3ᵃ ≤ pᵇ and pᵇ′ ≤ 2ᵃ′ < eᵃ′ (`ltexp1dd`, and `arithmetic`),
    /// each carried under the logarithm (`logltb`), where ln(eᵃ) is a and
    /// ln(pᵇ) is b·ln p as the logarithm is worked out; and a < b·ln p is
    /// a/b < ln p (`ltdivmuld`), b′·ln p < a′ is ln p < a′/b′
    /// (`ltmuldiv2d`).
    pub(super) fn ln_bounded(
        &mut self,
        p: u64,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Bounded>> {
        let surds::Bracket { below, above } = reals::ln_bracket(p);
        let said = spelt_atom(Atom::Ln(p));
        let [two_below_e, e_below_three] = self.e_bounds(scope);
        let spell = |n: &BigInt| numerals::spell(n.magnitude().clone());
        let prime = numerals::spell(p);
        let power = |x: &Rpn, n: &Rpn| t!(x, n, "cexp", "co");
        let e_rp = self.closed_law(&t!("ceu", "crp", "wcel"), "epr", scope);

        // a < b·ln p, from eᵃ < 3ᵃ ≤ pᵇ.
        let (a, b) = (spell(below.numer()), spell(below.denom()));
        let (e_a, three_a, p_b) = (
            power(&t!("ceu"), &a),
            power(&t!("c3"), &a),
            power(&prime, &b),
        );
        let a_nn = self.numeral_fact(&t!(&a, "cn", "wcel"), scope, facts)?;
        let three_rp = self.positive(&t!("c3"), scope, facts)?;
        let first = self.b.ap(
            "ltexp1dd",
            &binds! {"ph" => scope, "A" => "ceu", "B" => "c3", "N" => &a},
            &[&e_rp, &three_rp, &a_nn, &e_below_three],
        );
        let second =
            self.numeral_fact(&t!(&three_a, &p_b, "cle", "wbr"), scope, facts)?;
        let mut held = Vec::new();
        for x in [&e_a, &three_a, &p_b] {
            held.push(self.membership(x, "cr", scope, facts)?);
        }
        let chained = self.b.ap(
            transitivity("clt", "cle"),
            &binds! {"ph" => scope, "A" => &e_a, "B" => &three_a, "C" => &p_b},
            &[&held[0], &held[1], &held[2], &first, &second],
        );
        let a_z = self.numeral_fact(&t!(&a, "cz", "wcel"), scope, facts)?;
        let e_a_rp = self.b.ap(
            "rpexpcld",
            &binds! {"ph" => scope, "A" => "ceu", "N" => &a},
            &[&e_rp, &a_z],
        );
        let p_b_rp = self.positive(&p_b, scope, facts)?;
        let low_side = take!(self.logged_order(
            [&e_a, &p_b],
            [e_a_rp, p_b_rp],
            chained,
            scope,
            facts
        )?);
        let ln_real = self.membership(&said, "cr", scope, facts)?;
        let a_real = self.numeral_fact(&t!(&a, "cr", "wcel"), scope, facts)?;
        let b_rp = self.positive(&b, scope, facts)?;
        let low = t!(&a, &b, "cdiv", "co");
        let iff = self.b.ap(
            "ltdivmuld",
            &binds! {"ph" => scope, "A" => &a, "B" => &said, "C" => &b},
            &[&a_real, &ln_real, &b_rp],
        );
        let lower = self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => t!(&low, &said, "clt", "wbr"),
            "ch" => t!(&a, t!(&b, &said, "cmul", "co"), "clt", "wbr")},
            &[&low_side, &iff],
        );

        // b′·ln p < a′, from pᵇ′ ≤ 2ᵃ′ < eᵃ′.
        let (a, b) = (spell(above.numer()), spell(above.denom()));
        let (p_b, two_a, e_a) = (
            power(&prime, &b),
            power(&t!("c2"), &a),
            power(&t!("ceu"), &a),
        );
        let a_nn = self.numeral_fact(&t!(&a, "cn", "wcel"), scope, facts)?;
        let two_rp = self.positive(&t!("c2"), scope, facts)?;
        let first = self.numeral_fact(&t!(&p_b, &two_a, "cle", "wbr"), scope, facts)?;
        let second = self.b.ap(
            "ltexp1dd",
            &binds! {"ph" => scope, "A" => "c2", "B" => "ceu", "N" => &a},
            &[&two_rp, &e_rp, &a_nn, &two_below_e],
        );
        let mut held = Vec::new();
        for x in [&p_b, &two_a, &e_a] {
            held.push(self.membership(x, "cr", scope, facts)?);
        }
        let chained = self.b.ap(
            transitivity("cle", "clt"),
            &binds! {"ph" => scope, "A" => &p_b, "B" => &two_a, "C" => &e_a},
            &[&held[0], &held[1], &held[2], &first, &second],
        );
        let a_z = self.numeral_fact(&t!(&a, "cz", "wcel"), scope, facts)?;
        let e_a_rp = self.b.ap(
            "rpexpcld",
            &binds! {"ph" => scope, "A" => "ceu", "N" => &a},
            &[&e_rp, &a_z],
        );
        let p_b_rp = self.positive(&p_b, scope, facts)?;
        let high_side = take!(self.logged_order(
            [&p_b, &e_a],
            [p_b_rp, e_a_rp],
            chained,
            scope,
            facts
        )?);
        let a_real = self.numeral_fact(&t!(&a, "cr", "wcel"), scope, facts)?;
        let b_rp = self.positive(&b, scope, facts)?;
        let high = t!(&a, &b, "cdiv", "co");
        let iff = self.b.ap(
            "ltmuldiv2d",
            &binds! {"ph" => scope, "A" => &said, "B" => &a, "C" => &b},
            &[&ln_real, &a_real, &b_rp],
        );
        let upper = self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(t!(&b, &said, "cmul", "co"), &a, "clt", "wbr"),
            "ch" => t!(&said, &high, "clt", "wbr")},
            &[&high_side, &iff],
        );
        Ok(Built(Bounded {
            said,
            low,
            high,
            below: lower,
            above: upper,
        }))
    }

    /// ( scope -> canon(ln x) < canon(ln y) ) from ( scope -> x < y ), x and
    /// y in ℝ⁺ as `positive` says: `logltb` carries the order under the
    /// logarithm, and each logarithm is worked to its canon.
    pub(super) fn logged_order(
        &mut self,
        [x, y]: [&Rpn; 2],
        positive: [Proof; 2],
        x_below_y: Proof,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let logged = |z: &Rpn| t!(z, "clog", "cfv");
        let law = self.b.ap("logltb", &binds! {"A" => x, "B" => y}, &[]);
        let iff = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(x, "crp", "wcel"), "ch" => t!(y, "crp", "wcel"),
            "th" => t!(t!(x, y, "clt", "wbr"), t!(logged(x), logged(y), "clt", "wbr"), "wb")},
            &[&positive[0], &positive[1], &law],
        );
        let carried = self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(x, y, "clt", "wbr"), "ch" => t!(logged(x), logged(y), "clt", "wbr")},
            &[&x_below_y, &iff],
        );
        let left = take!(self.valued(&self.to_term(&logged(x)), scope, facts)?);
        let right = take!(self.valued(&self.to_term(&logged(y)), scope, facts)?);
        let moved = self.b.ap(
            "eqbrtrrd",
            &binds! {"ph" => scope, "A" => logged(x), "B" => &left.canon, "C" => logged(y), "R" => "clt"},
            &[&left.proof, &carried],
        );
        Ok(Built(self.b.ap(
            "breqtrd",
            &binds! {"ph" => scope, "A" => &left.canon, "B" => logged(y), "C" => &right.canon, "R" => "clt"},
            &[&moved, &right.proof],
        )))
    }
}
