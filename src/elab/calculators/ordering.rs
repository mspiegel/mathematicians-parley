//! Fractions and inequalities.

use std::mem;

use super::*;

impl<'a> Elaborator<'a> {
    /// A side as a fraction of two numerals, the second not zero, with
    /// |- side = ( over / under ): a quotient has each part worked
    /// (`numerals::worked`), and a whole number w is w/1 (`div1i`).
    pub(super) fn as_fraction(&self, side: &Term) -> Option<(BigUint, BigUint, Proof)> {
        let labels = self.b.flabel.clone();
        let kids = side.children();
        if side.variable().is_none()
            && side.label() == Some("co")
            && kids.len() == 3
            && kids[2].label() == Some("cdiv")
        {
            let (over, over_is) = numerals::worked(&self.b, &kids[0], &labels)?;
            let (under, under_is) = numerals::worked(&self.b, &kids[1], &labels)?;
            if under.is_zero() {
                return None;
            }
            let proof = self.b.ap(
                "oveq12i",
                &binds! {
                    "A" => self.rpn(&kids[0]), "B" => numerals::spell(over.clone()),
                    "C" => self.rpn(&kids[1]), "D" => numerals::spell(under.clone()),
                    "F" => "cdiv",
                },
                &[&over_is, &under_is],
            );
            return Some((over, under, proof));
        }
        let (whole, whole_is) = numerals::worked(&self.b, side, &labels)?;
        let sw = numerals::spell(whole.clone());
        let over_one = t!(&sw, n(1), "cdiv", "co");
        let one = self.b.ap(
            "div1i",
            &binds! {"A" => &sw},
            &[&numerals::cc(&self.b, whole.clone())],
        );
        let back = self
            .b
            .ap("eqcomi", &binds! {"A" => &over_one, "B" => &sw}, &[&one]);
        let proof = self.b.ap(
            "eqtri",
            &binds! {"A" => self.rpn(side), "B" => &sw, "C" => &over_one},
            &[&whole_is, &back],
        );
        Some((whole, BigUint::from(1u32), proof))
    }

    /// |- first R second, R being < or ≤, where the sides are fractions of
    /// whole numbers: A/D < C/B is A·B < C·D for positive B and D
    /// (`lt2mul2div`), and A/D ≤ C/B is that C/B < A/D does not hold
    /// (`lenlt`). None where a side is no such fraction or the order is not
    /// what the numbers do.
    pub(super) fn fractions_ordered(
        &self,
        goal: &Term,
        first: &Term,
        second: &Term,
        how: &str,
    ) -> Option<Proof> {
        let (a, d, first_is) = self.as_fraction(first)?;
        let (c, b, second_is) = self.as_fraction(second)?;
        let sp = |v: &BigUint| numerals::spell(v.clone());
        let (sa, sb, sc, sd) = (sp(&a), sp(&b), sp(&c), sp(&d));
        let (p, q) = (&a * &b, &c * &d);
        let (ab, cd) = (t!(&sa, &sb, "cmul", "co"), t!(&sc, &sd, "cmul", "co"));
        let (ad, cb) = (t!(&sa, &sd, "cdiv", "co"), t!(&sc, &sb, "cdiv", "co"));
        let (ab_is, cd_is) = (
            numerals::product(&self.b, a.clone(), b.clone()),
            numerals::product(&self.b, c.clone(), d.clone()),
        );
        let real = |v: &BigUint| numerals::re(&self.b, v.clone());
        let and = |x: &Rpn, y: &Rpn, px: &Proof, py: &Proof| {
            self.b
                .ap("pm3.2i", &binds! {"ph" => x, "ps" => y}, &[px, py])
        };
        // ( x e. RR /\ ( y e. RR /\ 0 < y ) ), y positive.
        let held = |x: &BigUint, y: &BigUint| {
            let (sx, sy) = (sp(x), sp(y));
            let positive =
                t!(t!(&sy, "cr", "wcel"), t!("cc0", &sy, "clt", "wbr"), "wa");
            let inner = and(
                &t!(&sy, "cr", "wcel"),
                &t!("cc0", &sy, "clt", "wbr"),
                &real(y),
                &numerals::pos(&self.b, y.clone()),
            );
            (
                t!(t!(&sx, "cr", "wcel"), &positive, "wa"),
                and(&t!(&sx, "cr", "wcel"), &positive, &real(x), &inner),
            )
        };
        // ( ( A x. B ) < ( C x. D ) <-> ( A / D ) < ( C / B ) ), and the
        // same with the two fractions exchanged.
        let crossed = |x: &BigUint, y: &BigUint, z: &BigUint, w: &BigUint| {
            let (left, left_held) = held(x, y);
            let (right, right_held) = held(z, w);
            let both = and(&left, &right, &left_held, &right_held);
            let law = self.b.ap(
                "lt2mul2div",
                &binds! {"A" => sp(x), "B" => sp(y), "C" => sp(z), "D" => sp(w)},
                &[],
            );
            let lt = |l: Rpn, r: Rpn| t!(l, r, "clt", "wbr");
            self.b.ap(
                "ax-mp",
                &binds! {
                    "ph" => t!(&left, &right, "wa"),
                    "ps" => t!(
                        lt(t!(sp(x), sp(y), "cmul", "co"), t!(sp(z), sp(w), "cmul", "co")),
                        lt(t!(sp(x), sp(w), "cdiv", "co"), t!(sp(z), sp(y), "cdiv", "co")),
                        "wb"
                    ),
                },
                &[&both, &law],
            )
        };
        let (sp_, sq) = (sp(&p), sp(&q));
        let relation = if how == "<" { "clt" } else { "cle" };
        let between = if how == "<" {
            if p >= q {
                return None;
            }
            // A·B < C·D, from the numerals they come to.
            let valued = self.b.ap(
                "breq12i",
                &binds! {"A" => &ab, "B" => &sp_, "C" => &cd, "D" => &sq, "R" => "clt"},
                &[&ab_is, &cd_is],
            );
            let products = self.b.ap(
                "mpbir",
                &binds! {"ph" => t!(&ab, &cd, "clt", "wbr"), "ps" => t!(&sp_, &sq, "clt", "wbr")},
                &[&numerals::below(&self.b, p.clone(), q.clone()), &valued],
            );
            self.b.ap(
                "mpbi",
                &binds! {"ph" => t!(&ab, &cd, "clt", "wbr"), "ps" => t!(&ad, &cb, "clt", "wbr")},
                &[&products, &crossed(&a, &b, &c, &d)],
            )
        } else {
            if p > q {
                return None;
            }
            // not C·D < A·B, from the numerals: P ≤ Q is not Q < P.
            let at_most = if p == q {
                self.b.ap("leidi", &binds! {"A" => &sp_}, &[&real(&p)])
            } else {
                let law = self.b.ap(
                    "ltlei",
                    &binds! {"A" => &sp_, "B" => &sq},
                    &[&real(&p), &real(&q)],
                );
                self.b.ap(
                    "ax-mp",
                    &binds! {"ph" => t!(&sp_, &sq, "clt", "wbr"), "ps" => t!(&sp_, &sq, "cle", "wbr")},
                    &[&numerals::below(&self.b, p.clone(), q.clone()), &law],
                )
            };
            let not_less = |x: &Rpn, y: &Rpn| t!(t!(y, x, "clt", "wbr"), "wn");
            let reals = |x: &Rpn, y: &Rpn, px: &Proof, py: &Proof| {
                and(&t!(x, "cr", "wcel"), &t!(y, "cr", "wcel"), px, py)
            };
            // ( x <_ y <-> -. y < x ), for x and y real.
            let lenlt = |x: &Rpn, y: &Rpn, px: &Proof, py: &Proof| {
                self.b.ap(
                    "ax-mp",
                    &binds! {
                        "ph" => t!(t!(x, "cr", "wcel"), t!(y, "cr", "wcel"), "wa"),
                        "ps" => t!(t!(x, y, "cle", "wbr"), not_less(x, y), "wb"),
                    },
                    &[
                        &reals(x, y, px, py),
                        &self.b.ap("lenlt", &binds! {"A" => x, "B" => y}, &[]),
                    ],
                )
            };
            let numerals_not = self.b.ap(
                "mpbi",
                &binds! {"ph" => t!(&sp_, &sq, "cle", "wbr"), "ps" => not_less(&sp_, &sq)},
                &[&at_most, &lenlt(&sp_, &sq, &real(&p), &real(&q))],
            );
            let valued = self.b.ap(
                "breq12i",
                &binds! {"A" => &cd, "B" => &sq, "C" => &ab, "D" => &sp_, "R" => "clt"},
                &[&cd_is, &ab_is],
            );
            let valued = self.b.ap(
                "notbii",
                &binds! {"ph" => t!(&cd, &ab, "clt", "wbr"), "ps" => t!(&sq, &sp_, "clt", "wbr")},
                &[&valued],
            );
            let products_not = self.b.ap(
                "mpbir",
                &binds! {"ph" => t!(t!(&cd, &ab, "clt", "wbr"), "wn"), "ps" => not_less(&sp_, &sq)},
                &[&numerals_not, &valued],
            );
            let exchanged = self.b.ap(
                "notbii",
                &binds! {"ph" => t!(&cd, &ab, "clt", "wbr"), "ps" => t!(&cb, &ad, "clt", "wbr")},
                &[&crossed(&c, &d, &a, &b)],
            );
            let fractions_not = self.b.ap(
                "mpbi",
                &binds! {"ph" => t!(t!(&cd, &ab, "clt", "wbr"), "wn"), "ps" => not_less(&ad, &cb)},
                &[&products_not, &exchanged],
            );
            let real_fraction = |x: &BigUint, y: &BigUint| {
                self.b.ap(
                    "redivcli",
                    &binds! {"A" => sp(x), "B" => sp(y)},
                    &[&real(x), &real(y), &numerals::ne0(&self.b, y.clone())],
                )
            };
            self.b.ap(
                "mpbir",
                &binds! {"ph" => t!(&ad, &cb, "cle", "wbr"), "ps" => not_less(&ad, &cb)},
                &[
                    &fractions_not,
                    &lenlt(&ad, &cb, &real_fraction(&a, &d), &real_fraction(&c, &b)),
                ],
            )
        };
        let back = self.b.ap(
            "breq12i",
            &binds! {"A" => self.rpn(first), "B" => &ad, "C" => self.rpn(second), "D" => &cb, "R" => relation},
            &[&first_is, &second_is],
        );
        Some(self.b.ap(
            "mpbir",
            &binds! {"ph" => self.rpn(goal), "ps" => t!(&ad, &cb, relation, "wbr")},
            &[&between, &back],
        ))
    }

    /// An order between sums, products and whole powers of whole numbers:
    /// each side is worked to its numeral (`numerals::worked`), the order
    /// between the two numerals is proved, and `breq12i` carries it back to
    /// the sides as written.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn order_by_values(
        &mut self,
        goal: &Term,
        first: &Term,
        second: &Term,
        how: &str,
        negated: bool,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let divides = |side: &Term| {
            side.variable().is_none()
                && side.label() == Some("co")
                && side.children().len() == 3
                && side.children()[2].label() == Some("cdiv")
        };
        // Below 0, or a denial between fractions: the routes after this work
        // with whole numbers of at least 0 and fractions of them, in order.
        let below_zero = |side: &Term| matches!(field::closed_value(side), Built(Value::Exact(v)) if v.is_negative());
        if below_zero(first)
            || below_zero(second)
            || (negated && (divides(first) || divides(second)))
        {
            return self.order_by_difference(first, second, how, negated, scope, facts);
        }
        if divides(first) || divides(second) {
            return Ok(match self.fractions_ordered(goal, first, second, how) {
                Some(closed) => Built(self.b.ap(
                    "a1i",
                    &binds! {"ph" => self.rpn(goal), "ps" => scope},
                    &[&closed],
                )),
                None => Route::no(
                    "the two sides are not fractions of whole numbers in that order",
                ),
            });
        }
        let (Some((a, a_is)), Some((b, b_is))) = (
            numerals::worked(&self.b, first, &labels),
            numerals::worked(&self.b, second, &labels),
        ) else {
            return Ok(Route::no(
                "a side is not a sum, product or whole power of whole numbers",
            ));
        };
        let relation = if how == "<" { "clt" } else { "cle" };
        let (na, nb) = (numerals::spell(a), numerals::spell(b));
        let said = self.rpn(goal);
        let valued = t!(&na, &nb, relation, "wbr");
        let mut turn = self.b.ap(
            "breq12i",
            &binds! {"A" => self.rpn(first), "B" => &na, "C" => self.rpn(second), "D" => &nb, "R" => relation},
            &[&a_is, &b_is],
        );
        let (said, valued) = if negated {
            turn =
                self.b
                    .ap("notbii", &binds! {"ph" => &said, "ps" => &valued}, &[&turn]);
            (t!(said, "wn"), t!(valued, "wn"))
        } else {
            (said, valued)
        };
        let held = take!(self.prove_numeral(&valued, scope, facts)?);
        Ok(Built(self.b.ap(
            "sylibr",
            &binds! {"ph" => scope, "ps" => &valued, "ch" => &said},
            &[&held, &turn],
        )))
    }

    /// ( scope -> -. first = second ) for closed terms of different values:
    /// the lower is below the higher (`order_by_difference`), so the two
    /// differ (`ltne`), turned to the order written (`necomd`, `neneqd`).
    pub(super) fn closed_apart(
        &mut self,
        first: &Term,
        second: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let (Built(Value::Exact(x)), Built(Value::Exact(y))) =
            (field::closed_value(first), field::closed_value(second))
        else {
            return Ok(Route::no("a side has no exact value"));
        };
        if x == y {
            return Ok(Route::no("the two sides are equal"));
        }
        if self.normaliser_opaque(first) || self.normaliser_opaque(second) {
            return Ok(Route::no(
                "a side holds what the normaliser does not work out, and is said by its value",
            ));
        }
        let first_lower = x < y;
        let (low, high) = if first_lower {
            (first, second)
        } else {
            (second, first)
        };
        let (sl, sh) = (self.rpn(low), self.rpn(high));
        let below =
            take!(self.order_by_difference(low, high, "<", false, scope, facts)?);
        let real = take!(self.prove_numeral(&t!(&sl, "cr", "wcel"), scope, facts)?);
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(&sl, "cr", "wcel"), "ch" => t!(&sl, &sh, "clt", "wbr")},
            &[&real, &below],
        );
        let law = self.b.ap("ltne", &binds! {"A" => &sl, "B" => &sh}, &[]);
        let mut apart = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(t!(&sl, "cr", "wcel"), t!(&sl, &sh, "clt", "wbr"), "wa"),
            "ch" => t!(&sh, &sl, "wne")},
            &[&both, &law],
        );
        let (sf, ss) = (self.rpn(first), self.rpn(second));
        if first_lower {
            apart = self.b.ap(
                "necomd",
                &binds! {"ph" => scope, "A" => &sh, "B" => &sl},
                &[&apart],
            );
        }
        Ok(Built(self.b.ap(
            "neneqd",
            &binds! {"ph" => scope, "A" => &sf, "B" => &ss},
            &[&apart],
        )))
    }

    /// An order between closed terms that are not whole numbers of at least
    /// 0, `−3 < 0` or `−1/2 ≤ 1/3`: the second less the first is worked out
    /// to its value, which is a numeral or a fraction of two, and its sign
    /// says the order (`posdif`, `subge0`). A denial is the order the other
    /// way, turned (`lenlt`, `ltnle`).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn order_by_difference(
        &mut self,
        first: &Term,
        second: &Term,
        how: &str,
        negated: bool,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let (Built(Value::Exact(x)), Built(Value::Exact(y))) =
            (field::closed_value(first), field::closed_value(second))
        else {
            return Ok(Route::no("a side has no exact value"));
        };
        if self.normaliser_opaque(first) || self.normaliser_opaque(second) {
            return Ok(Route::no(
                "a side holds what the normaliser does not work out, and is said by its value",
            ));
        }
        let (sf, ss) = (self.rpn(first), self.rpn(second));
        let real = |s: &Rpn| t!(s, "cr", "wcel");
        let first_real = take!(self.prove_numeral(&real(&sf), scope, facts)?);
        let second_real = take!(self.prove_numeral(&real(&ss), scope, facts)?);
        if negated {
            // not x < y is y ≤ x, and not x ≤ y is y < x.
            let (turned, law, relation) = if how == "<" {
                ("<=", "lenlt", "clt")
            } else {
                ("<", "ltnle", "cle")
            };
            let other = if turned == "<" { "clt" } else { "cle" };
            let held =
                take!(self
                    .order_by_difference(second, first, turned, false, scope, facts)?);
            let both = self.b.ap(
                "jca",
                &binds! {"ph" => scope, "ps" => real(&ss), "ch" => real(&sf)},
                &[&second_real, &first_real],
            );
            let said = t!(&sf, &ss, relation, "wbr");
            let valued = t!(&ss, &sf, other, "wbr");
            let iff = t!(&valued, t!(&said, "wn"), "wb");
            let law = self.b.ap(law, &binds! {"A" => &ss, "B" => &sf}, &[]);
            let iff = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => t!(real(&ss), real(&sf), "wa"), "ch" => &iff},
                &[&both, &law],
            );
            return Ok(Built(self.b.ap(
                "mpbid",
                &binds! {"ph" => scope, "ps" => &valued, "ch" => t!(&said, "wn")},
                &[&held, &iff],
            )));
        }
        let gap = &y - &x;
        if gap.is_negative() || (how == "<" && gap.is_zero()) {
            return Ok(Route::no(format!(
                "{x} {how} {y} is not what the numbers do"
            )));
        }
        let whole = |v: &BigInt| numerals::spell(v.to_biguint().unwrap_or_default());
        let value = if gap.is_integer() {
            whole(&gap.to_integer())
        } else {
            t!(whole(gap.numer()), whole(gap.denom()), DIV, "co")
        };
        let relation = if how == "<" { "clt" } else { "cle" };
        let difference = t!(&ss, &sf, SUB, "co");
        let equal = take!(self.prove_field(
            None,
            &t!(&difference, &value, "wceq"),
            scope,
            facts,
            &Lines::new()
        )?);
        let signed = take!(self.prove_numeral(
            &t!("cc0", &value, relation, "wbr"),
            scope,
            facts
        )?);
        let sign = self.b.ap(
            "breqtrrd",
            &binds! {"ph" => scope, "A" => "cc0", "R" => relation, "B" => &value, "C" => &difference},
            &[&signed, &equal],
        );
        let said = t!(&sf, &ss, relation, "wbr");
        let by_sign = t!("cc0", &difference, relation, "wbr");
        if how == "<" {
            let both = self.b.ap(
                "jca",
                &binds! {"ph" => scope, "ps" => real(&sf), "ch" => real(&ss)},
                &[&first_real, &second_real],
            );
            let law = self.b.ap("posdif", &binds! {"A" => &sf, "B" => &ss}, &[]);
            let iff = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => t!(real(&sf), real(&ss), "wa"), "ch" => t!(&said, &by_sign, "wb")},
                &[&both, &law],
            );
            return Ok(Built(self.b.ap(
                "mpbird",
                &binds! {"ph" => scope, "ps" => &said, "ch" => &by_sign},
                &[&sign, &iff],
            )));
        }
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => real(&ss), "ch" => real(&sf)},
            &[&second_real, &first_real],
        );
        let law = self.b.ap("subge0", &binds! {"A" => &ss, "B" => &sf}, &[]);
        let iff = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(real(&ss), real(&sf), "wa"), "ch" => t!(&by_sign, &said, "wb")},
            &[&both, &law],
        );
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => &by_sign, "ch" => &said},
            &[&sign, &iff],
        )))
    }

    /// ( scope -> -. y <_ x ) from ( scope -> x < y ), where `strict`, and
    /// ( scope -> -. y < x ) from ( scope -> x <_ y ) otherwise: an order
    /// turned round is the denial of the other (`ltnled`, `lenltd`).
    pub(in crate::elab) fn denied(
        &self,
        scope: &Rpn,
        x: &Rpn,
        y: &Rpn,
        held: &Ordered,
        strict: bool,
    ) -> Proof {
        let (relation, other, law) = if strict {
            ("clt", "cle", "ltnled")
        } else {
            ("cle", "clt", "lenltd")
        };
        let said = t!(x, y, relation, "wbr");
        let denial = t!(t!(y, x, other, "wbr"), "wn");
        let turned = self.b.ap(
            law,
            &binds! {"ph" => scope, "A" => x, "B" => y},
            &[&held.left_real, &held.right_real],
        );
        pf!(self.b; scope, said, denial, held.proof.clone(), turned, "mpbid")
    }

    /// An order of two numerals, with each side real (`real_numeral`).
    pub(super) fn numerals_ordered(
        &self,
        scope: &Rpn,
        x: &Rpn,
        y: &Rpn,
        proof: Proof,
    ) -> Ordered {
        let real = |n: &Rpn| {
            let value =
                linear::numeral(&self.to_term(n), &self.b.flabel).unwrap_or_default();
            self.real_numeral(scope, &value)
        };
        Ordered {
            proof,
            left_real: real(x),
            right_real: real(y),
        }
    }

    /// ( scope -> n e. RR ) for a whole multiplier.
    pub(super) fn real_numeral(&self, scope: &Rpn, times: &Q) -> Proof {
        let whole = times.numer().magnitude().clone();
        let nw = numerals::spell(whole.clone());
        let held = self.b.ap(
            "a1i",
            &binds! {"ph" => t!(nw, "cr", "wcel"), "ps" => scope},
            &[&numerals::re(&self.b, whole)],
        );
        if !times.numer().is_negative() {
            return held;
        }
        self.b
            .ap("renegcld", &binds! {"ph" => scope, "A" => nw}, &[&held])
    }

    /// ( scope -> a < b ), for whole numbers a below b (`numerals::below`).
    pub(super) fn numeral_below(&self, scope: &Rpn, a: &BigUint, b: &BigUint) -> Proof {
        self.b.ap(
            "a1i",
            &binds! {"ph" => t!(numerals::spell(a.clone()), numerals::spell(b.clone()), "clt", "wbr"), "ps" => scope},
            &[&numerals::below(&self.b, a.clone(), b.clone())],
        )
    }

    /// ( scope -> -. a = b ), from whichever of the two is below.
    pub(super) fn numerals_differ(
        &self,
        scope: &Rpn,
        a: &BigUint,
        b: &BigUint,
    ) -> Proof {
        let (low, high) = if a < b { (a, b) } else { (b, a) };
        let (nl, nh) = (numerals::spell(low.clone()), numerals::spell(high.clone()));
        let (nl, nh) = (&nl, &nh);
        let real = self.real_numeral(scope, &Q::from_integer(low.clone().into()));
        let below = self.numeral_below(scope, low, high);
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(nl, "cr", "wcel"), "ch" => t!(nl, nh, "clt", "wbr")},
            &[&real, &below],
        );
        let law = self.b.ap("ltne", &binds! {"A" => nl, "B" => nh}, &[]);
        let apart = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(t!(nl, "cr", "wcel"), t!(nl, nh, "clt", "wbr"), "wa"),
            "ch" => t!(nh, nl, "wne")},
            &[&both, &law],
        );
        let (na, nb) = (numerals::spell(a.clone()), numerals::spell(b.clone()));
        if a != low {
            return self.b.ap(
                "neneqd",
                &binds! {"ph" => scope, "A" => na, "B" => nb},
                &[&apart],
            );
        }
        let turned = self.b.ap(
            "necomd",
            &binds! {"ph" => scope, "A" => nh, "B" => nl},
            &[&apart],
        );
        self.b.ap(
            "neneqd",
            &binds! {"ph" => scope, "A" => na, "B" => nb},
            &[&turned],
        )
    }

    /// Decided by `linear`, and then taken where it cannot be emitted: what
    /// the method concludes is checked against what the step cites, so a
    /// step that does not follow is refused rather than assumed.
    ///
    /// A claim that writes an identity element is the claim without it
    /// (`SYNTAX.md`, "An identity element goes without saying"), and is
    /// proved so where the claim as written is not: `x^1` is an atom to the
    /// method that `x` is not, so the base case `P ≤ (S/1)^1` of an
    /// induction is the claim `P ≤ S` its rows end on, carried back.
    pub fn inequalities(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let found = self.inequalities_as_written(step, term, scope, facts, lines)?;
        let Declined(d) = &found else {
            return Ok(found);
        };
        let bare = self.rpn(&self.without_identities(&self.to_term(term)));
        if bare != *term {
            let tidy =
                self.inequalities_as_written(step, &bare, scope, facts, lines)?;
            if let Built(p) = tidy {
                if let Some(back) = self.tidied(&p, &bare, term, scope, facts)? {
                    return Ok(Built(back));
                }
            }
        }
        Err(self.defect(
            step.line,
            format!(
                "step {} follows from what it cites, and inequalities cannot write its proof: {}",
                step.number,
                self.say(d)
            ),
        ))
    }

    /// `inequalities` of the claim as `term` writes it; declined where the
    /// method cannot write its proof.
    pub(super) fn inequalities_as_written(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if let Some(proof) = self.weakened_line(step, term, scope, facts, lines)? {
            return Ok(Built(proof));
        }
        // A defined name is read as what it names, as `membership` and the
        // comparison of two spellings read it: the claim and each cited line
        // are taken with their defined names written out.
        let out = take!(self.names_written_out(
            Some(step),
            &step.just.refs,
            term,
            scope,
            facts,
            lines
        )?);
        let (term_out, lines_out) = (&out.term, &out.lines.copy());
        // A step said of every member has the membership its claim's "for
        // all" gives the member as a cited line (`SYNTAX.md`), with what it
        // implies, `i ≥ 1` of i ∈ ℕ, as the checker reads it. The step's own
        // claim says it, so it is cited under the step's number, which names
        // no line while the step is proved.
        let mut refs = step.just.refs.clone();
        if let Some(member) = self.member.clone() {
            if let Some(proof) = self.held(facts, &member, scope)? {
                let line = Line::new(member, proof, Vec::new());
                let own = step.number.to_string();
                lines_out.set(own.clone(), line);
                refs.push(own);
            }
        }
        // A cited line says each of its parts, a membership among them, as
        // the checker and R3 read it (`READERS.md`, what a membership says).
        // Only what the step may rest on is offered, so that a bound the
        // cited lines give is proved from them and not taken from a line in
        // scope that says the same, which the step does not name.
        let cited = self.with_cited(Some(step), scope, &out.facts, None)?;
        let facts_out = &cited;
        // A plain step adds its facts as they stand, the combination the
        // checker decided it by; a step with rows, a chain and an order
        // with its converse are proved from their lines in one, by any.
        let plain =
            step.just.head.is(Method::Inequalities) && step.just.rows.is_empty();
        // The method wants every atom in ℝ, and a `requires` line is where
        // the step writes that; offered to the membership lookup and to
        // nothing else.
        let known = self.supplied(Some(step), scope, facts)?;
        let kept = mem::replace(&mut self.adding_only, plain);
        let found = self.writing(scope, &known, false, |me| {
            let rewritten = me.algebra_rows(step, refs, scope, facts_out, lines_out)?;
            let skip = if plain {
                me.not_combined(step, &rewritten.refs, lines, &rewritten.lines)?
            } else {
                Vec::new()
            };
            me.prove_order(
                &rewritten.refs,
                term_out,
                scope,
                facts_out,
                &rewritten.lines,
                &skip,
            )
        });
        self.adding_only = kept;
        let found = found?;
        if found.is_declined() || term_out == term {
            return Ok(found);
        }
        // Back from the claim written out to the claim as the page writes it.
        let proof = take!(found);
        let (said, want) = (self.to_term(term_out), self.to_term(term));
        let Built(back) = self.same(&said, &want, scope, facts, Some(step))? else {
            return Ok(Route::no("the claim written out is not carried back"));
        };
        Ok(Built(
            pf!(self.b; scope, term_out, term, proof, back, "mpbid"),
        ))
    }

    /// `a ≤ b` from a line the step cites saying `a < b` of the same two
    /// terms, by `ltled`; None where no cited line does. The terms are not
    /// taken apart, so each needs only what the step's lines say of it
    /// whole: the area of a triangle is a number by `area-real`, though
    /// nothing says the size of the sine inside it is.
    pub(super) fn weakened_line(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Option<Proof>> {
        let claim = self.to_term(term);
        let kids = claim.children();
        if claim.variable().is_some()
            || claim.label() != Some("wbr")
            || kids.len() != 3
            || self.rpn(&kids[2]) != t!("cle")
        {
            return Ok(None);
        }
        let (a, b) = (self.rpn(&kids[0]), self.rpn(&kids[1]));
        let strict = t!(&a, &b, "clt", "wbr");
        for r in &step.just.refs {
            if !self.line_writes(r, lines).contains(&strict) {
                continue;
            }
            let node = self.to_term(&strict);
            let Built(given) = self.cited_fact(r, &node, scope, facts, lines)? else {
                continue;
            };
            let ra = self.membership(&a, "cr", scope, facts)?;
            let rb = self.membership(&b, "cr", scope, facts)?;
            return Ok(Some(self.b.ap(
                "ltled",
                &binds! {"ph" => scope, "A" => &a, "B" => &b},
                &[&ra, &rb, &given],
            )));
        }
        Ok(None)
    }
}
