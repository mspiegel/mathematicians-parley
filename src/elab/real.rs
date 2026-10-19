//! `real arithmetic`: closed facts about square roots of rationals, proved.
//!
//! The deciding is `crate::methods::surds`, and a claim is worked out
//! before anything is proved, so what cannot be proved is reported as what
//! it is. A proof takes each term to the **canon** of its value: the value
//! written as a sum of rational multiples of products of roots of primes,
//! rational part first, then by the product under the root, so that two
//! terms of one value come to one spelling (`canon`). A root of a rational
//! is its square part times a product of roots of primes (`root_piece`); an
//! operation is carried through to the canons of its operands, and what
//! that writes is brought to the canon of the result.
//!
//! Two expressions in roots of primes with one value differ by a sum of
//! multiples of (√p)² − p, one for each prime (`identity`); the decider
//! works out the multiples, and the normaliser checks that the sum is the
//! difference. A value not zero is shown by its cofactor, which multiplies
//! it to a rational not zero (`surd_apart`); that is what a division and a
//! disequality rest on. A power is built a step at a time, each step
//! brought to its canon, so that it never expands whole.

use indexmap::IndexMap;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::calculators::Work;
use super::field::{self, numeral, Monomial, Poly, Q};
use super::numerals;
use super::state::Elaborator;
use super::Facts;
use crate::binds;
use crate::corpus::{fmt, Step};
use crate::methods::surds::{self, Surd, Value, Verdict};
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::mm::Rpn;
use crate::outcome::{Built, Checked, Declined, Problem, Route};
use crate::{t, take};

/// A term proved equal to the canon of its value: ( scope -> term = canon ).
struct Valued {
    value: Surd,
    canon: Rpn,
    proof: Proof,
}

/// The multiple of (√p)² − p that a difference holds, for one prime.
struct Multiplier {
    /// √p, as set.mm spells it.
    root: Rpn,
    prime: u64,
    times: Poly,
}

impl<'a> Elaborator<'a> {
    /// A step citing `real arithmetic`.
    pub fn real_arithmetic(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let what = format!("step {} claims {}", fmt(&step.number), step.claim.text());
        self.real_fact(term, scope, facts, &what).map(Built)
    }

    /// A closed fact about square roots of rationals, worked out and then
    /// proved; `what` says where it was asked, as the page writes it.
    pub fn real_fact(
        &mut self,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        what: &str,
    ) -> Checked<Proof> {
        let goal = self.to_term(term);
        match surds::decide_closed(&goal) {
            Built(Verdict::Holds(true)) => {}
            other => return Err(self.real_unshown(other, what)),
        }
        let known = self.roots_known(&goal, scope, facts)?;
        match self.real_proved(&goal, scope, &known)? {
            Built(p) => Ok(p),
            Declined(d) => Err(self.defect(
                self.at,
                format!(
                    "{what}, which is true, and real arithmetic cannot show it yet: {}; cite a theorem that states it",
                    d.reason()
                ),
            )),
        }
    }

    /// The defect for a claim real arithmetic did not find true.
    fn real_unshown(&self, verdict: Route<Verdict>, what: &str) -> Problem {
        let message = match verdict {
            Declined(_) => format!(
                "{what}, which is not a fact about numerals and square roots alone, and real arithmetic decides nothing else"
            ),
            Built(Verdict::Holds(false)) => format!("{what}, which is false"),
            Built(Verdict::Unworked(why)) => format!("{what}, which {why}"),
            Built(Verdict::Undecided(why)) => {
                format!("{what}, which {why}; real arithmetic does not decide it")
            }
            Built(Verdict::Holds(true)) => unreachable!("a true claim is proved"),
        };
        self.defect(self.at, message)
    }

    /// The facts, with √p ∈ ℂ and √p ∈ ℝ for each prime p under a root of
    /// the claim: what the normaliser and a membership ask of each root.
    fn roots_known(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Facts> {
        let known = facts.copy();
        for p in primes_under(goal) {
            let prime = numerals::spell(p);
            let root = root_of_prime(p);
            let complex = self.numeral_fact(&t!(&prime, "cc", "wcel"), scope, facts)?;
            let in_cc = self.b.ap(
                "sqrtcld",
                &binds! {"ph" => scope, "A" => &prime},
                &[&complex],
            );
            self.know(&known, t!(&root, "cc", "wcel"), in_cc);
            let real = self.numeral_fact(&t!(&prime, "cr", "wcel"), scope, facts)?;
            let above =
                self.numeral_fact(&t!("cc0", &prime, "cle", "wbr"), scope, facts)?;
            let in_r = self.b.ap(
                "resqrtcld",
                &binds! {"ph" => scope, "A" => &prime},
                &[&real, &above],
            );
            self.know(&known, t!(&root, "cr", "wcel"), in_r);
        }
        Ok(known)
    }

    /// ( scope -> √x e. system ) for a root `real arithmetic` takes, in ℝ
    /// or ℂ: its membership said once (`READERS.md`). x is a rational of at
    /// least 0, which `arithmetic` says, and its root is real (`resqrtcld`),
    /// or complex (`sqrtcld`).
    pub(super) fn root_within(
        &mut self,
        root: &Term,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let x = self.rpn(&root.children()[0]);
        match system.alone() {
            Some("cr") => {
                let real = self.numeral_fact(&t!(&x, "cr", "wcel"), scope, facts)?;
                let above =
                    self.numeral_fact(&t!("cc0", &x, "cle", "wbr"), scope, facts)?;
                Ok(Built(self.b.ap(
                    "resqrtcld",
                    &binds! {"ph" => scope, "A" => &x},
                    &[&real, &above],
                )))
            }
            Some("cc") => {
                let complex = self.numeral_fact(&t!(&x, "cc", "wcel"), scope, facts)?;
                Ok(Built(self.b.ap(
                    "sqrtcld",
                    &binds! {"ph" => scope, "A" => &x},
                    &[&complex],
                )))
            }
            _ => Ok(Route::no("a root is said once only in ℝ and ℂ")),
        }
    }

    /// A fact about numerals alone, which arithmetic proves.
    fn numeral_fact(
        &mut self,
        claim: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let what = format!("real arithmetic asks {}", self.render(claim));
        self.closed_fact(claim, scope, facts, &what, None)
    }

    /// ( scope -> goal ) for a closed claim real arithmetic found true.
    fn real_proved(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let negated = goal.label() == Some("wn") && goal.children().len() == 1;
        let inner = if negated { &goal.children()[0] } else { goal };
        let kids = inner.children().to_vec();
        match (negated, inner.label(), kids.as_slice()) {
            (false, Some("wceq"), [a, b]) => {
                let left = take!(self.valued(a, scope, facts)?);
                let right = take!(self.valued(b, scope, facts)?);
                Ok(Built(self.b.ap(
                    "eqtr4d",
                    &binds! {"ph" => scope, "A" => self.rpn(a), "B" => &left.canon, "C" => self.rpn(b)},
                    &[&left.proof, &right.proof],
                )))
            }
            (false, Some("wne"), [a, b]) => self.real_apart(a, b, scope, facts),
            (true, Some("wceq"), [a, b]) => {
                let apart = take!(self.real_apart(a, b, scope, facts)?);
                Ok(Built(self.b.ap(
                    "neneqd",
                    &binds! {"ph" => scope, "A" => self.rpn(a), "B" => self.rpn(b)},
                    &[&apart],
                )))
            }
            _ => self.by_surd_values(goal, scope, facts),
        }
    }

    /// ( scope -> a =/= b ) for closed a and b of different values: a − b
    /// is the canon of the difference, which is not zero (`surd_apart`), and
    /// `subne0ad` turns that round.
    fn real_apart(
        &mut self,
        a: &Term,
        b: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let left = take!(self.valued(a, scope, facts)?);
        let right = take!(self.valued(b, scope, facts)?);
        let (sa, sb) = (self.rpn(a), self.rpn(b));
        let moved = self.b.ap(
            "oveq12d",
            &binds! {"ph" => scope, "A" => &sa, "B" => &left.canon, "C" => &sb, "D" => &right.canon, "F" => "cmin"},
            &[&left.proof, &right.proof],
        );
        let between = t!(&left.canon, &right.canon, "cmin", "co");
        let gap = left.value.minus(&right.value);
        let worked = take!(self.made_canon(&between, &gap, scope, facts)?);
        let difference = t!(&sa, &sb, "cmin", "co");
        let valued = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &difference, "B" => &between, "C" => &worked.canon},
            &[&moved, &worked.proof],
        );
        let canon_apart = take!(self.surd_apart(&worked.canon, &gap, scope, facts)?);
        let differs = self.b.ap(
            "eqnetrd",
            &binds! {"ph" => scope, "A" => &difference, "B" => &worked.canon, "C" => "cc0"},
            &[&valued, &canon_apart],
        );
        let a_cc = take!(self.carried_cc(&sa, &left, scope, facts)?);
        let b_cc = take!(self.carried_cc(&sb, &right, scope, facts)?);
        Ok(Built(self.b.ap(
            "subne0ad",
            &binds! {"ph" => scope, "A" => &sa, "B" => &sb},
            &[&a_cc, &b_cc, &differs],
        )))
    }

    /// ( scope -> said e. CC ) for a term proved equal to its canon, which
    /// is a number by the roots it is built from.
    fn carried_cc(
        &mut self,
        said: &Rpn,
        valued: &Valued,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let canon_cc = take!(self.in_cc(&valued.canon, scope, facts)?);
        Ok(Built(self.b.ap(
            "eqeltrd",
            &binds! {"ph" => scope, "A" => said, "B" => &valued.canon, "C" => "cc"},
            &[&valued.proof, &canon_cc],
        )))
    }

    /// ( scope -> claim ) for an order or a membership, said of its sides'
    /// canons and carried back to the sides as written (`breq12d`,
    /// `eleq1d`), as `arithmetic` says one of its sides' values. A side's
    /// canon is rational, which `arithmetic` decides of, except in a
    /// membership of ℝ or ℂ, which the canon has by the roots it is built
    /// from.
    fn by_surd_values(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let negated = goal.label() == Some("wn") && goal.children().len() == 1;
        let inner = if negated { &goal.children()[0] } else { goal };
        let kids = inner.children().to_vec();
        let (valued, iff) = match (inner.label(), kids.as_slice()) {
            (Some("wcel"), [x, set]) => {
                let side = take!(self.valued(x, scope, facts)?);
                let (sx, ss) = (self.rpn(x), self.rpn(set));
                let iff = self.b.ap(
                    "eleq1d",
                    &binds! {"ph" => scope, "A" => &sx, "B" => &side.canon, "C" => &ss},
                    &[&side.proof],
                );
                (t!(&side.canon, &ss, "wcel"), iff)
            }
            (Some("wbr"), [a, b, relation]) => {
                let left = take!(self.valued(a, scope, facts)?);
                let right = take!(self.valued(b, scope, facts)?);
                let r = self.rpn(relation);
                let iff = self.b.ap(
                    "breq12d",
                    &binds! {"ph" => scope, "A" => self.rpn(a), "B" => &left.canon, "C" => self.rpn(b), "D" => &right.canon, "R" => &r},
                    &[&left.proof, &right.proof],
                );
                (t!(&left.canon, &right.canon, &r, "wbr"), iff)
            }
            _ => return Ok(Route::no("not a relation real arithmetic proves")),
        };
        let said = self.rpn(inner);
        let (said, valued, iff) = if negated {
            let turned = self.b.ap(
                "notbid",
                &binds! {"ph" => scope, "ps" => &said, "ch" => &valued},
                &[&iff],
            );
            (t!(&said, "wn"), t!(&valued, "wn"), turned)
        } else {
            (said, valued, iff)
        };
        let held = if valued.has("csqrt") {
            // Only a membership of ℝ or ℂ is decided of a value that is not
            // rational.
            let goal = self.to_term(&valued);
            let system = goal.children()[1].label().unwrap_or("").to_string();
            let canon = self.rpn(&goal.children()[0]);
            self.membership(&canon, &system, scope, facts)?
        } else {
            self.numeral_fact(&valued, scope, facts)?
        };
        Ok(Built(self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &said, "ch" => &valued},
            &[&held, &iff],
        )))
    }

    /// ( scope -> t = canon ) for a closed term t.
    fn valued(
        &mut self,
        t: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let Built(Value::Exact(value)) = surds::closed_value(t) else {
            return Ok(Route::no("a term with no value"));
        };
        let said = self.rpn(t);
        if !surds::takes_root(t) {
            let canon = canon(&value);
            if said == canon {
                let same =
                    self.b
                        .ap("eqidd", &binds! {"ph" => scope, "A" => &said}, &[]);
                return Ok(Built(Valued {
                    value,
                    canon,
                    proof: same,
                }));
            }
            // `arithmetic` works a term of numerals to its value, except one
            // holding a power to an exponent below 0, whose power it holds as
            // an atom with no membership: that is taken apart here, as a
            // term with a root is, and `power` takes the exponent below 0.
            if !negative_power(t) {
                let (_, worked, proof) = take!(self.closed_valued(t, scope, facts)?);
                debug_assert_eq!(worked, canon, "a rational has one canon");
                return Ok(Built(Valued {
                    value,
                    canon,
                    proof,
                }));
            }
        }
        if surds::is_root(t) {
            return self.root_piece(t, value, scope, facts);
        }
        let kids = t.children().to_vec();
        let (written, moved) = match (t.label(), kids.as_slice()) {
            (Some("cneg"), [x]) => {
                let inner = take!(self.valued(x, scope, facts)?);
                let moved = self.b.ap(
                    "negeqd",
                    &binds! {"ph" => scope, "A" => self.rpn(x), "B" => &inner.canon},
                    &[&inner.proof],
                );
                (t!(&inner.canon, "cneg"), moved)
            }
            (Some("co"), [x, y, op]) => {
                let left = take!(self.valued(x, scope, facts)?);
                let right = take!(self.valued(y, scope, facts)?);
                let how = op.label().unwrap_or("").to_string();
                let op = self.rpn(op);
                let moved = self.b.ap(
                    "oveq12d",
                    &binds! {"ph" => scope, "A" => self.rpn(x), "B" => &left.canon,
                    "C" => self.rpn(y), "D" => &right.canon, "F" => &op},
                    &[&left.proof, &right.proof],
                );
                let written = t!(&left.canon, &right.canon, &op, "co");
                // A quotient and a power are worked from their parts'
                // canons; anything else is an identity of the canons.
                let worked = match how.as_str() {
                    field::DIV => take!(self.quotient(&left, &right, scope, facts)?),
                    field::EXP => take!(self.power(&left, &right, scope, facts)?),
                    _ => take!(self.made_canon(&written, &value, scope, facts)?),
                };
                let joined = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &said, "B" => &written, "C" => &worked.canon},
                    &[&moved, &worked.proof],
                );
                return Ok(Built(Valued {
                    value,
                    canon: worked.canon,
                    proof: joined,
                }));
            }
            _ => {
                return Ok(Route::no(
                    "an operation real arithmetic does not carry through",
                ))
            }
        };
        let worked = take!(self.made_canon(&written, &value, scope, facts)?);
        let joined = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &said, "B" => &written, "C" => &worked.canon},
            &[&moved, &worked.proof],
        );
        Ok(Built(Valued {
            value,
            canon: worked.canon,
            proof: joined,
        }))
    }

    /// ( scope -> written = canon ) for an expression in roots of primes
    /// whose value is `value`.
    fn made_canon(
        &mut self,
        written: &Rpn,
        value: &Surd,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let canon = canon(value);
        let proof = if *written == canon {
            self.b
                .ap("eqidd", &binds! {"ph" => scope, "A" => written}, &[])
        } else {
            take!(self.identity(written, &canon, scope, facts)?)
        };
        Ok(Built(Valued {
            value: value.clone(),
            canon,
            proof,
        }))
    }

    /// ( scope -> canon =/= 0 ) for the canon of a value not zero. A
    /// rational one is `arithmetic`'s; any other times its cofactor is its
    /// norm, a rational not zero, so it is not zero itself (`mulne0bad`).
    fn surd_apart(
        &mut self,
        canon_of: &Rpn,
        value: &Surd,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        if value.as_rational().is_some() {
            return self
                .numeral_fact(&t!(canon_of, "cc0", "wne"), scope, facts)
                .map(Built);
        }
        let surds::Cofactor { times, norm } = surds::cofactor(value);
        let cofactor = canon(&times);
        let norm = spelt_rational(&norm);
        let product = t!(canon_of, &cofactor, "cmul", "co");
        let is_norm = take!(self.identity(&product, &norm, scope, facts)?);
        let norm_apart = self.numeral_fact(&t!(&norm, "cc0", "wne"), scope, facts)?;
        let product_apart = self.b.ap(
            "eqnetrd",
            &binds! {"ph" => scope, "A" => &product, "B" => &norm, "C" => "cc0"},
            &[&is_norm, &norm_apart],
        );
        let value_cc = take!(self.in_cc(canon_of, scope, facts)?);
        let cofactor_cc = take!(self.in_cc(&cofactor, scope, facts)?);
        Ok(Built(self.b.ap(
            "mulne0bad",
            &binds! {"ph" => scope, "A" => canon_of, "B" => &cofactor},
            &[&value_cc, &cofactor_cc, &product_apart],
        )))
    }

    /// ( scope -> A / B = canon ) for canons A and B, B not zero: B times
    /// the canon of the quotient is A, which is an identity, and `divmuld`
    /// turns that into the quotient.
    fn quotient(
        &mut self,
        top: &Valued,
        below: &Valued,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        if below.value.is_zero() {
            return Ok(Route::no("a division by zero"));
        }
        let value = top.value.times(&below.value.recip());
        let canon = canon(&value);
        let (a, b) = (&top.canon, &below.canon);
        let back =
            take!(self.identity(&t!(b, &canon, "cmul", "co"), a, scope, facts)?);
        let a_cc = take!(self.in_cc(a, scope, facts)?);
        let b_cc = take!(self.in_cc(b, scope, facts)?);
        let canon_cc = take!(self.in_cc(&canon, scope, facts)?);
        let b_apart = take!(self.surd_apart(b, &below.value, scope, facts)?);
        let iff = self.b.ap(
            "divmuld",
            &binds! {"ph" => scope, "A" => a, "B" => b, "C" => &canon},
            &[&a_cc, &b_cc, &canon_cc, &b_apart],
        );
        let proof = self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => t!(t!(a, b, "cdiv", "co"), &canon, "wceq"),
            "ch" => t!(t!(b, &canon, "cmul", "co"), a, "wceq")},
            &[&back, &iff],
        );
        Ok(Built(Valued {
            value,
            canon,
            proof,
        }))
    }

    /// ( scope -> C ^ K = canon ) for a canon C and a whole exponent K:
    /// C¹ is C (`exp1d`) and each power after it is the one before times C
    /// (`expp1d`), brought to its canon before the next, so a power is never
    /// expanded whole. C⁰ is 1 (`exp0d`), and a negative exponent is one
    /// over the power (`expnegd`).
    fn power(
        &mut self,
        base: &Valued,
        exponent: &Valued,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let Some(k) = exponent
            .value
            .as_rational()
            .filter(|k| k.is_integer())
            .and_then(|k| k.to_integer().to_i64())
        else {
            return Ok(Route::no("a power whose exponent is not whole"));
        };
        let c = &base.canon;
        let c_cc = take!(self.in_cc(c, scope, facts)?);
        if k < 0 {
            let m = numerals::spell(k.unsigned_abs());
            let whole = Valued {
                value: Surd::rational(Q::from_integer(k.unsigned_abs().into())),
                canon: m.clone(),
                proof: self.b.ap("eqidd", &binds! {"ph" => scope, "A" => &m}, &[]),
            };
            let raised = take!(self.power(base, &whole, scope, facts)?);
            let c_apart = take!(self.surd_apart(c, &base.value, scope, facts)?);
            let m_z = self.numeral_fact(&t!(&m, "cz", "wcel"), scope, facts)?;
            let turned = self.b.ap(
                "expnegd",
                &binds! {"ph" => scope, "A" => c, "N" => &m},
                &[&c_cc, &c_apart, &m_z],
            );
            let one = Valued {
                value: Surd::rational(field::q(1)),
                canon: numeral(1),
                proof: self.b.ap(
                    "eqidd",
                    &binds! {"ph" => scope, "A" => numeral(1)},
                    &[],
                ),
            };
            let over = t!(c, &m, "cexp", "co");
            let carried = self.b.ap(
                "oveq2d",
                &binds! {"ph" => scope, "A" => &over, "B" => &raised.canon, "C" => numeral(1), "F" => "cdiv"},
                &[&raised.proof],
            );
            let worked = take!(self.quotient(&one, &raised, scope, facts)?);
            let first = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => t!(c, &exponent.canon, "cexp", "co"),
                "B" => t!(numeral(1), &over, "cdiv", "co"), "C" => t!(numeral(1), &raised.canon, "cdiv", "co")},
                &[&turned, &carried],
            );
            let proof = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => t!(c, &exponent.canon, "cexp", "co"),
                "B" => t!(numeral(1), &raised.canon, "cdiv", "co"), "C" => &worked.canon},
                &[&first, &worked.proof],
            );
            return Ok(Built(Valued {
                value: worked.value,
                canon: worked.canon,
                proof,
            }));
        }
        if k == 0 {
            let proof = self
                .b
                .ap("exp0d", &binds! {"ph" => scope, "A" => c}, &[&c_cc]);
            return Ok(Built(Valued {
                value: Surd::rational(field::q(1)),
                canon: numeral(1),
                proof,
            }));
        }
        let mut proof = self
            .b
            .ap("exp1d", &binds! {"ph" => scope, "A" => c}, &[&c_cc]);
        let mut at = base.value.clone();
        let mut written = c.clone();
        for j in 1..k as u32 {
            let (here, next) = (numeral(j), numeral(j + 1));
            let sum = t!(&here, numeral(1), "caddc", "co");
            let counted = self.numeral_fact(&t!(&next, &sum, "wceq"), scope, facts)?;
            let respelt = self.b.ap(
                "oveq2d",
                &binds! {"ph" => scope, "A" => &next, "B" => &sum, "C" => c, "F" => "cexp"},
                &[&counted],
            );
            let here_n0 = self.numeral_fact(&t!(&here, "cn0", "wcel"), scope, facts)?;
            let stepped = self.b.ap(
                "expp1d",
                &binds! {"ph" => scope, "A" => c, "N" => &here},
                &[&c_cc, &here_n0],
            );
            let before = t!(c, &here, "cexp", "co");
            let carried = self.b.ap(
                "oveq1d",
                &binds! {"ph" => scope, "A" => &before, "B" => &written, "C" => c, "F" => "cmul"},
                &[&proof],
            );
            at = at.times(&base.value);
            let product = t!(&written, c, "cmul", "co");
            let worked = take!(self.made_canon(&product, &at, scope, facts)?);
            let raised = t!(c, &next, "cexp", "co");
            let mut chain = respelt;
            for (from, to, link) in [
                (
                    t!(c, &sum, "cexp", "co"),
                    t!(&before, c, "cmul", "co"),
                    stepped,
                ),
                (t!(&before, c, "cmul", "co"), product.clone(), carried),
                (product.clone(), worked.canon.clone(), worked.proof),
            ] {
                chain = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &raised, "B" => &from, "C" => &to},
                    &[&chain, &link],
                );
            }
            proof = chain;
            written = worked.canon;
        }
        Ok(Built(Valued {
            value: at,
            canon: written,
            proof,
        }))
    }

    /// ( scope -> √x = c·(√p₁·(√p₂·…)) ) for a closed x whose value r is a
    /// rational of at least 0, where r = c²·(p₁·(p₂·…)): x is that product
    /// by arithmetic, the root of a product is the product of the roots
    /// (`sqrtmuld`), and the root of c² is c (`sqrtsqd`). That is the canon
    /// of the root.
    fn root_piece(
        &mut self,
        t: &Term,
        value: Surd,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let x = &t.children()[0];
        let Built(Value::Exact(v)) = surds::closed_value(x) else {
            return Ok(Route::no("a root of a number with no value"));
        };
        let Some(r) = v.as_rational() else {
            return Ok(Route::no("a root of a number that is not rational"));
        };
        let Ok(root) = surds::root_of(&r) else {
            return Ok(Route::no("a root real arithmetic does not take"));
        };
        let c = spelt_rational(&root.coefficient);
        let square = t!(&c, numeral(2), "cexp", "co");
        let primes = product_of_primes(&root.primes);
        let radicand = match &primes {
            None => square.clone(),
            Some(m) => t!(&square, m, "cmul", "co"),
        };
        let sx = self.rpn(x);
        let is = self.numeral_fact(&t!(&sx, &radicand, "wceq"), scope, facts)?;
        let carried = self.b.ap(
            "fveq2d",
            &binds! {"ph" => scope, "A" => &sx, "B" => &radicand, "F" => "csqrt"},
            &[&is],
        );
        let root_of = |r: &Rpn| t!(r, "csqrt", "cfv");
        let c_real = self.numeral_fact(&t!(&c, "cr", "wcel"), scope, facts)?;
        let c_above = self.numeral_fact(&t!("cc0", &c, "cle", "wbr"), scope, facts)?;
        let unsquared = self.b.ap(
            "sqrtsqd",
            &binds! {"ph" => scope, "A" => &c},
            &[&c_real, &c_above],
        );
        let (expression, valued) = match &primes {
            None => (c.clone(), unsquared),
            Some(m) => {
                let square_real =
                    self.numeral_fact(&t!(&square, "cr", "wcel"), scope, facts)?;
                let square_above =
                    self.numeral_fact(&t!("cc0", &square, "cle", "wbr"), scope, facts)?;
                let m_real = self.numeral_fact(&t!(m, "cr", "wcel"), scope, facts)?;
                let m_above =
                    self.numeral_fact(&t!("cc0", m, "cle", "wbr"), scope, facts)?;
                let apart = self.b.ap(
                    "sqrtmuld",
                    &binds! {"ph" => scope, "A" => &square, "B" => m},
                    &[&square_real, &square_above, &m_real, &m_above],
                );
                let first = self.b.ap(
                    "oveq1d",
                    &binds! {"ph" => scope, "A" => root_of(&square), "B" => &c, "C" => root_of(m), "F" => "cmul"},
                    &[&unsquared],
                );
                let (roots, split) = self.split_root(&root.primes, scope, facts)?;
                let second = self.b.ap(
                    "oveq2d",
                    &binds! {"ph" => scope, "A" => root_of(m), "B" => &roots, "C" => &c, "F" => "cmul"},
                    &[&split],
                );
                let both = t!(root_of(&square), root_of(m), "cmul", "co");
                let halfway = t!(&c, root_of(m), "cmul", "co");
                let expression = t!(&c, &roots, "cmul", "co");
                let one = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => root_of(&radicand), "B" => &both, "C" => &halfway},
                    &[&apart, &first],
                );
                let two = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => root_of(&radicand), "B" => &halfway, "C" => &expression},
                    &[&one, &second],
                );
                (expression, two)
            }
        };
        let proof = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => root_of(&sx), "B" => root_of(&radicand), "C" => &expression},
            &[&carried, &valued],
        );
        // A root with a whole coefficient is written as its canon; one over a
        // denominator, √(1/2) = 1/2·√2, is brought to (1·√2)/2.
        let worked = take!(self.made_canon(&expression, &value, scope, facts)?);
        let joined = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => root_of(&sx), "B" => &expression, "C" => &worked.canon},
            &[&proof, &worked.proof],
        );
        Ok(Built(Valued {
            value,
            canon: worked.canon,
            proof: joined,
        }))
    }

    /// ( scope -> √(p₁·(p₂·…)) = √p₁·(√p₂·…) ), and the right side.
    fn split_root(
        &mut self,
        primes: &[u64],
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<(Rpn, Proof)> {
        let product = product_of_primes(primes).expect("a root of at least one prime");
        let root_of = |r: &Rpn| t!(r, "csqrt", "cfv");
        let [first, rest @ ..] = primes else {
            unreachable!("a root of at least one prime");
        };
        if rest.is_empty() {
            let same = self.b.ap(
                "eqidd",
                &binds! {"ph" => scope, "A" => root_of(&product)},
                &[],
            );
            return Ok((root_of(&product), same));
        }
        let head = numerals::spell(*first);
        let tail = product_of_primes(rest).expect("at least one prime is left");
        let mut held = Vec::new();
        for claim in [
            t!(&head, "cr", "wcel"),
            t!("cc0", &head, "cle", "wbr"),
            t!(&tail, "cr", "wcel"),
            t!("cc0", &tail, "cle", "wbr"),
        ] {
            held.push(self.numeral_fact(&claim, scope, facts)?);
        }
        let apart = self.b.ap(
            "sqrtmuld",
            &binds! {"ph" => scope, "A" => &head, "B" => &tail},
            &[&held[0], &held[1], &held[2], &held[3]],
        );
        let (roots, split) = self.split_root(rest, scope, facts)?;
        let carried = self.b.ap(
            "oveq2d",
            &binds! {"ph" => scope, "A" => root_of(&tail), "B" => &roots, "C" => root_of(&head), "F" => "cmul"},
            &[&split],
        );
        let whole = t!(root_of(&head), &roots, "cmul", "co");
        let joined = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => root_of(&product), "B" => t!(root_of(&head), root_of(&tail), "cmul", "co"), "C" => &whole},
            &[&apart, &carried],
        );
        Ok((whole, joined))
    }

    /// ( scope -> left = right ) for two expressions whose only atoms are
    /// square roots of primes and which are equal: d·left − d·right, for d
    /// the least whole number that makes its coefficients whole, is a sum
    /// of whole multiples of (√p)² − p, each zero, and the normaliser shows
    /// the sum is the difference; d is cancelled (`mulcanad`). The
    /// multiples are whole so that the normaliser adds no fractions.
    fn identity(
        &mut self,
        left: &Rpn,
        right: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let read = |me: &Self, r: &Rpn| field::read(&me.to_term(r), &labels);
        let difference = read(self, left).minus(&read(self, right));
        let Some(under) = difference.under.constant_value().filter(|u| !u.is_zero())
        else {
            return Ok(Route::no("a divisor that is not a number"));
        };
        let exact = difference.over.scaled(&under.recip());
        let scale = exact
            .terms
            .values()
            .fold(BigInt::one(), |d, v| d.lcm(v.denom()));
        let mut rest = exact.scaled(&Q::from_integer(scale.clone()));
        let mut by: IndexMap<Rpn, Multiplier> = IndexMap::new();
        while let Some(found) = reducible(&rest, self) {
            rest.terms.shift_remove(&found.monomial);
            let lowered = lowered(&found.monomial, &found.root);
            let one = Poly::new(IndexMap::from([(lowered, found.weight)]));
            let entry = by.entry(found.root.clone()).or_insert_with(|| Multiplier {
                root: found.root.clone(),
                prime: found.prime,
                times: Poly::default(),
            });
            entry.times = entry.times.plus(&one);
            rest = rest.plus(&one.scaled(&field::q(found.prime as i64)));
        }
        if !rest.zero() {
            return Ok(Route::no("the two sides are not one value"));
        }
        let mut w = Work::plain(scope, facts);
        if by.is_empty() {
            return self.same_polynomial(&mut w, left, right);
        }
        let mut pieces: Vec<(Rpn, Proof)> = Vec::new();
        for m in by.values() {
            let prime = numerals::spell(m.prime);
            let squared = t!(&m.root, numeral(2), "cexp", "co");
            let gap = t!(&squared, &prime, "cmin", "co");
            let prime_cc =
                self.numeral_fact(&t!(&prime, "cc", "wcel"), scope, facts)?;
            let squares = self.b.ap(
                "sqsqrtd",
                &binds! {"ph" => scope, "A" => &prime},
                &[&prime_cc],
            );
            let squared_cc = take!(self.in_cc(&squared, scope, facts)?);
            let turn = self.b.ap(
                "subeq0ad",
                &binds! {"ph" => scope, "A" => &squared, "B" => &prime},
                &[&squared_cc, &prime_cc],
            );
            let vanishes = self.b.ap(
                "mpbird",
                &binds! {"ph" => scope, "ps" => t!(&gap, "cc0", "wceq"), "ch" => t!(&squared, &prime, "wceq")},
                &[&squares, &turn],
            );
            let times = spelt_poly(&m.times);
            let moved = self.b.ap(
                "oveq2d",
                &binds! {"ph" => scope, "A" => &gap, "B" => "cc0", "C" => &times, "F" => "cmul"},
                &[&vanishes],
            );
            let times_cc = self.membership(&times, "cc", scope, facts)?;
            let zero = self.b.ap(
                "mul01d",
                &binds! {"ph" => scope, "A" => &times},
                &[&times_cc],
            );
            let piece = t!(&times, &gap, "cmul", "co");
            let proof = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &piece, "B" => t!(&times, "cc0", "cmul", "co"), "C" => "cc0"},
                &[&moved, &zero],
            );
            pieces.push((piece, proof));
        }
        let (mut total, mut sums) = pieces[0].clone();
        let naught = t!("cc0", "cc0", "caddc", "co");
        for (piece, proof) in &pieces[1..] {
            let joined = t!(&total, piece, "caddc", "co");
            let both = self.b.ap(
                "oveq12d",
                &binds! {"ph" => scope, "A" => &total, "B" => "cc0", "C" => piece, "D" => "cc0", "F" => "caddc"},
                &[&sums, proof],
            );
            let zero = self.b.ap(
                "a1i",
                &binds! {"ph" => t!(&naught, "cc0", "wceq"), "ps" => scope},
                &[&self.step("00id")],
            );
            sums = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &joined, "B" => &naught, "C" => "cc0"},
                &[&both, &zero],
            );
            total = joined;
        }
        let scaled =
            (!scale.is_one()).then(|| numerals::spell(scale.magnitude().clone()));
        let (l, r) = match &scaled {
            None => (left.clone(), right.clone()),
            Some(d) => (t!(d, left, "cmul", "co"), t!(d, right, "cmul", "co")),
        };
        let whole = t!(&l, &r, "cmin", "co");
        let alike = take!(self.same_polynomial(&mut w, &total, &whole)?);
        let l_cc = take!(self.in_cc(&l, scope, facts)?);
        let r_cc = take!(self.in_cc(&r, scope, facts)?);
        let reached = self.b.ap(
            "eqtr3d",
            &binds! {"ph" => scope, "A" => &total, "B" => &whole, "C" => "cc0"},
            &[&alike, &sums],
        );
        let turn = self.b.ap(
            "subeq0ad",
            &binds! {"ph" => scope, "A" => &l, "B" => &r},
            &[&l_cc, &r_cc],
        );
        let equal = self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(&whole, "cc0", "wceq"), "ch" => t!(&l, &r, "wceq")},
            &[&reached, &turn],
        );
        let Some(d) = scaled else {
            return Ok(Built(equal));
        };
        let left_cc = take!(self.in_cc(left, scope, facts)?);
        let right_cc = take!(self.in_cc(right, scope, facts)?);
        let d_cc = self.numeral_fact(&t!(&d, "cc", "wcel"), scope, facts)?;
        let d_apart = self.numeral_fact(&t!(&d, "cc0", "wne"), scope, facts)?;
        Ok(Built(self.b.ap(
            "mulcanad",
            &binds! {"ph" => scope, "A" => left, "B" => right, "C" => &d},
            &[&left_cc, &right_cc, &d_cc, &d_apart, &equal],
        )))
    }
}

/// A monomial holding a root of a prime to the power 2 or more, which the
/// reduction takes (√p)² = p out of.
struct Reducible {
    monomial: Monomial,
    weight: Q,
    /// √p.
    root: Rpn,
    prime: u64,
}

/// The first monomial of `p`, in the order the polynomial holds them,
/// holding a root of a prime to the power 2 or more.
fn reducible(p: &Poly, el: &Elaborator) -> Option<Reducible> {
    for (monomial, weight) in &p.terms {
        for (atom, power) in monomial {
            if *power < 2 {
                continue;
            }
            if let Some(prime) = prime_under(&el.to_term(atom)) {
                return Some(Reducible {
                    monomial: monomial.clone(),
                    weight: weight.clone(),
                    root: atom.clone(),
                    prime,
                });
            }
        }
    }
    None
}

/// The monomial with the power of `atom` two less.
fn lowered(monomial: &Monomial, atom: &Rpn) -> Monomial {
    monomial
        .iter()
        .filter_map(|(a, power)| match (a == atom, power) {
            (true, 2) => None,
            (true, p) => Some((a.clone(), p - 2)),
            (false, p) => Some((a.clone(), *p)),
        })
        .collect()
}

/// The prime p where the term is √p.
fn prime_under(term: &Term) -> Option<u64> {
    if !surds::is_root(term) {
        return None;
    }
    let n = crate::methods::numerals::value(&term.children()[0])?.to_u64()?;
    surds::root_of(&field::q(n as i64))
        .ok()
        .filter(|r| r.primes == [n] && r.coefficient == field::q(1))
        .map(|_| n)
}

/// Every prime under a root of the term, as its value finds them.
fn primes_under(term: &Term) -> Vec<u64> {
    let mut out = Vec::new();
    collect_primes(term, &mut out);
    out.sort_unstable();
    out.dedup();
    out
}

fn collect_primes(term: &Term, out: &mut Vec<u64>) {
    if term.variable().is_some() {
        return;
    }
    if surds::is_root(term) {
        if let Built(Value::Exact(v)) = surds::closed_value(term) {
            out.extend(v.primes());
        }
    }
    for kid in term.children() {
        collect_primes(kid, out);
    }
}

/// Whether a term raises something to an exponent whose value is below 0.
fn negative_power(term: &Term) -> bool {
    if term.variable().is_some() {
        return false;
    }
    let kids = term.children();
    let here = term.label() == Some("co")
        && kids.len() == 3
        && kids[2].label() == Some(field::EXP)
        && matches!(
            field::closed_value(&kids[1]),
            Built(field::Value::Exact(v)) if v.is_negative()
        );
    here || kids.iter().any(negative_power)
}

/// √p, as set.mm spells it.
fn root_of_prime(p: u64) -> Rpn {
    t!(numerals::spell(p), "csqrt", "cfv")
}

/// p₁·(p₂·…), or None for no primes.
fn product_of_primes(primes: &[u64]) -> Option<Rpn> {
    let (last, before) = primes.split_last()?;
    let mut out = numerals::spell(*last);
    for p in before.iter().rev() {
        out = t!(numerals::spell(*p), out, "cmul", "co");
    }
    Some(out)
}

/// √p₁·(√p₂·…), or None for no primes.
fn product_of_roots(primes: &[u64]) -> Option<Rpn> {
    let (last, before) = primes.split_last()?;
    let mut out = root_of_prime(*last);
    for p in before.iter().rev() {
        out = t!(root_of_prime(*p), out, "cmul", "co");
    }
    Some(out)
}

/// The canon of a value: a rational as `arithmetic` writes it, and any
/// other value with whole coefficients as its parts added from the left,
/// the rational part first and then by the product under the root, each
/// part its coefficient times the product of its roots. A value with a
/// coefficient that is not whole is that sum for its multiple by the least
/// common denominator, over the denominator: the normaliser adds fractions
/// without cancelling, so a sum of eight parts each over the same N is
/// read over N⁸, and one over N is read over N.
fn canon(value: &Surd) -> Rpn {
    if let Some(rational) = value.as_rational() {
        return spelt_rational(&rational);
    }
    let common = surds::common_denominator(value);
    if common.is_one() {
        return whole_canon(value);
    }
    let whole = value.scaled(&Q::from_integer(BigInt::from(common.clone())));
    t!(whole_canon(&whole), numerals::spell(common), "cdiv", "co")
}

/// The canon of a value with whole coefficients.
fn whole_canon(value: &Surd) -> Rpn {
    let mut parts: Vec<(&Vec<u64>, &Q)> = value.parts.iter().collect();
    parts.sort_by_key(|(basis, _)| basis.iter().map(|p| *p as u128).product::<u128>());
    let mut out: Option<Rpn> = None;
    for (basis, weight) in parts {
        let coefficient = spelt_rational(weight);
        let part = match product_of_roots(basis) {
            None => coefficient,
            Some(roots) => t!(coefficient, roots, "cmul", "co"),
        };
        out = Some(match out {
            None => part,
            Some(sum) => t!(sum, part, "caddc", "co"),
        });
    }
    out.unwrap_or_else(|| numeral(0))
}

/// A rational number as a term: a whole number as a numeral, and any other
/// as the quotient of two, each negated where it is negative; as
/// `arithmetic` writes a value (`closed_valued`).
fn spelt_rational(value: &Q) -> Rpn {
    if let Some(whole) = field::spell_coefficient(value) {
        return whole;
    }
    let top = numerals::spell(value.numer().magnitude().clone());
    let below = numerals::spell(value.denom().magnitude().clone());
    let quotient = t!(top, below, "cdiv", "co");
    if value.is_negative() {
        t!(quotient, "cneg")
    } else {
        quotient
    }
}

/// A polynomial as a sum of its terms, each a rational times a product of
/// powers of its atoms.
fn spelt_poly(p: &Poly) -> Rpn {
    let mut out: Option<Rpn> = None;
    let mut terms: Vec<(&Monomial, &Q)> = p.terms.iter().collect();
    terms.sort_by_key(|(m, _)| field::order(m));
    for (monomial, weight) in terms {
        let factors = monomial
            .iter()
            .map(|(atom, power)| match power {
                1 => atom.clone(),
                _ => t!(atom, numeral(*power), "cexp", "co"),
            })
            .reduce(|acc, f| t!(acc, f, "cmul", "co"));
        let coefficient = spelt_rational(weight);
        let term = match factors {
            None => coefficient,
            Some(f) => t!(coefficient, f, "cmul", "co"),
        };
        out = Some(match out {
            None => term,
            Some(sum) => t!(sum, term, "caddc", "co"),
        });
    }
    out.unwrap_or_else(|| numeral(0))
}
