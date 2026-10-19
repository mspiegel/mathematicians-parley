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
use crate::methods::reals::{self, Atom, Real};
use crate::methods::surds::{self, Surd, Verdict};
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::mm::Rpn;
use crate::outcome::{Built, Checked, Declined, Problem, Route};
use crate::{t, take};

/// A term proved equal to the canon of its value: ( scope -> term = canon ).
struct Valued {
    value: Real,
    canon: Rpn,
    proof: Proof,
}

/// The logarithm of a positive rational worked out:
/// ( scope -> ( log ` ratio ) = expression ), the expression a sum of
/// whole multiples of logarithms of primes, 0 for the ratio 1.
struct Logarithm {
    /// The ratio, as `arithmetic` writes a value.
    ratio: Rpn,
    expression: Rpn,
    proof: Proof,
}

/// A product of powers of primes, with what it is proved of:
/// ( scope -> ( log ` product ) = expression ) and ( scope -> product e. RR+ ).
struct LoggedProduct {
    product: Rpn,
    expression: Rpn,
    logged: Proof,
    positive: Proof,
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
        match reals::decide_closed(&goal) {
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
                "{what}, which is not a fact about numerals, square roots, π, e and logarithms alone, and real arithmetic decides nothing else"
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
    /// the claim, and the same of π, e and each ln p its values hold: what
    /// the normaliser and a membership ask of each atom.
    fn roots_known(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Facts> {
        let known = facts.copy();
        for atom in atoms_under(goal) {
            let (said, real) = match atom {
                Atom::Pi => (
                    t!("cpi"),
                    self.closed_law(&t!("cpi", "cr", "wcel"), "pire", scope),
                ),
                Atom::E => (
                    t!("ceu"),
                    self.closed_law(&t!("ceu", "cr", "wcel"), "ere", scope),
                ),
                Atom::Ln(p) => {
                    let prime = numerals::spell(p);
                    let positive = self.positive(&prime, scope, facts)?;
                    let real = self.b.ap(
                        "relogcld",
                        &binds! {"ph" => scope, "A" => &prime},
                        &[&positive],
                    );
                    (spelt_atom(atom), real)
                }
            };
            let complex =
                self.b
                    .ap("recnd", &binds! {"ph" => scope, "A" => &said}, &[&real]);
            self.know(&known, t!(&said, "cr", "wcel"), real);
            self.know(&known, t!(&said, "cc", "wcel"), complex);
        }
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

    /// ( scope -> t e. system ) for a square root, π, e or a logarithm that
    /// `real arithmetic` takes, in ℝ or ℂ: its membership said once
    /// (`READERS.md`). π is real (`pire`) and complex (`picn`), e real
    /// (`ere`), and the logarithm of a positive rational real (`relogcld`);
    /// a real one is complex (`recnd`).
    pub(super) fn real_within(
        &mut self,
        t: &Term,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        if surds::is_root(t) {
            return self.root_within(t, system, scope, facts);
        }
        let said = self.rpn(t);
        // A sine or cosine of a real angle is real.
        let trig = reals::Trig::of(t).map(|f| match f {
            reals::Trig::Sine => "resincld",
            reals::Trig::Cosine => "recoscld",
        });
        let real = match t.label() {
            _ if trig.is_some() => {
                let x = self.rpn(&t.children()[0]);
                let angle = self.membership(&x, "cr", scope, facts)?;
                self.b.ap(
                    trig.expect("a sine or cosine"),
                    &binds! {"ph" => scope, "A" => &x},
                    &[&angle],
                )
            }
            Some("cpi") => self.closed_law(&t!("cpi", "cr", "wcel"), "pire", scope),
            Some("ceu") => self.closed_law(&t!("ceu", "cr", "wcel"), "ere", scope),
            _ => {
                let x = self.rpn(&t.children()[0]);
                let positive = self.positive(&x, scope, facts)?;
                self.b
                    .ap("relogcld", &binds! {"ph" => scope, "A" => &x}, &[&positive])
            }
        };
        match system.alone() {
            Some("cr") => Ok(Built(real)),
            Some("cc") => Ok(Built(self.b.ap(
                "recnd",
                &binds! {"ph" => scope, "A" => &said},
                &[&real],
            ))),
            _ => Ok(Route::no("said once only in ℝ and ℂ")),
        }
    }

    /// ( scope -> √x e. system ) for a root `real arithmetic` takes, in ℝ
    /// or ℂ: its membership said once (`READERS.md`). x is a rational of at
    /// least 0, which `arithmetic` says, and its root is real (`resqrtcld`),
    /// or complex (`sqrtcld`).
    fn root_within(
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

    /// ( scope -> claim ) for a theorem of set.mm stating `claim` with no
    /// hypothesis, as `pire` states π ∈ ℝ.
    fn closed_law(&self, claim: &Rpn, label: &str, scope: &Rpn) -> Proof {
        self.b.ap(
            "a1i",
            &binds! {"ph" => claim, "ps" => scope},
            &[&self.step(label)],
        )
    }

    /// ( scope -> x e. RR+ ) for a closed x of numerals with a positive
    /// value: x ∈ ℝ and 0 < x by arithmetic (`elrpd`).
    fn positive(&mut self, x: &Rpn, scope: &Rpn, facts: &Facts) -> Checked<Proof> {
        let real = self.numeral_fact(&t!(x, "cr", "wcel"), scope, facts)?;
        let above = self.numeral_fact(&t!("cc0", x, "clt", "wbr"), scope, facts)?;
        Ok(self
            .b
            .ap("elrpd", &binds! {"ph" => scope, "A" => x}, &[&real, &above]))
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
        // The decider found the difference a surd or logarithms of primes.
        let canon_apart = match gap.as_surd() {
            Some(s) => take!(self.surd_apart(&worked.canon, &s, scope, facts)?),
            None => take!(self.ln_apart(&worked.canon, &gap, scope, facts)?),
        };
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
        // A membership of a value that is not rational is ℝ's or ℂ's, which
        // the canon has by the atoms it is built from.
        let mut atoms_in = false;
        let (valued, iff) = match (inner.label(), kids.as_slice()) {
            (Some("wcel"), [x, set]) => {
                let side = take!(self.valued(x, scope, facts)?);
                atoms_in = side.value.as_surd().and_then(|s| s.as_rational()).is_none();
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
        let held = if atoms_in {
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
        let Built(reals::Value::Exact(value)) = reals::closed_value(t) else {
            return Ok(Route::no("a term with no value"));
        };
        let said = self.rpn(t);
        if !reals::beyond_arithmetic(t) {
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
            let (_, worked, proof) = take!(self.closed_valued(t, scope, facts)?);
            debug_assert_eq!(worked, canon, "a rational has one canon");
            return Ok(Built(Valued {
                value,
                canon,
                proof,
            }));
        }
        if surds::is_root(t) {
            return self.root_piece(t, value, scope, facts);
        }
        if reals::applies(t, "clog") {
            return self.ln_piece(t, value, scope, facts);
        }
        if reals::applies(t, "ce") {
            return self.exp_piece(t, value, scope, facts);
        }
        if let Some(f) = reals::Trig::of(t) {
            return self.trig_piece(t, f, value, scope, facts);
        }
        let kids = t.children().to_vec();
        if matches!(t.label(), Some("cpi" | "ceu")) && kids.is_empty() {
            return self.made_canon(&said, &value, scope, facts);
        }
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

    /// ( scope -> written = canon ) for an expression in roots of primes, π,
    /// e and logarithms of primes whose value is `value`.
    fn made_canon(
        &mut self,
        written: &Rpn,
        value: &Real,
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
        let cofactor = canon(&Real::surd(times));
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
        let Some(divisor) = below.value.as_surd().filter(|s| !s.is_zero()) else {
            return Ok(Route::no("a division by zero or by an atom"));
        };
        let value = top.value.times(&Real::surd(divisor.recip()));
        let canon = canon(&value);
        let (a, b) = (&top.canon, &below.canon);
        let back =
            take!(self.identity(&t!(b, &canon, "cmul", "co"), a, scope, facts)?);
        let a_cc = take!(self.in_cc(a, scope, facts)?);
        let b_cc = take!(self.in_cc(b, scope, facts)?);
        let canon_cc = take!(self.in_cc(&canon, scope, facts)?);
        let b_apart = take!(self.surd_apart(b, &divisor, scope, facts)?);
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
            .as_surd()
            .and_then(|s| s.as_rational())
            .filter(|k| k.is_integer())
            .and_then(|k| k.to_integer().to_i64())
        else {
            return Ok(Route::no("a power whose exponent is not whole"));
        };
        let c = &base.canon;
        let c_cc = take!(self.in_cc(c, scope, facts)?);
        if k < 0 {
            let Some(base_surd) = base.value.as_surd() else {
                return Ok(Route::no("a power of an atom to an exponent below 0"));
            };
            let m = numerals::spell(k.unsigned_abs());
            let whole = Valued {
                value: Real::rational(Q::from_integer(k.unsigned_abs().into())),
                canon: m.clone(),
                proof: self.b.ap("eqidd", &binds! {"ph" => scope, "A" => &m}, &[]),
            };
            let raised = take!(self.power(base, &whole, scope, facts)?);
            let c_apart = take!(self.surd_apart(c, &base_surd, scope, facts)?);
            let m_z = self.numeral_fact(&t!(&m, "cz", "wcel"), scope, facts)?;
            let turned = self.b.ap(
                "expnegd",
                &binds! {"ph" => scope, "A" => c, "N" => &m},
                &[&c_cc, &c_apart, &m_z],
            );
            let one = Valued {
                value: Real::rational(field::q(1)),
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
                value: Real::rational(field::q(1)),
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
        value: Real,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let x = &t.children()[0];
        let Built(surds::Value::Exact(v)) = surds::closed_value(x) else {
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

    /// The logarithm of a positive rational r = Π p^nₚ: r is that product of
    /// powers by arithmetic, carried under the logarithm (`fveq2d`), and the
    /// logarithm of the product is Σ nₚ·ln p (`ln_product`); ln 1 is 0
    /// (`log1`).
    fn ln_rational(
        &mut self,
        ratio: &Q,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Logarithm>> {
        let spelt = spelt_rational(ratio);
        let Ok(factors) = reals::factored(ratio) else {
            return Ok(Route::no("a ratio too large to factor"));
        };
        let powers: Vec<Rpn> = factors
            .iter()
            .filter(|(_, n)| **n != 0)
            .map(|(p, n)| t!(numerals::spell(*p), spelt_whole(*n), "cexp", "co"))
            .collect();
        if powers.is_empty() {
            let proof = self.closed_law(
                &t!(t!("c1", "clog", "cfv"), "cc0", "wceq"),
                "log1",
                scope,
            );
            return Ok(Built(Logarithm {
                ratio: spelt,
                expression: numeral(0),
                proof,
            }));
        }
        let product = take!(self.ln_product(&factors, scope, facts)?);
        let is =
            self.numeral_fact(&t!(&spelt, &product.product, "wceq"), scope, facts)?;
        let carried = self.b.ap(
            "fveq2d",
            &binds! {"ph" => scope, "A" => &spelt, "B" => &product.product, "F" => "clog"},
            &[&is],
        );
        let proof = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => t!(&spelt, "clog", "cfv"),
            "B" => t!(&product.product, "clog", "cfv"), "C" => &product.expression},
            &[&carried, &product.logged],
        );
        Ok(Built(Logarithm {
            ratio: spelt,
            expression: product.expression,
            proof,
        }))
    }

    /// p₁^n₁·p₂^n₂·…, multiplied from the left, with its logarithm
    /// n₁·ln p₁ + n₂·ln p₂ + …: the logarithm of a product of positive reals
    /// is the sum of theirs (`relogmuld`), and of a power to a whole
    /// exponent the exponent times it (`relogexp`).
    fn ln_product(
        &mut self,
        factors: &std::collections::BTreeMap<u64, i64>,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<LoggedProduct>> {
        let mut out: Option<LoggedProduct> = None;
        for (p, n) in factors.iter().filter(|(_, n)| **n != 0) {
            let prime = numerals::spell(*p);
            let exponent = spelt_whole(*n);
            let power = t!(&prime, &exponent, "cexp", "co");
            let prime_rp = self.positive(&prime, scope, facts)?;
            let exponent_z =
                self.numeral_fact(&t!(&exponent, "cz", "wcel"), scope, facts)?;
            let positive = self.b.ap(
                "rpexpcld",
                &binds! {"ph" => scope, "A" => &prime, "N" => &exponent},
                &[&prime_rp, &exponent_z],
            );
            let ln_p = t!(&prime, "clog", "cfv");
            let expression = t!(&exponent, &ln_p, "cmul", "co");
            let law =
                self.b
                    .ap("relogexp", &binds! {"A" => &prime, "N" => &exponent}, &[]);
            let logged = self.b.ap(
                "syl2anc",
                &binds! {"ph" => scope, "ps" => t!(&prime, "crp", "wcel"), "ch" => t!(&exponent, "cz", "wcel"),
                "th" => t!(t!(&power, "clog", "cfv"), &expression, "wceq")},
                &[&prime_rp, &exponent_z, &law],
            );
            let this = LoggedProduct {
                product: power,
                expression,
                logged,
                positive,
            };
            out = Some(match out {
                None => this,
                Some(before) => {
                    let product = t!(&before.product, &this.product, "cmul", "co");
                    let split = self.b.ap(
                        "relogmuld",
                        &binds! {"ph" => scope, "A" => &before.product, "B" => &this.product},
                        &[&before.positive, &this.positive],
                    );
                    let carried = self.b.ap(
                        "oveq12d",
                        &binds! {"ph" => scope, "A" => t!(&before.product, "clog", "cfv"), "B" => &before.expression,
                        "C" => t!(&this.product, "clog", "cfv"), "D" => &this.expression, "F" => "caddc"},
                        &[&before.logged, &this.logged],
                    );
                    let expression =
                        t!(&before.expression, &this.expression, "caddc", "co");
                    let logged = self.b.ap(
                        "eqtrd",
                        &binds! {"ph" => scope, "A" => t!(&product, "clog", "cfv"),
                        "B" => t!(t!(&before.product, "clog", "cfv"), t!(&this.product, "clog", "cfv"), "caddc", "co"),
                        "C" => &expression},
                        &[&split, &carried],
                    );
                    let positive = self.b.ap(
                        "rpmulcld",
                        &binds! {"ph" => scope, "A" => &before.product, "B" => &this.product},
                        &[&before.positive, &this.positive],
                    );
                    LoggedProduct {
                        product,
                        expression,
                        logged,
                        positive,
                    }
                }
            });
        }
        Ok(match out {
            Some(done) => Built(done),
            None => Route::no("a product of no primes"),
        })
    }

    /// ( scope -> ( log ` x ) = canon ) for x of value q·eᵏ: x is q·eᵏ
    /// written so, ln(q·eᵏ) = ln q + ln(eᵏ) (`relogmuld`), ln q is worked out
    /// (`ln_rational`), and ln(eᵏ) = k·ln e = k·1 (`relogexp`, `loge`).
    fn ln_piece(
        &mut self,
        t: &Term,
        value: Real,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let x = &t.children()[0];
        let inner = take!(self.valued(x, scope, facts)?);
        let Some((ratio, k)) = inner.value.rational_times_e() else {
            return Ok(Route::no("a logarithm of a number not q·eᵏ"));
        };
        let sx = self.rpn(x);
        let log = |r: &Rpn| t!(r, "clog", "cfv");
        let rational = take!(self.ln_rational(&ratio, scope, facts)?);
        // x is the ratio times eᵏ, as the logarithm takes it apart.
        let (written, is) = if k == 0 {
            (rational.ratio.clone(), inner.proof)
        } else {
            let power = match k {
                1 => t!("ceu"),
                _ => t!("ceu", numeral(k), "cexp", "co"),
            };
            let written = t!(&rational.ratio, &power, "cmul", "co");
            let same = take!(self.identity(&inner.canon, &written, scope, facts)?);
            let is = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &sx, "B" => &inner.canon, "C" => &written},
                &[&inner.proof, &same],
            );
            (written, is)
        };
        let carried = self.b.ap(
            "fveq2d",
            &binds! {"ph" => scope, "A" => &sx, "B" => &written, "F" => "clog"},
            &[&is],
        );
        let (expression, logged) = if k == 0 {
            (rational.expression, rational.proof)
        } else {
            let power = match k {
                1 => t!("ceu"),
                _ => t!("ceu", numeral(k), "cexp", "co"),
            };
            let e_rp = self.closed_law(&t!("ceu", "crp", "wcel"), "epr", scope);
            let k_spelt = numeral(k);
            let k_z = self.numeral_fact(&t!(&k_spelt, "cz", "wcel"), scope, facts)?;
            let power_rp = if k == 1 {
                e_rp.clone()
            } else {
                self.b.ap(
                    "rpexpcld",
                    &binds! {"ph" => scope, "A" => "ceu", "N" => &k_spelt},
                    &[&e_rp, &k_z],
                )
            };
            let ratio_rp = self.positive(&rational.ratio, scope, facts)?;
            let split = self.b.ap(
                "relogmuld",
                &binds! {"ph" => scope, "A" => &rational.ratio, "B" => &power},
                &[&ratio_rp, &power_rp],
            );
            let one = t!("c1");
            let log_e =
                self.closed_law(&t!(log(&t!("ceu")), &one, "wceq"), "loge", scope);
            let (e_part, e_logged) = if k == 1 {
                (one.clone(), log_e)
            } else {
                let law =
                    self.b
                        .ap("relogexp", &binds! {"A" => "ceu", "N" => &k_spelt}, &[]);
                let times_log = t!(&k_spelt, log(&t!("ceu")), "cmul", "co");
                let down = self.b.ap(
                    "syl2anc",
                    &binds! {"ph" => scope, "ps" => t!("ceu", "crp", "wcel"), "ch" => t!(&k_spelt, "cz", "wcel"),
                    "th" => t!(log(&power), &times_log, "wceq")},
                    &[&e_rp, &k_z, &law],
                );
                let times_one = t!(&k_spelt, &one, "cmul", "co");
                let to_one = self.b.ap(
                    "oveq2d",
                    &binds! {"ph" => scope, "A" => log(&t!("ceu")), "B" => &one, "C" => &k_spelt, "F" => "cmul"},
                    &[&log_e],
                );
                let joined = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => log(&power), "B" => &times_log, "C" => &times_one},
                    &[&down, &to_one],
                );
                (times_one, joined)
            };
            let expression = t!(&rational.expression, &e_part, "caddc", "co");
            let both = self.b.ap(
                "oveq12d",
                &binds! {"ph" => scope, "A" => log(&rational.ratio), "B" => &rational.expression,
                "C" => log(&power), "D" => &e_part, "F" => "caddc"},
                &[&rational.proof, &e_logged],
            );
            let logged = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => log(&written),
                "B" => t!(log(&rational.ratio), log(&power), "caddc", "co"), "C" => &expression},
                &[&split, &both],
            );
            (expression, logged)
        };
        let worked = take!(self.made_canon(&expression, &value, scope, facts)?);
        let reached = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => log(&sx), "B" => log(&written), "C" => &expression},
            &[&carried, &logged],
        );
        let proof = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => log(&sx), "B" => &expression, "C" => &worked.canon},
            &[&reached, &worked.proof],
        );
        Ok(Built(Valued {
            value,
            canon: worked.canon,
            proof,
        }))
    }

    /// ( scope -> ( exp ` x ) = canon ) for x of value k + Σ nₚ·ln p: with r
    /// = Π p^nₚ, x is k + ln r, exp(k + ln r) = exp k · exp(ln r) (`efadd`),
    /// exp(ln r) = r (`reeflogd`), and exp k = (exp 1)ᵏ = eᵏ (`efexp`,
    /// `df-e`); exp 0 is 1 (`ef0`).
    fn exp_piece(
        &mut self,
        t: &Term,
        value: Real,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let x = &t.children()[0];
        let inner = take!(self.valued(x, scope, facts)?);
        let Some(reals::Logarithmic { constant, logs }) = inner.value.logarithmic()
        else {
            return Ok(Route::no("an exponential of a number not k + Σ nₚ·ln p"));
        };
        let Some(k) = constant
            .to_integer()
            .to_u32()
            .filter(|_| constant.is_integer())
        else {
            return Ok(Route::no(
                "an exponential of a number whose rational part is not whole",
            ));
        };
        let mut ratio = field::q(1);
        for (p, n) in &logs {
            let n = n.to_integer().to_i32().unwrap_or(0);
            ratio *= Q::from_integer(BigInt::from(*p)).pow(n);
        }
        let sx = self.rpn(x);
        let exp = |r: &Rpn| t!(r, "ce", "cfv");
        let k_spelt = numeral(k);
        // x as k + ln r, or the one of them it holds.
        let rational = if logs.is_empty() {
            None
        } else {
            Some(take!(self.ln_rational(&ratio, scope, facts)?))
        };
        let (written, is) = match &rational {
            None => (k_spelt.clone(), inner.proof.clone()),
            Some(l) => {
                let as_logs = if k == 0 {
                    l.expression.clone()
                } else {
                    t!(&k_spelt, &l.expression, "caddc", "co")
                };
                let written = if k == 0 {
                    t!(&l.ratio, "clog", "cfv")
                } else {
                    t!(&k_spelt, t!(&l.ratio, "clog", "cfv"), "caddc", "co")
                };
                let same =
                    take!(self.identity(&inner.canon, &as_logs, scope, facts)?);
                let back = self.b.ap(
                    "eqcomd",
                    &binds! {"ph" => scope, "A" => t!(&l.ratio, "clog", "cfv"), "B" => &l.expression},
                    &[&l.proof],
                );
                let folded = if k == 0 {
                    back
                } else {
                    self.b.ap(
                        "oveq2d",
                        &binds! {"ph" => scope, "A" => &l.expression, "B" => t!(&l.ratio, "clog", "cfv"),
                        "C" => &k_spelt, "F" => "caddc"},
                        &[&back],
                    )
                };
                let first = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &sx, "B" => &inner.canon, "C" => &as_logs},
                    &[&inner.proof, &same],
                );
                let is = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &sx, "B" => &as_logs, "C" => &written},
                    &[&first, &folded],
                );
                (written, is)
            }
        };
        let carried = self.b.ap(
            "fveq2d",
            &binds! {"ph" => scope, "A" => &sx, "B" => &written, "F" => "ce"},
            &[&is],
        );
        // exp k = eᵏ, and exp 0 = 1.
        let power = match k {
            0 => t!("c1"),
            1 => t!("ceu"),
            _ => t!("ceu", &k_spelt, "cexp", "co"),
        };
        let exp_k = if k == 0 {
            self.closed_law(&t!(exp(&t!("cc0")), "c1", "wceq"), "ef0", scope)
        } else {
            self.exp_whole(&k_spelt, &power, scope, facts)?
        };
        let (expression, valued) = match &rational {
            None => (power.clone(), exp_k),
            Some(l) => {
                let r_rp = self.positive(&l.ratio, scope, facts)?;
                let back = self.b.ap(
                    "reeflogd",
                    &binds! {"ph" => scope, "A" => &l.ratio},
                    &[&r_rp],
                );
                if k == 0 {
                    (l.ratio.clone(), back)
                } else {
                    let log_r = t!(&l.ratio, "clog", "cfv");
                    let k_cc =
                        self.numeral_fact(&t!(&k_spelt, "cc", "wcel"), scope, facts)?;
                    let log_real = self.b.ap(
                        "relogcld",
                        &binds! {"ph" => scope, "A" => &l.ratio},
                        &[&r_rp],
                    );
                    let log_cc = self.b.ap(
                        "recnd",
                        &binds! {"ph" => scope, "A" => &log_r},
                        &[&log_real],
                    );
                    let law = self.b.ap(
                        "efadd",
                        &binds! {"A" => &k_spelt, "B" => &log_r},
                        &[],
                    );
                    let split = self.b.ap(
                        "syl2anc",
                        &binds! {"ph" => scope, "ps" => t!(&k_spelt, "cc", "wcel"), "ch" => t!(&log_r, "cc", "wcel"),
                        "th" => t!(exp(&written), t!(exp(&k_spelt), exp(&log_r), "cmul", "co"), "wceq")},
                        &[&k_cc, &log_cc, &law],
                    );
                    let both = self.b.ap(
                        "oveq12d",
                        &binds! {"ph" => scope, "A" => exp(&k_spelt), "B" => &power,
                        "C" => exp(&log_r), "D" => &l.ratio, "F" => "cmul"},
                        &[&exp_k, &back],
                    );
                    let expression = t!(&power, &l.ratio, "cmul", "co");
                    let joined = self.b.ap(
                        "eqtrd",
                        &binds! {"ph" => scope, "A" => exp(&written),
                        "B" => t!(exp(&k_spelt), exp(&log_r), "cmul", "co"), "C" => &expression},
                        &[&split, &both],
                    );
                    (expression, joined)
                }
            }
        };
        let worked = take!(self.made_canon(&expression, &value, scope, facts)?);
        let reached = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => exp(&sx), "B" => exp(&written), "C" => &expression},
            &[&carried, &valued],
        );
        let proof = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => exp(&sx), "B" => &expression, "C" => &worked.canon},
            &[&reached, &worked.proof],
        );
        Ok(Built(Valued {
            value,
            canon: worked.canon,
            proof,
        }))
    }

    /// ( scope -> ( exp ` k ) = e^k ) for a whole k of at least 1: k is k·1,
    /// exp(k·1) = (exp 1)ᵏ (`efexp`), and exp 1 is e (`df-e`).
    fn exp_whole(
        &mut self,
        k: &Rpn,
        power: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let exp = |r: &Rpn| t!(r, "ce", "cfv");
        let one = t!("c1");
        let times_one = t!(k, &one, "cmul", "co");
        let counted = self.numeral_fact(&t!(k, &times_one, "wceq"), scope, facts)?;
        let carried = self.b.ap(
            "fveq2d",
            &binds! {"ph" => scope, "A" => k, "B" => &times_one, "F" => "ce"},
            &[&counted],
        );
        let one_cc = self.numeral_fact(&t!(&one, "cc", "wcel"), scope, facts)?;
        let k_z = self.numeral_fact(&t!(k, "cz", "wcel"), scope, facts)?;
        let law = self.b.ap("efexp", &binds! {"A" => &one, "N" => k}, &[]);
        let raised = t!(exp(&one), k, "cexp", "co");
        let grown = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(&one, "cc", "wcel"), "ch" => t!(k, "cz", "wcel"),
            "th" => t!(exp(&times_one), &raised, "wceq")},
            &[&one_cc, &k_z, &law],
        );
        // e is exp 1, by its definition, turned.
        let defined = self.b.ap(
            "eqcomi",
            &binds! {"A" => "ceu", "B" => exp(&one)},
            &[&self.step("df-e")],
        );
        let named = self.b.ap(
            "a1i",
            &binds! {"ph" => t!(exp(&one), "ceu", "wceq"), "ps" => scope},
            &[&defined],
        );
        let e_power = t!("ceu", k, "cexp", "co");
        let to_e = self.b.ap(
            "oveq1d",
            &binds! {"ph" => scope, "A" => exp(&one), "B" => "ceu", "C" => k, "F" => "cexp"},
            &[&named],
        );
        let first = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => exp(k), "B" => exp(&times_one), "C" => &raised},
            &[&carried, &grown],
        );
        let to_power = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => exp(k), "B" => &raised, "C" => &e_power},
            &[&first, &to_e],
        );
        if *power == e_power {
            return Ok(to_power);
        }
        // e¹ is written e.
        let e_cc = self.closed_law(&t!("ceu", "cr", "wcel"), "ere", scope);
        let e_cc = self
            .b
            .ap("recnd", &binds! {"ph" => scope, "A" => "ceu"}, &[&e_cc]);
        let unit = self
            .b
            .ap("exp1d", &binds! {"ph" => scope, "A" => "ceu"}, &[&e_cc]);
        Ok(self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => exp(k), "B" => &e_power, "C" => power},
            &[&to_power, &unit],
        ))
    }

    /// ( scope -> canon =/= 0 ) for the canon of D = Σ qₚ·ln p, rational
    /// multiples of logarithms of primes and not all 0. With N the least
    /// whole number making each N·qₚ whole and r = Π p^(N·qₚ), D·N is ln r
    /// (an identity, and `ln_rational`), ln r ≠ 0 as r ≠ 1 (`logne0`), and
    /// so D ≠ 0 (`mulne0bad`).
    fn ln_apart(
        &mut self,
        canon_of: &Rpn,
        value: &Real,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let Some(reals::Logarithmic { logs, .. }) = value.logarithmic() else {
            return Ok(Route::no("a difference that is not logarithms of primes"));
        };
        let scale = logs.values().fold(BigInt::one(), |d, v| d.lcm(v.denom()));
        let mut ratio = field::q(1);
        for (p, weight) in &logs {
            let n = (weight * Q::from_integer(scale.clone())).to_integer();
            let Some(n) = n.to_i32() else {
                return Ok(Route::no("a multiple of a logarithm too large"));
            };
            ratio *= Q::from_integer(BigInt::from(*p)).pow(n);
        }
        let logged = take!(self.ln_rational(&ratio, scope, facts)?);
        let n = numerals::spell(scale.magnitude().clone());
        let product = t!(canon_of, &n, "cmul", "co");
        let is = take!(self.identity(&product, &logged.expression, scope, facts)?);
        let log_r = t!(&logged.ratio, "clog", "cfv");
        let back = self.b.ap(
            "eqcomd",
            &binds! {"ph" => scope, "A" => &log_r, "B" => &logged.expression},
            &[&logged.proof],
        );
        let is_log = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &product, "B" => &logged.expression, "C" => &log_r},
            &[&is, &back],
        );
        let r_rp = self.positive(&logged.ratio, scope, facts)?;
        let r_apart =
            self.numeral_fact(&t!(&logged.ratio, "c1", "wne"), scope, facts)?;
        let law = self.b.ap("logne0", &binds! {"A" => &logged.ratio}, &[]);
        let log_apart = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(&logged.ratio, "crp", "wcel"), "ch" => t!(&logged.ratio, "c1", "wne"),
            "th" => t!(&log_r, "cc0", "wne")},
            &[&r_rp, &r_apart, &law],
        );
        let product_apart = self.b.ap(
            "eqnetrd",
            &binds! {"ph" => scope, "A" => &product, "B" => &log_r, "C" => "cc0"},
            &[&is_log, &log_apart],
        );
        let value_cc = take!(self.in_cc(canon_of, scope, facts)?);
        let n_cc = self.numeral_fact(&t!(&n, "cc", "wcel"), scope, facts)?;
        Ok(Built(self.b.ap(
            "mulne0bad",
            &binds! {"ph" => scope, "A" => canon_of, "B" => &n},
            &[&value_cc, &n_cc, &product_apart],
        )))
    }

    /// ( scope -> ( f ` x ) = canon ) for f sine or cosine and x of value
    /// q·π: with q = 2k + r, 0 ≤ r < 2, x is a(r) + k·(2·π), or a(r) where k
    /// is 0 (`angle_form`), by an identity; a turn is taken off (`sinper`,
    /// `cosper`), the rest reduced to set.mm's values (`trig_reduced`), and
    /// what a value lemma says brought to the canon.
    fn trig_piece(
        &mut self,
        t: &Term,
        f: reals::Trig,
        value: Real,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let x = &t.children()[0];
        let inner = take!(self.valued(x, scope, facts)?);
        let Some(multiple) = reals::multiple_of_pi(&inner.value) else {
            return Ok(Route::no("an angle that is not a multiple of π"));
        };
        let r = reals::turned(&multiple);
        let turns = ((&multiple - &r) / field::q(2)).to_integer();
        let Some(turns) = turns.to_i64() else {
            return Ok(Route::no("an angle of too many turns"));
        };
        let label = trig_label(f);
        let apply = |a: &Rpn| t!(a, label, "cfv");
        let base = angle_form(&r);
        let written = if turns == 0 {
            base.clone()
        } else {
            t!(
                &base,
                t!(
                    spelt_whole(turns),
                    t!("c2", "cpi", "cmul", "co"),
                    "cmul",
                    "co"
                ),
                "caddc",
                "co"
            )
        };
        let sx = self.rpn(x);
        let same = if inner.canon == written {
            self.b
                .ap("eqidd", &binds! {"ph" => scope, "A" => &written}, &[])
        } else {
            take!(self.identity(&inner.canon, &written, scope, facts)?)
        };
        let is = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &sx, "B" => &inner.canon, "C" => &written},
            &[&inner.proof, &same],
        );
        let carried = self.b.ap(
            "fveq2d",
            &binds! {"ph" => scope, "A" => &sx, "B" => &written, "F" => label},
            &[&is],
        );
        // A turn taken off.
        let at_base = if turns == 0 {
            carried
        } else {
            let base_cc = take!(self.in_cc(&base, scope, facts)?);
            let k = spelt_whole(turns);
            let k_z = self.numeral_fact(&t!(&k, "cz", "wcel"), scope, facts)?;
            let periodic = match f {
                reals::Trig::Sine => "sinper",
                reals::Trig::Cosine => "cosper",
            };
            let law = self.b.ap(periodic, &binds! {"A" => &base, "K" => &k}, &[]);
            let turned = self.b.ap(
                "syl2anc",
                &binds! {"ph" => scope, "ps" => t!(&base, "cc", "wcel"), "ch" => t!(&k, "cz", "wcel"),
                "th" => t!(apply(&written), apply(&base), "wceq")},
                &[&base_cc, &k_z, &law],
            );
            self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => apply(&sx), "B" => apply(&written), "C" => apply(&base)},
                &[&carried, &turned],
            )
        };
        let (said, reduced) = take!(self.trig_reduced(f, &r, scope, facts)?);
        let reached = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => apply(&sx), "B" => apply(&base), "C" => &said},
            &[&at_base, &reduced],
        );
        let worked = take!(self.valued(&self.to_term(&said), scope, facts)?);
        let proof = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => apply(&sx), "B" => &said, "C" => &worked.canon},
            &[&reached, &worked.proof],
        );
        debug_assert_eq!(
            worked.value, value,
            "the reduction comes to the decider's value"
        );
        Ok(Built(Valued {
            value,
            canon: worked.canon,
            proof,
        }))
    }

    /// ( scope -> ( f ` a(r) ) = v ) for 0 ≤ r < 2 and v what set.mm's lemmas
    /// say: a π taken off (`sinppi`, `cosppi`), then π/2 (`sinhalfpip`,
    /// `coshalfpip`), and the value at 0, π/6, π/4 or π/3 (`sin0`, `cos0`,
    /// `sincos6thpi`, `sincos4thpi`, `sincos3rdpi`).
    fn trig_reduced(
        &mut self,
        f: reals::Trig,
        r: &Q,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<(Rpn, Proof)>> {
        use reals::Trig::{Cosine, Sine};
        let half = Q::new(BigInt::from(1), BigInt::from(2));
        let apply = |g: reals::Trig, a: &Rpn| t!(a, trig_label(g), "cfv");
        let angle = angle_form(r);
        // A π or a π/2 off: the lemma, the function and angle it leaves, and
        // whether it negates.
        let step = if *r >= field::q(1) {
            let rest = r - field::q(1);
            let lemma = match f {
                Sine => "sinppi",
                Cosine => "cosppi",
            };
            Some((lemma, f, rest, true))
        } else if *r >= half {
            let rest = r - &half;
            match f {
                Sine => Some(("sinhalfpip", Cosine, rest, false)),
                Cosine => Some(("coshalfpip", Sine, rest, true)),
            }
        } else {
            None
        };
        let Some((lemma, then, rest, negates)) = step else {
            return Ok(Built(self.trig_base(f, r, scope)));
        };
        let left = angle_form(&rest);
        let left_cc = take!(self.in_cc(&left, scope, facts)?);
        let shifted = if negates {
            t!(apply(then, &left), "cneg")
        } else {
            apply(then, &left)
        };
        let law = self.b.ap(lemma, &binds! {"A" => &left}, &[]);
        let moved = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(&left, "cc", "wcel"), "ch" => t!(apply(f, &angle), &shifted, "wceq")},
            &[&left_cc, &law],
        );
        let (below, proof) = take!(self.trig_reduced(then, &rest, scope, facts)?);
        let (said, carried) = if negates {
            let carried = self.b.ap(
                "negeqd",
                &binds! {"ph" => scope, "A" => apply(then, &left), "B" => &below},
                &[&proof],
            );
            (t!(&below, "cneg"), carried)
        } else {
            (below, proof)
        };
        let joined = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => apply(f, &angle), "B" => &shifted, "C" => &said},
            &[&moved, &carried],
        );
        Ok(Built((said, joined)))
    }

    /// ( scope -> ( f ` a ) = v ) for a = 0, π/6, π/4 or π/3, from set.mm's
    /// statement of the value, the one of its two halves that names f.
    fn trig_base(&mut self, f: reals::Trig, r: &Q, scope: &Rpn) -> (Rpn, Proof) {
        use reals::Trig::{Cosine, Sine};
        let apply = |g: reals::Trig, a: &Rpn| t!(a, trig_label(g), "cfv");
        let over = |top: Rpn, d: &str| t!(top, d, "cdiv", "co");
        let root = |p: &str| t!(p, "csqrt", "cfv");
        let twelfths = (r * field::q(12)).to_integer().to_i64().unwrap_or(-1);
        let angle = angle_form(r);
        if twelfths == 0 {
            let (value, label) = match f {
                Sine => (t!("cc0"), "sin0"),
                Cosine => (t!("c1"), "cos0"),
            };
            let proof =
                self.closed_law(&t!(apply(f, &angle), &value, "wceq"), label, scope);
            return (value, proof);
        }
        let (label, sine, cosine) = match twelfths {
            2 => ("sincos6thpi", over(t!("c1"), "c2"), over(root("c3"), "c2")),
            // set.mm writes both values at π/4 as 1/√2.
            3 => (
                "sincos4thpi",
                t!("c1", root("c2"), "cdiv", "co"),
                t!("c1", root("c2"), "cdiv", "co"),
            ),
            _ => ("sincos3rdpi", over(root("c3"), "c2"), over(t!("c1"), "c2")),
        };
        let first = t!(apply(Sine, &angle), &sine, "wceq");
        let second = t!(apply(Cosine, &angle), &cosine, "wceq");
        let (half, value, claim) = match f {
            Sine => ("simpli", sine, first.clone()),
            Cosine => ("simpri", cosine, second.clone()),
        };
        let taken = self.b.ap(
            half,
            &binds! {"ph" => &first, "ps" => &second},
            &[&self.step(label)],
        );
        let proof =
            self.b
                .ap("a1i", &binds! {"ph" => &claim, "ps" => scope}, &[&taken]);
        (value, proof)
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
        if let Built(surds::Value::Exact(v)) = surds::closed_value(term) {
            out.extend(v.primes());
        }
    }
    for kid in term.children() {
        collect_primes(kid, out);
    }
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

/// The canon of a value: a rational as `arithmetic` writes it, and any
/// other value with whole coefficients as its parts added from the left,
/// in the order of their atoms (none first, then π, e, ln 2, ln 3 and on)
/// and then by the product under the root, each part its coefficient times
/// the product of its roots and its atoms' powers. A value with a
/// coefficient that is not whole is that sum for its multiple by the least
/// common denominator, over the denominator: the normaliser adds fractions
/// without cancelling, so a sum of eight parts each over the same N is
/// read over N⁸, and one over N is read over N.
fn canon(value: &Real) -> Rpn {
    if let Some(rational) = value.as_surd().and_then(|s| s.as_rational()) {
        return spelt_rational(&rational);
    }
    let common = value
        .weights()
        .iter()
        .fold(BigInt::one(), |d, v| d.lcm(v.denom()));
    if common.is_one() {
        return whole_canon(value);
    }
    let whole = value.times(&Real::rational(Q::from_integer(common.clone())));
    t!(
        whole_canon(&whole),
        numerals::spell(common.magnitude().clone()),
        "cdiv",
        "co"
    )
}

/// The canon of a value with whole coefficients.
fn whole_canon(value: &Real) -> Rpn {
    let mut out: Option<Rpn> = None;
    for (monomial, surd) in &value.parts {
        let mut parts: Vec<(&Vec<u64>, &Q)> = surd.parts.iter().collect();
        parts.sort_by_key(|(basis, _)| {
            basis.iter().map(|p| *p as u128).product::<u128>()
        });
        for (basis, weight) in parts {
            let coefficient = spelt_rational(weight);
            let mut factors: Vec<Rpn> =
                basis.iter().map(|p| root_of_prime(*p)).collect();
            factors.extend(monomial.iter().map(|(atom, k)| match k {
                1 => spelt_atom(*atom),
                _ => t!(spelt_atom(*atom), numeral(*k), "cexp", "co"),
            }));
            let part = match right_product(factors) {
                None => coefficient,
                Some(rest) => t!(coefficient, rest, "cmul", "co"),
            };
            out = Some(match out {
                None => part,
                Some(sum) => t!(sum, part, "caddc", "co"),
            });
        }
    }
    out.unwrap_or_else(|| numeral(0))
}

/// A whole number as a term: a numeral, negated where it is below 0.
fn spelt_whole(n: i64) -> Rpn {
    let size = numerals::spell(n.unsigned_abs());
    if n < 0 {
        t!(size, "cneg")
    } else {
        size
    }
}

/// set.mm's function for sin or cos.
fn trig_label(f: reals::Trig) -> &'static str {
    match f {
        reals::Trig::Sine => "csin",
        reals::Trig::Cosine => "ccos",
    }
}

/// The angle r·π, 0 ≤ r < 2, as the reduction takes it apart (`trig_reduced`):
/// 0, π/6, π/4 or π/3 below π/2; (π/2) + a(r − 1/2) from π/2 to π; and
/// a(r − 1) + π from π to 2π.
fn angle_form(r: &Q) -> Rpn {
    let half = Q::new(BigInt::from(1), BigInt::from(2));
    if *r >= field::q(1) {
        return t!(angle_form(&(r - field::q(1))), "cpi", "caddc", "co");
    }
    if *r >= half {
        return t!(
            t!("cpi", "c2", "cdiv", "co"),
            angle_form(&(r - &half)),
            "caddc",
            "co"
        );
    }
    match (r * field::q(12)).to_integer().to_i64() {
        Some(2) => t!("cpi", "c6", "cdiv", "co"),
        Some(3) => t!("cpi", "c4", "cdiv", "co"),
        Some(4) => t!("cpi", "c3", "cdiv", "co"),
        _ => t!("cc0"),
    }
}

/// f₁·(f₂·(…)), or None for no factors.
fn right_product(factors: Vec<Rpn>) -> Option<Rpn> {
    let mut factors = factors.into_iter().rev();
    let last = factors.next()?;
    Some(factors.fold(last, |rest, f| t!(f, rest, "cmul", "co")))
}

/// An atom as set.mm spells it: `_pi`, `_e`, or ( log ` p ).
fn spelt_atom(atom: Atom) -> Rpn {
    match atom {
        Atom::Pi => t!("cpi"),
        Atom::E => t!("ceu"),
        Atom::Ln(p) => t!(numerals::spell(p), "clog", "cfv"),
    }
}

/// Every atom a value of the term or of a part of it holds, and π and e
/// wherever the term writes them.
fn atoms_under(term: &Term) -> Vec<Atom> {
    let mut out = Vec::new();
    collect_atoms(term, &mut out);
    out.sort();
    out.dedup();
    out
}

fn collect_atoms(term: &Term, out: &mut Vec<Atom>) {
    if term.variable().is_some() || !reals::holds_atom(term) {
        return;
    }
    if let Built(reals::Value::Exact(v)) = reals::closed_value(term) {
        out.extend(v.atoms());
    }
    match term.label() {
        Some("cpi") => out.push(Atom::Pi),
        Some("ceu") => out.push(Atom::E),
        _ => {}
    }
    for kid in term.children() {
        collect_atoms(kid, out);
    }
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
