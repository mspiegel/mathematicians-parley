//! What each claim is, worked out by the test alone: the oracle a method's
//! answer is compared with. It shares no code with the tools, so a fault in
//! a method is not a fault here too; it follows `METHODS.md` as written,
//! refusals included, so a method that departs from the document is found
//! either way.

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::gen::{Claim, Expr, Rel, System};

/// What the oracle says of a claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The method takes the claim, and it holds or fails.
    Holds(bool),
    /// `METHODS.md` says the method refuses the claim, with the words its
    /// refusal is reported in. A claim may hold more than one part it
    /// refuses, a division by zero and a remainder of a negative number, and
    /// the method may report any of them.
    Refused(Vec<&'static str>),
}

/// `arithmetic`'s refusals (`METHODS.md`, "Refusals"), each as the tools
/// word it.
pub const DIVIDES_BY_ZERO: &str = "divides by zero";
pub const REMAINDER: &str =
    "is a remainder arithmetic works out only of a whole number";
pub const DIVISIBILITY: &str =
    "is a divisibility arithmetic decides only of whole numbers";

/// A term's value, or the refusal that stops it.
fn value(e: &Expr) -> Result<BigRational, &'static str> {
    let two =
        |a: &Expr, b: &Expr| -> Result<(BigRational, BigRational), &'static str> {
            Ok((value(a)?, value(b)?))
        };
    Ok(match e {
        Expr::Num(n) => BigRational::from_integer(n.clone()),
        Expr::Neg(a) => -value(a)?,
        Expr::Add(a, b) => {
            let (a, b) = two(a, b)?;
            a + b
        }
        Expr::Sub(a, b) => {
            let (a, b) = two(a, b)?;
            a - b
        }
        Expr::Mul(a, b) => {
            let (a, b) = two(a, b)?;
            a * b
        }
        Expr::Div(a, b) => {
            let (a, b) = two(a, b)?;
            if b.is_zero() {
                return Err(DIVIDES_BY_ZERO);
            }
            a / b
        }
        Expr::Pow(a, k) => {
            let a = value(a)?;
            let mut out = BigRational::one();
            for _ in 0..*k {
                out *= &a;
            }
            out
        }
        // x mod n is worked out where x is a whole number and n one of at
        // least 1.
        Expr::Mod(a, b) => {
            let (a, b) = two(a, b)?;
            let (Some(x), Some(n)) = (whole(&a), whole(&b)) else {
                return Err(REMAINDER);
            };
            if n < BigInt::one() {
                return Err(REMAINDER);
            }
            BigRational::from_integer(x.mod_floor(&n))
        }
    })
}

/// The value as a whole number, nought or more, where it is one.
fn whole(v: &BigRational) -> Option<BigInt> {
    (v.is_integer() && !v.is_negative()).then(|| v.to_integer())
}

/// Whether d divides n, each a whole number and d at least 1.
fn divides(d: &BigRational, n: &BigRational) -> Result<bool, &'static str> {
    match (whole(d), whole(n)) {
        (Some(d), Some(n)) if d >= BigInt::one() => Ok((n % d).is_zero()),
        _ => Err(DIVISIBILITY),
    }
}

/// What `arithmetic` should make of the claim (`METHODS.md`, arithmetic).
pub fn arithmetic(c: &Claim) -> Verdict {
    let decided = || -> Result<bool, &'static str> {
        Ok(match c {
            Claim::Rel(rel, a, b) => {
                let (a, b) = (value(a)?, value(b)?);
                match rel {
                    Rel::Eq => a == b,
                    Rel::Ne => a != b,
                    Rel::Lt => a < b,
                    Rel::Le => a <= b,
                    Rel::Gt => a > b,
                    Rel::Ge => a >= b,
                }
            }
            Claim::Member(a, system, inside) => {
                let v = value(a)?;
                let is = match system {
                    System::Nat => v.is_integer() && v.is_positive(),
                    System::Nat0 => v.is_integer() && !v.is_negative(),
                    System::Int => v.is_integer(),
                    System::Rat | System::Real => true,
                };
                is == *inside
            }
            Claim::Divides(d, n, said) => divides(&value(d)?, &value(n)?)? == *said,
            // "n is even" is 2 divides n, and "n is odd" its denial.
            Claim::Parity(n, even) => {
                let two = BigRational::from_integer(BigInt::from(2));
                divides(&two, &value(n)?)? == *even
            }
            // a ≡ b (mod n) is n divides a − b.
            Claim::Congruent(a, b, n) => divides(&value(n)?, &(value(a)? - value(b)?))?,
        })
    };
    match decided() {
        Ok(holds) => Verdict::Holds(holds),
        Err(first) => {
            let mut all = vec![first];
            for e in claim_terms(c) {
                refusals(e, &mut all);
            }
            Verdict::Refused(all)
        }
    }
}

/// The terms a claim is said of.
fn claim_terms(c: &Claim) -> Vec<&Expr> {
    match c {
        Claim::Rel(_, a, b) => vec![a, b],
        Claim::Member(a, _, _) => vec![a],
        Claim::Divides(d, n, _) => vec![d, n],
        Claim::Parity(n, _) => vec![n],
        Claim::Congruent(a, b, n) => vec![a, b, n],
    }
}

/// Each refusal some part of `e` is stopped by, wherever it stands.
fn refusals(e: &Expr, out: &mut Vec<&'static str>) {
    if let Err(why) = value(e) {
        if !out.contains(&why) {
            out.push(why);
        }
    }
    match e {
        Expr::Num(_) => {}
        Expr::Neg(a) | Expr::Pow(a, _) => refusals(a, out),
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Mod(a, b) => {
            refusals(a, out);
            refusals(b, out);
        }
    }
}
