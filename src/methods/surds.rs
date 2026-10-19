//! Closed facts about square roots of rationals, as `METHODS.md` has
//! `real arithmetic`.
//!
//! A value is a sum of rational multiples of square roots of squarefree
//! whole numbers, each root held as the primes it is the product of:
//! √12 − 1/√3 is 2·√3 − 1/3·√3, which is 5/3·√3. Two values are equal when
//! their parts are, because the square roots of distinct squarefree numbers
//! are linearly independent over ℚ; so `=` and `≠` are decided completely.
//! An order or a membership of ℕ, ℕ₀, ℤ or ℚ is decided only where the
//! values are rational: that √2 is not in ℚ is a theorem a reader names,
//! and is not worked out here.
//!
//! What has no square root in it is `arithmetic`'s, and its value is read
//! by `field::closed_value`; this module adds the roots and nothing else.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

use super::field::{self, q, ADD, DIV, EXP, MUL, NEG, Q, SUB};
use crate::mm::kernel::Term;
use crate::outcome::{Built, Declined, Route};
use crate::rules::System;

/// A radicand whose numerator times denominator is longer than this many
/// bits is not worked out: its squarefree part is found by trial division,
/// which takes up to 2^20 divisions at this length.
pub const RADICAND_BITS: u64 = 40;

/// The most distinct primes a value may hold under its roots. Each prime
/// doubles how many parts a value can have, and a proof multiplies them
/// out.
pub const PRIMES: usize = 4;

/// Why a radicand is refused: set.mm's square root is taken in ℂ, so the
/// square root of a number below 0 is not a real number.
pub const BELOW_ZERO: &str =
    "takes the square root of a number below 0, which is not a real number";

/// Why a nested root is refused.
pub const NOT_RATIONAL: &str =
    "takes the square root of a number that is not rational, and real arithmetic takes roots of rationals only";

pub const TOO_LARGE: &str = "is too large to work out";

/// The primes whose product a root is the square root of, in ascending
/// order: the empty list is the root of 1, the rational part.
pub type Basis = Vec<u64>;

/// A value: a rational coefficient for each root, none of them zero.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Surd {
    pub parts: BTreeMap<Basis, Q>,
}

impl Surd {
    pub fn rational(value: Q) -> Surd {
        let mut parts = BTreeMap::new();
        if !value.is_zero() {
            parts.insert(Vec::new(), value);
        }
        Surd { parts }
    }

    /// The value where it is rational; None where it holds a root.
    pub fn as_rational(&self) -> Option<Q> {
        match self.parts.iter().collect::<Vec<_>>().as_slice() {
            [] => Some(Q::zero()),
            [(basis, value)] if basis.is_empty() => Some((*value).clone()),
            _ => None,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.parts.is_empty()
    }

    /// Every prime under a root of this value, in ascending order.
    pub fn primes(&self) -> Vec<u64> {
        let mut out: Vec<u64> = self.parts.keys().flatten().copied().collect();
        out.sort_unstable();
        out.dedup();
        out
    }

    fn put(&mut self, basis: Basis, weight: Q) {
        let held = self.parts.entry(basis.clone()).or_insert_with(Q::zero);
        *held += weight;
        if held.is_zero() {
            self.parts.remove(&basis);
        }
    }

    pub fn plus(&self, other: &Surd) -> Surd {
        let mut out = self.clone();
        for (basis, weight) in &other.parts {
            out.put(basis.clone(), weight.clone());
        }
        out
    }

    pub fn scaled(&self, by: &Q) -> Surd {
        let mut out = Surd::default();
        for (basis, weight) in &self.parts {
            out.put(basis.clone(), weight * by);
        }
        out
    }

    pub fn minus(&self, other: &Surd) -> Surd {
        self.plus(&other.scaled(&q(-1)))
    }

    /// The product: √m·√n is the product of the primes they share, times
    /// the root of the primes only one of them holds.
    pub fn times(&self, other: &Surd) -> Surd {
        let mut out = Surd::default();
        for (left, a) in &self.parts {
            for (right, b) in &other.parts {
                let (shared, apart) = joined(left, right);
                out.put(apart, a * b * Q::from_integer(BigInt::from(shared)));
            }
        }
        out
    }

    /// One over the value, which is not zero: multiplied by its conjugate
    /// in one prime, a value holds that prime no more, and once it holds
    /// none the product is rational (`cofactor`).
    pub fn recip(&self) -> Surd {
        let Cofactor { times, norm } = cofactor(self);
        times.scaled(&norm.recip())
    }

    pub fn power(&self, n: u64) -> Surd {
        let mut out = Surd::rational(q(1));
        for _ in 0..n {
            out = out.times(self);
        }
        out
    }

    /// The largest coefficient, in bits.
    fn size(&self) -> u64 {
        self.parts
            .values()
            .map(|v| v.numer().bits().max(v.denom().bits()))
            .max()
            .unwrap_or(0)
    }
}

/// The product of the primes two roots share, and the primes only one of
/// them holds: √(2·3)·√(3·5) is 3·√(2·5).
fn joined(left: &Basis, right: &Basis) -> (u64, Basis) {
    let mut shared: u64 = 1;
    let mut apart = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < left.len() || j < right.len() {
        match (left.get(i), right.get(j)) {
            (Some(a), Some(b)) if a == b => {
                shared *= a;
                i += 1;
                j += 1;
            }
            (Some(a), Some(b)) if a < b => {
                apart.push(*a);
                i += 1;
            }
            (Some(_), Some(b)) => {
                apart.push(*b);
                j += 1;
            }
            (Some(a), None) => {
                apart.push(*a);
                i += 1;
            }
            (None, Some(b)) => {
                apart.push(*b);
                j += 1;
            }
            (None, None) => unreachable!("the loop stops when both are spent"),
        }
    }
    (shared, apart)
}

/// What a value is multiplied by to make it rational, and the rational it
/// makes: the product of its conjugates, one prime at a time. For
/// a + b·√p, with a and b free of √p, the conjugate is a − b·√p and the
/// product a² − p·b².
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cofactor {
    pub times: Surd,
    pub norm: Q,
}

pub fn cofactor(value: &Surd) -> Cofactor {
    let mut times = Surd::rational(q(1));
    let mut at = value.clone();
    for p in value.primes() {
        let turned = conjugate(&at, p);
        times = times.times(&turned);
        at = at.times(&turned);
    }
    let norm = at
        .as_rational()
        .expect("a value times its conjugates in every prime is rational");
    Cofactor { times, norm }
}

/// The value with √p turned to −√p.
fn conjugate(value: &Surd, p: u64) -> Surd {
    let mut out = Surd::default();
    for (basis, weight) in &value.parts {
        let turned = if basis.contains(&p) {
            -weight.clone()
        } else {
            weight.clone()
        };
        out.put(basis.clone(), turned);
    }
    out
}

/// A rational's square root as c·√(p₁·…·pⱼ): the square part of its
/// numerator times its denominator, over the denominator, and the primes
/// left over once. √(1/2) is 1/2·√2, since 1·2 = 1²·2.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Root {
    pub coefficient: Q,
    pub primes: Basis,
}

/// The root of a rational of at least 0, or why it is refused.
pub fn root_of(value: &Q) -> Result<Root, &'static str> {
    if value.is_negative() {
        return Err(BELOW_ZERO);
    }
    let whole = value.numer() * value.denom();
    if whole.bits() > RADICAND_BITS {
        return Err(TOO_LARGE);
    }
    let mut left = whole.to_u64().expect("a radicand within RADICAND_BITS");
    let (mut square, mut primes) = (1u64, Vec::new());
    let mut p = 2u64;
    while p * p <= left {
        let mut times = 0;
        while left.is_multiple_of(p) {
            left /= p;
            times += 1;
        }
        square *= p.pow(times / 2);
        if times % 2 == 1 {
            primes.push(p);
        }
        p += 1;
    }
    if left > 1 {
        primes.push(left);
    }
    let coefficient =
        Q::from_integer(BigInt::from(square)) / Q::from_integer(value.denom().clone());
    Ok(Root {
        coefficient: if value.is_zero() {
            Q::zero()
        } else {
            coefficient
        },
        primes,
    })
}

/// What a closed term comes to: its value, or why it has none.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Exact(Surd),
    Unworked(&'static str),
}

/// Whether a term is set.mm's square root of something, `( sqrt ` A )`.
pub fn is_root(term: &Term) -> bool {
    term.variable().is_none()
        && term.label() == Some("cfv")
        && term.children().len() == 2
        && term.children()[1].label() == Some("csqrt")
}

/// Whether a term takes a square root anywhere in it.
pub fn takes_root(term: &Term) -> bool {
    term.variable().is_none()
        && (is_root(term) || term.children().iter().any(takes_root))
}

/// The value of a closed term built from numerals by the operations
/// `arithmetic` works out and square roots of rationals.
///
/// A part with no root is `arithmetic`'s and is read by
/// `field::closed_value`. A decline where the term is not built so.
pub fn closed_value(term: &Term) -> Route<Value> {
    if term.variable().is_some() {
        return Route::no("it holds a letter");
    }
    if !takes_root(term) {
        return match field::closed_value(term) {
            Built(field::Value::Exact(v)) => Built(Value::Exact(Surd::rational(v))),
            Built(field::Value::Unworked(why)) => Built(Value::Unworked(why)),
            Declined(d) => Declined(d),
        };
    }
    let kids = term.children();
    let value = if is_root(term) {
        let under = match closed_value(&kids[0]) {
            Built(Value::Exact(v)) => v,
            other => return other,
        };
        let Some(under) = under.as_rational() else {
            return Built(Value::Unworked(NOT_RATIONAL));
        };
        match root_of(&under) {
            Ok(root) => {
                let mut out = Surd::default();
                out.put(root.primes, root.coefficient);
                out
            }
            Err(why) => return Built(Value::Unworked(why)),
        }
    } else if term.label() == Some(NEG) && kids.len() == 1 {
        match closed_value(&kids[0]) {
            Built(Value::Exact(v)) => v.scaled(&q(-1)),
            other => return other,
        }
    } else if term.label() == Some("co") && kids.len() == 3 {
        let how = kids[2].label().unwrap_or("");
        let left = match closed_value(&kids[0]) {
            Built(Value::Exact(v)) => v,
            other => return other,
        };
        if how == EXP {
            return power(&left, &kids[1]);
        }
        let right = match closed_value(&kids[1]) {
            Built(Value::Exact(v)) => v,
            other => return other,
        };
        match how {
            ADD => left.plus(&right),
            SUB => left.minus(&right),
            MUL => left.times(&right),
            DIV if right.is_zero() => return Built(Value::Unworked("divides by zero")),
            DIV => left.times(&right.recip()),
            _ => return Route::no("not an operation real arithmetic reads"),
        }
    } else {
        return Route::no("not built from numerals and square roots");
    };
    held(value)
}

/// A value within the limits, or refused as too large.
fn held(value: Surd) -> Route<Value> {
    if value.primes().len() > PRIMES || value.size() > field::BITS {
        return Built(Value::Unworked(TOO_LARGE));
    }
    Built(Value::Exact(value))
}

/// A value raised to a whole exponent, which has no root in it: a negative
/// one is the power of one over the value.
fn power(base: &Surd, exponent: &Term) -> Route<Value> {
    let n = match closed_value(exponent) {
        Built(Value::Exact(v)) => v,
        other => return other,
    };
    let Some(n) = n.as_rational().filter(|n| n.is_integer()) else {
        return Built(Value::Unworked(
            "is a power real arithmetic works out only with a whole exponent",
        ));
    };
    let whole = n.to_integer();
    if base.is_zero() && whole.is_negative() {
        return Built(Value::Unworked("divides by zero"));
    }
    let magnitude = whole.magnitude().to_u64().unwrap_or(u64::MAX);
    let parts = base.parts.len().max(1) as u64;
    if (base.size() + parts).saturating_mul(magnitude) > field::BITS {
        return Built(Value::Unworked(TOO_LARGE));
    }
    let raised = base.power(magnitude);
    held(if whole.is_negative() {
        raised.recip()
    } else {
        raised
    })
}

/// What a closed claim comes to.
#[derive(Clone, Debug, PartialEq)]
pub enum Verdict {
    Holds(bool),
    /// A part of it has no value, and why.
    Unworked(&'static str),
    /// Each side has a value, and the relation between them is not one
    /// real arithmetic decides: an order or a membership where a value is
    /// not rational.
    Undecided(&'static str),
}

/// The number systems a rational value is tested for membership of.
fn system_test(system: System) -> fn(&Q) -> bool {
    match system {
        System::N => |v: &Q| v.is_integer() && v.is_positive(),
        System::N0 => |v: &Q| v.is_integer() && !v.is_negative(),
        System::Z => |v: &Q| v.is_integer(),
        System::Q | System::R | System::C => |_: &Q| true,
    }
}

/// Whether a relation between closed terms holds: `=` and `≠` of any
/// values, `<` and `≤` of rational ones, and membership of ℝ and ℂ of any
/// value and of ℕ, ℕ₀, ℤ and ℚ of a rational one; and the denial of each.
/// A decline where the claim is none of these or holds a letter.
pub fn decide_closed(claim: &Term) -> Route<Verdict> {
    let negated = claim.label() == Some("wn") && claim.children().len() == 1;
    let claim = if negated { &claim.children()[0] } else { claim };
    let kids = claim.children();
    let side = |t: &Term| match closed_value(t) {
        Built(Value::Exact(v)) => Ok(v),
        Built(Value::Unworked(why)) => Err(Built(Verdict::Unworked(why))),
        Declined(d) => Err(Declined(d)),
    };
    let holds = match claim.label() {
        Some("wceq" | "wne") if kids.len() == 2 => {
            let (a, b) = match (side(&kids[0]), side(&kids[1])) {
                (Ok(a), Ok(b)) => (a, b),
                (Err(stop), _) | (_, Err(stop)) => return stop,
            };
            (a == b) == (claim.label() == Some("wceq"))
        }
        Some("wbr")
            if kids.len() == 3 && matches!(kids[2].label(), Some("clt" | "cle")) =>
        {
            let (a, b) = match (side(&kids[0]), side(&kids[1])) {
                (Ok(a), Ok(b)) => (a, b),
                (Err(stop), _) | (_, Err(stop)) => return stop,
            };
            let (Some(a), Some(b)) = (a.as_rational(), b.as_rational()) else {
                return Built(Verdict::Undecided(
                    "is an order between numbers that are not both rational",
                ));
            };
            if kids[2].label() == Some("clt") {
                a < b
            } else {
                a <= b
            }
        }
        Some("wcel")
            if kids.len() == 2
                && kids[1].children().is_empty()
                && kids[1].label().and_then(System::of_label).is_some() =>
        {
            let system = System::of_label(kids[1].label().unwrap()).unwrap();
            let v = match side(&kids[0]) {
                Ok(v) => v,
                Err(stop) => return stop,
            };
            match (system, v.as_rational()) {
                (System::R | System::C, _) => true,
                (_, Some(v)) => system_test(system)(&v),
                (_, None) => {
                    return Built(Verdict::Undecided(
                        "is a membership of a number that is not rational, which is a theorem to cite",
                    ))
                }
            }
        }
        _ => return Route::no("not a relation real arithmetic decides"),
    };
    Built(Verdict::Holds(holds != negated))
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::One;

    fn unit() -> Surd {
        Surd::rational(Q::one())
    }

    fn root(n: i64, d: i64) -> Surd {
        let r = root_of(&(q(n) / q(d))).unwrap();
        let mut out = Surd::default();
        out.put(r.primes, r.coefficient);
        out
    }

    #[test]
    fn a_root_is_its_square_part_times_the_root_of_the_rest() {
        assert_eq!(
            root_of(&q(8)).unwrap(),
            Root {
                coefficient: q(2),
                primes: vec![2]
            }
        );
        assert_eq!(
            root_of(&(q(1) / q(2))).unwrap(),
            Root {
                coefficient: q(1) / q(2),
                primes: vec![2]
            }
        );
        assert_eq!(
            root_of(&q(36)).unwrap(),
            Root {
                coefficient: q(6),
                primes: vec![]
            }
        );
        assert_eq!(root_of(&q(0)).unwrap().coefficient, q(0));
        assert_eq!(root_of(&q(-2)), Err(BELOW_ZERO));
    }

    #[test]
    fn roots_multiply_by_the_primes_they_share() {
        assert_eq!(root(2, 1).times(&root(3, 1)), root(6, 1));
        assert_eq!(root(6, 1).times(&root(10, 1)), root(15, 1).scaled(&q(2)));
        assert_eq!(root(2, 1).times(&root(2, 1)), Surd::rational(q(2)));
    }

    #[test]
    fn one_over_a_value_times_the_value_is_one() {
        let x = unit().plus(&root(2, 1)).plus(&root(3, 1));
        assert_eq!(x.times(&x.recip()), unit());
        let Cofactor { times, norm } = cofactor(&x);
        assert_eq!(x.times(&times), Surd::rational(norm));
    }

    #[test]
    fn the_square_of_a_sum_of_three_roots() {
        let x = root(2, 1).plus(&root(3, 1)).plus(&root(5, 1));
        let want = Surd::rational(q(10))
            .plus(&root(6, 1).scaled(&q(2)))
            .plus(&root(10, 1).scaled(&q(2)))
            .plus(&root(15, 1).scaled(&q(2)));
        assert_eq!(x.power(2), want);
    }
}
