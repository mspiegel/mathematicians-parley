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

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

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

/// What a true claim may cost to prove (`proof_cost`). Each product of two
/// values the proof writes, of P and B parts, is an identity the
/// normaliser proves, and its proof restates the product at every move it
/// makes: it costs (P·B)³. Measured, (√2 + √3 + √5 + √7)⁴ costs some
/// 59 000 and peaks at 1.0 GB, 1/(1 + √2 + √3 + √5) ≠ 0 some 99 000 and
/// 0.8 GB, (√2 + √3 + √5 + √7)⁸ some 190 000 and 2.7 GB, and
/// 1/(1 + √2 + √3 + √5 + √7) ≠ 0 some 1 541 000 and 10.9 GB; this keeps a
/// claim under the build's 2 GB.
pub const WORK: u64 = 100_000;

/// The longest coefficient a proof may write, in bits. The normaliser
/// reads a numeral as a number only where it fits 64 bits, and as an atom
/// past that, so an identity holding a longer one does not come out.
pub const COEFFICIENT_BITS: u64 = 62;

/// Why a radicand is refused: set.mm's square root is taken in ℂ, so the
/// square root of a number below 0 is not a real number.
pub const BELOW_ZERO: &str =
    "takes the square root of a number below 0, which is not a real number";

/// Why a nested root is refused.
pub const NOT_RATIONAL: &str =
    "takes the square root of a number that is not rational, and real arithmetic takes roots of rationals only";

pub const TOO_LARGE: &str = "is too large to work out";

/// Why a membership of ℕ, ℕ₀, ℤ or ℚ is not decided.
pub const MEMBERSHIP_UNDECIDED: &str =
    "is a membership of a number that is not rational, which is a theorem to cite";

/// Whether `real arithmetic` works out the operations a notation record's
/// target applies: one `arithmetic` works out, or one whose record names
/// `real arithmetic` in its `decided` field, as `square-root` does.
pub fn worked_out(record: &crate::corpus::Record) -> bool {
    field::worked_out(record) || field::decides(record, "real arithmetic")
}

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
        // A conjugate in one prime may take another with it, as √21 in 3
        // takes 7: a prime the product no longer holds is passed over.
        if !at.primes().contains(&p) {
            continue;
        }
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

/// Two rationals a number lies strictly between.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bracket {
    pub below: Q,
    pub above: Q,
}

/// The bracket of √p for a prime p at a precision of j bits: ⌊2ʲ·√p⌋/2ʲ
/// and that plus 2⁻ʲ. Neither end is √p, which is not rational.
pub fn root_bracket(p: u64, precision: u32) -> Bracket {
    let scale = BigUint::one() << precision;
    let floor = (BigUint::from(p) * &scale * &scale).sqrt();
    let step = Q::new(BigInt::one(), BigInt::from(scale));
    let below = Q::from_integer(BigInt::from(floor)) * &step;
    Bracket {
        above: &below + step,
        below,
    }
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
    /// real arithmetic decides: an equation or an order the method cannot
    /// tell, or a membership where a value is not rational.
    Undecided(&'static str),
}

/// The number systems a rational value is tested for membership of.
pub(crate) fn system_test(system: System) -> fn(&Q) -> bool {
    match system {
        System::N => |v: &Q| v.is_integer() && v.is_positive(),
        System::N0 => |v: &Q| v.is_integer() && !v.is_negative(),
        System::Z => |v: &Q| v.is_integer(),
        System::Q | System::R | System::C => |_: &Q| true,
    }
}

/// Whether a relation between closed terms holds: `=` and `≠` of any
/// values, and membership of ℝ and ℂ of any value and of ℕ, ℕ₀, ℤ and ℚ
/// of a rational one; and the denial of each. An order is
/// `reals::decide_closed`'s, with or without atoms. A decline where the
/// claim is none of these or holds a letter.
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
                (_, None) => return Built(Verdict::Undecided(MEMBERSHIP_UNDECIDED)),
            }
        }
        _ => return Route::no("not a relation real arithmetic decides"),
    };
    let holds = holds != negated;
    if holds && takes_root(claim) {
        if let Err(why) = proof_cost(claim, negated) {
            return Built(Verdict::Unworked(why));
        }
    }
    Built(Verdict::Holds(holds))
}

/// Whether the proof of a true claim stays within [`WORK`] and writes no
/// coefficient past [`COEFFICIENT_BITS`]: each side's cost (`estimate`),
/// and for a disequality the difference of the sides and what shows it is
/// not zero.
fn proof_cost(claim: &Term, negated: bool) -> Result<(), &'static str> {
    let kids = claim.children();
    let sides: &[Term] = match claim.label() {
        Some("wcel") => &kids[..1],
        _ => &kids[..2],
    };
    let mut total = 0u64;
    let mut values = Vec::new();
    for side in sides {
        let side = estimate(side)?;
        total = total.saturating_add(side.cost);
        values.push(side.value);
    }
    let apart = match claim.label() {
        Some("wne") => !negated,
        Some("wceq") => negated,
        _ => false,
    };
    if apart {
        let gap = values[0].minus(&values[1]);
        written(&gap)?;
        total = total
            .saturating_add(cube(parts(&values[0]) + parts(&values[1])))
            .saturating_add(apart_cost(&gap)?);
    }
    if total > WORK {
        return Err(TOO_LARGE);
    }
    Ok(())
}

/// A term's value and what proving it equal to its canon costs, the sum of
/// the identities its proof writes, as `crate::elab::real` writes them.
struct Estimate {
    value: Surd,
    cost: u64,
}

/// What proving a term with no atom equal to its canon costs, or why it is
/// past the limits.
pub(crate) fn term_cost(term: &Term) -> Result<u64, &'static str> {
    estimate(term).map(|e| e.cost)
}

fn estimate(term: &Term) -> Result<Estimate, &'static str> {
    let Built(Value::Exact(value)) = closed_value(term) else {
        return Err(TOO_LARGE);
    };
    written(&value)?;
    if !takes_root(term) || is_root(term) {
        return Ok(Estimate { value, cost: 0 });
    }
    let kids = term.children();
    let cost = if term.label() == Some(NEG) {
        let x = estimate(&kids[0])?;
        x.cost.saturating_add(cube(parts(&x.value)))
    } else {
        let how = kids[2].label().unwrap_or("");
        let x = estimate(&kids[0])?;
        let y = estimate(&kids[1])?;
        let here = match how {
            ADD | SUB => cube(parts(&x.value) + parts(&y.value)),
            MUL => product_cost(&x.value, &y.value)?,
            DIV => quotient_cost(&x.value, &y.value)?,
            EXP => {
                let k = y
                    .value
                    .as_rational()
                    .filter(|k| k.is_integer())
                    .and_then(|k| k.to_integer().to_i64())
                    .ok_or(TOO_LARGE)?;
                power_cost(&x.value, k)?
            }
            _ => 0,
        };
        x.cost.saturating_add(y.cost).saturating_add(here)
    };
    Ok(Estimate { value, cost })
}

/// How many parts a value has, the value 0 counted as one.
fn parts(value: &Surd) -> u64 {
    value.parts.len().max(1) as u64
}

pub(crate) fn cube(n: u64) -> u64 {
    n.saturating_pow(3)
}

/// The longest numeral a canon writes whose coefficients are `weights`, in
/// bits: the least common denominator, and each coefficient times it.
pub(crate) fn weights_bits<'q>(weights: impl Iterator<Item = &'q Q> + Clone) -> u64 {
    let common = weights.clone().fold(BigInt::one(), |d, v| d.lcm(v.denom()));
    let scale = Q::from_integer(common.clone());
    weights
        .map(|v| (v * &scale).numer().bits())
        .max()
        .unwrap_or(0)
        .max(common.bits())
}

/// The least common denominator of a value's coefficients.
pub fn common_denominator(value: &Surd) -> BigUint {
    value
        .parts
        .values()
        .fold(BigUint::one(), |d, v| d.lcm(v.denom().magnitude()))
}

/// The longest numeral a value's canon writes, in bits: a rational's
/// numerator and denominator, and for any other value the common
/// denominator and each coefficient times it (`crate::elab::real`).
fn bits(value: &Surd) -> u64 {
    if value.as_rational().is_some() {
        return value.size();
    }
    weights_bits(value.parts.values())
}

/// The value, where its canon writes no coefficient past
/// [`COEFFICIENT_BITS`].
fn written(value: &Surd) -> Result<(), &'static str> {
    if bits(value) > COEFFICIENT_BITS {
        return Err(TOO_LARGE);
    }
    Ok(())
}

/// One part of a value as the bound on a product reads it: what the part
/// holds besides roots (nothing, for a value of this module; π, e and
/// logarithms for `reals`), its roots, and its coefficient.
pub(crate) struct Piece<K> {
    pub atoms: K,
    pub basis: Basis,
    pub weight: Q,
}

/// The pieces of a value with no atoms.
fn pieces(value: &Surd) -> Vec<Piece<()>> {
    value
        .parts
        .iter()
        .map(|(basis, weight)| Piece {
            atoms: (),
            basis: basis.clone(),
            weight: weight.clone(),
        })
        .collect()
}

/// The longest numeral the identity bringing a product of two canons to
/// the canon of their product writes, in bits. The expanded product has a
/// monomial for each pair of parts, a prime the two share squared in it,
/// and pairs of one monomial add. The multiple of (√p)² − p the identity
/// writes for a monomial is its coefficient times each shared prime but the
/// last taken out, times the least common denominator the identity scales
/// by, the product's own coefficients among those it takes; with a bit to
/// spare for multiples that add.
pub(crate) fn product_widest<K: Ord + Clone>(
    a: &[Piece<K>],
    b: &[Piece<K>],
    join: impl Fn(&K, &K) -> K,
    product: &[Q],
) -> u64 {
    let mut monomials: BTreeMap<(K, Basis, Basis), Q> = BTreeMap::new();
    for x in a {
        for y in b {
            let (once, twice) = squared_apart(&x.basis, &y.basis);
            let key = (join(&x.atoms, &y.atoms), once, twice);
            *monomials.entry(key).or_insert_with(Q::zero) += &x.weight * &y.weight;
        }
    }
    let scale = monomials
        .values()
        .chain(product)
        .fold(BigInt::one(), |d, v| d.lcm(v.denom()));
    let scale = Q::from_integer(scale);
    monomials
        .iter()
        .map(|((_, _, twice), w)| {
            let carried: u64 = twice.iter().rev().skip(1).product();
            (w * &scale * Q::from_integer(BigInt::from(carried)))
                .numer()
                .bits()
        })
        .max()
        .unwrap_or(0)
        + 1
}

/// The identity that brings a product of two canons to the canon of their
/// product, which must write no numeral past [`COEFFICIENT_BITS`]
/// (`product_widest`), and costs (P·B)³.
pub(crate) fn product_cost(a: &Surd, b: &Surd) -> Result<u64, &'static str> {
    let terms = parts(a) * parts(b);
    let product = a.times(b);
    let coefficients: Vec<Q> = product.parts.values().cloned().collect();
    if product_widest(&pieces(a), &pieces(b), |_, _| (), &coefficients)
        > COEFFICIENT_BITS
    {
        return Err(TOO_LARGE);
    }
    written(&product)?;
    Ok(cube(terms))
}

/// The primes one of two roots holds, and those both hold, which their
/// product holds squared.
fn squared_apart(left: &Basis, right: &Basis) -> (Basis, Basis) {
    let once: Basis = left
        .iter()
        .filter(|p| !right.contains(p))
        .chain(right.iter().filter(|p| !left.contains(p)))
        .copied()
        .collect();
    let mut once = once;
    once.sort_unstable();
    let twice: Basis = left.iter().filter(|p| right.contains(p)).copied().collect();
    (once, twice)
}

/// What shows a value is not zero: nothing for a rational, which
/// `arithmetic` decides, and otherwise the value times its cofactor.
pub(crate) fn apart_cost(value: &Surd) -> Result<u64, &'static str> {
    if value.as_rational().is_some() {
        return Ok(0);
    }
    let Cofactor { times, .. } = cofactor(value);
    written(&times)?;
    product_cost(value, &times)
}

/// A quotient: the divisor not zero, and the divisor times the quotient is
/// the dividend.
pub(crate) fn quotient_cost(top: &Surd, below: &Surd) -> Result<u64, &'static str> {
    if below.is_zero() {
        return Ok(0);
    }
    let quotient = top.times(&below.recip());
    written(&quotient)?;
    Ok(product_cost(below, &quotient)?.saturating_add(apart_cost(below)?))
}

/// A power built a step at a time, each step the power before times the
/// base; a negative exponent is one over the power.
pub(crate) fn power_cost(base: &Surd, k: i64) -> Result<u64, &'static str> {
    let mut cost = 0u64;
    let mut at = base.clone();
    for _ in 1..k.unsigned_abs() {
        cost = cost.saturating_add(product_cost(&at, base)?);
        at = at.times(base);
    }
    if k < 0 {
        let one = Surd::rational(q(1));
        cost = cost
            .saturating_add(apart_cost(base)?)
            .saturating_add(quotient_cost(&one, &at)?);
    }
    Ok(cost)
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn the_claims_measured_fall_on_their_side_of_the_limit() {
        let n = |d: &str| Term::apply(d, vec![]);
        let op = |a: Term, b: Term, o: &str| Term::apply("co", vec![a, b, n(o)]);
        let r = |d: &str| Term::apply("cfv", vec![n(d), n("csqrt")]);
        let three = op(op(op(n("c1"), r("c2"), ADD), r("c3"), ADD), r("c5"), ADD);
        let four = op(three.clone(), r("c7"), ADD);
        let apart = |d: Term| Term::apply("wne", vec![op(n("c1"), d, DIV), n("cc0")]);
        let roots = op(op(op(r("c2"), r("c3"), ADD), r("c5"), ADD), r("c7"), ADD);
        let power = |k: &str| {
            let raised = op(roots.clone(), n(k), EXP);
            let value = match closed_value(&raised) {
                Built(Value::Exact(v)) => v,
                _ => unreachable!("a power of roots has a value"),
            };
            let same = canon_term(&value);
            Term::apply("wceq", vec![raised, same])
        };
        assert_eq!(proof_cost(&apart(three), false), Ok(()));
        assert_eq!(proof_cost(&power("c4"), false), Ok(()));
        assert_eq!(proof_cost(&apart(four), false), Err(TOO_LARGE));
        assert_eq!(proof_cost(&power("c8"), false), Err(TOO_LARGE));
    }

    /// A value as a term, its parts added: what a claim states it equals.
    fn canon_term(value: &Surd) -> Term {
        let n = |d: &str| Term::apply(d, vec![]);
        let numeral = |v: &Q| {
            crate::methods::numerals::numeral_term(&v.to_integer().magnitude().clone())
        };
        value
            .parts
            .iter()
            .map(|(basis, weight)| {
                let roots = basis.iter().fold(None, |acc: Option<Term>, p| {
                    let root =
                        Term::apply("cfv", vec![numeral(&q(*p as i64)), n("csqrt")]);
                    Some(match acc {
                        None => root,
                        Some(a) => Term::apply("co", vec![a, root, n(MUL)]),
                    })
                });
                match roots {
                    None => numeral(weight),
                    Some(r) => Term::apply("co", vec![numeral(weight), r, n(MUL)]),
                }
            })
            .reduce(|a, b| Term::apply("co", vec![a, b, n(ADD)]))
            .expect("a value not zero")
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
