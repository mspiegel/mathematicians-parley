//! Closed facts about π, e and logarithms of rationals, with square roots
//! of rationals, as `METHODS.md` has `real arithmetic`.
//!
//! A value is a polynomial in the atoms π, e and ln p for primes p, its
//! coefficients values of `surds`: Σ sₘ·M, M a product of whole powers of
//! atoms. A logarithm of a positive rational is its numerator and
//! denominator factored, Σ nₚ·ln p, and of one times eᵏ that plus k; an
//! exponential of k + Σ nₚ·ln p, with k and every nₚ whole and k at least 0,
//! is eᵏ·Π p^nₚ. Two values are equal where their coefficients are. Where
//! they are not, the claim is decided only where the difference holds no
//! atom, or is rational multiples of logarithms of primes and nothing else,
//! which unique factorisation shows is not 0; any other difference is not
//! decided, never false.
//!
//! What holds none of these atoms is `surds`', and is decided there.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

use super::field::{q, ADD, DIV, EXP, MUL, NEG, Q, SUB};
use super::surds::{self, Piece, Surd, Verdict};
use crate::mm::kernel::Term;
use crate::outcome::{Built, Declined, Route};
use crate::rules::System;

/// Why a logarithm is refused: set.mm's log is taken in ℂ.
pub const LN_NOT_POSITIVE: &str =
    "takes the logarithm of a number not above 0, which is not a real number";

/// Why a logarithm of anything else is refused.
pub const LN_NOT_RATIONAL: &str =
    "takes the logarithm of a number that is neither a positive rational nor one times a whole power of e";

/// Why an exponential is refused.
pub const EXP_OUT_OF_RANGE: &str =
    "takes the exponential of a number that is not a whole number of at least 0 plus whole multiples of logarithms of primes";

/// Why a division is refused.
pub const DIVIDES_BY_ATOM: &str =
    "divides by a number holding π, e or a logarithm, which real arithmetic does not";

/// Why an equation or a disequality is not decided.
pub const NOT_DECIDED: &str =
    "relates numbers whose difference holds π, e or a logarithm otherwise than as multiples of logarithms of primes";

/// An atom of a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Atom {
    Pi,
    E,
    /// The natural logarithm of a prime.
    Ln(u64),
}

/// A product of whole powers of atoms, none of them 0; the empty one is 1.
pub type Monomial = BTreeMap<Atom, u32>;

/// A value: a coefficient for each monomial, none of them 0.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Real {
    pub parts: BTreeMap<Monomial, Surd>,
}

/// A value read as k + Σ qₚ·ln p: its rational part and each logarithm's
/// rational coefficient.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Logarithmic {
    pub constant: Q,
    pub logs: BTreeMap<u64, Q>,
}

impl Real {
    pub fn surd(value: Surd) -> Real {
        let mut out = Real::default();
        out.put(Monomial::new(), value);
        out
    }

    pub fn rational(value: Q) -> Real {
        Real::surd(Surd::rational(value))
    }

    pub fn atom(atom: Atom) -> Real {
        let mut out = Real::default();
        out.put(Monomial::from([(atom, 1)]), Surd::rational(q(1)));
        out
    }

    /// The value where it holds no atom.
    pub fn as_surd(&self) -> Option<Surd> {
        match self.parts.iter().collect::<Vec<_>>().as_slice() {
            [] => Some(Surd::default()),
            [(m, s)] if m.is_empty() => Some((*s).clone()),
            _ => None,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.parts.is_empty()
    }

    fn put(&mut self, monomial: Monomial, value: Surd) {
        let held = self.parts.entry(monomial.clone()).or_default();
        *held = held.plus(&value);
        if held.is_zero() {
            self.parts.remove(&monomial);
        }
    }

    pub fn plus(&self, other: &Real) -> Real {
        let mut out = self.clone();
        for (m, s) in &other.parts {
            out.put(m.clone(), s.clone());
        }
        out
    }

    pub fn negated(&self) -> Real {
        let mut out = Real::default();
        for (m, s) in &self.parts {
            out.put(m.clone(), s.scaled(&q(-1)));
        }
        out
    }

    pub fn minus(&self, other: &Real) -> Real {
        self.plus(&other.negated())
    }

    pub fn times(&self, other: &Real) -> Real {
        let mut out = Real::default();
        for (m, s) in &self.parts {
            for (n, t) in &other.parts {
                out.put(joined(m, n), s.times(t));
            }
        }
        out
    }

    pub fn power(&self, n: u64) -> Real {
        let mut out = Real::rational(q(1));
        for _ in 0..n {
            out = out.times(self);
        }
        out
    }

    /// How many parts the value has, each monomial's coefficient counted by
    /// its roots; the value 0 counted as one.
    pub fn part_count(&self) -> u64 {
        let n: usize = self.parts.values().map(|s| s.parts.len()).sum();
        n.max(1) as u64
    }

    /// Every prime under a root of the value.
    pub fn primes(&self) -> Vec<u64> {
        let mut out: Vec<u64> = self.parts.values().flat_map(Surd::primes).collect();
        out.sort_unstable();
        out.dedup();
        out
    }

    /// Each atom the value holds.
    pub fn atoms(&self) -> Vec<Atom> {
        let mut out: Vec<Atom> =
            self.parts.keys().flat_map(|m| m.keys().copied()).collect();
        out.sort();
        out.dedup();
        out
    }

    /// The value as q·eᵏ, q rational and k whole; None where it is not.
    pub fn rational_times_e(&self) -> Option<(Q, u32)> {
        match self.parts.iter().collect::<Vec<_>>().as_slice() {
            [] => Some((Q::zero(), 0)),
            [(m, s)] => {
                let q = s.as_rational()?;
                match m.iter().collect::<Vec<_>>().as_slice() {
                    [] => Some((q, 0)),
                    [(Atom::E, k)] => Some((q, **k)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The value as k + Σ qₚ·ln p, where it is one.
    pub fn logarithmic(&self) -> Option<Logarithmic> {
        let mut out = Logarithmic {
            constant: Q::zero(),
            logs: BTreeMap::new(),
        };
        for (m, s) in &self.parts {
            let weight = s.as_rational()?;
            match m.iter().collect::<Vec<_>>().as_slice() {
                [] => out.constant = weight,
                [(Atom::Ln(p), 1)] => {
                    out.logs.insert(*p, weight);
                }
                _ => return None,
            }
        }
        Some(out)
    }

    /// The value's parts as the bound on a product reads them.
    pub(crate) fn pieces(&self) -> Vec<Piece<Monomial>> {
        self.parts
            .iter()
            .flat_map(|(m, s)| {
                s.parts.iter().map(move |(basis, weight)| Piece {
                    atoms: m.clone(),
                    basis: basis.clone(),
                    weight: weight.clone(),
                })
            })
            .collect()
    }

    /// Each coefficient of the value, root by root.
    pub fn weights(&self) -> Vec<Q> {
        self.parts
            .values()
            .flat_map(|s| s.parts.values().cloned())
            .collect()
    }
}

/// The product of two monomials.
pub fn joined(m: &Monomial, n: &Monomial) -> Monomial {
    let mut out = m.clone();
    for (a, k) in n {
        *out.entry(*a).or_insert(0) += k;
    }
    out
}

/// What a closed term comes to: its value, or why it has none.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Exact(Real),
    Unworked(&'static str),
}

/// Whether a term is set.mm's function `label` applied, `( A label cfv )`.
pub fn applies(term: &Term, label: &str) -> bool {
    term.variable().is_none()
        && term.label() == Some("cfv")
        && term.children().len() == 2
        && term.children()[1].label() == Some(label)
}

/// Whether a term holds π, e, a logarithm or an exponential anywhere.
pub fn holds_atom(term: &Term) -> bool {
    if term.variable().is_some() {
        return false;
    }
    let here = matches!(term.label(), Some("cpi" | "ceu"))
        && term.children().is_empty()
        || applies(term, "clog")
        || applies(term, "ce")
        || Trig::of(term).is_some();
    here || term.children().iter().any(holds_atom)
}

/// The two functions of an angle the method works out.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Trig {
    Sine,
    Cosine,
}

impl Trig {
    /// The function a term applies, `( x csin cfv )` or `( x ccos cfv )`.
    pub fn of(term: &Term) -> Option<Trig> {
        if applies(term, "csin") {
            Some(Trig::Sine)
        } else if applies(term, "ccos") {
            Some(Trig::Cosine)
        } else {
            None
        }
    }
}

/// Why a sine or cosine is refused: its angle is no rational multiple of π.
pub const TRIG_NOT_SPECIAL: &str =
    "takes the sine or cosine of an angle that is not a rational multiple of π";

/// Why a sine or cosine of another rational multiple of π is refused.
pub const TRIG_DENOMINATOR: &str =
    "takes the sine or cosine of a multiple of π whose denominator divides neither 4 nor 6";

/// An angle's value as q·π, q rational, where it is one, 0 included.
pub fn multiple_of_pi(angle: &Real) -> Option<Q> {
    match angle.parts.iter().collect::<Vec<_>>().as_slice() {
        [] => Some(Q::zero()),
        [(m, s)] if m.len() == 1 && m.get(&Atom::Pi) == Some(&1) => s.as_rational(),
        _ => None,
    }
}

/// The sine or cosine of q·π, q with a denominator dividing 4 or 6: q less a
/// whole multiple of 2 is r, 0 ≤ r < 2; a π is taken off r of at least 1
/// (sin(t + π) = −sin t, cos(t + π) = −cos t), and π/2 off r of at least 1/2
/// (sin(π/2 + t) = cos t, cos(π/2 + t) = −sin t); what is left is 0, π/6,
/// π/4 or π/3.
pub fn trig_value(f: Trig, multiple: &Q) -> Result<Surd, &'static str> {
    let d = multiple.denom();
    if !(BigInt::from(4) % d).is_zero() && !(BigInt::from(6) % d).is_zero() {
        return Err(TRIG_DENOMINATOR);
    }
    Ok(reduced(f, &turned(multiple)))
}

/// q less the whole multiple of 2 that leaves it from 0 up to 2.
pub fn turned(multiple: &Q) -> Q {
    let two = q(2);
    multiple - (multiple / &two).floor() * &two
}

/// `trig_value` of r·π, 0 ≤ r < 2.
fn reduced(f: Trig, r: &Q) -> Surd {
    let half = Q::new(BigInt::from(1), BigInt::from(2));
    if *r >= q(1) {
        return reduced(f, &(r - q(1))).scaled(&q(-1));
    }
    if *r >= half {
        let rest = r - &half;
        return match f {
            Trig::Sine => reduced(Trig::Cosine, &rest),
            Trig::Cosine => reduced(Trig::Sine, &rest).scaled(&q(-1)),
        };
    }
    let root_half = |p: u64| {
        let mut out = Surd::default();
        out.parts.insert(vec![p], half.clone());
        out
    };
    let twelfths = (r * q(12)).to_integer();
    let twelfths = twelfths.to_i64().expect("r below 1/2");
    match (f, twelfths) {
        (Trig::Sine, 0) | (Trig::Cosine, 6) => Surd::default(),
        (Trig::Sine, 2) | (Trig::Cosine, 4) => Surd::rational(half.clone()),
        (_, 3) => root_half(2),
        (Trig::Sine, 4) | (Trig::Cosine, 2) => root_half(3),
        (Trig::Cosine, 0) => Surd::rational(q(1)),
        _ => unreachable!("a denominator dividing 4 or 6 leaves 0, π/6, π/4 or π/3"),
    }
}

/// Whether a term holds anything `real arithmetic` works out and
/// `arithmetic` does not: a square root, π, e, a logarithm or an
/// exponential. One that holds none is `arithmetic`'s.
pub fn beyond_arithmetic(term: &Term) -> bool {
    surds::takes_root(term) || holds_atom(term)
}

/// The value of a closed term built from numerals by the operations
/// `arithmetic` works out, square roots of rationals, π, e, and logarithms
/// and exponentials of the forms the module says. A part with no atom is
/// `surds`'. A decline where the term is not built so.
pub fn closed_value(term: &Term) -> Route<Value> {
    if term.variable().is_some() {
        return Route::no("it holds a letter");
    }
    if !holds_atom(term) {
        return match surds::closed_value(term) {
            Built(surds::Value::Exact(v)) => Built(Value::Exact(Real::surd(v))),
            Built(surds::Value::Unworked(why)) => Built(Value::Unworked(why)),
            Declined(d) => Declined(d),
        };
    }
    let kids = term.children();
    let value = match term.label() {
        Some("cpi") if kids.is_empty() => Real::atom(Atom::Pi),
        Some("ceu") if kids.is_empty() => Real::atom(Atom::E),
        _ if applies(term, "clog") => match closed_value(&kids[0]) {
            Built(Value::Exact(x)) => match logarithm(&x) {
                Ok(v) => v,
                Err(why) => return Built(Value::Unworked(why)),
            },
            other => return other,
        },
        _ if applies(term, "ce") => match closed_value(&kids[0]) {
            Built(Value::Exact(x)) => match exponential(&x) {
                Ok(v) => v,
                Err(why) => return Built(Value::Unworked(why)),
            },
            other => return other,
        },
        _ if Trig::of(term).is_some() => match closed_value(&kids[0]) {
            Built(Value::Exact(x)) => {
                let Some(q) = multiple_of_pi(&x) else {
                    return Built(Value::Unworked(TRIG_NOT_SPECIAL));
                };
                match trig_value(Trig::of(term).expect("a sine or cosine"), &q) {
                    Ok(v) => Real::surd(v),
                    Err(why) => return Built(Value::Unworked(why)),
                }
            }
            other => return other,
        },
        // A root of a term holding an atom is of no rational.
        _ if surds::is_root(term) => {
            return Built(Value::Unworked(surds::NOT_RATIONAL))
        }
        Some(NEG) if kids.len() == 1 => match closed_value(&kids[0]) {
            Built(Value::Exact(v)) => v.negated(),
            other => return other,
        },
        Some("co") if kids.len() == 3 => {
            let how = kids[2].label().unwrap_or("");
            let left = match closed_value(&kids[0]) {
                Built(Value::Exact(v)) => v,
                other => return other,
            };
            let right = match closed_value(&kids[1]) {
                Built(Value::Exact(v)) => v,
                other => return other,
            };
            match how {
                ADD => left.plus(&right),
                SUB => left.minus(&right),
                MUL => left.times(&right),
                DIV => match right.as_surd() {
                    None => return Built(Value::Unworked(DIVIDES_BY_ATOM)),
                    Some(s) if s.is_zero() => {
                        return Built(Value::Unworked("divides by zero"))
                    }
                    Some(s) => left.times(&Real::surd(s.recip())),
                },
                EXP => {
                    let whole = right
                        .as_surd()
                        .and_then(|s| s.as_rational())
                        .filter(|k| k.is_integer())
                        .and_then(|k| k.to_integer().to_i64());
                    match whole {
                        None => {
                            return Built(Value::Unworked(
                                "is a power real arithmetic works out only with a whole exponent",
                            ))
                        }
                        // A power to an exponent below 0 is one over the power,
                        // taken only of a value with no atom, as a sine's is.
                        Some(k) if k < 0 => match left.as_surd() {
                            None => return Built(Value::Unworked(DIVIDES_BY_ATOM)),
                            Some(s) if s.is_zero() => {
                                return Built(Value::Unworked("divides by zero"))
                            }
                            Some(s) => {
                                let m = k.unsigned_abs();
                                if m * left.part_count() > 64 {
                                    return Built(Value::Unworked(surds::TOO_LARGE));
                                }
                                Real::surd(s.power(m).recip())
                            }
                        },
                        Some(k) if k as u64 * left.part_count() > 64 => {
                            return Built(Value::Unworked(surds::TOO_LARGE))
                        }
                        Some(k) => left.power(k as u64),
                    }
                }
                _ => return Route::no("not an operation real arithmetic reads"),
            }
        }
        _ => return Route::no("not built from numerals, roots, π, e and logarithms"),
    };
    held(value)
}

/// A value within the limits, or refused as too large.
fn held(value: Real) -> Route<Value> {
    let size = value
        .weights()
        .iter()
        .map(|v| v.numer().bits().max(v.denom().bits()))
        .max()
        .unwrap_or(0);
    if value.primes().len() > surds::PRIMES || size > super::field::BITS {
        return Built(Value::Unworked(surds::TOO_LARGE));
    }
    Built(Value::Exact(value))
}

/// ln of q·eᵏ, q a positive rational: k + Σ nₚ·ln p, its numerator and
/// denominator factored.
fn logarithm(x: &Real) -> Result<Real, &'static str> {
    let Some((ratio, k)) = x.rational_times_e() else {
        return Err(LN_NOT_RATIONAL);
    };
    if !ratio.is_positive() {
        return Err(LN_NOT_POSITIVE);
    }
    let mut out = Real::rational(Q::from_integer(BigInt::from(k)));
    for (p, n) in factored(&ratio)? {
        let one = Real::atom(Atom::Ln(p));
        out = out.plus(&one.times(&Real::rational(Q::from_integer(BigInt::from(n)))));
    }
    Ok(out)
}

/// A positive rational's primes, each with its exponent, below 0 for one of
/// the denominator's.
pub fn factored(ratio: &Q) -> Result<BTreeMap<u64, i64>, &'static str> {
    let mut out = BTreeMap::new();
    for (whole, sign) in [(ratio.numer(), 1i64), (ratio.denom(), -1)] {
        if whole.bits() > surds::RADICAND_BITS {
            return Err(surds::TOO_LARGE);
        }
        let mut left = whole.to_u64().expect("within RADICAND_BITS");
        let mut p = 2u64;
        while p * p <= left {
            while left.is_multiple_of(p) {
                left /= p;
                *out.entry(p).or_insert(0) += sign;
            }
            p += 1;
        }
        if left > 1 {
            *out.entry(left).or_insert(0) += sign;
        }
    }
    Ok(out)
}

/// exp of k + Σ nₚ·ln p, k and each nₚ whole and k at least 0: eᵏ·Π p^nₚ.
fn exponential(x: &Real) -> Result<Real, &'static str> {
    let Some(Logarithmic { constant, logs }) = x.logarithmic() else {
        return Err(EXP_OUT_OF_RANGE);
    };
    let k = constant
        .is_integer()
        .then(|| constant.to_integer().to_u32())
        .flatten()
        .ok_or(EXP_OUT_OF_RANGE)?;
    let mut ratio = q(1);
    for (p, n) in logs {
        if !n.is_integer() {
            return Err(EXP_OUT_OF_RANGE);
        }
        let n = n.to_integer().to_i32().ok_or(surds::TOO_LARGE)?;
        if n.unsigned_abs() > 64 {
            return Err(surds::TOO_LARGE);
        }
        ratio *= num_traits::pow(
            Q::from_integer(BigInt::from(p)),
            n.unsigned_abs() as usize,
        )
        .pow(n.signum());
    }
    let mut out = Real::default();
    let monomial = if k == 0 {
        Monomial::new()
    } else {
        Monomial::from([(Atom::E, k)])
    };
    out.put(monomial, Surd::rational(ratio));
    Ok(out)
}

/// Whether a value is rational multiples of logarithms of primes and
/// nothing else, which is 0 only where every multiple is.
pub fn pure_logarithms(value: &Real) -> bool {
    value
        .logarithmic()
        .is_some_and(|l| l.constant.is_zero() && !l.logs.is_empty())
}

/// Whether a relation between closed terms holds, as `surds::decide_closed`
/// says of one holding no π, e or logarithm. An equation or a disequality
/// holding one is decided where the difference of its sides is 0, holds no
/// atom, or is `pure_logarithms`, and is not decided otherwise; an order is
/// decided between rational values, a membership of ℝ or ℂ always, and one
/// of ℕ, ℕ₀, ℤ or ℚ where the value is rational.
pub fn decide_closed(claim: &Term) -> Route<Verdict> {
    if !holds_atom(claim) {
        return surds::decide_closed(claim);
    }
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
            let gap = a.minus(&b);
            if !gap.is_zero() && gap.as_surd().is_none() && !pure_logarithms(&gap) {
                return Built(Verdict::Undecided(NOT_DECIDED));
            }
            gap.is_zero() == (claim.label() == Some("wceq"))
        }
        Some("wbr")
            if kids.len() == 3 && matches!(kids[2].label(), Some("clt" | "cle")) =>
        {
            let (a, b) = match (side(&kids[0]), side(&kids[1])) {
                (Ok(a), Ok(b)) => (a, b),
                (Err(stop), _) | (_, Err(stop)) => return stop,
            };
            let rational = |v: &Real| v.as_surd().and_then(|s| s.as_rational());
            let (Some(a), Some(b)) = (rational(&a), rational(&b)) else {
                return Built(Verdict::Undecided(surds::ORDER_UNDECIDED));
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
            match (system, v.as_surd().and_then(|s| s.as_rational())) {
                (System::R | System::C, _) => true,
                (_, Some(v)) => surds::system_test(system)(&v),
                (_, None) => {
                    return Built(Verdict::Undecided(surds::MEMBERSHIP_UNDECIDED))
                }
            }
        }
        _ => return Route::no("not a relation real arithmetic decides"),
    };
    let holds = holds != negated;
    if holds {
        if let Err(why) = proof_cost(claim, negated) {
            return Built(Verdict::Unworked(why));
        }
    }
    Built(Verdict::Holds(holds))
}

// --- what a proof costs ------------------------------------------------------

/// Whether the proof of a true claim stays within `surds::WORK` and writes
/// no numeral past `surds::COEFFICIENT_BITS`, as `surds::proof_cost` asks of
/// a claim with no atom.
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
        total = total.saturating_add(surds::cube(
            values[0].part_count() + values[1].part_count(),
        ));
        total = total.saturating_add(match gap.as_surd() {
            Some(s) => surds::apart_cost(&s)?,
            None => surds::cube(gap.part_count() + 2),
        });
    }
    if total > surds::WORK {
        return Err(surds::TOO_LARGE);
    }
    Ok(())
}

struct Estimate {
    value: Real,
    cost: u64,
}

fn estimate(term: &Term) -> Result<Estimate, &'static str> {
    let Built(Value::Exact(value)) = closed_value(term) else {
        return Err(surds::TOO_LARGE);
    };
    written(&value)?;
    if !holds_atom(term) {
        return Ok(Estimate {
            value,
            cost: surds::term_cost(term)?,
        });
    }
    let kids = term.children();
    let cost = match term.label() {
        Some("cpi" | "ceu") if kids.is_empty() => 0,
        // A logarithm or an exponential is its argument's value, a few
        // laws, and an identity to its canon.
        _ if applies(term, "clog")
            || applies(term, "ce")
            || Trig::of(term).is_some() =>
        {
            estimate(&kids[0])?
                .cost
                .saturating_add(surds::cube(value.part_count() + 2))
        }
        Some(NEG) => {
            let x = estimate(&kids[0])?;
            x.cost.saturating_add(surds::cube(x.value.part_count()))
        }
        _ => {
            let how = kids[2].label().unwrap_or("");
            let x = estimate(&kids[0])?;
            let y = estimate(&kids[1])?;
            let here = match how {
                ADD | SUB => surds::cube(x.value.part_count() + y.value.part_count()),
                MUL => product_cost(&x.value, &y.value)?,
                DIV => {
                    let below = y.value.as_surd().ok_or(DIVIDES_BY_ATOM)?;
                    let quotient = x.value.times(&Real::surd(below.recip()));
                    written(&quotient)?;
                    product_cost(&y.value, &quotient)?
                        .saturating_add(surds::apart_cost(&below)?)
                }
                EXP => {
                    let k = y
                        .value
                        .as_surd()
                        .and_then(|s| s.as_rational())
                        .and_then(|k| k.to_integer().to_i64())
                        .ok_or(surds::TOO_LARGE)?;
                    if k < 0 {
                        let base = x.value.as_surd().ok_or(DIVIDES_BY_ATOM)?;
                        return Ok(Estimate {
                            value,
                            cost: x
                                .cost
                                .saturating_add(y.cost)
                                .saturating_add(surds::power_cost(&base, k)?),
                        });
                    }
                    let k = k as u64;
                    let mut cost = 0u64;
                    let mut at = x.value.clone();
                    for _ in 1..k {
                        cost = cost.saturating_add(product_cost(&at, &x.value)?);
                        at = at.times(&x.value);
                    }
                    cost
                }
                _ => 0,
            };
            x.cost.saturating_add(y.cost).saturating_add(here)
        }
    };
    Ok(Estimate { value, cost })
}

/// The value, where its canon writes no numeral past
/// `surds::COEFFICIENT_BITS`.
fn written(value: &Real) -> Result<(), &'static str> {
    let bits = match value.as_surd().and_then(|s| s.as_rational()) {
        Some(r) => r.numer().bits().max(r.denom().bits()),
        None => surds::weights_bits(value.weights().iter()),
    };
    if bits > surds::COEFFICIENT_BITS {
        return Err(surds::TOO_LARGE);
    }
    Ok(())
}

/// The identity bringing a product of two canons to the canon of their
/// product, as `surds::product_cost` has it, a part's atoms multiplied with
/// its roots.
fn product_cost(a: &Real, b: &Real) -> Result<u64, &'static str> {
    let product = a.times(b);
    let widest =
        surds::product_widest(&a.pieces(), &b.pieces(), joined, &product.weights());
    if widest > surds::COEFFICIENT_BITS {
        return Err(surds::TOO_LARGE);
    }
    written(&product)?;
    Ok(surds::cube(a.part_count() * b.part_count()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(d: &str) -> Term {
        Term::apply(d, vec![])
    }

    fn op(a: Term, b: Term, o: &str) -> Term {
        Term::apply("co", vec![a, b, n(o)])
    }

    fn ln(x: Term) -> Term {
        Term::apply("cfv", vec![x, n("clog")])
    }

    fn exp(x: Term) -> Term {
        Term::apply("cfv", vec![x, n("ce")])
    }

    fn value(t: &Term) -> Real {
        match closed_value(t) {
            Built(Value::Exact(v)) => v,
            other => panic!("no value: {other:?}"),
        }
    }

    #[test]
    fn a_logarithm_is_its_argument_factored() {
        let eight = op(n("c4"), n("c2"), MUL);
        let ln2 = Real::atom(Atom::Ln(2));
        assert_eq!(value(&ln(eight)), ln2.times(&Real::rational(q(3))));
        assert_eq!(value(&ln(op(n("c1"), n("c2"), DIV))), ln2.negated());
        assert_eq!(value(&ln(n("c1"))), Real::default());
        assert_eq!(value(&ln(op(n("ceu"), n("c3"), EXP))), Real::rational(q(3)));
    }

    #[test]
    fn a_logarithm_of_a_number_not_above_zero_is_refused() {
        assert_eq!(
            closed_value(&ln(n("cc0"))),
            Built(Value::Unworked(LN_NOT_POSITIVE))
        );
        assert_eq!(
            closed_value(&ln(n("cpi"))),
            Built(Value::Unworked(LN_NOT_RATIONAL))
        );
    }

    #[test]
    fn an_exponential_of_a_logarithm_is_its_argument() {
        assert_eq!(value(&exp(ln(n("c5")))), Real::rational(q(5)));
        let squared = Real::atom(Atom::E).times(&Real::atom(Atom::E));
        assert_eq!(value(&exp(n("c2"))), squared);
        assert_eq!(
            closed_value(&exp(op(n("c1"), n("c2"), DIV))),
            Built(Value::Unworked(EXP_OUT_OF_RANGE))
        );
    }

    #[test]
    fn a_difference_of_logarithms_is_decided_and_one_with_pi_is_not() {
        let apart = Term::apply("wne", vec![ln(n("c2")), ln(n("c3"))]);
        assert_eq!(decide_closed(&apart), Built(Verdict::Holds(true)));
        let unknown = Term::apply("wceq", vec![n("cpi"), n("ceu")]);
        assert_eq!(
            decide_closed(&unknown),
            Built(Verdict::Undecided(NOT_DECIDED))
        );
        let sum = op(n("cpi"), n("ceu"), ADD);
        let square = op(sum.clone(), n("c2"), EXP);
        let expanded = op(
            op(
                op(n("cpi"), n("c2"), EXP),
                op(op(n("c2"), n("cpi"), MUL), n("ceu"), MUL),
                ADD,
            ),
            op(n("ceu"), n("c2"), EXP),
            ADD,
        );
        let claim = Term::apply("wceq", vec![square, expanded]);
        assert_eq!(decide_closed(&claim), Built(Verdict::Holds(true)));
    }

    #[test]
    fn sines_and_cosines_of_the_special_angles() {
        let half = q(1) / q(2);
        let root_half = |p: u64| {
            let mut out = Surd::default();
            out.parts.insert(vec![p], half.clone());
            out
        };
        // sin(nπ/12) for each n from 0 to 23 the method takes, written out.
        let table: [(i64, Surd); 16] = [
            (0, Surd::default()),
            (2, Surd::rational(half.clone())),
            (3, root_half(2)),
            (4, root_half(3)),
            (6, Surd::rational(q(1))),
            (8, root_half(3)),
            (9, root_half(2)),
            (10, Surd::rational(half.clone())),
            (12, Surd::default()),
            (14, Surd::rational(-half.clone())),
            (15, root_half(2).scaled(&q(-1))),
            (16, root_half(3).scaled(&q(-1))),
            (18, Surd::rational(q(-1))),
            (20, root_half(3).scaled(&q(-1))),
            (21, root_half(2).scaled(&q(-1))),
            (22, Surd::rational(-half.clone())),
        ];
        let at = |n: i64| Q::new(BigInt::from(n), BigInt::from(12));
        for (n, sine) in &table {
            assert_eq!(
                trig_value(Trig::Sine, &at(*n)).unwrap(),
                *sine,
                "sin({n}π/12)"
            );
            // cos t = sin(t + π/2), and the same angle a turn on or back.
            let cos_at = (n + 6).rem_euclid(24);
            let cosine = &table.iter().find(|(m, _)| *m == cos_at).unwrap().1;
            assert_eq!(
                trig_value(Trig::Cosine, &at(*n)).unwrap(),
                *cosine,
                "cos({n}π/12)"
            );
            assert_eq!(trig_value(Trig::Sine, &at(n + 24)).unwrap(), *sine);
            assert_eq!(trig_value(Trig::Sine, &at(n - 48)).unwrap(), *sine);
        }
        assert_eq!(trig_value(Trig::Sine, &at(1)), Err(TRIG_DENOMINATOR));
        assert_eq!(
            trig_value(Trig::Sine, &Q::new(BigInt::from(1), BigInt::from(5))),
            Err(TRIG_DENOMINATOR)
        );
    }

    #[test]
    fn a_sine_of_one_is_refused() {
        let sine = Term::apply("cfv", vec![n("c1"), n("csin")]);
        assert_eq!(
            closed_value(&sine),
            Built(Value::Unworked(TRIG_NOT_SPECIAL))
        );
    }

    #[test]
    fn a_division_by_pi_is_refused() {
        assert_eq!(
            closed_value(&op(n("c1"), n("cpi"), DIV)),
            Built(Value::Unworked(DIVIDES_BY_ATOM))
        );
    }
}
