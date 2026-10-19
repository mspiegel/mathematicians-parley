//! Claims for `real arithmetic`, drawn and judged by the test alone.
//!
//! The judge shares nothing with the method: where the method holds a value
//! as rational multiples of roots of squarefree numbers and decides by
//! comparing them, the judge works each term to an interval of rationals
//! around its value, 1024 bits wide at the least, and an exact rational
//! where it has no root. A difference whose interval holds 0 and is
//! narrower than 2⁻⁵¹² is 0; one that does not hold 0 is not. That is
//! sound for what is drawn: a value built from square roots of numbers
//! below a hundred, at most three deep, is an algebraic number of degree at
//! most 16 and small height, and such a number not 0 is far further from 0
//! than that. A value is rational where a fraction of denominator at most
//! 10¹² lies inside its interval, for the same reason.
//!
//! The terms hold the roots of at most two primes, and small numerals, so
//! no claim drawn is past the method's limits; claims past them are drawn
//! on purpose and judged refused.

use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use parley::formula::grammar::Grammar;
use parley::formula::node::Node;
use parley::formula::page::numeral;

use crate::gen::{made, Drawn};
use crate::judge::Verdict;
use crate::shared::Random;

type Q = BigRational;

/// The method's refusals, each as the tools word it.
pub const BELOW_ZERO: &str = "takes the square root of a number below 0";
pub const NOT_RATIONAL: &str = "takes the square root of a number that is not rational";
pub const DIVIDES_BY_ZERO: &str = "divides by zero";
pub const UNDECIDED: &str = "real arithmetic does not decide it";
pub const NO_ROOT: &str = "takes no square root";
pub const TOO_LARGE: &str = "is too large to work out";

/// A term of numerals and square roots.
#[derive(Clone, Debug)]
pub enum Real {
    Num(BigInt),
    Root(Box<Real>),
    Neg(Box<Real>),
    Add(Box<Real>, Box<Real>),
    Sub(Box<Real>, Box<Real>),
    Mul(Box<Real>, Box<Real>),
    Div(Box<Real>, Box<Real>),
    /// A power to a whole exponent, which may be below 0.
    Pow(Box<Real>, i64),
}

/// A relation between two terms.
#[derive(Clone, Copy, Debug)]
pub enum Rel {
    Eq,
    Ne,
    Lt,
    Le,
}

/// The number systems a membership is said of.
#[derive(Clone, Copy, Debug)]
pub enum System {
    Nat,
    Int,
    Rat,
    Real,
}

/// A claim `real arithmetic` is asked.
#[derive(Clone, Debug)]
pub enum Claim {
    Rel(Rel, Real, Real),
    Member(Real, System),
}

fn num(n: i64) -> Real {
    Real::Num(BigInt::from(n))
}

fn b(e: Real) -> Box<Real> {
    Box::new(e)
}

fn root(n: i64) -> Real {
    Real::Root(b(num(n)))
}

/// The two primes a claim's roots are drawn over.
fn primes(r: &mut Random) -> [i64; 2] {
    const POOL: [i64; 4] = [2, 3, 5, 7];
    let first = POOL[r.below(4) as usize];
    let mut second = POOL[r.below(4) as usize];
    while second == first {
        second = POOL[r.below(4) as usize];
    }
    [first, second]
}

/// A root of a rational over the primes: √(k²·m) or √(m/k²), m one of 1,
/// p, q and p·q.
fn root_drawn(r: &mut Random, ps: [i64; 2]) -> Real {
    let m = [1, ps[0], ps[1], ps[0] * ps[1]][r.below(4) as usize];
    let k = 1 + r.below(3) as i64;
    if r.below(3) == 0 {
        Real::Root(b(Real::Div(b(num(m)), b(num(k * k)))))
    } else {
        Real::Root(b(num(k * k * m)))
    }
}

/// A term at most `depth` deep.
fn expr(r: &mut Random, ps: [i64; 2], depth: u32) -> Real {
    if depth == 0 || r.below(3) == 0 {
        return match r.below(3) {
            0 => num(r.below(10) as i64 - 3),
            _ => root_drawn(r, ps),
        };
    }
    let sub = |r: &mut Random| b(expr(r, ps, depth - 1));
    match r.below(6) {
        0 => Real::Neg(sub(r)),
        1 => Real::Add(sub(r), sub(r)),
        2 => Real::Sub(sub(r), sub(r)),
        3 => Real::Mul(sub(r), sub(r)),
        4 => Real::Div(sub(r), sub(r)),
        // Exponents from −1 to 2, so that a power of a power keeps every
        // numeral its proof writes inside the 62 bits the method allows.
        _ => Real::Pow(sub(r), r.below(4) as i64 - 1),
    }
}

/// A claim true by construction, or one coefficient away where `off`.
fn identity(r: &mut Random, ps: [i64; 2], off: bool) -> Claim {
    let (p, q) = (ps[0], ps[1]);
    let a = 1 + r.below(6) as i64;
    let c = 1 + r.below(4) as i64;
    let bump = |n: i64| if off { n + 1 } else { n };
    let (left, right) = match r.below(5) {
        // √(c²·p) = c·√p
        0 => (root(c * c * p), Real::Mul(b(num(bump(c))), b(root(p)))),
        // (a + c√p)(a − c√p) = a² − p·c²
        1 => (
            Real::Mul(
                b(Real::Add(b(num(a)), b(Real::Mul(b(num(c)), b(root(p)))))),
                b(Real::Sub(b(num(a)), b(Real::Mul(b(num(c)), b(root(p)))))),
            ),
            num(bump(a * a - p * c * c)),
        ),
        // 1/(a + √p) = (a − √p)/(a² − p), where a² ≠ p
        2 => (
            Real::Div(b(num(1)), b(Real::Add(b(num(a)), b(root(p))))),
            Real::Div(b(Real::Sub(b(num(bump(a))), b(root(p)))), b(num(a * a - p))),
        ),
        // √p·√q = √(pq)
        3 => (Real::Mul(b(root(p)), b(root(q))), root(bump(p * q))),
        // (√p + √q)² = p + q + 2√(pq)
        _ => (
            Real::Pow(b(Real::Add(b(root(p)), b(root(q)))), 2),
            Real::Add(b(num(bump(p + q))), b(Real::Mul(b(num(2)), b(root(p * q))))),
        ),
    };
    Claim::Rel(Rel::Eq, left, right)
}

/// A claim refused by the document: a root of a number below 0, one of a
/// number that is not rational, a division by zero, a claim past the
/// limits, and one with no root.
fn refused(r: &mut Random, ps: [i64; 2]) -> Claim {
    let p = ps[0];
    let left = match r.below(5) {
        0 => Real::Add(b(root(p)), b(Real::Root(b(num(-p))))),
        1 => Real::Root(b(Real::Add(b(num(1)), b(root(p))))),
        2 => Real::Div(b(num(1)), b(Real::Sub(b(root(p)), b(root(p))))),
        3 => Real::Pow(
            b(Real::Add(
                b(Real::Add(b(root(2)), b(root(3)))),
                b(Real::Add(b(root(5)), b(root(7)))),
            )),
            8,
        ),
        _ => return Claim::Rel(Rel::Eq, num(p), num(p)),
    };
    Claim::Rel(Rel::Eq, left.clone(), left)
}

/// A claim of each form in turn.
pub fn draw(r: &mut Random) -> Claim {
    let ps = primes(r);
    let e = |r: &mut Random| expr(r, ps, 3);
    match r.below(10) {
        0..=2 => {
            let off = r.below(3) == 0;
            identity(r, ps, off)
        }
        3 | 4 => {
            let rel = [Rel::Eq, Rel::Ne, Rel::Lt, Rel::Le][r.below(4) as usize];
            Claim::Rel(rel, e(r), e(r))
        }
        5 => {
            // A term against itself and against itself moved by one, so
            // that true equations of drawn terms are asked.
            let left = e(r);
            let right = match r.below(2) {
                0 => left.clone(),
                _ => Real::Add(b(left.clone()), b(num(1))),
            };
            let rel = [Rel::Eq, Rel::Ne][r.below(2) as usize];
            Claim::Rel(rel, left, right)
        }
        6 | 7 => {
            let system = [System::Nat, System::Int, System::Rat, System::Real]
                [r.below(4) as usize];
            Claim::Member(e(r), system)
        }
        8 => {
            // A term whose value is rational, in a system or against a
            // numeral.
            let k = 1 + r.below(4) as i64;
            let whole = Real::Mul(b(root(ps[0])), b(root(k * k * ps[0])));
            match r.below(2) {
                0 => Claim::Member(
                    whole,
                    [System::Nat, System::Int][r.below(2) as usize],
                ),
                _ => Claim::Rel(Rel::Lt, whole, num(r.below(40) as i64)),
            }
        }
        _ => refused(r, ps),
    }
}

/// A claim for `real arithmetic`, drawn and judged.
pub fn claim(r: &mut Random, g: &Grammar) -> Drawn {
    let c = draw(r);
    Drawn {
        header: Vec::new(),
        written: written(g, &c),
        justification: "real arithmetic".to_string(),
        verdict: judged(&c),
        shown: format!("{c:?}"),
    }
}

// --- writing ----------------------------------------------------------------

fn term(g: &Grammar, e: &Real) -> Node {
    let two = |x: &Real, y: &Real, p: &str| made(g, p, vec![term(g, x), term(g, y)]);
    match e {
        Real::Num(n) if n.is_negative() => {
            made(g, "−_", vec![numeral(&(-n).to_string())])
        }
        Real::Num(n) => numeral(&n.to_string()),
        Real::Root(x) => made(g, "√_", vec![term(g, x)]),
        Real::Neg(x) => made(g, "−_", vec![term(g, x)]),
        Real::Add(x, y) => two(x, y, "_ + _"),
        Real::Sub(x, y) => two(x, y, "_ − _"),
        Real::Mul(x, y) => two(x, y, "_ · _"),
        Real::Div(x, y) => two(x, y, "_ / _"),
        Real::Pow(x, k) => {
            let exponent = numeral(&k.unsigned_abs().to_string());
            let exponent = if *k < 0 {
                made(g, "−_", vec![exponent])
            } else {
                exponent
            };
            made(g, "_^_", vec![term(g, x), exponent])
        }
    }
}

fn written(g: &Grammar, c: &Claim) -> String {
    let node = match c {
        Claim::Rel(rel, a, b) => {
            let pattern = match rel {
                Rel::Eq => "_ = _",
                Rel::Ne => "_ ≠ _",
                Rel::Lt => "_ < _",
                Rel::Le => "_ ≤ _",
            };
            made(g, pattern, vec![term(g, a), term(g, b)])
        }
        Claim::Member(a, system) => {
            let set = match system {
                System::Nat => "ℕ",
                System::Int => "ℤ",
                System::Rat => "ℚ",
                System::Real => "ℝ",
            };
            made(g, "_ ∈ _", vec![term(g, a), made(g, set, Vec::new())])
        }
    };
    g.print(&node)
}

// --- judging ----------------------------------------------------------------

/// The working precision, in bits.
const BITS: u32 = 1024;

/// A value: exact where the term has no root, and otherwise an interval
/// with rational ends that holds it.
#[derive(Clone, Debug)]
enum Value {
    Exact(Q),
    Between(Q, Q),
}

impl Value {
    fn ends(&self) -> (Q, Q) {
        match self {
            Value::Exact(v) => (v.clone(), v.clone()),
            Value::Between(lo, hi) => (lo.clone(), hi.clone()),
        }
    }
}

fn scale() -> Q {
    Q::from_integer(BigInt::one() << BITS)
}

/// The interval widened to ends of denominator 2^BITS, so that the ends do
/// not grow with every operation.
fn rounded(lo: Q, hi: Q) -> Value {
    let s = scale();
    let lo = (lo * &s).floor() / &s;
    let hi = (hi * &s).ceil() / &s;
    Value::Between(lo, hi)
}

/// Whether the value is 0, judged as the module says; None where the
/// interval is too wide to tell, which nothing drawn should give.
fn is_zero(v: &Value) -> Option<bool> {
    match v {
        Value::Exact(x) => Some(x.is_zero()),
        Value::Between(lo, hi) => {
            if lo.is_positive() || hi.is_negative() {
                return Some(false);
            }
            let tiny = Q::new(BigInt::one(), BigInt::one() << (BITS / 2));
            (hi - lo < tiny).then_some(true)
        }
    }
}

/// The rational the value is, where it is one: exact, or a fraction of
/// small denominator inside a narrow interval, found among the convergents
/// of the interval's middle.
fn rational(v: &Value) -> Option<Q> {
    let (lo, hi) = match v {
        Value::Exact(x) => return Some(x.clone()),
        Value::Between(lo, hi) => (lo, hi),
    };
    let mut x: Q = (lo + hi) / Q::from_integer(BigInt::from(2));
    let (mut p0, mut q0, mut p1, mut q1) =
        (BigInt::zero(), BigInt::one(), BigInt::one(), BigInt::zero());
    let limit = BigInt::from(10u64.pow(12));
    for _ in 0..80 {
        let a = x.floor().to_integer();
        let (p2, q2) = (&a * &p1 + &p0, &a * &q1 + &q0);
        if q2 > limit {
            return None;
        }
        let c = Q::new(p2.clone(), q2.clone());
        if &c >= lo && &c <= hi {
            return Some(c);
        }
        (p0, q0, p1, q1) = (p1, q1, p2, q2);
        let rest = &x - Q::from_integer(a);
        if rest.is_zero() {
            return None;
        }
        x = rest.recip();
    }
    None
}

fn sqrt_of(r: &Q) -> Value {
    // √(a/b) = √(a·b)/b, with √(a·b) between floor and floor + 1 at scale.
    let ab: BigUint = (r.numer() * r.denom()).to_biguint().expect("not below 0");
    let below = r.denom().clone();
    let root = ab.sqrt();
    if &root * &root == ab {
        return Value::Exact(Q::new(BigInt::from(root), below));
    }
    let scaled = (ab << (2 * BITS as usize)).sqrt();
    let at = BigInt::from(scaled) * &below;
    let unit = BigInt::one() << BITS;
    rounded(
        Q::new(at.clone(), &unit * &below * &below),
        Q::new(at + &below, unit * &below * &below),
    )
}

fn value(e: &Real) -> Result<Value, &'static str> {
    let both = |x: &Real, y: &Real| -> Result<(Value, Value), &'static str> {
        Ok((value(x)?, value(y)?))
    };
    Ok(match e {
        Real::Num(n) => Value::Exact(Q::from_integer(n.clone())),
        Real::Root(x) => {
            let under = value(x)?;
            let Some(r) = rational(&under) else {
                return Err(NOT_RATIONAL);
            };
            if r.is_negative() {
                return Err(BELOW_ZERO);
            }
            sqrt_of(&r)
        }
        Real::Neg(x) => match value(x)? {
            Value::Exact(v) => Value::Exact(-v),
            Value::Between(lo, hi) => Value::Between(-hi, -lo),
        },
        Real::Add(x, y) => match both(x, y)? {
            (Value::Exact(a), Value::Exact(c)) => Value::Exact(a + c),
            (a, c) => {
                let ((a0, a1), (c0, c1)) = (a.ends(), c.ends());
                rounded(a0 + c0, a1 + c1)
            }
        },
        Real::Sub(x, y) => match both(x, y)? {
            (Value::Exact(a), Value::Exact(c)) => Value::Exact(a - c),
            (a, c) => {
                let ((a0, a1), (c0, c1)) = (a.ends(), c.ends());
                rounded(a0 - c1, a1 - c0)
            }
        },
        Real::Mul(x, y) => {
            let (a, c) = both(x, y)?;
            times(&a, &c)
        }
        Real::Div(x, y) => {
            let (a, c) = both(x, y)?;
            over(&a, &c)?
        }
        Real::Pow(x, k) => {
            let base = value(x)?;
            let mut out = Value::Exact(Q::one());
            for _ in 0..k.unsigned_abs() {
                out = times(&out, &base);
            }
            if *k < 0 {
                over(&Value::Exact(Q::one()), &out)?
            } else {
                out
            }
        }
    })
}

fn times(a: &Value, c: &Value) -> Value {
    if let (Value::Exact(a), Value::Exact(c)) = (a, c) {
        return Value::Exact(a * c);
    }
    let ((a0, a1), (c0, c1)) = (a.ends(), c.ends());
    let all = [&a0 * &c0, &a0 * &c1, &a1 * &c0, &a1 * &c1];
    let lo = all.iter().min().unwrap().clone();
    let hi = all.iter().max().unwrap().clone();
    rounded(lo, hi)
}

fn over(a: &Value, c: &Value) -> Result<Value, &'static str> {
    match is_zero(c) {
        Some(true) => return Err(DIVIDES_BY_ZERO),
        Some(false) => {}
        None => panic!("the judge cannot tell whether a divisor is 0: {c:?}"),
    }
    if let (Value::Exact(a), Value::Exact(c)) = (a, c) {
        return Ok(Value::Exact(a / c));
    }
    let (c0, c1) = c.ends();
    Ok(times(
        a,
        &Value::Between(c1.recip().min(c0.recip()), c1.recip().max(c0.recip())),
    ))
}

/// Whether a term writes a square root anywhere.
fn has_root(e: &Real) -> bool {
    match e {
        Real::Num(_) => false,
        Real::Root(_) => true,
        Real::Neg(x) | Real::Pow(x, _) => has_root(x),
        Real::Add(x, y) | Real::Sub(x, y) | Real::Mul(x, y) | Real::Div(x, y) => {
            has_root(x) || has_root(y)
        }
    }
}

/// Every refusal some part of the term is stopped by.
fn refusals(e: &Real, out: &mut Vec<&'static str>) {
    if let Err(why) = value(e) {
        if !out.contains(&why) {
            out.push(why);
        }
    }
    match e {
        Real::Num(_) => {}
        Real::Root(x) | Real::Neg(x) | Real::Pow(x, _) => refusals(x, out),
        Real::Add(x, y) | Real::Sub(x, y) | Real::Mul(x, y) | Real::Div(x, y) => {
            refusals(x, out);
            refusals(y, out);
        }
    }
}

/// Whether the claim is past the method's limits: the one drawn on purpose,
/// four primes raised to the eighth power.
fn past_limits(e: &Real) -> bool {
    matches!(e, Real::Pow(_, 8))
}

/// What `real arithmetic` should make of the claim (`METHODS.md`).
pub fn judged(c: &Claim) -> Verdict {
    let terms: Vec<&Real> = match c {
        Claim::Rel(_, a, b) => vec![a, b],
        Claim::Member(a, _) => vec![a],
    };
    // A claim of numerals alone is worked out all the same; one that holds
    // is refused as arithmetic's, and one that fails is false.
    if !terms.iter().any(|t| has_root(t)) {
        return match decided(c, &terms) {
            Verdict::Holds(true) => Verdict::Refused(vec![NO_ROOT]),
            other => other,
        };
    }
    decided(c, &terms)
}

/// `judged`, with no word of whether the claim takes a root.
fn decided(c: &Claim, terms: &[&Real]) -> Verdict {
    let mut all = Vec::new();
    for t in terms {
        refusals(t, &mut all);
    }
    if !all.is_empty() {
        return Verdict::Refused(all);
    }
    if terms.iter().any(|t| past_limits(t)) {
        return Verdict::Refused(vec![TOO_LARGE]);
    }
    let values: Vec<Value> = terms.iter().map(|t| value(t).unwrap()).collect();
    match c {
        Claim::Rel(rel, _, _) => {
            let gap = match (&values[0], &values[1]) {
                (Value::Exact(a), Value::Exact(c)) => Value::Exact(a - c),
                (a, c) => {
                    let ((a0, a1), (c0, c1)) = (a.ends(), c.ends());
                    Value::Between(a0 - c1, a1 - c0)
                }
            };
            match rel {
                Rel::Eq | Rel::Ne => {
                    let zero = is_zero(&gap)
                        .unwrap_or_else(|| panic!("the judge cannot tell {c:?}"));
                    Verdict::Holds(zero == matches!(rel, Rel::Eq))
                }
                Rel::Lt | Rel::Le => {
                    let (Some(a), Some(b)) =
                        (rational(&values[0]), rational(&values[1]))
                    else {
                        return Verdict::Refused(vec![UNDECIDED]);
                    };
                    Verdict::Holds(if matches!(rel, Rel::Lt) {
                        a < b
                    } else {
                        a <= b
                    })
                }
            }
        }
        Claim::Member(_, system) => match (system, rational(&values[0])) {
            (System::Real, _) => Verdict::Holds(true),
            (_, None) => Verdict::Refused(vec![UNDECIDED]),
            (System::Rat, Some(_)) => Verdict::Holds(true),
            (System::Int, Some(v)) => Verdict::Holds(v.is_integer()),
            (System::Nat, Some(v)) => Verdict::Holds(v.is_integer() && v.is_positive()),
        },
    }
}
