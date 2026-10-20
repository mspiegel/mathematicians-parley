//! Claims for `real arithmetic` holding π, e and logarithms, drawn and
//! judged by construction.
//!
//! An interval around a value cannot tell a false claim from one the method
//! does not decide, π = e among them, so these are judged by the test's own
//! polynomial arithmetic over the atoms π, e and ln p: each term is worked to
//! a polynomial, a logarithm of a positive rational by the test's own
//! factoring and an exponential of k + ln r to r·eᵏ, and two sides are
//! compared as polynomials. Their difference is 0, and the sides are equal;
//! or rational, or rational multiples of logarithms of primes, and the claim
//! is decided against them (`METHODS.md`); or anything else, and the claim
//! is not decided.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use parley::formula::grammar::Grammar;
use parley::formula::node::Node;
use parley::formula::page::numeral;
use parley::formula::Sort;

use crate::gen::{made, Drawn};
use crate::judge::Verdict;
use crate::shared::Random;

type Q = BigRational;

/// The method's refusals and its word for a claim it does not decide.
pub const UNDECIDED: &str = "real arithmetic does not decide it";
pub const LN_NOT_POSITIVE: &str = "takes the logarithm of a number not above 0";
pub const LN_NOT_RATIONAL: &str = "takes the logarithm of a number that is neither";
pub const EXP_OUT_OF_RANGE: &str = "takes the exponential of a number that is not";
pub const DIVIDES_BY_ATOM: &str = "divides by a number holding π, e or a logarithm";
pub const NUMERALS_ALONE: &str = "a claim of numerals alone cites arithmetic";

/// An atom of the test's polynomials.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Atom {
    Pi,
    E,
    Ln(u64),
}

/// A product of powers of atoms.
type Monomial = BTreeMap<Atom, u32>;

/// A polynomial over the atoms with rational coefficients, none of them 0.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Poly(BTreeMap<Monomial, Q>);

impl Poly {
    fn constant(q: Q) -> Poly {
        let mut out = Poly::default();
        out.add(Monomial::new(), q);
        out
    }

    fn atom(a: Atom) -> Poly {
        let mut out = Poly::default();
        out.add(Monomial::from([(a, 1)]), Q::one());
        out
    }

    fn add(&mut self, m: Monomial, q: Q) {
        let held = self.0.entry(m.clone()).or_insert_with(Q::zero);
        *held += q;
        if held.is_zero() {
            self.0.remove(&m);
        }
    }

    fn plus(&self, other: &Poly) -> Poly {
        let mut out = self.clone();
        for (m, q) in &other.0 {
            out.add(m.clone(), q.clone());
        }
        out
    }

    fn scaled(&self, by: &Q) -> Poly {
        let mut out = Poly::default();
        for (m, q) in &self.0 {
            out.add(m.clone(), q * by);
        }
        out
    }

    fn times(&self, other: &Poly) -> Poly {
        let mut out = Poly::default();
        for (m, q) in &self.0 {
            for (n, r) in &other.0 {
                let mut joined = m.clone();
                for (a, k) in n {
                    *joined.entry(*a).or_insert(0) += k;
                }
                out.add(joined, q * r);
            }
        }
        out
    }

    /// The polynomial where it holds no atom.
    fn rational(&self) -> Option<Q> {
        match self.0.iter().collect::<Vec<_>>().as_slice() {
            [] => Some(Q::zero()),
            [(m, q)] if m.is_empty() => Some((*q).clone()),
            _ => None,
        }
    }

    /// Whether it is rational multiples of logarithms of primes, and not 0.
    fn logarithms_only(&self) -> bool {
        !self.0.is_empty()
            && self.0.keys().all(|m| {
                matches!(m.iter().collect::<Vec<_>>().as_slice(), [(Atom::Ln(_), 1)])
            })
    }
}

/// A term holding π, e and logarithms of rationals.
#[derive(Clone, Debug)]
pub enum Term {
    Num(i64),
    /// a/b, b not 0.
    Ratio(i64, i64),
    Pi,
    E,
    Ln(Box<Term>),
    Exp(Box<Term>),
    Neg(Box<Term>),
    Add(Box<Term>, Box<Term>),
    Sub(Box<Term>, Box<Term>),
    Mul(Box<Term>, Box<Term>),
    Div(Box<Term>, Box<Term>),
    /// A power to a whole exponent of at least 0.
    Pow(Box<Term>, u32),
}

fn b(t: Term) -> Box<Term> {
    Box::new(t)
}

/// A claim of this family.
#[derive(Clone, Debug)]
pub enum Claim {
    Equal(Term, Term),
    Apart(Term, Term),
    Below(Term, Term),
    /// The term in ℝ, or with `false`, in ℚ.
    Member(Term, bool),
}

// --- the judge's own working --------------------------------------------------

/// A positive whole number's primes, each with its exponent, by trial
/// division.
fn factor(mut n: u64, sign: i64, out: &mut BTreeMap<u64, i64>) {
    let mut p = 2;
    while p * p <= n {
        while n.is_multiple_of(p) {
            n /= p;
            *out.entry(p).or_insert(0) += sign;
        }
        p += 1;
    }
    if n > 1 {
        *out.entry(n).or_insert(0) += sign;
    }
}

/// What the term is, or the refusal that stops it.
fn worked(t: &Term) -> Result<Poly, &'static str> {
    Ok(match t {
        Term::Num(n) => Poly::constant(Q::from_integer(BigInt::from(*n))),
        Term::Ratio(a, d) => Poly::constant(Q::new(BigInt::from(*a), BigInt::from(*d))),
        Term::Pi => Poly::atom(Atom::Pi),
        Term::E => Poly::atom(Atom::E),
        Term::Ln(x) => {
            let x = worked(x)?;
            // q·eᵏ, q a positive rational: the only arguments taken.
            let (q, k) = match x.0.iter().collect::<Vec<_>>().as_slice() {
                [] => return Err(LN_NOT_POSITIVE),
                [(m, q)] if m.is_empty() => ((*q).clone(), 0),
                [(m, q)] => match m.iter().collect::<Vec<_>>().as_slice() {
                    [(Atom::E, k)] => ((*q).clone(), **k),
                    _ => return Err(LN_NOT_RATIONAL),
                },
                _ => return Err(LN_NOT_RATIONAL),
            };
            if !q.is_positive() {
                return Err(LN_NOT_POSITIVE);
            }
            let mut primes = BTreeMap::new();
            factor(q.numer().try_into().unwrap(), 1, &mut primes);
            factor(q.denom().try_into().unwrap(), -1, &mut primes);
            let mut out = Poly::constant(Q::from_integer(BigInt::from(k)));
            for (p, n) in primes.into_iter().filter(|(_, n)| *n != 0) {
                out = out.plus(
                    &Poly::atom(Atom::Ln(p)).scaled(&Q::from_integer(BigInt::from(n))),
                );
            }
            out
        }
        Term::Exp(x) => {
            let x = worked(x)?;
            let mut k = Q::zero();
            let mut r = Q::one();
            for (m, q) in &x.0 {
                match m.iter().collect::<Vec<_>>().as_slice() {
                    [] => k = q.clone(),
                    [(Atom::Ln(p), 1)] if q.is_integer() => {
                        let n: i32 =
                            q.to_integer().try_into().map_err(|_| EXP_OUT_OF_RANGE)?;
                        r *= Q::from_integer(BigInt::from(*p)).pow(n);
                    }
                    _ => return Err(EXP_OUT_OF_RANGE),
                }
            }
            if !k.is_integer() || k.is_negative() {
                return Err(EXP_OUT_OF_RANGE);
            }
            let k: u32 = k.to_integer().try_into().map_err(|_| EXP_OUT_OF_RANGE)?;
            let mut out = Poly::constant(r);
            for _ in 0..k {
                out = out.times(&Poly::atom(Atom::E));
            }
            out
        }
        Term::Neg(x) => worked(x)?.scaled(&-Q::one()),
        Term::Add(x, y) => worked(x)?.plus(&worked(y)?),
        Term::Sub(x, y) => worked(x)?.plus(&worked(y)?.scaled(&-Q::one())),
        Term::Mul(x, y) => worked(x)?.times(&worked(y)?),
        Term::Div(x, y) => {
            let (x, y) = (worked(x)?, worked(y)?);
            match y.rational() {
                Some(q) if q.is_zero() => return Err("divides by zero"),
                Some(q) => x.scaled(&q.recip()),
                None => return Err(DIVIDES_BY_ATOM),
            }
        }
        Term::Pow(x, k) => {
            let x = worked(x)?;
            let mut out = Poly::constant(Q::one());
            for _ in 0..*k {
                out = out.times(&x);
            }
            out
        }
    })
}

/// Whether a term writes π, e, a logarithm or an exponential.
fn has_atom(t: &Term) -> bool {
    match t {
        Term::Num(_) | Term::Ratio(..) => false,
        Term::Pi | Term::E | Term::Ln(_) | Term::Exp(_) => true,
        Term::Neg(x) | Term::Pow(x, _) => has_atom(x),
        Term::Add(x, y) | Term::Sub(x, y) | Term::Mul(x, y) | Term::Div(x, y) => {
            has_atom(x) || has_atom(y)
        }
    }
}

/// What `real arithmetic` should make of the claim: one of numerals alone
/// that holds is refused as `arithmetic`'s, and one that fails is false.
pub fn judged(c: &Claim) -> Verdict {
    let terms: Vec<&Term> = match c {
        Claim::Equal(a, b) | Claim::Apart(a, b) | Claim::Below(a, b) => vec![a, b],
        Claim::Member(a, _) => vec![a],
    };
    match decided(c) {
        Verdict::Holds(true) if !terms.iter().any(|t| has_atom(t)) => {
            Verdict::Refused(vec![NUMERALS_ALONE])
        }
        other => other,
    }
}

/// `judged`, with no word of whether the claim holds an atom.
fn decided(c: &Claim) -> Verdict {
    let pair = |a: &Term, b: &Term| -> Result<(Poly, Poly), &'static str> {
        Ok((worked(a)?, worked(b)?))
    };
    let refused = |why: &'static str| Verdict::Refused(vec![why]);
    match c {
        Claim::Equal(a, b) | Claim::Apart(a, b) => {
            let (a, b) = match pair(a, b) {
                Ok(both) => both,
                Err(why) => return refused(why),
            };
            let gap = a.plus(&b.scaled(&-Q::one()));
            let equal = gap.0.is_empty();
            if !equal && gap.rational().is_none() && !gap.logarithms_only() {
                return refused(UNDECIDED);
            }
            Verdict::Holds(equal == matches!(c, Claim::Equal(..)))
        }
        Claim::Below(a, b) => match pair(a, b) {
            Err(why) => refused(why),
            Ok((a, b)) => match above_zero(&b.plus(&a.scaled(&-Q::one()))) {
                Some(holds) => Verdict::Holds(holds),
                None => refused(UNDECIDED),
            },
        },
        Claim::Member(a, real) => match worked(a) {
            Err(why) => refused(why),
            Ok(_) if *real => Verdict::Holds(true),
            Ok(p) => match p.rational() {
                Some(_) => Verdict::Holds(true),
                None => refused(UNDECIDED),
            },
        },
    }
}

// --- order -----------------------------------------------------------------------

/// Whether a value is above 0, as `METHODS.md` says the method decides it:
/// 0 is not; a rational by its sign; rational multiples of logarithms of
/// primes by whether Π p^(n·qₚ) is above 1, n clearing the denominators;
/// and anything else by its bracket, where the bracket lies on one side of
/// 0. None where it does not. A sign so found is held to the value worked
/// out from π, e and the logarithms to 35 digits.
fn above_zero(gap: &Poly) -> Option<bool> {
    if gap.0.is_empty() {
        return Some(false);
    }
    if let Some(q) = gap.rational() {
        return Some(q.is_positive());
    }
    let sign = if gap.logarithms_only() {
        let scale = gap.0.values().fold(BigInt::one(), |d, q| {
            num_integer::Integer::lcm(&d, q.denom())
        });
        let (mut over, mut under) = (BigInt::one(), BigInt::one());
        for (m, q) in &gap.0 {
            let (Atom::Ln(p), _) = m.iter().next().expect("one logarithm") else {
                unreachable!("logarithms only")
            };
            let n = (q * Q::from_integer(scale.clone())).to_integer();
            let power = BigInt::from(*p).pow(n.magnitude().try_into().unwrap());
            if n.is_positive() {
                over *= power;
            } else {
                under *= power;
            }
        }
        over > under
    } else {
        let (low, high) = bracket(gap);
        if !low.is_negative() {
            true
        } else if !high.is_positive() {
            false
        } else {
            return None;
        }
    };
    let near = estimate(gap);
    assert!(
        near.abs() < Q::new(BigInt::one(), BigInt::from(10u64).pow(20))
            || near.is_positive() == sign,
        "the judge's sign for {gap:?} is not the value's"
    );
    Some(sign)
}

/// The ends of a value's bracket: each atom between two rationals, π
/// between 3 and 4, e between 2 and 3, ln p as `ln_ends` has it; a
/// monomial between the products of its atoms' ends; a part between its
/// coefficient times those, the other way round where the coefficient is
/// below 0; and the sum between the sums.
fn bracket(p: &Poly) -> (Q, Q) {
    let (mut low, mut high) = (Q::zero(), Q::zero());
    for (m, q) in &p.0 {
        let (mut l, mut h) = (Q::one(), Q::one());
        for (atom, k) in m {
            let (al, ah) = match atom {
                Atom::Pi => (Q::from_integer(3.into()), Q::from_integer(4.into())),
                Atom::E => (Q::from_integer(2.into()), Q::from_integer(3.into())),
                Atom::Ln(p) => ln_ends(*p),
            };
            l *= al.pow(*k as i32);
            h *= ah.pow(*k as i32);
        }
        if q.is_positive() {
            low += q * l;
            high += q * h;
        } else {
            low += q * h;
            high += q * l;
        }
    }
    (low, high)
}

/// ln p between a/b, the greatest with b at most 8 and 3ᵃ ≤ pᵇ, and a/b,
/// the least with b at most 8 and pᵇ ≤ 2ᵃ.
fn ln_ends(p: u64) -> (Q, Q) {
    let mut low = Q::zero();
    let mut high: Option<Q> = None;
    for b in 1..=8u32 {
        let power = BigInt::from(p).pow(b);
        let mut a = 0i64;
        while BigInt::from(3).pow(a as u32 + 1) <= power {
            a += 1;
        }
        low = low.max(Q::new(a.into(), b.into()));
        let mut a = 0i64;
        while BigInt::from(2).pow(a as u32) < power {
            a += 1;
        }
        let up = Q::new(a.into(), b.into());
        high = Some(high.map_or(up.clone(), |h| h.min(up)));
    }
    (low, high.expect("a denominator"))
}

/// The value worked out from π, e and the logarithms of 2, 3 and 5 to 35
/// digits.
fn estimate(p: &Poly) -> Q {
    let digits = |s: &str| {
        let (whole, frac) = s.split_once('.').unwrap();
        let top: BigInt = format!("{whole}{frac}").parse().unwrap();
        Q::new(top, BigInt::from(10u64).pow(frac.len() as u32))
    };
    let value = |a: &Atom| match a {
        Atom::Pi => digits("3.14159265358979323846264338327950288"),
        Atom::E => digits("2.71828182845904523536028747135266250"),
        Atom::Ln(2) => digits("0.69314718055994530941723212145817657"),
        Atom::Ln(3) => digits("1.09861228866810969139524523692252570"),
        Atom::Ln(5) => digits("1.60943791243410037460075933322618764"),
        Atom::Ln(p) => panic!("no value of ln {p} is written here"),
    };
    p.0.iter()
        .map(|(m, q)| {
            m.iter()
                .fold(q.clone(), |acc, (a, k)| acc * value(a).pow(*k as i32))
        })
        .fold(Q::zero(), |s, x| s + x)
}

// --- drawing -------------------------------------------------------------------

const PRIMES: [u64; 3] = [2, 3, 5];

/// A positive rational of small primes, as the page writes it.
fn ratio_drawn(r: &mut Random) -> Term {
    let pick = |r: &mut Random| PRIMES[r.below(3) as usize] as i64;
    let top = (0..r.below(3)).fold(1, |acc, _| acc * pick(r));
    let below = (0..r.below(2)).fold(1, |acc, _| acc * pick(r));
    if below == 1 {
        Term::Num(top)
    } else {
        Term::Ratio(top, below)
    }
}

/// A term at most `depth` deep, of π, e, logarithms of rationals and small
/// numerals, by +, −, · and squares.
fn term_drawn(r: &mut Random, depth: u32) -> Term {
    if depth == 0 || r.below(3) == 0 {
        return match r.below(5) {
            0 => Term::Pi,
            1 => Term::E,
            2 | 3 => Term::Ln(b(ratio_drawn(r))),
            _ => Term::Num(r.below(7) as i64 - 2),
        };
    }
    let sub = |r: &mut Random| b(term_drawn(r, depth - 1));
    match r.below(5) {
        0 => Term::Neg(sub(r)),
        1 => Term::Add(sub(r), sub(r)),
        2 => Term::Sub(sub(r), sub(r)),
        3 => Term::Mul(sub(r), sub(r)),
        _ => Term::Pow(sub(r), 2),
    }
}

/// The polynomial written out as the page would: its parts added, each a
/// coefficient times its atoms' powers.
fn spelt(p: &Poly) -> Term {
    let mut out: Option<Term> = None;
    for (m, q) in &p.0 {
        let coefficient = if q.is_integer() {
            Term::Num(q.to_integer().try_into().unwrap())
        } else {
            Term::Ratio(q.numer().try_into().unwrap(), q.denom().try_into().unwrap())
        };
        let part = m.iter().fold(coefficient, |acc, (a, k)| {
            let atom = match a {
                Atom::Pi => Term::Pi,
                Atom::E => Term::E,
                Atom::Ln(p) => Term::Ln(b(Term::Num(*p as i64))),
            };
            let power = if *k == 1 {
                atom
            } else {
                Term::Pow(b(atom), *k)
            };
            Term::Mul(b(acc), b(power))
        });
        out = Some(match out {
            None => part,
            Some(sum) => Term::Add(b(sum), b(part)),
        });
    }
    out.unwrap_or(Term::Num(0))
}

/// A claim of this family: an identity and its expansion, moved or not; a
/// logarithm or exponential and its value; a disequality, an order, a
/// membership; or a refusal.
pub fn draw(r: &mut Random) -> Claim {
    match r.below(9) {
        8 => {
            // Orders the bounds decide and orders they do not: π and e
            // against rationals near their bounds and each other, a
            // logarithm against a rational, and two multiples of
            // logarithms.
            let tenths =
                |r: &mut Random, from: i64| Term::Ratio(from + r.below(30) as i64, 10);
            let (a, c) = match r.below(4) {
                0 => {
                    let atom = [Term::Pi, Term::E][r.below(2) as usize].clone();
                    (atom, tenths(r, 15))
                }
                1 => (
                    Term::Mul(b(Term::Num(1 + r.below(2) as i64)), b(Term::E)),
                    Term::Pi,
                ),
                2 => (Term::Ln(b(ratio_drawn(r))), tenths(r, -5)),
                _ => (
                    Term::Mul(
                        b(Term::Num(1 + r.below(3) as i64)),
                        b(Term::Ln(b(ratio_drawn(r)))),
                    ),
                    Term::Ln(b(ratio_drawn(r))),
                ),
            };
            match r.below(2) {
                0 => Claim::Below(a, c),
                _ => Claim::Below(c, a),
            }
        }
        0..=2 => {
            let t = term_drawn(r, 3);
            let expanded = worked(&t).expect("a drawn term has a value");
            let moved = match r.below(5) {
                0 => Term::Add(b(spelt(&expanded)), b(Term::Num(1))),
                1 => Term::Add(b(spelt(&expanded)), b(Term::Ln(b(Term::Num(2))))),
                2 => Term::Add(b(spelt(&expanded)), b(Term::Pi)),
                _ => spelt(&expanded),
            };
            Claim::Equal(t, moved)
        }
        3 => {
            // exp(k + ln q) = q·eᵏ, or one away.
            let k = r.below(3) as i64;
            let q = ratio_drawn(r);
            let argument = Term::Add(b(Term::Num(k)), b(Term::Ln(b(q.clone()))));
            let value = worked(&Term::Exp(b(argument.clone())))
                .expect("an exponential's value");
            let said = match r.below(3) {
                0 => Term::Add(b(spelt(&value)), b(Term::Num(1))),
                _ => spelt(&value),
            };
            Claim::Equal(Term::Exp(b(argument)), said)
        }
        4 => {
            let (a, c) = (term_drawn(r, 2), term_drawn(r, 2));
            Claim::Apart(a, c)
        }
        5 => {
            let a = match r.below(2) {
                0 => Term::Exp(b(Term::Ln(b(ratio_drawn(r))))),
                _ => term_drawn(r, 2),
            };
            Claim::Below(a, Term::Num(r.below(9) as i64))
        }
        6 => {
            let a = match r.below(2) {
                0 => Term::Exp(b(Term::Ln(b(ratio_drawn(r))))),
                _ => term_drawn(r, 2),
            };
            Claim::Member(a, r.below(2) == 0)
        }
        _ => {
            let t = match r.below(5) {
                0 => Term::Ln(b(Term::Num(-(r.below(3) as i64)))),
                1 => Term::Ln(b(Term::Pi)),
                2 => Term::Exp(b(Term::Ratio(1, 2))),
                3 => Term::Exp(b(Term::Num(-1))),
                _ => Term::Div(b(Term::Num(1)), b(Term::Pi)),
            };
            Claim::Equal(t.clone(), t)
        }
    }
}

// --- writing ---------------------------------------------------------------------

fn node(g: &Grammar, t: &Term) -> Node {
    let two = |x: &Term, y: &Term, p: &str| made(g, p, vec![node(g, x), node(g, y)]);
    let applied = |name: &str, x: &Term| {
        made(
            g,
            "_(_)",
            vec![
                Node::name(Sort::of("function from number to number"), name),
                node(g, x),
            ],
        )
    };
    let whole = |n: i64| {
        let n_node = numeral(&n.unsigned_abs().to_string());
        if n < 0 {
            made(g, "−_", vec![n_node])
        } else {
            n_node
        }
    };
    match t {
        Term::Num(n) => whole(*n),
        Term::Ratio(a, d) => made(g, "_ / _", vec![whole(*a), whole(*d)]),
        Term::Pi => made(g, "π", Vec::new()),
        Term::E => made(g, "e", Vec::new()),
        Term::Ln(x) => applied("ln", x),
        Term::Exp(x) => applied("exp", x),
        Term::Neg(x) => made(g, "−_", vec![node(g, x)]),
        Term::Add(x, y) => two(x, y, "_ + _"),
        Term::Sub(x, y) => two(x, y, "_ − _"),
        Term::Mul(x, y) => two(x, y, "_ · _"),
        Term::Div(x, y) => two(x, y, "_ / _"),
        Term::Pow(x, k) => made(g, "_^_", vec![node(g, x), numeral(&k.to_string())]),
    }
}

fn written(g: &Grammar, c: &Claim) -> String {
    let n = match c {
        Claim::Equal(a, c) => made(g, "_ = _", vec![node(g, a), node(g, c)]),
        Claim::Apart(a, c) => made(g, "_ ≠ _", vec![node(g, a), node(g, c)]),
        Claim::Below(a, c) => made(g, "_ < _", vec![node(g, a), node(g, c)]),
        Claim::Member(a, real) => made(
            g,
            "_ ∈ _",
            vec![
                node(g, a),
                made(g, if *real { "ℝ" } else { "ℚ" }, Vec::new()),
            ],
        ),
    };
    g.print(&n)
}

/// A claim of this family for `real arithmetic`, drawn and judged.
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
