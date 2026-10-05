//! Equality of rational expressions over a field, as `METHODS.md` has it.
//!
//! `algebra` is the second method that decides rather than looks up, and it
//! differs from `inequalities` in two ways: it is not restricted to linear
//! expressions, and it knows nothing about order. Deciding it is done here;
//! emitting the Metamath proof of what was decided is [`super::normal`].
//!
//! An atom is a maximal subterm not built from numerals by `+`, `−`, unary
//! minus, `·`, `/`, and powers **with a numeral exponent**. The exponent rule
//! is the whole of the boundary: in `(2k + 1)² = 4k² + 4k + 1` the exponent is
//! 2, so the square is expanded and the only atom is `k`; in `2^k + 2^k = 2^k·2`
//! the exponent is a variable, so `2^k` is an atom and the step is `x + x = x·2`.
//!
//! A term reads as a quotient of two polynomials over those atoms. Two are
//! equal when the cross product of their numerators and denominators vanishes,
//! which is the identity the corpus's steps state; that the denominators are
//! not zero is a hypothesis the text writes as a `requires` line, and is not
//! decided here.

use std::cmp::Reverse;
use std::rc::Rc;
use std::sync::{LazyLock, Mutex};

use indexmap::IndexMap;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};

use crate::mm::kernel::{FloatLabels, Term};
use crate::outcome::{Built, Declined, Route};
use crate::rules::digit_of;

pub const ADD: &str = "caddc";
pub const SUB: &str = "cmin";
pub const MUL: &str = "cmul";
pub const DIV: &str = "cdiv";
pub const EXP: &str = "cexp";
pub const NEG: &str = "cneg";

/// An exponent past anything the corpus writes.
pub const CAP: i64 = 24;

/// An exact rational.
pub type Q = BigRational;

pub fn q(n: i64) -> Q {
    BigRational::from_integer(BigInt::from(n))
}

/// A whole number as set.mm spells it: a digit's constant, or a decimal
/// (`numerals::spell`). Each spelling is made once and kept for the run, so
/// that it is lent out as a digit's constant is.
pub fn numeral(value: u32) -> &'static str {
    static SPELT: LazyLock<Mutex<IndexMap<u32, &'static str>>> =
        LazyLock::new(Default::default);
    let mut spelt = SPELT.lock().unwrap_or_else(|e| e.into_inner());
    spelt.entry(value).or_insert_with(|| {
        Box::leak(super::numerals::spell(value as u64).into_boxed_str())
    })
}

/// A monomial: (atom, power) pairs in atom order, so the empty one is the
/// constant one and two spellings of a product are one key.
pub type Monomial = Vec<(Rc<str>, u32)>;

/// A polynomial over atoms, as coefficients by monomial, in the order the
/// monomials were first met.
#[derive(Clone, Debug, Default)]
pub struct Poly {
    pub terms: IndexMap<Monomial, Q>,
}

impl PartialEq for Poly {
    fn eq(&self, other: &Poly) -> bool {
        self.terms.len() == other.terms.len()
            && self
                .terms
                .iter()
                .all(|(k, v)| other.terms.get(k) == Some(v))
    }
}

impl Poly {
    pub fn new(terms: IndexMap<Monomial, Q>) -> Poly {
        Poly {
            terms: terms.into_iter().filter(|(_, v)| !v.is_zero()).collect(),
        }
    }

    pub fn zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn plus(&self, other: &Poly) -> Poly {
        let mut out = self.terms.clone();
        for (monomial, weight) in &other.terms {
            let held = out.entry(monomial.clone()).or_insert_with(Q::zero);
            *held += weight;
        }
        Poly::new(out)
    }

    pub fn scaled(&self, by: &Q) -> Poly {
        Poly::new(
            self.terms
                .iter()
                .map(|(k, v)| (k.clone(), v * by))
                .collect(),
        )
    }

    pub fn minus(&self, other: &Poly) -> Poly {
        self.plus(&other.scaled(&q(-1)))
    }

    pub fn times(&self, other: &Poly) -> Poly {
        let mut out: IndexMap<Monomial, Q> = IndexMap::new();
        for (left, a) in &self.terms {
            for (right, b) in &other.terms {
                let held = out.entry(join(left, right)).or_insert_with(Q::zero);
                *held += a * b;
            }
        }
        Poly::new(out)
    }

    pub fn power(&self, by: u32) -> Poly {
        let mut out = one();
        for _ in 0..by {
            out = out.times(self);
        }
        out
    }

    /// The largest monomial, in the order the keys sort in.
    pub fn lead(&self) -> Option<&Monomial> {
        self.terms.keys().max()
    }
}

/// One monomial from two, adding the powers of a shared atom.
fn join(left: &Monomial, right: &Monomial) -> Monomial {
    let mut powers: IndexMap<Rc<str>, u32> = left.iter().cloned().collect();
    for (atom, power) in right {
        *powers.entry(atom.clone()).or_insert(0) += power;
    }
    let mut out: Monomial = powers.into_iter().filter(|(_, p)| *p != 0).collect();
    out.sort();
    out
}

pub fn constant(value: Q) -> Poly {
    let mut terms = IndexMap::new();
    terms.insert(Vec::new(), value);
    Poly::new(terms)
}

pub fn one() -> Poly {
    constant(q(1))
}

pub fn atom(said: &str) -> Poly {
    let mut terms = IndexMap::new();
    terms.insert(vec![(Rc::from(said), 1)], q(1));
    Poly::new(terms)
}

/// Descending degree, then by atom: the order a polynomial is written in,
/// so that `4m^2 + 4m + 1` comes out that way round rather than the other.
pub fn order(monomial: &Monomial) -> (Reverse<u32>, Monomial) {
    let degree = monomial.iter().map(|(_, p)| p).sum();
    (Reverse(degree), monomial.clone())
}

/// One monomial in reverse Polish, as a product of powers.
///
/// Every factor is written `( x ^ k )`, the exponent one included, and the
/// empty monomial is `1`. The product associates to the left.
pub fn spell_monomial(monomial: &Monomial) -> String {
    if monomial.is_empty() {
        return numeral(1).to_string();
    }
    let said: Vec<String> = monomial
        .iter()
        .map(|(atom, power)| format!("{atom} {} cexp co", numeral(*power)))
        .collect();
    let mut out = said[0].clone();
    for one in &said[1..] {
        out = format!("{out} {one} cmul co");
    }
    out
}

/// A rational coefficient as a numeral, negated where it is negative; None
/// where it is not a whole number.
pub fn spell_coefficient(weight: &Q) -> Option<String> {
    if !weight.is_integer() {
        return None;
    }
    let whole = weight.to_integer().to_i64()?;
    let said = super::numerals::spell(whole.unsigned_abs());
    Some(if whole < 0 {
        format!("{said} cneg")
    } else {
        said
    })
}

/// A polynomial as one term in reverse Polish: the canonical form.
///
/// Both sides of an `algebra` step are driven to this, and the step is then
/// the two of them being the same term. Sums associate to the left and run
/// down in degree, and every term is `( c x. M )` with no case left out: a
/// coefficient of one is written, so is an exponent of one, and the constant
/// term is `( c x. 1 )`. What it buys is that every step of the arithmetic
/// over these forms has one shape to handle rather than four.
///
/// None where a coefficient is past what `spell_coefficient` writes.
pub fn spell(poly: &Poly) -> Option<String> {
    if poly.terms.is_empty() {
        return Some(numeral(0).to_string());
    }
    let mut monomials: Vec<&Monomial> = poly.terms.keys().collect();
    monomials.sort_by_key(|m| order(m));
    let mut said = Vec::new();
    for monomial in monomials {
        let digit = spell_coefficient(&poly.terms[monomial])?;
        said.push(format!("{digit} {} cmul co", spell_monomial(monomial)));
    }
    let mut out = said[0].clone();
    for one in &said[1..] {
        out = format!("{out} {one} caddc co");
    }
    Some(out)
}

/// A polynomial over a polynomial, which is what a term reads as.
#[derive(Clone, Debug)]
pub struct Quotient {
    pub over: Poly,
    pub under: Poly,
}

impl Quotient {
    pub fn whole(over: Poly) -> Quotient {
        Quotient { over, under: one() }
    }

    pub fn plus(&self, other: &Quotient) -> Quotient {
        Quotient {
            over: self
                .over
                .times(&other.under)
                .plus(&other.over.times(&self.under)),
            under: self.under.times(&other.under),
        }
    }

    pub fn minus(&self, other: &Quotient) -> Quotient {
        self.plus(&Quotient {
            over: other.over.scaled(&q(-1)),
            under: other.under.clone(),
        })
    }

    pub fn times(&self, other: &Quotient) -> Quotient {
        Quotient {
            over: self.over.times(&other.over),
            under: self.under.times(&other.under),
        }
    }

    pub fn over_under(&self, other: &Quotient) -> Quotient {
        Quotient {
            over: self.over.times(&other.under),
            under: self.under.times(&other.over),
        }
    }

    pub fn power(&self, by: u32) -> Quotient {
        Quotient {
            over: self.over.power(by),
            under: self.under.power(by),
        }
    }
}

/// The whole number a term denotes, if it denotes one: a numeral of any
/// length, or one negated.
pub fn whole_number(term: &Term) -> Option<i64> {
    if let Some(n) = super::numerals::value(term) {
        return i64::try_from(n).ok();
    }
    if term.variable().is_some() {
        return None;
    }
    let label = term.label()?;
    if label == NEG && term.children().len() == 1 {
        return whole_number(&term.children()[0]).map(|n| -n);
    }
    None
}

/// The operation a `co` term applies, spelt, or None where it is no `co`.
fn operation<'t>(
    term: &'t Term,
    labels: &FloatLabels,
) -> Option<(Rc<str>, &'t Term, &'t Term)> {
    if term.variable().is_none()
        && term.label() == Some("co")
        && term.children().len() == 3
    {
        let kids = term.children();
        return Some((kids[2].rpn(labels), &kids[0], &kids[1]));
    }
    None
}

/// One term of a finite sum read as linear: its weight, the factor free of
/// the sum's letter, and the factor holding it.
#[derive(Clone, Debug)]
pub struct SumPart {
    pub weight: Q,
    pub free: Monomial,
    pub bound: Monomial,
}

/// A finite sum over a range {a, …, b} read as linear: Σ(k ∈ R) Σᵢ wᵢ·Fᵢ·Mᵢ
/// is Σᵢ wᵢ·Fᵢ·Σ(k ∈ R) Mᵢ, each Fᵢ free of k and each Mᵢ holding it
/// (`fsumadd`, `fsummulc2`). Given as the range, the letter, and the parts,
/// all spelt; None where the sum is one atom: a range that is no {a, …, b},
/// a summand that divides or holds a sum of its own, or a part free of k,
/// which would be a count of the range rather than a sum.
pub fn linear_sum(
    term: &Term,
    labels: &FloatLabels,
) -> Option<(String, String, Vec<SumPart>)> {
    if term.variable().is_some()
        || term.label() != Some("csu")
        || term.children().len() != 3
    {
        return None;
    }
    let (range, summand, letter) = (
        &term.children()[0],
        &term.children()[1],
        &term.children()[2],
    );
    let ranged = range.variable().is_none()
        && range.label() == Some("co")
        && range.children().len() == 3
        && &*range.children()[2].rpn(labels) == "cfz";
    if !ranged || summand.rpn(labels).split_whitespace().any(|t| t == "csu") {
        return None;
    }
    let letter = letter.rpn(labels).to_string();
    let read = read(summand, labels);
    if read.under != one() {
        return None;
    }
    let holds = |atom: &str| atom.split_whitespace().any(|t| t == letter);
    let mut parts = Vec::new();
    for (monomial, weight) in &read.over.terms {
        let (bound, free): (Monomial, Monomial) =
            monomial.iter().cloned().partition(|(a, _)| holds(a));
        if bound.is_empty() {
            return None;
        }
        parts.push(SumPart {
            weight: weight.clone(),
            free,
            bound,
        });
    }
    if parts.is_empty() {
        return None;
    }
    Some((range.rpn(labels).to_string(), letter, parts))
}

thread_local! {
    static LINEAR: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Run `f` with finite sums read as linear, or as atoms, by `read`. Which a
/// step takes is decided once from its text (`says_something_linear`), and
/// deciding and proving it read the same way.
pub fn reading_sums<T>(linear: bool, f: impl FnOnce() -> T) -> T {
    let was = LINEAR.with(|c| c.replace(linear));
    let out = f();
    LINEAR.with(|c| c.set(was));
    out
}

/// Whether some finite sum in `term` is linear in something: it has two
/// parts or more, or a part with a factor free of its letter. A step one of
/// whose terms is reads every sum it holds as linear; a step none of whose
/// terms is reads each sum as one atom, as a reader takes Σ in x·Σ + 0.
pub fn says_something_linear(term: &Term, labels: &FloatLabels) -> bool {
    if let Some((_, _, parts)) = linear_sum(term, labels) {
        if parts.len() > 1
            || parts.iter().any(|p| !p.free.is_empty() || p.weight != q(1))
        {
            return true;
        }
    }
    term.variable().is_none()
        && term
            .children()
            .iter()
            .any(|c| says_something_linear(c, labels))
}

/// A monomial with every occurrence of one letter respelt as another.
pub fn respelt(monomial: &Monomial, from: &str, to: &str) -> Monomial {
    monomial
        .iter()
        .map(|(atom, power)| {
            let said: Vec<&str> = atom
                .split_whitespace()
                .map(|t| if t == from { to } else { t })
                .collect();
            (Rc::from(said.join(" ")), *power)
        })
        .collect()
}

/// A term as a quotient of polynomials over its atoms.
pub fn read(term: &Term, labels: &FloatLabels) -> Quotient {
    // A finite sum is linear, where the step reads sums so: each part's sum
    // over its letter is an atom, and the letter is read as one placeholder,
    // so that two sums over different letters are one atom.
    let linear = LINEAR.with(|c| c.get());
    if let Some((range, letter, parts)) =
        linear.then(|| linear_sum(term, labels)).flatten()
    {
        let mut out = Poly::default();
        for part in parts {
            let bound = respelt(&part.bound, &letter, "§");
            let inner = format!("{range} {} § csu", spell_monomial(&bound));
            let mut free = IndexMap::new();
            free.insert(part.free.clone(), part.weight.clone());
            out = out.plus(&Poly::new(free).times(&atom(&inner)));
        }
        return Quotient::whole(out);
    }
    if let Some(whole) = whole_number(term) {
        return Quotient::whole(constant(q(whole)));
    }
    if term.variable().is_none()
        && term.label() == Some(NEG)
        && term.children().len() == 1
    {
        let inner = read(&term.children()[0], labels);
        return Quotient {
            over: inner.over.scaled(&q(-1)),
            under: inner.under,
        };
    }
    if let Some((how, left, right)) = operation(term, labels) {
        match &*how {
            ADD => return read(left, labels).plus(&read(right, labels)),
            SUB => return read(left, labels).minus(&read(right, labels)),
            MUL => return read(left, labels).times(&read(right, labels)),
            DIV => {
                let under = read(right, labels);
                if !under.over.zero() {
                    return read(left, labels).over_under(&under);
                }
            }
            EXP => {
                // The exponent rule: a numeral exponent is expanded, and any
                // other leaves the whole power an atom.
                if let Some(by) = whole_number(right) {
                    if (0..=CAP).contains(&by) {
                        return read(left, labels).power(by as u32);
                    }
                }
            }
            _ => {}
        }
    }
    Quotient::whole(atom(&term.rpn(labels)))
}

/// A claim as a polynomial that must vanish, or None if it is not one.
pub fn equation(term: &Term, labels: &FloatLabels) -> Option<Poly> {
    if term.variable().is_some() || term.label() != Some("wceq") {
        return None;
    }
    if term.children().len() != 2 {
        return None;
    }
    let left = read(&term.children()[0], labels);
    let right = read(&term.children()[1], labels);
    // p/q = r/s exactly when ps − rq vanishes, the denominators being the
    // nonzero conditions the text writes as `requires` lines.
    Some(
        left.over
            .times(&right.under)
            .minus(&right.over.times(&left.under)),
    )
}

/// The polynomial a disequality says does not vanish, or None.
///
/// The corpus writes `a ≠ 1` as a negated equation, which the `negates` line
/// of `corpus/db/notation.records` folds into one tree, so what arrives here is a
/// `wn` around the equation and the polynomial is the equation's.
pub fn denied(term: &Term, labels: &FloatLabels) -> Option<Poly> {
    if term.variable().is_some() || term.label() != Some("wn") {
        return None;
    }
    if term.children().len() != 1 {
        return None;
    }
    equation(&term.children()[0], labels)
}

/// One equation taken off a claim: which, by what multiplier, how often.
#[derive(Clone, Debug)]
pub struct Taken {
    pub which: usize,
    pub shape: Poly,
    pub scale: Q,
}

/// How the claim is a combination of the given equations, or None.
///
/// With nothing cited the claim must vanish outright, and the combination is
/// empty. With equations cited it must be a combination of them — ideal
/// membership — and the multipliers looked for are a rational times a
/// monomial of degree at most one, which is every such step the corpus has.
/// Nothing is searched for past that.
///
/// At most one cited equation is multiplied by a monomial with a letter in
/// it; the others are added, subtracted and scaled by numbers. A step does
/// one thing, and multiplying a second equation by a term is a second thing,
/// a step of its own (`METHODS.md`, "algebra").
///
/// What is returned is the combination itself: the claim is the sum of what
/// each [`Taken`] takes off. A proof of the step is built from it.
pub fn follows(given: &[Poly], claim: &Poly, atoms: &[Rc<str>]) -> Option<Vec<Taken>> {
    if claim.zero() {
        return Some(Vec::new());
    }
    if given.is_empty() {
        return None;
    }
    let mut sorted: Vec<&Rc<str>> = atoms.iter().collect();
    sorted.sort();
    sorted.dedup();
    let mut shapes = vec![one()];
    shapes.extend(sorted.into_iter().map(|a| atom(a)));
    reduces(claim, given, &shapes, 3, None)
}

/// Take one cited equation off the claim, by some allowed multiplier.
///
/// `shapes[0]` is 1, and every other shape is an atom. `multiplied` is the
/// one equation an atom has multiplied so far, which only that equation may
/// be again.
fn reduces(
    claim: &Poly,
    given: &[Poly],
    shapes: &[Poly],
    depth: u32,
    multiplied: Option<usize>,
) -> Option<Vec<Taken>> {
    if claim.zero() {
        return Some(Vec::new());
    }
    if depth == 0 {
        return None;
    }
    for (which, held) in given.iter().enumerate() {
        if held.zero() {
            continue;
        }
        for (k, shape) in shapes.iter().enumerate() {
            let by_atom = k > 0;
            if by_atom && multiplied.is_some_and(|m| m != which) {
                continue;
            }
            let part = held.times(shape);
            let Some(scale) = cancels(claim, &part) else {
                continue;
            };
            let next = if by_atom { Some(which) } else { multiplied };
            let rest = reduces(
                &claim.minus(&part.scaled(&scale)),
                given,
                shapes,
                depth - 1,
                next,
            );
            if let Some(rest) = rest {
                let mut out = vec![Taken {
                    which,
                    shape: shape.clone(),
                    scale,
                }];
                out.extend(rest);
                return Some(out);
            }
        }
    }
    None
}

/// The rational that makes this part cancel the claim's leading term.
///
/// The leading term is the largest monomial the claim has, in the order the
/// keys sort in, so taking it off strictly shrinks what is left.
fn cancels(claim: &Poly, part: &Poly) -> Option<Q> {
    if part.zero() {
        return None;
    }
    let lead = claim.lead()?;
    let theirs = part.terms.get(lead)?;
    if part.lead() != Some(lead) {
        return None;
    }
    Some(&claim.terms[lead] / theirs)
}

// --- closed numeral claims, which `arithmetic` decides ----------------------

/// A number more than this many bits long is not worked out: what a claim
/// like 9^(9^9) costs is time and memory without end, and it is refused
/// before it is computed. The corpus's largest number is 10; ten thousand
/// bits is some three thousand digits.
pub const BITS: u64 = 10_000;

/// What a closed term comes to: its exact value, or why it has none — it
/// divides by zero, it is too large to work out, or it is not rational.
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Exact(Q),
    Unworked(&'static str),
}

/// What a closed claim comes to: whether it holds, or why it could not be
/// worked out.
#[derive(Clone, Debug, PartialEq)]
pub enum Verdict {
    Holds(bool),
    Unworked(&'static str),
}

fn size(value: &Q) -> u64 {
    value.numer().bits().max(value.denom().bits())
}

/// The exact value of a term built from numerals alone.
///
/// Every value is exact from the numeral up and an exponent is whole before
/// it is used. [`Value::Unworked`] where the term has no exact value, and a
/// decline where it is not built from numerals at all.
pub fn closed_value(term: &Term) -> Route<Value> {
    if term.variable().is_some() {
        return Route::no("it holds a letter");
    }
    let label = term.label().unwrap_or("");
    let value = if let (Some(d), true) = (digit_of(label), term.children().is_empty()) {
        return Built(Value::Exact(q(d as i64)));
    } else if label == "cdc" && term.children().len() == 2 {
        let parts: Vec<Route<Value>> =
            term.children().iter().map(closed_value).collect();
        let (a, b) = match stopped(parts) {
            Stop::Go(mut values) => {
                let b = values.pop().unwrap();
                (values.pop().unwrap(), b)
            }
            Stop::At(r) => return r,
        };
        a * q(10) + b
    } else if label == NEG && term.children().len() == 1 {
        match closed_value(&term.children()[0]) {
            Built(Value::Exact(v)) => -v,
            other => return other,
        }
    } else if label == "co" && term.children().len() == 3 {
        let how = term.children()[2].label().unwrap_or("");
        let parts: Vec<Route<Value>> =
            term.children()[..2].iter().map(closed_value).collect();
        let (left, right) = match stopped(parts) {
            Stop::Go(mut values) => {
                let b = values.pop().unwrap();
                (values.pop().unwrap(), b)
            }
            Stop::At(r) => return r,
        };
        match how {
            ADD => left + right,
            SUB => left - right,
            MUL => left * right,
            DIV => {
                if right.is_zero() {
                    return Built(Value::Unworked("divides by zero"));
                }
                left / right
            }
            EXP => {
                if !right.is_integer() {
                    return Built(Value::Unworked(
                        "is not a rational number: its exponent is not whole",
                    ));
                }
                let power = right.to_integer();
                if left.is_zero() && power.is_negative() {
                    return Built(Value::Unworked("divides by zero"));
                }
                let bits = size(&left);
                let magnitude = power.magnitude().to_u64().unwrap_or(u64::MAX);
                if bits.saturating_mul(magnitude) > BITS {
                    return Built(Value::Unworked("is too large to work out"));
                }
                let raised = num_traits::pow(left.clone(), magnitude as usize);
                if power.is_negative() {
                    raised.recip()
                } else {
                    raised
                }
            }
            _ => return Route::no("not an operation arithmetic reads"),
        }
    } else {
        return Route::no("not built from numerals");
    };
    if size(&value) > BITS {
        return Built(Value::Unworked("is too large to work out"));
    }
    Built(Value::Exact(value))
}

enum Stop {
    Go(Vec<Q>),
    At(Route<Value>),
}

/// The values, or the first part that is not one: a decline before an
/// unworked value.
fn stopped(parts: Vec<Route<Value>>) -> Stop {
    if let Some(d) = parts.iter().find(|p| p.is_declined()) {
        return Stop::At(d.clone());
    }
    if let Some(u) = parts
        .iter()
        .find(|p| matches!(p, Built(Value::Unworked(_))))
    {
        return Stop::At(u.clone());
    }
    Stop::Go(
        parts
            .into_iter()
            .map(|p| match p {
                Built(Value::Exact(v)) => v,
                _ => unreachable!("every part is a value"),
            })
            .collect(),
    )
}

/// The number systems a closed number is tested for membership of, by
/// `METHODS.md`'s tests on its value.
fn system_test(system: &str) -> Option<fn(&Q) -> bool> {
    Some(match system {
        "cn" => |v: &Q| v.is_integer() && v.is_positive(),
        "cn0" => |v: &Q| v.is_integer() && !v.is_negative(),
        "cz" => |v: &Q| v.is_integer(),
        "cq" | "cr" | "cc" => |_: &Q| true,
        _ => return None,
    })
}

/// Whether a relation between closed numeral terms holds.
///
/// `METHODS.md`'s procedure for `arithmetic`: evaluate each side to a
/// rational and decide the relation, or for a membership test the value.
/// `=`, `≠`, `<` and `≤` — a reader's `>` and `≥` arrive as these with the
/// sides turned — denials of any of them, and membership of ℕ, ℕ₀, ℤ, ℚ, ℝ
/// and ℂ. A decline where the claim is none of these or holds a letter.
pub fn decide_closed(claim: &Term) -> Route<Verdict> {
    let negated = claim.label() == Some("wn") && claim.children().len() == 1;
    let claim = if negated { &claim.children()[0] } else { claim };
    let kids = claim.children();
    enum Test {
        Two(fn(&Q, &Q) -> bool),
        One(fn(&Q) -> bool),
    }
    let (sides, test): (&[Term], Test) = match claim.label() {
        Some("wceq") if kids.len() == 2 => (kids, Test::Two(|a, b| a == b)),
        Some("wne") if kids.len() == 2 => (kids, Test::Two(|a, b| a != b)),
        Some("wbr") if kids.len() == 3 && kids[2].label() == Some("clt") => {
            (&kids[..2], Test::Two(|a, b| a < b))
        }
        Some("wbr") if kids.len() == 3 && kids[2].label() == Some("cle") => {
            (&kids[..2], Test::Two(|a, b| a <= b))
        }
        Some("wcel")
            if kids.len() == 2
                && kids[1].children().is_empty()
                && kids[1].label().and_then(system_test).is_some() =>
        {
            (
                &kids[..1],
                Test::One(system_test(kids[1].label().unwrap()).unwrap()),
            )
        }
        _ => return Route::no("not a relation arithmetic decides"),
    };
    let values = match stopped(sides.iter().map(closed_value).collect()) {
        Stop::Go(values) => values,
        Stop::At(Declined(d)) => return Declined(d),
        Stop::At(Built(Value::Unworked(why))) => return Built(Verdict::Unworked(why)),
        Stop::At(Built(Value::Exact(_))) => unreachable!("a stop is never a value"),
    };
    let holds = match test {
        Test::Two(f) => f(&values[0], &values[1]),
        Test::One(f) => f(&values[0]),
    };
    Built(Verdict::Holds(holds != negated))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn m(atoms: &[(&str, u32)]) -> Monomial {
        atoms.iter().map(|(a, p)| (Rc::from(*a), *p)).collect()
    }

    #[test]
    fn a_square_expands_and_writes_down_in_degree() {
        let k = atom("vk");
        let two_k_plus_one = k.scaled(&q(2)).plus(&one());
        let square = two_k_plus_one.power(2);
        assert_eq!(square.terms[&m(&[("vk", 2)])], q(4));
        assert_eq!(square.terms[&m(&[("vk", 1)])], q(4));
        assert_eq!(square.terms[&m(&[])], q(1));
        assert_eq!(
            spell(&square).unwrap(),
            "c4 vk c2 cexp co cmul co c4 vk c1 cexp co cmul co caddc co \
             c1 c1 cmul co caddc co"
        );
    }

    #[test]
    fn a_claim_that_vanishes_follows_from_nothing() {
        let x = atom("vx");
        assert_eq!(follows(&[], &x.minus(&x), &[]).unwrap().len(), 0);
        assert!(follows(&[], &x, &[]).is_none());
    }

    #[test]
    fn a_multiple_of_a_cited_equation_follows_from_it() {
        let x = atom("vx");
        let y = atom("vy");
        let given = x.minus(&y);
        let claim = given.scaled(&q(3));
        let taken = follows(&[given], &claim, &[]).unwrap();
        assert_eq!(taken.len(), 1);
        assert_eq!(taken[0].scale, q(3));
    }

    /// The atoms of the two tests below, and the two equations they cite:
    /// a = b and c = d.
    fn two_equations() -> (Vec<Poly>, [Poly; 6], Vec<Rc<str>>) {
        let names = ["va", "vb", "vc", "vd", "vx", "vy"];
        let [a, b, c, d, x, y] = names.map(atom);
        let given = vec![a.minus(&b), c.minus(&d)];
        let atoms = names.iter().map(|n| Rc::from(*n)).collect();
        (given, [a, b, c, d, x, y], atoms)
    }

    #[test]
    fn two_equations_each_multiplied_by_a_term_are_two_steps() {
        // x·(a − b) + y·(c − d): a combination of the two, and one that
        // multiplies both by a term, which `algebra` does not do in one step.
        let (given, [a, b, c, d, x, y], atoms) = two_equations();
        let claim = a.minus(&b).times(&x).plus(&c.minus(&d).times(&y));
        assert!(follows(&given, &claim, &atoms).is_none());
    }

    #[test]
    fn one_equation_multiplied_and_another_added_is_one_step() {
        // x·(a − b) + (c − d): one equation multiplied, the other added.
        let (given, [a, b, c, d, x, _], atoms) = two_equations();
        let claim = a.minus(&b).times(&x).plus(&c.minus(&d));
        assert!(follows(&given, &claim, &atoms).is_some());
    }
}
