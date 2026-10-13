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
pub const MOD: &str = "cmo";
pub const NEG: &str = "cneg";

/// What a power may cost to multiply out. The proof raises a power one step
/// of the exponent at a time, and each step puts the terms it makes in
/// order one by one, every move rewriting the polynomial so far: a step
/// whose result has T terms, from a base of b, costs T³·b, and no step less
/// than [`STEP`]. Measured, a million of these is 3 to 5 GB of memory, and
/// this is what keeps a power under the build's 2 GB: (x + y)^24 costs some
/// 210 000 and (x + y + z)^7 some 250 000, (x + y)^30 some 490 000 and
/// (x + y + z)^8 some 520 000, and x^27 a few hundred. A power past it is
/// refused rather than worked.
pub const WORK: usize = 300_000;

/// The least a step of a power costs: each restates the power, however few
/// its terms, and x^3000 takes 0.3 GB.
pub const STEP: usize = 50;

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
    let whole = weight.to_integer();
    let said = super::numerals::spell(whole.magnitude().clone());
    Some(if whole.is_negative() {
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

/// What the exponent rule makes of a power.
pub enum Power {
    /// A whole exponent, nought or more: the power multiplied out.
    Expanded { by: u32, raised: Quotient },
    /// Any other exponent: the whole power is an atom.
    Atom,
    /// A whole exponent whose power costs more than [`WORK`] to multiply
    /// out, which `algebra` refuses.
    Past,
}

/// `base ^ exponent` under the exponent rule. The numerator and the
/// denominator are raised each, and what both cost is counted together.
pub fn power_of(base: &Term, exponent: &Term, labels: &FloatLabels) -> Power {
    let Some(by) = whole_number(exponent).filter(|by| *by >= 0) else {
        return Power::Atom;
    };
    let Some(by) = u32::try_from(by)
        .ok()
        .filter(|by| (*by as usize).saturating_mul(STEP) <= WORK + STEP)
    else {
        return Power::Past;
    };
    let base = read(base, labels);
    let mut left = WORK;
    let Built(over) = raised(&base.over, by, &mut left) else {
        return Power::Past;
    };
    let under = if base.under == one() {
        one()
    } else {
        match raised(&base.under, by, &mut left) {
            Built(under) => under,
            Declined(_) => return Power::Past,
        }
    };
    Power::Expanded {
        by,
        raised: Quotient { over, under },
    }
}

/// `base ^ by` multiplied out as the proof multiplies it, by the base once
/// for each step past the first, each step costing what [`WORK`] says; or a
/// decline where that is more than `left`, which is what is left of it
/// after.
fn raised(base: &Poly, by: u32, left: &mut usize) -> Route<Poly> {
    if by == 0 {
        return Built(one());
    }
    let mut out = base.clone();
    for _ in 1..by {
        // Multiplying is a product for each pair of terms, which a step
        // whose terms cancel may cost more than its result says.
        if out.terms.len().saturating_mul(base.terms.len()) > *left {
            return Route::no("a power past what it may cost");
        }
        out = out.times(base);
        let made = out.terms.len();
        let cost = made
            .saturating_mul(made)
            .saturating_mul(made)
            .saturating_mul(base.terms.len())
            .max(STEP);
        if cost > *left {
            return Route::no("a power past what it may cost");
        }
        *left -= cost;
    }
    Built(out)
}

/// The first power in `term`, innermost first, that the exponent rule
/// multiplies out and that costs more than [`WORK`] to.
pub fn past_expanding(term: &Term, labels: &FloatLabels) -> Option<Term> {
    if term.variable().is_some() {
        return None;
    }
    if let Some(inner) = term
        .children()
        .iter()
        .find_map(|child| past_expanding(child, labels))
    {
        return Some(inner);
    }
    match operation(term, labels) {
        Some((how, base, exponent)) if &*how == EXP => {
            matches!(power_of(base, exponent, labels), Power::Past)
                .then(|| term.clone())
        }
        _ => None,
    }
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
                // other leaves the whole power an atom. A power past what
                // may be multiplied out is an atom here too, and `algebra`
                // refuses a step that reads one (`past_expanding`).
                if let Power::Expanded { raised, .. } = power_of(left, right, labels) {
                    return raised;
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

/// One cited equation a claim is made of, and what it is multiplied by:
/// `scale` times `shape`, the first term of `shape` as it is written having
/// a coefficient of 1, so that a multiplier of −q is −1 times q.
#[derive(Clone, Debug)]
pub struct Taken {
    pub which: usize,
    pub shape: Poly,
    pub scale: Q,
}

impl Taken {
    /// The multiplier whole: `scale` times `shape`.
    pub fn multiplier(&self) -> Poly {
        self.shape.scaled(&self.scale)
    }
}

/// How the claim is a combination of the given equations, or None.
///
/// With nothing cited the claim must vanish outright, and the combination is
/// empty. With equations cited the claim must be `Σ pᵢ · gᵢ`, at most one
/// `pᵢ` a polynomial with a letter in it and the others numbers: a step does
/// one thing, and multiplying a second equation by a term is a second thing,
/// a step of its own (`METHODS.md`, "algebra").
///
/// Each equation in turn is the one a term may multiply. Dividing by one
/// polynomial leaves a remainder that is nought exactly for its multiples,
/// and the remainder of a sum is the sum of the remainders. So the numbers
/// the other equations are taken by are what solves the remainders' linear
/// equations, and the multiplier of the one is the quotient of what is left.
///
/// What is returned is the combination itself, each equation at most once
/// and in the order cited: the claim is the sum of each [`Taken`]'s equation
/// times its multiplier. A proof of the step is built from it.
pub fn follows(given: &[Poly], claim: &Poly) -> Option<Vec<Taken>> {
    if claim.zero() {
        return Some(Vec::new());
    }
    let atoms = atoms_of(given.iter().chain(std::iter::once(claim)));
    for (k, held) in given.iter().enumerate() {
        if held.zero() {
            continue;
        }
        let rest: Vec<usize> = (0..given.len())
            .filter(|&j| j != k && !given[j].zero())
            .collect();
        let columns: Vec<Poly> = rest
            .iter()
            .map(|&j| divided(&given[j], held, &atoms).remainder)
            .collect();
        let wanted = divided(claim, held, &atoms).remainder;
        let Some(numbers) = solved(&columns, &wanted) else {
            continue;
        };
        let mut left = claim.clone();
        for (&j, c) in rest.iter().zip(&numbers) {
            left = left.minus(&given[j].scaled(c));
        }
        let Divided {
            quotient,
            remainder,
        } = divided(&left, held, &atoms);
        debug_assert!(remainder.zero(), "the numbers solve the remainders");
        let mut multipliers: Vec<(usize, Poly)> = rest
            .into_iter()
            .zip(numbers)
            .map(|(j, c)| (j, constant(c)))
            .collect();
        multipliers.push((k, quotient));
        multipliers.sort_by_key(|(j, _)| *j);
        return Some(
            multipliers
                .into_iter()
                .filter(|(_, p)| !p.zero())
                .map(|(which, p)| {
                    let first = p.terms.keys().min_by_key(|m| order(m)).cloned();
                    let scale =
                        p.terms[&first.expect("a multiplier not nought")].clone();
                    Taken {
                        which,
                        shape: p.scaled(&(q(1) / &scale)),
                        scale,
                    }
                })
                .collect(),
        );
    }
    None
}

/// `p` divided by `by`, where `by` divides it; None where a remainder is
/// left. `by` is not nought.
pub fn exactly(p: &Poly, by: &Poly) -> Option<Poly> {
    let Divided {
        quotient,
        remainder,
    } = divided(p, by, &atoms_of([p, by]));
    remainder.zero().then_some(quotient)
}

/// Every atom the polynomials hold, once each and sorted.
fn atoms_of<'p>(polys: impl IntoIterator<Item = &'p Poly>) -> Vec<Rc<str>> {
    let mut atoms: Vec<Rc<str>> = polys
        .into_iter()
        .flat_map(|p| p.terms.keys().flatten().map(|(a, _)| a.clone()))
        .collect();
    atoms.sort();
    atoms.dedup();
    atoms
}

/// A polynomial divided by another: `quotient · by + remainder`.
struct Divided {
    quotient: Poly,
    /// No term of it is a multiple of the leading term of what divided.
    remainder: Poly,
}

/// A monomial's place in the order division takes terms in: by degree, then
/// by the power of each atom in turn. Multiplying keeps it, which is what
/// makes a remainder nought exactly for a multiple.
fn rank(monomial: &Monomial, atoms: &[Rc<str>]) -> (u32, Vec<u32>) {
    let power = |atom: &Rc<str>| {
        monomial
            .iter()
            .find(|(a, _)| a == atom)
            .map_or(0, |(_, p)| *p)
    };
    (
        monomial.iter().map(|(_, p)| p).sum(),
        atoms.iter().map(power).collect(),
    )
}

fn leading<'p>(p: &'p Poly, atoms: &[Rc<str>]) -> Option<&'p Monomial> {
    p.terms.keys().max_by_key(|m| rank(m, atoms))
}

/// `over / under`, where `under` divides it.
fn monomial_over(over: &Monomial, under: &Monomial) -> Option<Monomial> {
    let mut out = over.clone();
    for (atom, power) in under {
        let held = out.iter_mut().find(|(a, _)| a == atom)?;
        held.1 = held.1.checked_sub(*power)?;
    }
    out.retain(|(_, p)| *p != 0);
    Some(out)
}

/// `p` divided by `by`, which is not nought, term by leading term.
fn divided(p: &Poly, by: &Poly, atoms: &[Rc<str>]) -> Divided {
    let lead = leading(by, atoms).expect("a divisor not nought").clone();
    let weight = by.terms[&lead].clone();
    let mut left = p.clone();
    let mut quotient = Poly::default();
    let mut remainder = Poly::default();
    while let Some(top) = leading(&left, atoms).cloned() {
        let mut term = IndexMap::new();
        term.insert(top.clone(), left.terms[&top].clone());
        let term = Poly::new(term);
        match monomial_over(&top, &lead) {
            Some(times) => {
                let mut part = IndexMap::new();
                part.insert(times, &term.terms[&top] / &weight);
                let part = Poly::new(part);
                left = left.minus(&part.times(by));
                quotient = quotient.plus(&part);
            }
            None => {
                left = left.minus(&term);
                remainder = remainder.plus(&term);
            }
        }
    }
    Divided {
        quotient,
        remainder,
    }
}

/// Numbers `cⱼ` with `Σ cⱼ · columns[j] = wanted`, monomial by monomial, or
/// None where there are none. Where several do, a number free to be anything
/// is nought.
fn solved(columns: &[Poly], wanted: &Poly) -> Option<Vec<Q>> {
    let every: Vec<&Poly> = columns.iter().chain(std::iter::once(wanted)).collect();
    let mut monomials: Vec<&Monomial> =
        every.iter().flat_map(|p| p.terms.keys()).collect();
    monomials.sort();
    monomials.dedup();
    let width = columns.len();
    let mut rows: Vec<Vec<Q>> = monomials
        .iter()
        .map(|m| {
            every
                .iter()
                .map(|p| p.terms.get(*m).cloned().unwrap_or_else(Q::zero))
                .collect()
        })
        .collect();
    let mut pivots: Vec<usize> = Vec::new();
    for column in 0..width {
        let at = pivots.len();
        let Some(found) = (at..rows.len()).find(|&i| !rows[i][column].is_zero()) else {
            continue;
        };
        rows.swap(at, found);
        let lead = rows[at][column].clone();
        let pivot: Vec<Q> = rows[at].iter().map(|x| x / &lead).collect();
        for row in rows.iter_mut() {
            let factor = row[column].clone();
            if !factor.is_zero() {
                for (x, p) in row.iter_mut().zip(&pivot) {
                    *x -= p * &factor;
                }
            }
        }
        rows[at] = pivot;
        pivots.push(column);
    }
    if rows[pivots.len()..].iter().any(|row| !row[width].is_zero()) {
        return None;
    }
    let mut out = vec![Q::zero(); width];
    for (row, column) in pivots.iter().enumerate() {
        out[*column] = rows[row][width].clone();
    }
    Some(out)
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
            MOD => {
                if !left.is_integer()
                    || left.is_negative()
                    || !right.is_integer()
                    || right < q(1)
                {
                    return Built(Value::Unworked(
                        "is a remainder arithmetic works out only of a whole number, on dividing by one of at least 1",
                    ));
                }
                Q::from_integer(left.to_integer() % right.to_integer())
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
    } else if label == "cprod" && term.children().len() == 3 {
        match range_product(term) {
            Built(Value::Exact(v)) => v,
            other => return other,
        }
    } else {
        return Route::no("not built from numerals");
    };
    if size(&value) > BITS {
        return Built(Value::Unworked("is too large to work out"));
    }
    Built(Value::Exact(value))
}

/// The value of a product over a range of whole numbers from zero up,
/// ∏(k ∈ {a, …, b}) body, each factor its body with k worked as a numeral.
fn range_product(term: &Term) -> Route<Value> {
    let kids = term.children();
    let (range, body) = (&kids[0], &kids[1]);
    let Some(k) = kids[2].variable() else {
        return Route::no("not built from numerals");
    };
    if range.label() != Some("co")
        || range.children().len() != 3
        || range.children()[2].label() != Some("cfz")
    {
        return Route::no("not a product over a range");
    }
    let (Some(from), Some(to)) = (
        super::numerals::value(&range.children()[0]),
        super::numerals::value(&range.children()[1]),
    ) else {
        return Route::no("not a range between numerals");
    };
    // A range of more factors than a value may have bits.
    if to > from && &to - &from > BITS.into() {
        return Built(Value::Unworked("is too large to work out"));
    }
    let mut total = q(1);
    let mut at = from;
    while at <= to {
        match closed_value(&super::numerals::at_number(body, k, &at)) {
            Built(Value::Exact(v)) => total *= v,
            other => return other,
        }
        if size(&total) > BITS {
            return Built(Value::Unworked("is too large to work out"));
        }
        at += 1u32;
    }
    Built(Value::Exact(total))
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

/// The two sides of a divisibility worked out, each an integer and the
/// divisor not 0: what `arithmetic` decides one of (`METHODS.md`,
/// arithmetic). A sign is turned by `negdvdsb` and `dvdsnegb`, so the
/// proof works at the sizes, which `ndvdsi` is stated for.
pub fn integer_division(
    divisor: &Term,
    number: &Term,
) -> Route<Result<(BigInt, BigInt), &'static str>> {
    let mut values = Vec::new();
    for side in [divisor, number] {
        match closed_value(side) {
            Declined(d) => return Declined(d),
            Built(Value::Unworked(why)) => return Built(Err(why)),
            Built(Value::Exact(v)) => values.push(v),
        }
    }
    let (d, n) = (&values[0], &values[1]);
    if !d.is_integer() || !n.is_integer() || d.is_zero() {
        return Built(Err(
            "is a divisibility arithmetic decides only of integers, by a divisor not 0",
        ));
    }
    Built(Ok((d.to_integer(), n.to_integer())))
}

/// Whether a relation between closed numeral terms holds.
///
/// `METHODS.md`'s procedure for `arithmetic`: evaluate each side to a
/// rational and decide the relation, or for a membership test the value.
/// `=`, `≠`, `<` and `≤` — a reader's `>` and `≥` arrive as these with the
/// sides turned — divisibility of integers, which is what "is even" and
/// "is odd" are too, denials of any of them, and membership of ℕ, ℕ₀, ℤ, ℚ,
/// ℝ and ℂ. A decline where the claim is none of these or holds a letter.
pub fn decide_closed(claim: &Term) -> Route<Verdict> {
    let negated = claim.label() == Some("wn") && claim.children().len() == 1;
    let claim = if negated { &claim.children()[0] } else { claim };
    let kids = claim.children();
    if claim.label() == Some("wbr")
        && kids.len() == 3
        && kids[2].label() == Some("cdvds")
    {
        return match integer_division(&kids[0], &kids[1]) {
            Declined(d) => Declined(d),
            Built(Err(why)) => Built(Verdict::Unworked(why)),
            Built(Ok((d, n))) => Built(Verdict::Holds((n % d).is_zero() != negated)),
        };
    }
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
        assert_eq!(follows(&[], &x.minus(&x)).unwrap().len(), 0);
        assert!(follows(&[], &x).is_none());
    }

    #[test]
    fn a_multiple_of_a_cited_equation_follows_from_it() {
        let x = atom("vx");
        let y = atom("vy");
        let given = x.minus(&y);
        let claim = given.scaled(&q(3));
        let taken = follows(&[given], &claim).unwrap();
        assert_eq!(taken.len(), 1);
        assert_eq!(taken[0].scale, q(3));
    }

    /// The atoms of the tests below, and the two equations they cite: a = b
    /// and c = d.
    fn two_equations() -> (Vec<Poly>, [Poly; 6]) {
        let [a, b, c, d, x, y] = ["va", "vb", "vc", "vd", "vx", "vy"].map(atom);
        let given = vec![a.minus(&b), c.minus(&d)];
        (given, [a, b, c, d, x, y])
    }

    #[test]
    fn two_equations_each_multiplied_by_a_term_are_two_steps() {
        // x·(a − b) + y·(c − d): a combination of the two, and one that
        // multiplies both by a term, which `algebra` does not do in one step.
        let (given, [a, b, c, d, x, y]) = two_equations();
        let claim = a.minus(&b).times(&x).plus(&c.minus(&d).times(&y));
        assert!(follows(&given, &claim).is_none());
    }

    #[test]
    fn one_equation_multiplied_and_another_added_is_one_step() {
        // x·(a − b) + (c − d): one equation multiplied, the other added.
        let (given, [a, b, c, d, x, _]) = two_equations();
        let claim = a.minus(&b).times(&x).plus(&c.minus(&d));
        assert!(follows(&given, &claim).is_some());
    }

    #[test]
    fn a_multiplier_of_any_degree_is_found_whole() {
        // (x²·y/5 − 3·x + 2)·(a − b) − 4·(c − d): the multiplier comes back
        // as it was, the first term as written its scale.
        let (given, [a, b, c, d, x, y]) = two_equations();
        let times = x
            .power(2)
            .times(&y)
            .scaled(&(q(1) / q(5)))
            .minus(&x.scaled(&q(3)))
            .plus(&constant(q(2)));
        let claim = a.minus(&b).times(&times).minus(&c.minus(&d).scaled(&q(4)));
        let taken = follows(&given, &claim).unwrap();
        assert_eq!(taken.len(), 2);
        assert_eq!((taken[0].which, taken[1].which), (0, 1));
        assert_eq!(taken[0].multiplier(), times);
        assert_eq!(taken[0].scale, q(1) / q(5));
        assert_eq!(taken[1].multiplier(), constant(q(-4)));
    }

    #[test]
    fn a_claim_one_coefficient_away_does_not_follow() {
        let (given, [a, b, c, d, x, _]) = two_equations();
        let claim = a.minus(&b).times(&x).plus(&c.minus(&d)).plus(&one());
        assert!(follows(&given, &claim).is_none());
    }
}
