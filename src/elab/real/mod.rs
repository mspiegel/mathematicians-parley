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
//! brought to its canon, so that it never expands whole. An order is the
//! difference of its sides above 0 (`real_below`), shown as the decider
//! found its sign: by `arithmetic`, by the ratio of logarithms, or from
//! rational brackets on each root and atom, added part by part
//! (`bracketed_positive`).

use indexmap::IndexMap;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::calculators::{Ordered, Revalued, Vanishing, Work};
use super::field::{self, numeral, Monomial, Poly, Q};
use super::numerals;
use super::provenance::MEMBERSHIP;
use super::state::{fit, names_of, Binding, Elaborator};
use super::Facts;
use crate::binds;
use crate::corpus::Step;
use crate::methods::pairs::{self, Coordinate, PairRelation};
use crate::methods::reals::{self, Atom, Real};
use crate::methods::surds::{self, Surd, Verdict};
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::mm::Rpn;
use crate::outcome::{Built, Checked, Declined, Problem, Route};
use crate::rules;
use crate::{t, take};

mod pieces;
mod positives;
mod proving;

/// The lemmas that read a difference of two points out of a line that says
/// it inside something more (`apart_held`): a betweenness says its
/// three points differ, a side of a line says the line's two points differ
/// and each point on that side is off the line, and a point off a line is
/// neither of its two points.
const APART_LEMMAS: [&str; 10] = [
    "gbetne0",
    "gbetends",
    "gsameoffab",
    "gsameoffp",
    "gsameoffq",
    "goppoffab",
    "goppoffp",
    "goppoffq",
    "goffapart1",
    "goffapart2",
];

/// A term proved equal to the canon of its value: ( scope -> term = canon ).
struct Valued {
    value: Real,
    canon: Rpn,
    proof: Proof,
}

/// Two terms, each proved equal to its canon, and their difference proved
/// equal to the canon of its value: ( scope -> ( a − b ) = canon ).
struct Difference {
    left: Valued,
    right: Valued,
    gap: Valued,
}

/// A term between two closed numeral terms: ( scope -> low < said ) and
/// ( scope -> said < high ).
struct Bounded {
    said: Rpn,
    low: Rpn,
    high: Rpn,
    below: Proof,
    above: Proof,
}

/// A sum of parts of a canon above a closed numeral term: ( scope -> low <
/// said ), or ( scope -> low <_ said ) where it is not `strict`, as a
/// rational part alone is.
struct SumBelow {
    said: Rpn,
    low: Rpn,
    proof: Proof,
    strict: bool,
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

/// A monomial holding a root of a prime to the power 2 or more, which the
/// reduction takes (√p)² = p out of.
struct Reducible {
    monomial: Monomial,
    weight: Q,
    /// √p.
    root: Rpn,
    prime: u64,
}

/// Whether an equation of closed real terms holds, as `real arithmetic`
/// decides it; None where it does not decide it.
fn real_equal(equation: &Term) -> Option<bool> {
    match reals::decide_closed(equation) {
        Built(Verdict::Holds(holds)) => Some(holds),
        _ => None,
    }
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
    gathered(term, &|t| {
        if !surds::is_root(t) {
            return Vec::new();
        }
        match surds::closed_value(t) {
            Built(surds::Value::Exact(v)) => v.primes(),
            _ => Vec::new(),
        }
    })
}

/// What `found` finds at each closed part of a term, in order, each once.
/// A part `found` gives nothing for is still searched within.
fn gathered<T: Ord>(term: &Term, found: &dyn Fn(&Term) -> Vec<T>) -> Vec<T> {
    fn walk<T>(term: &Term, found: &dyn Fn(&Term) -> Vec<T>, out: &mut Vec<T>) {
        if term.variable().is_some() {
            return;
        }
        out.extend(found(term));
        for kid in term.children() {
            walk(kid, found, out);
        }
    }
    let mut out = Vec::new();
    walk(term, found, &mut out);
    out.sort();
    out.dedup();
    out
}

/// √p, as set.mm spells it.
fn root_of_prime(p: u64) -> Rpn {
    t!(numerals::spell(p), "csqrt", "cfv")
}

/// The transitivity lemma taking a < b or a ≤ b, by `first`, and b < c or
/// b ≤ c, by `second`, to a < c or a ≤ c (`rules::ORDER_FOLDING`).
fn transitivity(first: &str, second: &str) -> &'static str {
    rules::order_folding(first, second)
        .expect("every two orders fold")
        .lemma
}

/// p₁·(p₂·…), or None for no primes.
fn product_of_primes(primes: &[u64]) -> Option<Rpn> {
    right_product(primes.iter().map(|p| numerals::spell(*p)).collect())
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
        return field::spell_rational(&rational);
    }
    let common = field::common_denominator(&value.weights());
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
    canon_parts(value)
        .into_iter()
        .map(|part| part.said)
        .reduce(|sum, part| t!(sum, part, "caddc", "co"))
        .unwrap_or_else(|| numeral(0))
}

/// A part of the canon of a value with whole coefficients.
struct CanonPart {
    weight: Q,
    /// Its roots and then its atoms, each with its power
    /// (`reals::part_factors`).
    factors: Vec<(reals::Factor, u32)>,
    /// The part as the canon writes it: the coefficient alone, or times the
    /// product of its factors (`factor_said`), nested from the right.
    said: Rpn,
}

/// The parts of the canon of a value with whole coefficients, in the order
/// the canon adds them: by their atoms, and then by the product under the
/// root.
fn canon_parts(value: &Real) -> Vec<CanonPart> {
    let mut out = Vec::new();
    for (monomial, surd) in &value.parts {
        let mut parts: Vec<(&Vec<u64>, &Q)> = surd.parts.iter().collect();
        // Four primes of up to 40 bits multiply past 128 bits, so the
        // product is taken exactly.
        parts.sort_by_key(|(basis, _)| {
            basis.iter().map(|p| BigUint::from(*p)).product::<BigUint>()
        });
        for (basis, weight) in parts {
            let factors = reals::part_factors(basis, monomial);
            let coefficient = field::spell_rational(weight);
            let said = match right_product(factors.iter().map(factor_said).collect()) {
                None => coefficient,
                Some(rest) => t!(coefficient, rest, "cmul", "co"),
            };
            out.push(CanonPart {
                weight: weight.clone(),
                factors,
                said,
            });
        }
    }
    out
}

/// A factor of a canon's part as the canon writes it: √p, or an atom, to
/// its power where that is not 1.
fn factor_said(&(factor, k): &(reals::Factor, u32)) -> Rpn {
    let base = match factor {
        reals::Factor::Root(p) => root_of_prime(p),
        reals::Factor::Atom(atom) => spelt_atom(atom),
    };
    match k {
        1 => base,
        _ => t!(base, numeral(k), "cexp", "co"),
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
    gathered(term, &|t| {
        if !reals::holds_atom(t) {
            return Vec::new();
        }
        let mut out = match reals::closed_value(t) {
            Built(reals::Value::Exact(v)) => v.atoms(),
            _ => Vec::new(),
        };
        match t.label() {
            Some("cpi") => out.push(Atom::Pi),
            Some("ceu") => out.push(Atom::E),
            _ => {}
        }
        out
    })
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
        let coefficient = field::spell_rational(weight);
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
