//! Metamath proofs of ring identities over ℂ.
//!
//! [`super::field`] decides whether an `algebra` step holds; this builds the
//! proof of one that does. The two are separate because deciding needs no
//! kernel and emitting is most of the work.
//!
//! A step claims `L = R` where both sides are the same polynomial. The proof
//! is that each side equals one canonical term — `field::spell` of that
//! polynomial — so what is needed is a procedure taking a term to its
//! canonical form and saying why. That is done by recursion on the term
//! rather than by searching for a chain of rewrites: at `a + b` both sides
//! are already canonical, and what remains is to add two canonical forms,
//! which is a merge.
//!
//! Every step carries its membership alongside its equality. A ring lemma
//! wants its arguments in ℂ, and a canonical form's membership is built as the
//! form is built rather than asked for again at each use: `m ∈ ℂ` is proved
//! once, and everything above it follows by `mulcld`, `addcld` and `expcld`.
//!
//! The elaborator drives this; nothing here reads the database or the corpus.
//! What it cannot do for itself — say that an atom is a complex number, or
//! that a term is not zero — it asks of an [`Oracle`].

use indexmap::IndexMap;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

use super::field::{
    self, numeral as n, order, q, spell_coefficient, spell_monomial, Monomial, Op, Q,
};
use super::numerals;
use crate::mm::kernel::{term_of, FloatLabels, Term};
use crate::mm::spell::{Builder, Proof};
use crate::mm::Rpn;
use crate::outcome::{Built, Checked, Decline, Declined, Route};
use crate::{binds, t, take};

mod products;
mod quotients;
mod runs;

const ADD: &str = "caddc";
const MUL: &str = "cmul";
const EXP: &str = "cexp";
const DIV: &str = "cdiv";
const SUB: &str = "cmin";

/// A canonical form: its terms, each a monomial and a coefficient, in the
/// order the form writes them.
pub type Run = Vec<(Monomial, Q)>;

/// A term's canonical form as a quotient.
pub struct Quotiented {
    /// The numerator.
    pub over: Run,
    /// The denominator, or None where the term divides nothing.
    pub under: Option<Run>,
    /// ( under -> term = over / under ), or `= over` where it divides
    /// nothing.
    pub proof: Proof,
}

/// What the emitter asks of the elaborator driving it.
pub trait Oracle {
    /// The builder every step is assembled on.
    fn b(&self) -> &Builder;
    /// ( under -> said e. CC ), for a term the recursion bottoms out at.
    fn atom(&mut self, said: &Rpn) -> Checked<Proof>;
    /// ( under -> said =/= 0 ), asked only of an emitter given a way to;
    /// `named` is the term as the page wrote it, which a message names.
    fn apart(&mut self, said: &Rpn, named: &Rpn) -> Checked<Proof>;
    /// ( under -> said =/= 0 ) as the checker recorded the reason's
    /// divisors not zero (`Elaborator::reason_apart`); a decline where the
    /// record does not say so.
    fn nonzero(&mut self, said: &Rpn) -> Checked<Route<Proof>>;
    /// A finite sum written out as linear, as `field::linear_sum` reads it,
    /// and ( under -> said = that ); declined where sums are atoms.
    fn linear_sum(&mut self, said: &Rpn) -> Checked<Route<(Term, Proof)>> {
        let _ = said;
        Ok(Route::no("a sum is one atom here"))
    }
    /// A term as the page would write it, for a message to name.
    fn shown(&self, said: &Rpn) -> String {
        said.to_string()
    }
}

/// A decline naming a term, which a message writes in the page's notation
/// (`Elaborator::say`).
fn named_decline<T>(shape: &'static str, term: &Rpn) -> Route<T> {
    Route::Declined(Decline::shaped(shape, vec![term.to_string()]))
}

/// `( left what right )`, which reverse Polish writes the other way.
fn op(left: &Rpn, right: &Rpn, what: &str) -> Rpn {
    t!(left, right, what, "co")
}

/// A left-associated run, which is the shape every canonical form has.
fn join(terms: &[Rpn], what: &str) -> Rpn {
    let mut out = terms[0].clone();
    for one in &terms[1..] {
        out = op(&out, one, what);
    }
    out
}

/// Two fractions multiplied, ( over / under ) x. ( below / beneath ), each
/// part in canonical form.
#[derive(Clone)]
struct Fractions {
    over: Run,
    under: Run,
    below: Run,
    beneath: Run,
}

impl Fractions {
    fn spelt(&self) -> Rpn {
        op(
            &op(
                &Emitter::spell_run(&self.over),
                &Emitter::spell_run(&self.under),
                DIV,
            ),
            &op(
                &Emitter::spell_run(&self.below),
                &Emitter::spell_run(&self.beneath),
                DIV,
            ),
            MUL,
        )
    }
}

/// The greatest whole number dividing every coefficient of a run, where
/// every one is whole and one is not zero.
fn content(run: &Run) -> Option<BigInt> {
    let mut g = BigInt::zero();
    for (_, w) in run {
        if !w.is_integer() {
            return None;
        }
        g = g.gcd(&w.to_integer());
    }
    (!g.is_zero()).then_some(g)
}

/// A run that is one whole number alone, its size.
fn constant(run: &Run) -> Option<BigInt> {
    match run.as_slice() {
        [(m, w)] if m.is_empty() && w.is_integer() => Some(w.to_integer().abs()),
        _ => None,
    }
}

/// A run with every coefficient divided by g.
fn divided(run: &Run, g: &BigInt) -> Run {
    let by = Q::from_integer(g.clone());
    run.iter().map(|(m, w)| (m.clone(), w / &by)).collect()
}

/// A whole coefficient's value, of any size.
fn whole(weight: &Q) -> BigInt {
    weight.to_integer()
}

/// A whole number's magnitude as set.mm spells it.
fn spelt(value: &BigInt) -> Rpn {
    numerals::spell(value.magnitude().clone())
}

fn big(value: i64) -> BigInt {
    BigInt::from(value)
}

fn coeff(weight: &Q) -> Rpn {
    spell_coefficient(weight).unwrap_or_default()
}

/// What an emitter has built and remembers, because it will be asked for it
/// again: these build from their arguments and from `under`, which does not
/// change while one emitter is alive.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Made {
    Number(BigInt),
    Index(i64),
    Coefficient(Q),
    MonomialCc(Monomial),
    TermCc(Monomial, Q),
    FactorCc(Rpn, u32),
}

/// Proofs over one scope.
///
/// `under` is the antecedent every statement carries, in reverse Polish.
/// Everything here is built by applying a label to what it is applied to,
/// and nothing is parsed.
pub struct Emitter {
    pub under: Rpn,
    /// Whether the oracle can say a term is not zero, by search.
    apart: bool,
    /// Whether the oracle can say what the page wrote a term is not.
    written: bool,
    held: IndexMap<Rpn, Proof>,
    made: IndexMap<Made, Proof>,
    nonzero: IndexMap<Rpn, Proof>,
    /// Each denominator made from a divisor the page wrote, by its
    /// canonical form, and the divisor as written: what a message names
    /// where nothing says it is not zero.
    divisors: IndexMap<Rpn, Rpn>,
}

/// A rational as Python writes a `Fraction`: `3`, or `-1/2`.
pub fn show(value: &Q) -> String {
    if value.is_integer() {
        value.to_integer().to_string()
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

/// Whether a division appears in this term outside its atoms.
///
/// Only the arithmetic the normaliser reads is looked through. A sum whose
/// summand divides, Σ(k = 1 to n) 1/T(k), is an atom, and what is inside it
/// is not a denominator of the term it stands in.
pub fn divides(term: &Term) -> bool {
    if term.variable().is_some() {
        return false;
    }
    if term.label() == Some("cneg") {
        return term.children().iter().any(divides);
    }
    match Op::applied(term) {
        Some(Op::Div) => true,
        // A power to anything but a whole numeral is an atom, whatever its
        // base divides by (`field::Power::Atom`): (b/5)^b is not taken apart.
        Some(Op::Exp) => {
            numerals::value(&term.children()[1]).is_some()
                && divides(&term.children()[0])
        }
        Some(_) => term.children()[..2].iter().any(divides),
        None => false,
    }
}

/// One factor of a monomial, always `( x ^ k )`.
fn spell_factor(factor: &(Rpn, u32)) -> Rpn {
    op(&factor.0, &n(factor.1), EXP)
}
