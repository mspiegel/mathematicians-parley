//! The calculators: `algebra`, `inequalities` and `arithmetic`.
//!
//! This is the fifth of the elaborator's six parts (`ELABORATION.md`, "How
//! the elaborator is built"). Given a claim and the lines a step cites, each
//! method decides whether the claim follows and produces its proof;
//! `METHODS.md` specifies each. The deciding is done by `field` (identities
//! of the field), `linear` (linear facts over an ordered field) and `normal`
//! (driving two terms to one canonical form, and the proof that it did).
//! What is here is how their answers become proof steps under the step's
//! scope.
//!
//! What a method decides but cannot write is a defect at its line: nothing is
//! taken as stated in its place.

use std::cell::{OnceCell, RefCell};
use std::collections::BTreeSet;

use indexmap::IndexMap;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::elaborate::Sides;
use super::field::{self, numeral as n, q, Poly, Value, Verdict, DIV, Q, SUB};
use super::linear::{self, Certificate, How};
use super::normal::{Emitter, Oracle, Quotiented, Run};
use super::state::{Elaborator, ProvedClaim, Vars};
use super::{numerals, Facts, Line, Lines};
use crate::corpus::proof::{rows, RowReason};
use crate::corpus::{Item, Method, RecordKind, Step};
use crate::formula::symbol::Symbol;
pub use crate::methods::algebra::rescales;
use crate::methods::algebra::{
    claim_says, combination, denominators, readings, Factor,
};
use crate::methods::pairs::{self, Coordinate, PairRelation};
use crate::mm::kernel::Term;
use crate::mm::spell::{Builder, Proof};
use crate::mm::Rpn;
use crate::outcome::{Built, Checked, Declined, Problem, Route};
use crate::rules::{self, lookup};
use crate::{binds, pf, t, take};

mod algebra;
mod bounds;
mod ordering;
mod polynomials;
mod rows;
mod sums;
mod values;

/// What an emitter asks of the elaborator: the scope, the facts a
/// membership is answered from, whether it may search for a term not being
/// zero, and what the page says of that.
pub struct Spec {
    pub scope: Rpn,
    pub facts: Facts,
    pub apart: bool,
    pub written: Option<Facts>,
    /// Each atom's membership of ℂ, once proved. The scope and the facts do
    /// not change for as long as the spec lives, so an atom asked again is
    /// the same question: four asks in five during a comparison of two
    /// polynomials were one already answered.
    pub atoms: RefCell<IndexMap<Rpn, Proof>>,
    /// What each of `facts` also says (`implied`), in their order, worked
    /// out the first time a denominator asks: every denominator asked it of
    /// every fact again.
    pub implied: Implied,
}

/// What each fact a membership is answered from also says
/// (`Elaborator::implied`).
#[derive(Default)]
pub struct Implied {
    facts: OnceCell<Vec<Facts>>,
}

/// An emitter and what it asks, which live as long as one calculation.
pub struct Work {
    pub e: Emitter,
    pub spec: Spec,
}

impl Work {
    pub fn new(spec: Spec) -> Work {
        Work {
            e: Emitter::new(&spec.scope, spec.apart, spec.written.is_some()),
            spec,
        }
    }

    /// An emitter asking only for the membership of what it bottoms out at.
    pub fn plain(scope: &Rpn, facts: &Facts) -> Work {
        Work::new(Spec {
            scope: scope.clone(),
            facts: facts.clone(),
            apart: false,
            written: None,
            atoms: RefCell::default(),
            implied: Implied::default(),
        })
    }
}

/// The elaborator answering an emitter, for as long as one call.
pub struct Ask<'e, 'a> {
    el: &'e mut Elaborator<'a>,
    spec: &'e Spec,
}

impl Ask<'_, '_> {
    /// ( under -> said e. CC ), proved.
    fn atom_proved(&mut self, said: &Rpn) -> Checked<Proof> {
        // A sum a linear reading wrote is a number because its terms are,
        // as `membership` builds any sum (`summed`).
        let key = (self.spec.scope.clone(), said.clone());
        if let Some(p) = self.el.sums_in_cc.get(&key) {
            return Ok(p.clone());
        }
        // Any other atom, a sum included, is a number by what the step's own
        // lines say before it is built from its parts: a sum whose terms are
        // a defined function's values is real by the line the step cites,
        // and building it from the function's type would rest on a line the
        // step does not name.
        self.el
            .membership(said, "cc", &self.spec.scope, &self.spec.facts)
    }
}

/// What each of `facts` also says, from `kept` where it was worked out
/// already for this spec, and worked out and kept there where not.
fn take_implied<'k>(
    kept: &'k OnceCell<Vec<Facts>>,
    el: &mut Elaborator,
    scope: &Rpn,
    facts: &Facts,
) -> Checked<&'k [Facts]> {
    if let Some(each) = kept.get() {
        return Ok(each);
    }
    let mut each = Vec::new();
    for (fact, proof) in facts.entries() {
        each.push(el.implied(&fact, &proof, scope, facts)?);
    }
    Ok(kept.get_or_init(|| each))
}

impl Oracle for Ask<'_, '_> {
    fn b(&self) -> &Builder {
        &self.el.b
    }

    fn atom(&mut self, said: &Rpn) -> Checked<Proof> {
        if let Some(p) = self.spec.atoms.borrow().get(said) {
            return Ok(p.clone());
        }
        let p = self.atom_proved(said)?;
        self.spec.atoms.borrow_mut().insert(said.clone(), p.clone());
        Ok(p)
    }

    fn apart(&mut self, said: &Rpn, named: &Rpn) -> Checked<Proof> {
        let (scope, facts) = (&self.spec.scope, &self.spec.facts);
        let implied = &self.spec.implied.facts;
        let written = self.spec.written.as_ref();
        self.el
            .not_zero_named(scope, facts, implied, written, said, named)
    }

    fn nonzero(&mut self, said: &Rpn) -> Checked<Route<Proof>> {
        let spec = self.spec;
        self.el.reason_apart(
            said,
            &spec.scope,
            &spec.facts,
            &spec.implied.facts,
            spec.written.as_ref(),
        )
    }

    fn linear_sum(&mut self, said: &Rpn) -> Checked<Route<(Term, Proof)>> {
        let Some(letter) = self.el.sum_letter.clone() else {
            return Ok(Route::no("a sum is one atom outside `algebra`"));
        };
        let (scope, facts) = (self.spec.scope.clone(), self.spec.facts.clone());
        self.el.linear_sum(said, &letter, &scope, &facts)
    }

    fn shown(&self, said: &Rpn) -> String {
        self.el.render(said)
    }
}

/// Whether an equation of closed terms holds, as `arithmetic` works it
/// out; None where it does not work it out.
fn closed_equal(equation: &Term) -> Option<bool> {
    match field::decide_closed(equation) {
        Built(Verdict::Holds(holds)) => Some(holds),
        _ => None,
    }
}

/// Whether `claim` is the word `word` is the kernel form of: the same tree,
/// where each letter of the word's record, read as a set variable's class,
/// stands for any term.
fn fits_word(word: &Term, claim: &Term) -> bool {
    if word.variable().is_some() || word.label() == Some("cv") {
        return true;
    }
    claim.variable().is_none()
        && word.label() == claim.label()
        && word.children().len() == claim.children().len()
        && word
            .children()
            .iter()
            .zip(claim.children())
            .all(|(w, c)| fits_word(w, c))
}

/// The two sides of a claim and which relation stands between them: `=`,
/// `<` or `<=`.
pub fn order_sides(goal: &Term) -> Option<(Term, Term, &'static str)> {
    if goal.variable().is_some() {
        return None;
    }
    let kids = goal.children();
    if goal.label() == Some("wceq") && kids.len() == 2 {
        return Some((kids[0].clone(), kids[1].clone(), "="));
    }
    if goal.label() != Some("wbr") || kids.len() != 3 {
        return None;
    }
    let how = match kids[2].label() {
        Some("clt") => "<",
        Some("cle") => "<=",
        _ => return None,
    };
    Some((kids[0].clone(), kids[1].clone(), how))
}

/// How many times the claim the cited equation is, if a whole number of 2
/// or more: both are the polynomial that must vanish, so one being a
/// multiple of the other is the two saying the same thing at different
/// scales.
pub fn whole_multiple(cited: Option<&Poly>, claim: Option<&Poly>) -> Option<i64> {
    let (cited, claim) = (cited?, claim?);
    let lead = claim.lead()?;
    let theirs = cited.terms.get(lead)?;
    let times = theirs / &claim.terms[lead];
    if !times.is_integer() {
        return None;
    }
    let whole = times.to_integer().to_i64()?;
    if whole < 2 {
        return None;
    }
    if *cited != claim.scaled(&times) {
        return None;
    }
    Some(whole)
}

/// The term a combination multiplies one cited equation by, or None where a
/// coefficient is not whole: a multiplier is written the short way, `-u q`
/// rather than the canonical `( -u 1 x. ( q ^ 1 ) )`, its terms in the
/// order a polynomial is written and each after the first added or taken
/// away.
pub fn multiplier(times: &Poly) -> Option<Rpn> {
    let mut terms: Vec<(&field::Monomial, &Q)> = times.terms.iter().collect();
    terms.sort_by_key(|(m, _)| field::order(m));
    let mut out: Option<Rpn> = None;
    for (monomial, weight) in terms {
        let size = weight.abs();
        let factors: Vec<Rpn> = monomial
            .iter()
            .map(|(atom, power)| match power {
                1 => atom.clone(),
                _ => t!(atom, field::numeral(*power), "cexp", "co"),
            })
            .collect();
        let product = factors
            .into_iter()
            .reduce(|acc, factor| t!(acc, factor, "cmul", "co"));
        // The first term carries its own sign, and each after it its size,
        // added or taken away.
        let first = out.is_none();
        let shown = if first { weight.clone() } else { size };
        let term = match product {
            None => field::spell_coefficient(&shown)?,
            Some(product) if shown.is_one() => product,
            Some(product) if shown == q(-1) => t!(product, "cneg"),
            Some(product) => {
                t!(field::spell_coefficient(&shown)?, product, "cmul", "co")
            }
        };
        out = Some(match out {
            None => term,
            Some(sum) if weight.is_negative() => t!(sum, term, "cmin", "co"),
            Some(sum) => t!(sum, term, "caddc", "co"),
        });
    }
    out
}

/// Whether a term raises something to an exponent whose value is below 0,
/// which the normaliser holds as an atom.
pub(super) fn negative_power(term: &Term) -> bool {
    if term.variable().is_some() {
        return false;
    }
    let kids = term.children();
    let here = term.label() == Some("co")
        && kids.len() == 3
        && kids[2].label() == Some(field::EXP)
        && matches!(
            field::closed_value(&kids[1]),
            Built(Value::Exact(v)) if v.is_negative()
        );
    here || kids.iter().any(negative_power)
}

/// What an inequalities step with rows is proved from (`algebra_rows`): the
/// lines it cites with each algebra row's side equations, and the table
/// holding them.
struct RowsRewritten {
    refs: Vec<String>,
    lines: Lines,
}

/// A divisor −(c/e) of an algebra claim, and its parts, as set.mm writes
/// them (`negated_top_apart`).
struct NegatedQuotient {
    /// −(c/e).
    divisor: Rpn,
    /// c/e.
    quotient: Rpn,
    /// c.
    top: Rpn,
    /// e.
    below: Rpn,
}

/// An order of two terms, ( scope -> a R b ), with each side in ℝ, as the
/// laws that turn an order round ask (`denied`).
pub(super) struct Ordered {
    pub(super) proof: Proof,
    /// ( scope -> a e. RR )
    pub(super) left_real: Proof,
    /// ( scope -> b e. RR )
    pub(super) right_real: Proof,
}

/// A claim of closed terms and the same claim of their values, with
/// ( scope -> ( said <-> valued ) ), which a proof of the second carries
/// back to the first (`carried_back`).
pub(super) struct Revalued {
    pub(super) said: Rpn,
    pub(super) valued: Rpn,
    pub(super) iff: Proof,
}

/// A term shown to be 0 (`multiple_vanishing`, `vanishing_sum`).
#[derive(Clone)]
pub(super) struct Vanishing {
    pub(super) term: Rpn,
    /// ( scope -> term = 0 ).
    pub(super) proof: Proof,
}

/// One fact a combination uses, and its weight.
struct Part {
    /// The line the fact is cited from.
    cited: String,
    /// The fact as that line says it.
    said: Term,
    times: Q,
}

/// A step's claim, facts and cited lines with defined names written out, as
/// `inequalities` reads them.
struct WrittenOut {
    term: Rpn,
    facts: Facts,
    lines: Lines,
}

/// What a sum read as linear is shown at a member, each under the member's
/// scope.
struct AtMember {
    /// The summand is the parts added.
    pointwise: Proof,
    /// Each run of the first parts added is a number, the first part alone
    /// first.
    runs: Vec<Proof>,
    /// Each part is a number.
    terms: Vec<Proof>,
    /// Each part's factor holding the letter is a number.
    bounds: Vec<Proof>,
}

/// A term against zero, as `inequalities` combines the facts it is given.
#[derive(Clone)]
struct Against {
    term: Rpn,
    /// Whether the term is strictly below zero, or at most zero.
    strict: bool,
    /// ( scope -> term < 0 ), or `<_` where not strict.
    below: Proof,
    /// ( scope -> term e. RR ).
    real: Proof,
}
