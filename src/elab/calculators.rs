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
use super::numerals;
use super::state::{Elaborator, ProvedClaim, Vars};
use super::{Facts, Line, Lines};
use crate::binds;
use crate::corpus::proof::{rows, RowReason};
use crate::corpus::{fmt, Item, Method, RecordKind, Step};
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
use crate::{pf, t, take};

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
    /// What each of `facts` and of `written` also says (`implied`), in their
    /// order, worked out the first time a denominator asks: every
    /// denominator asked it of every fact again.
    pub implied: Implied,
}

/// How far `Elaborator::divisor_apart` looks for a divisor's ≠ 0 past the
/// lines the step may rest on and the divisor's parts.
pub struct Reach<'r> {
    /// The lines the page writes in scope (stage 4).
    pub in_scope: Option<InScope<'r>>,
    /// Whether the search is asked last (stage 5).
    pub search: bool,
}

/// The lines the page writes in scope, as `Reach` reads them: those of
/// them the step may rest on with the lines the step names, and the rest
/// after the divisor's parts, each with what it also says worked out once.
pub struct InScope<'r> {
    pub lines: &'r Facts,
    /// What each of `lines` also says.
    pub implied: &'r OnceCell<Vec<Facts>>,
    /// What each of `lines` the step may rest on also says.
    pub named: &'r OnceCell<Vec<Facts>>,
}

/// What each fact of a table also says (`Elaborator::implied`), by the
/// table: the facts a membership is answered from, and those the page
/// writes.
#[derive(Default)]
pub struct Implied {
    facts: OnceCell<Vec<Facts>>,
    written: OnceCell<Vec<Facts>>,
    named: OnceCell<Vec<Facts>>,
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
        self.el.not_zero_named(scope, facts, implied, said, named)
    }

    fn written(&mut self, said: &Rpn) -> Checked<Option<Proof>> {
        let facts = self.spec.written.clone().unwrap_or_default();
        let implied = &self.spec.implied.written;
        self.el
            .written_nonzero(&self.spec.scope, &facts, implied, said)
    }

    fn named(&mut self, said: &Rpn) -> Checked<Option<Proof>> {
        let facts = self.spec.written.clone().unwrap_or_default();
        let facts = self.el.restable(&facts);
        let implied = &self.spec.implied.named;
        self.el
            .written_nonzero(&self.spec.scope, &facts, implied, said)
    }

    fn positive(&mut self, said: &Rpn) -> Checked<Option<Proof>> {
        let (scope, facts) = (self.spec.scope.clone(), self.spec.facts.clone());
        self.el.positive_divisor(said, &scope, &facts)
    }

    fn nonzero(&mut self, said: &Rpn, search: bool) -> Checked<Route<Proof>> {
        let spec = self.spec;
        let in_scope = spec.written.as_ref().map(|lines| InScope {
            lines,
            implied: &spec.implied.written,
            named: &spec.implied.named,
        });
        let reach = Reach {
            in_scope,
            search: search && spec.apart,
        };
        let implied = &spec.implied.facts;
        self.el
            .divisor_apart(said, &spec.scope, &spec.facts, implied, &reach)
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

impl<'a> Elaborator<'a> {
    fn ask<'s>(&'s mut self, spec: &'s Spec) -> Ask<'s, 'a> {
        Ask { el: self, spec }
    }

    /// Decided by `field`, then proved by `normal`. A step that is not an
    /// identity of the field is refused rather than assumed; what `normal`
    /// does not yet write is taken as stated.
    pub fn algebra(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if let Some(pairs) = pairs::relation(&self.to_term(term)) {
            return self.algebra_pairs(step, &pairs, scope, facts, lines);
        }
        // A defined name is read as what it names, as `inequalities` reads
        // it: the claim and each cited line are taken with their defined
        // names written out, decided so, and the proof is carried back to
        // the claim as the page writes it.
        let out = take!(self.names_written_out(
            Some(step),
            &step.just.refs,
            term,
            scope,
            facts,
            lines
        )?);
        let found =
            self.algebra_written_out(step, &out.term, scope, &out.facts, &out.lines)?;
        if out.term == *term {
            return Ok(found);
        }
        let proof = take!(found);
        let (said, want) = (self.to_term(&out.term), self.to_term(term));
        let Built(back) = self.same(&said, &want, scope, facts, Some(step))? else {
            return Ok(Route::no("the claim written out is not carried back"));
        };
        Ok(Built(
            pf!(self.b; scope, out.term, term, proof, back, "mpbid"),
        ))
    }

    /// Two pairs compared coordinate by coordinate by `algebra`
    /// (`METHODS.md`, Pairs): both coordinates' equations, or the
    /// difference at the first coordinate whose difference rescales one
    /// the step cites (`methods::algebra::apart_at`).
    fn algebra_pairs(
        &mut self,
        step: &Step,
        pairs: &PairRelation,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if !pairs.apart {
            let mut proved = Vec::new();
            for at in Coordinate::BOTH {
                let equation = self.rpn(&pairs.equation(at));
                proved.push(take!(self.algebra(step, &equation, scope, facts, lines)?));
            }
            return Ok(Built(
                self.pairs_equal(pairs, scope, &proved[0], &proved[1]),
            ));
        }
        let cited: Vec<Term> = step
            .just
            .refs
            .iter()
            .filter_map(|r| self.line_written(r, lines).map(|l| self.to_term(&l.claim)))
            .collect();
        let labels = self.b.flabel.clone();
        let Some(at) = crate::methods::algebra::apart_at(pairs, &cited, &labels) else {
            return Ok(Route::no(
                "no coordinate's difference is a disequality the step cites, rescaled",
            ));
        };
        let denial = self.rpn(&pairs.denial(at));
        let apart = take!(self.algebra(step, &denial, scope, facts, lines)?);
        let members = self.number_members(pairs, scope, facts)?;
        Ok(Built(self.pairs_apart(pairs, scope, at, &apart, &members)))
    }

    /// `algebra` over a claim and lines whose defined names are written out.
    fn algebra_written_out(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let mut found = self.prove_field(Some(step), term, scope, facts, lines)?;
        // An equation is one claim either way round, and a route that reaches
        // `b = a` reaches the claim `a = b` turned (`turned_claim`).
        if found.is_declined() {
            if let Some((turned, flip)) = self.turned_claim(term) {
                if let Built(p) =
                    self.prove_field(Some(step), &turned, scope, facts, lines)?
                {
                    let Sides { left, right } = self.equation_sides(&turned);
                    found = Built(pf!(self.b; scope, left, right, p, flip));
                }
            }
        }
        if let Declined(d) = &found {
            // Decided but not written is a gap in the method, and nothing is
            // taken in its place: the build stops here.
            return Err(self.defect(
                step.line,
                format!(
                    "step {} is an identity, and algebra cannot write its proof: {}",
                    fmt(&step.number),
                    self.say(d)
                ),
            ));
        }
        Ok(found)
    }

    /// An `algebra` claim, by whichever of the routes reaches it, in the
    /// order they cost; refused in the words of every route that declined.
    /// Whether a step reads its sums as linear: one of them, in its claim or
    /// a line it cites, is linear in something (`field::says_something_linear`).
    pub fn sums_linear(&self, term: &Rpn, step: Option<&Step>, lines: &Lines) -> bool {
        let labels = self.b.flabel.clone();
        let mut said = vec![self.to_term(term)];
        if let Some(step) = step {
            for r in &step.just.refs {
                if let Some(line) = self.line_written(r, lines) {
                    said.push(self.to_term(&line.claim));
                }
            }
        }
        said.iter()
            .any(|t| field::says_something_linear(t, &labels))
    }

    pub fn prove_field(
        &mut self,
        step: Option<&Step>,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        // Every finite sum the step reads is written over one letter nothing
        // holds, which neither the claim, the scope nor a cited line spells;
        // where the step reads its sums as atoms there is none.
        let linear = self.sums_linear(term, step, lines);
        let letter = if linear {
            let mut seen: Vec<Term> = vec![self.to_term(term), self.to_term(scope)];
            if let Some(step) = step {
                for r in &step.just.refs {
                    if let Some(line) = self.line_written(r, lines) {
                        seen.push(self.to_term(&line.claim));
                    }
                }
            }
            let refs: Vec<&Term> = seen.iter().collect();
            self.unheld(&refs).map(|v| self.rpn(&v).to_string())
        } else {
            None
        };
        let kept = std::mem::replace(&mut self.sum_letter, letter);
        let out = field::reading_sums(linear, || {
            self.field_proved(step, term, scope, facts, lines)
        });
        self.sum_letter = kept;
        out
    }

    fn field_proved(
        &mut self,
        step: Option<&Step>,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let goal = self.to_term(term);
        let apart = goal.variable().is_none()
            && goal.label() == Some("wn")
            && goal.children().len() == 1;
        if !apart
            && (goal.variable().is_some()
                || goal.label() != Some("wceq")
                || goal.children().len() != 2)
        {
            return Ok(Route::no("the claim is not an equation"));
        }
        // A `requires` line is where a step says its denominator is not
        // zero, so what the normalizer is asked is asked of those as well;
        // and what the step cites is laid over the scope's copies, so that
        // a fact one of its lines says is taken from that line.
        let facts = match step {
            Some(step) => {
                let supplied = self.supplied(Some(step), scope, facts)?;
                self.with_cited(Some(step), scope, &supplied, None)?
            }
            None => facts.clone(),
        };
        let mut w = Work::new(Spec {
            scope: scope.clone(),
            facts: facts.clone(),
            apart: true,
            written: Some(facts.clone()),
            atoms: RefCell::default(),
            implied: Implied::default(),
        });
        if apart {
            return self.apart_from_cited(step, &goal, scope, &facts, lines, &mut w);
        }
        let left = self.rpn(&goal.children()[0]);
        let right = self.rpn(&goal.children()[1]);
        // Each route's decline, written out only if every route declines.
        let mut declines = Vec::new();
        let found = self.same_polynomial(&mut w, &left, &right)?;
        match found {
            Built(p) => return Ok(Built(p)),
            Declined(d) => declines.push(d),
        }
        if let Some(step) = step {
            for route in 0..3 {
                let found = match route {
                    0 => self.scaled_from_cited(
                        step, &left, &right, scope, &facts, lines, &mut w,
                    )?,
                    1 => self.crossed_from_cited(
                        step, &left, &right, scope, &facts, lines, &mut w,
                    )?,
                    _ => self.summed_from_cited(
                        step, &left, &right, scope, &facts, lines, &mut w,
                    )?,
                };
                match found {
                    Built(p) => return Ok(Built(p)),
                    Declined(d) => declines.push(d),
                }
            }
        }
        let said: Vec<String> = declines.iter().map(|d| self.say(d)).collect();
        Ok(Route::no(said.join("; ")))
    }

    /// A disequality that is a cited one rescaled: the cited fact becomes a
    /// difference that is not zero, the two differences are shown to be one
    /// polynomial, and the claim's difference is not zero either, the cited
    /// difference multiplied by any rational other than 0 (`METHODS.md`).
    fn apart_from_cited(
        &mut self,
        step: Option<&Step>,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        w: &mut Work,
    ) -> Checked<Route<Proof>> {
        let Some(step) = step else {
            return Ok(Route::no("a disequality needs the step it cites"));
        };
        let labels = self.b.flabel.clone();
        let claim = field::denied(goal, &labels);
        let inner = goal.children()[0].clone();
        let (lhs, rhs) = (
            self.rpn(&inner.children()[0]),
            self.rpn(&inner.children()[1]),
        );
        let whole = t!(lhs, rhs, "cmin", "co");
        for r in &step.just.refs {
            for said in self.line_writes(r, lines) {
                let node = self.to_term(&said);
                let cited = field::denied(&node, &labels);
                let Some(numerators) = rescales(cited.as_ref(), claim.as_ref()) else {
                    continue;
                };
                let pair = node.children()[0].clone();
                let (p, qq) =
                    (self.rpn(&pair.children()[0]), self.rpn(&pair.children()[1]));
                let mut gap = t!(p, qq, "cmin", "co");
                // A disequality is read by its numerator, so the two
                // differences are one a multiple of the other by the scale
                // of their numerators times the ratio of their denominators,
                // where both are numbers: k(k + 1)/2 − 0 is 1/2 of k(k + 1) − 0.
                let below = |t: &Rpn| {
                    field::read(&self.to_term(t), &labels)
                        .under
                        .constant_value()
                };
                let scale = match (below(&gap), below(&whole)) {
                    (Some(theirs), Some(ours)) if !ours.is_zero() => {
                        numerators * theirs / ours
                    }
                    _ => numerators,
                };
                let given = take!(self.cited_fact(r, &node, scope, facts, lines)?);
                let pp = self.membership(&p, "cc", scope, &w.spec.facts)?;
                let pq = self.membership(&qq, "cc", scope, &w.spec.facts)?;
                let turned = self.b.ap(
                    "neqned",
                    &binds! {"ph" => scope, "A" => &p, "B" => &qq},
                    &[&given],
                );
                let mut apart = self.b.ap(
                    "subne0d",
                    &binds! {"ph" => scope, "A" => &p, "B" => &qq},
                    &[&pp, &pq, &turned],
                );
                if scale == q(-1) {
                    let pg = self.membership(&gap, "cc", scope, &w.spec.facts)?;
                    apart = self.b.ap(
                        "negne0d",
                        &binds! {"ph" => scope, "A" => &gap},
                        &[&pg, &apart],
                    );
                    gap = t!(gap, "cneg");
                } else if scale != q(1) {
                    // Any other rational multiple (`METHODS.md`): the scale is
                    // a closed number other than 0, k(k + 1)/2 ≠ 0 from
                    // k(k + 1) ≠ 0 at 1/2.
                    let times = field::spell_rational(&scale);
                    let what = format!(
                        "the scale {} of step {}",
                        self.render(&times),
                        fmt(&step.number)
                    );
                    let apart_from_zero = t!(times, "cc0", "wne");
                    let nonzero = self.closed_fact(
                        &apart_from_zero,
                        scope,
                        facts,
                        &what,
                        Some(step),
                    )?;
                    let ps = self.membership(&times, "cc", scope, &w.spec.facts)?;
                    let pg = self.membership(&gap, "cc", scope, &w.spec.facts)?;
                    apart = self.b.ap(
                        "mulne0d",
                        &binds! {"ph" => scope, "A" => &times, "B" => &gap},
                        &[&ps, &pg, &nonzero, &apart],
                    );
                    gap = t!(times, gap, "cmul", "co");
                }
                let alike = take!(self.same_polynomial(w, &gap, &whole)?);
                let pl = self.membership(&lhs, "cc", scope, &w.spec.facts)?;
                let pr = self.membership(&rhs, "cc", scope, &w.spec.facts)?;
                let moved = self.b.ap(
                    "eqnetrrd",
                    &binds! {"ph" => scope, "A" => &gap, "B" => &whole, "C" => "cc0"},
                    &[&alike, &apart],
                );
                let differ = self.b.ap(
                    "subne0ad",
                    &binds! {"ph" => scope, "A" => &lhs, "B" => &rhs},
                    &[&pl, &pr, &moved],
                );
                return Ok(Built(self.b.ap(
                    "neneqd",
                    &binds! {"ph" => scope, "A" => &lhs, "B" => &rhs},
                    &[&differ],
                )));
            }
        }
        Ok(Route::no("no cited disequality is the claim rescaled"))
    }

    /// A claim the cited equation already is, once its division goes:
    /// `divmuleq` is the step between them.
    #[allow(clippy::too_many_arguments)]
    fn crossed_from_cited(
        &mut self,
        step: &Step,
        left: &Rpn,
        right: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        w: &mut Work,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let want = field::equation(&self.to_term(&t!(left, right, "wceq")), &labels);
        for r in &step.just.refs {
            // A line saying several things is read a sentence at a time, as
            // any line a step cites is.
            for part in self.line_writes(r, lines) {
                let cited = self.to_term(&part);
                if cited.variable().is_some()
                    || cited.label() != Some("wceq")
                    || cited.children().len() != 2
                {
                    continue;
                }
                let mine = field::equation(&cited, &labels);
                match (&want, &mine) {
                    (Some(want), Some(mine)) if mine == want => {}
                    _ => continue,
                }
                let Built(given) = self.cited_fact(r, &cited, scope, facts, lines)?
                else {
                    continue;
                };
                let found = self.cleared(w, &cited, left, right, given)?;
                if !found.is_declined() {
                    return Ok(found);
                }
            }
        }
        Ok(Route::no("no cited equation is the claim divided"))
    }

    /// The cited equation with its denominators multiplied out.
    fn cleared(
        &mut self,
        w: &mut Work,
        cited: &Term,
        left: &Rpn,
        right: &Rpn,
        given: Proof,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let was: Vec<Rpn> = cited.children().iter().map(|c| self.rpn(c)).collect();
        let mut quotients = Vec::new();
        for (side, said) in cited.children().iter().zip(&was) {
            let Quotiented { over, under, proof } =
                take!(w
                    .e
                    .normalize_quotient(&mut self.ask(&w.spec), side, &labels)?);
            quotients.push(w.e.as_quotient(
                &mut self.ask(&w.spec),
                over,
                under,
                proof,
                said,
            )?);
        }
        let (below, beneath, second) = quotients.pop().unwrap();
        let (over, under, first) = quotients.pop().unwrap();
        let (a, b) = (Emitter::spell_run(&over), Emitter::spell_run(&under));
        let (c, d) = (Emitter::spell_run(&below), Emitter::spell_run(&beneath));
        let p1 = w.e.pair_of(&mut self.ask(&w.spec), &under)?;
        let p2 = w.e.pair_of(&mut self.ask(&w.spec), &beneath)?;
        let (p1, p2) = (take!(p1), take!(p2));
        let u = w.spec.scope.clone();
        let rc1 = w.e.run_cc(&mut self.ask(&w.spec), &over)?;
        let rc2 = w.e.run_cc(&mut self.ask(&w.spec), &below)?;
        let quotient = t!(t!(a, b, "cdiv", "co"), t!(c, d, "cdiv", "co"), "wceq");
        let crossed_eq = t!(t!(a, d, "cmul", "co"), t!(c, b, "cmul", "co"), "wceq");
        let matched = self.b.ap(
            "3eqtr3d",
            &binds! {"ph" => &u, "A" => &was[0], "B" => &was[1], "C" => t!(a, b, "cdiv", "co"), "D" => t!(c, d, "cdiv", "co")},
            &[&given, &first, &second],
        );
        let tops = self.b.ap("jca", &binds! {"ph" => &u, "ps" => t!(a, "cc", "wcel"), "ch" => t!(c, "cc", "wcel")}, &[&rc1, &rc2]);
        let pair = |x: &Rpn| t!(t!(x, "cc", "wcel"), t!(x, "cc0", "wne"), "wa");
        let bottoms = self.b.ap(
            "jca",
            &binds! {"ph" => &u, "ps" => pair(&b), "ch" => pair(&d)},
            &[&p1, &p2],
        );
        let law = self.b.ap(
            "divmuleq",
            &binds! {"A" => &a, "B" => &c, "C" => &b, "D" => &d},
            &[],
        );
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => &u, "ps" => t!(t!(a, "cc", "wcel"), t!(c, "cc", "wcel"), "wa"),
            "ch" => t!(pair(&b), pair(&d), "wa"), "th" => t!(quotient, crossed_eq, "wb")},
            &[&tops, &bottoms, &law],
        );
        let crossed = self.b.ap(
            "mpbid",
            &binds! {"ph" => &u, "ps" => &quotient, "ch" => &crossed_eq},
            &[&matched, &turn],
        );
        // The claim and the crossed equation are one polynomial, which says
        // their differences agree and not their sides: (H(b) − H(a))·1 =
        // 0·(b − a) carries H(b) = H(a) with each side split otherwise.
        let facts = w.spec.facts.clone();
        let (p, q) = (t!(a, d, "cmul", "co"), t!(c, b, "cmul", "co"));
        let p_cc = self.in_cc(&p, &u, &facts)?;
        let gap = t!(p, q, "cmin", "co");
        let whole = t!(left, right, "cmin", "co");
        let alike = self.same_polynomial(w, &gap, &whole)?;
        let left_cc = self.in_cc(left, &u, &facts)?;
        let right_cc = self.in_cc(right, &u, &facts)?;
        let (p_cc, alike, left_cc, right_cc) =
            (take!(p_cc), take!(alike), take!(left_cc), take!(right_cc));
        let vanishes = self.b.ap(
            "subeq0bd",
            &binds! {"ph" => &u, "A" => &p, "B" => &q},
            &[&p_cc, &crossed],
        );
        let reached = self.b.ap(
            "eqtr3d",
            &binds! {"ph" => &u, "A" => &gap, "B" => &whole, "C" => "cc0"},
            &[&alike, &vanishes],
        );
        let turn = self.b.ap(
            "subeq0ad",
            &binds! {"ph" => &u, "A" => left, "B" => right},
            &[&left_cc, &right_cc],
        );
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => &u, "ps" => t!(whole, "cc0", "wceq"), "ch" => t!(left, right, "wceq")},
            &[&reached, &turn],
        )))
    }

    /// What says a denominator is not zero, asked of the scope: the text
    /// writes these, so the fact is there to be found. `normal` asks this
    /// while writing a proof it has already decided, so a missing fact is a
    /// defect here and not a decline.
    pub fn not_zero(
        &mut self,
        scope: &Rpn,
        facts: &Facts,
        said: &Rpn,
    ) -> Checked<Proof> {
        let kept = OnceCell::new();
        self.not_zero_named(scope, facts, &kept, said, said)
    }

    /// `not_zero`, where what is asked is a form the normaliser made of a
    /// divisor the page wrote as `named`, which a defect names. Every stage
    /// of `divisor_apart` but a line the step does not name, the search
    /// last.
    pub fn not_zero_named(
        &mut self,
        scope: &Rpn,
        facts: &Facts,
        implied: &OnceCell<Vec<Facts>>,
        said: &Rpn,
        named: &Rpn,
    ) -> Checked<Proof> {
        let reach = Reach {
            in_scope: None,
            search: true,
        };
        match self.divisor_apart(said, scope, facts, implied, &reach)? {
            Built(p) => Ok(p),
            Declined(_) => Err(self.defect(
                self.at,
                format!(
                    "nothing says {}, which this step needs to divide by it",
                    self.render(&t!(named, "cc0", "wne"))
                ),
            )),
        }
    }

    /// ( scope -> divisor =/= 0 ) by the one order the build takes evidence
    /// of a divisor in (`ELABORATION.md`, a divisor's ≠ 0), or a decline:
    ///
    /// 1. a term of numerals alone whose value is not zero, worked out as
    ///    `arithmetic` works one out, or a positive integer the page says
    ///    once (`SYNTAX.md`), which rests on no line;
    /// 2. a line the step may rest on saying it (`written_nonzero`);
    /// 3. its parts: a product, a quotient, a negation or a power to a
    ///    numeral is not zero when its parts are, each by this same order;
    /// 4. a line in scope the step does not name, where `reach` gives them,
    ///    which the step then rests on;
    /// 5. the search, where `reach` says, which offers only lines the step
    ///    may rest on.
    ///
    /// A line saying the whole comes before its parts, and the parts before
    /// a line the step does not name: a step citing t² ≠ 0 rests on that,
    /// and one naming x ≠ 0 rests on that, not on an uncited 1/x ≠ 0.
    pub fn divisor_apart(
        &mut self,
        divisor: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        implied: &OnceCell<Vec<Facts>>,
        reach: &Reach,
    ) -> Checked<Route<Proof>> {
        let apart = t!(divisor, "cc0", "wne");
        // What the step may rest on, and nothing else in scope, until
        // `reach` lets a line it does not name be read (`GOALS.md` decision
        // 9).
        let named = self.restable(facts);
        let numeral = numerals::value(&self.to_term(divisor)).filter(|v| !v.is_zero());
        if let Some(value) = numeral {
            let closed = numerals::ne0(&self.b, value);
            return Ok(Built(pf!(self.b; apart, scope, closed, "a1i")));
        }
        if let Some(found) = self.closed_nonzero(divisor, scope, &named)? {
            return Ok(Built(found));
        }
        if let Some(positive) = self.positive_divisor(divisor, scope, &named)? {
            return Ok(Built(positive));
        }
        if let Some(found) = self.written_nonzero(scope, &named, implied, divisor)? {
            return Ok(Built(found));
        }
        if let Some(lines) = &reach.in_scope {
            let restable = self.restable(lines.lines);
            if let Some(found) =
                self.written_nonzero(scope, &restable, lines.named, divisor)?
            {
                return Ok(Built(found));
            }
        }
        if let Built(found) =
            self.parts_apart(divisor, scope, &named, implied, reach)?
        {
            return Ok(Built(found));
        }
        if let Some(lines) = &reach.in_scope {
            if let Some(found) =
                self.written_nonzero(scope, lines.lines, lines.implied, divisor)?
            {
                return Ok(Built(found));
            }
        }
        if reach.search {
            // Any other divisor's `≠ 0` is the page's to say, so no
            // membership said once leads to it (`READERS.md`).
            self.beyond_once += 1;
            let found =
                self.settle(&self.to_term(&apart), scope, &named, 3, None, None);
            self.beyond_once -= 1;
            if let Built(p) = found? {
                return Ok(Built(p));
            }
        }
        Ok(self.no(
            "nothing says {}, which this step needs to divide by it",
            &[&apart],
        ))
    }

    /// ( scope -> divisor =/= 0 ) from its parts, each by `divisor_apart`:
    /// a product or a quotient by `mulne0d` or `divne0d`, a negation by
    /// `negne0d`, a power to a numeral by `expne0d`, the numeral 0 among
    /// them. A decline for any other divisor, or a part not so.
    fn parts_apart(
        &mut self,
        divisor: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        implied: &OnceCell<Vec<Facts>>,
        reach: &Reach,
    ) -> Checked<Route<Proof>> {
        let term = self.to_term(divisor);
        if term.variable().is_some() {
            return Ok(Route::no("a letter has no parts"));
        }
        let kids: Vec<Rpn> = term.children().iter().map(|c| self.rpn(c)).collect();
        let how = (term.label() == Some("co") && kids.len() == 3)
            .then(|| kids[2].alone().map(String::from))
            .flatten();
        let power = (how.as_deref() == Some("cexp"))
            .then(|| numerals::value(&term.children()[1]))
            .flatten();
        let (lemma, parts): (&str, Vec<&Rpn>) = match (term.label(), how.as_deref()) {
            (Some("cneg"), _) if kids.len() == 1 => ("negne0d", vec![&kids[0]]),
            (_, Some("cmul")) => ("mulne0d", vec![&kids[0], &kids[1]]),
            (_, Some("cdiv")) => ("divne0d", vec![&kids[0], &kids[1]]),
            (_, Some("cexp")) if power.is_some() => ("expne0d", vec![&kids[0]]),
            _ => return Ok(Route::no(
                "the divisor is no product, quotient, negation or power to a numeral",
            )),
        };
        let mut held = Vec::new();
        let mut apart = Vec::new();
        for part in &parts {
            held.push(take!(self.in_cc(part, scope, facts)?));
            apart.push(take!(
                self.divisor_apart(part, scope, facts, implied, reach)?
            ));
        }
        let mut binds = binds! {"ph" => scope, "A" => parts[0]};
        if let Some(second) = parts.get(1) {
            binds.insert("B".to_string(), (*second).clone());
        }
        let mut hyps: Vec<Proof> = held.into_iter().chain(apart).collect();
        // ( A ^ N ) with N the whole number written, which `expne0d` asks
        // in ℤ.
        if let Some(power) = power {
            let exponent = &kids[1];
            let whole = if power.is_zero() {
                self.b.step("0z")
            } else {
                let natural = numerals::nn(&self.b, power);
                self.b.ap("nnzi", &binds! {"N" => exponent}, &[&natural])
            };
            hyps.push(self.b.ap(
                "a1i",
                &binds! {"ph" => t!(exponent, "cz", "wcel"), "ps" => scope},
                &[&whole],
            ));
            binds.insert("N".to_string(), exponent.clone());
        }
        let hyps: Vec<&Proof> = hyps.iter().collect();
        Ok(Built(self.b.ap(lemma, &binds, &hyps)))
    }

    /// ( scope -> divisor =/= 0 ) for a closed divisor whose value is not
    /// zero, a fact about numerals worked out as `arithmetic` works one out,
    /// which the page says once (`SYNTAX.md`); None for any other.
    fn closed_nonzero(
        &mut self,
        divisor: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        if !matches!(field::closed_value(&self.to_term(divisor)), Built(Value::Exact(v)) if !v.is_zero())
        {
            return Ok(None);
        }
        let denial = t!(t!(divisor, "cc0", "wceq"), "wn");
        let worked = match self.prove_numeral(&denial, scope, facts)? {
            Built(p) => Built(p),
            Declined(_) => self.by_values(&denial, scope, facts)?,
        };
        Ok(match worked {
            Built(p) => Some(self.b.ap(
                "neqned",
                &binds! {"ph" => scope, "A" => divisor, "B" => "cc0"},
                &[&p],
            )),
            Declined(_) => None,
        })
    }

    /// What a line among `facts`, or what the step wrote, says makes a term
    /// not zero, or None: the one reading of a line for a divisor's ≠ 0
    /// (`divisor_apart`, stages 2 and 5).
    pub fn written_nonzero(
        &mut self,
        scope: &Rpn,
        facts: &Facts,
        implied: &OnceCell<Vec<Facts>>,
        said: &Rpn,
    ) -> Checked<Option<Proof>> {
        // Written either way round, and as ¬ said = 0 as well (`held`), in
        // a line or in what the step wrote.
        let want = t!(said, "cc0", "wne");
        if let Some(p) = self.held(facts, &want, scope)? {
            return Ok(Some(p));
        }
        if let Some(w) = self.written_held(&want)? {
            if let Some(p) = self.lifted_to(&want, &w.proof, &w.at, scope) {
                return Ok(Some(p));
            }
        }
        // A line saying the term is above zero, or below it, says it is not
        // zero (`gt0ne0d`, `lt0ne0d`), as a reader takes A > 0.
        for (sign, lemma) in [
            (t!("cc0", said, "clt", "wbr"), "gt0ne0d"),
            (t!(said, "cc0", "clt", "wbr"), "lt0ne0d"),
        ] {
            let mut found = self.held(facts, &sign, scope)?;
            if found.is_none() {
                if let Some(w) = self.written_held(&sign)? {
                    found = self.lifted_to(&sign, &w.proof, &w.at, scope);
                }
            }
            if let Some(found) = found {
                return Ok(Some(self.b.ap(
                    lemma,
                    &binds! {"ph" => scope, "A" => said},
                    &[&found],
                )));
            }
        }
        // Or a membership written that says it: N ∈ ℕ says N ≠ 0. What each
        // of `facts` also says is worked out once for all the denominators
        // that ask (`take_implied`).
        for more in take_implied(implied, self, scope, facts)? {
            if let Some(p) = self.held(more, &want, scope)? {
                return Ok(Some(p));
            }
        }
        if let Some(p) = self.apart_as_written(said, scope, facts)? {
            return Ok(Some(p));
        }
        // A term is not zero where its negation is not (`negne0bd`): the
        // normaliser writes (−q)/(−p) over p, and the page says −p ∈ ℕ.
        let term = self.to_term(said);
        if term.label() == Some("cneg") {
            return Ok(None);
        }
        let negated = t!(said, "cneg");
        let Some(found) = self.written_nonzero(scope, facts, implied, &negated)? else {
            return Ok(None);
        };
        let Built(number) = self.part(said, &t!("cc"), scope, facts)? else {
            return Ok(None);
        };
        let turned =
            self.b
                .ap("negne0bd", &binds! {"ph" => scope, "A" => said}, &[&number]);
        Ok(Some(self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &want, "ch" => t!(&negated, "cc0", "wne")},
            &[&found, &turned],
        )))
    }

    /// The same fact about the same denominator, spelt as the text spells
    /// it: what decides is the polynomial, and the equation carrying one
    /// spelling to the other is the normalizer's own.
    fn apart_as_written(
        &mut self,
        said: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let mut w = Work::plain(scope, facts);
        let labels = self.b.flabel.clone();
        for (fact, proof) in facts.entries() {
            if !fact.ends_with(&["wne"]) && !fact.ends_with(&["wn"]) {
                continue;
            }
            let node = self.to_term(&fact);
            if node.variable().is_some() {
                continue;
            }
            let sides = if node.label() == Some("wn") {
                let inner = node.children()[0].clone();
                if inner.variable().is_some() || inner.label() != Some("wceq") {
                    continue;
                }
                inner.children().to_vec()
            } else {
                node.children().to_vec()
            };
            if sides.len() != 2 {
                continue;
            }
            // The side that is not zero, whichever side the page wrote it on,
            // and the fact read as that side =/= 0 (`held`).
            let (left, right) = (self.rpn(&sides[0]), self.rpn(&sides[1]));
            let subject =
                match (left.alone() == Some("cc0"), right.alone() == Some("cc0")) {
                    (false, true) => sides[0].clone(),
                    (true, false) => sides[1].clone(),
                    _ => continue,
                };
            let was = self.rpn(&subject);
            if was == *said {
                continue;
            }
            let wanted = t!(was, "cc0", "wne");
            let one = Facts::new();
            self.know(&one, fact.clone(), proof.clone());
            let Some(given) = self.held(&one, &wanted, scope)? else {
                continue;
            };
            let Built((items, same)) =
                w.e.normalize(&mut self.ask(&w.spec), &subject, &labels)?
            else {
                continue;
            };
            if Emitter::spell_run(&items) != *said {
                continue;
            }
            return Ok(Some(self.b.ap(
                "eqnetrrd",
                &binds! {"ph" => scope, "A" => &was, "B" => said, "C" => "cc0"},
                &[&same, &given],
            )));
        }
        Ok(None)
    }

    /// Two terms driven to one canonical form, and so to each other. Where
    /// either divides, the canonical form is a numerator over a denominator,
    /// and two of those are the same when the cross product is.
    pub(super) fn same_polynomial(
        &mut self,
        w: &mut Work,
        left: &Rpn,
        right: &Rpn,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let lt = self.to_term(left);
        let Quotiented {
            over: first_items,
            under: first_under,
            proof: first,
        } = take!(w
            .e
            .normalize_quotient(&mut self.ask(&w.spec), &lt, &labels)?);
        let rt = self.to_term(right);
        let Quotiented {
            over: second_items,
            under: second_under,
            proof: second,
        } = take!(w
            .e
            .normalize_quotient(&mut self.ask(&w.spec), &rt, &labels)?);
        if first_under.is_none() && second_under.is_none() {
            if Emitter::spell_run(&first_items) != Emitter::spell_run(&second_items) {
                return Ok(Route::no("the two are not one polynomial"));
            }
            return Ok(Built(self.b.ap(
                "eqtr4d",
                &binds! {"ph" => &w.spec.scope, "A" => left, "B" => Emitter::spell_run(&first_items), "C" => right},
                &[&first, &second],
            )));
        }
        self.cross_multiplied(
            w,
            left,
            right,
            (first_items, first_under, first),
            (second_items, second_under, second),
        )
    }

    /// Two quotients equal, because their cross product is.
    fn cross_multiplied(
        &mut self,
        w: &mut Work,
        left: &Rpn,
        right: &Rpn,
        one: (Run, Option<Run>, Proof),
        other: (Run, Option<Run>, Proof),
    ) -> Checked<Route<Proof>> {
        let (over, under, first) =
            w.e.as_quotient(&mut self.ask(&w.spec), one.0, one.1, one.2, left)?;
        let (below, beneath, second) =
            w.e.as_quotient(&mut self.ask(&w.spec), other.0, other.1, other.2, right)?;
        let (a, b) = (Emitter::spell_run(&over), Emitter::spell_run(&under));
        let (c, d) = (Emitter::spell_run(&below), Emitter::spell_run(&beneath));
        let crossed = take!(self.same_polynomial(
            w,
            &t!(a, d, "cmul", "co"),
            &t!(c, b, "cmul", "co")
        )?);
        let p1 = w.e.pair_of(&mut self.ask(&w.spec), &beneath)?;
        let p2 = w.e.pair_of(&mut self.ask(&w.spec), &under)?;
        let (p1, p2) = (take!(p1), take!(p2));
        let u = w.spec.scope.clone();
        let rc1 = w.e.run_cc(&mut self.ask(&w.spec), &below)?;
        let rc2 = w.e.run_cc(&mut self.ask(&w.spec), &over)?;
        let pair = |x: &Rpn| t!(t!(x, "cc", "wcel"), t!(x, "cc0", "wne"), "wa");
        let turned = self.b.ap(
            "eqcomd",
            &binds! {"ph" => &u, "A" => t!(a, d, "cmul", "co"), "B" => t!(c, b, "cmul", "co")},
            &[&crossed],
        );
        let tops = self.b.ap("jca", &binds! {"ph" => &u, "ps" => t!(c, "cc", "wcel"), "ch" => t!(a, "cc", "wcel")}, &[&rc1, &rc2]);
        let bottoms = self.b.ap(
            "jca",
            &binds! {"ph" => &u, "ps" => pair(&d), "ch" => pair(&b)},
            &[&p1, &p2],
        );
        let law = self.b.ap(
            "divmuleq",
            &binds! {"A" => &c, "B" => &a, "C" => &d, "D" => &b},
            &[],
        );
        let quotients = t!(t!(c, d, "cdiv", "co"), t!(a, b, "cdiv", "co"), "wceq");
        let products = t!(t!(c, b, "cmul", "co"), t!(a, d, "cmul", "co"), "wceq");
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => &u, "ps" => t!(t!(c, "cc", "wcel"), t!(a, "cc", "wcel"), "wa"),
            "ch" => t!(pair(&d), pair(&b), "wa"), "th" => t!(quotients, products, "wb")},
            &[&tops, &bottoms, &law],
        );
        let back = self.b.ap(
            "mpbird",
            &binds! {"ph" => &u, "ps" => &quotients, "ch" => &products},
            &[&turned, &turn],
        );
        let across = self.b.ap(
            "eqtrd",
            &binds! {"ph" => &u, "A" => right, "B" => t!(c, d, "cdiv", "co"), "C" => t!(a, b, "cdiv", "co")},
            &[&second, &back],
        );
        Ok(Built(self.b.ap(
            "eqtr4d",
            &binds! {"ph" => &u, "A" => left, "B" => t!(a, b, "cdiv", "co"), "C" => right},
            &[&first, &across],
        )))
    }

    /// ( scope -> times · gap = 0 ) from ( scope -> gap = 0 ), `vanishes`:
    /// a multiple of 0 is 0 (`mul01d`), `times` a complex number by
    /// `times_cc`.
    pub(super) fn multiple_vanishing(
        &self,
        gap: &Rpn,
        vanishes: &Proof,
        times: &Rpn,
        times_cc: &Proof,
        scope: &Rpn,
    ) -> Vanishing {
        let moved = self.b.ap(
            "oveq2d",
            &binds! {"ph" => scope, "A" => gap, "B" => "cc0", "C" => times, "F" => "cmul"},
            &[vanishes],
        );
        let zero =
            self.b
                .ap("mul01d", &binds! {"ph" => scope, "A" => times}, &[times_cc]);
        let term = t!(times, gap, "cmul", "co");
        let proof = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &term, "B" => t!(times, "cc0", "cmul", "co"), "C" => "cc0"},
            &[&moved, &zero],
        );
        Vanishing { term, proof }
    }

    /// ( scope -> t₁ + … + tₙ = 0 ), the terms added from the left, from
    /// each of them 0: 0 + 0 is 0 (`00id`). At least one term.
    pub(super) fn vanishing_sum(&self, terms: &[Vanishing], scope: &Rpn) -> Vanishing {
        let naught = t!("cc0", "cc0", "caddc", "co");
        let mut sum = terms[0].clone();
        for one in &terms[1..] {
            let joined = t!(&sum.term, &one.term, "caddc", "co");
            let both = self.b.ap(
                "oveq12d",
                &binds! {"ph" => scope, "A" => &sum.term, "B" => "cc0", "C" => &one.term, "D" => "cc0", "F" => "caddc"},
                &[&sum.proof, &one.proof],
            );
            let zero = self.closed_law(&t!(&naught, "cc0", "wceq"), "00id", scope);
            sum = Vanishing {
                proof: self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &joined, "B" => &naught, "C" => "cc0"},
                    &[&both, &zero],
                ),
                term: joined,
            };
        }
        sum
    }

    /// A claim the cited equations add up to: each cited equation is a
    /// difference that is zero, multiplied by what the combination says and
    /// still zero; the sum of them is zero, and that sum is the claim's own
    /// difference, which is the normalizer's question.
    #[allow(clippy::too_many_arguments)]
    fn summed_from_cited(
        &mut self,
        step: &Step,
        left: &Rpn,
        right: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        w: &mut Work,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let claimed = self.to_term(&t!(left, right, "wceq"));
        let want = field::equation(&claimed, &labels);
        let mut given = Vec::new();
        let mut unders = Vec::new();
        let mut where_: Vec<(String, Term)> = Vec::new();
        // What each cited equation had divided out of it.
        let mut taken_out: Vec<Poly> = Vec::new();
        for r in &step.just.refs {
            for said in self.line_writes(r, lines) {
                let node = self.to_term(&said);
                if let Some(one) = field::equation(&node, &labels) {
                    let read = claim_says(&node, one, &labels);
                    given.push(read.says);
                    unders.push(field::exactly(
                        &denominators(&node, &labels),
                        &read.taken,
                    ));
                    taken_out.push(read.taken);
                    where_.push((r.clone(), node));
                }
            }
        }
        let Some(want) = want.filter(|_| !given.is_empty()) else {
            return Ok(Route::no("the step cites no equation"));
        };
        // The first reading of the claim the cited equations make, as the
        // decision found it (`readings`, `combination`).
        let claim_under = denominators(&claimed, &labels);
        let found = readings(&claimed, want, &labels)
            .into_iter()
            .find_map(|says| {
                combination(&given, &unders, &says, &claim_under)
                    .filter(|h| !h.is_empty())
                    .map(|how| (says, how))
            });
        let Some((says, how)) = found else {
            return Ok(Route::no("no sum of the cited equations is the claim"));
        };
        // The decision reads what the claim says (`claim_says`), and the
        // proof takes each cited equation as written: so each multiplier
        // carries its equation's denominators, and is divided by a divisor
        // of the claim's that every one carries; the claim's sides are each
        // multiplied by the divisors left, which are taken off at the end.
        let across = |node: &Term| denominators(node, &labels);
        let mut factors: Vec<Factor> = Vec::new();
        let mut written = says.taken.clone();
        for f in says.kept {
            let Some(f) = f else {
                return Ok(Route::no("a divisor that divides more than once"));
            };
            written = written.times(&field::read(f.term(), &labels).over);
            factors.push(f);
        }
        if written != across(&claimed) {
            return Ok(Route::no(
                "the divisors written are not the claim's denominators",
            ));
        }
        // A divisor every multiplier carries is divided out of them, and only
        // the rest multiply the claim's sides: (f(b) − f(a))/(b − a) from an
        // equation over b − a needs nothing multiplied.
        let mut multipliers: Vec<Poly> = Vec::new();
        for taken in &how {
            let carried = taken.multiplier().times(&across(&where_[taken.which].1));
            let Some(by) = field::exactly(&carried, &taken_out[taken.which]) else {
                return Ok(Route::no(
                    "a cited equation's divisors are not its denominators",
                ));
            };
            multipliers.push(by);
        }
        let mut multiplying: Vec<Factor> = Vec::new();
        for f in factors {
            let by = field::read(f.term(), &labels).over;
            let carried: Option<Vec<Poly>> =
                multipliers.iter().map(|p| field::exactly(p, &by)).collect();
            match carried {
                Some(divided) => multipliers = divided,
                None => multiplying.push(f),
            }
        }
        let factors = multiplying;
        // Weights with a denominator are all multiplied by the least common
        // one, which the sum then shows the claim's sides each multiplied
        // by, and which is cancelled at the end: s = t is half of
        // 2·s + 1 = 2·t + 1, and the proof doubles s = t instead.
        let common = field::common_denominator(
            multipliers.iter().flat_map(|p| p.terms.values()),
        );
        let Some(common) = common.to_i64() else {
            return Ok(Route::no("a common denominator past what a numeral writes"));
        };
        let mut pieces: Vec<Vanishing> = Vec::new();
        for (taken, by) in how.iter().zip(&multipliers) {
            let (r, node) = where_[taken.which].clone();
            let (a, b) = (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
            let gap = t!(a, b, "cmin", "co");
            let Some(times) =
                multiplier(&by.scaled(&Q::from_integer(BigInt::from(common))))
            else {
                return Ok(Route::no("a multiplier with no spelling"));
            };
            // A sum the decision read as linear is written over a placeholder
            // letter; in a proof it is the step's own (`sum_letter`).
            let times = match &self.sum_letter {
                Some(letter) => Rpn::from(
                    times
                        .tokens()
                        .iter()
                        .map(|t| if *t == "§" { Symbol::of(letter) } else { *t })
                        .collect::<Vec<_>>(),
                ),
                None if times.has("§") => {
                    return Ok(Route::no("a multiplier holding a sum read as linear"));
                }
                None => times,
            };
            let cited = self.cited_fact(&r, &node, scope, facts, lines)?;
            let a_cc = self.in_cc(&a, scope, facts)?;
            let b_cc = self.in_cc(&b, scope, facts)?;
            let (cited, a_cc, b_cc) = (take!(cited), take!(a_cc), take!(b_cc));
            let turn = self.b.ap(
                "subeq0ad",
                &binds! {"ph" => scope, "A" => &a, "B" => &b},
                &[&a_cc, &b_cc],
            );
            let vanishes = self.b.ap(
                "mpbird",
                &binds! {"ph" => scope, "ps" => t!(gap, "cc0", "wceq"), "ch" => t!(a, b, "wceq")},
                &[&cited, &turn],
            );
            let atom = self.membership(
                &times,
                "cc",
                &w.spec.scope.clone(),
                &w.spec.facts.clone(),
            )?;
            pieces.push(self.multiple_vanishing(&gap, &vanishes, &times, &atom, scope));
        }
        let Vanishing {
            term: total,
            proof: sums,
        } = self.vanishing_sum(&pieces, scope);
        // What the claim's sides are multiplied by: the common denominator of
        // the weights, then each divisor the claim writes.
        let mut spelt: Vec<Rpn> = factors.iter().map(|f| self.rpn(f.term())).collect();
        if common != 1 {
            spelt.insert(0, numerals::spell(common.unsigned_abs()));
        }
        let factor: Option<Rpn> = spelt
            .iter()
            .cloned()
            .reduce(|acc, one| t!(acc, one, "cmul", "co"));
        let sides: Vec<Rpn> = match &factor {
            None => vec![left.clone(), right.clone()],
            Some(factor) => [left, right]
                .iter()
                .map(|one| t!(factor, one, "cmul", "co"))
                .collect(),
        };
        let (l, r) = (&sides[0], &sides[1]);
        let whole = t!(l, r, "cmin", "co");
        let alike = self.same_polynomial(w, &total, &whole)?;
        let left_cc = self.in_cc(l, scope, facts)?;
        let right_cc = self.in_cc(r, scope, facts)?;
        let (alike, left_cc, right_cc) =
            (take!(alike), take!(left_cc), take!(right_cc));
        let reached = self.b.ap(
            "eqtr3d",
            &binds! {"ph" => scope, "A" => &total, "B" => &whole, "C" => "cc0"},
            &[&alike, &sums],
        );
        let turn = self.b.ap(
            "subeq0ad",
            &binds! {"ph" => scope, "A" => l, "B" => r},
            &[&left_cc, &right_cc],
        );
        let equal = self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(whole, "cc0", "wceq"), "ch" => t!(l, r, "wceq")},
            &[&reached, &turn],
        );
        let Some(factor) = factor else {
            return Ok(Built(equal));
        };
        let Built(apart) = self.factors_apart(w, common, &factors, scope, facts)?
        else {
            return Ok(Route::no("a divisor not known to be a number"));
        };
        self.cancelled_by(&factor, apart, left, right, &sides, equal, scope, facts)
            .map(Built)
    }

    /// ( scope -> ( F e. CC /\ F =/= 0 ) ) for F the numeral `common`, where
    /// it is not 1, times each of `factors` in turn: the numeral is not 0 as
    /// a numeral, and a divisor by what the page says of it, which a step
    /// that divides writes. The numerator c of a divisor c/e is not 0 by
    /// what the page says of c/e, carried to c by `divne0bd`; the −c of a
    /// divisor −(c/e) by `negated_top_apart`.
    fn factors_apart(
        &mut self,
        w: &mut Work,
        common: i64,
        factors: &[Factor],
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut each: Vec<(Rpn, Proof, Proof)> = Vec::new();
        if common != 1 {
            let numeral = numerals::spell(common.unsigned_abs());
            let held = w.e.number(&self.ask(&w.spec), &BigInt::from(common));
            let apart = self.b.ap(
                "a1i",
                &binds! {"ph" => t!(numeral, "cc0", "wne"), "ps" => scope},
                &[&numerals::ne0(&self.b, common.unsigned_abs())],
            );
            each.push((numeral, held, apart));
        }
        for f in factors {
            let said = self.rpn(f.term());
            let held = take!(self.in_cc(&said, scope, facts)?);
            let apart = take!(self.factor_apart(f, &said, &held, scope, facts)?);
            each.push((said, held, apart));
        }
        let mut parts = each.into_iter();
        let (mut so_far, mut held, mut apart) =
            parts.next().expect("a factor at least");
        for (one, one_held, one_apart) in parts {
            let binds = binds! {"ph" => scope, "A" => &so_far, "B" => &one};
            apart =
                self.b
                    .ap("mulne0d", &binds, &[&held, &one_held, &apart, &one_apart]);
            held = self.b.ap("mulcld", &binds, &[&held, &one_held]);
            so_far = t!(so_far, one, "cmul", "co");
        }
        Ok(Built(self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(so_far, "cc", "wcel"), "ch" => t!(so_far, "cc0", "wne")},
            &[&held, &apart],
        )))
    }

    /// ( scope -> said =/= 0 ) for `said`, what the factor `f` multiplies a
    /// claim's sides by, held in ℂ by `held`: a divisor by what the page
    /// says of it; the numerator c of a divisor c/e by what the page says of
    /// c/e, carried to c by `divne0bd`; the −c of a divisor −(c/e) by
    /// `negated_top_apart`; and the product of a divisor X·Y's two parts'
    /// by each part's, joined by `mulne0d`.
    fn factor_apart(
        &mut self,
        f: &Factor,
        said: &Rpn,
        held: &Proof,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        Ok(Built(match f {
            Factor::Divisor(_) => self.not_zero(scope, facts, said)?,
            Factor::Numerator { divisor, below, .. } => {
                let (whole, under) = (self.rpn(divisor), self.rpn(below));
                let whole_apart = self.not_zero(scope, facts, &whole)?;
                let under_apart = self.not_zero(scope, facts, &under)?;
                let under_cc = take!(self.in_cc(&under, scope, facts)?);
                let iff = self.b.ap(
                    "divne0bd",
                    &binds! {"ph" => scope, "A" => said, "B" => &under},
                    &[held, &under_cc, &under_apart],
                );
                self.b.ap(
                    "mpbird",
                    &binds! {"ph" => scope, "ps" => t!(said, "cc0", "wne"),
                    "ch" => t!(whole, "cc0", "wne")},
                    &[&whole_apart, &iff],
                )
            }
            Factor::NegatedNumerator {
                divisor,
                quotient,
                top,
                below,
                ..
            } => {
                let parts = NegatedQuotient {
                    divisor: self.rpn(divisor),
                    quotient: self.rpn(quotient),
                    top: self.rpn(top),
                    below: self.rpn(below),
                };
                take!(self.negated_top_apart(&parts, scope, facts)?)
            }
            Factor::Product { left, right, .. } => {
                let (x, y) = (self.rpn(left.term()), self.rpn(right.term()));
                let x_cc = take!(self.in_cc(&x, scope, facts)?);
                let y_cc = take!(self.in_cc(&y, scope, facts)?);
                let x_apart = take!(self.factor_apart(left, &x, &x_cc, scope, facts)?);
                let y_apart = take!(self.factor_apart(right, &y, &y_cc, scope, facts)?);
                self.b.ap(
                    "mulne0d",
                    &binds! {"ph" => scope, "A" => &x, "B" => &y},
                    &[&x_cc, &y_cc, &x_apart, &y_apart],
                )
            }
        }))
    }

    /// ( scope -> -u c =/= 0 ) for a divisor −(c/e) the page says is not 0:
    /// c/e is not 0 as its negation is not, c as c/e is not (`divne0bd`),
    /// and −c as c is not (`negne0bd` each way).
    fn negated_top_apart(
        &mut self,
        parts: &NegatedQuotient,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let NegatedQuotient {
            divisor,
            quotient,
            top,
            below,
        } = parts;
        let ne0 = |t: &Rpn| t!(t, "cc0", "wne");
        let whole_apart = self.not_zero(scope, facts, divisor)?;
        let quotient_cc = take!(self.in_cc(quotient, scope, facts)?);
        let top_cc = take!(self.in_cc(top, scope, facts)?);
        let below_cc = take!(self.in_cc(below, scope, facts)?);
        let below_apart = self.not_zero(scope, facts, below)?;
        let quotient_turn = self.b.ap(
            "negne0bd",
            &binds! {"ph" => scope, "A" => quotient},
            &[&quotient_cc],
        );
        let quotient_apart = self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => ne0(quotient), "ch" => ne0(divisor)},
            &[&whole_apart, &quotient_turn],
        );
        let divided = self.b.ap(
            "divne0bd",
            &binds! {"ph" => scope, "A" => top, "B" => below},
            &[&top_cc, &below_cc, &below_apart],
        );
        let top_apart = self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => ne0(top), "ch" => ne0(quotient)},
            &[&quotient_apart, &divided],
        );
        let top_turn =
            self.b
                .ap("negne0bd", &binds! {"ph" => scope, "A" => top}, &[&top_cc]);
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => ne0(top), "ch" => ne0(&t!(top, "cneg"))},
            &[&top_apart, &top_turn],
        )))
    }

    /// ( scope -> said e. CC ), for a term of the step's own depth: built by
    /// `part` first, from the step's own lines, and searched for where that
    /// cannot, to the depth every side condition is searched to.
    pub(super) fn in_cc(
        &mut self,
        said: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let found = self.part(said, &t!("cc"), scope, facts)?;
        if !found.is_declined() {
            return Ok(found);
        }
        self.within(said, &t!("cc"), scope, facts, 3)
    }

    /// A claim a cited equation is a whole multiple of: proving each side is
    /// that multiple is the polynomial case again, and what is left is
    /// cancelling the multiplier.
    #[allow(clippy::too_many_arguments)]
    fn scaled_from_cited(
        &mut self,
        step: &Step,
        left: &Rpn,
        right: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        w: &mut Work,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let want = field::equation(&self.to_term(&t!(left, right, "wceq")), &labels);
        for r in &step.just.refs {
            let Some(held) = self.line_written(r, lines) else {
                continue;
            };
            let cited = self.to_term(&held.claim);
            if cited.variable().is_some() || cited.label() != Some("wceq") {
                continue;
            }
            let times = whole_multiple(
                field::equation(&cited, &labels).as_ref(),
                want.as_ref(),
            );
            let Some(times) = times else {
                continue;
            };
            let numeral = numerals::spell(times.unsigned_abs());
            let scaled: Vec<Rpn> = [left, right]
                .iter()
                .map(|one| t!(numeral, one, "cmul", "co"))
                .collect();
            let was: Vec<Rpn> = cited.children().iter().map(|c| self.rpn(c)).collect();
            let mut sides = Vec::new();
            for (x, y) in was.iter().zip(&scaled) {
                sides.push(self.same_polynomial(w, x, y)?);
            }
            if sides.iter().any(|s| s.is_declined()) {
                continue;
            }
            let sides: Vec<Proof> =
                sides.into_iter().filter_map(|s| s.built()).collect();
            let given = self.carried(r, facts, lines);
            return self
                .cancel_multiple(
                    w, times, left, right, &scaled, &sides, given, &cited, scope, facts,
                )
                .map(Built);
        }
        Ok(Route::no("no cited equation is a multiple of the claim"))
    }

    /// The multiplier taken off both sides, which is `mulcan`.
    #[allow(clippy::too_many_arguments)]
    fn cancel_multiple(
        &mut self,
        w: &mut Work,
        times: i64,
        left: &Rpn,
        right: &Rpn,
        scaled: &[Rpn],
        sides: &[Proof],
        given: Proof,
        cited: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let matched = self.b.ap(
            "3eqtr3d",
            &binds! {"ph" => scope, "A" => self.rpn(&cited.children()[0]), "B" => self.rpn(&cited.children()[1]),
            "C" => &scaled[0], "D" => &scaled[1]},
            &[&given, &sides[0], &sides[1]],
        );
        let Built(both) = self.factors_apart(w, times, &[], scope, facts)? else {
            unreachable!("a numeral is a number and not 0");
        };
        let numeral = numerals::spell(times.unsigned_abs());
        self.cancelled_by(&numeral, both, left, right, scaled, matched, scope, facts)
    }

    /// ( scope -> left = right ) from `matched`, which proves the two sides
    /// `scaled`, each `factor` times its own side, and `both`, which says
    /// `factor` is a number and not 0: `mulcan` takes it off.
    #[allow(clippy::too_many_arguments)]
    fn cancelled_by(
        &mut self,
        factor: &Rpn,
        both: Proof,
        left: &Rpn,
        right: &Rpn,
        scaled: &[Rpn],
        matched: Proof,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let ml = self.membership(left, "cc", scope, facts)?;
        let mr = self.membership(right, "cc", scope, facts)?;
        let law = self.b.ap(
            "mulcan",
            &binds! {"A" => left, "B" => right, "C" => factor},
            &[],
        );
        let turn = self.b.ap(
            "syl3anc",
            &binds! {"ph" => scope, "ps" => t!(left, "cc", "wcel"), "ch" => t!(right, "cc", "wcel"),
            "th" => t!(t!(factor, "cc", "wcel"), t!(factor, "cc0", "wne"), "wa"),
            "ta" => t!(t!(scaled[0], scaled[1], "wceq"), t!(left, right, "wceq"), "wb")},
            &[&ml, &mr, &both, &law],
        );
        Ok(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(scaled[0], scaled[1], "wceq"), "ch" => t!(left, right, "wceq")},
            &[&matched, &turn],
        ))
    }

    /// Closed numerals, worked out and then said. Nothing is taken as
    /// stated: the claim is worked out first, so what cannot be proved is
    /// reported as what it is.
    pub fn arithmetic(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let what = format!("step {} claims {}", fmt(&step.number), step.claim.text());
        self.closed_fact(term, scope, facts, &what, Some(step))
            .map(Built)
    }

    /// A fact about closed numerals, worked out and then proved, wherever it
    /// stands; `what` says where it was asked, as the page writes it.
    pub fn closed_fact(
        &mut self,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        what: &str,
        step: Option<&Step>,
    ) -> Checked<Proof> {
        let said = self.to_term(term);
        // A claim of several sentences, `2 + 2 = 4. 3 + 3 = 6.`, is each of
        // them worked out, as the checker decides each.
        let parts = self.conjoined(&said, scope, &mut |me, one| {
            let one = me.rpn(one);
            me.closed_fact(&one, scope, facts, what, step).map(Built)
        })?;
        if let Some(Built(p)) = parts {
            return Ok(p);
        }
        if let Some(pairs) = pairs::relation(&said) {
            return self.closed_pairs(&pairs, term, scope, facts, what, step);
        }
        if let Built(p) = self.prove_numeral(term, scope, facts)? {
            return Ok(p);
        }
        // A remainder or a product over a range is no atom of the normaliser's:
        // a claim holding one is said of its sides' values.
        if !self.normaliser_opaque(&said) {
            if let Built(p) =
                self.prove_field(step, term, scope, facts, &Lines::new())?
            {
                return Ok(p);
            }
        }
        if let Built(p) = self.by_values(term, scope, facts)? {
            return Ok(p);
        }
        Err(self.unshown(term, what))
    }

    /// Two pairs of closed terms, compared coordinate by coordinate
    /// (`METHODS.md`, Pairs): both coordinates' equations, or the
    /// difference at the first coordinate whose equation is false.
    fn closed_pairs(
        &mut self,
        pairs: &PairRelation,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        what: &str,
        step: Option<&Step>,
    ) -> Checked<Proof> {
        if !pairs.apart {
            let mut proved = Vec::new();
            for at in Coordinate::BOTH {
                let equation = self.rpn(&pairs.equation(at));
                proved.push(self.closed_fact(&equation, scope, facts, what, step)?);
            }
            return Ok(self.pairs_equal(pairs, scope, &proved[0], &proved[1]));
        }
        let Some(at) = pairs.apart_at(&mut closed_equal) else {
            return Err(self.unshown(term, what));
        };
        let denial = self.rpn(&pairs.denial(at));
        let apart = self.closed_fact(&denial, scope, facts, what, step)?;
        let members = self.number_members(pairs, scope, facts)?;
        Ok(self.pairs_apart(pairs, scope, at, &apart, &members))
    }

    /// Whether a term holds what the normaliser holds as an atom where
    /// `arithmetic` works it out: a remainder, a product over a range, or a
    /// power to an exponent below 0.
    pub(super) fn normaliser_opaque(&self, t: &Term) -> bool {
        let said = self.rpn(t);
        said.has("cmo") || said.has("cprod") || negative_power(t)
    }

    /// ( scope -> claim ) for a closed claim, said of its sides' values: each
    /// side is worked to its value written plainly (`closed_valued`), the
    /// claim is proved of the values by the routes above, and the law that
    /// carries an equation through the relation brings it back to the sides
    /// as written (`breq12d`, `eqeq12d`, `eleq1d`). A claim whose sides are
    /// values already is one those routes did not prove.
    fn by_values(
        &mut self,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut goal = self.to_term(term);
        let negated = goal.label() == Some("wn") && goal.children().len() == 1;
        if negated {
            goal = goal.children()[0].clone();
        }
        let kids = goal.children().to_vec();
        let side = |me: &mut Self, t: &Term| me.closed_valued(t, scope, facts);
        let (valued, iff) = match (goal.label(), kids.as_slice()) {
            (Some("wcel"), [x, set]) => {
                let (_, cx, px) = take!(side(self, x)?);
                let (sx, ss) = (self.rpn(x), self.rpn(set));
                let iff = self.b.ap(
                    "eleq1d",
                    &binds! {"ph" => scope, "A" => &sx, "B" => &cx, "C" => &ss},
                    &[&px],
                );
                (t!(&cx, &ss, "wcel"), iff)
            }
            (Some("wceq"), [a, b]) => {
                let (_, ca, pa) = take!(side(self, a)?);
                let (_, cb, pb) = take!(side(self, b)?);
                let iff = self.b.ap(
                    "eqeq12d",
                    &binds! {"ph" => scope, "A" => self.rpn(a), "B" => &ca, "C" => self.rpn(b), "D" => &cb},
                    &[&pa, &pb],
                );
                (t!(&ca, &cb, "wceq"), iff)
            }
            (Some("wbr"), [a, b, relation]) => {
                let (_, ca, pa) = take!(side(self, a)?);
                let (_, cb, pb) = take!(side(self, b)?);
                let r = self.rpn(relation);
                let iff = self.b.ap(
                    "breq12d",
                    &binds! {"ph" => scope, "A" => self.rpn(a), "B" => &ca, "C" => self.rpn(b), "D" => &cb, "R" => &r},
                    &[&pa, &pb],
                );
                (t!(&ca, &cb, &r, "wbr"), iff)
            }
            _ => return Ok(Route::no("not a relation of closed terms")),
        };
        let said = self.rpn(&goal);
        if valued == said {
            return Ok(Route::no("its sides are their values already"));
        }
        let at = self.denied_if(Revalued { said, valued, iff }, negated, scope);
        let held = match self.prove_numeral(&at.valued, scope, facts)? {
            Built(p) => p,
            Declined(_) => {
                take!(self.prove_field(
                    None,
                    &at.valued,
                    scope,
                    facts,
                    &Lines::new()
                )?)
            }
        };
        Ok(Built(self.carried_back(&at, &held, scope)))
    }

    /// The same of the two claims' denials, where `negated` (`notbid`).
    pub(super) fn denied_if(
        &self,
        at: Revalued,
        negated: bool,
        scope: &Rpn,
    ) -> Revalued {
        if !negated {
            return at;
        }
        let iff = self.b.ap(
            "notbid",
            &binds! {"ph" => scope, "ps" => &at.said, "ch" => &at.valued},
            &[&at.iff],
        );
        Revalued {
            said: t!(&at.said, "wn"),
            valued: t!(&at.valued, "wn"),
            iff,
        }
    }

    /// ( scope -> said ) from ( scope -> valued ), `held` (`mpbird`).
    pub(super) fn carried_back(
        &self,
        at: &Revalued,
        held: &Proof,
        scope: &Rpn,
    ) -> Proof {
        self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &at.said, "ch" => &at.valued},
            &[held, &at.iff],
        )
    }

    /// ( scope -> -. x e. S ) for a closed x whose value v is no whole
    /// number, and S one of ℤ, ℕ and ℕ₀: v lies strictly between the whole
    /// number below it and the next (`btwnnz`), so x is not in ℤ, and ℕ and
    /// ℕ₀ lie in ℤ (`nnz`, `nn0z`).
    fn not_whole(
        &mut self,
        member: &Term,
        v: &Q,
        system: Option<&str>,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let lift = match system {
            Some("cz") => None,
            Some("cn") => Some("nnz"),
            Some("cn0") => Some("nn0z"),
            _ => return Ok(Route::no("a non-membership of a system a fraction is in")),
        };
        let floor = v.floor().to_integer();
        let low = numerals::spell_integer(&floor);
        let sm = self.rpn(member);
        let next = t!(&low, "c1", "caddc", "co");
        let closed = |me: &mut Self, claim: Rpn| -> Checked<Route<Proof>> {
            Ok(match me.prove_numeral(&claim, scope, facts)? {
                Built(p) => Built(p),
                Declined(_) => me.by_values(&claim, scope, facts)?,
            })
        };
        let whole = take!(closed(self, t!(&low, "cz", "wcel"))?);
        let above = take!(closed(self, t!(&low, &sm, "clt", "wbr"))?);
        let below = take!(closed(self, t!(&sm, &next, "clt", "wbr"))?);
        let law = self.b.ap("btwnnz", &binds! {"A" => &low, "B" => &sm}, &[]);
        let not_integer = self.b.ap(
            "syl3anc",
            &binds! {"ph" => scope, "ps" => t!(&low, "cz", "wcel"), "ch" => t!(&low, &sm, "clt", "wbr"),
            "th" => t!(&sm, &next, "clt", "wbr"), "ta" => t!(t!(&sm, "cz", "wcel"), "wn")},
            &[&whole, &above, &below, &law],
        );
        let Some(lift) = lift else {
            return Ok(Built(not_integer));
        };
        let set = system.unwrap_or_default();
        let lift = self.b.ap(lift, &binds! {"N" => &sm}, &[]);
        let lift = pf!(self.b; t!(t!(&sm, set, "wcel"), t!(&sm, "cz", "wcel"), "wi"), scope, lift, "a1i");
        Ok(Built(self.b.ap(
            "mtod",
            &binds! {"ph" => scope, "ps" => t!(&sm, set, "wcel"), "ch" => t!(&sm, "cz", "wcel")},
            &[&not_integer, &lift],
        )))
    }

    /// ( scope -> t = v ) for a closed term t, with its value and v: the
    /// value written plainly, a numeral, its negation, a fraction of two
    /// numerals or the negation of one. The normaliser works out sums,
    /// differences, products, quotients and whole powers (`prove_field`); a
    /// remainder and a product over a range it holds as an atom, so each is
    /// worked first (`numerals::worked`), from the inside out, and carried up
    /// through the operations above it (`oveq12d`, `negeqd`).
    pub(super) fn closed_valued(
        &mut self,
        t: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<(Q, Rpn, Proof)>> {
        let Built(Value::Exact(v)) = field::closed_value(t) else {
            return Ok(Route::no("it has no exact value"));
        };
        let plain = |n: &BigInt| numerals::spell(n.magnitude().clone());
        let body = if v.is_integer() {
            plain(v.numer())
        } else {
            t!(plain(v.numer()), plain(v.denom()), DIV, "co")
        };
        let canon = if v.is_negative() {
            t!(body, "cneg")
        } else {
            body
        };
        let said = self.rpn(t);
        if said == canon {
            let same = self
                .b
                .ap("eqidd", &binds! {"ph" => scope, "A" => &said}, &[]);
            return Ok(Built((v, canon, same)));
        }
        let labels = self.b.flabel.clone();
        let lifted = |me: &Self, is: Proof, from: &Rpn| pf!(me.b; t!(from, &canon, "wceq"), scope, is, "a1i");
        // The term whole, where the normaliser reaches it; else part by part.
        if !self.normaliser_opaque(t) {
            if let Built(equal) = self.prove_field(
                None,
                &t!(&said, &canon, "wceq"),
                scope,
                facts,
                &Lines::new(),
            )? {
                return Ok(Built((v, canon, equal)));
            }
        }
        if let Some((_, is)) = numerals::worked(&self.b, t, &labels) {
            return Ok(Built((v, canon.clone(), lifted(self, is, &said))));
        }
        let kids = t.children().to_vec();
        let (moved, middle) = match (t.label(), kids.as_slice()) {
            (Some("co"), [x, y, op]) => {
                let (_, cx, px) = take!(self.closed_valued(x, scope, facts)?);
                let (_, cy, py) = take!(self.closed_valued(y, scope, facts)?);
                let op = self.rpn(op);
                let moved = self.b.ap(
                    "oveq12d",
                    &binds! {"ph" => scope, "A" => self.rpn(x), "B" => &cx, "C" => self.rpn(y), "D" => &cy, "F" => &op},
                    &[&px, &py],
                );
                (moved, t!(&cx, &cy, &op, "co"))
            }
            (Some("cneg"), [x]) => {
                let (_, cx, px) = take!(self.closed_valued(x, scope, facts)?);
                let moved = self.b.ap(
                    "negeqd",
                    &binds! {"ph" => scope, "A" => self.rpn(x), "B" => &cx},
                    &[&px],
                );
                (moved, t!(&cx, "cneg"))
            }
            _ => return Ok(Route::no("an operation its value is not carried through")),
        };
        // What is left is an operation on values: a remainder of two whole
        // numbers is worked, a division by a value below 0 is the negation
        // of one by its opposite (`divneg2d`), and anything else is the
        // normaliser's.
        let field = |me: &mut Self, from: &Rpn| {
            me.prove_field(None, &t!(from, &canon, "wceq"), scope, facts, &Lines::new())
        };
        let middle_term = self.to_term(&middle);
        let by_negative = match (middle_term.label(), middle_term.children()) {
            (Some("co"), [x, y, op])
                if op.label() == Some(DIV) && y.label() == Some("cneg") =>
            {
                Some((self.rpn(x), self.rpn(&y.children()[0])))
            }
            _ => None,
        };
        // A power to −n is one over the power to n (`expnegd`), which the
        // normaliser multiplies out.
        let by_reciprocal = match (middle_term.label(), middle_term.children()) {
            (Some("co"), [x, y, op])
                if op.label() == Some(field::EXP) && y.label() == Some("cneg") =>
            {
                Some((self.rpn(x), self.rpn(&y.children()[0])))
            }
            _ => None,
        };
        let rest = match (
            numerals::worked(&self.b, &middle_term, &labels),
            by_negative,
            by_reciprocal,
        ) {
            (Some((_, is)), _, _) => lifted(self, is, &middle),
            (None, None, Some((base, n))) => {
                let goal = self.to_term(&t!(&base, "cc", "wcel"));
                let base_cc = take!(self.numeral_within(&goal, scope, facts)?);
                let apart = self.not_zero(scope, facts, &base)?;
                let goal = self.to_term(&t!(&n, "cz", "wcel"));
                let n_z = take!(self.numeral_within(&goal, scope, facts)?);
                let turned = self.b.ap(
                    "expnegd",
                    &binds! {"ph" => scope, "A" => &base, "N" => &n},
                    &[&base_cc, &apart, &n_z],
                );
                let over = t!("c1", t!(&base, &n, field::EXP, "co"), DIV, "co");
                let valued = take!(field(self, &over)?);
                self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &middle, "B" => &over, "C" => &canon},
                    &[&turned, &valued],
                )
            }
            (None, Some((top, bottom)), _) => {
                let within = |me: &mut Self, s: &Rpn| {
                    let goal = me.to_term(&t!(s, "cc", "wcel"));
                    me.numeral_within(&goal, scope, facts)
                };
                let top_cc = take!(within(self, &top)?);
                let bottom_cc = take!(within(self, &bottom)?);
                let apart = self.not_zero(scope, facts, &bottom)?;
                let moved_in = self.b.ap(
                    "divneg2d",
                    &binds! {"ph" => scope, "A" => &top, "B" => &bottom},
                    &[&top_cc, &bottom_cc, &apart],
                );
                let negated = t!(t!(&top, &bottom, DIV, "co"), "cneg");
                let turned = self.b.ap(
                    "eqcomd",
                    &binds! {"ph" => scope, "A" => &negated, "B" => &middle},
                    &[&moved_in],
                );
                let valued = take!(field(self, &negated)?);
                self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &middle, "B" => &negated, "C" => &canon},
                    &[&turned, &valued],
                )
            }
            (None, None, None) => take!(field(self, &middle)?),
        };
        let joined = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &said, "B" => &middle, "C" => &canon},
            &[&moved, &rest],
        );
        Ok(Built((v, canon, joined)))
    }

    /// The defect for a claim `arithmetic` could not prove: it is never taken
    /// as stated instead.
    pub fn unshown(&self, term: &Rpn, what: &str) -> Problem {
        match field::decide_closed(&self.to_term(term)) {
            Declined(_) => self.defect(
                self.at,
                format!("{what}, which is not a fact about numerals alone, and arithmetic decides nothing else"),
            ),
            Built(Verdict::Holds(false)) => {
                self.defect(self.at, format!("{what}, which is false"))
            }
            Built(Verdict::Unworked(why)) => {
                self.defect(self.at, format!("{what}, which {why}"))
            }
            Built(Verdict::Holds(true)) => self.defect(
                self.at,
                format!("{what}, which is true, and arithmetic cannot show it yet; cite a theorem that states it"),
            ),
        }
    }

    /// A closed numeral fact, decided by working it out and then said: that
    /// one number is below another is what set.mm names for every pair, and
    /// everything else is that weakened or turned.
    pub fn prove_numeral(
        &mut self,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut goal = self.to_term(term);
        // set.mm's other spelling of a disequation, A =/= B, is the page's
        // ¬ (A = B) proved and turned (`neqned`).
        if goal.variable().is_none()
            && goal.label() == Some("wne")
            && goal.children().len() == 2
        {
            let (a, b) = (self.rpn(&goal.children()[0]), self.rpn(&goal.children()[1]));
            let denied = t!(t!(&a, &b, "wceq"), "wn");
            let proof = take!(self.prove_numeral(&denied, scope, facts)?);
            return Ok(Built(self.b.ap(
                "neqned",
                &binds! {"ph" => scope, "A" => &a, "B" => &b},
                &[&proof],
            )));
        }
        let mut negated = false;
        if goal.variable().is_none()
            && goal.label() == Some("wn")
            && goal.children().len() == 1
        {
            negated = true;
            goal = goal.children()[0].clone();
        }
        // Belonging to a number system is the other thing a claim with no
        // atom can say.
        if !negated
            && goal.variable().is_none()
            && goal.label() == Some("wcel")
            && goal.children().len() == 2
        {
            return self.numeral_within(&goal, scope, facts);
        }
        // A divisibility, which is what "is even" and "is odd" are too, where
        // the word's record says `arithmetic` decides it.
        if goal.variable().is_none()
            && goal.label() == Some("wbr")
            && goal.children().len() == 3
            && goal.children()[2].label() == Some("cdvds")
        {
            let whole = if negated {
                Term::apply("wn", vec![goal.clone()])
            } else {
                goal.clone()
            };
            if !self.decided_by("arithmetic", &whole)? {
                return Ok(Route::no(
                    "no record of a word says arithmetic decides this divisibility",
                ));
            }
            return self.divides_proved(&goal, negated, scope, facts);
        }
        // Not in ℕ₀ for a value below 0, whose members are at least 0
        // (`nn0ge0`); not in ℕ for one at most 0, whose members are above it
        // (`nngt0`).
        if negated
            && goal.variable().is_none()
            && goal.label() == Some("wcel")
            && goal.children().len() == 2
        {
            let (member, system) = (&goal.children()[0], goal.children()[1].label());
            if let Built(Value::Exact(v)) = field::closed_value(member) {
                if !v.is_integer() {
                    return self.not_whole(member, &v, system, scope, facts);
                }
            }
            let (how, law) = match system {
                Some("cn0") => ("<=", "nn0ge0"),
                Some("cn") => ("<", "nngt0"),
                _ => {
                    return Ok(Route::no(
                        "a non-membership of a system other than ℕ or ℕ₀",
                    ))
                }
            };
            let zero = Term::apply("cc0", Vec::new());
            let below = take!(
                self.order_by_difference(&zero, member, how, true, scope, facts)?
            );
            let m = self.rpn(member);
            let relation = if how == "<" { "clt" } else { "cle" };
            let held = t!("cc0", &m, relation, "wbr");
            let law = self.b.ap(law, &binds! {"N" => &m, "A" => &m}, &[]);
            let law = self.b.ap(
                "a1i",
                &binds! {"ph" => t!(self.rpn(&goal), &held, "wi"), "ps" => scope},
                &[&law],
            );
            return Ok(Built(self.b.ap(
                "mtod",
                &binds! {"ph" => scope, "ps" => self.rpn(&goal), "ch" => &held},
                &[&below, &law],
            )));
        }
        let Some((first, second, how)) = order_sides(&goal) else {
            return Ok(Route::no("the claim states no relation"));
        };
        let (Some(a), Some(b)) = (numerals::value(&first), numerals::value(&second))
        else {
            // An equation of whole numbers each side works out to, a
            // remainder among them, is the two worked out and joined
            // (`eqtr4i`).
            if how == "=" && !negated {
                let labels = self.b.flabel.clone();
                if let (Some((a, a_is)), Some((b, b_is))) = (
                    numerals::worked(&self.b, &first, &labels),
                    numerals::worked(&self.b, &second, &labels),
                ) {
                    if a == b {
                        let (sf, ss) = (self.rpn(&first), self.rpn(&second));
                        let joined = self.b.ap(
                            "eqtr4i",
                            &binds! {"A" => &sf, "B" => numerals::spell(a), "C" => &ss},
                            &[&a_is, &b_is],
                        );
                        return Ok(Built(self.b.ap(
                            "a1i",
                            &binds! {"ph" => t!(sf, ss, "wceq"), "ps" => scope},
                            &[&joined],
                        )));
                    }
                }
            }
            // A disequation with a side below 0 is the lower below the
            // higher (`order_by_difference`), and so apart (`ltne`).
            let below_zero = |side: &Term| matches!(field::closed_value(side), Built(Value::Exact(v)) if v.is_negative());
            if how == "=" && negated && (below_zero(&first) || below_zero(&second)) {
                return self.closed_apart(&first, &second, scope, facts);
            }
            // A disequation of whole numbers each side works out to is the
            // two values apart, carried to the sides as written (`eqeq12i`).
            if how == "=" && negated {
                let labels = self.b.flabel.clone();
                if let (Some((a, a_is)), Some((b, b_is))) = (
                    numerals::worked(&self.b, &first, &labels),
                    numerals::worked(&self.b, &second, &labels),
                ) {
                    if a != b {
                        let apart = self.numerals_differ(scope, &a, &b);
                        let (sf, ss) = (self.rpn(&first), self.rpn(&second));
                        let (na, nb) = (numerals::spell(a), numerals::spell(b));
                        let same = self.b.ap(
                            "eqeq12i",
                            &binds! {"A" => &sf, "B" => &na, "C" => &ss, "D" => &nb},
                            &[&a_is, &b_is],
                        );
                        let (said, valued) =
                            (t!(&sf, &ss, "wceq"), t!(&na, &nb, "wceq"));
                        let turned = self.b.ap(
                            "notbii",
                            &binds! {"ph" => &said, "ps" => &valued},
                            &[&same],
                        );
                        return Ok(Built(self.b.ap(
                            "sylibr",
                            &binds! {"ph" => scope, "ps" => t!(valued, "wn"), "ch" => t!(said, "wn")},
                            &[&apart, &turned],
                        )));
                    }
                }
            }
            // A disequation of sides that are not both whole numbers, a
            // fraction among them, is the lower below the higher too.
            if how == "=" && negated {
                return self.closed_apart(&first, &second, scope, facts);
            }
            // An equation is the normaliser's, which works fractions too.
            if how == "=" {
                return Ok(Route::no(
                    "a side works out to a whole number but is one only after working out",
                ));
            }
            return self
                .order_by_values(&goal, &first, &second, how, negated, scope, facts);
        };
        let (na, nb) = (numerals::spell(a.clone()), numerals::spell(b.clone()));
        let (na, nb) = (&na, &nb);
        if negated {
            return Ok(match how {
                "=" if a != b => Built(self.numerals_differ(scope, &a, &b)),
                // not a ≤ b is b < a, and not a < b is b ≤ a, each turned by
                // the law that says so (`ltnled`, `lenltd`).
                "<=" if b < a => {
                    let below = self.numeral_below(scope, &b, &a);
                    let below = self.numerals_ordered(scope, nb, na, below);
                    Built(self.denied(scope, nb, na, &below, true))
                }
                "<" if b <= a => {
                    let held = take!(self.prove_numeral(
                        &t!(nb, na, "cle", "wbr"),
                        scope,
                        facts
                    )?);
                    let held = self.numerals_ordered(scope, nb, na, held);
                    Built(self.denied(scope, nb, na, &held, false))
                }
                _ => Route::no("a denial of what holds"),
            });
        }
        if how == "=" && a == b {
            let same = self.b.ap("eqid", &binds! {"A" => na}, &[]);
            return Ok(Built(self.b.ap(
                "a1i",
                &binds! {"ph" => t!(na, nb, "wceq"), "ps" => scope},
                &[&same],
            )));
        }
        if how == "<" && a < b {
            return Ok(Built(self.numeral_below(scope, &a, &b)));
        }
        if how == "<=" && a <= b {
            if a == b {
                let real = self.real_numeral(scope, &Q::from_integer(a.clone().into()));
                let law = self.b.ap("leid", &binds! {"A" => na}, &[]);
                return Ok(Built(self.b.ap(
                    "syl",
                    &binds! {"ph" => scope, "ps" => t!(na, "cr", "wcel"), "ch" => t!(na, na, "cle", "wbr")},
                    &[&real, &law],
                )));
            }
            let below = self.numeral_below(scope, &a, &b);
            let ra = self.real_numeral(scope, &Q::from_integer(a.clone().into()));
            let rb = self.real_numeral(scope, &Q::from_integer(b.clone().into()));
            let law = self.b.ap("ltle", &binds! {"A" => na, "B" => nb}, &[]);
            let weaken = self.b.ap(
                "syl2anc",
                &binds! {"ph" => scope, "ps" => t!(na, "cr", "wcel"), "ch" => t!(nb, "cr", "wcel"),
                "th" => t!(t!(na, nb, "clt", "wbr"), t!(na, nb, "cle", "wbr"), "wi")},
                &[&ra, &rb, &law],
            );
            return Ok(Built(self.b.ap(
                "mpd",
                &binds! {"ph" => scope, "ps" => t!(na, nb, "clt", "wbr"), "ch" => t!(na, nb, "cle", "wbr")},
                &[&below, &weaken],
            )));
        }
        Ok(Route::no(format!(
            "{a} {how} {b} is not what the numbers do"
        )))
    }

    /// Whether the word `claim` says, or for a denial the word it denies, is
    /// one whose record names `method` in its `decided` field
    /// (`DATABASE.md`). Each such record's `then` line is read in its own
    /// sorts, and the kernel form of what it defines, its letters standing
    /// for any term, is fitted to the claim.
    pub fn decided_by(&mut self, method: &str, claim: &Term) -> Checked<bool> {
        if !self.decided.contains_key(method) {
            let records = self.records;
            let mut words = Vec::new();
            for r in records {
                if r.kind != RecordKind::Definition || !field::decides(r, method) {
                    continue;
                }
                // Each letter the word is said of stands for a set variable's
                // class, which `fits_word` lets any term fill.
                let hole = t!(self.spare[0], "cv");
                let said =
                    self.in_its_names(Item::Record(r), |me| -> Checked<Rpn> {
                        me.names_kept(|me| {
                            let node = me.read_one(&r.stated()[0])?;
                            let left = node.children[0].clone();
                            for name in left.names() {
                                me.names.insert(name, hole.clone());
                            }
                            me.term(&left)
                        })
                    })?;
                words.push(self.to_term(&said));
            }
            self.decided.insert(method.to_string(), words);
        }
        let mut forms = vec![claim.clone()];
        if claim.label() == Some("wn") && claim.children().len() == 1 {
            forms.push(claim.children()[0].clone());
        }
        Ok(self.decided[method]
            .iter()
            .any(|word| forms.iter().any(|f| fits_word(word, f))))
    }

    /// ( scope -> d ∥ n ), or its denial where `negated`, for closed d and n
    /// that work out to whole numbers, d at least 1 (`METHODS.md`,
    /// arithmetic): at their values by `dvdsmul1` at the quotient, or by
    /// `ndvdsi` from the quotient and the remainder, and carried back to the
    /// terms as written by `breq12i`. A decline where the sides do not work
    /// out so, or where what is asked is not what the numbers do.
    pub fn numeral_divides(
        &self,
        core: &Term,
        negated: bool,
        scope: &Rpn,
    ) -> Route<Proof> {
        let labels = self.b.flabel.clone();
        let kids = core.children();
        let (Some((d, d_is)), Some((num, n_is))) = (
            numerals::worked(&self.b, &kids[0], &labels),
            numerals::worked(&self.b, &kids[1], &labels),
        ) else {
            return Route::no(
                "a side of the divisibility is not a whole number worked out",
            );
        };
        if d.is_zero() {
            return Route::no("a divisor of 0");
        }
        if (&num % &d).is_zero() == negated {
            return Route::no("a divisibility that is not what the numbers do");
        }
        let (sd, sn) = (numerals::spell(d.clone()), numerals::spell(num.clone()));
        let at_values = t!(sd, sn, "cdvds", "wbr");
        let shown = self.divides_at_values(&d, &num);
        let said = |t: Rpn| if negated { t!(t, "wn") } else { t };
        let (written, at) = (said(self.rpn(core)), said(at_values.clone()));
        let closed = if written == at {
            shown
        } else {
            let (rd, rn) = (self.rpn(&kids[0]), self.rpn(&kids[1]));
            let mut same = self.b.ap(
                "breq12i",
                &binds! {"A" => &rd, "B" => &sd, "C" => &rn, "D" => &sn, "R" => "cdvds"},
                &[&d_is, &n_is],
            );
            if negated {
                same = self.b.ap(
                    "notbii",
                    &binds! {"ph" => self.rpn(core), "ps" => &at_values},
                    &[&same],
                );
            }
            self.b.ap(
                "mpbir",
                &binds! {"ph" => &written, "ps" => &at},
                &[&shown, &same],
            )
        };
        Built(
            self.b
                .ap("a1i", &binds! {"ph" => &written, "ps" => scope}, &[&closed]),
        )
    }

    /// |- d ∥ n where d divides n, and |- -. d ∥ n where it does not, d at
    /// least 1, each spelt as `numerals::spell` spells them: by `dvdsmul1`
    /// at the quotient, or by `ndvdsi` from the quotient and the remainder.
    pub fn divides_at_values(&self, d: &BigUint, num: &BigUint) -> Proof {
        let (quotient, rest) = (num / d, num % d);
        let negated = !rest.is_zero();
        let (sd, sn, sq) = (
            numerals::spell(d.clone()),
            numerals::spell(num.clone()),
            numerals::spell(quotient.clone()),
        );
        let times = t!(sd, sq, "cmul", "co");
        let product = numerals::product(&self.b, d.clone(), quotient.clone());
        if negated {
            // n = d·q + r with 0 < r < d.
            let sr = numerals::spell(rest.clone());
            let sp = numerals::spell(d * &quotient);
            let moved = self.b.ap(
                "oveq1i",
                &binds! {"A" => &times, "B" => &sp, "C" => &sr, "F" => "caddc"},
                &[&product],
            );
            let total = self.b.ap(
                "eqtri",
                &binds! {"A" => t!(times, sr, "caddc", "co"), "B" => t!(sp, sr, "caddc", "co"), "C" => &sn},
                &[&moved, &numerals::sum(&self.b, d * &quotient, rest.clone())],
            );
            self.b.ap(
                "ndvdsi",
                &binds! {"A" => &sd, "B" => &sn, "Q" => &sq, "R" => &sr},
                &[
                    &numerals::nn(&self.b, d.clone()),
                    &numerals::nn0(&self.b, quotient.clone()),
                    &numerals::nn(&self.b, rest.clone()),
                    &total,
                    &numerals::below(&self.b, rest.clone(), d.clone()),
                ],
            )
        } else {
            let whole_d = self.b.ap(
                "nnzi",
                &binds! {"N" => &sd},
                &[&numerals::nn(&self.b, d.clone())],
            );
            let whole_q = self.b.ap(
                "nn0zi",
                &binds! {"N" => &sq},
                &[&numerals::nn0(&self.b, quotient.clone())],
            );
            let law = self.b.ap("dvdsmul1", &binds! {"M" => &sd, "N" => &sq}, &[]);
            let held = self.b.ap(
                "mp2an",
                &binds! {"ph" => t!(sd, "cz", "wcel"), "ps" => t!(sq, "cz", "wcel"),
                "ch" => t!(sd, times, "cdvds", "wbr")},
                &[&whole_d, &whole_q, &law],
            );
            self.b.ap(
                "breqtri",
                &binds! {"A" => &sd, "R" => "cdvds", "B" => &times, "C" => &sn},
                &[&held, &product],
            )
        }
    }

    /// ( scope -> d ∥ n ), or its denial where `negated`, for closed d and n
    /// that work out to integers, d not 0. Where both work out to whole
    /// numbers it is `numeral_divides`. Otherwise it is that at their sizes,
    /// the signs turned by `dvdsnegb` and `negdvdsb`, each of which says a
    /// divisibility holds exactly where it does with a side negated, and
    /// carried back to the terms as written by `breq12d`.
    pub fn divides_proved(
        &mut self,
        core: &Term,
        negated: bool,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let kids = core.children().to_vec();
        let whole = kids[..2]
            .iter()
            .all(|side| numerals::worked(&self.b, side, &labels).is_some());
        if whole {
            return Ok(self.numeral_divides(core, negated, scope));
        }
        let (d, vd, d_is) = take!(self.closed_valued(&kids[0], scope, facts)?);
        let (n, vn, n_is) = take!(self.closed_valued(&kids[1], scope, facts)?);
        if !d.is_integer() || !n.is_integer() || d.is_zero() {
            return Ok(Route::no("a side of the divisibility is not an integer"));
        }
        let (a, b) = (
            d.to_integer().magnitude().clone(),
            n.to_integer().magnitude().clone(),
        );
        let (sa, sb) = (numerals::spell(a.clone()), numerals::spell(b.clone()));
        let sizes = t!(sa, sb, "cdvds", "wbr");
        let at_sizes =
            take!(self.numeral_divides(&self.to_term(&sizes), negated, scope));
        // |- ( a ∥ b <-> vd ∥ vn ), a sign turned at a time.
        let za = self.b.ap(
            "nnzi",
            &binds! {"N" => &sa},
            &[&numerals::nn(&self.b, a.clone())],
        );
        let zb = self.b.ap(
            "nn0zi",
            &binds! {"N" => &sb},
            &[&numerals::nn0(&self.b, b.clone())],
        );
        let mut number = sb.clone();
        let mut number_z = zb;
        // Where the turns have reached, and |- ( a ∥ b <-> that ), each turn
        // chained onto the last by `bitri`.
        let mut turned: Option<(Rpn, Proof)> = None;
        let chain = |me: &Self, turned: Option<(Rpn, Proof)>, to: Rpn, iff: Proof| {
            Some(match turned {
                None => (to, iff),
                Some((was, before)) => {
                    let chained = me.b.ap(
                        "bitri",
                        &binds! {"ph" => &sizes, "ps" => &was, "ch" => &to},
                        &[&before, &iff],
                    );
                    (to, chained)
                }
            })
        };
        if n.is_negative() {
            let to = t!(sa, t!(sb, "cneg"), "cdvds", "wbr");
            let law = self.b.ap("dvdsnegb", &binds! {"M" => &sa, "N" => &sb}, &[]);
            let iff = self.b.ap(
                "mp2an",
                &binds! {"ph" => t!(sa, "cz", "wcel"), "ps" => t!(sb, "cz", "wcel"),
                "ch" => t!(&sizes, &to, "wb")},
                &[&za, &number_z, &law],
            );
            turned = chain(self, turned, to, iff);
            let negz = self.b.ap("znegcl", &binds! {"N" => &sb}, &[]);
            number_z = self.b.ap(
                "ax-mp",
                &binds! {"ph" => t!(sb, "cz", "wcel"), "ps" => t!(t!(sb, "cneg"), "cz", "wcel")},
                &[&number_z, &negz],
            );
            number = t!(sb, "cneg");
        }
        if d.is_negative() {
            let from = t!(sa, &number, "cdvds", "wbr");
            let to = t!(t!(sa, "cneg"), &number, "cdvds", "wbr");
            let law = self
                .b
                .ap("negdvdsb", &binds! {"M" => &sa, "N" => &number}, &[]);
            let iff = self.b.ap(
                "mp2an",
                &binds! {"ph" => t!(sa, "cz", "wcel"), "ps" => t!(&number, "cz", "wcel"),
                "ch" => t!(&from, &to, "wb")},
                &[&za, &number_z, &law],
            );
            turned = chain(self, turned, to, iff);
        }
        let Some((at_values, mut iff)) = turned else {
            return Ok(Route::no(
                "a divisibility of whole numbers is `numeral_divides`",
            ));
        };
        if at_values != t!(vd, vn, "cdvds", "wbr") {
            return Ok(Route::no("the values are not spelt as their sizes turned"));
        }
        let (mut before, mut after) = (sizes.clone(), at_values.clone());
        if negated {
            iff =
                self.b
                    .ap("notbii", &binds! {"ph" => &before, "ps" => &after}, &[&iff]);
            before = t!(before, "wn");
            after = t!(after, "wn");
        }
        let at_signs = self.b.ap(
            "sylib",
            &binds! {"ph" => scope, "ps" => &before, "ch" => &after},
            &[&at_sizes, &iff],
        );
        let written = self.rpn(core);
        let mut same = self.b.ap(
            "breq12d",
            &binds! {"ph" => scope, "A" => self.rpn(&kids[0]), "B" => &vd,
            "C" => self.rpn(&kids[1]), "D" => &vn, "R" => "cdvds"},
            &[&d_is, &n_is],
        );
        let claim = if negated {
            same = self.b.ap(
                "notbid",
                &binds! {"ph" => scope, "ps" => &written, "ch" => &at_values},
                &[&same],
            );
            t!(written, "wn")
        } else {
            written
        };
        Ok(Built(self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &claim, "ch" => &after},
            &[&at_signs, &same],
        )))
    }

    /// A side as a fraction of two numerals, the second not zero, with
    /// |- side = ( over / under ): a quotient has each part worked
    /// (`numerals::worked`), and a whole number w is w/1 (`div1i`).
    fn as_fraction(&self, side: &Term) -> Option<(BigUint, BigUint, Proof)> {
        let labels = self.b.flabel.clone();
        let kids = side.children();
        if side.variable().is_none()
            && side.label() == Some("co")
            && kids.len() == 3
            && kids[2].label() == Some("cdiv")
        {
            let (over, over_is) = numerals::worked(&self.b, &kids[0], &labels)?;
            let (under, under_is) = numerals::worked(&self.b, &kids[1], &labels)?;
            if under.is_zero() {
                return None;
            }
            let proof = self.b.ap(
                "oveq12i",
                &binds! {
                    "A" => self.rpn(&kids[0]), "B" => numerals::spell(over.clone()),
                    "C" => self.rpn(&kids[1]), "D" => numerals::spell(under.clone()),
                    "F" => "cdiv",
                },
                &[&over_is, &under_is],
            );
            return Some((over, under, proof));
        }
        let (whole, whole_is) = numerals::worked(&self.b, side, &labels)?;
        let sw = numerals::spell(whole.clone());
        let over_one = t!(&sw, n(1), "cdiv", "co");
        let one = self.b.ap(
            "div1i",
            &binds! {"A" => &sw},
            &[&numerals::cc(&self.b, whole.clone())],
        );
        let back = self
            .b
            .ap("eqcomi", &binds! {"A" => &over_one, "B" => &sw}, &[&one]);
        let proof = self.b.ap(
            "eqtri",
            &binds! {"A" => self.rpn(side), "B" => &sw, "C" => &over_one},
            &[&whole_is, &back],
        );
        Some((whole, BigUint::from(1u32), proof))
    }

    /// |- first R second, R being < or ≤, where the sides are fractions of
    /// whole numbers: A/D < C/B is A·B < C·D for positive B and D
    /// (`lt2mul2div`), and A/D ≤ C/B is that C/B < A/D does not hold
    /// (`lenlt`). None where a side is no such fraction or the order is not
    /// what the numbers do.
    fn fractions_ordered(
        &self,
        goal: &Term,
        first: &Term,
        second: &Term,
        how: &str,
    ) -> Option<Proof> {
        let (a, d, first_is) = self.as_fraction(first)?;
        let (c, b, second_is) = self.as_fraction(second)?;
        let sp = |v: &BigUint| numerals::spell(v.clone());
        let (sa, sb, sc, sd) = (sp(&a), sp(&b), sp(&c), sp(&d));
        let (p, q) = (&a * &b, &c * &d);
        let (ab, cd) = (t!(&sa, &sb, "cmul", "co"), t!(&sc, &sd, "cmul", "co"));
        let (ad, cb) = (t!(&sa, &sd, "cdiv", "co"), t!(&sc, &sb, "cdiv", "co"));
        let (ab_is, cd_is) = (
            numerals::product(&self.b, a.clone(), b.clone()),
            numerals::product(&self.b, c.clone(), d.clone()),
        );
        let real = |v: &BigUint| numerals::re(&self.b, v.clone());
        let and = |x: &Rpn, y: &Rpn, px: &Proof, py: &Proof| {
            self.b
                .ap("pm3.2i", &binds! {"ph" => x, "ps" => y}, &[px, py])
        };
        // ( x e. RR /\ ( y e. RR /\ 0 < y ) ), y positive.
        let held = |x: &BigUint, y: &BigUint| {
            let (sx, sy) = (sp(x), sp(y));
            let positive =
                t!(t!(&sy, "cr", "wcel"), t!("cc0", &sy, "clt", "wbr"), "wa");
            let inner = and(
                &t!(&sy, "cr", "wcel"),
                &t!("cc0", &sy, "clt", "wbr"),
                &real(y),
                &numerals::pos(&self.b, y.clone()),
            );
            (
                t!(t!(&sx, "cr", "wcel"), &positive, "wa"),
                and(&t!(&sx, "cr", "wcel"), &positive, &real(x), &inner),
            )
        };
        // ( ( A x. B ) < ( C x. D ) <-> ( A / D ) < ( C / B ) ), and the
        // same with the two fractions exchanged.
        let crossed = |x: &BigUint, y: &BigUint, z: &BigUint, w: &BigUint| {
            let (left, left_held) = held(x, y);
            let (right, right_held) = held(z, w);
            let both = and(&left, &right, &left_held, &right_held);
            let law = self.b.ap(
                "lt2mul2div",
                &binds! {"A" => sp(x), "B" => sp(y), "C" => sp(z), "D" => sp(w)},
                &[],
            );
            let lt = |l: Rpn, r: Rpn| t!(l, r, "clt", "wbr");
            self.b.ap(
                "ax-mp",
                &binds! {
                    "ph" => t!(&left, &right, "wa"),
                    "ps" => t!(
                        lt(t!(sp(x), sp(y), "cmul", "co"), t!(sp(z), sp(w), "cmul", "co")),
                        lt(t!(sp(x), sp(w), "cdiv", "co"), t!(sp(z), sp(y), "cdiv", "co")),
                        "wb"
                    ),
                },
                &[&both, &law],
            )
        };
        let (sp_, sq) = (sp(&p), sp(&q));
        let relation = if how == "<" { "clt" } else { "cle" };
        let between = if how == "<" {
            if p >= q {
                return None;
            }
            // A·B < C·D, from the numerals they come to.
            let valued = self.b.ap(
                "breq12i",
                &binds! {"A" => &ab, "B" => &sp_, "C" => &cd, "D" => &sq, "R" => "clt"},
                &[&ab_is, &cd_is],
            );
            let products = self.b.ap(
                "mpbir",
                &binds! {"ph" => t!(&ab, &cd, "clt", "wbr"), "ps" => t!(&sp_, &sq, "clt", "wbr")},
                &[&numerals::below(&self.b, p.clone(), q.clone()), &valued],
            );
            self.b.ap(
                "mpbi",
                &binds! {"ph" => t!(&ab, &cd, "clt", "wbr"), "ps" => t!(&ad, &cb, "clt", "wbr")},
                &[&products, &crossed(&a, &b, &c, &d)],
            )
        } else {
            if p > q {
                return None;
            }
            // not C·D < A·B, from the numerals: P ≤ Q is not Q < P.
            let at_most = if p == q {
                self.b.ap("leidi", &binds! {"A" => &sp_}, &[&real(&p)])
            } else {
                let law = self.b.ap(
                    "ltlei",
                    &binds! {"A" => &sp_, "B" => &sq},
                    &[&real(&p), &real(&q)],
                );
                self.b.ap(
                    "ax-mp",
                    &binds! {"ph" => t!(&sp_, &sq, "clt", "wbr"), "ps" => t!(&sp_, &sq, "cle", "wbr")},
                    &[&numerals::below(&self.b, p.clone(), q.clone()), &law],
                )
            };
            let not_less = |x: &Rpn, y: &Rpn| t!(t!(y, x, "clt", "wbr"), "wn");
            let reals = |x: &Rpn, y: &Rpn, px: &Proof, py: &Proof| {
                and(&t!(x, "cr", "wcel"), &t!(y, "cr", "wcel"), px, py)
            };
            // ( x <_ y <-> -. y < x ), for x and y real.
            let lenlt = |x: &Rpn, y: &Rpn, px: &Proof, py: &Proof| {
                self.b.ap(
                    "ax-mp",
                    &binds! {
                        "ph" => t!(t!(x, "cr", "wcel"), t!(y, "cr", "wcel"), "wa"),
                        "ps" => t!(t!(x, y, "cle", "wbr"), not_less(x, y), "wb"),
                    },
                    &[
                        &reals(x, y, px, py),
                        &self.b.ap("lenlt", &binds! {"A" => x, "B" => y}, &[]),
                    ],
                )
            };
            let numerals_not = self.b.ap(
                "mpbi",
                &binds! {"ph" => t!(&sp_, &sq, "cle", "wbr"), "ps" => not_less(&sp_, &sq)},
                &[&at_most, &lenlt(&sp_, &sq, &real(&p), &real(&q))],
            );
            let valued = self.b.ap(
                "breq12i",
                &binds! {"A" => &cd, "B" => &sq, "C" => &ab, "D" => &sp_, "R" => "clt"},
                &[&cd_is, &ab_is],
            );
            let valued = self.b.ap(
                "notbii",
                &binds! {"ph" => t!(&cd, &ab, "clt", "wbr"), "ps" => t!(&sq, &sp_, "clt", "wbr")},
                &[&valued],
            );
            let products_not = self.b.ap(
                "mpbir",
                &binds! {"ph" => t!(t!(&cd, &ab, "clt", "wbr"), "wn"), "ps" => not_less(&sp_, &sq)},
                &[&numerals_not, &valued],
            );
            let exchanged = self.b.ap(
                "notbii",
                &binds! {"ph" => t!(&cd, &ab, "clt", "wbr"), "ps" => t!(&cb, &ad, "clt", "wbr")},
                &[&crossed(&c, &d, &a, &b)],
            );
            let fractions_not = self.b.ap(
                "mpbi",
                &binds! {"ph" => t!(t!(&cd, &ab, "clt", "wbr"), "wn"), "ps" => not_less(&ad, &cb)},
                &[&products_not, &exchanged],
            );
            let real_fraction = |x: &BigUint, y: &BigUint| {
                self.b.ap(
                    "redivcli",
                    &binds! {"A" => sp(x), "B" => sp(y)},
                    &[&real(x), &real(y), &numerals::ne0(&self.b, y.clone())],
                )
            };
            self.b.ap(
                "mpbir",
                &binds! {"ph" => t!(&ad, &cb, "cle", "wbr"), "ps" => not_less(&ad, &cb)},
                &[
                    &fractions_not,
                    &lenlt(&ad, &cb, &real_fraction(&a, &d), &real_fraction(&c, &b)),
                ],
            )
        };
        let back = self.b.ap(
            "breq12i",
            &binds! {"A" => self.rpn(first), "B" => &ad, "C" => self.rpn(second), "D" => &cb, "R" => relation},
            &[&first_is, &second_is],
        );
        Some(self.b.ap(
            "mpbir",
            &binds! {"ph" => self.rpn(goal), "ps" => t!(&ad, &cb, relation, "wbr")},
            &[&between, &back],
        ))
    }

    /// An order between sums, products and whole powers of whole numbers:
    /// each side is worked to its numeral (`numerals::worked`), the order
    /// between the two numerals is proved, and `breq12i` carries it back to
    /// the sides as written.
    #[allow(clippy::too_many_arguments)]
    fn order_by_values(
        &mut self,
        goal: &Term,
        first: &Term,
        second: &Term,
        how: &str,
        negated: bool,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let divides = |side: &Term| {
            side.variable().is_none()
                && side.label() == Some("co")
                && side.children().len() == 3
                && side.children()[2].label() == Some("cdiv")
        };
        // Below 0, or a denial between fractions: the routes after this work
        // with whole numbers of at least 0 and fractions of them, in order.
        let below_zero = |side: &Term| matches!(field::closed_value(side), Built(Value::Exact(v)) if v.is_negative());
        if below_zero(first)
            || below_zero(second)
            || (negated && (divides(first) || divides(second)))
        {
            return self.order_by_difference(first, second, how, negated, scope, facts);
        }
        if divides(first) || divides(second) {
            return Ok(match self.fractions_ordered(goal, first, second, how) {
                Some(closed) => Built(self.b.ap(
                    "a1i",
                    &binds! {"ph" => self.rpn(goal), "ps" => scope},
                    &[&closed],
                )),
                None => Route::no(
                    "the two sides are not fractions of whole numbers in that order",
                ),
            });
        }
        let (Some((a, a_is)), Some((b, b_is))) = (
            numerals::worked(&self.b, first, &labels),
            numerals::worked(&self.b, second, &labels),
        ) else {
            return Ok(Route::no(
                "a side is not a sum, product or whole power of whole numbers",
            ));
        };
        let relation = if how == "<" { "clt" } else { "cle" };
        let (na, nb) = (numerals::spell(a), numerals::spell(b));
        let said = self.rpn(goal);
        let valued = t!(&na, &nb, relation, "wbr");
        let mut turn = self.b.ap(
            "breq12i",
            &binds! {"A" => self.rpn(first), "B" => &na, "C" => self.rpn(second), "D" => &nb, "R" => relation},
            &[&a_is, &b_is],
        );
        let (said, valued) = if negated {
            turn =
                self.b
                    .ap("notbii", &binds! {"ph" => &said, "ps" => &valued}, &[&turn]);
            (t!(said, "wn"), t!(valued, "wn"))
        } else {
            (said, valued)
        };
        let held = take!(self.prove_numeral(&valued, scope, facts)?);
        Ok(Built(self.b.ap(
            "sylibr",
            &binds! {"ph" => scope, "ps" => &valued, "ch" => &said},
            &[&held, &turn],
        )))
    }

    /// ( scope -> -. first = second ) for closed terms of different values:
    /// the lower is below the higher (`order_by_difference`), so the two
    /// differ (`ltne`), turned to the order written (`necomd`, `neneqd`).
    fn closed_apart(
        &mut self,
        first: &Term,
        second: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let (Built(Value::Exact(x)), Built(Value::Exact(y))) =
            (field::closed_value(first), field::closed_value(second))
        else {
            return Ok(Route::no("a side has no exact value"));
        };
        if x == y {
            return Ok(Route::no("the two sides are equal"));
        }
        if self.normaliser_opaque(first) || self.normaliser_opaque(second) {
            return Ok(Route::no(
                "a side holds what the normaliser does not work out, and is said by its value",
            ));
        }
        let first_lower = x < y;
        let (low, high) = if first_lower {
            (first, second)
        } else {
            (second, first)
        };
        let (sl, sh) = (self.rpn(low), self.rpn(high));
        let below =
            take!(self.order_by_difference(low, high, "<", false, scope, facts)?);
        let real = take!(self.prove_numeral(&t!(&sl, "cr", "wcel"), scope, facts)?);
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(&sl, "cr", "wcel"), "ch" => t!(&sl, &sh, "clt", "wbr")},
            &[&real, &below],
        );
        let law = self.b.ap("ltne", &binds! {"A" => &sl, "B" => &sh}, &[]);
        let mut apart = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(t!(&sl, "cr", "wcel"), t!(&sl, &sh, "clt", "wbr"), "wa"),
            "ch" => t!(&sh, &sl, "wne")},
            &[&both, &law],
        );
        let (sf, ss) = (self.rpn(first), self.rpn(second));
        if first_lower {
            apart = self.b.ap(
                "necomd",
                &binds! {"ph" => scope, "A" => &sh, "B" => &sl},
                &[&apart],
            );
        }
        Ok(Built(self.b.ap(
            "neneqd",
            &binds! {"ph" => scope, "A" => &sf, "B" => &ss},
            &[&apart],
        )))
    }

    /// An order between closed terms that are not whole numbers of at least
    /// 0, `−3 < 0` or `−1/2 ≤ 1/3`: the second less the first is worked out
    /// to its value, which is a numeral or a fraction of two, and its sign
    /// says the order (`posdif`, `subge0`). A denial is the order the other
    /// way, turned (`lenlt`, `ltnle`).
    #[allow(clippy::too_many_arguments)]
    fn order_by_difference(
        &mut self,
        first: &Term,
        second: &Term,
        how: &str,
        negated: bool,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let (Built(Value::Exact(x)), Built(Value::Exact(y))) =
            (field::closed_value(first), field::closed_value(second))
        else {
            return Ok(Route::no("a side has no exact value"));
        };
        if self.normaliser_opaque(first) || self.normaliser_opaque(second) {
            return Ok(Route::no(
                "a side holds what the normaliser does not work out, and is said by its value",
            ));
        }
        let (sf, ss) = (self.rpn(first), self.rpn(second));
        let real = |s: &Rpn| t!(s, "cr", "wcel");
        let first_real = take!(self.prove_numeral(&real(&sf), scope, facts)?);
        let second_real = take!(self.prove_numeral(&real(&ss), scope, facts)?);
        if negated {
            // not x < y is y ≤ x, and not x ≤ y is y < x.
            let (turned, law, relation) = if how == "<" {
                ("<=", "lenlt", "clt")
            } else {
                ("<", "ltnle", "cle")
            };
            let other = if turned == "<" { "clt" } else { "cle" };
            let held =
                take!(self
                    .order_by_difference(second, first, turned, false, scope, facts)?);
            let both = self.b.ap(
                "jca",
                &binds! {"ph" => scope, "ps" => real(&ss), "ch" => real(&sf)},
                &[&second_real, &first_real],
            );
            let said = t!(&sf, &ss, relation, "wbr");
            let valued = t!(&ss, &sf, other, "wbr");
            let iff = t!(&valued, t!(&said, "wn"), "wb");
            let law = self.b.ap(law, &binds! {"A" => &ss, "B" => &sf}, &[]);
            let iff = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => t!(real(&ss), real(&sf), "wa"), "ch" => &iff},
                &[&both, &law],
            );
            return Ok(Built(self.b.ap(
                "mpbid",
                &binds! {"ph" => scope, "ps" => &valued, "ch" => t!(&said, "wn")},
                &[&held, &iff],
            )));
        }
        let gap = &y - &x;
        if gap.is_negative() || (how == "<" && gap.is_zero()) {
            return Ok(Route::no(format!(
                "{x} {how} {y} is not what the numbers do"
            )));
        }
        let whole = |v: &BigInt| numerals::spell(v.to_biguint().unwrap_or_default());
        let value = if gap.is_integer() {
            whole(&gap.to_integer())
        } else {
            t!(whole(gap.numer()), whole(gap.denom()), DIV, "co")
        };
        let relation = if how == "<" { "clt" } else { "cle" };
        let difference = t!(&ss, &sf, SUB, "co");
        let equal = take!(self.prove_field(
            None,
            &t!(&difference, &value, "wceq"),
            scope,
            facts,
            &Lines::new()
        )?);
        let signed = take!(self.prove_numeral(
            &t!("cc0", &value, relation, "wbr"),
            scope,
            facts
        )?);
        let sign = self.b.ap(
            "breqtrrd",
            &binds! {"ph" => scope, "A" => "cc0", "R" => relation, "B" => &value, "C" => &difference},
            &[&signed, &equal],
        );
        let said = t!(&sf, &ss, relation, "wbr");
        let by_sign = t!("cc0", &difference, relation, "wbr");
        if how == "<" {
            let both = self.b.ap(
                "jca",
                &binds! {"ph" => scope, "ps" => real(&sf), "ch" => real(&ss)},
                &[&first_real, &second_real],
            );
            let law = self.b.ap("posdif", &binds! {"A" => &sf, "B" => &ss}, &[]);
            let iff = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => t!(real(&sf), real(&ss), "wa"), "ch" => t!(&said, &by_sign, "wb")},
                &[&both, &law],
            );
            return Ok(Built(self.b.ap(
                "mpbird",
                &binds! {"ph" => scope, "ps" => &said, "ch" => &by_sign},
                &[&sign, &iff],
            )));
        }
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => real(&ss), "ch" => real(&sf)},
            &[&second_real, &first_real],
        );
        let law = self.b.ap("subge0", &binds! {"A" => &ss, "B" => &sf}, &[]);
        let iff = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(real(&ss), real(&sf), "wa"), "ch" => t!(&by_sign, &said, "wb")},
            &[&both, &law],
        );
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => &by_sign, "ch" => &said},
            &[&sign, &iff],
        )))
    }

    /// ( scope -> -. y <_ x ) from ( scope -> x < y ), where `strict`, and
    /// ( scope -> -. y < x ) from ( scope -> x <_ y ) otherwise: an order
    /// turned round is the denial of the other (`ltnled`, `lenltd`).
    pub(super) fn denied(
        &self,
        scope: &Rpn,
        x: &Rpn,
        y: &Rpn,
        held: &Ordered,
        strict: bool,
    ) -> Proof {
        let (relation, other, law) = if strict {
            ("clt", "cle", "ltnled")
        } else {
            ("cle", "clt", "lenltd")
        };
        let said = t!(x, y, relation, "wbr");
        let denial = t!(t!(y, x, other, "wbr"), "wn");
        let turned = self.b.ap(
            law,
            &binds! {"ph" => scope, "A" => x, "B" => y},
            &[&held.left_real, &held.right_real],
        );
        pf!(self.b; scope, said, denial, held.proof.clone(), turned, "mpbid")
    }

    /// An order of two numerals, with each side real (`real_numeral`).
    fn numerals_ordered(&self, scope: &Rpn, x: &Rpn, y: &Rpn, proof: Proof) -> Ordered {
        let real = |n: &Rpn| {
            let value =
                linear::numeral(&self.to_term(n), &self.b.flabel).unwrap_or_default();
            self.real_numeral(scope, &value)
        };
        Ordered {
            proof,
            left_real: real(x),
            right_real: real(y),
        }
    }

    /// ( scope -> n e. RR ) for a whole multiplier.
    fn real_numeral(&self, scope: &Rpn, times: &Q) -> Proof {
        let whole = times.numer().magnitude().clone();
        let nw = numerals::spell(whole.clone());
        let held = self.b.ap(
            "a1i",
            &binds! {"ph" => t!(nw, "cr", "wcel"), "ps" => scope},
            &[&numerals::re(&self.b, whole)],
        );
        if !times.numer().is_negative() {
            return held;
        }
        self.b
            .ap("renegcld", &binds! {"ph" => scope, "A" => nw}, &[&held])
    }

    /// ( scope -> a < b ), for whole numbers a below b (`numerals::below`).
    fn numeral_below(&self, scope: &Rpn, a: &BigUint, b: &BigUint) -> Proof {
        self.b.ap(
            "a1i",
            &binds! {"ph" => t!(numerals::spell(a.clone()), numerals::spell(b.clone()), "clt", "wbr"), "ps" => scope},
            &[&numerals::below(&self.b, a.clone(), b.clone())],
        )
    }

    /// ( scope -> -. a = b ), from whichever of the two is below.
    fn numerals_differ(&self, scope: &Rpn, a: &BigUint, b: &BigUint) -> Proof {
        let (low, high) = if a < b { (a, b) } else { (b, a) };
        let (nl, nh) = (numerals::spell(low.clone()), numerals::spell(high.clone()));
        let (nl, nh) = (&nl, &nh);
        let real = self.real_numeral(scope, &Q::from_integer(low.clone().into()));
        let below = self.numeral_below(scope, low, high);
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(nl, "cr", "wcel"), "ch" => t!(nl, nh, "clt", "wbr")},
            &[&real, &below],
        );
        let law = self.b.ap("ltne", &binds! {"A" => nl, "B" => nh}, &[]);
        let apart = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(t!(nl, "cr", "wcel"), t!(nl, nh, "clt", "wbr"), "wa"),
            "ch" => t!(nh, nl, "wne")},
            &[&both, &law],
        );
        let (na, nb) = (numerals::spell(a.clone()), numerals::spell(b.clone()));
        if a != low {
            return self.b.ap(
                "neneqd",
                &binds! {"ph" => scope, "A" => na, "B" => nb},
                &[&apart],
            );
        }
        let turned = self.b.ap(
            "necomd",
            &binds! {"ph" => scope, "A" => nh, "B" => nl},
            &[&apart],
        );
        self.b.ap(
            "neneqd",
            &binds! {"ph" => scope, "A" => na, "B" => nb},
            &[&turned],
        )
    }

    /// Decided by `linear`, and then taken where it cannot be emitted: what
    /// the method concludes is checked against what the step cites, so a
    /// step that does not follow is refused rather than assumed.
    ///
    /// A claim that writes an identity element is the claim without it
    /// (`SYNTAX.md`, "An identity element goes without saying"), and is
    /// proved so where the claim as written is not: `x^1` is an atom to the
    /// method that `x` is not, so the base case `P ≤ (S/1)^1` of an
    /// induction is the claim `P ≤ S` its rows end on, carried back.
    pub fn inequalities(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let found = self.inequalities_as_written(step, term, scope, facts, lines)?;
        let Declined(d) = &found else {
            return Ok(found);
        };
        let bare = self.rpn(&self.without_identities(&self.to_term(term)));
        if bare != *term {
            let tidy =
                self.inequalities_as_written(step, &bare, scope, facts, lines)?;
            if let Built(p) = tidy {
                if let Some(back) = self.tidied(&p, &bare, term, scope, facts)? {
                    return Ok(Built(back));
                }
            }
        }
        Err(self.defect(
            step.line,
            format!(
                "step {} follows from what it cites, and inequalities cannot write its proof: {}",
                fmt(&step.number),
                self.say(d)
            ),
        ))
    }

    /// `inequalities` of the claim as `term` writes it; declined where the
    /// method cannot write its proof.
    fn inequalities_as_written(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if let Some(proof) = self.weakened_line(step, term, scope, facts, lines)? {
            return Ok(Built(proof));
        }
        // A defined name is read as what it names, as `membership` and the
        // comparison of two spellings read it: the claim and each cited line
        // are taken with their defined names written out.
        let out = take!(self.names_written_out(
            Some(step),
            &step.just.refs,
            term,
            scope,
            facts,
            lines
        )?);
        let (term_out, lines_out) = (&out.term, &out.lines.copy());
        // A step said of every member has the membership its claim's "for
        // all" gives the member as a cited line (`SYNTAX.md`), with what it
        // implies, `i ≥ 1` of i ∈ ℕ, as the checker reads it. The step's own
        // claim says it, so it is cited under the step's number, which names
        // no line while the step is proved.
        let mut refs = step.just.refs.clone();
        if let Some(member) = self.member.clone() {
            if let Some(proof) = self.held(facts, &member, scope)? {
                let line = Line::new(member, proof, Vec::new());
                let own = fmt(&step.number);
                lines_out.set(own.clone(), line);
                refs.push(own);
            }
        }
        // A cited line says each of its parts, a membership among them, as
        // the checker and R3 read it (`READERS.md`, what a membership says).
        // Only what the step may rest on is offered, so that a bound the
        // cited lines give is proved from them and not taken from a line in
        // scope that says the same, which the step does not name.
        let cited = self.with_cited(Some(step), scope, &out.facts, None)?;
        let facts_out = &self.restable(&cited);
        // A plain step adds its facts as they stand, the combination the
        // checker decided it by; a step with rows, a chain and an order
        // with its converse are proved from their lines in one, by any.
        let plain =
            step.just.head.is(Method::Inequalities) && step.just.rows.is_empty();
        // The method wants every atom in ℝ, and a `requires` line is where
        // the step writes that; offered to the membership lookup and to
        // nothing else.
        let known = self.supplied(Some(step), scope, facts)?;
        let kept = std::mem::replace(&mut self.adding_only, plain);
        let found = self.writing(scope, &known, false, |me| {
            let rewritten = me.algebra_rows(step, refs, scope, facts_out, lines_out)?;
            let skip = if plain {
                me.not_combined(&rewritten.refs, term_out, facts_out, &rewritten.lines)?
            } else {
                Vec::new()
            };
            me.prove_order(
                &rewritten.refs,
                term_out,
                scope,
                facts_out,
                &rewritten.lines,
                &skip,
            )
        });
        self.adding_only = kept;
        let found = found?;
        if found.is_declined() || term_out == term {
            return Ok(found);
        }
        // Back from the claim written out to the claim as the page writes it.
        let proof = take!(found);
        let (said, want) = (self.to_term(term_out), self.to_term(term));
        let Built(back) = self.same(&said, &want, scope, facts, Some(step))? else {
            return Ok(Route::no("the claim written out is not carried back"));
        };
        Ok(Built(
            pf!(self.b; scope, term_out, term, proof, back, "mpbid"),
        ))
    }

    /// `a ≤ b` from a line the step cites saying `a < b` of the same two
    /// terms, by `ltled`; None where no cited line does. The terms are not
    /// taken apart, so each needs only what the step's lines say of it
    /// whole: the area of a triangle is a number by `area-real`, though
    /// nothing says the size of the sine inside it is.
    fn weakened_line(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Option<Proof>> {
        let claim = self.to_term(term);
        let kids = claim.children();
        if claim.variable().is_some()
            || claim.label() != Some("wbr")
            || kids.len() != 3
            || self.rpn(&kids[2]) != t!("cle")
        {
            return Ok(None);
        }
        let (a, b) = (self.rpn(&kids[0]), self.rpn(&kids[1]));
        let strict = t!(&a, &b, "clt", "wbr");
        for r in &step.just.refs {
            if !self.line_writes(r, lines).contains(&strict) {
                continue;
            }
            let node = self.to_term(&strict);
            let Built(given) = self.cited_fact(r, &node, scope, facts, lines)? else {
                continue;
            };
            let ra = self.membership(&a, "cr", scope, facts)?;
            let rb = self.membership(&b, "cr", scope, facts)?;
            return Ok(Some(self.b.ap(
                "ltled",
                &binds! {"ph" => scope, "A" => &a, "B" => &b},
                &[&ra, &rb, &given],
            )));
        }
        Ok(None)
    }

    /// What an inequalities step with rows is proved from: the lines it
    /// cites, and for each `algebra` row, the equation of each side it
    /// rewrites with that side of the row above, which the algebra method
    /// proves (`METHODS.md`, inequalities, Rows). A row keeps its sides where
    /// the row above has them, so side meets side. With the equations, what
    /// the rows make is linear in what the step writes; without them a
    /// rewriting such as a·a^m to a^m·a is two atoms. A step with no rows is
    /// proved from its lines as they are.
    fn algebra_rows(
        &mut self,
        step: &Step,
        refs: Vec<String>,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<RowsRewritten> {
        let unchanged = RowsRewritten {
            refs: refs.clone(),
            lines: lines.clone(),
        };
        let Some(cut) = rows(&step.just, &self.thm.path) else {
            return Ok(unchanged);
        };
        let here = lines.copy();
        let mut refs = refs;
        let mut above: Option<Term> = None;
        for row in cut? {
            let node = self.read_one(&row.formula)?;
            let written = self.term(&node)?;
            let said = self.to_term(&written);
            if let (RowReason::Algebra, Some(before)) = (&row.reason, &above) {
                for side in 0..2 {
                    let was = self.rpn(&before.children()[side]);
                    let now = self.rpn(&said.children()[side]);
                    if was == now {
                        continue;
                    }
                    let equation = t!(&was, &now, "wceq");
                    match self.prove_field(None, &equation, scope, facts, &here)? {
                        Built(proof) => {
                            let label = format!("row {} side {side}", row.line);
                            here.set(
                                label.clone(),
                                Line::new(equation, proof, Vec::new()),
                            );
                            refs.push(label);
                        }
                        Declined(d) => {
                            return Err(self.defect(
                                row.line,
                                format!(
                                    "the algebra row of step {} rewrites {} as {}, which algebra does not prove: {}",
                                    fmt(&step.number),
                                    self.render(&was),
                                    self.render(&now),
                                    self.say(&d)
                                ),
                            ))
                        }
                    }
                }
            }
            above = Some(said);
        }
        Ok(RowsRewritten { refs, lines: here })
    }

    /// A term with each defined name written out as what it names.
    pub(crate) fn defined_names_out(&self, term: &Term) -> Term {
        if term.variable().is_some() {
            return term.clone();
        }
        let kids = term.children();
        if term.label() == Some("cv") && kids.len() == 1 {
            if let Some(body) = self.named_body(term, &Vars::new()) {
                return self.defined_names_out(&body);
            }
        }
        let parts: Vec<Term> = kids.iter().map(|k| self.defined_names_out(k)).collect();
        Term::apply(term.label().unwrap_or(""), parts)
    }

    /// A term with each finite sum, one holding no sum of its own, written
    /// over `letter`: a sum a define names and the same sum a line writes
    /// are then one term, whatever letters the two were written over.
    fn sums_over(&self, term: &Term, letter: &str) -> Term {
        if term.variable().is_some() {
            return term.clone();
        }
        let kids = term.children();
        if term.label() == Some("csu") && kids.len() == 3 {
            let inner = self.rpn(&kids[1]);
            if !inner.has("csu") {
                let from = self.rpn(&kids[2]);
                let summand =
                    self.restated(&kids[1], &t!(from, "cv"), &t!(letter, "cv"));
                return Term::apply(
                    "csu",
                    vec![kids[0].clone(), summand, self.var_of(letter)],
                );
            }
        }
        let parts: Vec<Term> = kids.iter().map(|k| self.sums_over(k, letter)).collect();
        Term::apply(term.label().unwrap_or(""), parts)
    }

    /// The claim, the facts and the lines a step or a requires line cites,
    /// with defined names written out: each cited line written otherwise is
    /// laid down written out, carried across by `same`, which reads a defined
    /// name the same way.
    fn names_written_out(
        &mut self,
        step: Option<&Step>,
        refs: &[String],
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<WrittenOut>> {
        let claim = self.to_term(term);
        let cited: Vec<ProvedClaim> = refs
            .iter()
            .filter_map(|r| self.line_written(r, lines))
            .collect();
        let labels: Vec<&String> = refs
            .iter()
            .filter(|r| self.line_written(r, lines).is_some())
            .collect();
        // Every sum is written over one letter nothing holds, so that a sum
        // a define names and the same sum a line writes are one term.
        let mut seen: Vec<Term> = vec![claim.clone(), self.to_term(scope)];
        seen.extend(cited.iter().map(|l| self.to_term(&l.claim)));
        let refs: Vec<&Term> = seen.iter().collect();
        let as_written = WrittenOut {
            term: term.clone(),
            facts: facts.clone(),
            lines: lines.clone(),
        };
        let Some(letter) = self.unheld(&refs).map(|v| self.rpn(&v).to_string()) else {
            return Ok(Built(as_written));
        };
        // Only a step that writes both a defined name and what it names
        // reads its names written out; any other reads them as written.
        let mut written: BTreeSet<Rpn> = BTreeSet::new();
        let mut named: BTreeSet<Rpn> = BTreeSet::new();
        let mut rest: Vec<Term> = vec![self.sums_over(&claim, &letter)];
        rest.extend(
            cited
                .iter()
                .map(|l| self.sums_over(&self.to_term(&l.claim), &letter)),
        );
        while let Some(node) = rest.pop() {
            if node.variable().is_some() {
                continue;
            }
            let kids = node.children();
            if node.label() == Some("cv") && kids.len() == 1 {
                if let Some(body) = self.named_body(&node, &Vars::new()) {
                    let out = self.defined_names_out(&body);
                    named.insert(self.rpn(&self.sums_over(&out, &letter)));
                }
            }
            // A defined function applied names its rule at the argument:
            // t(k) with t(j) = j + 1 names k + 1.
            if node.label() == Some("cfv") && kids.len() == 2 {
                let out = self.read_out(&node);
                if self.rpn(&out) != self.rpn(&node) {
                    named.insert(self.rpn(&self.sums_over(&out, &letter)));
                }
            }
            written.insert(self.rpn(&node));
            rest.extend(kids.iter().cloned());
        }
        if !named.iter().any(|body| written.contains(body)) {
            return Ok(Built(as_written));
        }
        let written_out = |me: &mut Self, t: &Term| {
            let out = me.read_out(t);
            me.sums_over(&out, &letter)
        };
        let out = written_out(self, &claim);
        let term_out = self.rpn(&out);
        let (facts_out, lines_out) = (facts.copy(), lines.copy());
        for (r, line) in labels.into_iter().zip(&cited) {
            let said = self.to_term(&line.claim);
            let written = written_out(self, &said);
            let out_rpn = self.rpn(&written);
            if out_rpn == line.claim {
                continue;
            }
            let held = self.carried(r, facts, lines);
            let Built(alike) = self.same(&said, &written, scope, facts, step)? else {
                return Ok(Route::no(
                    "a cited line is not carried to its names written out",
                ));
            };
            let proof = pf!(self.b; scope, line.claim, out_rpn, held, alike, "mpbid");
            self.know(&facts_out, out_rpn.clone(), proof.clone());
            let kept = lines.get(r).expect("a line cited");
            lines_out.set(r.clone(), kept.restated(out_rpn, proof));
        }
        Ok(Built(WrittenOut {
            term: term_out,
            facts: facts_out,
            lines: lines_out,
        }))
    }

    /// The parts of the cited lines a plain step leaves out: those outside
    /// the combination the checker decided it by (`inequalities::combined`),
    /// whose facts added as they stand are the claim. Another combination
    /// that contradicts the claim denied may rest on more lines and ask more
    /// of its atoms, as `2/p < m` with `0 < 2/p` asks p ≠ 0 where `m ∈ ℕ`
    /// gives `0 < m` alone.
    fn not_combined(
        &mut self,
        refs: &[String],
        term: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Vec<Rpn>> {
        let labels = self.b.flabel.clone();
        let mut parts: Vec<Rpn> = Vec::new();
        let mut cited: Vec<Term> = Vec::new();
        let mut line_of: Vec<usize> = Vec::new();
        let mut implied: Vec<Term> = Vec::new();
        for (at, r) in refs.iter().enumerate() {
            for said in self.line_writes(r, lines) {
                let one = self.to_term(&said);
                if linear::fact(&one, &labels).is_some() {
                    parts.push(said);
                    cited.push(one);
                    line_of.push(at);
                }
            }
            for said in &self.stated_claims(r, facts, lines) {
                for (extra, _lemmas) in self.implied_terms(said) {
                    implied.push(self.to_term(&extra));
                }
            }
        }
        let goal = self.to_term(term);
        let Some(used) = crate::methods::inequalities::combined(
            &goal, &cited, &line_of, &implied, &labels,
        ) else {
            return Err(self.unreached(
                self.at,
                "the checker took this step as adding its facts, and no combination of them adds to its claim",
            ));
        };
        Ok(parts
            .into_iter()
            .enumerate()
            .filter(|(i, _)| !used.contains(i))
            .map(|(_, p)| p)
            .collect())
    }

    /// An `inequalities` claim, by whichever route reaches it. `skip` names
    /// sentences of the cited lines to leave out: a case of a split must not
    /// split again on the disequality it split on.
    pub fn prove_order(
        &mut self,
        refs: &[String],
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let goal = self.to_term(term);
        let mut given = Vec::new();
        let mut where_: Vec<(String, Term)> = Vec::new();
        // What a cited membership implies is offered with the facts as
        // written.
        let mut implied_given = Vec::new();
        let mut implied_where: Vec<(String, Term)> = Vec::new();
        for r in refs {
            for said in self.line_writes(r, lines) {
                if skip.contains(&said) {
                    continue;
                }
                if let Some(one) = linear::fact(&self.to_term(&said), &labels) {
                    given.push(one);
                    where_.push((r.clone(), self.to_term(&said)));
                }
            }
            // The bounds only: k ≠ 0 would split every certificate.
            for said in &self.stated_claims(r, facts, lines) {
                if skip.contains(said) {
                    continue;
                }
                for (extra, _lemmas) in self.implied_terms(said) {
                    if let Some(one) = linear::fact(&self.to_term(&extra), &labels) {
                        if one.how != How::Ne {
                            implied_given.push(one);
                            implied_where.push((r.clone(), self.to_term(&extra)));
                        }
                    }
                }
            }
        }
        if goal.variable().is_none() && goal.label() == Some("wa") {
            return self.both_halves(refs, &goal, scope, facts, lines, skip);
        }
        let Some(claim) = linear::fact(&goal, &labels) else {
            return Ok(Route::no("the claim is not linear"));
        };
        if let Some(closed) = self.by_antisymmetry(&goal, scope, facts)? {
            return Ok(Built(closed));
        }
        let written = given.len();
        given.extend(implied_given);
        where_.extend(implied_where);
        let mut all = given.clone();
        all.push(linear::opposite(&claim));
        // Which cited line each fact came from; the claim denied is none.
        let mut line_of: Vec<Option<usize>> = where_
            .iter()
            .map(|(r, _)| refs.iter().position(|one| one == r))
            .collect();
        line_of.push(None);
        let Some(found) = linear::certificate(&all, &line_of, self.adding_only) else {
            return Ok(Route::no("the cited facts do not reach the claim"));
        };
        let found = match found {
            Certificate::Farkas(w) => w,
            either => {
                return self.either_way(
                    &either, refs, &where_, &given, term, scope, facts, lines, skip,
                )
            }
        };
        if !found.contains_key(&given.len()) {
            // The denied claim went unused, so the cited facts refute each
            // other, and any claim follows (`METHODS.md`, inequalities: the
            // set with the claim denied has no solution). One written fact
            // the refutation uses is denied from the rest, by this route
            // with that fact left out, and the two give the claim
            // (`pm2.21dd`).
            let Some(j) = found
                .iter()
                .filter(|(i, k)| !k.is_zero() && **i < written)
                .map(|(i, _)| *i)
                .next()
            else {
                return Ok(Route::no(
                    "the cited facts refute each other only through what their memberships imply",
                ));
            };
            let (r, said) = where_[j].clone();
            let fact = self.rpn(&said);
            let mut leave = skip.to_vec();
            leave.push(fact.clone());
            let denied = take!(self.prove_order(
                refs,
                &t!(&fact, "wn"),
                scope,
                facts,
                lines,
                &leave
            )?);
            let held = take!(self.cited_fact(&r, &said, scope, facts, lines)?);
            return Ok(Built(
                pf!(self.b; scope, fact, term, held, denied, "pm2.21dd"),
            ));
        }
        let used: Vec<usize> = found
            .iter()
            .filter(|(i, k)| !k.is_zero() && **i < given.len())
            .map(|(i, _)| *i)
            .collect();
        let weight = found[&given.len()].clone();
        if claim.how == How::Ne {
            let made = self.stays_apart(
                &used, &given, &where_, &claim, &goal, scope, facts, lines,
            )?;
            if made.is_declined() {
                let apart =
                    self.apart_by_order(refs, &goal, scope, facts, lines, skip)?;
                if !apart.is_declined() {
                    return Ok(apart);
                }
            }
            return Ok(made);
        }
        if goal.variable().is_none() && goal.label() == Some("wn") {
            return self.negated_order(&goal, refs, term, scope, facts, lines, skip);
        }
        let Some((left, right, how)) = order_sides(&goal) else {
            return Ok(Route::no("the claim states no relation"));
        };
        let (left, right) = (self.rpn(&left), self.rpn(&right));
        // What the scaled facts leave over is a constant, which the method
        // may use as a closed numeral fact the step does not cite.
        let mut spare = claim.side.clone();
        for i in &used {
            spare = spare.minus(&given[*i].side.scaled(&(&found[i] / &weight)));
        }
        if !spare.constant_only() {
            return Ok(Route::no("what is left over is not a constant"));
        }
        // One equation, scaled by a whole number, that is the claim with
        // nothing left over. A fraction is `combination`'s, which clears its
        // denominator.
        let one_equation = match used.as_slice() {
            [only] if given[*only].how == How::Eq && spare.constant.is_zero() => {
                Some((*only, &found[only] / &weight)).filter(|(_, t)| t.is_integer())
            }
            _ => None,
        };
        if let Some((only, times)) = one_equation {
            return self.one_equation_scaled(
                &where_[only],
                &times,
                &left,
                &right,
                how,
                scope,
                facts,
                lines,
            );
        }
        let parts: Vec<Part> = used
            .iter()
            .map(|i| {
                let (cited, said) = where_[*i].clone();
                Part {
                    cited,
                    said,
                    times: &found[i] / &weight,
                }
            })
            .collect();
        self.combination(
            &parts,
            &left,
            &right,
            how,
            &spare.constant,
            scope,
            facts,
            lines,
        )
    }

    /// `membership`: a term in a number system because its parts are, down
    /// to atoms whose membership the step's lines say.
    pub fn by_membership(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let claim = self.to_term(term);
        let supplied = self.supplied(Some(step), scope, facts)?;
        let cited = self.with_cited(Some(step), scope, &supplied, None)?;
        let known = facts.with(&cited);
        match self.member_of(&claim, scope, &known, Some(step))? {
            Built(p) => Ok(Built(p)),
            Declined(d) => Err(self.defect(
                step.line,
                format!(
                    "{} is not built from what step {} cites: {}",
                    self.render(term),
                    fmt(&step.number),
                    self.say(&d)
                ),
            )),
        }
    }

    /// The proof of one membership by `membership`'s procedure, from the
    /// facts `known`, or a decline naming what it lacks.
    pub fn member_of(
        &mut self,
        claim: &Term,
        scope: &Rpn,
        known: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        // Said of every member: the member is fixed, what its membership says
        // is laid beside it, and the claim is generalised.
        if claim.variable().is_none() && claim.label() == Some("wral") {
            let (body, variable, over) = (
                claim.children()[0].clone(),
                claim.children()[1].clone(),
                claim.children()[2].clone(),
            );
            return self.for_every(
                scope,
                known,
                &body,
                &variable,
                &over,
                &mut |me, said, inner, lifted| me.member_of(said, inner, lifted, step),
                true,
            );
        }
        let term = self.rpn(claim);
        // The claim with its defined names and maps read as what they stand
        // for, and nothing else changed (`read_out`): a part is then the term
        // the page wrote, which the facts saying it are found by, and not a
        // respelling of it, ⌊c·10^n⌋ for ⌊10^n·c⌋, that only the parts' own
        // memberships would carry back.
        let read = self.read_out(claim);
        let (whole, system) = (read.children()[0].clone(), read.children()[1].clone());
        // The claim is read with its defined names written out, and so is
        // each membership the facts hold: a line saying a defined name is
        // real is then a line about what the claim, read, holds.
        let known = &self.read_memberships(scope, known, step)?;
        let made = if whole.variable().is_none() && whole.label() == Some("csu") {
            self.summed(&whole, &self.rpn(&system), scope, known, step)?
        } else {
            self.part(&self.rpn(&whole), &self.rpn(&system), scope, known)?
        };
        if made.is_declined() || self.rpn(&read) == term {
            return Ok(made);
        }
        let made = take!(made);
        let alike = take!(self.same(&read, claim, scope, known, step)?);
        Ok(Built(
            pf!(self.b; scope, self.rpn(&read), term, made, alike, "mpbid"),
        ))
    }

    /// `known`, with each fact `part` builds from — a membership in a number
    /// system, a term's not being 0, and a term above 0 or below it — laid
    /// down beside itself in its standard form, where that differs.
    pub(crate) fn read_memberships(
        &mut self,
        scope: &Rpn,
        known: &Facts,
        step: Option<&Step>,
    ) -> Checked<Facts> {
        let kept = std::mem::replace(&mut self.reading_facts, true);
        let out = self.memberships_read(scope, known, step);
        self.reading_facts = kept;
        out
    }

    fn memberships_read(
        &mut self,
        scope: &Rpn,
        known: &Facts,
        step: Option<&Step>,
    ) -> Checked<Facts> {
        let out = known.copy();
        // The side conditions the step wrote are facts here as well, read
        // as the rest are.
        let mut offered = known.entries();
        for (said, w) in self.written.entries() {
            if let Some(lifted) = self.lifted_to(&said, &w.proof, &w.at, scope) {
                offered.push((said, lifted));
            }
        }
        for (said, held) in offered {
            let fact = self.to_term(&said);
            let member = fact.label() == Some("wcel")
                && lookup(
                    rules::SYSTEMS,
                    self.rpn(&fact.children()[1]).alone().unwrap_or_default(),
                )
                .is_some();
            let nonzero = fact.label() == Some("wn")
                && fact.children()[0].label() == Some("wceq")
                && self.rpn(&fact.children()[0].children()[1]).alone() == Some("cc0");
            // A term above zero or below it, which says it is not zero.
            let signed = fact.label() == Some("wbr")
                && self.rpn(&fact.children()[2]).alone() == Some("clt")
                && (self.rpn(&fact.children()[0]).alone() == Some("cc0")
                    || self.rpn(&fact.children()[1]).alone() == Some("cc0"));
            if fact.variable().is_some() || !(member || nonzero || signed) {
                continue;
            }
            let read = self.standard(&fact);
            let read_rpn = self.rpn(&read);
            if read_rpn == said || self.holds(&out, &read_rpn) {
                continue;
            }
            if let Built(alike) = self.same(&fact, &read, scope, known, step)? {
                let proof = pf!(self.b; scope, said, read_rpn, held, alike, "mpbid");
                self.know(&out, read_rpn.clone(), proof);
            }
        }
        Ok(out)
    }

    /// The scope widened by one member of `over`, and the facts with what
    /// that membership says laid beside it.
    fn fixed(
        &mut self,
        scope: &Rpn,
        known: &Facts,
        variable: &Term,
        over: &Term,
    ) -> Checked<(Rpn, Facts)> {
        let member = t!(self.rpn(variable), "cv", self.rpn(over), "wcel");
        let (inner, lifted) = self.widen(scope, known, &member, None);
        let held = self
            .held(&lifted, &member, &inner)?
            .expect("the membership just laid down");
        let more = self.implied(&member, &held, &inner, &lifted)?;
        let out = lifted.copy();
        for (k, v) in more.entries() {
            self.know(&out, k, v);
        }
        Ok((inner, out))
    }

    /// ( scope -> said = L ) and L: a finite sum written out as linear over
    /// `spare`, the step's one letter nothing holds (`field::linear_sum`).
    /// The sum is renamed to the spare (`class_alpha`), its summand is shown
    /// at a member to be the parts added (`sumeq2dv`), the sum is split a
    /// part at a time (`fsumadd`), and each part's free factor is taken out
    /// (`fsummulc2`). The sum lemmas keep their letter apart from the scope
    /// and the range, which the spare is.
    pub fn linear_sum(
        &mut self,
        said: &Rpn,
        spare: &str,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<(Term, Proof)>> {
        let labels = self.b.flabel.clone();
        let whole = self.to_term(said);
        let Some(field::LinearSum {
            range,
            letter,
            parts,
        }) = field::linear_sum(&whole, &labels)
        else {
            return Ok(Route::no("the sum is read as one atom"));
        };
        let summand = whole.children()[1].clone();
        let range_term = whole.children()[0].clone();
        // Already as the parts write it, and nothing to do.
        if letter == spare
            && parts.len() == 1
            && parts[0].weight == q(1)
            && parts[0].free.is_empty()
            && self.rpn(&summand) == field::spell_monomial(&parts[0].bound)
        {
            return Ok(Route::no("the sum is written out already"));
        }
        let member_cv = t!(spare, "cv");
        let summand_at = if letter == spare {
            self.rpn(&summand)
        } else {
            let moved = self.restated(&summand, &t!(letter, "cv"), &member_cv);
            self.rpn(&moved)
        };
        let at_spare = t!(range, summand_at, spare, "csu");
        let renamed = if letter == spare {
            None
        } else {
            let Some(closed) = self.class_alpha(&whole, &self.to_term(&at_spare))?
            else {
                return Ok(Route::no("the sum is not renamed to the spare letter"));
            };
            Some(pf!(self.b; t!(said, at_spare, "wceq"), scope, closed, "a1i"))
        };
        // The parts, each its free factor times what holds the letter.
        let mut scaled: Vec<(Rpn, Rpn, Rpn)> = Vec::new();
        for part in &parts {
            let bound = field::respelt(&part.bound, letter, Symbol::of(spare));
            let m = field::spell_monomial(&bound);
            let c = Emitter::spell_run(&[(part.free.clone(), part.weight.clone())]);
            let t = t!(c, m, "cmul", "co");
            scaled.push((c, m, t));
        }
        let mut prefixes: Vec<Rpn> = vec![scaled[0].2.clone()];
        for one in &scaled[1..] {
            let last = prefixes.last().unwrap().clone();
            prefixes.push(t!(last, one.2, "caddc", "co"));
        }
        let added = prefixes.last().unwrap().clone();
        // At a member: the summand is the parts added, and each part and
        // each run of them is a number.
        let variable = self.var_of(spare);
        let at_member = self.frames_kept(|me| -> Checked<Route<AtMember>> {
            let (inner, lifted) = me.fixed(scope, facts, &variable, &range_term)?;
            // What the member's membership says is the step's to use there,
            // as a line it writes: the claim's sum ranges over it.
            let kept = me.written.clone();
            for (said, held) in lifted.entries() {
                if !me.holds(facts, &said) {
                    me.write(said, inner.clone(), held);
                }
            }
            let made = (|| -> Checked<Route<AtMember>> {
                let mut w = Work::plain(&inner, &lifted);
                let pointwise =
                    take!(me.same_polynomial(&mut w, &summand_at, &added)?);
                let mut runs = Vec::new();
                for p in &prefixes {
                    runs.push(me.membership(p, "cc", &inner, &lifted)?);
                }
                let mut terms = Vec::new();
                let mut bounds = Vec::new();
                for (_, m, t) in &scaled {
                    terms.push(me.membership(t, "cc", &inner, &lifted)?);
                    bounds.push(me.membership(m, "cc", &inner, &lifted)?);
                }
                Ok(Built(AtMember {
                    pointwise,
                    runs,
                    terms,
                    bounds,
                }))
            })();
            me.written = kept;
            made
        })?;
        let AtMember {
            pointwise,
            runs,
            terms,
            bounds,
        } = take!(at_member);
        let sum_of = |s: &Rpn| t!(range, s, spare, "csu");
        let finite = {
            let kids = range_term.children();
            let law = self.b.ap(
                "fzfi",
                &binds! {"M" => self.rpn(&kids[0]), "N" => self.rpn(&kids[1])},
                &[],
            );
            pf!(self.b; t!(range, "cfn", "wcel"), scope, law, "a1i")
        };
        // Each part's sum is a number, its terms being (`fsumcl`), kept for
        // when the normaliser asks.
        for (i, (_, m, _)) in scaled.iter().enumerate() {
            let p = self.b.ap(
                "fsumcl",
                &binds! {"ph" => scope, "A" => &range, "B" => m, "k" => spare},
                &[&finite, &bounds[i]],
            );
            self.sums_in_cc.insert((scope.clone(), sum_of(m)), p);
        }
        // ( scope -> sum of the summand = sum of the parts added ).
        let lifted = self.b.ap(
            "sumeq2dv",
            &binds! {"ph" => scope, "k" => spare, "A" => &range, "B" => &summand_at, "C" => &added},
            &[&pointwise],
        );
        // ( scope -> sum of the parts added = the parts' sums added ).
        let mut split: Option<Proof> = None;
        let mut sums = sum_of(&scaled[0].2);
        for i in 1..scaled.len() {
            let (before, part) = (&prefixes[i - 1], &scaled[i].2);
            let step = self.b.ap(
                "fsumadd",
                &binds! {"ph" => scope, "A" => &range, "B" => before, "C" => part, "k" => spare},
                &[&finite, &runs[i - 1], &terms[i]],
            );
            let next = t!(sums, sum_of(part), "caddc", "co");
            split = Some(match split {
                None => step,
                Some(earlier) => {
                    let carried = self.b.ap(
                        "oveq1d",
                        &binds! {"ph" => scope, "A" => sum_of(before), "B" => &sums,
                        "C" => sum_of(part), "F" => "caddc"},
                        &[&earlier],
                    );
                    self.b.ap(
                        "eqtrd",
                        &binds! {"ph" => scope, "A" => sum_of(&prefixes[i]),
                        "B" => t!(sum_of(before), sum_of(part), "caddc", "co"), "C" => &next},
                        &[&step, &carried],
                    )
                }
            });
            sums = next;
        }
        // ( scope -> the parts' sums added = each free factor times its sum ).
        let mut pulled: Option<(Proof, Rpn, Rpn)> = None;
        for (i, (c, m, t)) in scaled.iter().enumerate() {
            let free = self.membership(c, "cc", scope, facts)?;
            let out = self.b.ap(
                "fsummulc2",
                &binds! {"ph" => scope, "A" => &range, "B" => m, "C" => c, "k" => spare},
                &[&finite, &free, &bounds[i]],
            );
            let times = t!(c, sum_of(m), "cmul", "co");
            let this = self.b.ap(
                "eqcomd",
                &binds! {"ph" => scope, "A" => &times, "B" => sum_of(t)},
                &[&out],
            );
            pulled = Some(match pulled {
                None => (this, sum_of(t), times),
                Some((earlier, from, to)) => {
                    let joined = self.b.ap(
                        "oveq12d",
                        &binds! {"ph" => scope, "A" => &from, "B" => &to,
                        "C" => sum_of(t), "D" => &times, "F" => "caddc"},
                        &[&earlier, &this],
                    );
                    (
                        joined,
                        t!(from, sum_of(t), "caddc", "co"),
                        t!(to, times, "caddc", "co"),
                    )
                }
            });
        }
        let (pulled, from, linear) = pulled.expect("a sum of one part at least");
        // said = at_spare = sum of parts added = sums added = linear.
        let mut chain: Vec<(Proof, Rpn, Rpn)> = Vec::new();
        if let Some(r) = renamed {
            chain.push((r, said.clone(), at_spare.clone()));
        }
        chain.push((lifted, at_spare.clone(), sum_of(&added)));
        if let Some(s) = split {
            chain.push((s, sum_of(&added), from.clone()));
        }
        chain.push((pulled, from, linear.clone()));
        let (mut proof, first, mut last) = chain[0].clone();
        for (p, a, b) in chain.into_iter().skip(1) {
            debug_assert_eq!(a, last);
            proof = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &first, "B" => &a, "C" => &b},
                &[&proof, &p],
            );
            last = b;
        }
        let _ = last;
        Ok(Built((self.to_term(&linear), proof)))
    }

    /// A finite sum in ℝ or ℂ because each term is, for each index in its
    /// range (`fsumrecl`, `fsumcl`). Its terms are a family's values.
    pub(crate) fn summed(
        &mut self,
        whole: &Term,
        system: &Rpn,
        scope: &Rpn,
        known: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        self.in_family += 1;
        let out = self.summed_terms(whole, system, scope, known, step);
        self.in_family -= 1;
        out
    }

    fn summed_terms(
        &mut self,
        whole: &Term,
        system: &Rpn,
        scope: &Rpn,
        known: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        let lemma = match system.alone().unwrap_or_default() {
            "cr" => Some("fsumrecl"),
            "cc" => Some("fsumcl"),
            _ => None,
        };
        let (limits, summand, index) = (
            whole.children()[0].clone(),
            whole.children()[1].clone(),
            whole.children()[2].clone(),
        );
        // A sum the checker found the page says once is a number by its
        // terms at each index, whatever they divide by
        // (`CheckedTheorem::said_sums`), over its own index or one it is
        // renamed to.
        let spelt = self.rpn(whole);
        let said_once = self
            .said_sums
            .iter()
            .any(|s| *s == spelt || self.rebound(s, &spelt));
        let Some(lemma) = lemma.filter(|_| {
            limits.variable().is_none()
                && limits.label() == Some("co")
                && self.rpn(&limits.children()[2]).alone() == Some("cfz")
        }) else {
            return Ok(Route::no(format!(
                "a sum in {system} over this range is not written"
            )));
        };
        // The lemma keeps its index out of the scope and the range. Where
        // either spells it, as an induction hypothesis about a sum over the
        // same letter does, the sum is shown over a letter nothing holds and
        // renamed back (`renaming_apart`).
        let letter = self.rpn(&index);
        let spells = |said: &Rpn| letter.alone().is_some_and(|l| said.has(l));
        if spells(scope) || spells(&self.rpn(&limits)) {
            let Some(name) = index.variable() else {
                return Ok(Route::no("a sum's index is no letter"));
            };
            let Some(fresh) = self.unheld(&[&self.to_term(scope), whole]) else {
                return Ok(Route::no("no letter is left to sum over"));
            };
            let mut put = IndexMap::new();
            put.insert(Symbol::of(name), fresh);
            let moved = whole.substitute(&put);
            let shown = take!(self.summed(&moved, system, scope, known, step)?);
            let said = t!(self.rpn(&moved), system, "wcel");
            let want = t!(self.rpn(whole), system, "wcel");
            let Some(across) = self.renaming_apart(&said, &want)? else {
                return Ok(Route::no("the sum does not rename back"));
            };
            let turned = pf!(self.b; t!(said, want, "wb"), scope, across, "a1i");
            return Ok(Built(
                pf!(self.b; scope, said, want, shown, turned, "mpbid"),
            ));
        }
        let (low, high) = (
            self.rpn(&limits.children()[0]),
            self.rpn(&limits.children()[1]),
        );
        let finite = self.b.ap(
            "fzfid",
            &binds! {"ph" => scope, "M" => &low, "N" => &high},
            &[],
        );
        let system_term = self.to_term(system);
        let each = self.frames_kept(|me| {
            let (inner, lifted) = me.fixed(scope, known, &index, &limits)?;
            let claim = Term::apply("wcel", vec![summand.clone(), system_term.clone()]);
            // A line saying the term at every index says it, whatever the
            // term; a term dividing by the index is so only by such a line
            // (`methods::membership::summed`).
            let by_line = me.said_at_every_index(&claim, &inner, &lifted)?;
            if let Built(_) = by_line {
                return Ok(by_line);
            }
            if !said_once && me.divides_by_index(&summand, &letter, &inner, &lifted)? {
                return Ok(by_line);
            }
            me.member_of(&claim, &inner, &lifted, step)
        })?;
        let each = take!(each);
        Ok(Built(self.b.ap(
            lemma,
            &binds! {"ph" => scope, "A" => self.rpn(&limits), "B" => self.rpn(&summand), "k" => self.rpn(&index)},
            &[&finite, &each],
        )))
    }

    /// Whether a sum's term divides by something holding its index that the
    /// page does not say once is a positive integer (`positive_divisor`),
    /// `letter` as a proof spells it and `scope` fixing it in its range: a
    /// divisor no line outside the sum can say is not zero (`SYNTAX.md`).
    fn divides_by_index(
        &mut self,
        summand: &Term,
        letter: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<bool> {
        if summand.variable().is_some() {
            return Ok(false);
        }
        let kids = summand.children();
        if summand.label() == Some("co")
            && kids.len() == 3
            && self.rpn(&kids[2]).alone() == Some("cdiv")
        {
            let divisor = self.rpn(&kids[1]);
            let holds = letter.alone().is_some_and(|l| divisor.has(l));
            if holds && self.positive_divisor(&divisor, scope, facts)?.is_none() {
                return Ok(true);
            }
        }
        for k in kids {
            if self.divides_by_index(k, letter, scope, facts)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// A sum's term at its index taken from a line the step cites saying it
    /// at every point of a set holding the range (`instance_of_universal`,
    /// `instance_at_a_term`), and from nothing else: its divisor holds the
    /// index, which nothing outside the sum can say is not zero.
    fn said_at_every_index(
        &mut self,
        claim: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        // Only what the proof may rest on, as `settle` offers it.
        let facts = &self.restable(facts);
        let wanted = self.rpn(claim);
        if let Some(p) = self.instance_of_universal(&wanted, scope, facts)? {
            return Ok(Built(p));
        }
        if let Some(p) = self.instance_at_a_term(claim, scope, facts, 3)? {
            return Ok(Built(p));
        }
        Ok(self.no("no line the step cites says {} at every index", &[&wanted]))
    }

    /// A claim of two sentences joined by "and", each proved in turn.
    fn both_halves(
        &mut self,
        refs: &[String],
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        let halves: Vec<Rpn> = goal.children().iter().map(|c| self.rpn(c)).collect();
        let mut made = Vec::new();
        for one in &halves {
            made.push(self.prove_order(refs, one, scope, facts, lines, skip)?);
        }
        let mut proofs = Vec::new();
        for one in made {
            proofs.push(take!(one));
        }
        Ok(Built(
            pf!(self.b; scope, halves[0], halves[1], proofs[0], proofs[1], "jca"),
        ))
    }

    /// `a ≠ b` as the strict bound between them the cited facts give.
    fn apart_by_order(
        &mut self,
        refs: &[String],
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        if goal.variable().is_some()
            || goal.label() != Some("wn")
            || goal.children()[0].label() != Some("wceq")
        {
            return Ok(Route::no("the claim is not a disequality"));
        }
        let pair = goal.children()[0].clone();
        let (a, b) = (self.rpn(&pair.children()[0]), self.rpn(&pair.children()[1]));
        for (lo, hi, turn) in [(&b, &a, "gtned"), (&a, &b, "ltned")] {
            let Built(below) = self.prove_order(
                refs,
                &t!(lo, hi, "clt", "wbr"),
                scope,
                facts,
                lines,
                skip,
            )?
            else {
                continue;
            };
            let real = self.membership(lo, "cr", scope, facts)?;
            let apart = self.b.ap(
                turn,
                &binds! {"ph" => scope, "A" => lo, "B" => hi},
                &[&real, &below],
            );
            return Ok(Built(self.b.ap(
                "neneqd",
                &binds! {"ph" => scope, "A" => &a, "B" => &b},
                &[&apart],
            )));
        }
        Ok(Route::no(
            "the cited facts put neither side below the other",
        ))
    }

    /// Any positive combination of cited facts, and a number left over,
    /// written as the certificate stands: the weights are made whole by
    /// taking the claim's difference `W` times over, each fact is said
    /// against zero and scaled keeping its strictness, what is left over is
    /// one more fact, and the lot is added two at a time.
    #[allow(clippy::too_many_arguments)]
    fn combination(
        &mut self,
        parts: &[Part],
        left: &Rpn,
        right: &Rpn,
        how: &str,
        spare: &Q,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if how != "<" && how != "<=" {
            return Ok(Route::no(format!(
                "a combination reaching {how} is not written"
            )));
        }
        if parts.is_empty() && how == "<=" && spare.is_zero() && left == right {
            let real = self.membership(left, "cr", scope, facts)?;
            return Ok(Built(self.b.ap(
                "leidd",
                &binds! {"ph" => scope, "A" => left},
                &[&real],
            )));
        }
        let whole = field::common_denominator(
            std::iter::once(spare).chain(parts.iter().map(|p| &p.times)),
        );
        let whole_q = Q::from_integer(whole.clone());
        // A reciprocal atom's divisor not being zero is the page's to say, in
        // its own spelling, which `written_nonzero` reads as a polynomial.
        let known = facts.copy();
        for (claim, w) in self.written.entries() {
            if let Some(lifted) = self.lifted_to(&claim, &w.proof, &w.at, scope) {
                self.know_default(&known, claim, lifted);
            }
        }
        let mut w = Work::new(Spec {
            scope: scope.clone(),
            facts: facts.clone(),
            apart: false,
            written: Some(known),
            atoms: RefCell::default(),
            implied: Implied::default(),
        });
        let mut terms: Vec<Against> = Vec::new();
        for Part {
            cited: r,
            said,
            times,
        } in parts
        {
            let given = take!(self.cited_fact(r, said, scope, facts, lines)?);
            let one = take!(self.scaled_bound(
                &mut w,
                said,
                given,
                &(times * &whole_q),
                facts
            )?);
            terms.push(one);
        }
        let left_over = spare * &whole_q;
        if left_over.is_positive() {
            return Ok(Route::no("what is left over is above zero"));
        }
        if left_over.is_negative() {
            let one = take!(self.number_below(scope, &-left_over));
            terms.push(one);
        }
        // Sides that differ only in how they are spelt combine nothing: the
        // claim's difference is zero as a polynomial, and zero is at most
        // zero.
        if terms.is_empty() && how == "<=" {
            let below = self.closed_law(&t!("cc0", "cc0", "cle", "wbr"), "0le0", scope);
            let real = self.closed_law(&t!("cc0", "cr", "wcel"), "0re", scope);
            terms.push(Against {
                term: t!("cc0"),
                strict: false,
                below,
                real,
            });
        }
        if terms.is_empty() {
            return Ok(Route::no("nothing is combined"));
        }
        let mut total = terms[0].clone();
        for one in &terms[1..] {
            total = self.added_pair(scope, &total, one);
        }
        let Against {
            term,
            strict,
            below,
            ..
        } = total;
        if how == "<" && !strict {
            return Ok(Route::no("nothing combined is strict"));
        }
        let mut rel = if strict { "clt" } else { "cle" };
        let span = t!(left, right, "cmin", "co");
        let rl = self.membership(left, "cr", scope, facts)?;
        let rr = self.membership(right, "cr", scope, facts)?;
        let span_real = self.b.ap(
            "resubcld",
            &binds! {"ph" => scope, "A" => left, "B" => right},
            &[&rl, &rr],
        );
        let (mut times_span, mut times_real) = (span.clone(), span_real.clone());
        let numeral = numerals::spell(whole.magnitude().clone());
        if !whole.is_one() {
            times_span = t!(&numeral, span, "cmul", "co");
            let real = self.real_numeral(scope, &whole_q);
            times_real = self.b.ap(
                "remulcld",
                &binds! {"ph" => scope, "A" => &numeral, "B" => &span},
                &[&real, &span_real],
            );
        }
        let alike = take!(self.same_polynomial(&mut w, &times_span, &term)?);
        let mut reached = self.b.ap(
            "eqbrtrd",
            &binds! {"ph" => scope, "A" => &times_span, "B" => &term, "C" => "cc0", "R" => rel},
            &[&alike, &below],
        );
        if strict && how == "<=" {
            let zero = self.closed_law(&t!("cc0", "cr", "wcel"), "0re", scope);
            reached = self.b.ap(
                "ltled",
                &binds! {"ph" => scope, "A" => &times_span, "B" => "cc0"},
                &[&times_real, &zero, &reached],
            );
            rel = "cle";
        }
        if !whole.is_one() {
            reached = self
                .unscaled(&mut w, &span, &span_real, &numeral, &whole, rel, &reached);
        }
        let turn = t!(
            t!(span, "cc0", rel, "wbr"),
            t!(left, right, rel, "wbr"),
            "wb"
        );
        let rl = self.membership(left, "cr", scope, facts)?;
        let rr = self.membership(right, "cr", scope, facts)?;
        let back = if rel == "clt" {
            self.b.ap(
                "sublt0d",
                &binds! {"ph" => scope, "A" => left, "B" => right},
                &[&rl, &rr],
            )
        } else {
            let law = self
                .b
                .ap("suble0", &binds! {"A" => left, "B" => right}, &[]);
            self.b.ap(
                "syl2anc",
                &binds! {"ph" => scope, "ps" => t!(left, "cr", "wcel"), "ch" => t!(right, "cr", "wcel"), "th" => &turn},
                &[&rl, &rr, &law],
            )
        };
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(span, "cc0", rel, "wbr"), "ch" => t!(left, right, rel, "wbr")},
            &[&reached, &back],
        )))
    }

    /// One cited fact scaled by a positive whole number, against zero: an
    /// equation or a bound at most is `at_most_zero`'s; a strict bound is
    /// said as its difference below zero and scaled by `ltmul2`, which keeps
    /// it strict.
    fn scaled_bound(
        &mut self,
        w: &mut Work,
        said: &Term,
        given: Proof,
        times: &Q,
        facts: &Facts,
    ) -> Checked<Route<Against>> {
        let scope = w.spec.scope.clone();
        if !times.is_integer() {
            return Ok(Route::no(format!(
                "a fact scaled by {} is not written",
                super::normal::show(times)
            )));
        }
        let (mut said, mut given) = (said.clone(), given);
        if said.variable().is_none()
            && said.label() == Some("wn")
            && said.children().len() == 1
        {
            let (turned, proof) =
                take!(self.unnegated(&scope, &said.children()[0], &given, facts)?);
            said = turned;
            given = proof;
        }
        let Some((_, _, rel)) = order_sides(&said) else {
            return Ok(Route::no("a cited fact states no relation"));
        };
        // An equation may be taken either way round; a bound only upward.
        if !times.is_positive() && rel != "=" {
            return Ok(Route::no("a bound may only be scaled upward"));
        }
        if rel != "<" {
            let (term, below, real) =
                take!(self.at_most_zero(w, &said, times, given, facts)?);
            return Ok(Built(Against {
                term,
                strict: false,
                below,
                real,
            }));
        }
        let was: Vec<Rpn> = said.children()[..2].iter().map(|c| self.rpn(c)).collect();
        let gap = t!(was[0], was[1], "cmin", "co");
        let r0 = self.membership(&was[0], "cr", &scope, facts)?;
        let r1 = self.membership(&was[1], "cr", &scope, facts)?;
        let real = self.b.ap(
            "resubcld",
            &binds! {"ph" => &scope, "A" => &was[0], "B" => &was[1]},
            &[&r0, &r1],
        );
        let r0 = self.membership(&was[0], "cr", &scope, facts)?;
        let r1 = self.membership(&was[1], "cr", &scope, facts)?;
        let turn = self.b.ap(
            "sublt0d",
            &binds! {"ph" => &scope, "A" => &was[0], "B" => &was[1]},
            &[&r0, &r1],
        );
        let below = self.b.ap(
            "mpbird",
            &binds! {"ph" => &scope, "ps" => t!(gap, "cc0", "clt", "wbr"), "ch" => t!(was[0], was[1], "clt", "wbr")},
            &[&given, &turn],
        );
        if times.is_one() {
            return Ok(Built(Against {
                term: gap,
                strict: true,
                below,
                real,
            }));
        }
        let times_n = times.to_integer();
        let numeral = numerals::spell(times_n.magnitude().clone());
        let scaled = t!(&numeral, gap, "cmul", "co");
        let rn = self.real_numeral(&scope, times);
        let scaled_real = self.b.ap(
            "remulcld",
            &binds! {"ph" => &scope, "A" => &numeral, "B" => &gap},
            &[&rn, &real],
        );
        let moved =
            self.times_positive(w, &gap, &real, &numeral, &times_n, "clt", &below);
        Ok(Built(Against {
            term: scaled,
            strict: true,
            below: moved,
            real: scaled_real,
        }))
    }

    /// ( scope -> ( n x. gap ) R 0 ) from ( scope -> gap R 0 ), n > 0.
    #[allow(clippy::too_many_arguments)]
    fn times_positive(
        &mut self,
        w: &mut Work,
        gap: &Rpn,
        real: &Proof,
        numeral: &Rpn,
        whole: &BigInt,
        rel: &str,
        below: &Proof,
    ) -> Proof {
        let scope = w.spec.scope.clone();
        let lemma = if rel == "clt" { "ltmul2" } else { "lemul2" };
        let scaled = t!(numeral, gap, "cmul", "co");
        let at_zero = t!(numeral, "cc0", "cmul", "co");
        let whole_q = Q::from_integer(whole.clone());
        let rn = self.real_numeral(&scope, &whole_q);
        let pos = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", numeral, "clt", "wbr"), "ps" => &scope},
            &[&numerals::pos(&self.b, whole.magnitude().clone())],
        );
        let positive = self.b.ap(
            "jca",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cr", "wcel"), "ch" => t!("cc0", numeral, "clt", "wbr")},
            &[&rn, &pos],
        );
        let zero = self.closed_law(&t!("cc0", "cr", "wcel"), "0re", &scope);
        let law = self.b.ap(
            lemma,
            &binds! {"A" => gap, "B" => "cc0", "C" => numeral},
            &[],
        );
        let turn = self.b.ap(
            "syl3anc",
            &binds! {"ph" => &scope, "ps" => t!(gap, "cr", "wcel"), "ch" => t!("cc0", "cr", "wcel"),
            "th" => t!(t!(numeral, "cr", "wcel"), t!("cc0", numeral, "clt", "wbr"), "wa"),
            "ta" => t!(t!(gap, "cc0", rel, "wbr"), t!(scaled, at_zero, rel, "wbr"), "wb")},
            &[real, &zero, &positive, &law],
        );
        let moved = self.b.ap(
            "mpbid",
            &binds! {"ph" => &scope, "ps" => t!(gap, "cc0", rel, "wbr"), "ch" => t!(scaled, at_zero, rel, "wbr")},
            &[below, &turn],
        );
        let c = w.e.coefficient(&self.ask(&w.spec), &whole_q);
        let law = self.b.ap("mul01", &binds! {"A" => numeral}, &[]);
        let zeroed = self.b.ap(
            "syl",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cc", "wcel"), "ch" => t!(at_zero, "cc0", "wceq")},
            &[&c, &law],
        );
        self.b.ap(
            "breqtrd",
            &binds! {"ph" => &scope, "A" => &scaled, "B" => &at_zero, "C" => "cc0", "R" => rel},
            &[&moved, &zeroed],
        )
    }

    /// ( scope -> span R 0 ) from ( scope -> ( n x. span ) R 0 ), n > 0.
    #[allow(clippy::too_many_arguments)]
    fn unscaled(
        &mut self,
        w: &mut Work,
        span: &Rpn,
        span_real: &Proof,
        numeral: &Rpn,
        whole: &BigInt,
        rel: &str,
        reached: &Proof,
    ) -> Proof {
        let scope = w.spec.scope.clone();
        let lemma = if rel == "clt" { "ltmul2" } else { "lemul2" };
        let scaled = t!(numeral, span, "cmul", "co");
        let at_zero = t!(numeral, "cc0", "cmul", "co");
        let whole_q = Q::from_integer(whole.clone());
        let rn = self.real_numeral(&scope, &whole_q);
        let pos = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", numeral, "clt", "wbr"), "ps" => &scope},
            &[&numerals::pos(&self.b, whole.magnitude().clone())],
        );
        let positive = self.b.ap(
            "jca",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cr", "wcel"), "ch" => t!("cc0", numeral, "clt", "wbr")},
            &[&rn, &pos],
        );
        let c = w.e.coefficient(&self.ask(&w.spec), &whole_q);
        let law = self.b.ap("mul01", &binds! {"A" => numeral}, &[]);
        let zeroed = self.b.ap(
            "syl",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cc", "wcel"), "ch" => t!(at_zero, "cc0", "wceq")},
            &[&c, &law],
        );
        let at = self.b.ap(
            "breqtrrd",
            &binds! {"ph" => &scope, "A" => &scaled, "B" => "cc0", "C" => &at_zero, "R" => rel},
            &[reached, &zeroed],
        );
        let zero = self.closed_law(&t!("cc0", "cr", "wcel"), "0re", &scope);
        let law = self.b.ap(
            lemma,
            &binds! {"A" => span, "B" => "cc0", "C" => numeral},
            &[],
        );
        let turn = self.b.ap(
            "syl3anc",
            &binds! {"ph" => &scope, "ps" => t!(span, "cr", "wcel"), "ch" => t!("cc0", "cr", "wcel"),
            "th" => t!(t!(numeral, "cr", "wcel"), t!("cc0", numeral, "clt", "wbr"), "wa"),
            "ta" => t!(t!(span, "cc0", rel, "wbr"), t!(scaled, at_zero, rel, "wbr"), "wb")},
            &[span_real, &zero, &positive, &law],
        );
        self.b.ap(
            "mpbird",
            &binds! {"ph" => &scope, "ps" => t!(span, "cc0", rel, "wbr"), "ch" => t!(scaled, at_zero, rel, "wbr")},
            &[&at, &turn],
        )
    }

    /// (−n, True, ( scope -> -u n < 0 ), ( scope -> -u n e. RR )), the
    /// number a combination leaves over, as a closed numeral fact.
    fn number_below(&self, scope: &Rpn, value: &Q) -> Route<Against> {
        if !value.is_integer() || !value.is_positive() {
            return Route::no(format!(
                "{} is not a positive whole number",
                super::normal::show(value)
            ));
        }
        let whole = value.to_integer();
        let numeral = numerals::spell(whole.magnitude().clone());
        let numeral = &numeral;
        let real = self.real_numeral(scope, value);
        let positive = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", numeral, "clt", "wbr"), "ps" => scope},
            &[&numerals::pos(&self.b, whole.magnitude().clone())],
        );
        let negated = t!(numeral, "cneg");
        let turn = self.b.ap(
            "lt0neg2d",
            &binds! {"ph" => scope, "A" => numeral},
            &[&real],
        );
        let below = self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!("cc0", numeral, "clt", "wbr"), "ch" => t!(negated, "cc0", "clt", "wbr")},
            &[&positive, &turn],
        );
        let neg_real = self.b.ap(
            "renegcld",
            &binds! {"ph" => scope, "A" => numeral},
            &[&real],
        );
        Built(Against {
            term: negated,
            strict: true,
            below,
            real: neg_real,
        })
    }

    /// Two terms against zero added, strict where either is.
    fn added_pair(&self, scope: &Rpn, one: &Against, other: &Against) -> Against {
        let (a, sa, pa, ra) = (&one.term, &one.strict, &one.below, &one.real);
        let (b, sb, pb, rb) = (&other.term, &other.strict, &other.below, &other.real);
        let rel_a = if *sa { "clt" } else { "cle" };
        let rel_b = if *sb { "clt" } else { "cle" };
        let lemma = rules::adding(*sa, *sb).closed;
        let rel = if *sa || *sb { "clt" } else { "cle" };
        let total = t!(a, b, "caddc", "co");
        let sum_zero = t!("cc0", "cc0", "caddc", "co");
        let zero = self.closed_law(&t!("cc0", "cr", "wcel"), "0re", scope);
        let each = t!(t!(a, "cc0", rel_a, "wbr"), t!(b, "cc0", rel_b, "wbr"), "wa");
        let reals = t!(t!(a, "cr", "wcel"), t!(b, "cr", "wcel"), "wa");
        let zeros = t!(t!("cc0", "cr", "wcel"), t!("cc0", "cr", "wcel"), "wa");
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(a, "cc0", rel_a, "wbr"), "ch" => t!(b, "cc0", rel_b, "wbr")},
            &[pa, pb],
        );
        let real_pair = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(a, "cr", "wcel"), "ch" => t!(b, "cr", "wcel")},
            &[ra, rb],
        );
        let zero_pair = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!("cc0", "cr", "wcel"), "ch" => t!("cc0", "cr", "wcel")},
            &[&zero, &zero],
        );
        let asks = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => &reals, "ch" => &zeros},
            &[&real_pair, &zero_pair],
        );
        let law = self.b.ap(
            lemma,
            &binds! {"A" => a, "B" => b, "C" => "cc0", "D" => "cc0"},
            &[],
        );
        let lifted = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(reals, zeros, "wa"), "ch" => t!(each, t!(total, sum_zero, rel, "wbr"), "wi")},
            &[&asks, &law],
        );
        let added = self.b.ap(
            "mpd",
            &binds! {"ph" => scope, "ps" => &each, "ch" => t!(total, sum_zero, rel, "wbr")},
            &[&both, &lifted],
        );
        let naught = self.closed_law(&t!(sum_zero, "cc0", "wceq"), "00id", scope);
        let below = self.b.ap(
            "breqtrd",
            &binds! {"ph" => scope, "A" => &total, "B" => &sum_zero, "C" => "cc0", "R" => rel},
            &[&added, &naught],
        );
        let real = self.b.ap(
            "readdcld",
            &binds! {"ph" => scope, "A" => a, "B" => b},
            &[ra, rb],
        );
        Against {
            term: total,
            strict: *sa || *sb,
            below,
            real,
        }
    }

    /// An equation from the two bounds that close on it: a number neither
    /// greater nor smaller than another is that number (`letri3`).
    fn by_antisymmetry(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let Some((a, b, how)) = order_sides(goal) else {
            return Ok(None);
        };
        if how != "=" {
            return Ok(None);
        }
        let (a, b) = (self.rpn(&a), self.rpn(&b));
        let (up, down) = (t!(a, b, "cle", "wbr"), t!(b, a, "cle", "wbr"));
        let (Some(pu), Some(pd)) = (
            self.held(facts, &up, scope)?,
            self.held(facts, &down, scope)?,
        ) else {
            return Ok(None);
        };
        self.joined_bounds(&a, &b, pu, pd, goal, scope, facts)
            .map(Some)
    }

    /// An equation claim that is a split of its own: the claim denied is
    /// two terms differing, so it is shown as the two bounds it is made of,
    /// each held or proved by the method from what the step cites, and
    /// joined by `letri3`.
    #[allow(clippy::too_many_arguments)]
    fn both_bounds(
        &mut self,
        refs: &[String],
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        let goal = self.to_term(term);
        let Some((a, b, how)) = order_sides(&goal) else {
            return Ok(Route::no("the claim states no relation"));
        };
        if how != "=" {
            return Ok(Route::no("what splits is the claim, and it is no equation"));
        }
        let (a, b) = (self.rpn(&a), self.rpn(&b));
        let mut halves = Vec::new();
        for half in [t!(a, b, "cle", "wbr"), t!(b, a, "cle", "wbr")] {
            halves.push(match self.held(facts, &half, scope)? {
                Some(p) => p,
                None => {
                    take!(self.prove_order(refs, &half, scope, facts, lines, skip)?)
                }
            });
        }
        let pd = halves.pop().expect("two halves");
        let pu = halves.pop().expect("two halves");
        self.joined_bounds(&a, &b, pu, pd, &goal, scope, facts)
            .map(Built)
    }

    /// ( scope -> a = b ) from ( scope -> a <_ b ) and ( scope -> b <_ a ).
    #[allow(clippy::too_many_arguments)]
    fn joined_bounds(
        &mut self,
        a: &Rpn,
        b: &Rpn,
        pu: Proof,
        pd: Proof,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let (up, down) = (t!(a, b, "cle", "wbr"), t!(b, a, "cle", "wbr"));
        let both = t!(up, down, "wa");
        let paired = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => &up, "ch" => &down},
            &[&pu, &pd],
        );
        let ra = self.membership(a, "cr", scope, facts)?;
        let rb = self.membership(b, "cr", scope, facts)?;
        let law = self.b.ap("letri3", &binds! {"A" => a, "B" => b}, &[]);
        let g = self.rpn(goal);
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(a, "cr", "wcel"), "ch" => t!(b, "cr", "wcel"), "th" => t!(g, both, "wb")},
            &[&ra, &rb, &law],
        );
        Ok(self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &g, "ch" => &both},
            &[&paired, &turn],
        ))
    }

    /// A claim denying a relation, as the relation that holds instead,
    /// proved first and turned round by `ltnle` or `lenlt`.
    #[allow(clippy::too_many_arguments)]
    fn negated_order(
        &mut self,
        goal: &Term,
        refs: &[String],
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        let Some((a, b, how)) =
            order_sides(&goal.children()[0]).filter(|s| s.2 == "<" || s.2 == "<=")
        else {
            return Ok(Route::no("what is denied states no relation"));
        };
        let (a, b) = (self.rpn(&a), self.rpn(&b));
        let (turns, rel) = if how == "<=" {
            ("ltnle", "clt")
        } else {
            ("lenlt", "cle")
        };
        let instead = t!(b, a, rel, "wbr");
        let held = match self.held(facts, &instead, scope)? {
            Some(p) => p,
            None => take!(self.prove_order(refs, &instead, scope, facts, lines, skip)?),
        };
        let rb = self.membership(&b, "cr", scope, facts)?;
        let ra = self.membership(&a, "cr", scope, facts)?;
        let law = self.b.ap(turns, &binds! {"A" => &b, "B" => &a}, &[]);
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(b, "cr", "wcel"), "ch" => t!(a, "cr", "wcel"), "th" => t!(instead, term, "wb")},
            &[&rb, &ra, &law],
        );
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => &instead, "ch" => term},
            &[&held, &turn],
        )))
    }

    /// A claim proved twice, once each side of a cited disequality: each side
    /// is the same claim at a scope one wider, with the side's bound standing
    /// as a line of its own, and `mpjaodan` puts the two back together.
    #[allow(clippy::too_many_arguments)]
    fn either_way(
        &mut self,
        found: &Certificate,
        refs: &[String],
        where_: &[(String, Term)],
        given: &[linear::Fact],
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        let Certificate::Either { at: which, .. } = found else {
            unreachable!("a certificate that splits");
        };
        if *which >= given.len() {
            return self.both_bounds(refs, term, scope, facts, lines, skip);
        }
        let (r, said) = where_[*which].clone();
        if said.variable().is_some()
            || said.label() != Some("wn")
            || said.children()[0].label() != Some("wceq")
        {
            return Ok(Route::no("what splits is not a denied equation"));
        }
        let pair = said.children()[0].clone();
        let (a, b) = (self.rpn(&pair.children()[0]), self.rpn(&pair.children()[1]));
        let (below, above) = (t!(a, b, "clt", "wbr"), t!(b, a, "clt", "wbr"));
        let given_fact = take!(self.cited_fact(&r, &said, scope, facts, lines)?);
        let turned = self.b.ap(
            "neqned",
            &binds! {"ph" => scope, "A" => &a, "B" => &b},
            &[&given_fact],
        );
        let ra = self.membership(&a, "cr", scope, facts)?;
        let rb = self.membership(&b, "cr", scope, facts)?;
        let law = self.b.ap("lttri2", &binds! {"A" => &a, "B" => &b}, &[]);
        let split = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(a, "cr", "wcel"), "ch" => t!(b, "cr", "wcel"),
            "th" => t!(t!(a, b, "wne"), t!(below, above, "wo"), "wb")},
            &[&ra, &rb, &law],
        );
        let whether = self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(a, b, "wne"), "ch" => t!(below, above, "wo")},
            &[&turned, &split],
        );
        let said_rpn = self.rpn(&said);
        let sides = self.frames_kept(|me| -> Checked<Route<Vec<Proof>>> {
            let mut sides = Vec::new();
            for bound in [&below, &above] {
                let (inner, lifted) = me.widen(scope, facts, bound, None);
                let proof = me
                    .held(&lifted, bound, &inner)?
                    .expect("the bound just laid down");
                // The bound stands as a line named by its own text.
                let name = bound.to_string();
                let held = lines.copy();
                held.set(name.clone(), Line::new(bound.clone(), proof, Vec::new()));
                let mut more = refs.to_vec();
                more.push(name);
                let mut skipped = skip.to_vec();
                skipped.push(said_rpn.clone());
                let side = take!(
                    me.one_way(bound, term, &inner, &lifted, &held, &more, &skipped)?
                );
                sides.push(side);
            }
            Ok(Built(sides))
        })?;
        let sides = take!(sides);
        Ok(Built(self.b.ap(
            "mpjaodan",
            &binds! {"ph" => scope, "ps" => &below, "ch" => term, "th" => &above},
            &[&sides[0], &sides[1], &whether],
        )))
    }

    /// One side of a split, at the scope that side opened: the side's own
    /// bound may be the claim, the claim may follow from the bound and what
    /// is cited, or the bound may contradict what is cited.
    #[allow(clippy::too_many_arguments)]
    fn one_way(
        &mut self,
        bound: &Rpn,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        refs: &[String],
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        if let Some(p) = self.held(facts, term, scope)? {
            return Ok(Built(p));
        }
        let found = self.prove_order(refs, term, scope, facts, lines, skip)?;
        if !found.is_declined() {
            return Ok(found);
        }
        self.impossible(bound, term, scope, facts, lines, refs, skip)
    }

    /// The claim, because the bound this scope opened cannot hold: `lenlt`
    /// says a ≤ b and b < a deny each other, and what denies the bound is
    /// held already or follows from what the step cites.
    #[allow(clippy::too_many_arguments)]
    fn impossible(
        &mut self,
        bound: &Rpn,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        refs: &[String],
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        let node = self.to_term(bound);
        let Some((low, high, _)) = order_sides(&node).filter(|s| s.2 == "<") else {
            return Ok(Route::no("the bound states no strict order"));
        };
        let (low, high) = (self.rpn(&low), self.rpn(&high));
        let denies = t!(high, low, "cle", "wbr");
        let held = match self.held(facts, &denies, scope)? {
            Some(p) => p,
            None => {
                // The bound's line is named by its text (`either_way`).
                let name = bound.to_string();
                let cited: Vec<String> =
                    refs.iter().filter(|r| **r != name).cloned().collect();
                take!(self.prove_order(&cited, &denies, scope, facts, lines, skip)?)
            }
        };
        let rh = self.membership(&high, "cr", scope, facts)?;
        let rl = self.membership(&low, "cr", scope, facts)?;
        let law = self.b.ap("lenlt", &binds! {"A" => &high, "B" => &low}, &[]);
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(high, "cr", "wcel"), "ch" => t!(low, "cr", "wcel"),
            "th" => t!(denies, t!(bound, "wn"), "wb")},
            &[&rh, &rl, &law],
        );
        let refuted = self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => &denies, "ch" => t!(bound, "wn")},
            &[&held, &turn],
        );
        let supposed = self
            .held(facts, bound, scope)?
            .expect("the bound this scope opened");
        Ok(Built(self.b.ap(
            "pm2.21dd",
            &binds! {"ph" => scope, "ps" => bound, "ch" => term},
            &[&supposed, &refuted],
        )))
    }

    /// Two things the step says are not equal, because one is below: where
    /// the contradiction is with a single strict bound between the very two
    /// the claim names, the whole argument is `ltne`.
    #[allow(clippy::too_many_arguments)]
    fn stays_apart(
        &mut self,
        used: &[usize],
        given: &[linear::Fact],
        where_: &[(String, Term)],
        claim: &linear::Fact,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if used.len() != 1 || given[used[0]].how != How::Lt {
            return Ok(Route::no("not one strict bound"));
        }
        let (r, said) = where_[used[0]].clone();
        let Some(_) = order_sides(&said).filter(|s| s.2 == "<") else {
            return Ok(Route::no("the cited bound is not stated as one"));
        };
        let below: Vec<Rpn> =
            said.children()[..2].iter().map(|c| self.rpn(c)).collect();
        // The claim must be about the two the bound is about, and no more.
        let left_over = claim.side.minus(&given[used[0]].side.scaled(&q(-1)));
        if !left_over.atoms().is_empty() || !left_over.constant.is_zero() {
            return Ok(Route::no("the claim is not that bound turned"));
        }
        // And written as the two of them: `b − a ≠ 0` is the same bound
        // turned, and another statement, which the order proves.
        if self.rpn(goal) != t!(t!(below[1], below[0], "wceq"), "wn") {
            return Ok(Route::no("the claim is not the two the bound names"));
        }
        let bound = take!(self.cited_fact(&r, &said, scope, facts, lines)?);
        let real = self.membership(&below[0], "cr", scope, facts)?;
        let law = self
            .b
            .ap("ltne", &binds! {"A" => &below[0], "B" => &below[1]}, &[]);
        let apart = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(below[0], "cr", "wcel"), "ch" => t!(below[0], below[1], "clt", "wbr"),
            "th" => t!(below[1], below[0], "wne")},
            &[&real, &bound, &law],
        );
        Ok(Built(self.b.ap(
            "neneqd",
            &binds! {"ph" => scope, "A" => &below[1], "B" => &below[0]},
            &[&apart],
        )))
    }

    /// One cited fact, scaled, as a term that is at most zero: an equation is
    /// at most zero because it is zero exactly; an inequality already is,
    /// and scaling it by something positive leaves it so.
    fn at_most_zero(
        &mut self,
        w: &mut Work,
        said: &Term,
        times: &Q,
        given: Proof,
        facts: &Facts,
    ) -> Checked<Route<(Rpn, Proof, Proof)>> {
        let scope = w.spec.scope.clone();
        let (mut said, mut given) = (said.clone(), given);
        if said.variable().is_none()
            && said.label() == Some("wn")
            && said.children().len() == 1
        {
            let (turned, proof) =
                take!(self.unnegated(&scope, &said.children()[0], &given, facts)?);
            said = turned;
            given = proof;
        }
        let Some((_, _, rel)) = order_sides(&said) else {
            return Ok(Route::no("a cited fact states no relation"));
        };
        let was: Vec<Rpn> = said.children()[..2].iter().map(|c| self.rpn(c)).collect();
        let gap = t!(was[0], was[1], "cmin", "co");
        let r0 = self.membership(&was[0], "cr", &scope, facts)?;
        let r1 = self.membership(&was[1], "cr", &scope, facts)?;
        let law = self
            .b
            .ap("resubcl", &binds! {"A" => &was[0], "B" => &was[1]}, &[]);
        let real = self.b.ap(
            "syl2anc",
            &binds! {"ph" => &scope, "ps" => t!(was[0], "cr", "wcel"), "ch" => t!(was[1], "cr", "wcel"), "th" => t!(gap, "cr", "wcel")},
            &[&r0, &r1, &law],
        );
        let Some(numeral) = field::spell_coefficient(times) else {
            return Ok(Route::no(format!(
                "{} is not a whole number",
                super::normal::show(times)
            )));
        };
        let scaled = t!(numeral, gap, "cmul", "co");
        let rn = self.real_numeral(&scope, times);
        let law = self
            .b
            .ap("remulcl", &binds! {"A" => &numeral, "B" => &gap}, &[]);
        let scaled_real = self.b.ap(
            "syl2anc",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cr", "wcel"), "ch" => t!(gap, "cr", "wcel"), "th" => t!(scaled, "cr", "wcel")},
            &[&rn, &real, &law],
        );
        let at_zero = t!(numeral, "cc0", "cmul", "co");
        if rel == "=" {
            let zeroed = self.difference_zero(w, &was, &given)?;
            let lifted = self.b.ap(
                "oveq2d",
                &binds! {"ph" => &scope, "A" => &gap, "B" => "cc0", "C" => &numeral, "F" => "cmul"},
                &[&zeroed],
            );
            let c = w.e.coefficient(&self.ask(&w.spec), times);
            let law = self.b.ap("mul01", &binds! {"A" => &numeral}, &[]);
            let naught = self.b.ap(
                "syl",
                &binds! {"ph" => &scope, "ps" => t!(numeral, "cc", "wcel"), "ch" => t!(at_zero, "cc0", "wceq")},
                &[&c, &law],
            );
            let vanishes = w.e.chain(
                &self.ask(&w.spec),
                &lifted,
                &naught,
                &scaled,
                &at_zero,
                &t!("cc0"),
            );
            let below = self.b.ap(
                "eqled",
                &binds! {"ph" => &scope, "A" => &scaled, "B" => "cc0"},
                &[&scaled_real, &vanishes],
            );
            return Ok(Built((scaled, below, scaled_real)));
        }
        if rel == "<" {
            // A sum that lands on `at most` has no use for the strictness, so
            // it is given up here and the one case below serves both.
            let r0 = self.membership(&was[0], "cr", &scope, facts)?;
            let r1 = self.membership(&was[1], "cr", &scope, facts)?;
            given = self.b.ap(
                "ltled",
                &binds! {"ph" => &scope, "A" => &was[0], "B" => &was[1]},
                &[&r0, &r1, &given],
            );
        } else if rel != "<=" {
            return Ok(Route::no(format!("a cited {rel} is not written")));
        }
        let bound = self.difference_le(&scope, &was, &given, facts)?;
        if times.is_one() {
            return Ok(Built((gap, bound, real)));
        }
        if !times.is_positive() {
            return Ok(Route::no("a bound may only be scaled upward"));
        }
        let zero = self.closed_law(&t!("cc0", "cr", "wcel"), "0re", &scope);
        let rn = self.real_numeral(&scope, times);
        let pos = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", numeral, "clt", "wbr"), "ps" => &scope},
            &[&numerals::pos(&self.b, times.numer().magnitude().clone())],
        );
        let positive = self.b.ap(
            "jca",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cr", "wcel"), "ch" => t!("cc0", numeral, "clt", "wbr")},
            &[&rn, &pos],
        );
        let law = self.b.ap(
            "lemul2",
            &binds! {"A" => &gap, "B" => "cc0", "C" => &numeral},
            &[],
        );
        let turn = self.b.ap(
            "syl3anc",
            &binds! {"ph" => &scope, "ps" => t!(gap, "cr", "wcel"), "ch" => t!("cc0", "cr", "wcel"),
            "th" => t!(t!(numeral, "cr", "wcel"), t!("cc0", numeral, "clt", "wbr"), "wa"),
            "ta" => t!(t!(gap, "cc0", "cle", "wbr"), t!(scaled, at_zero, "cle", "wbr"), "wb")},
            &[&real, &zero, &positive, &law],
        );
        let moved = self.b.ap(
            "mpbid",
            &binds! {"ph" => &scope, "ps" => t!(gap, "cc0", "cle", "wbr"), "ch" => t!(scaled, at_zero, "cle", "wbr")},
            &[&bound, &turn],
        );
        let c = w.e.coefficient(&self.ask(&w.spec), times);
        let law = self.b.ap("mul01", &binds! {"A" => &numeral}, &[]);
        let naught = self.b.ap(
            "syl",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cc", "wcel"), "ch" => t!(at_zero, "cc0", "wceq")},
            &[&c, &law],
        );
        let below = self.b.ap(
            "breqtrd",
            &binds! {"ph" => &scope, "A" => &scaled, "B" => &at_zero, "C" => "cc0", "R" => "cle"},
            &[&moved, &naught],
        );
        Ok(Built((scaled, below, scaled_real)))
    }

    /// A cited fact stated as a denial, said the other way round: `lenlt`
    /// and `ltnle` say a denied `<` or `≤` is the other relation turned.
    fn unnegated(
        &mut self,
        scope: &Rpn,
        inner: &Term,
        given: &Proof,
        facts: &Facts,
    ) -> Checked<Route<(Term, Proof)>> {
        let found =
            order_sides(inner).and_then(|s| lookup(rules::DENIED, s.2).map(|d| (s, d)));
        let Some((_sides, (denied, said, lemma))) = found else {
            return Ok(Route::no("only a denied `<` or `≤` is turned round"));
        };
        let was: Vec<Rpn> = inner.children()[..2].iter().map(|c| self.rpn(c)).collect();
        let turned = self.to_term(&t!(was[1], was[0], said, "wbr"));
        let r1 = self.membership(&was[1], "cr", scope, facts)?;
        let r0 = self.membership(&was[0], "cr", scope, facts)?;
        let law = self
            .b
            .ap(lemma, &binds! {"A" => &was[1], "B" => &was[0]}, &[]);
        let holds = t!(was[1], was[0], said, "wbr");
        let not_held = t!(t!(was[0], was[1], denied, "wbr"), "wn");
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(was[1], "cr", "wcel"), "ch" => t!(was[0], "cr", "wcel"),
            "th" => t!(holds, not_held, "wb")},
            &[&r1, &r0, &law],
        );
        Ok(Built((
            turned,
            self.b.ap(
                "mpbird",
                &binds! {"ph" => scope, "ps" => &holds, "ch" => &not_held},
                &[given, &turn],
            ),
        )))
    }

    /// The proof of one fact a cited line states: a line may say several
    /// things at once, and what the step uses is one of them.
    pub fn cited_fact(
        &mut self,
        r: &str,
        said: &Term,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let want = self.rpn(said);
        let held = self.carried(r, facts, lines);
        let term = self
            .line_written(r, lines)
            .map(|l| l.claim)
            .unwrap_or_default();
        if term == want {
            return Ok(Built(held));
        }
        let known = facts.copy();
        self.unpack_all(&term, &held, scope, &known);
        if let Some(p) = self.held(&known, &want, scope)? {
            return Ok(Built(p));
        }
        // A bound the line's membership implies, read off what the line
        // states and nothing else in scope.
        for (s, proof) in self.stated_by(r, scope, &known, lines)? {
            let proof = if s == term { Some(held.clone()) } else { proof };
            let Some(proof) = proof else {
                continue;
            };
            let more = self.implied(&s, &proof, scope, &known)?;
            if let Some(p) = self.held(&more, &want, scope)? {
                return Ok(Built(p));
            }
        }
        Ok(Route::no("that line does not reach the fact"))
    }

    /// ( scope -> ( A - B ) <_ 0 ) from a cited A <_ B.
    fn difference_le(
        &mut self,
        scope: &Rpn,
        was: &[Rpn],
        given: &Proof,
        facts: &Facts,
    ) -> Checked<Proof> {
        let gap = t!(was[0], was[1], "cmin", "co");
        let r0 = self.membership(&was[0], "cr", scope, facts)?;
        let r1 = self.membership(&was[1], "cr", scope, facts)?;
        let law = self
            .b
            .ap("suble0", &binds! {"A" => &was[0], "B" => &was[1]}, &[]);
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(was[0], "cr", "wcel"), "ch" => t!(was[1], "cr", "wcel"),
            "th" => t!(t!(gap, "cc0", "cle", "wbr"), t!(was[0], was[1], "cle", "wbr"), "wb")},
            &[&r0, &r1, &law],
        );
        Ok(self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => t!(gap, "cc0", "cle", "wbr"), "ch" => t!(was[0], was[1], "cle", "wbr")},
            &[given, &turn],
        ))
    }

    /// The claim as one cited equation, scaled: an equation may be
    /// multiplied by anything, which is what lets one cited equation carry a
    /// claim on its own.
    #[allow(clippy::too_many_arguments)]
    fn one_equation_scaled(
        &mut self,
        cited: &(String, Term),
        times: &Q,
        left: &Rpn,
        right: &Rpn,
        how: &str,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let (r, said) = cited;
        let Some(_) = order_sides(said).filter(|s| s.2 == "=") else {
            return Ok(Route::no("the cited fact is not an equation"));
        };
        let Some(numeral) = field::spell_coefficient(times) else {
            return Ok(Route::no(format!(
                "{} is not a whole number",
                super::normal::show(times)
            )));
        };
        let mut w = Work::plain(scope, facts);
        let was: Vec<Rpn> = said.children().iter().map(|c| self.rpn(c)).collect();
        let gap = t!(was[0], was[1], "cmin", "co");
        let scaled = t!(numeral, gap, "cmul", "co");
        let span = t!(left, right, "cmin", "co");
        let alike = self.same_polynomial(&mut w, &span, &scaled)?;
        let stated = self.cited_fact(r, said, scope, facts, lines)?;
        let (alike, stated) = (take!(alike), take!(stated));
        let zeroed = self.difference_zero(&mut w, &was, &stated)?;
        let lifted = self.b.ap(
            "oveq2d",
            &binds! {"ph" => scope, "A" => &gap, "B" => "cc0", "C" => &numeral, "F" => "cmul"},
            &[&zeroed],
        );
        let c = w.e.coefficient(&self.ask(&w.spec), times);
        let law = self.b.ap("mul01", &binds! {"A" => &numeral}, &[]);
        let at_zero = t!(numeral, "cc0", "cmul", "co");
        let naught = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(numeral, "cc", "wcel"), "ch" => t!(at_zero, "cc0", "wceq")},
            &[&c, &law],
        );
        let inner = w.e.chain(
            &self.ask(&w.spec),
            &lifted,
            &naught,
            &scaled,
            &at_zero,
            &t!("cc0"),
        );
        let reached = w.e.chain(
            &self.ask(&w.spec),
            &alike,
            &inner,
            &span,
            &scaled,
            &t!("cc0"),
        );
        if how == "=" {
            let cl = self.membership(left, "cc", scope, facts)?;
            let cr = self.membership(right, "cc", scope, facts)?;
            let law = self
                .b
                .ap("subeq0", &binds! {"A" => left, "B" => right}, &[]);
            let turn = self.b.ap(
                "syl2anc",
                &binds! {"ph" => scope, "ps" => t!(left, "cc", "wcel"), "ch" => t!(right, "cc", "wcel"),
                "th" => t!(t!(span, "cc0", "wceq"), t!(left, right, "wceq"), "wb")},
                &[&cl, &cr, &law],
            );
            return Ok(Built(self.b.ap(
                "mpbid",
                &binds! {"ph" => scope, "ps" => t!(span, "cc0", "wceq"), "ch" => t!(left, right, "wceq")},
                &[&reached, &turn],
            )));
        }
        if how != "<=" {
            return Ok(Route::no(format!("a {how} conclusion is not written")));
        }
        // A difference that is zero is at most zero.
        let rl = self.membership(left, "cr", scope, facts)?;
        let rr = self.membership(right, "cr", scope, facts)?;
        let law = self
            .b
            .ap("resubcl", &binds! {"A" => left, "B" => right}, &[]);
        let real = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(left, "cr", "wcel"), "ch" => t!(right, "cr", "wcel"), "th" => t!(span, "cr", "wcel")},
            &[&rl, &rr, &law],
        );
        let at_most = self.b.ap(
            "eqled",
            &binds! {"ph" => scope, "A" => &span, "B" => "cc0"},
            &[&real, &reached],
        );
        // A difference at most zero is what `<_` says of the two sides.
        let rl = self.membership(left, "cr", scope, facts)?;
        let rr = self.membership(right, "cr", scope, facts)?;
        let law = self
            .b
            .ap("suble0", &binds! {"A" => left, "B" => right}, &[]);
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(left, "cr", "wcel"), "ch" => t!(right, "cr", "wcel"),
            "th" => t!(t!(span, "cc0", "cle", "wbr"), t!(left, right, "cle", "wbr"), "wb")},
            &[&rl, &rr, &law],
        );
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(span, "cc0", "cle", "wbr"), "ch" => t!(left, right, "cle", "wbr")},
            &[&at_most, &turn],
        )))
    }

    /// ( scope -> ( A - B ) = 0 ) from a cited A = B.
    fn difference_zero(
        &mut self,
        w: &mut Work,
        was: &[Rpn],
        given: &Proof,
    ) -> Checked<Proof> {
        let scope = w.spec.scope.clone();
        let a0 = self.membership(&was[0], "cc", &scope, &w.spec.facts.clone())?;
        let a1 = self.membership(&was[1], "cc", &scope, &w.spec.facts.clone())?;
        let gap = t!(was[0], was[1], "cmin", "co");
        let law = self
            .b
            .ap("subeq0", &binds! {"A" => &was[0], "B" => &was[1]}, &[]);
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => &scope, "ps" => t!(was[0], "cc", "wcel"), "ch" => t!(was[1], "cc", "wcel"),
            "th" => t!(t!(gap, "cc0", "wceq"), t!(was[0], was[1], "wceq"), "wb")},
            &[&a0, &a1, &law],
        );
        Ok(self.b.ap(
            "mpbird",
            &binds! {"ph" => &scope, "ps" => t!(gap, "cc0", "wceq"), "ch" => t!(was[0], was[1], "wceq")},
            &[given, &turn],
        ))
    }
}
