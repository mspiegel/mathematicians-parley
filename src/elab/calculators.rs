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

use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::IndexMap;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::field::{self, numeral as n, q, Poly, Verdict, Q};
use super::linear::{self, Certificate, How};
use super::normal::{Emitter, Oracle, Quotiented, Run};
use super::numerals;
use super::provenance::requirement;
use super::state::{Elaborator, Vars};
use super::{Facts, Line, Lines};
use crate::binds;
use crate::corpus::{fmt, Step};
use crate::mm::kernel::Term;
use crate::mm::spell::{Builder, Proof};
use crate::outcome::{Built, Checked, Declined, Problem, Route};
use crate::rules::{self, lookup};
use crate::{pf, t, take};

/// What an emitter asks of the elaborator: the scope, the facts a
/// membership is answered from, whether it may search for a term not being
/// zero, and what the page says of that.
#[derive(Clone)]
pub struct Spec {
    pub scope: String,
    pub facts: Facts,
    pub apart: bool,
    pub written: Option<Facts>,
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
    pub fn plain(scope: &str, facts: &Facts) -> Work {
        Work::new(Spec {
            scope: scope.to_string(),
            facts: facts.clone(),
            apart: false,
            written: None,
        })
    }
}

/// The elaborator answering an emitter, for as long as one call.
pub struct Ask<'e, 'a> {
    el: &'e mut Elaborator<'a>,
    spec: &'e Spec,
}

impl Oracle for Ask<'_, '_> {
    fn b(&self) -> &Builder {
        &self.el.b
    }

    fn atom(&mut self, said: &str) -> Checked<Proof> {
        // A sum a linear reading wrote is a number because its terms are,
        // as `membership` builds any sum (`summed`).
        let key = (self.spec.scope.clone(), said.to_string());
        if let Some(p) = self.el.sums_in_cc.get(&key) {
            return Ok(p.clone());
        }
        let term = self.el.to_term(said);
        if term.variable().is_none() && term.label() == Some("csu") {
            let (scope, facts) = (self.spec.scope.clone(), self.spec.facts.clone());
            if let Built(p) = self.el.summed(&term, "cc", &scope, &facts, None)? {
                return Ok(p);
            }
        }
        self.el
            .membership(said, "cc", &self.spec.scope, &self.spec.facts)
    }

    fn apart(&mut self, said: &str) -> Checked<Proof> {
        self.el.not_zero(&self.spec.scope, &self.spec.facts, said)
    }

    fn written(&mut self, said: &str) -> Checked<Option<Proof>> {
        let facts = self.spec.written.clone().unwrap_or_default();
        self.el.written_nonzero(&self.spec.scope, &facts, said)
    }

    fn linear_sum(&mut self, said: &str) -> Checked<Route<(Term, Proof)>> {
        let Some(letter) = self.el.sum_letter.clone() else {
            return Ok(Route::no("a sum is one atom outside `algebra`"));
        };
        let (scope, facts) = (self.spec.scope.clone(), self.spec.facts.clone());
        self.el.linear_sum(said, &letter, &scope, &facts)
    }
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

/// The term a combination multiplies one cited equation by, or None: a
/// multiplier is written the short way, `-u q` rather than the canonical
/// `( -u 1 x. ( q ^ 1 ) )`.
pub fn multiplier(shape: &Poly, scale: &Q) -> Option<String> {
    if shape.terms.len() != 1 {
        return None;
    }
    let (monomial, weight) = shape.terms.iter().next()?;
    if !weight.is_one() {
        return None;
    }
    if monomial.is_empty() {
        return field::spell_coefficient(scale);
    }
    if monomial.len() != 1 || monomial[0].1 != 1 {
        return None;
    }
    let name = monomial[0].0.to_string();
    if scale.is_one() {
        return Some(name);
    }
    if *scale == q(-1) {
        return Some(t!(name, "cneg"));
    }
    let digit = field::spell_coefficient(scale)?;
    Some(t!(digit, name, "cmul", "co"))
}

/// What the cited polynomial is multiplied by to become the claim's: two
/// disequalities say one thing when one polynomial is the other scaled.
pub fn rescales(cited: Option<&Poly>, claim: Option<&Poly>) -> Option<Q> {
    let (cited, claim) = (cited?, claim?);
    if cited.terms.is_empty() || claim.terms.is_empty() {
        return None;
    }
    let lead = claim.lead()?;
    let theirs = cited.terms.get(lead)?;
    let times = &claim.terms[lead] / theirs;
    if times.is_zero() || *claim != cited.scaled(&times) {
        return None;
    }
    Some(times)
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
    term: String,
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
    term: String,
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
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let linear = self.sums_linear(term, Some(step), lines);
        field::reading_sums(linear, || self.decide_field(step, term, lines))?;
        let found = self.prove_field(Some(step), term, scope, facts, lines)?;
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
    pub fn sums_linear(&self, term: &str, step: Option<&Step>, lines: &Lines) -> bool {
        let labels = self.b.flabel.clone();
        let mut said = vec![self.to_term(term)];
        if let Some(step) = step {
            for r in &step.just.refs {
                if let Some(line) = lines.get(r) {
                    said.push(self.to_term(&line.term));
                }
            }
        }
        said.iter()
            .any(|t| field::says_something_linear(t, &labels))
    }

    pub fn prove_field(
        &mut self,
        step: Option<&Step>,
        term: &str,
        scope: &str,
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
                    if let Some(line) = lines.get(r) {
                        seen.push(self.to_term(&line.term));
                    }
                }
            }
            let refs: Vec<&Term> = seen.iter().collect();
            self.unheld(&refs).map(|v| self.rpn(&v))
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
        term: &str,
        scope: &str,
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
        self.combining(&[term.to_string()]);
        // A `requires` line is where a step says its denominator is not
        // zero, so what the normalizer is asked is asked of those as well.
        let facts = match step {
            Some(step) => self.supplied(Some(step), scope, facts)?,
            None => facts.clone(),
        };
        let mut w = Work::new(Spec {
            scope: scope.to_string(),
            facts: facts.clone(),
            apart: true,
            written: Some(facts.clone()),
        });
        if apart {
            return self.apart_from_cited(step, &goal, scope, &facts, lines, &mut w);
        }
        let left = self.rpn(&goal.children()[0]);
        let right = self.rpn(&goal.children()[1]);
        let mut declines = Vec::new();
        let found = self.same_polynomial(&mut w, &left, &right)?;
        match found {
            Built(p) => return Ok(Built(p)),
            Declined(d) => declines.push(self.say(&d)),
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
                    Declined(d) => declines.push(self.say(&d)),
                }
            }
        }
        Ok(Route::no(declines.join("; ")))
    }

    /// A disequality that is a cited one rescaled: the cited fact becomes a
    /// difference that is not zero, the two differences are shown to be one
    /// polynomial, and the claim's difference is not zero either. The scalar
    /// is 1 or −1.
    fn apart_from_cited(
        &mut self,
        step: Option<&Step>,
        goal: &Term,
        scope: &str,
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
            let Some(held) = lines.get(r) else {
                continue;
            };
            for said in self.parts(&held.term) {
                let node = self.to_term(&said);
                let cited = field::denied(&node, &labels);
                let scale = rescales(cited.as_ref(), claim.as_ref());
                let Some(scale) = scale.filter(|s| *s == q(1) || *s == q(-1)) else {
                    continue;
                };
                let pair = node.children()[0].clone();
                let (p, qq) =
                    (self.rpn(&pair.children()[0]), self.rpn(&pair.children()[1]));
                let mut gap = t!(p, qq, "cmin", "co");
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
        left: &str,
        right: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
        w: &mut Work,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let want = field::equation(&self.to_term(&t!(left, right, "wceq")), &labels);
        for r in &step.just.refs {
            let Some(held) = lines.get(r) else {
                continue;
            };
            let cited = self.to_term(&held.term);
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
            let Built(given) = self.cited_fact(r, &cited, scope, facts, lines)? else {
                continue;
            };
            let found = self.cleared(w, &cited, left, right, given)?;
            if !found.is_declined() {
                return Ok(found);
            }
        }
        Ok(Route::no("no cited equation is the claim divided"))
    }

    /// The cited equation with its denominators multiplied out.
    fn cleared(
        &mut self,
        w: &mut Work,
        cited: &Term,
        left: &str,
        right: &str,
        given: Proof,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let was: Vec<String> = cited.children().iter().map(|c| self.rpn(c)).collect();
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
        let pair = |x: &str| t!(t!(x, "cc", "wcel"), t!(x, "cc0", "wne"), "wa");
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
        let s1 = self.same_polynomial(w, left, &t!(a, d, "cmul", "co"))?;
        let s2 = self.same_polynomial(w, right, &t!(c, b, "cmul", "co"))?;
        let (s1, s2) = (take!(s1), take!(s2));
        Ok(Built(self.b.ap(
            "3eqtr4d",
            &binds! {"ph" => &u, "A" => t!(a, d, "cmul", "co"), "B" => t!(c, b, "cmul", "co"), "C" => left, "D" => right},
            &[&crossed, &s1, &s2],
        )))
    }

    /// What says a denominator is not zero, asked of the scope: the text
    /// writes these, so the fact is there to be found. `normal` asks this
    /// while writing a proof it has already decided, so a missing fact is a
    /// defect here and not a decline.
    pub fn not_zero(
        &mut self,
        scope: &str,
        facts: &Facts,
        said: &str,
    ) -> Checked<Proof> {
        if let Some(found) = self.written_nonzero(scope, facts, said)? {
            return Ok(found);
        }
        let want = t!(said, "cc0", "wne");
        match self.settle(&self.to_term(&want), scope, facts, 3, None, None)? {
            Built(p) => Ok(p),
            Declined(_) => Err(self.defect(
                self.at,
                format!(
                    "nothing says {}, which this step needs to divide by it",
                    self.render(&want)
                ),
            )),
        }
    }

    /// What the page says makes a term not zero, or None: `not_zero` without
    /// the search it falls back on.
    pub fn written_nonzero(
        &mut self,
        scope: &str,
        facts: &Facts,
        said: &str,
    ) -> Checked<Option<Proof>> {
        // Written either way round, and as ¬ said = 0 as well (`held`).
        let want = t!(said, "cc0", "wne");
        if let Some(p) = self.held(facts, &want, scope)? {
            return Ok(Some(p));
        }
        // Or a membership written that says it: N ∈ ℕ says N ≠ 0.
        for (fact, proof) in facts.entries() {
            let more = self.implied(&fact, &proof, scope, facts)?;
            if let Some(p) = self.held(&more, &want, scope)? {
                return Ok(Some(p));
            }
        }
        self.apart_as_written(said, scope, facts)
    }

    /// The same fact about the same denominator, spelt as the text spells
    /// it: what decides is the polynomial, and the equation carrying one
    /// spelling to the other is the normalizer's own.
    fn apart_as_written(
        &mut self,
        said: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let mut w = Work::plain(scope, facts);
        let labels = self.b.flabel.clone();
        for (fact, proof) in facts.entries() {
            let tail = fact.split_whitespace().last().unwrap_or("");
            if tail != "wne" && tail != "wn" {
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
            let subject = match (left == "cc0", right == "cc0") {
                (false, true) => sides[0].clone(),
                (true, false) => sides[1].clone(),
                _ => continue,
            };
            let was = self.rpn(&subject);
            if was == said {
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
            if Emitter::spell_run(&items) != said {
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
    fn same_polynomial(
        &mut self,
        w: &mut Work,
        left: &str,
        right: &str,
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
        left: &str,
        right: &str,
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
        let pair = |x: &str| t!(t!(x, "cc", "wcel"), t!(x, "cc0", "wne"), "wa");
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

    /// A claim the cited equations add up to: each cited equation is a
    /// difference that is zero, multiplied by what the combination says and
    /// still zero; the sum of them is zero, and that sum is the claim's own
    /// difference, which is the normalizer's question.
    #[allow(clippy::too_many_arguments)]
    fn summed_from_cited(
        &mut self,
        step: &Step,
        left: &str,
        right: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
        w: &mut Work,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let want = field::equation(&self.to_term(&t!(left, right, "wceq")), &labels);
        let mut given = Vec::new();
        let mut where_: Vec<(String, Term)> = Vec::new();
        for r in &step.just.refs {
            let Some(held) = lines.get(r) else {
                continue;
            };
            for said in self.parts(&held.term) {
                let node = self.to_term(&said);
                if let Some(one) = field::equation(&node, &labels) {
                    given.push(one);
                    where_.push((r.clone(), node));
                }
            }
        }
        let Some(want) = want.filter(|_| !given.is_empty()) else {
            return Ok(Route::no("the step cites no equation"));
        };
        let mut atoms: BTreeSet<Rc<str>> = BTreeSet::new();
        for p in given.iter().chain(std::iter::once(&want)) {
            for m in p.terms.keys() {
                atoms.extend(m.iter().map(|(a, _)| a.clone()));
            }
        }
        let atoms: Vec<Rc<str>> = atoms.into_iter().collect();
        let Some(how) = field::follows(&given, &want, &atoms).filter(|h| !h.is_empty())
        else {
            return Ok(Route::no("no sum of the cited equations is the claim"));
        };
        let mut combined = vec![t!(left, right, "wceq")];
        combined.extend(how.iter().map(|taken| self.rpn(&where_[taken.which].1)));
        self.combining(&combined);
        let mut pieces: Vec<(String, Proof)> = Vec::new();
        for taken in &how {
            let (r, node) = where_[taken.which].clone();
            let (a, b) = (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
            let gap = t!(a, b, "cmin", "co");
            let Some(times) = multiplier(&taken.shape, &taken.scale) else {
                return Ok(Route::no("a multiplier with no spelling"));
            };
            // A sum the decision read as linear is written over a placeholder
            // letter; in a proof it is the step's own (`sum_letter`).
            let times = match &self.sum_letter {
                Some(letter) => times
                    .split_whitespace()
                    .map(|t| if t == "§" { letter.as_str() } else { t })
                    .collect::<Vec<_>>()
                    .join(" "),
                None if times.split_whitespace().any(|t| t == "§") => {
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
            let piece = t!(times, gap, "cmul", "co");
            let moved = self.b.ap(
                "oveq2d",
                &binds! {"ph" => scope, "A" => &gap, "B" => "cc0", "C" => &times, "F" => "cmul"},
                &[&vanishes],
            );
            let atom = self.membership(
                &times,
                "cc",
                &w.spec.scope.clone(),
                &w.spec.facts.clone(),
            )?;
            let zero =
                self.b
                    .ap("mul01d", &binds! {"ph" => scope, "A" => &times}, &[&atom]);
            let proof = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &piece, "B" => t!(times, "cc0", "cmul", "co"), "C" => "cc0"},
                &[&moved, &zero],
            );
            pieces.push((piece, proof));
        }
        let (mut total, mut sums) = pieces[0].clone();
        let naught = t!("cc0", "cc0", "caddc", "co");
        for (piece, proof) in &pieces[1..] {
            let joined = t!(total, piece, "caddc", "co");
            let both = self.b.ap(
                "oveq12d",
                &binds! {"ph" => scope, "A" => &total, "B" => "cc0", "C" => piece, "D" => "cc0", "F" => "caddc"},
                &[&sums, proof],
            );
            let zero = self.b.ap(
                "a1i",
                &binds! {"ph" => t!(naught, "cc0", "wceq"), "ps" => scope},
                &[&self.step("00id")],
            );
            sums = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &joined, "B" => &naught, "C" => "cc0"},
                &[&both, &zero],
            );
            total = joined;
        }
        let whole = t!(left, right, "cmin", "co");
        let alike = self.same_polynomial(w, &total, &whole)?;
        let left_cc = self.in_cc(left, scope, facts)?;
        let right_cc = self.in_cc(right, scope, facts)?;
        let (alike, left_cc, right_cc) =
            (take!(alike), take!(left_cc), take!(right_cc));
        let reached = self.b.ap(
            "eqtr3d",
            &binds! {"ph" => scope, "A" => &total, "B" => &whole, "C" => "cc0"},
            &[&alike, &sums],
        );
        let turn = self.b.ap(
            "subeq0ad",
            &binds! {"ph" => scope, "A" => left, "B" => right},
            &[&left_cc, &right_cc],
        );
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(whole, "cc0", "wceq"), "ch" => t!(left, right, "wceq")},
            &[&reached, &turn],
        )))
    }

    /// ( scope -> said e. CC ), for a term of the step's own depth: built by
    /// `part` first, from the step's own lines, and searched for where that
    /// cannot, to the depth every side condition is searched to.
    fn in_cc(
        &mut self,
        said: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let found = self.part(said, "cc", scope, facts)?;
        if !found.is_declined() {
            return Ok(found);
        }
        self.within(said, "cc", scope, facts, 3)
    }

    /// A claim a cited equation is a whole multiple of: proving each side is
    /// that multiple is the polynomial case again, and what is left is
    /// cancelling the multiplier.
    #[allow(clippy::too_many_arguments)]
    fn scaled_from_cited(
        &mut self,
        step: &Step,
        left: &str,
        right: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
        w: &mut Work,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let want = field::equation(&self.to_term(&t!(left, right, "wceq")), &labels);
        for r in &step.just.refs {
            let Some(held) = lines.get(r) else {
                continue;
            };
            let cited = self.to_term(&held.term);
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
            let numeral = n(times as u32);
            let scaled: Vec<String> = [left, right]
                .iter()
                .map(|one| t!(numeral, one, "cmul", "co"))
                .collect();
            let was: Vec<String> =
                cited.children().iter().map(|c| self.rpn(c)).collect();
            let mut sides = Vec::new();
            for (x, y) in was.iter().zip(&scaled) {
                sides.push(self.same_polynomial(w, x, y)?);
            }
            if sides.iter().any(|s| s.is_declined()) {
                continue;
            }
            let sides: Vec<Proof> =
                sides.into_iter().filter_map(|s| s.built()).collect();
            self.combining(&[t!(left, right, "wceq"), held.term.clone()]);
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
        left: &str,
        right: &str,
        scaled: &[String],
        sides: &[Proof],
        given: Proof,
        cited: &Term,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Proof> {
        let numeral = n(times as u32);
        let matched = self.b.ap(
            "3eqtr3d",
            &binds! {"ph" => scope, "A" => self.rpn(&cited.children()[0]), "B" => self.rpn(&cited.children()[1]),
            "C" => &scaled[0], "D" => &scaled[1]},
            &[&given, &sides[0], &sides[1]],
        );
        let ml = self.membership(left, "cc", scope, facts)?;
        let mr = self.membership(right, "cc", scope, facts)?;
        let num = w.e.number(&self.ask(&w.spec), times);
        let apart = self.b.ap(
            "a1i",
            &binds! {"ph" => t!(numeral, "cc0", "wne"), "ps" => scope},
            &[&numerals::ne0(&self.b, times as u64)],
        );
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(numeral, "cc", "wcel"), "ch" => t!(numeral, "cc0", "wne")},
            &[&num, &apart],
        );
        let law = self.b.ap(
            "mulcan",
            &binds! {"A" => left, "B" => right, "C" => numeral},
            &[],
        );
        let turn = self.b.ap(
            "syl3anc",
            &binds! {"ph" => scope, "ps" => t!(left, "cc", "wcel"), "ch" => t!(right, "cc", "wcel"),
            "th" => t!(t!(numeral, "cc", "wcel"), t!(numeral, "cc0", "wne"), "wa"),
            "ta" => t!(t!(scaled[0], scaled[1], "wceq"), t!(left, right, "wceq"), "wb")},
            &[&ml, &mr, &both, &law],
        );
        Ok(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(scaled[0], scaled[1], "wceq"), "ch" => t!(left, right, "wceq")},
            &[&matched, &turn],
        ))
    }

    /// Refuse an `algebra` step that is not an identity: with nothing cited
    /// the claim must vanish outright; with equations cited it must be a
    /// combination of them.
    fn decide_field(&mut self, step: &Step, term: &str, lines: &Lines) -> Checked<()> {
        let labels = self.b.flabel.clone();
        let Some(claim) = field::equation(&self.to_term(term), &labels) else {
            return self.decide_apart(step, term, lines);
        };
        let mut given = Vec::new();
        for r in &step.just.refs {
            let Some(held) = lines.get(r) else {
                continue;
            };
            for said in self.parts(&held.term) {
                if let Some(one) = field::equation(&self.to_term(&said), &labels) {
                    given.push(one);
                }
            }
        }
        let mut atoms: BTreeSet<Rc<str>> = BTreeSet::new();
        for p in given.iter().chain(std::iter::once(&claim)) {
            for m in p.terms.keys() {
                atoms.extend(m.iter().map(|(a, _)| a.clone()));
            }
        }
        let atoms: Vec<Rc<str>> = atoms.into_iter().collect();
        if field::follows(&given, &claim, &atoms).is_none() {
            return Err(self.defect(
                step.line,
                format!(
                    "{} is not an identity, nor does it follow from what step {} cites, \
                     added and subtracted with at most one equation multiplied by a term",
                    self.render(term),
                    fmt(&step.number)
                ),
            ));
        }
        Ok(())
    }

    /// Refuse a disequality `algebra` step that is not a cited one rescaled:
    /// the method is allowed one disequality and no more.
    fn decide_apart(&mut self, step: &Step, term: &str, lines: &Lines) -> Checked<()> {
        let labels = self.b.flabel.clone();
        let Some(claim) = field::denied(&self.to_term(term), &labels) else {
            return Ok(());
        };
        for r in &step.just.refs {
            let Some(held) = lines.get(r) else {
                continue;
            };
            for said in self.parts(&held.term) {
                let one = field::denied(&self.to_term(&said), &labels);
                if one.is_some() && rescales(one.as_ref(), Some(&claim)).is_some() {
                    return Ok(());
                }
            }
        }
        Err(self.defect(
            step.line,
            format!(
                "{} is not a rescaling of any disequality step {} cites",
                self.render(term),
                fmt(&step.number)
            ),
        ))
    }

    /// Closed numerals, worked out and then said. Nothing is taken as
    /// stated: the claim is worked out first, so what cannot be proved is
    /// reported as what it is.
    pub fn arithmetic(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let what =
            format!("step {} claims {}", fmt(&step.number), step.claim.join(" "));
        self.closed_fact(term, scope, facts, &what, Some(step))
            .map(Built)
    }

    /// A fact about closed numerals, worked out and then proved, wherever it
    /// stands; `what` says where it was asked, as the page writes it.
    pub fn closed_fact(
        &mut self,
        term: &str,
        scope: &str,
        facts: &Facts,
        what: &str,
        step: Option<&Step>,
    ) -> Checked<Proof> {
        self.worked_out(term, what)?;
        if let Built(p) = self.prove_numeral(term, scope, facts)? {
            return Ok(p);
        }
        if let Built(p) = self.prove_field(step, term, scope, facts, &Lines::new())? {
            return Ok(p);
        }
        Err(self.unshown(term, what))
    }

    /// A claim `arithmetic` is asked for, refused where it is false or has
    /// no exact value.
    pub fn worked_out(&self, term: &str, what: &str) -> Checked<()> {
        match field::decide_closed(&self.to_term(term)) {
            Declined(_) => Ok(()),
            Built(Verdict::Holds(true)) => Ok(()),
            Built(Verdict::Holds(false)) => {
                Err(self.defect(self.at, format!("{what}, which is false")))
            }
            Built(Verdict::Unworked(why)) => {
                Err(self.defect(self.at, format!("{what}, which {why}")))
            }
        }
    }

    /// The defect for a claim `arithmetic` could not prove: it is never taken
    /// as stated instead.
    pub fn unshown(&self, term: &str, what: &str) -> Problem {
        match field::decide_closed(&self.to_term(term)) {
            Declined(_) => self.defect(
                self.at,
                format!("{what}, which is not a fact about numerals alone, and arithmetic decides nothing else"),
            ),
            Built(_) => self.defect(
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
        term: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut goal = self.to_term(term);
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
        let Some((first, second, how)) = order_sides(&goal) else {
            return Ok(Route::no("the claim states no relation"));
        };
        let labels = self.b.flabel.clone();
        let whole = |v: Option<Q>| -> Option<i64> {
            let v = v?;
            if !v.is_integer() {
                return None;
            }
            let n = v.to_integer().to_i64()?;
            (n >= 0).then_some(n)
        };
        let (Some(a), Some(b)) = (
            whole(linear::numeral(&first, &labels)),
            whole(linear::numeral(&second, &labels)),
        ) else {
            return Ok(Route::no("the two sides are not whole numbers"));
        };
        // Each side must *be* its numeral, not merely come to it.
        if self.rpn(&first) != n(a as u32) || self.rpn(&second) != n(b as u32) {
            return Ok(Route::no(
                "a side works out to a whole number but is one only after working out",
            ));
        }
        let (na, nb) = (n(a as u32), n(b as u32));
        if negated {
            if how != "=" || a == b {
                return Ok(Route::no("a denial of what holds"));
            }
            return Ok(Built(self.numerals_differ(scope, a, b)));
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
            return Ok(Built(self.numeral_below(scope, a, b)));
        }
        if how == "<=" && a <= b {
            if a == b {
                let real = self.real_numeral(scope, &q(a));
                let law = self.b.ap("leid", &binds! {"A" => na}, &[]);
                return Ok(Built(self.b.ap(
                    "syl",
                    &binds! {"ph" => scope, "ps" => t!(na, "cr", "wcel"), "ch" => t!(na, na, "cle", "wbr")},
                    &[&real, &law],
                )));
            }
            let below = self.numeral_below(scope, a, b);
            let ra = self.real_numeral(scope, &q(a));
            let rb = self.real_numeral(scope, &q(b));
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

    /// ( scope -> n e. RR ) for a whole multiplier.
    fn real_numeral(&self, scope: &str, times: &Q) -> Proof {
        let numerator = times.numer().to_i64().unwrap_or(0);
        let whole = numerator.abs();
        let nw = n(whole as u32);
        let held = self.b.ap(
            "a1i",
            &binds! {"ph" => t!(nw, "cr", "wcel"), "ps" => scope},
            &[&numerals::re(&self.b, whole as u64)],
        );
        if numerator >= 0 {
            return held;
        }
        self.b
            .ap("renegcld", &binds! {"ph" => scope, "A" => nw}, &[&held])
    }

    /// ( scope -> a < b ), for whole numbers a below b (`numerals::below`).
    fn numeral_below(&self, scope: &str, a: i64, b: i64) -> Proof {
        self.b.ap(
            "a1i",
            &binds! {"ph" => t!(n(a as u32), n(b as u32), "clt", "wbr"), "ps" => scope},
            &[&numerals::below(&self.b, a as u64, b as u64)],
        )
    }

    /// ( scope -> -. a = b ), from whichever of the two is below.
    fn numerals_differ(&self, scope: &str, a: i64, b: i64) -> Proof {
        let (low, high) = if a < b { (a, b) } else { (b, a) };
        let (nl, nh) = (n(low as u32), n(high as u32));
        let real = self.real_numeral(scope, &q(low));
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
        let (na, nb) = (n(a as u32), n(b as u32));
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
    pub fn inequalities(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
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
        let (term_out, lines_out) = (&out.term, &out.lines);
        // A cited line says each of its parts, a membership among them, as
        // the checker and R3 read it (`READERS.md`, what a membership says).
        let facts_out = &self.with_cited(Some(step), scope, &out.facts, None);
        self.decide_order(step, term_out, facts_out, lines_out)?;
        // The method wants every atom in ℝ, and a `requires` line is where
        // the step writes that; offered to the membership lookup and to
        // nothing else.
        let known = self.supplied(Some(step), scope, facts)?;
        let refs = step.just.refs.clone();
        let found = self.writing(scope, &known, false, |me| {
            me.prove_order(&refs, term_out, scope, facts_out, lines_out, &[])
        })?;
        if let Declined(d) = &found {
            return Err(self.defect(
                step.line,
                format!(
                    "step {} follows from what it cites, and inequalities cannot write its proof: {}",
                    fmt(&step.number),
                    self.say(d)
                ),
            ));
        }
        if term_out == term {
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
            if !inner.split_whitespace().any(|t| t == "csu") {
                let from = self.rpn(&kids[2]);
                let summand = self.restated(
                    &kids[1],
                    &format!("{from} cv"),
                    &format!("{letter} cv"),
                );
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
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<WrittenOut>> {
        let claim = self.to_term(term);
        let cited: Vec<(String, Line)> = refs
            .iter()
            .filter_map(|r| lines.get(r).map(|l| (r.clone(), l)))
            .collect();
        // Every sum is written over one letter nothing holds, so that a sum
        // a define names and the same sum a line writes are one term.
        let mut seen: Vec<Term> = vec![claim.clone(), self.to_term(scope)];
        seen.extend(cited.iter().map(|(_, l)| self.to_term(&l.term)));
        let refs: Vec<&Term> = seen.iter().collect();
        let as_written = WrittenOut {
            term: term.to_string(),
            facts: facts.clone(),
            lines: lines.clone(),
        };
        let Some(letter) = self.unheld(&refs).map(|v| self.rpn(&v)) else {
            return Ok(Built(as_written));
        };
        // Only a step that writes both a defined name and what it names
        // reads its names written out; any other reads them as written.
        let mut written: BTreeSet<String> = BTreeSet::new();
        let mut named: BTreeSet<String> = BTreeSet::new();
        let mut rest: Vec<Term> = vec![self.sums_over(&claim, &letter)];
        rest.extend(
            cited
                .iter()
                .map(|(_, l)| self.sums_over(&self.to_term(&l.term), &letter)),
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
            written.insert(self.rpn(&node));
            rest.extend(kids.iter().cloned());
        }
        if !named.iter().any(|body| written.contains(body)) {
            return Ok(Built(as_written));
        }
        let written_out =
            |me: &Self, t: &Term| me.sums_over(&me.defined_names_out(t), &letter);
        let term_out = self.rpn(&written_out(self, &claim));
        let (facts_out, lines_out) = (facts.copy(), lines.copy());
        for (r, line) in &cited {
            let said = self.to_term(&line.term);
            let written = written_out(self, &said);
            let out_rpn = self.rpn(&written);
            if out_rpn == line.term {
                continue;
            }
            let held = self.carried(r, facts, lines);
            let Built(alike) = self.same(&said, &written, scope, facts, step)? else {
                return Ok(Route::no(
                    "a cited line is not carried to its names written out",
                ));
            };
            let proof = pf!(self.b; scope, line.term, out_rpn, held, alike, "mpbid");
            self.know(&facts_out, out_rpn.clone(), proof.clone());
            lines_out.set(
                r.clone(),
                Line {
                    term: out_rpn,
                    proof,
                    sentences: line.sentences.clone(),
                },
            );
        }
        Ok(Built(WrittenOut {
            term: term_out,
            facts: facts_out,
            lines: lines_out,
        }))
    }

    /// An `inequalities` claim, by whichever route reaches it. `skip` names
    /// sentences of the cited lines to leave out: a case of a split must not
    /// split again on the disequality it split on.
    pub fn prove_order(
        &mut self,
        refs: &[String],
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
        skip: &[String],
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
            let Some(held) = lines.get(r) else {
                continue;
            };
            for said in self.parts(&held.term) {
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
        self.combining(&[term.to_string()]);
        if let Some(closed) = self.by_antisymmetry(&goal, scope, facts)? {
            return Ok(Built(closed));
        }
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
        let Some(found) = linear::certificate(&all, &line_of) else {
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
            // other; that is not this method's to emit.
            return Ok(Route::no("the cited facts refute each other"));
        }
        let used: Vec<usize> = found
            .iter()
            .filter(|(i, k)| !k.is_zero() && **i < given.len())
            .map(|(i, _)| *i)
            .collect();
        let mut combined = vec![term.to_string()];
        combined.extend(used.iter().map(|i| self.rpn(&where_[*i].1)));
        self.combining(&combined);
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
        // One equation, scaled, that is the claim with nothing left over.
        if used.len() == 1 && given[used[0]].how == How::Eq && spare.constant.is_zero()
        {
            let times = &found[&used[0]] / &weight;
            return self.one_equation_scaled(
                &where_[used[0]],
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
        term: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let claim = self.to_term(term);
        // What is said of every member is read at one, down to the
        // membership (`member_of`).
        let mut said = claim.clone();
        while said.variable().is_none() && said.label() == Some("wral") {
            said = said.children()[0].clone();
        }
        if said.variable().is_some()
            || said.label() != Some("wcel")
            || lookup(rules::SYSTEMS, &self.rpn(&said.children()[1])).is_none()
        {
            return Err(self.defect(
                step.line,
                format!(
                    "step {} names membership for {}, which says no term is in a number system",
                    fmt(&step.number),
                    self.render(term)
                ),
            ));
        }
        let supplied = self.supplied(Some(step), scope, facts)?;
        let cited = self.with_cited(Some(step), scope, &supplied, None);
        let known = facts.with(&cited);
        // The one method that reads a cited equation as saying a membership.
        let kept = std::mem::replace(&mut self.reading_equations, true);
        let made = self.member_of(&claim, scope, &known, Some(step));
        self.reading_equations = kept;
        match made? {
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
        scope: &str,
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
        let read = self.standard(claim);
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
        scope: &str,
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
        scope: &str,
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
                && lookup(rules::SYSTEMS, &self.rpn(&fact.children()[1])).is_some();
            let nonzero = fact.label() == Some("wn")
                && fact.children()[0].label() == Some("wceq")
                && self.rpn(&fact.children()[0].children()[1]) == "cc0";
            // A term above zero or below it, which says it is not zero.
            let signed = fact.label() == Some("wbr")
                && self.rpn(&fact.children()[2]) == "clt"
                && (self.rpn(&fact.children()[0]) == "cc0"
                    || self.rpn(&fact.children()[1]) == "cc0");
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
        scope: &str,
        known: &Facts,
        variable: &Term,
        over: &Term,
    ) -> Checked<(String, Facts)> {
        let member = t!(format!("{} cv", self.rpn(variable)), self.rpn(over), "wcel");
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
        said: &str,
        spare: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<(Term, Proof)>> {
        let labels = self.b.flabel.clone();
        let whole = self.to_term(said);
        let Some((range, letter, parts)) = field::linear_sum(&whole, &labels) else {
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
        let member_cv = format!("{spare} cv");
        let summand_at = if letter == spare {
            self.rpn(&summand)
        } else {
            let moved = self.restated(&summand, &format!("{letter} cv"), &member_cv);
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
        let mut scaled: Vec<(String, String, String)> = Vec::new();
        for part in &parts {
            let bound = field::respelt(&part.bound, &letter, spare);
            let m = field::spell_monomial(&bound);
            let c = Emitter::spell_run(&[(part.free.clone(), part.weight.clone())]);
            let t = t!(c, m, "cmul", "co");
            scaled.push((c, m, t));
        }
        let mut prefixes: Vec<String> = vec![scaled[0].2.clone()];
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
        let sum_of = |s: &str| t!(range, s, spare, "csu");
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
            self.sums_in_cc.insert((scope.to_string(), sum_of(m)), p);
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
        let mut pulled: Option<(Proof, String, String)> = None;
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
        let mut chain: Vec<(Proof, String, String)> = Vec::new();
        if let Some(r) = renamed {
            chain.push((r, said.to_string(), at_spare.clone()));
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
        system: &str,
        scope: &str,
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
        system: &str,
        scope: &str,
        known: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        let lemma = match system {
            "cr" => Some("fsumrecl"),
            "cc" => Some("fsumcl"),
            _ => None,
        };
        let (limits, summand, index) = (
            whole.children()[0].clone(),
            whole.children()[1].clone(),
            whole.children()[2].clone(),
        );
        let Some(lemma) = lemma.filter(|_| {
            limits.variable().is_none()
                && limits.label() == Some("co")
                && self.rpn(&limits.children()[2]) == "cfz"
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
        let spells = |text: &str| text.split_whitespace().any(|t| t == letter);
        if spells(scope) || spells(&self.rpn(&limits)) {
            let Some(name) = index.variable() else {
                return Ok(Route::no("a sum's index is no letter"));
            };
            let Some(fresh) = self.unheld(&[&self.to_term(scope), whole]) else {
                return Ok(Route::no("no letter is left to sum over"));
            };
            let mut put = IndexMap::new();
            put.insert(name.to_string(), fresh);
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
            me.member_of(&claim, &inner, &lifted, step)
        })?;
        let each = take!(each);
        Ok(Built(self.b.ap(
            lemma,
            &binds! {"ph" => scope, "A" => self.rpn(&limits), "B" => self.rpn(&summand), "k" => self.rpn(&index)},
            &[&finite, &each],
        )))
    }

    /// A claim of two sentences joined by "and", each proved in turn.
    fn both_halves(
        &mut self,
        refs: &[String],
        goal: &Term,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
        skip: &[String],
    ) -> Checked<Route<Proof>> {
        let halves: Vec<String> = goal.children().iter().map(|c| self.rpn(c)).collect();
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
        scope: &str,
        facts: &Facts,
        lines: &Lines,
        skip: &[String],
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
        left: &str,
        right: &str,
        how: &str,
        spare: &Q,
        scope: &str,
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
        let mut whole = spare.denom().clone();
        for Part { times, .. } in parts {
            whole = whole.lcm(times.denom());
        }
        let whole = whole.to_i64().unwrap_or(i64::MAX);
        // A reciprocal atom's divisor not being zero is the page's to say, in
        // its own spelling, which `written_nonzero` reads as a polynomial.
        let known = facts.copy();
        for (claim, w) in self.written.entries() {
            if let Some(lifted) = self.lifted_to(&claim, &w.proof, &w.at, scope) {
                self.know_default(&known, claim, lifted);
            }
        }
        let mut w = Work::new(Spec {
            scope: scope.to_string(),
            facts: facts.clone(),
            apart: false,
            written: Some(known),
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
                &(times * q(whole)),
                facts
            )?);
            terms.push(one);
        }
        let left_over = spare * q(whole);
        if left_over.is_positive() {
            return Ok(Route::no("what is left over is above zero"));
        }
        if left_over.is_negative() {
            let one = take!(self.number_below(scope, &-left_over));
            terms.push(one);
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
        if whole != 1 {
            let numeral = n(whole as u32);
            times_span = t!(numeral, span, "cmul", "co");
            let real = self.real_numeral(scope, &q(whole));
            times_real = self.b.ap(
                "remulcld",
                &binds! {"ph" => scope, "A" => numeral, "B" => &span},
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
            let zero = self.b.ap(
                "a1i",
                &binds! {"ph" => t!("cc0", "cr", "wcel"), "ps" => scope},
                &[&self.step("0re")],
            );
            reached = self.b.ap(
                "ltled",
                &binds! {"ph" => scope, "A" => &times_span, "B" => "cc0"},
                &[&times_real, &zero, &reached],
            );
            rel = "cle";
        }
        if whole != 1 {
            reached = self.unscaled(
                &mut w,
                &span,
                &span_real,
                n(whole as u32),
                whole,
                rel,
                &reached,
            );
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
        let was: Vec<String> =
            said.children()[..2].iter().map(|c| self.rpn(c)).collect();
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
        let times_n = times.to_integer().to_i64().unwrap_or(0);
        let numeral = n(times_n as u32);
        let scaled = t!(numeral, gap, "cmul", "co");
        let rn = self.real_numeral(&scope, times);
        let scaled_real = self.b.ap(
            "remulcld",
            &binds! {"ph" => &scope, "A" => numeral, "B" => &gap},
            &[&rn, &real],
        );
        let moved =
            self.times_positive(w, &gap, &real, numeral, times_n, "clt", &below);
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
        gap: &str,
        real: &Proof,
        numeral: &str,
        whole: i64,
        rel: &str,
        below: &Proof,
    ) -> Proof {
        let scope = w.spec.scope.clone();
        let lemma = if rel == "clt" { "ltmul2" } else { "lemul2" };
        let scaled = t!(numeral, gap, "cmul", "co");
        let at_zero = t!(numeral, "cc0", "cmul", "co");
        let rn = self.real_numeral(&scope, &q(whole));
        let pos = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", numeral, "clt", "wbr"), "ps" => &scope},
            &[&numerals::pos(&self.b, whole as u64)],
        );
        let positive = self.b.ap(
            "jca",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cr", "wcel"), "ch" => t!("cc0", numeral, "clt", "wbr")},
            &[&rn, &pos],
        );
        let zero = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", "cr", "wcel"), "ps" => &scope},
            &[&self.step("0re")],
        );
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
        let c = w.e.coefficient(&self.ask(&w.spec), &q(whole));
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
        span: &str,
        span_real: &Proof,
        numeral: &str,
        whole: i64,
        rel: &str,
        reached: &Proof,
    ) -> Proof {
        let scope = w.spec.scope.clone();
        let lemma = if rel == "clt" { "ltmul2" } else { "lemul2" };
        let scaled = t!(numeral, span, "cmul", "co");
        let at_zero = t!(numeral, "cc0", "cmul", "co");
        let rn = self.real_numeral(&scope, &q(whole));
        let pos = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", numeral, "clt", "wbr"), "ps" => &scope},
            &[&numerals::pos(&self.b, whole as u64)],
        );
        let positive = self.b.ap(
            "jca",
            &binds! {"ph" => &scope, "ps" => t!(numeral, "cr", "wcel"), "ch" => t!("cc0", numeral, "clt", "wbr")},
            &[&rn, &pos],
        );
        let c = w.e.coefficient(&self.ask(&w.spec), &q(whole));
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
        let zero = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", "cr", "wcel"), "ps" => &scope},
            &[&self.step("0re")],
        );
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
    fn number_below(&self, scope: &str, value: &Q) -> Route<Against> {
        let whole = value
            .to_integer()
            .to_i64()
            .filter(|w| value.is_integer() && *w > 0);
        let Some(whole) = whole else {
            return Route::no(format!(
                "{} is not a positive whole number",
                super::normal::show(value)
            ));
        };
        let numeral = n(whole as u32);
        let real = self.real_numeral(scope, &q(whole));
        let positive = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", numeral, "clt", "wbr"), "ps" => scope},
            &[&numerals::pos(&self.b, whole as u64)],
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
    fn added_pair(&self, scope: &str, one: &Against, other: &Against) -> Against {
        let (a, sa, pa, ra) = (&one.term, &one.strict, &one.below, &one.real);
        let (b, sb, pb, rb) = (&other.term, &other.strict, &other.below, &other.real);
        let rel_a = if *sa { "clt" } else { "cle" };
        let rel_b = if *sb { "clt" } else { "cle" };
        let lemma = rules::ADDING
            .iter()
            .find(|(k, _)| *k == (*sa, *sb))
            .map(|(_, l)| *l)
            .unwrap_or("le2add");
        let rel = if *sa || *sb { "clt" } else { "cle" };
        let total = t!(a, b, "caddc", "co");
        let sum_zero = t!("cc0", "cc0", "caddc", "co");
        let zero = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", "cr", "wcel"), "ps" => scope},
            &[&self.step("0re")],
        );
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
        let naught = self.b.ap(
            "a1i",
            &binds! {"ph" => t!(sum_zero, "cc0", "wceq"), "ps" => scope},
            &[&self.step("00id")],
        );
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
        scope: &str,
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
        let both = t!(up, down, "wa");
        let paired = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => &up, "ch" => &down},
            &[&pu, &pd],
        );
        let ra = self.membership(&a, "cr", scope, facts)?;
        let rb = self.membership(&b, "cr", scope, facts)?;
        let law = self.b.ap("letri3", &binds! {"A" => &a, "B" => &b}, &[]);
        let g = self.rpn(goal);
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(a, "cr", "wcel"), "ch" => t!(b, "cr", "wcel"), "th" => t!(g, both, "wb")},
            &[&ra, &rb, &law],
        );
        Ok(Some(self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &g, "ch" => &both},
            &[&paired, &turn],
        )))
    }

    /// A claim denying a relation, as the relation that holds instead,
    /// proved first and turned round by `ltnle` or `lenlt`.
    #[allow(clippy::too_many_arguments)]
    fn negated_order(
        &mut self,
        goal: &Term,
        refs: &[String],
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
        skip: &[String],
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
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
        skip: &[String],
    ) -> Checked<Route<Proof>> {
        let Certificate::Either { at: which, .. } = found else {
            unreachable!("a certificate that splits");
        };
        if *which >= given.len() {
            return Ok(Route::no("what splits is the claim, not a citation"));
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
                let held = lines.copy();
                held.set(
                    bound.clone(),
                    Line {
                        term: bound.clone(),
                        proof,
                        sentences: Vec::new(),
                    },
                );
                let mut more = refs.to_vec();
                more.push(bound.clone());
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
        bound: &str,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
        refs: &[String],
        skip: &[String],
    ) -> Checked<Route<Proof>> {
        if let Some(p) = self.held(facts, term, scope)? {
            return Ok(Built(p));
        }
        let found = self.prove_order(refs, term, scope, facts, lines, skip)?;
        if !found.is_declined() {
            return Ok(found);
        }
        self.impossible(bound, term, scope, facts)
    }

    /// The claim, because the bound this scope opened cannot hold: `lenlt`
    /// says a ≤ b and b < a deny each other.
    fn impossible(
        &mut self,
        bound: &str,
        term: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let node = self.to_term(bound);
        let Some((low, high, how)) = order_sides(&node).filter(|s| s.2 == "<") else {
            return Ok(Route::no("the bound states no strict order"));
        };
        let _ = how;
        let (low, high) = (self.rpn(&low), self.rpn(&high));
        let denies = t!(high, low, "cle", "wbr");
        let Some(held) = self.held(facts, &denies, scope)? else {
            return Ok(Route::no("nothing in scope denies the bound"));
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
        scope: &str,
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
        let below: Vec<String> =
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
    ) -> Checked<Route<(String, Proof, Proof)>> {
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
        let was: Vec<String> =
            said.children()[..2].iter().map(|c| self.rpn(c)).collect();
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
                "cc0",
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
        let zero = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", "cr", "wcel"), "ps" => &scope},
            &[&self.step("0re")],
        );
        let rn = self.real_numeral(&scope, times);
        let pos = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", numeral, "clt", "wbr"), "ps" => &scope},
            &[&numerals::pos(&self.b, times.numer().to_u64().unwrap_or(0))],
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
        scope: &str,
        inner: &Term,
        given: &Proof,
        facts: &Facts,
    ) -> Checked<Route<(Term, Proof)>> {
        let found =
            order_sides(inner).and_then(|s| lookup(rules::DENIED, s.2).map(|d| (s, d)));
        let Some((_sides, (denied, said, lemma))) = found else {
            return Ok(Route::no("only a denied `<` or `≤` is turned round"));
        };
        let was: Vec<String> =
            inner.children()[..2].iter().map(|c| self.rpn(c)).collect();
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
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let want = self.rpn(said);
        let held = self.carried(r, facts, lines);
        let term = lines.get(r).map(|l| l.term).unwrap_or_default();
        if term == want {
            return Ok(Built(held));
        }
        let known = facts.copy();
        self.unpack(&term, &held, scope, &known, 4);
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
        scope: &str,
        was: &[String],
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
        left: &str,
        right: &str,
        how: &str,
        scope: &str,
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
        let was: Vec<String> = said.children().iter().map(|c| self.rpn(c)).collect();
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
            "cc0",
        );
        let reached =
            w.e.chain(&self.ask(&w.spec), &alike, &inner, &span, &scaled, "cc0");
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
        was: &[String],
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

    /// Refuse an `inequalities` step that does not follow from its lines: a
    /// cited line of several sentences supplies each sentence that is a
    /// linear fact, and the bounds a membership it states implies.
    fn decide_order(
        &mut self,
        step: &Step,
        term: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<()> {
        let labels = self.b.flabel.clone();
        let Some(claim) = linear::fact(&self.to_term(term), &labels) else {
            return Ok(()); // not a relation this decides
        };
        let mut given = Vec::new();
        for r in &step.just.refs {
            let Some(held) = lines.get(r) else {
                continue;
            };
            for said in self.parts(&held.term) {
                if let Some(one) = linear::fact(&self.to_term(&said), &labels) {
                    given.push(one);
                }
            }
            for said in &self.stated_claims(r, facts, lines) {
                for (extra, _lemmas) in self.implied_terms(said) {
                    if let Some(one) = linear::fact(&self.to_term(&extra), &labels) {
                        if one.how != How::Ne {
                            given.push(one);
                        }
                    }
                }
            }
        }
        if !linear::follows(&given, &claim) {
            return Err(self.defect(
                step.line,
                format!(
                    "{} does not follow from what step {} cites",
                    self.render(term),
                    fmt(&step.number)
                ),
            ));
        }
        Ok(())
    }

    /// The variables a statement mentions, in the order the database
    /// declares their floats.
    pub fn free_floats(&self, text: &str) -> Vec<String> {
        let mut free: Vec<String> = text
            .split_whitespace()
            .filter(|t| self.b.flabel.contains(t))
            .map(String::from)
            .collect::<BTreeSet<String>>()
            .into_iter()
            .collect();
        free.sort_by_key(|v| {
            self.b
                .forder
                .get(&self.float_of(v))
                .copied()
                .unwrap_or(usize::MAX)
        });
        free
    }

    /// Whether a `requires` line of the step has been proved from its reason.
    pub fn proved_requirement(&self, line: usize) -> bool {
        self.rests_on.contains_key(&requirement(line))
    }

    /// Two terms in one set of rational weights, as the calculators keep them.
    pub fn weights_of(found: &IndexMap<usize, Q>) -> Vec<(usize, Q)> {
        found.iter().map(|(k, v)| (*k, v.clone())).collect()
    }
}
