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
//! What a method decides but cannot yet prove is taken as stated, and listed
//! at the head of the file it writes (`assume`, `stated`).

use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::IndexMap;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::field::{self, numeral as n, q, Poly, Verdict, Q};
use super::linear::{self, Certificate, How};
use super::normal::{Emitter, Oracle, Run};
use super::provenance::requirement;
use super::state::Elaborator;
use super::{Facts, Line, Lines};
use crate::binds;
use crate::corpus::{fmt, Step};
use crate::formula::Node;
use crate::mm::kernel::Term;
use crate::mm::spell::{Builder, Proof};
use crate::mm::{Kind, Signature};
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

/// How many times the claim the cited equation is, if a whole number from 2
/// to 9: both are the polynomial that must vanish, so one being a multiple
/// of the other is the two saying the same thing at different scales.
pub fn whole_multiple(cited: Option<&Poly>, claim: Option<&Poly>) -> Option<i64> {
    let (cited, claim) = (cited?, claim?);
    let lead = claim.lead()?;
    let theirs = cited.terms.get(lead)?;
    let times = theirs / &claim.terms[lead];
    if !times.is_integer() {
        return None;
    }
    let whole = times.to_integer().to_i64()?;
    if !(2..=9).contains(&whole) {
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

/// A combination's parts: what was cited, which fact, and its weight.
type Part = ((String, Term), linear::Fact, Q);

/// A term against zero: the term, whether strictly, the proof it is below
/// zero, and the proof it is real.
type Against = (String, bool, Proof, Proof);

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
        self.decide_field(step, term, lines)?;
        let found = self.prove_field(Some(step), term, scope, facts, lines)?;
        if found.is_declined() {
            return self
                .assume(step, term, scope, facts, "alg", lines)
                .map(Built);
        }
        Ok(found)
    }

    /// An `algebra` claim, by whichever of the routes reaches it, in the
    /// order they cost; refused in the words of every route that declined.
    pub fn prove_field(
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
            let (over, under, proof) =
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
        let want = t!(said, "cc0", "wne");
        if let Some(p) = facts.get(&want) {
            return Ok(Some(p));
        }
        let denied = t!(t!(said, "cc0", "wceq"), "wn");
        if let Some(p) = facts.get(&denied) {
            return Ok(Some(pf!(self.b; scope, said, "cc0", p, "neqned")));
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
            let (subject, zero, given);
            if node.label() == Some("wn") {
                let inner = node.children()[0].clone();
                if inner.variable().is_some() || inner.label() != Some("wceq") {
                    continue;
                }
                subject = inner.children()[0].clone();
                zero = inner.children()[1].clone();
                given = pf!(self.b; scope, self.rpn(&subject), "cc0", proof, "neqned");
            } else {
                subject = node.children()[0].clone();
                zero = node.children()[1].clone();
                given = proof;
            }
            let was = self.rpn(&subject);
            if self.rpn(&zero) != "cc0" || was == said {
                continue;
            }
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
        let (first_items, first_under, first) =
            take!(w
                .e
                .normalize_quotient(&mut self.ask(&w.spec), &lt, &labels)?);
        let rt = self.to_term(right);
        let (second_items, second_under, second) =
            take!(w
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
    /// `part` first, from the step's own lines, and searched for at a depth
    /// of its own where that cannot.
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
        self.within(said, "cc", scope, facts, 12)
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
            let Some(times) =
                times.filter(|t| self.b.sigs.contains_key(&format!("{t}ne0")))
            else {
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
            &[&self.step(&format!("{times}ne0"))],
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
        let digit = |v: Option<Q>| -> Option<i64> {
            let v = v?;
            if !v.is_integer() {
                return None;
            }
            let n = v.to_integer().to_i64()?;
            (0..=9).contains(&n).then_some(n)
        };
        let (Some(a), Some(b)) = (
            digit(linear::numeral(&first, &labels)),
            digit(linear::numeral(&second, &labels)),
        ) else {
            return Ok(Route::no("the two sides are not single digits"));
        };
        // Each side must *be* its digit, not merely come to it.
        if self.rpn(&first) != n(a as u32) || self.rpn(&second) != n(b as u32) {
            return Ok(Route::no(
                "a side works out to a digit but is one only after working out",
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
            &[&self.step(&format!("{whole}re"))],
        );
        if numerator >= 0 {
            return held;
        }
        self.b
            .ap("renegcld", &binds! {"ph" => scope, "A" => nw}, &[&held])
    }

    /// ( scope -> a < b ), the one thing set.mm names for every pair: `0 < n`
    /// is `npos` rather than `0ltn`, and one is the exception to that.
    fn numeral_below(&self, scope: &str, a: i64, b: i64) -> Proof {
        let label = if a != 0 {
            format!("{a}lt{b}")
        } else if b == 1 {
            "0lt1".to_string()
        } else {
            format!("{b}pos")
        };
        self.b.ap(
            "a1i",
            &binds! {"ph" => t!(n(a as u32), n(b as u32), "clt", "wbr"), "ps" => scope},
            &[&self.step(&label)],
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
        self.decide_order(step, term, facts, lines)?;
        // The method wants every atom in ℝ, and a `requires` line is where
        // the step writes that; offered to the membership lookup and to
        // nothing else.
        let known = self.supplied(Some(step), scope, facts)?;
        let refs = step.just.refs.clone();
        let found = self.writing(scope, &known, false, |me| {
            me.prove_order(&refs, term, scope, facts, lines, &[])
        })?;
        if found.is_declined() {
            return self
                .assume(step, term, scope, facts, "ine", lines)
                .map(Built);
        }
        Ok(found)
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
            for said in self.stated_by(r, facts, lines).keys() {
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
            .map(|i| (where_[*i].clone(), given[*i].clone(), &found[i] / &weight))
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
    /// system, and a term's not being 0 — laid down beside itself in its
    /// standard form, where that differs.
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
        for (said, (at, held)) in self.written.clone() {
            if let Some(lifted) = self.lifted_to(&said, &held, &at, scope) {
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
            if fact.variable().is_some() || !(member || nonzero) {
                continue;
            }
            let read = self.standard(&fact);
            let read_rpn = self.rpn(&read);
            if read_rpn == said || out.has(&read_rpn) {
                continue;
            }
            if let Built(alike) = self.same(&fact, &read, scope, known, step)? {
                out.set(
                    read_rpn.clone(),
                    pf!(self.b; scope, said, read_rpn, held, alike, "mpbid"),
                );
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
    ) -> (String, Facts) {
        let member = t!(format!("{} cv", self.rpn(variable)), self.rpn(over), "wcel");
        let (inner, lifted) = self.widen(scope, known, &member, None);
        let held = lifted.get(&member).expect("the membership just laid down");
        let more = self.implied(&member, &held, &inner);
        let out = lifted.copy();
        for (k, v) in more {
            out.set(k, v);
        }
        (inner, out)
    }

    /// A finite sum in ℝ or ℂ because each term is, for each index in its
    /// range (`fsumrecl`, `fsumcl`).
    fn summed(
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
            let (inner, lifted) = me.fixed(scope, known, &index, &limits);
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
        for (_, _, times) in parts {
            whole = whole.lcm(times.denom());
        }
        let whole = whole.to_i64().unwrap_or(i64::MAX);
        // A reciprocal atom's divisor not being zero is the page's to say, in
        // its own spelling, which `written_nonzero` reads as a polynomial.
        let known = facts.copy();
        for (claim, (at, proof)) in self.written.clone() {
            if let Some(lifted) = self.lifted_to(&claim, &proof, &at, scope) {
                known.set_default(claim, lifted);
            }
        }
        let mut w = Work::new(Spec {
            scope: scope.to_string(),
            facts: facts.clone(),
            apart: false,
            written: Some(known),
        });
        let mut terms: Vec<Against> = Vec::new();
        for ((r, said), _fact, times) in parts {
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
        let (term, strict, below, _real) = total;
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
        let numeral = crate::rules::numeral_label(whole as u32)
            .filter(|_| (0..=9).contains(&whole));
        if whole != 1 {
            let Some(numeral) = numeral else {
                return Ok(Route::no(format!("{whole} is past one digit")));
            };
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
                numeral.unwrap(),
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
            return Ok(Built((term, false, below, real)));
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
            return Ok(Built((gap, true, below, real)));
        }
        let times_n = times.to_integer().to_i64().unwrap_or(0);
        let Some(numeral) = crate::rules::numeral_label(times_n as u32)
            .filter(|_| (0..=9).contains(&times_n))
        else {
            return Ok(Route::no(format!(
                "{} is past one digit",
                super::normal::show(times)
            )));
        };
        let scaled = t!(numeral, gap, "cmul", "co");
        let rn = self.real_numeral(&scope, times);
        let scaled_real = self.b.ap(
            "remulcld",
            &binds! {"ph" => &scope, "A" => numeral, "B" => &gap},
            &[&rn, &real],
        );
        let moved =
            self.times_positive(w, &gap, &real, numeral, times_n, "clt", &below);
        Ok(Built((scaled, true, moved, scaled_real)))
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
            &[&self.step(&format!("{whole}pos"))],
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
            &[&self.step(&format!("{whole}pos"))],
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
            .filter(|w| value.is_integer() && (0..=9).contains(w));
        let Some(whole) = whole else {
            return Route::no(format!(
                "{} is past one digit",
                super::normal::show(value)
            ));
        };
        let numeral = n(whole as u32);
        let real = self.real_numeral(scope, &q(whole));
        let label = if whole == 1 {
            "0lt1".to_string()
        } else {
            format!("{whole}pos")
        };
        let positive = self.b.ap(
            "a1i",
            &binds! {"ph" => t!("cc0", numeral, "clt", "wbr"), "ps" => scope},
            &[&self.step(&label)],
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
        Built((negated, true, below, neg_real))
    }

    /// Two terms against zero added, strict where either is.
    fn added_pair(&self, scope: &str, one: &Against, other: &Against) -> Against {
        let (a, sa, pa, ra) = one;
        let (b, sb, pb, rb) = other;
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
        (total, *sa || *sb, below, real)
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
        let (Some(pu), Some(pd)) = (facts.get(&up), facts.get(&down)) else {
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
        let held = match facts.get(&instead) {
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
                let held = lines.copy();
                held.set(
                    bound.clone(),
                    Line {
                        term: bound.clone(),
                        proof: lifted.get(bound).expect("the bound just laid down"),
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
        if let Some(p) = facts.get(term) {
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
        let Some(held) = facts.get(&denies) else {
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
        let supposed = facts.get(bound).expect("the bound this scope opened");
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
                "{} is past one digit",
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
            &[&self.step(&format!("{}pos", times.numer()))],
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
        if let Some(p) = known.get(&want) {
            return Ok(Built(p));
        }
        // A bound the line's membership implies, read off what the line
        // states and nothing else in scope.
        for (s, proof) in self.stated_by(r, &known, lines) {
            let proof = if s == term { Some(held.clone()) } else { proof };
            let Some(proof) = proof else {
                continue;
            };
            let more = self.implied(&s, &proof, scope);
            if let Some(p) = more.get(&want) {
                return Ok(Built(p.clone()));
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
                "{} is past one digit",
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
            for said in self.stated_by(r, facts, lines).keys() {
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

    /// State what a step claims, under everything it rests on, and take it:
    /// the lines it cites as well as the conditions it writes. What the file
    /// assumes is listed at its head.
    pub fn assume(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
        prefix: &str,
        lines: &Lines,
    ) -> Checked<Proof> {
        let mut asks: Vec<(String, Proof)> = Vec::new();
        for r in &step.just.refs {
            let cited = lines.get(r).unwrap_or_else(|| panic!("no line {r} cited"));
            asks.push((cited.term.clone(), self.carried(r, facts, lines)));
        }
        let mut wants: Vec<Node> = Vec::new();
        for r in &step.requires {
            wants.push(self.read(&r.fact)?);
        }
        for (want, r) in wants.iter().zip(&step.requires) {
            let here = self.term(want)?;
            if !asks.iter().any(|(a, _)| *a == here) {
                // Proved from its reason and checked against it, as
                // `supplied` and `required` prove one.
                let made = match self.side(want, &r.how, scope, facts, Some(step))? {
                    Built(p) => self.discharged_by(p, step, &r.how, r.line)?,
                    Declined(d) => panic!(
                        "the requires line at {} declined where it is assumed from: {}",
                        r.line,
                        self.say(&d)
                    ),
                };
                asks.push((here, made));
            }
        }
        let mut statement = term.to_string();
        for (one, _given) in asks.iter().rev() {
            statement = t!(one, statement, "wi");
        }
        let mut proof =
            self.stated(prefix, &format!("|- {}", self.render(&statement)))?;
        if asks.is_empty() {
            // Nothing to discharge, so the statement is taken at the scope
            // the step sits in.
            return Ok(pf!(self.b; term, scope, proof, "a1i"));
        }
        // The conditions nest, outermost first, so each is answered in turn.
        for (i, (one, given)) in asks.iter().enumerate() {
            let mut rest = term.to_string();
            for (later, _p) in asks[i + 1..].iter().rev() {
                rest = t!(later, rest, "wi");
            }
            let fold = if i == 0 { "syl" } else { "mpd" };
            proof = pf!(self.b; scope, one, rest, given, proof, fold);
        }
        Ok(proof)
    }

    /// Register a statement this file takes rather than proves, pushing every
    /// variable it mentions in the order the database declares them. The
    /// same statement asked for twice is listed once.
    pub fn stated(&mut self, prefix: &str, text: &str) -> Checked<Proof> {
        if let Some(p) = self.assumed.get(text) {
            return Ok(p.clone());
        }
        let label = self.fresh(prefix)?;
        self.axioms.push((label.clone(), text.to_string()));
        let free = self.free_floats(text);
        let floats = free
            .iter()
            .map(|v| (self.typecode(&self.float_of(v)).to_string(), v.clone()))
            .collect();
        self.b.sigs.insert(
            label.clone(),
            Signature {
                label: label.clone(),
                kind: Kind::Axiom,
                statement: text.split_whitespace().map(String::from).collect(),
                floats,
                essentials: Vec::new(),
                disjoint: std::collections::BTreeSet::new(),
            },
        );
        let mut parts: Vec<String> = free.iter().map(|v| self.float_of(v)).collect();
        parts.push(label);
        let proof = pf!(self.b; parts.join(" "));
        self.assumed.insert(text.to_string(), proof.clone());
        Ok(proof)
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
