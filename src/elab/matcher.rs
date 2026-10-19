//! The matcher: a lemma fitted to a claim.
//!
//! This is the third of the elaborator's six parts (`ELABORATION.md`, "How
//! the elaborator is built"). Given a lemma's statement, a claim, and the
//! facts a step names, it produces what the lemma's variables stand for and
//! the antecedents left to discharge, and discharges them. `settle` is the
//! search for a side condition the page does not write, through the lemmas
//! `rules::MEMBERSHIP` declares; `apply_lemma` fits one named lemma;
//! `rewrite` and `descend` carry an equation to where it is used inside a
//! term.
//!
//! What it matches modulo is written here as cases: a claim spelt with other
//! bound letters (`respelt`, `renaming`), a biconditional read either way
//! (`fits`, `one_direction`), an equation that says a term another way
//! (`rewritten`, `said_otherwise`), a lemma's implicit substitution
//! (`instanced`, `substituted_slot`, `as_class`), an existential introduced
//! or eliminated (`witnessed`, `introduced`, `through_existential`), and a
//! conjunct projected (`as_conjunct`).

use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use super::elaborate::Sides;
use super::provenance::{from_requires, may_rest_on, MEMBERSHIP};
use super::state::{
    fit, fit_respelt, names_of, Binding, Elaborator, Frame, HeadKey, Role, Shape, Vars,
};
use super::tables::{Leaf, Row};
use super::{Facts, Lines, WrittenFact};
use crate::binds;
use crate::corpus::Step;
use crate::formula::symbol::Symbol;
use crate::formula::Node;
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::mm::{Rpn, Signature};
use crate::outcome::{Built, Checked, Decline, Declined, Route};
use crate::rules::{self, discharge, lookup, Join, Side};
use crate::{pf, t, take};

/// One rule of the standard form: its label, the side it rewrites, the side
/// it becomes, and the lemma's variables.
#[derive(Clone)]
pub struct Rewrite {
    pub label: String,
    pub given: Term,
    pub gives: Term,
    pub names: Vars,
}

/// How one rewrite toward the standard form is made at the head of a term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum How {
    /// A name a `define` introduced, read as its body.
    Defined,
    /// A defined function applied, read as its rule at the value.
    Applied,
    /// A rule of `rules::STANDARD`, by its label.
    Rule(String),
    /// An equation's sides put in order.
    Eqcom,
    /// A symmetric pair put in order.
    Commuted,
}

/// A link of a chain of equalities or equivalences: ( scope -> from = to ),
/// or `<->` between formulas.
#[derive(Clone)]
pub struct ChainLink {
    pub from: Term,
    pub to: Term,
    pub proof: Proof,
}

/// A node's holes walked: each as written and as rewritten, by place.
struct Walked {
    holes: Vec<Rpn>,
    after: Vec<Rpn>,
    /// The proof at each place that changed, that the hole as written is the
    /// hole as rewritten.
    proofs: IndexMap<usize, Proof>,
}

impl<'a> Elaborator<'a> {
    // --- the facts at a scope, by standard form ---------------------------

    /// The standard form a fact is stored and found by (`Facts`): the claim
    /// with the normalizer's rules applied, parts first, and each symmetric
    /// pair in order (`written_step`), no letter read as bound. A defined
    /// name and a map's value stay as written, since reading them depends on
    /// the step and the scope, and a fact's key must be the same wherever it
    /// is stored and wherever it is asked for. `0 ≠ k`, `k ≠ 0` and
    /// `¬ k = 0` have one key.
    pub fn fact_key(&mut self, claim: &Rpn) -> Rpn {
        if let Some(found) = self.fact_keys.get(claim) {
            return found.clone();
        }
        let kept = std::mem::take(&mut self.binding);
        let term = self.to_term(claim);
        let written = self.written_form(&term);
        self.binding = kept;
        let key = self.rpn(&written);
        self.fact_keys.insert(claim.clone(), key.clone());
        key
    }

    /// The term with every rule `written_step` takes applied, parts first,
    /// and every identity element dropped: an identity element goes without
    /// saying wherever it stands (`SYNTAX.md`), so x + 0 = y is found where
    /// x = y is asked, and `held` carries the one to the other.
    fn written_form(&mut self, term: &Term) -> Term {
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        let kids: Vec<Term> = term
            .children()
            .iter()
            .map(|c| self.written_form(c))
            .collect();
        let parts = Term::apply(term.label().unwrap_or(""), kids);
        if let Some(kept) = self.identity_dropped(&parts) {
            return self.written_form(&kept);
        }
        match self.written_step(&parts) {
            None => parts,
            Some((_, next)) => self.written_form(&next),
        }
    }

    /// `claim`, proved by `proof`, among `facts`.
    pub fn know(&mut self, facts: &Facts, claim: Rpn, proof: Proof) {
        let key = self.fact_key(&claim);
        facts.store(claim, key, proof);
    }

    /// `know`, where the claim is not held yet as it is spelt.
    pub fn know_default(&mut self, facts: &Facts, claim: Rpn, proof: Proof) {
        let key = self.fact_key(&claim);
        facts.store_default(claim, key, proof);
    }

    /// A proof of `wanted`, under `scope`, among `facts`: the fact with its
    /// standard form proved last, as a later proof of a claim replaces an
    /// earlier one, carried to `wanted` by the normalizer's proof that the
    /// two are one claim (`same`) where it is spelt otherwise. `0 ≠ k` is
    /// held where `k ≠ 0` was proved, and a step's own requires line saying
    /// it is the one taken over a line of the scope saying it earlier.
    /// Every route that asks whether a fact is held asks here.
    pub fn held(
        &mut self,
        facts: &Facts,
        wanted: &Rpn,
        scope: &Rpn,
    ) -> Checked<Option<Proof>> {
        let key = self.fact_key(wanted);
        let claims = facts.under(&key);
        // A claim held as it is wanted is taken as it stands, before one of
        // the same standard form spelt otherwise: an equation is held both
        // ways round (`know_turned`), and the way asked for is the one meant.
        if claims.iter().any(|c| c == wanted) {
            if let Some(proof) = facts.proof(wanted) {
                return Ok(Some(proof));
            }
        }
        let Some(stored) = claims.last() else {
            // An equation is held whichever way round it was proved: `m = |X|`
            // holds `|X| = m`. The standard form keeps the sides as written,
            // so the other way round is a fact of its own to look for.
            if let Some((turned, flip)) = self.turned_claim(wanted) {
                if !facts.under(&self.fact_key(&turned)).is_empty() {
                    if let Some(p) = self.held(facts, &turned, scope)? {
                        let Sides { left, right } = self.equation_sides(&turned);
                        return Ok(Some(pf!(self.b; scope, left, right, p, flip)));
                    }
                }
            }
            return self.held_reordered(facts, wanted, scope);
        };
        let Some(proof) = facts.proof(stored) else {
            return Ok(None);
        };
        if stored == wanted {
            return Ok(Some(proof));
        }
        // The normalizer proves under the innermost frame it may (`allowed`),
        // and the fact is held under `scope`, which may be an outer one: the
        // two are made one claim at a frame of `scope`'s own.
        let (was, now) = (self.to_term(stored), self.to_term(wanted));
        let across = self.frames_kept(|me| {
            me.frames.push(Frame {
                scope: scope.clone(),
                added: None,
                facts: Facts::new(),
            });
            me.same(&was, &now, scope, &Facts::new(), None)
        })?;
        match across {
            Built(across) => Ok(Some(
                pf!(self.b; scope, stored, wanted, proof, across, "mpbid"),
            )),
            // The two may differ by an identity element, which is filed
            // under the same form and asks the scope that what is left is a
            // number. The standard form files an equation whichever way
            // round it is written, so the one held may also be the wanted
            // turned round: `x·1 = y` is `y = x` with the element dropped
            // and the sides turned.
            Declined(_) => {
                if let Some(p) = self.tidied(&proof, stored, wanted, scope, facts)? {
                    return Ok(Some(p));
                }
                let Some((turned, flip)) = self.turned_claim(wanted) else {
                    return Ok(None);
                };
                let Some(p) = self.tidied(&proof, stored, &turned, scope, facts)?
                else {
                    return Ok(None);
                };
                let Sides { left, right } = self.equation_sides(&turned);
                Ok(Some(pf!(self.b; scope, left, right, p, flip)))
            }
        }
    }

    /// A triangle held with its points named in another order: three points
    /// form a triangle in any order (`forms-a-triangle`, `commutes yes`), and
    /// the one held is carried to the order wanted by as few swaps and
    /// rotations as reach it (`gtriswap`, `gtrirotate`). None where `wanted`
    /// is no triangle, or no order of its points is held.
    fn held_reordered(
        &mut self,
        facts: &Facts,
        wanted: &Rpn,
        scope: &Rpn,
    ) -> Checked<Option<Proof>> {
        const SWAP: &str = "gtriswap";
        const ROTATE: &str = "gtrirotate";
        if !self.b.sigs.contains_key(SWAP) || !self.b.sigs.contains_key(ROTATE) {
            return Ok(None);
        }
        // ( the points are numbers -> ( P, Q, R form a triangle -> … ) ).
        let whole = self.statement(SWAP);
        let shape = whole.children()[1].children()[0].clone();
        let mut letters: Vec<Symbol> = Vec::new();
        let mut rest = vec![shape.clone()];
        while let Some(node) = rest.pop() {
            if let Some(v) = node.variable_symbol() {
                if !letters.contains(&v) {
                    letters.push(v);
                }
                continue;
            }
            rest.extend(node.children().iter().rev().cloned());
        }
        if letters.len() != 3 {
            return Ok(None);
        }
        let Some(at) =
            self.fits_as(&shape, &self.to_term(wanted), &names_of(&shape), None)
        else {
            return Ok(None);
        };
        let Some(points) = letters
            .iter()
            .map(|l| at.get(l.as_str()).cloned())
            .collect::<Option<Vec<Term>>>()
        else {
            return Ok(None);
        };
        let named = |me: &Self, order: &[usize]| -> Rpn {
            let mut put = Binding::new();
            for (&letter, &i) in letters.iter().zip(order) {
                put.insert(letter, points[i].clone());
            }
            me.rpn(&shape.substitute(&put))
        };
        let swap = |o: &[usize]| vec![o[0], o[2], o[1]];
        let rotate = |o: &[usize]| vec![o[1], o[2], o[0]];
        let goal = vec![0, 1, 2];
        for start in [[0, 2, 1], [1, 2, 0], [2, 0, 1], [1, 0, 2], [2, 1, 0]] {
            let said = named(self, &start);
            if facts.under(&self.fact_key(&said)).is_empty() {
                continue;
            }
            let Some(mut proof) = self.held(facts, &said, scope)? else {
                continue;
            };
            // The fewest moves from the order held to the order wanted.
            let mut paths: Vec<(Vec<usize>, Vec<&str>)> =
                vec![(start.to_vec(), Vec::new())];
            let moves = loop {
                let Some((order, path)) = paths.first().cloned() else {
                    break None;
                };
                paths.remove(0);
                if order == goal {
                    break Some(path);
                }
                if path.len() < 3 {
                    for (label, next) in
                        [(SWAP, swap(&order)), (ROTATE, rotate(&order))]
                    {
                        let mut longer = path.clone();
                        longer.push(label);
                        paths.push((next, longer));
                    }
                }
            };
            let Some(moves) = moves else {
                continue;
            };
            let known = facts.copy();
            let mut order = start.to_vec();
            for label in moves {
                self.know(&known, named(self, &order), proof);
                order = if label == SWAP {
                    swap(&order)
                } else {
                    rotate(&order)
                };
                let next = self.to_term(&named(self, &order));
                let Built(made) =
                    self.apply_lemma(label, &next, scope, &known, None, false, None)?
                else {
                    return Ok(None);
                };
                proof = made;
            }
            return Ok(Some(proof));
        }
        Ok(None)
    }

    /// `wanted` from a fact that says it over other bound letters, under any
    /// binder and at any depth: the two are one claim, and `renaming_apart`
    /// says so, closed, by way of letters nothing holds so that no letter is
    /// caught on the way. A lemma given letters of its own (`letters_unheld`)
    /// asks its facts this way, and so does a line joined, which a `proof`
    /// block may have closed over a spare letter.
    pub fn held_rebound(
        &mut self,
        facts: &Facts,
        wanted: &Rpn,
        scope: &Rpn,
    ) -> Checked<Option<Proof>> {
        for (said, proof) in facts.entries() {
            if said == *wanted || !self.rebound(&said, wanted) {
                continue;
            }
            if let Some(across) = self.renaming_apart(&said, wanted)? {
                let turned = pf!(self.b; t!(said, wanted, "wb"), scope, across, "a1i");
                return Ok(Some(
                    pf!(self.b; scope, said, wanted, proof, turned, "mpbid"),
                ));
            }
        }
        Ok(None)
    }

    /// `claim`, proved by `proof` under `at`, among what the step's lines
    /// wrote (`Written`).
    pub fn write(&mut self, claim: Rpn, at: Rpn, proof: Proof) {
        let key = self.fact_key(&claim);
        self.written.store(claim, key, at, proof);
    }

    /// `wanted`, among what the step's lines wrote, under the scope the fact
    /// it is held by was proved under: found by standard form as `held`
    /// finds a fact.
    pub fn written_held(&mut self, wanted: &Rpn) -> Checked<Option<WrittenFact>> {
        let key = self.fact_key(wanted);
        let written = self.written.clone();
        let Some(latest) = written.facts().under(&key).last().cloned() else {
            return Ok(None);
        };
        let Some(at) = written.at(&latest).cloned() else {
            return Ok(None);
        };
        Ok(self
            .held(written.facts(), wanted, &at)?
            .map(|proof| WrittenFact { proof, at }))
    }

    /// Whether `wanted` is held among `facts` (`held`), with no proof built.
    pub fn holds(&mut self, facts: &Facts, wanted: &Rpn) -> bool {
        let key = self.fact_key(wanted);
        !facts.under(&key).is_empty()
    }

    // --- facts the text never writes ------------------------------------

    /// `wanted` from the declared lemmas, or said another way. Every lemma is
    /// tried as it is written before any is read backwards, so that a
    /// biconditional turned round never stands in for one that says what is
    /// wanted outright.
    fn searched(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Option<Proof>> {
        for backwards in [false, true] {
            for lemma in self.declared(wanted, backwards) {
                if let Some(found) =
                    self.fits(&lemma, wanted, scope, facts, depth, backwards)?
                {
                    return Ok(Some(found));
                }
            }
        }
        self.said_otherwise(wanted, scope, facts, depth)
    }

    /// `settle`, and where that declines, the claim with its identity
    /// elements dropped settled and carried back to it (`tidied`): k·N + 0 = A
    /// from a line saying k·N = A (`SYNTAX.md`, "An identity element goes
    /// without saying").
    pub fn settle_or_bare(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        lines: Option<&Lines>,
    ) -> Checked<Route<Proof>> {
        let settled = self.settle(wanted, scope, facts, 3, step, lines)?;
        if !settled.is_declined() {
            return Ok(settled);
        }
        let (want, bare) = (self.rpn(wanted), self.without_identities(wanted));
        let bare_rpn = self.rpn(&bare);
        if bare_rpn == want {
            return Ok(settled);
        }
        let Built(p) = self.settle(&bare, scope, facts, 3, step, lines)? else {
            return Ok(settled);
        };
        Ok(match self.tidied(&p, &bare_rpn, &want, scope, facts)? {
            Some(p) => Built(p),
            None => settled,
        })
    }

    /// A proof of something a step needs and the text does not write.
    ///
    /// `depth` bounds how many declared lemmas a chain applies one on top of
    /// another, and three is the deepest chain in the corpus. That a term is
    /// a set is not searched for and spends none of it, and neither does
    /// splitting a conjunction.
    ///
    /// What is offered is only what the proof being built may rest on
    /// (`resting_on`). A step is passed only where one is there to have
    /// cited a witness, which is what lets an existential be proved at all.
    pub fn settle(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
        step: Option<&Step>,
        lines: Option<&Lines>,
    ) -> Checked<Route<Proof>> {
        let unfiltered = facts;
        let facts = self.restable(facts);
        // A membership the page says once. It comes before what is held,
        // since the scope holds a copy of the line introducing a letter that
        // the step does not name. A numeral's is worked out below, and
        // `numeral_within` comes back here for it.
        let numeral = wanted.label() == Some("wcel")
            && wanted.children().len() == 2
            && self
                .rpn(&wanted.children()[0])
                .tokens()
                .iter()
                .all(|t| rules::numeric(t.as_str()));
        if !numeral {
            if let Built(p) = self.said_once_proof(wanted, scope, unfiltered)? {
                return Ok(Built(p));
            }
        }
        let rpn = self.rpn(wanted);
        if let Some(p) = self.held(&facts, &rpn, scope)? {
            return Ok(Built(p));
        }
        let label = wanted.label().unwrap_or("");
        let kids = wanted.children();
        // Truth, the body of a "there is" that says nothing of what it names.
        if label == "wtru" {
            return Ok(Built(pf!(self.b; rpn, scope, self.step("tru"), "a1i")));
        }
        // A term equals itself, which no line need write.
        if label == "wceq"
            && kids.len() == 2
            && self.rpn(&kids[0]) == self.rpn(&kids[1])
        {
            let a = self.rpn(&kids[0]);
            return Ok(Built(self.b.ap(
                "eqidd",
                &binds! {"ph" => scope, "A" => &a},
                &[],
            )));
        }
        // A number's membership of a number system is worked out from the
        // numeral, not searched for, and spends none of the depth.
        if label == "wcel"
            && kids.len() == 2
            && kids[1]
                .label()
                .is_some_and(|l| lookup(rules::SYSTEMS, l).is_some())
            && self
                .rpn(&kids[0])
                .tokens()
                .iter()
                .all(|t| rules::numeric(t.as_str()))
        {
            // Inside the search that works out one number, the numbers it is
            // built from are looked up and not searched for again.
            let number = if !self.numbering.is_empty() {
                self.digit_within(wanted, scope, &facts)?
            } else {
                self.numeral_within(wanted, scope, &facts)?
            };
            if !number.is_declined() {
                return Ok(number);
            }
        }
        // Whether a term is a set is read off its structure, not searched
        // for.
        if label == "wcel"
            && kids.len() == 2
            && self.rpn(&kids[1]).alone() == Some("cvv")
        {
            let made = self.made_a_set(wanted, scope, &facts)?;
            if !made.is_declined() {
                return Ok(made);
            }
        }
        // A membership a requires line wrote in another number system is the
        // one to carry, before the lemmas below are tried in their order.
        if label == "wcel" && kids.len() == 2 {
            let (s, sys) = (self.rpn(&kids[0]), self.rpn(&kids[1]));
            if let Some(found) = self.bridged(&s, &sys, scope, &facts)? {
                return Ok(Built(found));
            }
            // A function's value at a point of its domain, from the
            // function's type, spending none of the depth.
            if lookup(rules::SYSTEMS, sys.alone().unwrap_or_default()).is_some() {
                if let Some(found) = self.function_value(&s, &sys, scope, &facts)? {
                    return Ok(Built(found));
                }
                // A finite sum is a number because its terms are, spending
                // none of the depth (`summed`).
                if kids[0].variable().is_none() && kids[0].label() == Some("csu") {
                    if let Built(found) =
                        self.summed(&kids[0], &sys, scope, &facts, None)?
                    {
                        return Ok(Built(found));
                    }
                }
            }
        }
        // A sum, difference, product, power or negation is in a number
        // system because its parts are, spending none of the depth.
        if label == "wcel"
            && kids.len() == 2
            && kids[1]
                .label()
                .is_some_and(|l| lookup(rules::SYSTEMS, l).is_some())
        {
            let made = self.closed_under(wanted, scope, &facts, depth)?;
            if !made.is_declined() {
                return Ok(made);
            }
        }
        if lookup(rules::BOUND, label).is_some() {
            // A `define` and a `proof` block may write the same letter, and one of
            // them is renamed so that they do not collide: the same line.
            for (said, proof) in facts.entries() {
                if let Some(spelt) = self.respelt(&proof, &said, &rpn, scope)? {
                    return Ok(Built(spelt));
                }
            }
        }
        if let Some(p) = self.held_rebound(&facts, &rpn, scope)? {
            return Ok(Built(p));
        }
        if depth > 0 {
            let joined = self.conjoined(wanted, scope, &mut |me, one| {
                me.settle(one, scope, &facts, depth, step, lines)
            })?;
            if let Some(joined) = joined {
                return Ok(joined);
            }
            if label == "wrex" {
                if let Some(step) = step {
                    let lines = lines.cloned().unwrap_or_default();
                    return self.witnessed(step, wanted, scope, &facts, &lines);
                }
            }
            if label == "wral" {
                // A side condition may be asked of every member at once. The
                // name is fixed, the condition settled of it, and the claim
                // generalised; going under the binder spends no depth.
                let (body, variable, over) =
                    (kids[0].clone(), kids[1].clone(), kids[2].clone());
                self.in_family += 1;
                let made = self.for_every(
                    scope,
                    &facts,
                    &body,
                    &variable,
                    &over,
                    &mut |me, said, inner, lifted| {
                        me.settle(said, inner, lifted, depth, None, None)
                    },
                    false,
                );
                self.in_family -= 1;
                let made = made?;
                if !made.is_declined() {
                    return Ok(made);
                }
                // A line may say it whole over another letter.
                let respelt = self.fact_respelt(wanted, scope, &facts)?;
                return Ok(match respelt {
                    Some(p) => Built(p),
                    None => made,
                });
            }
            if label == "wf" && !self.map_types_off {
                if let Some(found) = self.map_into(wanted, scope, unfiltered, depth)? {
                    return Ok(Built(found));
                }
            }
            if let Some(found) = self.searched(wanted, scope, &facts, depth)? {
                return Ok(Built(found));
            }
            let found = self.rewritten(wanted, scope, &facts, depth)?;
            if !found.is_declined() {
                return Ok(found);
            }
        }
        if let Some(found) = self.instance_of_universal(&rpn, scope, &facts)? {
            return Ok(Built(found));
        }
        if depth > 0 {
            if let Some(found) =
                self.instance_at_a_term(wanted, scope, &facts, depth)?
            {
                return Ok(Built(found));
            }
        }
        Ok(self.no("cannot settle {}", &[&rpn]))
    }

    /// ( scope -> F : A ⟶ C ), F the name a define gives the map ( x ∈ A ↦
    /// B ), where B is in C at every point of A (`fmpt`, `feq1d`): a
    /// defined function's type, which the page says once where its rule is
    /// a number there by what it says once (`SYNTAX.md`, "A define with a
    /// parameter also states what its function is on").
    ///
    /// `facts` are the scope's whole, which holds its copy of the define's
    /// line; `settle` keeps of them what the step may rest on.
    fn map_into(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Option<Proof>> {
        let [domain, codomain, named] = wanted.children() else {
            return Ok(None);
        };
        // A define's name is equal to its map by the define's own line,
        // which every step may rest on.
        let var = match (named.label(), named.children()) {
            (Some("cv"), [v]) => self.rpn(v).alone().unwrap_or_default(),
            _ => return Ok(None),
        };
        let (Some(body), Some(label)) = (
            self.definitions.get(var).cloned(),
            self.defined_by.get(var).cloned(),
        ) else {
            return Ok(None);
        };
        let map = self.to_term(&body);
        if map.variable().is_some() || map.label() != Some("cmpt") {
            return Ok(None);
        }
        let Some(typed) = self.map_type(&map, domain, codomain, scope, facts, depth)?
        else {
            return Ok(None);
        };
        let (a, c, name) = (self.rpn(domain), self.rpn(codomain), self.rpn(named));
        let Some(equal) = self.held(facts, &t!(name, body, "wceq"), scope)? else {
            return Ok(None);
        };
        let turned = self.b.ap(
            "feq1d",
            &binds! {"ph" => scope, "A" => &a, "B" => &c, "F" => &name, "G" => &body},
            &[&equal],
        );
        let want = self.rpn(wanted);
        let theirs = t!(a, c, body, "wf");
        let made = pf!(self.b; scope, want, theirs, typed, turned, "mpbird");
        // The page says the type once, on the define's line, and a step
        // rests on it without naming that line, as on a letter's membership.
        Ok(Some(Proof {
            items: made.items,
            origin: std::iter::once(format!("{MEMBERSHIP}{label}")).collect(),
        }))
    }

    /// ( scope -> ( x ∈ A ↦ B ) : A ⟶ C ) where B is in C at every point of
    /// A (`fmpt`); None where the map is over another set, or the rule is
    /// not settled there.
    fn map_type(
        &mut self,
        map: &Term,
        domain: &Term,
        codomain: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Option<Proof>> {
        let [x, over, rule] = map.children() else {
            return Ok(None);
        };
        if self.rpn(over) != self.rpn(domain) {
            return Ok(None);
        }
        let (x, over, rule, codomain, map) = (
            self.rpn(x),
            self.rpn(over),
            self.rpn(rule),
            self.rpn(codomain),
            self.rpn(map),
        );
        let every = t!(t!(rule, codomain, "wcel"), x, over, "wral");
        let Built(each) =
            self.settle(&self.to_term(&every), scope, facts, depth - 1, None, None)?
        else {
            return Ok(None);
        };
        let iff = self.b.ap(
            "fmpt",
            &binds! {"x" => &x, "A" => &over, "B" => &codomain, "C" => &rule, "F" => &map},
            &[&pf!(self.b; map, "eqid")],
        );
        let want = t!(over, codomain, map, "wf");
        Ok(Some(pf!(self.b; scope, every, want, each, iff, "sylib")))
    }

    /// ( scope -> wanted ) where a fact says it of every member of a set and
    /// another puts a term in that set whose instance it is (`rspcv`), as
    /// `instantiate` reads a line at a name the step gives. A sum lemma
    /// moved to a letter the scope does not hold asks its terms at that
    /// letter, and the line the step cites says them of every index. The
    /// instance may spell a letter it binds otherwise than the wanted, as an
    /// integral inside it over t where the lemma's is over k, and is carried
    /// across that renaming as any fact is (`held_rebound`).
    pub(crate) fn instance_of_universal(
        &mut self,
        wanted: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        for (said, held) in facts.entries() {
            let whole = self.to_term(&said);
            if whole.variable().is_some() || whole.label() != Some("wral") {
                continue;
            }
            let (body, letter, domain) = (
                whole.children()[0].clone(),
                self.rpn(&whole.children()[1]),
                self.rpn(&whole.children()[2]),
            );
            let mark = t!(letter, "cv");
            for (member, inside) in facts.entries() {
                let m = self.to_term(&member);
                if m.variable().is_some()
                    || m.label() != Some("wcel")
                    || self.rpn(&m.children()[1]) != domain
                {
                    continue;
                }
                let at = self.rpn(&m.children()[0]);
                let instance = self.rpn(&self.restated(&body, &mark, &at));
                let across = if instance == *wanted {
                    None
                } else if self.rebound(&instance, wanted) {
                    let Some(across) = self.renaming_apart(&instance, wanted)? else {
                        continue;
                    };
                    Some(across)
                } else {
                    continue;
                };
                let ph = self.rpn(&body);
                // At the letter it binds the instance is the body itself, and
                // `rsp` takes it: `rspcv` keeps its term apart from the letter.
                let applied = if at == mark {
                    // `rsp` takes the "for all" first and the membership
                    // second, the other way round from `rspcv`.
                    let taken = self.b.ap(
                        "rsp",
                        &binds! {"ph" => &ph, "x" => &letter, "A" => &domain},
                        &[],
                    );
                    self.b.ap(
                        "com12",
                        &binds! {"ph" => &said, "ps" => &member, "ch" => &ph},
                        &[&taken],
                    )
                } else {
                    let tie = self.to_term(&t!(
                        t!(mark, at, "wceq"),
                        t!(ph, instance, "wb"),
                        "wi"
                    ));
                    let Built(asked) = self.prove_essential(&tie, scope, facts)? else {
                        continue;
                    };
                    self.b.ap(
                        "rspcv",
                        &binds! {"ph" => &ph, "ps" => &instance, "x" => &letter, "A" => &at, "B" => &domain},
                        &[&asked],
                    )
                };
                let carried = pf!(self.b; scope, member, t!(said, instance, "wi"), inside, applied, "syl");
                let proof = pf!(self.b; scope, said, instance, held, carried, "mpd");
                let Some(across) = across else {
                    return Ok(Some(proof));
                };
                let turned =
                    pf!(self.b; t!(instance, wanted, "wb"), scope, across, "a1i");
                return Ok(Some(
                    pf!(self.b; scope, instance, wanted, proof, turned, "mpbid"),
                ));
            }
        }
        Ok(None)
    }

    /// `instance_of_universal` at a term no fact puts in the set: the wanted
    /// is read as the "for all"'s body at some term, the term shown a member
    /// of the set by the search, and the line taken there. A requires line
    /// "for all i ∈ {1, …, 1}, i/(i + 1)! ∈ ℝ" is read at the numeral 1,
    /// which no line puts in {1, …, 1}. A membership asked in a wider number
    /// system than the body says is the body's carried there (`bridged`).
    pub(crate) fn instance_at_a_term(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Option<Proof>> {
        for (said, _) in facts.entries() {
            let whole = self.to_term(&said);
            if whole.variable().is_some() || whole.label() != Some("wral") {
                continue;
            }
            let (body, letter, domain) = (
                whole.children()[0].clone(),
                self.rpn(&whole.children()[1]),
                self.rpn(&whole.children()[2]),
            );
            // The body with its letter a pattern variable no part of it names.
            let text = self.rpn(&body);
            let Some(hole) = ["A", "B", "C", "D", "E", "F"]
                .into_iter()
                .find(|v| !text.has(v))
            else {
                continue;
            };
            fn holed(t: &Term, letter: &str, hole: &Term) -> Term {
                if t.label() == Some("cv") && t.children()[0].variable() == Some(letter)
                {
                    return hole.clone();
                }
                if t.variable().is_some() {
                    return t.clone();
                }
                let kids = t
                    .children()
                    .iter()
                    .map(|c| holed(c, letter, hole))
                    .collect();
                Term::apply(t.label().unwrap_or(""), kids)
            }
            let name = whole.children()[1].variable().unwrap_or("").to_string();
            let pattern = holed(&body, &name, &Term::var(hole));
            let vars: Vars = [Symbol::of(hole)].into_iter().collect();
            let membership = |t: &Term| {
                t.label() == Some("wcel")
                    && t.children().len() == 2
                    && t.children()[1]
                        .label()
                        .is_some_and(|l| lookup(rules::SYSTEMS, l).is_some())
            };
            let binding = fit(&pattern, wanted, &Binding::new(), &vars).or_else(|| {
                (membership(&pattern) && membership(wanted))
                    .then(|| {
                        fit(
                            &pattern.children()[0],
                            &wanted.children()[0],
                            &Binding::new(),
                            &vars,
                        )
                    })
                    .flatten()
            });
            let Some(at) = binding.and_then(|b| b.get(hole).cloned()) else {
                continue;
            };
            let at = self.rpn(&at);
            if letter.alone().is_some_and(|l| at.has(l)) {
                continue;
            }
            let member = self.to_term(&t!(at, domain, "wcel"));
            let Built(inside) =
                self.settle(&member, scope, facts, depth - 1, None, None)?
            else {
                continue;
            };
            let there = facts.copy();
            self.know(&there, self.rpn(&member), inside);
            let instance = self.rpn(&self.restated(&body, &t!(letter, "cv"), &at));
            let Some(p) = self.instance_of_universal(&instance, scope, &there)? else {
                continue;
            };
            let rpn = self.rpn(wanted);
            if instance == rpn {
                return Ok(Some(p));
            }
            self.know(&there, instance.clone(), p);
            if let Some(found) = self.held(&there, &rpn, scope)? {
                return Ok(Some(found));
            }
            if membership(wanted) {
                let (s, sys) = (
                    self.rpn(&wanted.children()[0]),
                    self.rpn(&wanted.children()[1]),
                );
                if let Some(found) = self.bridged(&s, &sys, scope, &there)? {
                    return Ok(Some(found));
                }
            }
        }
        Ok(None)
    }

    /// The declared lemmas that could conclude what is wanted, in order,
    /// through an index built from each lemma's own statement.
    fn declared(&mut self, wanted: &Term, backwards: bool) -> Vec<String> {
        let keys = self.head_keys(wanted);
        let index = self.lemma_index();
        index
            .iter()
            .filter(|(_, (heads, _))| {
                heads[backwards as usize].iter().any(|k| keys.contains(k))
            })
            .map(|(label, _)| label.clone())
            .collect()
    }

    /// The declared lemmas of one role, in the order they are declared.
    pub fn declared_as(&mut self, role: Role) -> Vec<String> {
        self.lemma_index()
            .iter()
            .filter(|(_, (_, said))| *said == role)
            .map(|(label, _)| label.clone())
            .collect()
    }

    /// Every declared lemma set.mm has, with its readings and its role.
    fn lemma_index(&mut self) -> &IndexMap<String, ([IndexSet<HeadKey>; 2], Role)> {
        if self.lemma_heads.is_none() {
            let mut index = IndexMap::new();
            for label in rules::MEMBERSHIP {
                if let Some(sig) = self.b.sigs.get(label) {
                    let sig = sig.clone();
                    index
                        .insert(label.to_string(), (self.heads(&sig), self.role(&sig)));
                }
            }
            self.lemma_heads = Some(index);
        }
        self.lemma_heads.as_ref().unwrap()
    }

    /// What a declared lemma is for, read off what it states.
    fn role(&self, sig: &Signature) -> Role {
        let whole = self.statement(&sig.label);
        if !sig.essentials.is_empty() {
            return Role::Side;
        }
        if sig.floats.len() == 1 && whole.label() == Some("wi") {
            let (given, gives) = (&whole.children()[0], &whole.children()[1]);
            if given.label() == Some("wcel")
                && gives.label() == Some("wcel")
                && given.children()[0].variable().is_some()
                && self.rpn(&given.children()[0]) == self.rpn(&gives.children()[0])
            {
                return Role::Carrier;
            }
        }
        Role::Side
    }

    /// What each reading of a lemma can end on, forwards and backwards.
    fn heads(&self, sig: &Signature) -> [IndexSet<HeadKey>; 2] {
        let whole = self.statement(&sig.label);
        let mut reads = whole.clone();
        while reads.label() == Some("wi") {
            reads = reads.children()[1].clone();
        }
        let said = if whole.label() == Some("wb") {
            whole.clone()
        } else {
            reads
        };
        let mut forward = vec![whole.clone()];
        let mut backward = Vec::new();
        if said.label() == Some("wb") {
            forward.push(said.children()[1].clone());
            backward.push(said.children()[0].clone());
        }
        let ends = |starts: Vec<Term>| {
            let mut out = IndexSet::new();
            for start in starts {
                let mut node = start;
                out.insert(self.head_key(&node));
                while node.label() == Some("wi") && node.variable().is_none() {
                    node = node.children()[1].clone();
                    out.insert(self.head_key(&node));
                }
            }
            out
        };
        [ends(forward), ends(backward)]
    }

    /// How a lemma's conclusion constrains what it can match.
    fn head_key(&self, node: &Term) -> HeadKey {
        if node.variable().is_some() {
            return HeadKey::Any;
        }
        if node.label() == Some("wcel")
            && node.children().len() == 2
            && node.children()[1].names().is_empty()
        {
            return HeadKey::Member(self.rpn(&node.children()[1]));
        }
        HeadKey::Head(node.label().unwrap_or("").to_string())
    }

    /// The keys a lemma's conclusion may carry and still match `wanted`.
    fn head_keys(&self, wanted: &Term) -> IndexSet<HeadKey> {
        let mut keys = IndexSet::new();
        keys.insert(HeadKey::Any);
        if wanted.variable().is_some() {
            return keys;
        }
        keys.insert(HeadKey::Head(wanted.label().unwrap_or("").to_string()));
        if wanted.label() == Some("wcel") && wanted.children().len() == 2 {
            keys.insert(HeadKey::Member(self.rpn(&wanted.children()[1])));
        }
        keys
    }

    /// What is wanted, with a term in it put as an equation in hand says.
    ///
    /// The equations are the ones in `facts`, which during a step is what the
    /// step names, so this rewrites only by a line the step cites. Only a
    /// term built from others is replaced, never a name or a constant. Each
    /// rewrite spends a level, and a term already being rewritten is not
    /// rewritten again, so the rewrites stop.
    fn rewritten(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Route<Proof>> {
        let want = self.rpn(wanted);
        if self.rewriting.contains(&want) {
            return Ok(self.no("{} is already being rewritten", &[&want]));
        }
        self.rewriting.insert(want.clone());
        let out = self.rewrite_by_facts(wanted, &want, scope, facts, depth);
        self.rewriting.shift_remove(&want);
        out
    }

    /// One pass over the equations in hand, for `rewritten`.
    fn rewrite_by_facts(
        &mut self,
        wanted: &Term,
        want: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Route<Proof>> {
        for said in facts.keys() {
            let equation = self.to_term(&said);
            if equation.label() != Some("wceq") || equation.children().len() != 2 {
                continue;
            }
            let (left, right) = (
                equation.children()[0].clone(),
                equation.children()[1].clone(),
            );
            for (old, new, flip) in [(&left, &right, true), (&right, &left, false)] {
                if old.variable().is_some()
                    || old.children().is_empty()
                    || old.label() == Some("cv")
                {
                    continue;
                }
                let (was, now) = (self.rpn(old), self.rpn(new));
                // A numeral is a constant however set.mm spells it, and so is
                // a sum of them.
                if was.tokens().iter().all(|t| rules::numeric(t.as_str())) {
                    continue;
                }
                let put = self.replaced(wanted, &was, new);
                if self.rpn(&put) == *want {
                    continue;
                }
                let Built(under) =
                    self.settle(&put, scope, facts, depth - 1, None, None)?
                else {
                    continue;
                };
                let leaf = Leaf::Rows(vec![Row::Cited {
                    was: was.clone(),
                    now: now.clone(),
                    said: said.clone(),
                    flip,
                }]);
                let Built(alike) =
                    self.congruence(&put, wanted, scope, facts, None, &leaf)?
                else {
                    continue;
                };
                return Ok(Built(
                    pf!(self.b; scope, self.rpn(&put), want, under, alike, "mpbid"),
                ));
            }
        }
        Ok(self.no("no equation in hand rewrites {}", &[want]))
    }

    /// `term` with every occurrence of the term spelt `was` put as `new`.
    pub(crate) fn replaced(&self, term: &Term, was: &Rpn, new: &Term) -> Term {
        if self.rpn(term) == *was {
            return new.clone();
        }
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        Term::apply(
            term.label().unwrap_or(""),
            term.children()
                .iter()
                .map(|c| self.replaced(c, was, new))
                .collect(),
        )
    }

    /// What is wanted, held by the scope under another name for a term: a
    /// declared equation is asked whether the fact in hand is the fact wanted
    /// said differently, and the congruence carries it across.
    ///
    /// A fact is read in other words only where no other is being read so:
    /// what this reaches through asks `settle` afresh, which starts its depth
    /// over, and each fact it asks may be a larger term than the last
    /// (|⌊A⌋| ∈ ℕ₀, then ||⌊A⌋|| ∈ ℕ₀), so a reading inside a reading has
    /// nothing that must decrease and need not end. No proof of the corpus
    /// reads a fact in other words inside such a reading.
    fn said_otherwise(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Option<Proof>> {
        let _ = depth;
        let want = self.rpn(wanted);
        if !self.saying.is_empty() {
            return Ok(None);
        }
        self.saying.insert(want.clone());
        let out = self.otherwise(wanted, &want, scope, facts);
        self.saying.shift_remove(&want);
        out
    }

    /// One pass over the facts in hand, for `said_otherwise`: the first
    /// whose standard form is what is wanted's.
    fn otherwise(
        &mut self,
        wanted: &Term,
        want: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        for (said, proof) in facts.entries() {
            if said == *want {
                continue;
            }
            let alike = self.same(&self.to_term(&said), wanted, scope, facts, None)?;
            if let Built(alike) = alike {
                return Ok(Some(pf!(self.b; scope, said, want, proof, alike, "mpbid")));
            }
        }
        Ok(None)
    }

    /// Whether one lemma settles what is wanted, and how.
    ///
    /// A biconditional says two things, so it can be read either way, and a
    /// lemma may ask something and only then say its two things: the asking
    /// is peeled off first and what is left is read the same way a bare
    /// biconditional is.
    fn fits(
        &mut self,
        label: &str,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
        backwards: bool,
    ) -> Checked<Option<Proof>> {
        let whole = self.statement(label);
        let mut asks = Vec::new();
        let mut joins = Vec::new();
        let mut reads = whole.clone();
        while reads.label() == Some("wi") {
            asks.push(reads.children()[0].clone());
            joins.push(Join::Implies);
            reads = reads.children()[1].clone();
        }
        let side = if backwards { 0 } else { 1 };
        let mut readings: Vec<(Vec<Term>, Vec<Join>, Term)> = Vec::new();
        if whole.label() == Some("wb") {
            readings.push((
                vec![whole.children()[1 - side].clone()],
                vec![Join::Iff],
                whole.children()[side].clone(),
            ));
            // and the biconditional itself, which a side condition may ask
            // for as it stands
            if !backwards {
                readings.push((Vec::new(), Vec::new(), whole.clone()));
            }
        } else if reads.label() == Some("wb") {
            let mut a = asks.clone();
            a.push(reads.children()[1 - side].clone());
            let mut j = joins.clone();
            j.push(Join::Iff);
            readings.push((a, j, reads.children()[side].clone()));
            if !backwards {
                readings.push((Vec::new(), Vec::new(), whole.clone()));
            }
        } else if !backwards {
            // Nothing was said two ways, so the statement is read as it
            // stands and `fitting` peels it.
            readings.push((Vec::new(), Vec::new(), whole.clone()));
        }
        for (antecedents, held, side) in readings {
            let found = self.fitting(
                label,
                &whole,
                antecedents,
                held,
                side,
                wanted,
                scope,
                facts,
                depth,
                backwards,
            )?;
            if found.is_some() {
                return Ok(found);
            }
        }
        Ok(None)
    }

    /// One reading of a lemma, applied to what is wanted: its antecedents
    /// are peeled until what is left is what is wanted.
    #[allow(clippy::too_many_arguments)]
    fn fitting(
        &mut self,
        label: &str,
        whole: &Term,
        mut antecedents: Vec<Term>,
        mut joins: Vec<Join>,
        reads: Term,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
        backwards: bool,
    ) -> Checked<Option<Proof>> {
        let variables = names_of(whole);
        let mut reads = reads;
        let binding = loop {
            if let Some(b) = fit(&reads, wanted, &Binding::new(), &variables) {
                break b;
            }
            if reads.label() != Some("wi") {
                return Ok(None);
            }
            antecedents.push(reads.children()[0].clone());
            joins.push(Join::Implies);
            reads = reads.children()[1].clone();
        };
        // What the lemma concludes need not fix everything it asks, so an
        // antecedent still open is matched against something already known,
        // whole, and failing that a conjunct at a time.
        let sig = self.sig(label).clone();
        let read = self.read_off(&sig, binding, &variables);
        let binding = self.opened(&antecedents, read, facts, &variables);
        self.fitted(
            label,
            &sig,
            &antecedents,
            &joins,
            wanted,
            scope,
            facts,
            depth,
            backwards,
            binding,
        )
    }

    /// The binding with what the antecedents leave open filled in.
    ///
    /// A conjunct asking where to look for something rather than anything of
    /// it is left to `sethood`, which reads it so, and is not matched. Every
    /// antecedent is matched whole before any is taken apart. Both are read
    /// through the standard form's one-way rules first, so that a fact
    /// answers a slot however either is spelt: `X ∈ 𝒫A` in hand fills the
    /// A of a slot asking `X ⊆ A`.
    fn opened(
        &mut self,
        antecedents: &[Term],
        binding: Binding,
        facts: &Facts,
        variables: &Vars,
    ) -> Binding {
        let mut binding = binding;
        let mut whole = Vec::new();
        let keys: Vec<Term> = facts
            .keys()
            .iter()
            .map(|held| {
                let held = self.to_term(held);
                self.read_through(&held, false, None)
            })
            .collect();
        for slot in antecedents {
            if slot.names().iter().all(|n| binding.contains_key(&**n)) {
                continue;
            }
            let slot = self.read_through(slot, false, None);
            let mut filled_any = false;
            for held in &keys {
                if let Some(filled) = fit(&slot, held, &binding, variables) {
                    binding = filled;
                    filled_any = true;
                    break;
                }
            }
            if !filled_any {
                whole.push(slot);
            }
        }
        for slot in &whole {
            for piece in conjuncts_of(slot) {
                if piece.names().iter().all(|n| binding.contains_key(&**n)) {
                    continue;
                }
                // A fixed function's type is what a line says of it, not a
                // place to look.
                if !sethood(&piece, &binding).is_empty()
                    && !function_fixed(&piece, &binding)
                {
                    continue;
                }
                for held in &keys {
                    if let Some(filled) = fit(&piece, held, &binding, variables) {
                        binding = filled;
                        break;
                    }
                }
            }
            // A class neither the claim nor a fact fixes is set.mm asking
            // where to look for the thing rather than asking anything of it,
            // and _V holds every set.
            for open in sethood(slot, &binding) {
                binding.insert(open, Term::apply("cvv", Vec::new()));
            }
        }
        binding
    }

    /// The lemma proved under one binding, or None where it is not.
    #[allow(clippy::too_many_arguments)]
    fn fitted(
        &mut self,
        label: &str,
        sig: &Signature,
        antecedents: &[Term],
        joins: &[Join],
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
        backwards: bool,
        binding: Binding,
    ) -> Checked<Option<Proof>> {
        let variables = names_of(&self.statement(label));
        // A declared lemma may state a hypothesis in full rather than ask for
        // it, which is a spelling and not a difference in what it leans on.
        let read = self.read_off(sig, binding, &variables);
        let binding = self.instanced(sig, read);
        let mut essentials = Vec::new();
        for e in &sig.essentials {
            let asked = self.essential(e).substitute(&binding);
            essentials.push(self.prove_essential(&asked, scope, facts)?);
        }
        let mut proofs = Vec::new();
        for one in essentials {
            match one {
                Built(p) => proofs.push(p),
                Declined(_) => return Ok(None),
            }
        }
        let mut proof = self.b.ap(
            label,
            &self.spelt(&binding),
            &proofs.iter().collect::<Vec<_>>(),
        );
        if antecedents.is_empty() {
            return Ok(Some(pf!(self.b; self.rpn(wanted), scope, proof, "a1i")));
        }
        for (i, slot) in antecedents.iter().enumerate() {
            let asks = slot.substitute(&binding);
            let mut rest = self.rpn(wanted);
            for (later, join) in antecedents[i + 1..].iter().zip(&joins[i + 1..]).rev()
            {
                let said = self.rpn(&later.substitute(&binding));
                // A biconditional read backwards states its sides the other
                // way round from the order they are taken in.
                rest = if *join == Join::Iff && backwards {
                    t!(rest, said, "wb")
                } else {
                    t!(said, rest, join_token(*join))
                };
            }
            let Built(under) =
                self.settle(&asks, scope, facts, depth - 1, None, None)?
            else {
                return Ok(None);
            };
            let first = proof.last() == label;
            let mut fold = discharge(joins[i], first);
            if joins[i] == Join::Iff && backwards {
                fold = if first { "sylibr" } else { "mpbird" };
            }
            proof = pf!(self.b; scope, self.rpn(&asks), rest, under, proof, fold);
        }
        Ok(Some(proof))
    }

    // --- congruence -----------------------------------------------------

    /// A target read as a tree, so a rewrite can walk down it: a target need
    /// not be one constructor, and each level wants its own congruence
    /// lemma.
    pub fn shape(&mut self, pattern: &str) -> Shape {
        if let Some(found) = self.shapes.get(pattern) {
            return found.clone();
        }
        let mut stack: Vec<Shape> = Vec::new();
        for token in pattern.split_whitespace() {
            if let Some(n) = token.strip_prefix('_') {
                stack.push(Shape::Hole(n.parse::<usize>().unwrap() - 1));
                continue;
            }
            let count = self.sig(token).floats.len();
            if count == 0 {
                stack.push(Shape::Const(token.to_string()));
                continue;
            }
            let args = stack.split_off(stack.len() - count);
            // The operation is an operand of the lemma that rewrites under it
            // where it is a constant, as `cabs` is in |x|. Where it is a hole
            // it is an argument like any other.
            match (rules::WRAPS.contains(&token), args.last()) {
                (true, Some(Shape::Const(op))) => {
                    let op = op.clone();
                    let kids = args[..args.len() - 1].to_vec();
                    stack.push(Shape::App(op, Some(token.to_string()), kids));
                }
                _ => stack.push(Shape::App(token.to_string(), None, args)),
            }
        }
        let found = stack.swap_remove(0);
        self.shapes.insert(pattern.to_string(), found.clone());
        found
    }

    /// A proof that `node` equals `node` with `old` replaced by `new`.
    ///
    /// The path from the root of the claim to the occurrence decides the
    /// lemmas, one per step along it, and which hole the occurrence sits in
    /// decides which lemma. Nothing is searched for.
    pub fn rewrite(
        &mut self,
        node: &Node,
        old: &Rpn,
        new: &Rpn,
        scope: &Rpn,
        eqproof: &Proof,
    ) -> Checked<Route<(Rpn, Proof)>> {
        if self.term(node)? == *old {
            return Ok(Built((new.clone(), eqproof.clone())));
        }
        // A library function's application fills what its definition builds
        // with its arguments; its name fills no slot.
        let library = self.library_application(node);
        let children: &[Node] = match &library {
            Some((_, arguments)) => arguments,
            None => &node.children,
        };
        // A binder's variable fills its slot as itself, and nothing rewrites
        // it; the body speaks of what the binder introduces.
        let bound = self
            .binders
            .get(&node.notation())
            .cloned()
            .unwrap_or_default();
        let walked = self.names_kept(|me| -> Checked<Route<Walked>> {
            for &i in &bound {
                let said = node.children[i].text.to_string();
                let var = me.binder_var(&said)?;
                me.names.insert(said, t!(var, "cv"));
            }
            let mut holes = Vec::new();
            for (i, c) in children.iter().enumerate() {
                holes.push(if bound.contains(&i) {
                    t!(me.binder_var(&c.text)?)
                } else {
                    me.term(c)?
                });
            }
            let mut after = holes.clone();
            let mut proofs = IndexMap::new();
            for (i, child) in children.iter().enumerate() {
                if bound.contains(&i) || !holds_run(&me.term(child)?, old) {
                    continue;
                }
                let (built, proof) =
                    take!(me.rewrite(child, old, new, scope, eqproof)?);
                after[i] = built;
                proofs.insert(i, proof);
            }
            Ok(Built(Walked {
                holes,
                after,
                proofs,
            }))
        })?;
        let Walked {
            holes,
            after,
            proofs,
        } = take!(walked);
        if proofs.is_empty() {
            let said = self.term(node)?;
            return Ok(Route::no(format!("nothing to rewrite in {said}")));
        }
        let pattern = match library {
            Some((builds, _)) => builds,
            None => self.pattern(node)?,
        };
        let tree = self.shape(&pattern);
        Ok(self.descend(&tree, &holes, &after, &proofs, scope))
    }

    /// Walk a target down to the holes that changed, a lemma a level.
    fn descend(
        &mut self,
        tree: &Shape,
        before: &[Rpn],
        after: &[Rpn],
        proofs: &IndexMap<usize, Proof>,
        scope: &Rpn,
    ) -> Route<(Rpn, Proof)> {
        let (label, wrap, kids) = match tree {
            Shape::Hole(i) => return Built((after[*i].clone(), proofs[i].clone())),
            Shape::Const(_) => return Route::no("no hole changed under this target"),
            Shape::App(label, wrap, kids) => (label, wrap, kids),
        };
        let was: Vec<Rpn> = kids.iter().map(|k| spell(k, before)).collect();
        let mut now = was.clone();
        let mut deeper = Vec::new();
        let mut slots = Vec::new();
        for (slot, kid) in kids.iter().enumerate() {
            if !proofs.keys().any(|h| holds(kid, *h)) {
                continue;
            }
            match self.descend(kid, before, after, proofs, scope) {
                Built((built, under)) => {
                    now[slot] = built;
                    deeper.push(under);
                    slots.push(slot);
                }
                Declined(d) => return Declined(d),
            }
        }
        if slots.is_empty() {
            return Route::no("no hole changed under this target");
        }
        // An operation or a relation is itself an operand of the lemma that
        // rewrites under it; a constructor that takes its arguments directly
        // is not. What changed comes first, old beside new, then the rest.
        let head = wrap.clone().unwrap_or_else(|| label.clone());
        let spelt_now = applied(&now, label, wrap.as_deref());
        if head == "csu" && slots.contains(&1) {
            let by_slot: IndexMap<usize, Proof> =
                slots.iter().copied().zip(deeper.iter().cloned()).collect();
            return self
                .summand_changed(scope, &was, &now, &by_slot)
                .map(|p| (spelt_now, p));
        }
        // A map or an indexed union over another domain: `mpteq1d` and
        // `iuneq1d` take the letter before the domains, so their parts are
        // given by name.
        if (head == "cmpt" || head == "ciun") && slots == [1] {
            let old_map = self.to_term(&t!(was[0], was[1], was[2], label));
            let new_map = self.to_term(&t!(now[0], now[1], now[2], label));
            if let Some(wider) =
                self.domain_holding(&old_map, &new_map, scope, &deeper[0])
            {
                return Built((spelt_now, wider));
            }
            let lemma =
                rules::congruence(&head, &[1]).expect("a congruence for a domain");
            return Built((
                spelt_now,
                self.b.ap(
                    lemma,
                    &binds! {"ph" => scope, "x" => &was[0], "A" => &was[1], "B" => &now[1], "C" => &was[2]},
                    &deeper.iter().collect::<Vec<_>>(),
                ),
            ));
        }
        // A value whose function changes: `fveq1d` takes the argument before
        // the two functions, so its parts are given by name.
        if head == "cfv" && slots == [1] {
            return Built((
                spelt_now,
                self.b.ap(
                    "fveq1d",
                    &binds! {"ph" => scope, "A" => &was[0], "F" => &was[1], "G" => &now[1]},
                    &deeper.iter().collect::<Vec<_>>(),
                ),
            ));
        }
        // A function changing in a statement that it is one-to-one, or onto:
        // the closed law after the equation by `syl`.
        if let Some(law) = rules::function_law(&head, &slots) {
            let parts =
                binds! {"A" => &was[0], "B" => &was[1], "F" => &was[2], "G" => &now[2]};
            let old = t!(was[0], was[1], was[2], head);
            let carried = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => t!(was[2], now[2], "wceq"),
                "ch" => t!(old, spelt_now, "wb")},
                &[&deeper[0], &self.b.ap(law, &parts, &[])],
            );
            return Built((spelt_now, carried));
        }
        let lemma = rules::congruence(&head, &slots)
            .unwrap_or_else(|| panic!("no congruence for {head} at {slots:?}"));
        let mut all: Vec<crate::mm::spell::Part> = vec![crate::elab::part(scope)];
        for &slot in &slots {
            all.push(crate::elab::part(&was[slot]));
            all.push(crate::elab::part(&now[slot]));
        }
        for (j, o) in was.iter().enumerate() {
            if !slots.contains(&j) {
                all.push(crate::elab::part(o));
            }
        }
        if wrap.is_some() {
            all.push(crate::elab::part(label));
        }
        all.extend(deeper.iter().map(|p| crate::elab::part(p)));
        all.push(crate::elab::part(lemma));
        Built((spelt_now, self.b.proof(&all)))
    }

    /// A sum rewritten where its summand changes, and its range maybe.
    ///
    /// `sumeq2sdv` rewrites the summand from an equation with no index in
    /// it, which set.mm lets it do only where the scope does not mention the
    /// index. The range, where it changes too, is rewritten first by
    /// `sumeq1d`, and `eqtrd` joins the two.
    fn summand_changed(
        &self,
        scope: &Rpn,
        was: &[Rpn],
        now: &[Rpn],
        proofs: &IndexMap<usize, Proof>,
    ) -> Route<Proof> {
        let (limits, summand, index) = (&was[0], &was[1], &was[2]);
        if index.alone().is_some_and(|i| scope.has(i)) {
            return Route::no("the scope mentions the index the sum binds");
        }
        let rewritten = self.b.ap(
            "sumeq2sdv",
            &binds! {"ph" => scope, "A" => &now[0], "B" => summand, "C" => &now[1], "k" => index},
            &[&proofs[&1]],
        );
        let Some(first) = proofs.get(&0) else {
            return Built(rewritten);
        };
        let moved = self.b.ap(
            "sumeq1d",
            &binds! {"ph" => scope, "A" => limits, "B" => &now[0], "C" => summand, "k" => index},
            &[first],
        );
        Built(self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => t!(limits, summand, index, "csu"),
            "B" => t!(now[0], summand, index, "csu"), "C" => t!(now[0], now[1], index, "csu")},
            &[&moved, &rewritten],
        ))
    }

    // --- closing a difference -------------------------------------------

    /// What a leaf of the walk says where two terms differ: a proof, a
    /// decline, or None where the walk goes a level in.
    pub fn leaf(
        &mut self,
        leaf: &Leaf,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Route<Proof>>> {
        match leaf {
            Leaf::Rows(rows) => {
                for row in rows {
                    let found = match row {
                        Row::Held => self.closed_held(one, other, where_, held)?,
                        Row::Cited {
                            was,
                            now,
                            said,
                            flip,
                        } => self.closed_cited(
                            one, other, where_, held, was, now, said, *flip,
                        )?,
                        Row::Assumed { was, now, under } => self.closed_assumed(
                            one, other, where_, held, was, now, under,
                        )?,
                        Row::Standard => {
                            self.closed_standard(one, other, where_, held)?
                        }
                        Row::Toward => self.closed_toward(one, other, where_, held)?,
                        Row::Identity => {
                            self.closed_identity(one, other, where_, held)?
                        }
                        Row::Bare => self.closed_bare(one, other, where_, held)?,
                    };
                    if found.is_some() {
                        return Ok(found);
                    }
                }
                Ok(None)
            }
            Leaf::Arithmetic { what, step } => {
                if !one.names().is_empty() || !other.names().is_empty() {
                    return Ok(None);
                }
                // A pair arithmetic does not work out whole, 2! and (1 + 1)!,
                // is carried a level in, where the pieces that change are.
                let claim = t!(self.rpn(one), self.rpn(other), "wceq");
                if super::field::decide_closed(&self.to_term(&claim)).is_declined() {
                    return Ok(None);
                }
                self.closed_fact(&claim, where_, held, what, Some(step))
                    .map(|p| Some(Built(p)))
            }
        }
    }

    /// Two terms that are one once their identity elements are dropped, x + 0
    /// and x, or a^(0 + 1) and a: each is carried to that one (`bared`).
    /// The walk goes a level in at a formula, and where the two are not one.
    fn closed_identity(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Route<Proof>>> {
        if self.rpn(one) == self.rpn(other) || self.is_wff(one) {
            return Ok(None);
        }
        let bare = self.without_identities(one);
        if self.rpn(&bare) != self.rpn(&self.without_identities(other)) {
            return Ok(None);
        }
        let mut links = Vec::new();
        if self.rpn(one) != self.rpn(&bare) {
            let made = match self.bared(one, where_, held)? {
                Built(p) => p,
                declined => return Ok(Some(declined)),
            };
            links.push(ChainLink {
                from: one.clone(),
                to: bare.clone(),
                proof: made,
            });
        }
        if self.rpn(other) != self.rpn(&bare) {
            let made = match self.bared(other, where_, held)? {
                Built(p) => p,
                declined => return Ok(Some(declined)),
            };
            links.push(ChainLink {
                from: bare.clone(),
                to: other.clone(),
                proof: self.flipped(where_, other, &bare, &made),
            });
        }
        Ok(Some(Built(self.chained(where_, &links))))
    }

    /// A part of a term carried to itself with its identity elements
    /// dropped, inside `bared`, where an element stands at its head; the
    /// walk goes a level in elsewhere.
    fn closed_bare(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Route<Proof>>> {
        if self.rpn(one) == self.rpn(other)
            || self.rpn(&self.without_identities(one)) != self.rpn(other)
            || one.variable().is_some()
        {
            return Ok(None);
        }
        let kids: Vec<Term> = one
            .children()
            .iter()
            .map(|c| self.without_identities(c))
            .collect();
        if self
            .identity_dropped(&Term::apply(one.label().unwrap_or(""), kids))
            .is_none()
        {
            return Ok(None);
        }
        Ok(Some(self.bared(one, where_, held)?))
    }

    /// ( where_ -> term = the term with its identity elements dropped ): its
    /// parts first, then each element at its head, by the law of
    /// `rules::IDENTITY` that drops it, which asks the operand be a number.
    fn bared(
        &mut self,
        term: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut links = Vec::new();
        let kids: Vec<Term> = term
            .children()
            .iter()
            .map(|c| self.without_identities(c))
            .collect();
        let mut cur = Term::apply(term.label().unwrap_or(""), kids);
        if self.rpn(&cur) != self.rpn(term) {
            let made = take!(self.congruence(
                term,
                &cur,
                where_,
                held,
                None,
                &Leaf::Rows(vec![Row::Bare]),
            )?);
            links.push(ChainLink {
                from: term.clone(),
                to: cur.clone(),
                proof: made,
            });
        }
        while let Some(kept) = self.identity_dropped(&cur) {
            let made = take!(self.identity_law(&cur, &kept, where_, held)?);
            links.push(ChainLink {
                from: cur.clone(),
                to: kept.clone(),
                proof: made,
            });
            cur = kept;
        }
        Ok(Built(self.chained(where_, &links)))
    }

    /// ( where_ -> term = kept ), where `kept` is `term` with the identity
    /// element at its head dropped, by the law of `rules::IDENTITY` that
    /// drops it.
    fn identity_law(
        &mut self,
        term: &Term,
        kept: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Route<Proof>> {
        // What a law asks, that the operand is a number, may be what a
        // requires line of the step says (`SYNTAX.md`), so the step's own
        // lines are offered over the scope's, as a membership is searched
        // for elsewhere.
        let written = held.filtered(|_, v| from_requires(v));
        for (k, w) in self.written.entries() {
            if let Some(lifted) = self.lifted_to(&k, &w.proof, &w.at, where_) {
                self.know(&written, k, lifted);
            }
        }
        let offered = held.with(&written);
        let goal = self.to_term(&t!(self.rpn(term), self.rpn(kept), "wceq"));
        for label in rules::IDENTITY {
            if let Built(p) =
                self.apply_lemma(label, &goal, where_, &offered, None, false, None)?
            {
                return Ok(Built(p));
            }
        }
        Ok(self.no("no identity law drops it from {}", &[&self.rpn(term)]))
    }

    /// The operand an identity element leaves, where `term` is an operation
    /// with its identity in a hole the notation record allows it: x for
    /// x + 0, 0 + x, x − 0, x·1, 1·x, x/1 and x^1. None otherwise.
    fn identity_dropped(&self, term: &Term) -> Option<Term> {
        if term.variable().is_some() {
            return None;
        }
        for law in &self.identities {
            if term.label() != Some(law.constructor.as_str())
                || term.children().len() != law.fixed.len() + 2
                || law.fixed.iter().any(|(k, token)| {
                    self.rpn(&term.children()[*k]).alone() != Some(token.as_str())
                })
            {
                continue;
            }
            let element = super::field::numeral(law.element);
            for &hole in &law.holes {
                let (at, other) = if hole == 0 {
                    (law.places.0, law.places.1)
                } else {
                    (law.places.1, law.places.0)
                };
                if self.rpn(&term.children()[at]) == element {
                    return Some(term.children()[other].clone());
                }
            }
        }
        None
    }

    /// Two terms an equation in hand says are equal.
    fn closed_held(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Route<Proof>>> {
        let (a, b) = (self.rpn(one), self.rpn(other));
        if a == b {
            return Ok(None);
        }
        Ok(self.held(held, &t!(a, b, "wceq"), where_)?.map(Built))
    }

    /// The place one cited equation rewrote, carried back. The line says
    /// `was = now` or `now = was` (`flip`), and what carries the settled
    /// term back is `now = was`.
    #[allow(clippy::too_many_arguments)]
    fn closed_cited(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
        was: &Rpn,
        now: &Rpn,
        said: &Rpn,
        flip: bool,
    ) -> Checked<Option<Route<Proof>>> {
        if self.rpn(one) != *now || self.rpn(other) != *was {
            return Ok(None);
        }
        let Some(proof) = self.held(held, said, where_)? else {
            return Ok(Some(self.no("{} is not in hand here", &[said])));
        };
        Ok(Some(Built(if flip {
            pf!(self.b; where_, was, now, proof, "eqcomd")
        } else {
            proof
        })))
    }

    /// The place a lemma's own assumed equation says the two agree: the
    /// equation is handed over as a fact rather than reproved at the leaf.
    #[allow(clippy::too_many_arguments)]
    fn closed_assumed(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
        was: &Rpn,
        now: &Rpn,
        under: &Rpn,
    ) -> Checked<Option<Route<Proof>>> {
        if self.rpn(one) == *was && self.rpn(other) == *now {
            Ok(self.held(held, under, where_)?.map(Built))
        } else {
            Ok(None)
        }
    }

    // --- one standard form ----------------------------------------------

    /// ( scope -> given <-> want ), or `=` for classes, where the two have
    /// one standard form; a decline where they do not.
    ///
    /// What a lemma says and what the page says may differ in how they are
    /// written and not in what they say. Each is a rule of `rules::STANDARD`
    /// or `rules::SYMMETRIC`, or a renaming, and the two are the same claim
    /// exactly when their standard forms agree up to the letters they bind.
    pub fn same(
        &mut self,
        given: &Term,
        want: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        // The two are compared with their defined names written out, and
        // what that asks of a part is asked of it written out, so the facts
        // are read the same way.
        let read;
        let facts = if self.reading_facts || self.definitions.is_empty() {
            facts
        } else {
            read = self.read_memberships(scope, facts, step)?;
            &read
        };
        // The standard form reads a defined name as its body, so the letters
        // that body binds are bound in what is compared as well: a body's
        // letter read as a name would put an equation in a different order
        // from the same equation over the page's letter.
        let (given_read, want_read) = (self.read_out(given), self.read_out(want));
        let mut letters = self.letters_bound(&given_read);
        letters.extend(self.letters_bound(&want_read));
        let kept = std::mem::replace(&mut self.binding, letters);
        let out = self.congruence(
            given,
            want,
            scope,
            facts,
            step,
            &Leaf::Rows(vec![Row::Standard]),
        );
        self.binding = kept;
        out
    }

    /// The variables a term binds: each set variable standing directly under
    /// a constructor other than `cv`, as `rebound` reads them. A set variable
    /// stands only where a binder puts it or under `cv`; a class variable
    /// under a constructor is a term the statement is about, and is bound by
    /// nothing.
    pub fn letters_bound(&self, term: &Term) -> Vars {
        let mut out = Vars::new();
        let mut rest = vec![term.clone()];
        while let Some(node) = rest.pop() {
            if node.variable().is_some() {
                continue;
            }
            if node.label() != Some("cv") {
                out.extend(
                    node.children()
                        .iter()
                        .filter_map(|c| c.variable_symbol())
                        .filter(|v| self.is_setvar(&self.float_of(v))),
                );
            }
            rest.extend(node.children().iter().cloned());
        }
        out
    }

    /// What decides which of a symmetric pair goes first: the term as
    /// reverse Polish, with every letter the statement binds read as a
    /// blank.
    fn order_key(&self, term: &Term) -> String {
        if let Some(v) = term.variable() {
            if self.binding.contains(v) {
                return "_".to_string();
            }
            return self.float_of(v);
        }
        let mut parts: Vec<String> =
            term.children().iter().map(|c| self.order_key(c)).collect();
        parts.push(term.label().unwrap_or("").to_string());
        parts.join(" ")
    }

    /// The term with every rule applied, parts first, each pair in order.
    pub fn standard(&mut self, term: &Term) -> Term {
        let key = (self.rpn(term), self.binding.clone(), self.names_readable());
        if let Some(found) = self.standards.get(&key) {
            return found.clone();
        }
        let found = if term.variable().is_some() || term.children().is_empty() {
            term.clone()
        } else {
            let kids: Vec<Term> =
                term.children().iter().map(|c| self.standard(c)).collect();
            let parts = Term::apply(term.label().unwrap_or(""), kids);
            match self.standard_step(&parts) {
                None => parts,
                Some((_, next)) => self.standard(&next),
            }
        };
        self.standards.insert(key, found.clone());
        found
    }

    /// The term with each defined name, and each map applied to an argument,
    /// read as what it stands for (`named_body`, `applied_body`), parts
    /// first, and nothing else changed: no rule rewrites it and no pair is
    /// put in order, so its other parts are spelt as the page spelt them.
    pub fn read_out(&mut self, term: &Term) -> Term {
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        let kids: Vec<Term> =
            term.children().iter().map(|c| self.read_out(c)).collect();
        let parts = Term::apply(term.label().unwrap_or(""), kids);
        let binding = self.binding.clone();
        if let Some(body) = self.named_body(&parts, &binding) {
            return self.read_out(&body);
        }
        if let Some(body) = self.applied_body(&parts) {
            return self.read_out(&body);
        }
        parts
    }

    /// One rewrite toward the standard form at the head of `term`; None
    /// where nothing rewrites the head.
    pub fn standard_step(&mut self, term: &Term) -> Option<(How, Term)> {
        if term.variable().is_some() {
            return None;
        }
        let binding = self.binding.clone();
        if let Some(body) = self.named_body(term, &binding) {
            return Some((How::Defined, body));
        }
        if let Some(body) = self.applied_body(term) {
            return Some((How::Applied, body));
        }
        self.written_step(term)
    }

    /// `standard_step` by the rules alone: a declared rule, or a symmetric
    /// pair put in order, and never a defined name or a map read as what it
    /// stands for, which depend on what the step cites and on the scope.
    fn written_step(&mut self, term: &Term) -> Option<(How, Term)> {
        if term.variable().is_some() {
            return None;
        }
        for rule in self.rewrites(false).iter() {
            if let Some(bound) = fit(&rule.given, term, &Binding::new(), &rule.names) {
                if rule.gives.names().iter().all(|n| bound.contains_key(&**n)) {
                    return Some((
                        How::Rule(rule.label.clone()),
                        rule.gives.substitute(&bound),
                    ));
                }
            }
        }
        if term.label() == Some("wceq") && term.children().len() == 2 {
            let (a, b) = (&term.children()[0], &term.children()[1]);
            if self.order_key(b) < self.order_key(a) {
                return Some((
                    How::Eqcom,
                    Term::apply("wceq", vec![b.clone(), a.clone()]),
                ));
            }
        }
        for c in self.commutes.clone() {
            let (i, j) = c.places;
            if term.label() != Some(c.constructor.as_str())
                || term.children().len() != c.fixed.len() + 2
            {
                continue;
            }
            if c.fixed.iter().any(|(k, token)| {
                self.rpn(&term.children()[*k]).alone() != Some(token.as_str())
            }) {
                continue;
            }
            if self.order_key(&term.children()[j]) < self.order_key(&term.children()[i])
            {
                let mut kids = term.children().to_vec();
                kids.swap(i, j);
                return Some((How::Commuted, Term::apply(&c.constructor, kids)));
            }
        }
        None
    }

    /// What a name a `define` introduced names, where `term` is that name
    /// standing free and the proof being built may rest on the define; else
    /// None. A letter the compared statements bind is never a defined name.
    ///
    /// A step that uses what a define says cites it (`SYNTAX.md`), so a name
    /// whose define the step does not cite stays a name: x₁ ∈ S, cited from
    /// the define of S and a line saying x₁ ∈ [a, b], reads S as its set and
    /// x₁ as written.
    pub fn named_body(&self, term: &Term, bound: &Vars) -> Option<Term> {
        if term.variable().is_some()
            || term.label() != Some("cv")
            || term.children().len() != 1
        {
            return None;
        }
        if term.children()[0]
            .variable()
            .is_some_and(|v| bound.contains(v))
        {
            return None;
        }
        let var = self.rpn(&term.children()[0]);
        let var = var.alone().unwrap_or_default();
        if !self.may_read(var) {
            return None;
        }
        let body = self.definitions.get(var)?;
        Some(self.to_term(body))
    }

    /// Whether the proof being built may read the defined name `var` as what
    /// it names: whether it may rest on the name's define.
    fn may_read(&self, var: &str) -> bool {
        match (&self.resting, self.defined_by.get(var)) {
            (Some(allowed), Some(label)) => allowed.contains(label),
            _ => true,
        }
    }

    /// The defined names the proof being built may read, as a key.
    fn names_readable(&self) -> String {
        let readable: Vec<&str> = self
            .definitions
            .keys()
            .filter(|v| self.may_read(v))
            .map(String::as_str)
            .collect();
        readable.join(" ")
    }

    /// What a map applied to a value comes to: the map's rule with the value
    /// for the name it binds; else None.
    ///
    /// A letter the rule binds is kept apart from every letter the value
    /// spells, bound there or not; where they meet, the rule is read in its
    /// other spelling (`rule_apart`).
    fn applied_body(&mut self, term: &Term) -> Option<Term> {
        if term.label() == Some("co") {
            return self.applied_body_of_two(term);
        }
        let f = self.applied_map(term)?;
        let at = term.children()[0].clone();
        let (bound, rule) = (f.children()[0].clone(), f.children()[2].clone());
        let mut spelt: BTreeSet<String> = self
            .rpn(&at)
            .tokens()
            .iter()
            .map(|t| t.to_string())
            .collect();
        let through = self.read_through(&at, true, None);
        spelt.extend(self.rpn(&through).tokens().iter().map(|t| t.to_string()));
        let own = bound.variable().unwrap_or("").to_string();
        let meets = |me: &Self, one: &Term| {
            me.letters_bound(one)
                .iter()
                .filter(|v| ***v != *own)
                .any(|v| {
                    let label = me.float_of(v);
                    spelt.contains(&label) && me.is_setvar(&label)
                })
        };
        let mut rule = rule;
        if meets(self, &rule) {
            let other = self.rule_apart(&f);
            if !meets(self, &other) {
                rule = other;
            }
        }
        let was = t!(self.rpn(&bound), "cv");
        Some(self.restated(&rule, &was, &self.rpn(&at)))
    }

    /// The map of two arguments an application `( A F B )` applies, written
    /// as a map or as the name a define gave it; else None.
    fn applied_map_of_two(&self, term: &Term) -> Option<Term> {
        if term.variable().is_some()
            || term.label() != Some("co")
            || term.children().len() != 3
        {
            return None;
        }
        let mut f = term.children()[2].clone();
        if let Some(named) = self.named_body(&f, &self.binding) {
            f = named;
        }
        if f.variable().is_some()
            || f.label() != Some("cmpo")
            || f.children().len() != 5
        {
            return None;
        }
        Some(f)
    }

    /// What a map of two arguments applied to two values comes to: its rule
    /// with the first value for its first letter and the second for its
    /// second; else None, and None where a value spells a letter the rule
    /// binds, which would be captured.
    fn applied_body_of_two(&mut self, term: &Term) -> Option<Term> {
        let f = self.applied_map_of_two(term)?;
        let (first, second) = (term.children()[0].clone(), term.children()[1].clone());
        let kids = f.children();
        let (x, y, rule) = (kids[0].clone(), kids[1].clone(), kids[4].clone());
        let spelt: BTreeSet<String> = [&first, &second]
            .iter()
            .flat_map(|v| {
                self.rpn(v)
                    .tokens()
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
            })
            .collect();
        let bound: Vec<String> = self
            .letters_bound(&rule)
            .iter()
            .map(|v| self.float_of(v))
            .chain([self.rpn(&x).to_string(), self.rpn(&y).to_string()])
            .collect();
        if bound.iter().any(|v| spelt.contains(v)) {
            return None;
        }
        let at_first = self.restated(&rule, &t!(self.rpn(&x), "cv"), &self.rpn(&first));
        Some(self.restated(&at_first, &t!(self.rpn(&y), "cv"), &self.rpn(&second)))
    }

    /// ( where -> ( A F B ) = S ), S the rule of F's map of two at A and B:
    /// `ovmpoga` at the map as written, and the define's equation carries it
    /// to the name (`oveqd`). A decline where A or B is not shown to be in
    /// its domain.
    fn applied_proof_of_two(
        &mut self,
        cur: &Term,
        nxt: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Route<Proof>> {
        let kids = cur.children();
        let (a, b, written) =
            (self.rpn(&kids[0]), self.rpn(&kids[1]), self.rpn(&kids[2]));
        let map = self.applied_map_of_two(cur).expect("an applied map of two");
        let m = map.children();
        let (x, y, c, d, r) = (
            self.rpn(&m[0]),
            self.rpn(&m[1]),
            self.rpn(&m[2]),
            self.rpn(&m[3]),
            self.rpn(&m[4]),
        );
        let s = self.rpn(nxt);
        // The rule moves one letter at a time, the first to A and then the
        // second to B, and `sylan9eq` joins the two moves.
        let (x_is, y_is) = (t!(x, "cv", a, "wceq"), t!(y, "cv", b, "wceq"));
        let halfway = self.rpn(&self.restated(&m[4], &t!(x, "cv"), &a));
        let first = self.to_term(&t!(x_is, t!(r, halfway, "wceq"), "wi"));
        let first =
            take!(self.prove_essential(&first, &Rpn::default(), &Facts::new())?);
        let second = self.to_term(&t!(y_is, t!(halfway, s, "wceq"), "wi"));
        let second =
            take!(self.prove_essential(&second, &Rpn::default(), &Facts::new())?);
        let instance = self.b.ap(
            "sylan9eq",
            &binds! {"ph" => &x_is, "ps" => &y_is, "A" => &r, "B" => &halfway, "C" => &s},
            &[&first, &second],
        );
        let mut members = Vec::new();
        for want in [t!(a, c, "wcel"), t!(b, d, "wcel"), t!(s, "cvv", "wcel")] {
            members.push(take!(self.settle(
                &self.to_term(&want),
                where_,
                held,
                3,
                None,
                None
            )?));
        }
        let mapped = self.rpn(&map);
        let closed = self.b.ap(
            "ovmpoga",
            &binds! {"x" => &x, "y" => &y, "A" => &a, "B" => &b, "C" => &c, "D" => &d,
            "R" => &r, "S" => &s, "F" => &mapped, "H" => "cvv"},
            &[&instance, &pf!(self.b; mapped, "eqid")],
        );
        let three = self.b.ap(
            "3jca",
            &binds! {"ph" => where_, "ps" => t!(a, c, "wcel"), "ch" => t!(b, d, "wcel"),
            "th" => t!(s, "cvv", "wcel")},
            &[&members[0], &members[1], &members[2]],
        );
        let value = t!(t!(a, b, mapped, "co"), s, "wceq");
        let direct = pf!(self.b; where_,
            t!(t!(a, c, "wcel"), t!(b, d, "wcel"), t!(s, "cvv", "wcel"), "w3a"),
            value, three, closed, "syl");
        if written == mapped {
            return Ok(Built(direct));
        }
        // A defined name is carried to its map first.
        let Some(named) = self.held(held, &t!(written, mapped, "wceq"), where_)? else {
            return Ok(Route::no("the equation a define holds is not in hand"));
        };
        let via = self.b.ap(
            "oveqd",
            &binds! {"ph" => where_, "A" => &written, "B" => &mapped, "C" => &a, "D" => &b},
            &[&named],
        );
        Ok(Built(self.b.ap(
            "eqtrd",
            &binds! {"ph" => where_, "A" => t!(a, b, written, "co"), "B" => t!(a, b, mapped, "co"), "C" => &s},
            &[&via, &direct],
        )))
    }

    /// A map's rule with every setvar it binds, but the map's own, renamed to
    /// letters nothing holds when it is first asked for: one spelling per
    /// map, so that the rule at any value reads one way wherever it is read.
    fn rule_apart(&mut self, f: &Term) -> Term {
        let key = self.rpn(f);
        if let Some(found) = self.rules_read.get(&key) {
            return found.clone();
        }
        let (bound, mut rule) = (f.children()[0].clone(), f.children()[2].clone());
        let own = bound.variable().unwrap_or("").to_string();
        let mut letters: Vec<Symbol> = self
            .letters_bound(&rule)
            .into_iter()
            .filter(|v| *v != own)
            .collect();
        letters.sort_by_key(|v| {
            self.b.float_order(&self.float_of(v)).unwrap_or(usize::MAX)
        });
        for letter in letters {
            let label = self.float_of(&letter);
            if !self.is_setvar(&label) {
                continue;
            }
            let Some(fresh) = self.unheld(&[&rule, f]) else {
                break;
            };
            let mut put = Binding::new();
            put.insert(letter, fresh);
            rule = rule.substitute(&put);
        }
        self.rules_read.insert(key, rule.clone());
        rule
    }

    /// The rules of `rules::STANDARD` set.mm has. A rule that asks something
    /// first holds only where that is so, which a standard form cannot know;
    /// such a rule is `conditional`, and is used only where it closes a
    /// difference the walk has found.
    pub fn rewrites(&mut self, conditional: bool) -> Rc<[Rewrite]> {
        if self.rewrite_rules.is_none() {
            let [plain, asking] = self.standard_rules();
            self.rewrite_rules = Some([plain.into(), asking.into()]);
        }
        Rc::clone(&self.rewrite_rules.as_ref().unwrap()[conditional as usize])
    }

    /// The rules of `rules::STANDARD` set.mm has, those that ask nothing
    /// first and those that do (`rewrites`).
    pub fn standard_rules(&self) -> [Vec<Rewrite>; 2] {
        let mut plain = Vec::new();
        let mut asking = Vec::new();
        for (label, side) in rules::STANDARD {
            if !self.b.sigs.contains_key(label) {
                continue;
            }
            let says = self.statement(label);
            let mut body = says.clone();
            while body.label() == Some("wi") {
                body = body.children()[1].clone();
            }
            let s = *side as usize;
            let rule = Rewrite {
                label: label.to_string(),
                given: body.children()[1 - s].clone(),
                gives: body.children()[s].clone(),
                names: names_of(&says),
            };
            if says.label() == Some("wi") {
                asking.push(rule);
            } else {
                plain.push(rule);
            }
        }
        [plain, asking]
    }

    /// ( where -> cur <-> nxt ), or `=`, for one rewrite at the head.
    pub fn standard_proof(
        &mut self,
        cur: &Term,
        how: &How,
        nxt: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Route<Proof>> {
        let (a, b) = (self.rpn(cur), self.rpn(nxt));
        match how {
            How::Defined => Ok(match self.held(held, &t!(a, b, "wceq"), where_)? {
                Some(p) => Built(p),
                None => Route::no("the equation a define holds is not in hand"),
            }),
            How::Applied if cur.label() == Some("co") => {
                self.applied_proof_of_two(cur, nxt, where_, held)
            }
            How::Applied => self.applied_proof(cur, nxt, where_, held),
            How::Eqcom => {
                let (left, right) =
                    (self.rpn(&cur.children()[0]), self.rpn(&cur.children()[1]));
                let law =
                    self.b
                        .ap("eqcom", &binds! {"A" => &left, "B" => &right}, &[]);
                Ok(Built(pf!(self.b; t!(a, b, "wb"), where_, law, "a1i")))
            }
            How::Commuted => {
                let goal = self.to_term(&t!(a, b, "wceq"));
                self.settle(&goal, where_, held, 3, None, None)
            }
            How::Rule(label) => {
                let wff = self.is_wff(cur);
                let join = if wff { "wb" } else { "wceq" };
                if lookup(rules::STANDARD, label) == Some(Side::Right) {
                    let goal = self.to_term(&t!(a, b, join));
                    return self
                        .apply_lemma(label, &goal, where_, held, None, false, None);
                }
                let goal = self.to_term(&t!(b, a, join));
                let made =
                    take!(self
                        .apply_lemma(label, &goal, where_, held, None, false, None)?);
                Ok(Built(if wff {
                    self.b.ap(
                        "bicomd",
                        &binds! {"ph" => where_, "ps" => &b, "ch" => &a},
                        &[&made],
                    )
                } else {
                    self.b.ap(
                        "eqcomd",
                        &binds! {"ph" => where_, "A" => &b, "B" => &a},
                        &[&made],
                    )
                }))
            }
        }
    }

    /// The map a function application applies, written as a map or as the
    /// name a define gave it; else None.
    fn applied_map(&self, term: &Term) -> Option<Term> {
        if term.variable().is_some()
            || term.label() != Some("cfv")
            || term.children().len() != 2
        {
            return None;
        }
        let mut f = term.children()[1].clone();
        if let Some(named) = self.named_body(&f, &self.binding) {
            f = named;
        }
        if f.variable().is_some()
            || f.label() != Some("cmpt")
            || f.children().len() != 3
        {
            return None;
        }
        Some(f)
    }

    /// ( where -> ( F ` A ) = C ), C the rule of F's map at A; a decline
    /// where A is not shown to be in the map's domain.
    fn applied_proof(
        &mut self,
        cur: &Term,
        nxt: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Route<Proof>> {
        let (at, written) = (cur.children()[0].clone(), cur.children()[1].clone());
        let own = self.applied_map(cur).expect("an applied map");
        let mut f = own.clone();
        let (bound, over, mut rule) = (
            own.children()[0].clone(),
            own.children()[1].clone(),
            own.children()[2].clone(),
        );
        let c = self.rpn(nxt);
        // Where the rule was read in its other spelling, the map is first
        // shown to be the same map over that spelling, closed, and the value
        // is taken there.
        let apart = self.rules_read.get(&self.rpn(&own)).cloned();
        let mut renamed = None;
        if let Some(apart) = apart {
            let was = t!(self.rpn(&bound), "cv");
            if self.rpn(&self.restated(&rule, &was, &self.rpn(&at))) != c {
                f = Term::apply(
                    own.label().unwrap_or(""),
                    vec![bound.clone(), over.clone(), apart.clone()],
                );
                rule = apart;
                renamed = self.class_alpha(&own, &f)?;
                if renamed.is_none() {
                    return Ok(Route::no("the rule is not renamed apart"));
                }
            }
        }
        let x = self.rpn(&bound);
        let a = self.rpn(&at);
        let b = self.rpn(&rule);
        let d = self.rpn(&over);
        let written_f = self.rpn(&written);
        let tie = self.to_term(&t!(t!(x, "cv", a, "wceq"), t!(b, c, "wceq"), "wi"));
        let instance =
            take!(self.prove_essential(&tie, &Rpn::default(), &Facts::new())?);
        let member = take!(self.settle(
            &self.to_term(&t!(a, d, "wcel")),
            where_,
            held,
            3,
            None,
            None
        )?);
        let a_set = take!(self.settle(
            &self.to_term(&t!(c, "cvv", "wcel")),
            where_,
            held,
            3,
            None,
            None
        )?);
        let mapped = self.rpn(&f);
        let direct = self.b.ap(
            "fvmptd3",
            &binds! {"ph" => where_, "x" => &x, "A" => &a, "B" => &b, "C" => &c, "D" => &d, "F" => &mapped, "V" => "cvv"},
            &[&pf!(self.b; mapped, "eqid"), &instance, &member, &a_set],
        );
        if written_f == mapped {
            return Ok(Built(direct));
        }
        // A defined name is carried to its map first.
        let spelt = self.rpn(&own);
        let mut named = None;
        if written_f != spelt {
            named = self.held(held, &t!(written_f, spelt, "wceq"), where_)?;
            if named.is_none() {
                return Ok(Route::no("the equation a define holds is not in hand"));
            }
        }
        if let Some(renamed) = renamed {
            let same_map =
                pf!(self.b; t!(spelt, mapped, "wceq"), where_, renamed, "a1i");
            named = Some(match named {
                None => same_map,
                Some(n) => self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => where_, "A" => &written_f, "B" => &spelt, "C" => &mapped},
                    &[&n, &same_map],
                ),
            });
        }
        let named = named.expect("a proof the name is its map");
        let via = self.b.ap(
            "fveq1d",
            &binds! {"ph" => where_, "A" => &a, "F" => &written_f, "G" => &mapped},
            &[&named],
        );
        Ok(Built(self.b.ap(
            "eqtrd",
            &binds! {"ph" => where_, "A" => t!(a, written_f, "cfv"), "B" => t!(a, mapped, "cfv"), "C" => &c},
            &[&via, &direct],
        )))
    }

    /// Whether a term is a statement rather than a class.
    pub fn is_wff(&self, term: &Term) -> bool {
        let label = match term.variable() {
            Some(v) => self.float_of(v),
            None => term.label().unwrap_or("").to_string(),
        };
        self.typecode(&label) == "wff"
    }

    /// One proof of the first term against the last, from links each proving
    /// one against the next, joined by `bitrd` or `eqtrd`.
    pub fn chained(&self, where_: &Rpn, links: &[ChainLink]) -> Proof {
        let (first, mut last, mut proof) = (
            links[0].from.clone(),
            links[0].to.clone(),
            links[0].proof.clone(),
        );
        let wff = self.is_wff(&first);
        let start = self.rpn(&first);
        for ChainLink {
            to: now,
            proof: more,
            ..
        } in &links[1..]
        {
            let (mid, end) = (self.rpn(&last), self.rpn(now));
            proof = if wff {
                self.b.ap(
                    "bitrd",
                    &binds! {"ph" => where_, "ps" => &start, "ch" => &mid, "th" => &end},
                    &[&proof, more],
                )
            } else {
                self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => where_, "A" => &start, "B" => &mid, "C" => &end},
                    &[&proof, more],
                )
            };
            last = now.clone();
        }
        proof
    }

    /// Whether the walk can go a level in from these two: the same
    /// constructor, and a lemma in `rules::CONGRUENCE` for the places that
    /// differ; under an existential only its body may.
    fn lifts(&self, one: &Term, other: &Term) -> bool {
        if one.variable().is_some()
            || other.variable().is_some()
            || one.label() != other.label()
            || one.children().len() != other.children().len()
        {
            return false;
        }
        let spelt: Vec<Rpn> = one.children().iter().map(|c| self.rpn(c)).collect();
        let theirs: Vec<Rpn> = other.children().iter().map(|c| self.rpn(c)).collect();
        let label = one.label().unwrap_or("");
        if label == "wrex" && spelt[1] != theirs[1] {
            return false;
        }
        if label == "csu" && spelt[1] != theirs[1] {
            return spelt[0] == theirs[0] && spelt[2] == theirs[2];
        }
        let mut places = spelt.len();
        if rules::WRAPS.contains(&label) && spelt[places - 1] == theirs[places - 1] {
            places -= 1;
        }
        let slots: Vec<usize> =
            (0..places).filter(|&i| spelt[i] != theirs[i]).collect();
        slots.is_empty()
            || rules::congruence(label, &slots).is_some()
            || rules::function_law(label, &slots).is_some()
    }

    /// `one` carried to `other`, its standard form: where only the parts
    /// rewrite, the walk goes a level in; otherwise the parts are put in
    /// standard form first, the head is rewritten once, and what that gives
    /// is carried on the same way.
    fn closed_toward(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Route<Proof>>> {
        if self.rpn(one) == self.rpn(other) {
            return Ok(None);
        }
        // A function applied keeps its function.
        let wrapped = rules::WRAPS.contains(&one.label().unwrap_or(""));
        let n = one.children().len();
        let kids: Vec<Term> = one
            .children()
            .iter()
            .enumerate()
            .map(|(i, c)| {
                if wrapped && i == n - 1 {
                    c.clone()
                } else {
                    self.standard(c)
                }
            })
            .collect();
        let parts = Term::apply(one.label().unwrap_or(""), kids);
        if self.rpn(&parts) == self.rpn(other) && self.lifts(one, &parts) {
            return Ok(None);
        }
        let mut links: Vec<ChainLink> = Vec::new();
        let mut cur = one.clone();
        if self.rpn(&parts) != self.rpn(one) {
            if !self.lifts(one, &parts) {
                return Ok(Some(Route::no("the parts cannot be rewritten in place")));
            }
            let made = self.congruence(
                one,
                &parts,
                where_,
                held,
                None,
                &Leaf::Rows(vec![Row::Toward]),
            )?;
            let Built(made) = made else {
                return Ok(Some(made));
            };
            links.push(ChainLink {
                from: one.clone(),
                to: parts.clone(),
                proof: made,
            });
            cur = parts;
        }
        let Some((how, nxt)) = self.standard_step(&cur) else {
            return Ok(Some(Route::no("no rule rewrites the head")));
        };
        let made = self.standard_proof(&cur, &how, &nxt, where_, held)?;
        let Built(made) = made else {
            return Ok(Some(made));
        };
        links.push(ChainLink {
            from: cur,
            to: nxt.clone(),
            proof: made,
        });
        if self.rpn(&nxt) != self.rpn(other) {
            let made = self.congruence(
                &nxt,
                other,
                where_,
                held,
                None,
                &Leaf::Rows(vec![Row::Toward]),
            )?;
            let Built(made) = made else {
                return Ok(Some(made));
            };
            links.push(ChainLink {
                from: nxt,
                to: other.clone(),
                proof: made,
            });
        }
        Ok(Some(Built(self.chained(where_, &links))))
    }

    /// Two terms with one standard form, at the smallest place they differ:
    /// each carried to its standard form, and the two forms joined by a
    /// renaming where they differ only in the letters they bind.
    fn closed_standard(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Route<Proof>>> {
        let (a, b) = (self.rpn(one), self.rpn(other));
        if a == b {
            return Ok(None);
        }
        // Two that differ only in the letters they bind are one claim by a
        // renaming, which is closed and asks nothing of the scope.
        if self.rebound(&a, &b) {
            let wff = self.is_wff(one);
            let renamed = if wff {
                self.renamed_apart(one, other)?
            } else {
                self.class_renamed(one, other)?
            };
            if let Some(renamed) = renamed {
                let join = if wff { "wb" } else { "wceq" };
                return Ok(Some(Built(
                    pf!(self.b; t!(a, b, join), where_, renamed, "a1i"),
                )));
            }
        }
        let (ours, theirs) = (self.standard(one), self.standard(other));
        let (said, want) = (self.rpn(&ours), self.rpn(&theirs));
        // Letters bound at two depths are paired at each by `class_alpha`
        // and not by `rebound`, which pairs them once for the whole term.
        if said != want && !self.rebound(&said, &want) {
            let unpaired =
                self.is_wff(&ours) || self.class_alpha(&ours, &theirs)?.is_none();
            if unpaired {
                return Ok(self.conditioned(one, other, where_, held)?.map(Built));
            }
        }
        if self.lifts(one, other) {
            let mut all = true;
            for (x, y) in one.children().iter().zip(other.children()) {
                if !self.alike_in_place(x, y) {
                    all = false;
                    break;
                }
            }
            if all {
                return Ok(None); // the walk goes a level in
            }
        }
        // One rewrite at the head of either side, and the walk again from
        // there, touches only what differs.
        for (x, y, forward) in [(one, other, true), (other, one, false)] {
            let Some((how, nxt)) = self.standard_step(x) else {
                continue;
            };
            let Built(made) = self.standard_proof(x, &how, &nxt, where_, held)? else {
                continue;
            };
            let mut links = vec![ChainLink {
                from: x.clone(),
                to: nxt.clone(),
                proof: made,
            }];
            if self.rpn(&nxt) != self.rpn(y) {
                let Built(rest) = self.congruence(
                    &nxt,
                    y,
                    where_,
                    held,
                    None,
                    &Leaf::Rows(vec![Row::Standard]),
                )?
                else {
                    continue;
                };
                links.push(ChainLink {
                    from: nxt,
                    to: y.clone(),
                    proof: rest,
                });
            }
            let proof = self.chained(where_, &links);
            return Ok(Some(Built(if forward {
                proof
            } else {
                self.flipped(where_, x, y, &proof)
            })));
        }
        let mut links: Vec<ChainLink> = Vec::new();
        if self.rpn(&ours) != a {
            let made = self.congruence(
                one,
                &ours,
                where_,
                held,
                None,
                &Leaf::Rows(vec![Row::Toward]),
            )?;
            let Built(made) = made else {
                return Ok(Some(made));
            };
            links.push(ChainLink {
                from: one.clone(),
                to: ours.clone(),
                proof: made,
            });
        }
        if said != want {
            let wff = self.is_wff(&ours);
            let renamed = if wff {
                self.renamed_apart(&ours, &theirs)?
            } else {
                self.class_alpha(&ours, &theirs)?
            };
            let Some(renamed) = renamed else {
                return Ok(Some(Route::no("no renaming says the two are one")));
            };
            let join = if wff { "wb" } else { "wceq" };
            links.push(ChainLink {
                from: ours.clone(),
                to: theirs.clone(),
                proof: pf!(self.b; t!(said, want, join), where_, renamed, "a1i"),
            });
        }
        if self.rpn(&theirs) != b {
            let made = self.congruence(
                other,
                &theirs,
                where_,
                held,
                None,
                &Leaf::Rows(vec![Row::Toward]),
            )?;
            let Built(made) = made else {
                return Ok(Some(made));
            };
            let flipped = self.flipped(where_, other, &theirs, &made);
            links.push(ChainLink {
                from: theirs.clone(),
                to: other.clone(),
                proof: flipped,
            });
        }
        Ok(Some(Built(self.chained(where_, &links))))
    }

    /// A closed proof that two statements differing in their bound letters
    /// are one, by way of letters neither holds; else None.
    pub fn renamed_apart(
        &mut self,
        one: &Term,
        other: &Term,
    ) -> Checked<Option<Proof>> {
        let (a, b) = (self.rpn(one), self.rpn(other));
        self.renaming_apart(&a, &b)
    }

    /// Whether two parts come to one standard form, where the walk can close
    /// them one by one below. Classes may also differ in the letters they
    /// bind, which only `class_renamed` closes and only at the class itself.
    fn alike_in_place(&mut self, one: &Term, other: &Term) -> bool {
        let said = self.standard(one);
        let said = self.rpn(&said);
        let want = self.standard(other);
        let want = self.rpn(&want);
        said == want || (!self.is_wff(one) && self.rebound(&said, &want))
    }

    /// Two maps differing in their letter, over a domain that binds one of
    /// the two letters itself: `cbvmptv` holds both apart from the domain,
    /// so the domain's own letter is moved to one neither map holds first
    /// (`mpteq1i`), the maps' letter renamed over the domain so spelt, and
    /// the other map carried back. g(x) = √x over D = {x ∈ ℝ : x > 0} is
    /// such a map. None where the domain binds neither letter.
    fn renamed_over_a_domain_apart(
        &mut self,
        one: &Term,
        other: &Term,
    ) -> Checked<Option<Proof>> {
        let letters: Vars = [&one.children()[0], &other.children()[0]]
            .iter()
            .filter_map(|v| v.variable_symbol())
            .collect();
        let (domain, there) = (&one.children()[1], &other.children()[1]);
        let clashing: Vec<Symbol> = self
            .letters_bound(domain)
            .union(&self.letters_bound(there))
            .filter(|v| letters.contains(*v))
            .copied()
            .collect();
        if clashing.is_empty() {
            return Ok(None);
        }
        let Some(moved) = self.unheld_for(clashing, &[one, other]) else {
            return Ok(None);
        };
        let apart = domain.substitute(&moved);
        let to_apart = |me: &mut Self, d: &Term| -> Checked<Option<Proof>> {
            if me.rpn(d) == me.rpn(&apart) {
                let d = me.rpn(d);
                return Ok(Some(me.b.ap("eqid", &binds! {"A" => &d}, &[])));
            }
            me.class_alpha(d, &apart)
        };
        let (Some(from_one), Some(from_other)) =
            (to_apart(self, domain)?, to_apart(self, there)?)
        else {
            return Ok(None);
        };
        let over = |map: &Term| {
            let kids = vec![
                map.children()[0].clone(),
                apart.clone(),
                map.children()[2].clone(),
            ];
            Term::apply("cmpt", kids)
        };
        let (one_there, other_there) = (over(one), over(other));
        let (Some(first), Some(last)) = (
            self.by_lemma("mpteq1i", one, &one_there, &[&from_one]),
            self.by_lemma("mpteq1i", other, &other_there, &[&from_other]),
        ) else {
            return Ok(None);
        };
        let Some(middle) = self.class_renamed(&one_there, &other_there)? else {
            return Ok(None);
        };
        let (a, b, c, d) = (
            self.rpn(one),
            self.rpn(&one_there),
            self.rpn(&other_there),
            self.rpn(other),
        );
        let to_there = self.b.ap(
            "eqtri",
            &binds! {"A" => &a, "B" => &b, "C" => &c},
            &[&first, &middle],
        );
        Ok(Some(self.b.ap(
            "eqtr4i",
            &binds! {"A" => &a, "B" => &c, "C" => &d},
            &[&to_there, &last],
        )))
    }

    /// A closed proof that two classes differing in the letter they bind are
    /// one (`one = other`), by the lemma `rules::CLASS_BOUND` names for the
    /// binder; else None.
    fn class_renamed(&mut self, one: &Term, other: &Term) -> Checked<Option<Proof>> {
        let lemma = if one.variable().is_none() && other.label() == one.label() {
            one.label().and_then(|l| lookup(rules::CLASS_BOUND, l))
        } else {
            None
        };
        let Some(lemma) = lemma else {
            return Ok(None);
        };
        let says = self.statement(lemma);
        let variables = names_of(&says);
        let Some(binding) = fit(&says.children()[0], one, &Binding::new(), &variables)
            .and_then(|b| fit(&says.children()[1], other, &b, &variables))
        else {
            return Ok(None);
        };
        let sig = self.sig(lemma).clone();
        let asked = self.essential(&sig.essentials[0]).substitute(&binding);
        let said = self.prove_essential(&asked, &Rpn::default(), &Facts::new())?;
        let Built(said) = said else {
            return self.class_renamed_within(one, other);
        };
        Ok(Some(self.b.ap(lemma, &self.spelt(&binding), &[&said])))
    }

    /// The closed `lemma` applied so that it states `one` against `other`,
    /// its variables read off matching the two; else None.
    fn by_lemma(
        &self,
        lemma: &str,
        one: &Term,
        other: &Term,
        given: &[&Proof],
    ) -> Option<Proof> {
        let says = self.statement(lemma);
        let variables = names_of(&says);
        let binding = fit(&says.children()[0], one, &Binding::new(), &variables)
            .and_then(|b| fit(&says.children()[1], other, &b, &variables))?;
        Some(self.b.ap(lemma, &self.spelt(&binding), given))
    }

    /// A closed proof of `one = other`, two classes that differ only in the
    /// letters they bind; None where they differ in more, or not at all.
    pub fn class_alpha(&mut self, one: &Term, other: &Term) -> Checked<Option<Proof>> {
        let (a, b) = (self.rpn(one), self.rpn(other));
        if a == b
            || one.variable().is_some()
            || other.variable().is_some()
            || one.label() != other.label()
            || one.children().len() != other.children().len()
        {
            return Ok(None);
        }
        let label = one.label().unwrap_or("").to_string();
        if lookup(rules::CLASS_BOUND, &label).is_some() {
            // The renaming lemmas hold their two letters apart, so they are
            // asked only where the letters differ.
            let letters = label != "cmpt"
                || self.rpn(&one.children()[0]) != self.rpn(&other.children()[0]);
            if letters && label == "cmpt" {
                if let Some(p) = self.renamed_over_a_domain_apart(one, other)? {
                    return Ok(Some(p));
                }
            }
            let renamed = if letters {
                self.class_renamed(one, other)?
            } else {
                None
            };
            if !letters {
                // One letter over both: the domain and the rule are carried
                // each by itself, and `mpteq12i` asks nothing of the letter.
                let mut parts = Vec::new();
                for (x, y) in one.children()[1..].iter().zip(&other.children()[1..]) {
                    if self.rpn(x) == self.rpn(y) {
                        let x = self.rpn(x);
                        parts.push(Some(self.b.ap("eqid", &binds! {"A" => &x}, &[])));
                    } else {
                        parts.push(self.class_alpha(x, y)?);
                    }
                }
                if parts.iter().any(Option::is_none) {
                    return Ok(None);
                }
                let parts: Vec<Proof> = parts.into_iter().flatten().collect();
                let k: Vec<Rpn> = one.children().iter().map(|c| self.rpn(c)).collect();
                let o: Vec<Rpn> =
                    other.children().iter().map(|c| self.rpn(c)).collect();
                return Ok(Some(self.b.ap(
                    "mpteq12i",
                    &binds! {"x" => &k[0], "A" => &k[1], "B" => &k[2], "C" => &o[1], "D" => &o[2]},
                    &[&parts[0], &parts[1]],
                )));
            }
            if renamed.is_some() || lookup(rules::DOMAIN, &label).is_none() {
                return Ok(renamed);
            }
            // The domain may differ too, in the letters it binds: the domain
            // is made the other's first, and the letter renamed over the
            // domain the two then share.
            let (x, y) = (&one.children()[1], &other.children()[1]);
            let Some(inner) = self.class_alpha(x, y)? else {
                return Ok(None);
            };
            let mut kids = one.children().to_vec();
            kids[1] = y.clone();
            let there = Term::apply(&label, kids);
            let lemma = lookup(rules::DOMAIN, &label).unwrap();
            let Some(moved) = self.by_lemma(lemma, one, &there, &[&inner]) else {
                return Ok(None);
            };
            let there_rpn = self.rpn(&there);
            if there_rpn == b {
                return Ok(Some(moved));
            }
            let rest = if letters {
                self.class_renamed(&there, other)?
            } else {
                None
            };
            let Some(rest) = rest else {
                return Ok(None);
            };
            return Ok(Some(self.b.ap(
                "eqtri",
                &binds! {"A" => &a, "B" => &there_rpn, "C" => &b},
                &[&moved, &rest],
            )));
        }
        let mut here = one.clone();
        let mut proof: Option<Proof> = None;
        for (i, (x, y)) in one.children().iter().zip(other.children()).enumerate() {
            if self.rpn(x) == self.rpn(y) {
                continue;
            }
            let lemma = class_lift(&label, i);
            let inner = self.class_alpha(x, y)?;
            let (Some(lemma), Some(inner)) = (lemma, inner) else {
                return Ok(None);
            };
            let mut kids = here.children().to_vec();
            kids[i] = y.clone();
            let there = Term::apply(here.label().unwrap_or(""), kids);
            let Some(step) = self.by_lemma(lemma, &here, &there, &[&inner]) else {
                return Ok(None);
            };
            proof = Some(match proof {
                None => step,
                Some(p) => self.b.ap(
                    "eqtri",
                    &binds! {"A" => &a, "B" => self.rpn(&here), "C" => self.rpn(&there)},
                    &[&p, &step],
                ),
            });
            here = there;
        }
        Ok(proof)
    }

    /// `class_renamed` where a binder sits inside the one renamed: the outer
    /// letter of `other` is put back to `one`'s, the bodies are then one
    /// class by renaming the inner binder, which `rules::CLASS_BODY` carries
    /// up through the outer, and the outer is renamed last.
    fn class_renamed_within(
        &mut self,
        one: &Term,
        other: &Term,
    ) -> Checked<Option<Proof>> {
        if one.label() == Some("crab") {
            return self.selection_renamed_within(one, other);
        }
        let Some(body_lemma) = one.label().and_then(|l| lookup(rules::CLASS_BODY, l))
        else {
            return Ok(None);
        };
        let letters: Vec<(usize, Term)> = one
            .children()
            .iter()
            .enumerate()
            .filter(|(_, c)| {
                c.variable().is_some()
                    && self.typecode(self.rpn(c).alone().unwrap_or_default())
                        == "setvar"
            })
            .map(|(i, c)| (i, c.clone()))
            .collect();
        if letters.len() != 1 {
            return Ok(None);
        }
        let (at, ours) = letters[0].clone();
        let theirs = other.children()[at].clone();
        if theirs.variable().is_none() || theirs.variable() == ours.variable() {
            return Ok(None);
        }
        let mut put = Binding::new();
        put.insert(theirs.variable_symbol().unwrap(), ours.clone());
        let middle = other.substitute(&put);
        let differ: Vec<usize> = (0..one.children().len())
            .filter(|&i| {
                self.rpn(&one.children()[i]) != self.rpn(&middle.children()[i])
            })
            .collect();
        if differ.len() != 1 {
            return Ok(None);
        }
        let Some(inner) = self
            .class_renamed(&one.children()[differ[0]], &middle.children()[differ[0]])?
        else {
            return Ok(None);
        };
        let says = self.statement(body_lemma);
        let variables = names_of(&says);
        let Some(binding) = fit(&says.children()[0], one, &Binding::new(), &variables)
            .and_then(|b| fit(&says.children()[1], &middle, &b, &variables))
        else {
            return Ok(None);
        };
        let sig = self.sig(body_lemma).clone();
        let asked = self.essential(&sig.essentials[0]).substitute(&binding);
        let (under, equal) = (
            self.rpn(&asked.children()[0]),
            self.rpn(&asked.children()[1]),
        );
        let carried =
            self.b
                .ap("a1i", &binds! {"ph" => &equal, "ps" => &under}, &[&inner]);
        let lifted = self.b.ap(body_lemma, &self.spelt(&binding), &[&carried]);
        let Some(outer) = self.class_renamed(&middle, other)? else {
            return Ok(None);
        };
        Ok(Some(self.b.ap(
            "eqtri",
            &binds! {"A" => self.rpn(one), "B" => self.rpn(&middle), "C" => self.rpn(other)},
            &[&lifted, &outer],
        )))
    }

    /// `class_renamed_within` of a selection, {y ∈ B | φ}, whose body is a
    /// statement: the body's own bound letters are renamed first, under the
    /// selection's letter as it stands (`renaming`, carried in by `rabbii`),
    /// and then the selection's letter (`class_renamed`). {y ∈ B : there is
    /// x ∈ X with F(x) = y} is so {j ∈ B : there is i ∈ X with F(i) = j}.
    fn selection_renamed_within(
        &mut self,
        one: &Term,
        other: &Term,
    ) -> Checked<Option<Proof>> {
        let [_, ours, _] = one.children() else {
            return Ok(None);
        };
        let theirs = &other.children()[1];
        let (Some(_), Some(their_letter)) = (ours.variable(), theirs.variable()) else {
            return Ok(None);
        };
        if ours.variable() == theirs.variable() {
            return Ok(None);
        }
        let mut put = Binding::new();
        put.insert(Symbol::of(their_letter), ours.clone());
        let middle = other.substitute(&put);
        if self.rpn(&one.children()[2]) != self.rpn(&middle.children()[2]) {
            return Ok(None);
        }
        let Some(inner) = self.renaming(&one.children()[0], &middle.children()[0])?
        else {
            return Ok(None);
        };
        let Some(lifted) = self.by_lemma("rabbii", one, &middle, &[&inner]) else {
            return Ok(None);
        };
        let Some(outer) = self.class_renamed(&middle, other)? else {
            return Ok(None);
        };
        Ok(Some(self.b.ap(
            "eqtri",
            &binds! {"A" => self.rpn(one), "B" => self.rpn(&middle), "C" => self.rpn(other)},
            &[&lifted, &outer],
        )))
    }

    /// ( where -> y <-> x ), or `=`, from a proof of `x` against `y`.
    pub fn flipped(&self, where_: &Rpn, x: &Term, y: &Term, proof: &Proof) -> Proof {
        let (a, b) = (self.rpn(x), self.rpn(y));
        if self.is_wff(x) {
            self.b.ap(
                "bicomd",
                &binds! {"ph" => where_, "ps" => &a, "ch" => &b},
                &[proof],
            )
        } else {
            self.b.ap(
                "eqcomd",
                &binds! {"ph" => where_, "A" => &a, "B" => &b},
                &[proof],
            )
        }
    }

    /// Two terms a conditional rule makes one, at this place; else None: the
    /// rule is applied to either side where it stands, what it asks is
    /// settled here, and what it gives must then have the other side's
    /// standard form.
    fn conditioned(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Proof>> {
        for rule in self.rewrites(true).iter() {
            for (a, b, forward) in [(one, other, true), (other, one, false)] {
                let Some(bound) = fit(&rule.given, a, &Binding::new(), &rule.names)
                else {
                    continue;
                };
                if !rule.gives.names().iter().all(|n| bound.contains_key(&**n)) {
                    continue;
                }
                let became = rule.gives.substitute(&bound);
                let ours = self.standard(&became);
                let ours = self.rpn(&ours);
                let theirs = self.standard(b);
                let theirs = self.rpn(&theirs);
                if ours != theirs && !self.rebound(&ours, &theirs) {
                    continue;
                }
                let Built(made) = self.standard_proof(
                    a,
                    &How::Rule(rule.label.clone()),
                    &became,
                    where_,
                    held,
                )?
                else {
                    continue;
                };
                let mut links = vec![ChainLink {
                    from: a.clone(),
                    to: became.clone(),
                    proof: made,
                }];
                if self.rpn(&became) != self.rpn(b) {
                    let Built(rest) = self.congruence(
                        &became,
                        b,
                        where_,
                        held,
                        None,
                        &Leaf::Rows(vec![Row::Standard]),
                    )?
                    else {
                        continue;
                    };
                    links.push(ChainLink {
                        from: became,
                        to: b.clone(),
                        proof: rest,
                    });
                }
                let proof = self.chained(where_, &links);
                return Ok(Some(if forward {
                    proof
                } else {
                    self.flipped(where_, a, b, &proof)
                }));
            }
        }
        Ok(None)
    }

    // --- a lemma's own substitutions ------------------------------------

    /// A wff slot an essential fixes by saying it is a substitution: `elrab`
    /// asks `( x = A -> ( ph <-> ps ) )`, and where the claim has not filled
    /// `ps` this hypothesis is the only thing that says what it is.
    pub fn substituted_slot(&self, asked: &Term, binding: &Binding) -> Option<Binding> {
        if asked.label() != Some("wi") || asked.children().len() != 2 {
            return None;
        }
        let (same_, iff) = (&asked.children()[0], &asked.children()[1]);
        if same_.label() != Some("wceq") || iff.label() != Some("wb") {
            return None;
        }
        let over = same_.children()[0].substitute(binding);
        let element = same_.children()[1].substitute(binding);
        let (body, slot) = (&iff.children()[0], &iff.children()[1]);
        let held = slot.variable().and_then(|v| binding.get(v));
        if slot.variable().is_none()
            || over.label() != Some("cv")
            || over.children()[0].variable().is_none()
            || held.is_some_and(|h| h.variable() != slot.variable())
            || !body.names().iter().all(|n| binding.contains_key(&**n))
        {
            return None;
        }
        // The body holds the variable as a binder writes it, `cv` over a
        // setvar; the element is a class. Stripping the `cv` is what lets the
        // one stand in for the other.
        let name = over.children()[0].variable().unwrap().to_string();
        let marks: BTreeSet<String> = std::iter::once(name.clone()).collect();
        let said = as_class(&body.substitute(binding), &marks);
        let mut put = Binding::new();
        put.insert(Symbol::of(&name), element);
        let mut out = Binding::new();
        out.insert(slot.variable_symbol().unwrap(), said.substitute(&put));
        Some(out)
    }

    /// The side of an equation, the innermost body of an existential, that
    /// names none of its witnesses, where the other names one; else None.
    fn witnessless_side(
        &self,
        body: &Term,
        layers: &[(Term, Rpn, Rpn)],
    ) -> Option<Rpn> {
        if body.label() != Some("wceq") || body.children().len() != 2 {
            return None;
        }
        let names = |t: &Term| {
            let spelt = self.rpn(t);
            layers
                .iter()
                .any(|(_, v, _)| v.alone().is_some_and(|v| spelt.has(v)))
        };
        let (left, right) = (&body.children()[0], &body.children()[1]);
        match (names(left), names(right)) {
            (false, true) => Some(self.rpn(left)),
            (true, false) => Some(self.rpn(right)),
            _ => None,
        }
    }

    /// A restricted existential, with as many witnesses as it quantifies
    /// over, from the lines a step names for it: what `exhibit` proves, and
    /// the right side a definition concludes from (`conclude`).
    ///
    /// The text never writes the witness as a witness: it writes a line that
    /// happens to name one. Taken from the lines the step cites and its
    /// `requires` lines, in that order, and never searched for among the
    /// facts in scope. Each sentence of a line is read, and an equation
    /// facing either way. Built from the innermost quantifier out, which is
    /// the order the witnesses go in.
    pub fn witnessed(
        &mut self,
        step: &Step,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let mut layers: Vec<(Term, Rpn, Rpn)> = Vec::new();
        let mut rest = wanted.clone();
        while rest.label() == Some("wrex") {
            let kids = rest.children().to_vec();
            layers.push((kids[0].clone(), self.rpn(&kids[1]), self.rpn(&kids[2])));
            rest = kids[0].clone();
        }
        // A line proved before a block opened holds inside it too, and the
        // scope's own copy is what says so where the step sits.
        let mut sources: Vec<(Rpn, Proof)> = Vec::new();
        for cited in step.just.refs.iter().filter_map(|r| lines.get(r)) {
            let proof = match self.held(facts, &cited.term, scope)? {
                Some(p) => p,
                None => cited.proof.clone(),
            };
            sources.push((cited.term, proof));
        }
        for r in &step.requires {
            let said = self.claim_of(&r.fact)?;
            if let Some(proof) = self.held(facts, &said, scope)? {
                sources.push((said, proof));
            }
        }
        // A cited line that is the claim once identity elements are dropped
        // and bound letters renamed names no witness: it is the claim
        // (`reached`), as "there is q ∈ ℤ with q·N = A" is "there is z ∈ ℤ
        // with z·N + 0 = A".
        let want = self.rpn(wanted);
        for (said, proof) in &sources {
            if self.to_term(said).label() != Some("wrex") {
                continue;
            }
            if let Some(p) = self.reached(proof, said, &want, scope, facts)? {
                return Ok(Built(p));
            }
        }
        // An equation the body asks whose one side names no witness is the
        // same on both sides once the witnesses are read off the other, and
        // needs no line (`SYNTAX.md`, the literal-instance rule): a·x + b·y =
        // a·m + b·n is met by m := x and n := y.
        if let Some(sides) = self.witnessless_side(&rest, &layers) {
            let said = t!(sides, sides, "wceq");
            let proof = self
                .b
                .ap("eqidd", &binds! {"ph" => scope, "A" => &sides}, &[]);
            sources.push((said, proof));
        }
        // The witnesses are as many as a line names, from the outermost
        // quantifier in: a line saying "n ∈ ℕ₀ and there is f with …" names
        // n, and the "there is f" is what the claim says of it. The deepest
        // the cited lines reach is the one taken.
        let quantified = layers;
        let mut layers = Vec::new();
        let mut chosen = None;
        // A line that leaves out an identity element the body has, or has
        // one the body leaves out, names the same witnesses (`SYNTAX.md`, "An
        // identity element goes without saying"); each line is read as
        // written first.
        for bare in [false, true] {
            if chosen.is_some() {
                break;
            }
            'depths: for depth in (1..=quantified.len()).rev() {
                let here = quantified[..depth].to_vec();
                let mut rest = here[depth - 1].0.clone();
                if bare {
                    rest = self.without_identities(&rest);
                }
                let marks: BTreeSet<Rpn> =
                    here.iter().map(|(_, v, _)| t!(v, "cv")).collect();
                let shapes: Vec<Term> = std::iter::once(rest.clone())
                    .chain(turned_equation(&rest))
                    .collect();
                // A body saying nothing of its one variable takes any member of
                // the domain a line names; one that says something takes what it
                // says.
                let silent = here.len() == 1
                    && !here[0].1.alone().is_some_and(|v| self.rpn(&rest).has(v));
                for (said, proof) in &sources {
                    for part in self.parts(said) {
                        let mut held = self.to_term(&part);
                        if bare {
                            held = self.without_identities(&held);
                        }
                        for shape in &shapes {
                            let found = self.witnesses_in(shape, &held, &marks);
                            if let Some(found) = found.filter(|f| !f.is_empty()) {
                                chosen = Some((
                                    part.clone(),
                                    said.clone(),
                                    proof.clone(),
                                    found,
                                ));
                                layers = here;
                                break 'depths;
                            }
                        }
                    }
                    if silent {
                        if let Some(found) = self.member_named(said, &here[0]) {
                            chosen = Some((
                                said.clone(),
                                said.clone(),
                                proof.clone(),
                                found,
                            ));
                            layers = here;
                            break 'depths;
                        }
                    }
                }
            }
        }
        let Some((part, said, whole, found)) = chosen else {
            return Err(self.defect(
                step.line,
                format!(
                    "no cited line names a witness for {}",
                    self.render(&self.rpn(wanted))
                ),
            ));
        };
        // A witness may spell a letter the claim binds, as the n obtained
        // for "there are m, n ∈ ℕ with …" does, and `rspcev` keeps its
        // letter apart from what the body says. So the claim is shown under
        // letters nothing holds and renamed back, as `exhibit` does for one.
        let letters: Vec<Rpn> = layers.iter().map(|(_, v, _)| v.clone()).collect();
        let meets = found
            .values()
            .any(|w| letters.iter().any(|v| v.alone().is_some_and(|v| w.has(v))));
        if meets {
            let witnesses: Vec<Term> =
                found.values().map(|w| self.to_term(w)).collect();
            let mut seen: Vec<&Term> = witnesses.iter().collect();
            seen.push(wanted);
            let names: Vec<Symbol> = letters
                .iter()
                .filter_map(|l| {
                    self.var_of(l.alone().unwrap_or_default()).variable_symbol()
                })
                .collect();
            let Some(moved) = self.unheld_for(names, &seen) else {
                return Err(
                    self.defect(step.line, "no letter left to exhibit the witness by")
                );
            };
            let renamed = wanted.substitute(&moved);
            let made = take!(self.witnessed(step, &renamed, scope, facts, lines)?);
            let Some(back) = self.renaming(&renamed, wanted)? else {
                return Err(self.defect(
                    step.line,
                    "the renamed claim does not read back as the claim",
                ));
            };
            return Ok(Built(self.b.ap(
                "sylib",
                &binds! {"ph" => scope, "ps" => &self.rpn(&renamed), "ch" => &self.rpn(wanted)},
                &[&made, &back],
            )));
        }
        // Where the line naming the witnesses is all the claim says of them,
        // its own proof is taken, turned where it faces the other way.
        let mut proof = whole;
        let mut innermost = layers[layers.len() - 1].0.clone();
        for (_, v, _) in &layers {
            let mark = t!(v, "cv");
            innermost = self.restated(&innermost, &mark, &found[&mark]);
        }
        let inner_rpn = self.rpn(&innermost);
        let turned = turned_equation(&innermost).map(|t| self.rpn(&t));
        if inner_rpn.alone() == Some("wtru") {
            // A body that says nothing of its variable holds outright, by
            // the one lemma that states truth.
            proof = pf!(self.b; "wtru", scope, "tru", "a1i");
        } else if part == said && turned.as_ref() == Some(&said) {
            let (a, b) = (
                self.rpn(&innermost.children()[0]),
                self.rpn(&innermost.children()[1]),
            );
            proof = pf!(self.b; scope, b, a, proof, "eqcomd");
        } else if inner_rpn != said {
            proof = take!(self.settle_or_bare(
                &innermost,
                scope,
                facts,
                Some(step),
                Some(lines)
            )?);
        }
        for i in (0..layers.len()).rev() {
            let (body, var, over) = layers[i].clone();
            let mark = t!(var, "cv");
            let mut held = body;
            let mut over = self.to_term(&over);
            // The quantifiers further out are still open here, and the ones
            // already closed have their witnesses in place: in the body, and
            // in the domain, which may run over one of them, as a walk's
            // vertices run over {0, …, n}.
            for (_, v, _) in &layers[..i] {
                let m = t!(v, "cv");
                held = self.restated(&held, &m, &found[&m]);
                over = self.restated(&over, &m, &found[&m]);
            }
            let over = self.rpn(&over);
            let witness = found[&mark].clone();
            let here = self.restated(&held, &mark, &witness);
            let (ph, ps) = (self.rpn(&held), self.rpn(&here));
            let instance = if ph == ps {
                // The body does not mention the variable, so the witness
                // changes nothing in it: `biidd` says so outright.
                pf!(self.b; t!(mark, witness, "wceq"), ph, "biidd")
            } else {
                let tie = self.to_term(&t!(
                    t!(mark, witness, "wceq"),
                    t!(ph, ps, "wb"),
                    "wi"
                ));
                take!(self.prove_essential(&tie, scope, facts)?)
            };
            let member = t!(witness, over, "wcel");
            let supplied = self.required(step, &member, scope, facts)?;
            let both = pf!(self.b; scope, member, ps, supplied, proof, "jca");
            proof = pf!(self.b; scope, t!(member, ps, "wa"), t!(ph, var, over, "wrex"), both,
                ph, ps, var, witness, over, instance, "rspcev", "syl");
        }
        Ok(Built(proof))
    }

    /// The witness a line gives by putting something in the domain, for a
    /// "there is s ∈ S" whose body says nothing of s.
    fn member_named(
        &self,
        said: &Rpn,
        layer: &(Term, Rpn, Rpn),
    ) -> Option<IndexMap<Rpn, Rpn>> {
        let (_, var, over) = layer;
        for part in self.parts(said) {
            let node = self.to_term(&part);
            if node.variable().is_none()
                && node.label() == Some("wcel")
                && self.rpn(&node.children()[1]) == *over
            {
                let mut out = IndexMap::new();
                out.insert(t!(var, "cv"), self.rpn(&node.children()[0]));
                return Some(out);
            }
        }
        None
    }

    /// `term` with every occurrence of the subterm `was` reading `now`, both
    /// given in reverse Polish, because a term is compared by what it spells.
    pub fn restated(&self, term: &Term, was: &Rpn, now: &Rpn) -> Term {
        if self.rpn(term) == *was {
            return self.to_term(now);
        }
        if term.variable().is_some() {
            return term.clone();
        }
        Term::apply(
            term.label().unwrap_or(""),
            term.children()
                .iter()
                .map(|c| self.restated(c, was, now))
                .collect(),
        )
    }

    /// What a lemma's naming hypothesis says its own variables are: where a
    /// lemma names a map in a hypothesis and speaks of its range in the
    /// conclusion, what the map binds, where that runs and what it builds are
    /// read back out of it; and the other way, where the naming is what says
    /// what a variable is.
    pub fn read_off(
        &self,
        sig: &Signature,
        binding: Binding,
        variables: &Vars,
    ) -> Binding {
        let mut binding = binding;
        for text in &sig.essentials {
            let asked = self.essential(text);
            if asked.label() != Some("wceq") || asked.children().len() != 2 {
                continue;
            }
            let name = asked.children()[0].variable_symbol();
            if let Some(name) = &name {
                if !binding.contains_key(name)
                    && asked.children()[1]
                        .names()
                        .iter()
                        .all(|n| binding.contains_key(&**n))
                {
                    let value = asked.children()[1].substitute(&binding);
                    binding.insert(*name, value);
                    continue;
                }
            }
            let Some(name) = name.filter(|n| binding.contains_key(n)) else {
                continue;
            };
            let mut vars = variables.clone();
            vars.extend(asked.names().iter().cloned());
            if let Some(said) = fit(
                &asked.children()[1],
                &binding[&name].clone(),
                &binding,
                &vars,
            ) {
                binding = said;
            }
        }
        binding
    }

    /// What a lemma asking `( x = A -> ( ph <-> ps ) )` means by `ps`: `ps`
    /// is `ph` with the variable reading the term. Worked out and not taken
    /// from the step. A hypothesis relating two terms says the same thing of
    /// them as one relating two formulas.
    pub fn instanced(&self, sig: &Signature, binding: Binding) -> Binding {
        let mut out = binding;
        let kinds: IndexMap<&str, &str> = sig
            .floats
            .iter()
            .map(|(t, v)| (v.as_str(), t.as_str()))
            .collect();
        for text in &sig.essentials {
            let asked = self.essential(text);
            if asked.label() != Some("wi") {
                continue;
            }
            let (at, says) = (&asked.children()[0], &asked.children()[1]);
            if at.label() != Some("wceq")
                || !matches!(says.label(), Some("wb") | Some("wceq"))
                || at.children()[0].label() != Some("cv")
            {
                continue;
            }
            let Some(name) = says.children()[1].variable_symbol() else {
                continue;
            };
            let summand = says.children()[0].variable_symbol();
            let index = at.children()[0].children()[0].clone();
            let other = at.children()[1].clone();
            // Read the other way where the claim fixed the instance and not
            // the summand: A is B with the claim's index moved to a letter
            // nothing holds.
            if let Some(summand) = &summand {
                if !out.contains_key(summand)
                    && kinds.get(summand.as_str()) == Some(&"class")
                    && out.contains_key(&name)
                    && !index.variable().is_some_and(|v| out.contains_key(v))
                    && other.label() == Some("cv")
                    && other.children()[0]
                        .variable()
                        .is_some_and(|v| out.contains_key(v))
                {
                    let held: Vec<&Term> = out.values().collect();
                    let Some(letter) = self.unheld(&held) else {
                        continue;
                    };
                    let was = self.rpn(&Term::apply(
                        "cv",
                        vec![out[other.children()[0].variable().unwrap()].clone()],
                    ));
                    let now = self.rpn(&Term::apply("cv", vec![letter.clone()]));
                    let value = self.restated(&out[&name].clone(), &was, &now);
                    out.insert(Symbol::of(index.variable().unwrap_or("")), letter);
                    out.insert(*summand, value);
                    continue;
                }
            }
            if at
                .names()
                .iter()
                .any(|v| !out.contains_key(&**v) && kinds.get(&**v) == Some(&"class"))
            {
                continue;
            }
            let was = self.rpn(&at.children()[0].substitute(&out));
            let now = self.rpn(&at.children()[1].substitute(&out));
            let value = self.restated(&says.children()[0].substitute(&out), &was, &now);
            out.insert(name, value);
        }
        out
    }

    // --- one claim spelt two ways ---------------------------------------

    /// A proof that two terms written differently agree: `same` says so.
    pub fn bridging(
        &mut self,
        given: &Term,
        want: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        self.same(given, want, scope, facts, step)
    }

    /// The two as one claim, spelt with different bound variables:
    /// `cbvrexvw` is set.mm saying those are one claim. Closed, and lifted
    /// by closed lemmas, since none of this wants a scope.
    pub fn renaming(&mut self, given: &Term, want: &Term) -> Checked<Option<Proof>> {
        if self.rpn(given) == self.rpn(want) {
            return Ok(None); // nothing is spelt differently
        }
        if given.label() != want.label()
            || given.children().len() != want.children().len()
        {
            return Ok(None);
        }
        let label = given.label().unwrap_or("").to_string();
        if let Some((same_lemma, cross)) = lookup(rules::BOUND, &label) {
            let (body, variable, other, renamed, over);
            if given.children().len() == 3 {
                body = given.children()[0].clone();
                variable = given.children()[1].clone();
                over = Some(given.children()[2].clone());
                other = want.children()[0].clone();
                renamed = want.children()[1].clone();
                let runs = want.children()[2].clone();
                if self.rpn(over.as_ref().unwrap()) != self.rpn(&runs) {
                    // The domains may be one class spelt with other bound
                    // letters inside. The domain is carried across first,
                    // and the rest renamed.
                    let lemma = lookup(rules::DOMAIN, &label);
                    let same_class = self.class_alpha(over.as_ref().unwrap(), &runs)?;
                    let (Some(lemma), Some(same_class)) = (lemma, same_class) else {
                        return Ok(None);
                    };
                    let moved = Term::apply(
                        &label,
                        vec![body.clone(), variable.clone(), runs.clone()],
                    );
                    let Some(first) =
                        self.by_lemma(lemma, given, &moved, &[&same_class])
                    else {
                        return Ok(None);
                    };
                    if self.rpn(&moved) == self.rpn(want) {
                        return Ok(Some(first));
                    }
                    let Some(rest) = self.renaming(&moved, want)? else {
                        return Ok(None);
                    };
                    return Ok(Some(self.b.ap(
                        "bitri",
                        &binds! {"ph" => self.rpn(given), "ps" => self.rpn(&moved), "ch" => self.rpn(want)},
                        &[&first, &rest],
                    )));
                }
            } else {
                body = given.children()[0].clone();
                variable = given.children()[1].clone();
                other = want.children()[0].clone();
                renamed = want.children()[1].clone();
                over = None;
            }
            let x = self.rpn(&variable);
            let mut binds =
                binds! {"ph" => self.rpn(&body), "ps" => self.rpn(&other), "x" => &x};
            if let Some(over) = &over {
                binds.insert("A".to_string(), self.rpn(over));
            }
            let bound = |me: &Self, said: &Rpn| -> Rpn {
                match &over {
                    Some(runs) => t!(said, x, me.rpn(runs), label),
                    None => t!(said, x, label),
                }
            };
            if variable.variable() == renamed.variable() {
                let Some(inner) = self.renaming(&body, &other)? else {
                    return Ok(None);
                };
                return Ok(Some(self.b.ap(same_lemma, &binds, &[&inner])));
            }
            // The cross lemma changes one binder and wants a hypothesis
            // relating the two bodies at x = y, which a body still spelt two
            // ways inside is not. So the bodies are made to agree first, over
            // this binder as it stands, and only then is it changed.
            let y = self.rpn(&renamed);
            let here = self.restated(&other, &t!(y, "cv"), &t!(x, "cv"));
            let mut middle = binds.clone();
            middle.insert("ph".to_string(), self.rpn(&here));
            let at = t!(
                t!(x, "cv", y, "cv", "wceq"),
                t!(middle["ph"], binds["ps"], "wb"),
                "wi"
            );
            let Built(said) = self.prove_essential(
                &self.to_term(&at),
                &Rpn::default(),
                &Facts::new(),
            )?
            else {
                return Ok(None);
            };
            let mut crossed = middle.clone();
            crossed.insert("y".to_string(), y.clone());
            let changed = self.b.ap(cross, &crossed, &[&said]);
            if middle["ph"] == binds["ph"] {
                return Ok(Some(changed));
            }
            let Some(inner) = self.renaming(&body, &here)? else {
                return Ok(None);
            };
            let mut agreeing = binds.clone();
            agreeing.insert("ps".to_string(), middle["ph"].clone());
            let agreed = self.b.ap(same_lemma, &agreeing, &[&inner]);
            return Ok(Some(self.b.ap(
                "bitri",
                &binds! {"ph" => bound(self, &binds["ph"]), "ps" => bound(self, &middle["ph"]), "ch" => self.rpn(want)},
                &[&agreed, &changed],
            )));
        }
        let spelt: Vec<Rpn> = given.children().iter().map(|c| self.rpn(c)).collect();
        let other: Vec<Rpn> = want.children().iter().map(|c| self.rpn(c)).collect();
        // Both halves of an implication may be spelt differently at once. The
        // lifters each change one side and hold the other, so the sides are
        // changed one at a time and the halfway claim is what joins the two.
        let mut here = spelt.clone();
        let start = applied(&spelt, &label, None);
        let mut proof: Option<Proof> = None;
        for slot in (0..spelt.len()).filter(|&i| spelt[i] != other[i]) {
            // A connective carries a renamed statement, and a predicate over
            // classes a class renamed inside it (`class_alpha`); either
            // lemma is applied by matching what it states to the claim
            // before and after, whatever else the constructor takes.
            let (lemma, inner) = if let Some(lemma) = rules::renamed(&label, slot) {
                (
                    lemma,
                    self.renaming(&given.children()[slot], &want.children()[slot])?,
                )
            } else if let Some(lemma) = rules::PREDICATE_LIFT
                .iter()
                .find(|(l, s, _)| *l == label && *s == slot)
                .map(|(_, _, lemma)| *lemma)
            {
                (
                    lemma,
                    self.class_alpha(&given.children()[slot], &want.children()[slot])?,
                )
            } else {
                return Ok(None);
            };
            let Some(inner) = inner else {
                return Ok(None);
            };
            let was = applied(&here, &label, None);
            let mut next = here.clone();
            next[slot] = other[slot].clone();
            let now = applied(&next, &label, None);
            let Some(step) = self.by_lemma(
                lemma,
                &self.to_term(&was),
                &self.to_term(&now),
                &[&inner],
            ) else {
                return Ok(None);
            };
            here = next;
            proof = Some(match proof {
                None => step,
                Some(p) => self.b.ap(
                    "bitri",
                    &binds! {"ph" => &start, "ps" => &was, "ch" => applied(&here, &label, None)},
                    &[&p, &step],
                ),
            });
        }
        Ok(proof)
    }

    /// A proof of a claim, made a proof of the literal instance it is with
    /// identity elements dropped (`Row::Identity`): L(p) ≤ L(p) carried to
    /// L(p) ≤ L(p + 0). None where the two differ in anything else.
    pub fn tidied(
        &mut self,
        proof: &Proof,
        said: &Rpn,
        want: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        if said == want {
            return Ok(Some(proof.clone()));
        }
        let (from, to) = (self.to_term(said), self.to_term(want));
        let across = self.congruence(
            &from,
            &to,
            scope,
            facts,
            None,
            &Leaf::Rows(vec![Row::Identity]),
        )?;
        Ok(match across {
            Built(across) => {
                Some(pf!(self.b; scope, said, want, proof, across, "mpbid"))
            }
            Declined(_) => None,
        })
    }

    /// A proof of what a part of a block ends on, made a proof of the
    /// instance it is written for: the page's claim with its identity
    /// elements dropped, renamed to the instance's bound letters, and
    /// carried to the instance as it stands (`SYNTAX.md`). None where they
    /// differ in anything else.
    pub fn reached(
        &mut self,
        proof: &Proof,
        said: &Rpn,
        want: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        // A claim written as its instance, letters renamed or not, is the
        // instance, and no element is dropped from it to be put back.
        if let Some(p) = self.respelt(proof, said, want, scope)? {
            return Ok(Some(p));
        }
        // Each line the part may rest on is read in its parts as well, as a
        // cited line is: "a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀" says b(0) ∈ ℕ₀. What it may
        // not rest on is left out first, so that a copy of a part proved
        // elsewhere does not stand in the way of this one.
        let known = match &self.resting {
            Some(resting) => {
                let resting = resting.clone();
                facts.filtered(|_, v| v.origin.iter().all(|o| may_rest_on(&resting, o)))
            }
            None => facts.copy(),
        };
        for (line, held) in known.entries() {
            self.unpack_all(&line, &held, scope, &known);
        }
        let facts = &known;
        let said_bare = self.rpn(&self.without_identities(&self.to_term(said)));
        let want_bare = self.rpn(&self.without_identities(&self.to_term(want)));
        let Some(bare) = self.tidied(proof, said, &said_bare, scope, facts)? else {
            return Ok(None);
        };
        let Some(renamed) = self.respelt(&bare, &said_bare, &want_bare, scope)? else {
            return Ok(None);
        };
        self.tidied(&renamed, &want_bare, want, scope, facts)
    }

    /// The term with every identity element dropped where it stands, parts
    /// first.
    pub fn without_identities(&self, term: &Term) -> Term {
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        let kids: Vec<Term> = term
            .children()
            .iter()
            .map(|c| self.without_identities(c))
            .collect();
        let mut out = Term::apply(term.label().unwrap_or(""), kids);
        while let Some(kept) = self.identity_dropped(&out) {
            out = kept;
        }
        out
    }

    /// A proof of a claim, made a proof of it spelt another way: what is
    /// proved is the same claim, and `same` is what says so, asking nothing
    /// of the scope.
    pub fn respelt(
        &mut self,
        proof: &Proof,
        said: &Rpn,
        want: &Rpn,
        scope: &Rpn,
    ) -> Checked<Option<Proof>> {
        if said == want {
            return Ok(Some(proof.clone()));
        }
        let alike = self.same(
            &self.to_term(said),
            &self.to_term(want),
            scope,
            &Facts::new(),
            None,
        )?;
        let Built(alike) = alike else {
            return Ok(None);
        };
        Ok(Some(pf!(self.b; scope, said, want, proof, alike, "mpbid")))
    }

    /// `renaming` by way of letters neither statement holds: every letter
    /// the first statement binds where the second binds another, under a
    /// statement's binder or a class's, is moved to one nothing holds, and
    /// the statement is renamed from there, where nothing can be caught. The
    /// letters are only looked at, not taken.
    ///
    /// A letter both bind at the same place stays: a sequence by recursion
    /// written out binds letters inside it, which the two statements share,
    /// and set.mm has no lemma carrying a renaming through a sequence.
    pub fn renaming_apart(&mut self, said: &Rpn, want: &Rpn) -> Checked<Option<Proof>> {
        let mut letters: Vec<Symbol> = Vec::new();
        let mut rest = vec![(self.to_term(said), Some(self.to_term(want)))];
        while let Some((node, theirs)) = rest.pop() {
            // Where the two are built alike, each part is compared with the
            // other's part in its place; below a place where they are not,
            // no letter of the first is bound where the second binds it.
            let theirs = theirs.filter(|t| {
                t.label() == node.label() && t.children().len() == node.children().len()
            });
            // What a binder binds is the set variable it takes as an
            // operand, wherever the binder puts it.
            let binder = node.label().is_some_and(|l| {
                lookup(rules::BOUND, l).is_some()
                    || lookup(rules::CLASS_BOUND, l).is_some()
            });
            for (at, kid) in node.children().iter().enumerate() {
                let other = theirs.as_ref().map(|t| t.children()[at].clone());
                rest.push((kid.clone(), other.clone()));
                if !binder {
                    continue;
                }
                let Some(letter) = kid.variable_symbol() else {
                    continue;
                };
                if self.typecode(self.rpn(kid).alone().unwrap_or_default()) != "setvar"
                    || letters.contains(&letter)
                    || other.and_then(|o| o.variable_symbol()) == Some(letter)
                {
                    continue;
                }
                letters.push(letter);
            }
        }
        if letters.is_empty() {
            return Ok(None); // it binds nothing, so it is not the other respelt
        }
        let Some(moved) =
            self.unheld_for(letters, &[&self.to_term(said), &self.to_term(want)])
        else {
            return Ok(None);
        };
        let middle = self.to_term(said).substitute(&moved);
        let there = self.renaming(&self.to_term(said), &middle)?;
        let back = self.renaming(&middle, &self.to_term(want))?;
        let (Some(there), Some(back)) = (there, back) else {
            return Ok(None);
        };
        Ok(Some(self.b.ap(
            "bitri",
            &binds! {"ph" => said, "ps" => self.rpn(&middle), "ch" => want},
            &[&there, &back],
        )))
    }

    /// A set variable no name in the proof holds and none of `terms` spells,
    /// or None when there is none left. Looked at, not taken.
    pub fn unheld(&self, terms: &[&Term]) -> Option<Term> {
        let mut held = self.names_held();
        held.extend(self.reserved.iter().cloned());
        held.extend(self.bound_as.values().cloned());
        for t in terms {
            held.extend(self.rpn(t).tokens().iter().map(|t| t.to_string()));
        }
        let free = self.spare.iter().find(|v| !held.contains(*v))?;
        Some(self.var_of(free))
    }

    /// Each of `letters` with a letter of its own from `unheld`: none that
    /// `terms` spells or that another of them was given. None when too few
    /// are left. Looked at, not taken.
    pub fn unheld_for(
        &self,
        letters: impl IntoIterator<Item = Symbol>,
        terms: &[&Term],
    ) -> Option<Binding> {
        let mut moved = Binding::new();
        for letter in letters {
            let fresh = {
                let mut seen: Vec<&Term> = terms.to_vec();
                seen.extend(moved.values());
                self.unheld(&seen)?
            };
            moved.insert(letter, fresh);
        }
        Some(moved)
    }

    /// ( scope -> wanted ) from a fact saying it over other bound letters,
    /// carried by `renaming`; None where no fact does.
    fn fact_respelt(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let want = self.rpn(wanted);
        for (said, proof) in facts.entries() {
            if said == want {
                return Ok(Some(proof));
            }
            let held = self.to_term(&said);
            if held.label() != wanted.label() {
                continue;
            }
            let Some(across) = self.renaming_apart(&said, &want)? else {
                // Or read the same in standard form.
                let Built(alike) = self.same(&held, wanted, scope, facts, None)? else {
                    continue;
                };
                return Ok(Some(pf!(self.b; scope, said, want, proof, alike, "mpbid")));
            };
            let turned = pf!(self.b; t!(said, want, "wb"), scope, across, "a1i");
            return Ok(Some(pf!(self.b; scope, said, want, proof, turned, "mpbid")));
        }
        Ok(None)
    }

    /// Every token the scopes of the open frames spell.
    fn frames_spell(&self) -> BTreeSet<String> {
        self.frames
            .iter()
            .flat_map(|f| {
                f.scope
                    .tokens()
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    /// `binding` with a letter nothing in the proof holds, for each set
    /// variable the lemma keeps apart from its scope and the claim did not
    /// fix: always, and not only where the frames spell the lemma's own, so
    /// that which letter a line happened to bind decides nothing
    /// (`ELABORATION.md`, "Where a step is proved").
    fn letters_unheld(&self, sig: &Signature, binding: Binding) -> Binding {
        let kinds: IndexMap<&str, &str> = sig
            .floats
            .iter()
            .map(|(t, v)| (v.as_str(), t.as_str()))
            .collect();
        let mut apart: BTreeSet<Symbol> = BTreeSet::new();
        for (a, b) in &sig.disjoint {
            for (one, other) in [(a, b), (b, a)] {
                if kinds.get(one.as_str()) != Some(&"setvar") {
                    continue;
                }
                // Kept apart from a class the claim leaves open, which the
                // scope may spell; or from another letter the claim has
                // fixed, which a cited line may bind as well: `gfprodrp`
                // keeps its x from the product's k, and a line saying "for
                // all r ∈ S" would hand x the r the product fixed as k.
                let from_class = !binding.contains_key(other)
                    && !matches!(kinds.get(other.as_str()), None | Some(&"setvar"));
                let from_fixed = kinds.get(other.as_str()) == Some(&"setvar")
                    && binding.contains_key(other);
                if from_class || from_fixed {
                    apart.insert(*one);
                }
            }
        }
        let mut out = binding;
        let open: Vec<Symbol> =
            apart.into_iter().filter(|v| !out.contains_key(v)).collect();
        let moved = {
            let frames: Vec<Term> =
                self.frames.iter().map(|f| self.to_term(&f.scope)).collect();
            let mut terms: Vec<&Term> = frames.iter().collect();
            terms.extend(out.values());
            self.unheld_for(open, &terms)
        };
        if let Some(moved) = moved {
            out.extend(moved);
        }
        out
    }

    /// The claim proved with its bound letters moved off what the frames
    /// spell, and spelt back; `why` where it binds none of those.
    #[allow(clippy::too_many_arguments)]
    fn over_other_letters(
        &mut self,
        label: &str,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        crossing: bool,
        seed: Option<&Binding>,
        why: Decline,
    ) -> Checked<Route<Proof>> {
        let held = self.names_held();
        let spelt = self.frames_spell();
        let mut letters: BTreeSet<Symbol> = BTreeSet::new();
        let mut rest = vec![goal.clone()];
        while let Some(node) = rest.pop() {
            if let Some(letter) = node.variable_symbol() {
                let said = self.rpn(&node);
                let said = said.alone().unwrap_or_default();
                if self.typecode(said) == "setvar"
                    && !held.contains(said)
                    && spelt.contains(said)
                {
                    letters.insert(letter);
                }
                continue;
            }
            rest.extend(node.children().iter().cloned());
        }
        if letters.is_empty() {
            return Ok(Declined(why));
        }
        let frames: Vec<Term> =
            self.frames.iter().map(|f| self.to_term(&f.scope)).collect();
        let mut terms: Vec<&Term> = vec![goal];
        terms.extend(frames.iter());
        let Some(moved) = self.unheld_for(letters, &terms) else {
            return Ok(Declined(why));
        };
        let other = goal.substitute(&moved);
        // What the citation fixed of the claim is fixed of it over the new
        // letters too: a set-builder's letter the seed names moves with it.
        let seed: Option<Binding> =
            seed.map(|s| s.iter().map(|(k, v)| (*k, v.substitute(&moved))).collect());
        let proof = take!(self.apply_lemma(
            label,
            &other,
            scope,
            facts,
            step,
            crossing,
            seed.as_ref()
        )?);
        let back = self.respelt(&proof, &self.rpn(&other), &self.rpn(goal), scope)?;
        Ok(match back {
            Some(p) => Built(p),
            None => Declined(why),
        })
    }

    /// A lemma that binds two letters apart, where the claim binds one: the
    /// sum on the right is renamed to a letter nothing holds, the lemma
    /// proves that, and `cbvsumv` says the two sums are one.
    #[allow(clippy::too_many_arguments)]
    fn letters_apart(
        &mut self,
        label: &str,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        crossing: bool,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        if goal.label() != Some("wceq") || goal.children()[1].label() != Some("csu") {
            return Ok(Route::no(format!(
                "{label} binds two letters apart where the claim binds one, and the claim is not an equation with a sum on its right"
            )));
        }
        let (left, right) = (goal.children()[0].clone(), goal.children()[1].clone());
        let (limits, summand, index) = (
            right.children()[0].clone(),
            right.children()[1].clone(),
            right.children()[2].clone(),
        );
        let Some(letter) = self.unheld(&[goal]) else {
            return Ok(Route::no("no letter left to rename a sum with"));
        };
        let mut put = Binding::new();
        put.insert(Symbol::of(index.variable().unwrap_or("")), letter.clone());
        let moved = summand.substitute(&put);
        let renamed =
            Term::apply("csu", vec![limits.clone(), moved.clone(), letter.clone()]);
        let first = take!(self.apply_lemma(
            label,
            &Term::apply("wceq", vec![left.clone(), renamed.clone()]),
            scope,
            facts,
            step,
            crossing,
            seed
        )?);
        let tie = Term::apply(
            "wi",
            vec![
                Term::apply(
                    "wceq",
                    vec![
                        Term::apply("cv", vec![letter.clone()]),
                        Term::apply("cv", vec![index.clone()]),
                    ],
                ),
                Term::apply("wceq", vec![moved.clone(), summand.clone()]),
            ],
        );
        let tie = take!(self.prove_essential(&tie, scope, facts)?);
        let same_sum = self.b.ap(
            "cbvsumv",
            &binds! {"j" => self.rpn(&letter), "k" => self.rpn(&index), "A" => self.rpn(&limits),
            "B" => self.rpn(&moved), "C" => self.rpn(&summand)},
            &[&tie],
        );
        let (was, now) = (self.rpn(&renamed), self.rpn(&right));
        let carried = pf!(self.b; t!(was, now, "wceq"), scope, same_sum, "a1i");
        Ok(Built(self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => self.rpn(&left), "B" => &was, "C" => &now},
            &[&first, &carried],
        )))
    }

    // --- one lemma ------------------------------------------------------

    /// A lemma's existential taken apart, and the claim's put back: the
    /// lemma's existential is proved, weakened where it says exactly one,
    /// eliminated, and the claim introduced at the variables it gave up.
    #[allow(clippy::too_many_arguments)]
    fn through_existential(
        &mut self,
        label: &str,
        reads: &Term,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        if goal.label() != Some("wrex")
            || !matches!(reads.label(), Some("wrex") | Some("wreu"))
        {
            return Ok(Route::no(format!(
                "{label} and the claim are not both \"there is\""
            )));
        }
        let own = self.bound_in(reads);
        let unfixed = match seed {
            None => true,
            Some(seed) => reads
                .names()
                .iter()
                .any(|n| !seed.contains_key(&**n) && !own.iter().any(|b| **b == **n)),
        };
        if unfixed {
            return Ok(Route::no(format!("nothing fixes the variables of {label}")));
        }
        let seed = seed.unwrap();
        let mut ground = reads.substitute(seed);
        // The lemma's binders become names in the open, so they must be
        // variables nothing else holds, and the claim's own binders are
        // among what is held.
        let taken = self.bound_in(goal);
        let mut swap = Binding::new();
        for name in self.bound_in(&ground) {
            let mut fresh = self.spare_var()?;
            while taken.contains(&self.sig(&fresh).statement[1]) {
                fresh = self.spare_var()?;
            }
            swap.insert(name, self.var_of(&fresh));
        }
        ground = ground.substitute(&swap);
        let mut strong = take!(self.apply_lemma(
            label,
            &ground,
            scope,
            facts,
            step,
            false,
            Some(seed)
        )?);
        if ground.label() == Some("wreu") {
            let weaker = Term::apply("wrex", ground.children().to_vec());
            let kids: Vec<Rpn> =
                ground.children().iter().map(|c| self.rpn(c)).collect();
            let law = self.b.ap(
                "reurex",
                &binds! {"ph" => &kids[0], "x" => &kids[1], "A" => &kids[2]},
                &[],
            );
            strong = pf!(self.b; scope, self.rpn(&ground), self.rpn(&weaker), strong, law, "syl");
            ground = weaker;
        }
        let mut layers: Vec<(Rpn, Rpn)> = Vec::new();
        let mut rest = ground.clone();
        while rest.label() == Some("wrex") {
            let kids = rest.children().to_vec();
            layers.push((self.rpn(&kids[1]), self.rpn(&kids[2])));
            rest = kids[0].clone();
        }
        let body = self.rpn(&rest);
        let memberships: Vec<Rpn> =
            layers.iter().map(|(v, s)| t!(v, "cv", s, "wcel")).collect();
        let mut member =
            Rpn::joined(&memberships.iter().map(Rpn::tokens).collect::<Vec<_>>());
        if layers.len() > 1 {
            member = t!(member, "wa");
        }
        let made = self.frames_kept(|me| {
            let (outer, held) = me.widen(scope, facts, &member, None);
            let (inner, lifted) = me.widen(&outer, &held, &body, None);
            me.introduced(goal, &inner, &lifted)
                .map(|r| r.map(|p| (outer, p)))
        })?;
        let (outer, made) = take!(made);
        let want = self.rpn(goal);
        let discharge = if layers.len() == 1 {
            "rexlimdva"
        } else {
            "rexlimdvva"
        };
        let mut pushed: Vec<Rpn> = layers.iter().map(|(v, _)| v.clone()).collect();
        pushed.extend(layers.iter().map(|(_, s)| s.clone()));
        let lifted = pf!(self.b; outer, body, want, made, "ex");
        let mut all: Vec<crate::mm::spell::Part> = vec![
            crate::elab::part(scope),
            crate::elab::part(&body),
            crate::elab::part(&want),
        ];
        all.extend(pushed.iter().map(|p| crate::elab::part(p)));
        all.push(crate::elab::part(&lifted));
        all.push(crate::elab::part(discharge));
        let eliminated = self.b.proof(&all);
        Ok(Built(
            pf!(self.b; scope, self.rpn(&ground), want, strong, eliminated, "mpd"),
        ))
    }

    /// An existence claim its item's lemmas together give: each is proved at
    /// what the `with` target says it is about, and the claim introduced at
    /// the terms they turn out to be about.
    pub fn by_lemmas(
        &mut self,
        labels: &[String],
        goal: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        step: &Step,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let Some(seed) = seed.filter(|s| !labels.is_empty() && !s.is_empty()) else {
            return Ok(Route::no("no `with` target says what the lemmas are about"));
        };
        let want = self.to_term(goal);
        if want.label() != Some("wrex") {
            return Ok(Route::no("the claim is not \"there is\""));
        }
        if labels.iter().any(|l| !self.b.sigs.contains_key(l)) {
            return Ok(Route::no(format!(
                "{} are not all in the library",
                labels.join(", ")
            )));
        }
        let theirs: BTreeSet<String> = labels
            .iter()
            .flat_map(|l| {
                self.sig(l)
                    .push()
                    .into_iter()
                    .map(String::from)
                    .collect::<Vec<_>>()
            })
            .collect();
        let witness: Vec<Symbol> = seed
            .keys()
            .filter(|n| !theirs.contains(n.as_str()))
            .copied()
            .collect();
        if !witness.is_empty() {
            return self.at_witness(labels, &want, seed, &witness, scope, facts, step);
        }
        let known = facts.copy();
        for label in labels {
            let mut reads = self.statement(label);
            while reads.label() == Some("wi") {
                reads = reads.children()[1].clone();
            }
            if reads.names().iter().any(|n| !seed.contains_key(&**n)) {
                return Ok(Route::no(format!(
                    "the target does not say what {label} is about"
                )));
            }
            let said = self.rpn(&reads.substitute(seed));
            let proof = take!(self.apply_lemma(
                label,
                &self.to_term(&said),
                scope,
                facts,
                Some(step),
                false,
                Some(seed)
            )?);
            self.know(&known, said.clone(), proof.clone());
            self.unpack_all(&said, &proof, scope, &known);
        }
        self.introduced(&want, scope, &known)
    }

    /// An existence claim at the thing a `with` target names for it: the
    /// witness is put in for the binder, each part of what the claim then
    /// says is proved by the first lemma that reaches it, and the claim is
    /// introduced at the witness.
    #[allow(clippy::too_many_arguments)]
    fn at_witness(
        &mut self,
        labels: &[String],
        want: &Term,
        seed: &Binding,
        witness: &[Symbol],
        scope: &Rpn,
        facts: &Facts,
        step: &Step,
    ) -> Checked<Route<Proof>> {
        if witness.len() != 1 {
            return Ok(Route::no(format!(
                "the target names {} witnesses and the claim is read one binder at a time",
                witness.len()
            )));
        }
        let (body, variable, over) = (
            want.children()[0].clone(),
            want.children()[1].clone(),
            want.children()[2].clone(),
        );
        let stood = seed[&witness[0]].clone();
        let member = t!(self.rpn(&stood), self.rpn(&over), "wcel");
        let said = self.replaced(&body, &t!(self.rpn(&variable), "cv"), &stood);
        let mut by_lemmas = |me: &mut Self, one: &Term| -> Checked<Route<Proof>> {
            let mut refused = Vec::new();
            for label in labels {
                let made =
                    me.apply_lemma(label, one, scope, facts, Some(step), true, None)?;
                match made {
                    Built(p) => return Ok(Built(p)),
                    Declined(d) => refused.push(format!("{label}: {}", me.say(&d))),
                }
            }
            Ok(Route::no(refused.join("; ")))
        };
        let known = facts.copy();
        for part in [self.to_term(&member), said] {
            let made = match self.conjoined(&part, scope, &mut by_lemmas)? {
                Some(made) => made,
                None => by_lemmas(self, &part)?,
            };
            let made = take!(made);
            let key = self.rpn(&part);
            self.know(&known, key.clone(), made.clone());
            self.unpack_all(&key, &made, scope, &known);
        }
        self.introduced(want, scope, &known)
    }

    /// An existential claim at witnesses the scope already names: which of
    /// them stands for which binder is read off the body, one part of the
    /// claim matched against one fact in scope. A witness may be a term and
    /// not a name, so the binder is matched as the class it stands for.
    fn introduced(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut marks: Vec<String> = Vec::new();
        let mut rest = goal.clone();
        while rest.label() == Some("wrex") {
            marks.push(rest.children()[1].variable().unwrap_or("").to_string());
            rest = rest.children()[0].clone();
        }
        let mark_set: BTreeSet<String> = marks.iter().cloned().collect();
        let mut found: Option<Binding> = None;
        let keys = facts.keys();
        'parts: for piece in self.parts(&self.rpn(&rest)) {
            let shape = as_class(&self.to_term(&piece), &mark_set);
            for said in &keys {
                if let Some(fits) =
                    fit(&shape, &self.to_term(said), &Binding::new(), &mark_set)
                {
                    if fits.len() == marks.len() {
                        found = Some(fits);
                        break 'parts;
                    }
                }
            }
        }
        let Some(found) = found else {
            return Ok(Route::no("no fact in scope names what the claim binds"));
        };
        // What each binder stands for, as `rspcev` wants it: a class.
        let mut stood: IndexMap<String, Rpn> = IndexMap::new();
        for (name, term) in &found {
            let said = self.rpn(term);
            stood.insert(
                name.to_string(),
                if term.variable().is_some() {
                    t!(said, "cv")
                } else {
                    said
                },
            );
        }
        let mut layers: Vec<(Term, String, Rpn)> = Vec::new();
        let mut rest = goal.clone();
        while rest.label() == Some("wrex") {
            let kids = rest.children().to_vec();
            layers.push((
                kids[0].clone(),
                kids[1].variable().unwrap_or("").to_string(),
                self.rpn(&kids[2]),
            ));
            rest = kids[0].clone();
        }
        let mut proof: Option<Proof> = None;
        for i in (0..layers.len()).rev() {
            let (body, name, over) = layers[i].clone();
            // The body with every binder outside this one already standing
            // at its witness, and then with this one too.
            let var = self.float_of(&name);
            let mut held = body;
            for (_, n, _) in &layers[..i] {
                held = self.restated(&held, &t!(self.float_of(n), "cv"), &stood[n]);
            }
            let here = self.restated(&held, &t!(var, "cv"), &stood[&name]);
            let (ph, ps) = (self.rpn(&held), self.rpn(&here));
            if proof.is_none() {
                proof = Some(take!(self.settle(&here, scope, facts, 3, None, None)?));
            }
            let witness = stood[&name].clone();
            let tie = self.to_term(&t!(
                t!(var, "cv", witness, "wceq"),
                t!(ph, ps, "wb"),
                "wi"
            ));
            let instance = take!(self.prove_essential(&tie, scope, facts)?);
            let member = t!(witness, over, "wcel");
            let stands = take!(self.settle(
                &self.to_term(&member),
                scope,
                facts,
                3,
                None,
                None
            )?);
            let inner = proof.take().unwrap();
            let both = pf!(self.b; scope, member, ps, stands, inner, "jca");
            proof = Some(
                pf!(self.b; scope, t!(member, ps, "wa"), t!(ph, var, over, "wrex"), both,
                ph, ps, var, witness, over, instance, "rspcev", "syl"),
            );
        }
        Ok(Built(proof.expect("an existential of one binder at least")))
    }

    /// A lemma said of every such name: the name is fixed, the lemma applied
    /// to it, and the claim generalised (`for_every`).
    fn as_generalised(
        &mut self,
        label: &str,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        if goal.label() != Some("wral") {
            return Ok(Route::no("the claim is not \"for all\""));
        }
        let (body, variable, over) = (
            goal.children()[0].clone(),
            goal.children()[1].clone(),
            goal.children()[2].clone(),
        );
        self.for_every(
            scope,
            facts,
            &body,
            &variable,
            &over,
            &mut |me, said, inner, lifted| {
                me.apply_lemma(label, said, inner, lifted, step, false, seed)
            },
            false,
        )
    }

    /// One half of what a lemma concludes: the half the claim is fixes the
    /// lemma, and `simpld` or `simprd` takes it.
    #[allow(clippy::too_many_arguments)]
    fn as_conjunct(
        &mut self,
        label: &str,
        whole: &Term,
        reads: &Term,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        if reads.label() != Some("wa") || reads.children().len() != 2 {
            return Ok(Route::no(format!(
                "{label} does not conclude a conjunction"
            )));
        }
        let mut asks = Vec::new();
        let mut walk = whole.clone();
        while matches!(walk.label(), Some("wi") | Some("wb"))
            && !walk.same_object(reads)
        {
            asks.push(walk.children()[0].clone());
            walk = walk.children()[1].clone();
        }
        let variables = names_of(whole);
        let keys = facts.keys();
        for (i, part) in reads.children().iter().enumerate() {
            let Some(mut bound) =
                fit(part, goal, &seed.cloned().unwrap_or_default(), &variables)
            else {
                continue;
            };
            // A half need not name everything the lemma does, and what is
            // left open is what the step cited a line for.
            for slot in &asks {
                if reads.names().iter().all(|n| bound.contains_key(&**n)) {
                    break;
                }
                for held in &keys {
                    if let Some(filled) =
                        fit(slot, &self.to_term(held), &bound, &variables)
                    {
                        bound = filled;
                        break;
                    }
                }
            }
            if reads.names().iter().any(|n| !bound.contains_key(&**n)) {
                continue;
            }
            let said = reads.substitute(&bound);
            let Built(proof) = self.apply_lemma(
                label,
                &said,
                scope,
                facts,
                step,
                false,
                Some(&bound),
            )?
            else {
                continue;
            };
            let (a, b) = (self.rpn(&said.children()[0]), self.rpn(&said.children()[1]));
            let pick = if i == 0 { "simpld" } else { "simprd" };
            return Ok(Built(pf!(self.b; scope, a, b, proof, pick)));
        }
        Ok(Route::no(format!(
            "neither half of what {label} concludes is the claim"
        )))
    }

    /// A lemma whose `with` target already says what it concludes: where the
    /// seed fixes every variable there is nothing left for the claim to fix,
    /// and the two need not be spelt the same.
    #[allow(clippy::too_many_arguments)]
    fn as_seeded(
        &mut self,
        label: &str,
        reads: &Term,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let full =
            seed.is_some_and(|s| reads.names().iter().all(|n| s.contains_key(&**n)));
        if !full {
            return Ok(Route::no(format!(
                "the target does not fix every variable of {label}"
            )));
        }
        let seed = seed.unwrap();
        let said = reads.substitute(seed);
        if self.rpn(&said) == self.rpn(goal) {
            return Ok(Route::no(format!(
                "{label} at its seed is the claim as written"
            )));
        }
        let proof = take!(self.apply_lemma(
            label,
            &said,
            scope,
            facts,
            step,
            false,
            Some(seed)
        )?);
        // No bridge means the lemma is not this claim said otherwise.
        let across = match self.bridging(&said, goal, scope, facts, step)? {
            Built(p) => Some(p),
            Declined(_) => self.by_equation(&said, goal, scope, facts, step)?,
        };
        let Some(across) = across else {
            return Ok(Route::no(format!(
                "nothing carries what {label} gives to the claim"
            )));
        };
        Ok(Built(
            pf!(self.b; scope, self.rpn(&said), self.rpn(goal), proof, across, "mpbid"),
        ))
    }

    /// A lemma's conclusion carried to the claim by an equation proved: each
    /// place the two terms differ is one equation, and it is settled where it
    /// stands.
    fn by_equation(
        &mut self,
        said: &Term,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
    ) -> Checked<Option<Proof>> {
        let proved = Leaf::Rows(vec![Row::Held]);
        if let Built(straight) =
            self.congruence(said, goal, scope, facts, step, &proved)?
        {
            return Ok(Some(straight));
        }
        if goal.label() != Some("wceq") || goal.children().len() != 2 {
            return Ok(None);
        }
        // An equation is the same equation written the other way round.
        let turned = Term::apply(
            "wceq",
            vec![goal.children()[1].clone(), goal.children()[0].clone()],
        );
        let Built(across) =
            self.congruence(said, &turned, scope, facts, step, &proved)?
        else {
            return Ok(None);
        };
        let Built(back) = self.same(&turned, goal, scope, facts, step)? else {
            return Ok(None);
        };
        Ok(Some(self.chained(
            scope,
            &[
                ChainLink {
                    from: said.clone(),
                    to: turned.clone(),
                    proof: across,
                },
                ChainLink {
                    from: turned,
                    to: goal.clone(),
                    proof: back,
                },
            ],
        )))
    }

    /// A lemma reaching a claim it says in other words: both are read through
    /// the rules of `rules::STANDARD` and matched again, which fixes what the
    /// lemma's variables stand for, and `same` carries it to the claim.
    /// What the lemma concludes is tried first, then the near side of each
    /// biconditional it states, and last each biconditional whole.
    #[allow(clippy::too_many_arguments)]
    fn in_other_words(
        &mut self,
        label: &str,
        whole: &Term,
        reads: &Term,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let variables = names_of(whole);
        let mut sides = vec![reads.clone()];
        let mut wholes = Vec::new();
        let mut rest = whole.clone();
        while matches!(rest.label(), Some("wi") | Some("wb")) {
            if rest.label() == Some("wb") {
                sides.push(rest.children()[0].clone());
                wholes.push(rest.clone());
            }
            rest = rest.children()[1].clone();
        }
        sides.extend(wholes);
        let theirs = self.read_through(goal, true, None);
        let mut found: Route<Proof> = Route::no(format!(
            "{label} does not conclude the claim in any words the rules read"
        ));
        // The seed as written first, and then read the way the claim is.
        let mut seeds = vec![seed.cloned().unwrap_or_default()];
        if let Some(seed) = seed.filter(|s| !s.is_empty()) {
            let mut read = Binding::new();
            for (name, value) in seed {
                read.insert(*name, self.read_through(value, true, None));
            }
            seeds.push(read);
        }
        for side in &sides {
            for sown in &seeds {
                let Some(binding) = self.fit_read(side, &theirs, sown, &variables)
                else {
                    continue;
                };
                if side.names().iter().any(|n| !binding.contains_key(&**n)) {
                    continue;
                }
                let binding = self.refolded(binding, goal);
                let instance = side.substitute(&binding);
                if self.rpn(&instance) == self.rpn(goal) {
                    continue;
                }
                found = self.apply_lemma(
                    label,
                    &instance,
                    scope,
                    facts,
                    step,
                    false,
                    Some(&binding),
                )?;
                let Built(made) = found.clone() else {
                    continue;
                };
                // What carries the instance to the claim asks as a lemma
                // does, from what the step names.
                let held = match step {
                    None => facts.clone(),
                    Some(step) => {
                        let supplied = self.supplied(Some(step), scope, facts)?;
                        self.with_cited(Some(step), scope, &supplied, None)
                    }
                };
                let across = self.same(&instance, goal, scope, &held, step)?;
                let Built(across) = across else {
                    found = across;
                    continue;
                };
                return Ok(Built(
                    pf!(self.b; scope, self.rpn(&instance), self.rpn(goal), made, across, "mpbid"),
                ));
            }
        }
        Ok(found)
    }

    /// What a lemma's variables stand for where its `pattern` is `term`: as
    /// written, or else with both read in standard form (`read_through`);
    /// None where neither fits.
    pub fn fits_as(
        &mut self,
        pattern: &Term,
        term: &Term,
        variables: &Vars,
        seed: Option<&Binding>,
    ) -> Option<Binding> {
        let start = seed.cloned().unwrap_or_default();
        if let Some(binding) = fit(pattern, term, &start, variables) {
            return Some(binding);
        }
        let t = self.read_through(term, true, None);
        let binding = self.fit_read(pattern, &t, &start, variables)?;
        Some(self.refolded(binding, term))
    }

    /// What a lemma's variables stand for where its `pattern`, read in
    /// standard form, is `read`, a term already read so: the two are fitted
    /// with `read`'s bound letters spelt as the pattern binds them
    /// (`respelt_as`). What is fitted is the lemma's instance, which says what
    /// `read` says over other bound letters at most, and the caller carries
    /// it to the claim by `same`.
    fn fit_read(
        &mut self,
        pattern: &Term,
        read: &Term,
        seed: &Binding,
        variables: &Vars,
    ) -> Option<Binding> {
        let p = self.read_through(pattern, false, None);
        let t = self.respelt_as(&p, read, variables);
        fit_either_way(&p, &t, seed, variables)
    }

    /// `term` with its bound letters respelt so that each letter `pattern`
    /// binds is met in one spelling. A lemma may bind one letter at two
    /// binders, as `count-shift` binds i on both sides, while the claim spells
    /// the two apart: a define's body binds a letter of its own (`apart`), so
    /// a claim naming it reads one set over that letter and the other over
    /// the page's. The two spellings are one claim by a renaming, but a fit
    /// reads the lemma's letter off the first binder and finds the second
    /// different. Where the pattern binds one of its `variables` and has met
    /// it before, the term's letter at that binder is renamed to the one met,
    /// throughout the binder's part and only where that letter appears
    /// nowhere in it, so the result says what `term` says. A binder is a
    /// constructor other than `cv` with a set variable directly under it, as
    /// `letters_bound` reads them.
    fn respelt_as(&self, pattern: &Term, term: &Term, variables: &Vars) -> Term {
        let mut met = IndexMap::new();
        self.respelt_within(pattern, term, variables, &mut met)
    }

    /// `respelt_as` at one part, `met` holding the spelling each pattern
    /// letter was met in so far.
    fn respelt_within(
        &self,
        pattern: &Term,
        term: &Term,
        variables: &Vars,
        met: &mut IndexMap<String, String>,
    ) -> Term {
        if pattern.variable().is_some()
            || term.variable().is_some()
            || pattern.label() != term.label()
            || pattern.children().len() != term.children().len()
        {
            return term.clone();
        }
        let mut term = term.clone();
        if pattern.label() != Some("cv") {
            for (k, p) in pattern.children().iter().enumerate() {
                let (Some(p), Some(w)) = (p.variable(), term.children()[k].variable())
                else {
                    continue;
                };
                if !variables.contains(p)
                    || !self.is_setvar(&self.float_of(p))
                    || !self.is_setvar(&self.float_of(w))
                {
                    continue;
                }
                let Some(u) = met.get(p).cloned() else {
                    met.insert(p.to_string(), w.to_string());
                    continue;
                };
                if u != w && !term.names().contains(u.as_str()) {
                    let mut to = Binding::new();
                    to.insert(Symbol::of(w), Term::var(&u));
                    term = term.substitute(&to);
                }
            }
        }
        let kids: Vec<Term> = pattern
            .children()
            .iter()
            .zip(term.children())
            .map(|(p, t)| self.respelt_within(p, t, variables, met))
            .collect();
        Term::apply(term.label().unwrap_or(""), kids)
    }

    /// `binding` with a value the reading wrote out put back as `term`
    /// writes it, where written out it spells a letter another value binds.
    fn refolded(&mut self, binding: Binding, term: &Term) -> Binding {
        // What each value binds, and a lemma's own letter as the letter it
        // stands for.
        let mut binds: IndexMap<String, BTreeSet<String>> = IndexMap::new();
        for (name, value) in &binding {
            let mut out: BTreeSet<String> = self
                .letters_bound(value)
                .iter()
                .map(|v| self.float_of(v))
                .filter(|l| self.is_setvar(l))
                .collect();
            if let Some(v) = value.variable() {
                let l = self.float_of(v);
                if self.is_setvar(&l) {
                    out.insert(l);
                }
            }
            binds.insert(name.to_string(), out);
        }
        let mut written: IndexMap<Rpn, Term> = IndexMap::new();
        for sub in subterms(term) {
            let read = self.read_through(&sub, true, None);
            written.entry(self.rpn(&read)).or_insert(sub);
        }
        let mut out = binding.clone();
        for (name, value) in &binding {
            let said = self.rpn(value);
            let others: BTreeSet<&String> = binds
                .iter()
                .filter(|(n, _)| *n != name)
                .flat_map(|(_, b)| b.iter())
                .collect();
            if let Some(w) = written.get(&said) {
                if said
                    .tokens()
                    .iter()
                    .any(|t| others.iter().any(|o| *t == o.as_str()))
                    && self.rpn(w) != said
                {
                    out.insert(*name, w.clone());
                }
            }
        }
        out
    }

    /// A term with every one-way rule of the standard form applied, parts
    /// first, and nothing put in order: for finding what a lemma's variables
    /// stand for, and nothing else. A defined name is read as what it names
    /// only where `named`.
    pub fn read_through(
        &mut self,
        term: &Term,
        named: bool,
        letters: Option<&Vars>,
    ) -> Term {
        let owned;
        let letters = match letters {
            Some(l) => l,
            None => {
                owned = self.letters_bound(term);
                &owned
            }
        };
        if named {
            if let Some(body) = self.named_body(term, letters) {
                return self.read_through(&body, named, Some(letters));
            }
        }
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        let kids: Vec<Term> = term
            .children()
            .iter()
            .map(|c| self.read_through(c, named, Some(letters)))
            .collect();
        let term = Term::apply(term.label().unwrap_or(""), kids);
        if named {
            if let Some(applied) = self.applied_body(&term) {
                return self.read_through(&applied, named, Some(letters));
            }
        }
        for conditional in [false, true] {
            for rule in self.rewrites(conditional).iter() {
                if let Some(bound) =
                    fit(&rule.given, &term, &Binding::new(), &rule.names)
                {
                    if rule.gives.names().iter().all(|n| bound.contains_key(&**n)) {
                        return self.read_through(
                            &rule.gives.substitute(&bound),
                            named,
                            Some(letters),
                        );
                    }
                }
            }
        }
        term
    }

    /// A term with each defined name standing free read as what it names,
    /// and nothing else rewritten: a function applied is left applied.
    pub fn names_read(&self, term: &Term, letters: Option<&Vars>) -> Term {
        let owned;
        let letters = match letters {
            Some(l) => l,
            None => {
                owned = self.letters_bound(term);
                &owned
            }
        };
        if let Some(body) = self.named_body(term, letters) {
            return self.names_read(&body, Some(letters));
        }
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        let n = term.children().len();
        let kids: Vec<Term> = term
            .children()
            .iter()
            .enumerate()
            .map(|(i, c)| {
                if term.label() == Some("cfv") && i == n - 1 {
                    c.clone()
                } else {
                    self.names_read(c, Some(letters))
                }
            })
            .collect();
        Term::apply(term.label().unwrap_or(""), kids)
    }

    /// A term with each defined function applied to a value read as its rule
    /// there, parts first, and nothing else rewritten.
    pub fn applications_read(&mut self, term: &Term) -> Term {
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        let kids: Vec<Term> = term
            .children()
            .iter()
            .map(|c| self.applications_read(c))
            .collect();
        let term = Term::apply(term.label().unwrap_or(""), kids);
        match self.applied_body(&term) {
            None => term,
            Some(applied) => self.applications_read(&applied),
        }
    }

    /// `fit_respelt` of a hypothesis to a line, where a letter the binding
    /// already fixes may come out as the same formula over other bound
    /// letters. A claim made where its bound letter is a fixed name binds
    /// another: inside a block that lets x, "for all x ∈ V, …" is spelt over a
    /// spare letter, and the induction hypothesis it is the consequent of is
    /// not. The line is fitted with the fixed letters left open, and each
    /// must come out the formula it has, or that formula over other bound
    /// letters, which `held_rebound` carries across when the hypothesis is
    /// proved.
    fn fit_over_bound(
        &self,
        pattern: &Term,
        held: &Term,
        binding: &Binding,
        variables: &Vars,
        fresh: &Binding,
    ) -> Option<Binding> {
        let filled = fit_respelt(pattern, held, &Binding::new(), variables, fresh)?;
        let agrees = filled.iter().all(|(k, v)| match binding.get(k) {
            Some(had) => {
                let (had, v) = (self.rpn(had), self.rpn(v));
                had == v || self.rebound(&had, &v)
            }
            None => true,
        });
        if !agrees {
            return None;
        }
        let mut out = binding.clone();
        for (k, v) in filled {
            out.entry(k).or_insert(v);
        }
        Some(out)
    }

    /// A lemma reaching a claim written without an identity element its
    /// conclusion has (`SYNTAX.md`, the literal-instance rule): the
    /// conclusion is fitted reading x + 0 as x where the claim has x
    /// (`fit_tidied`), the lemma is applied to that literal instance, and
    /// the instance is carried to the claim (`tidied`).
    #[allow(clippy::too_many_arguments)]
    fn as_tidied(
        &mut self,
        label: &str,
        reads: &Term,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let variables = names_of(&self.statement(label));
        let start = seed.cloned().unwrap_or_default();
        let Some(binding) = self.fit_tidied(reads, goal, &start, &variables) else {
            return Ok(Route::no(format!("{label} does not conclude the claim")));
        };
        // A variable a hypothesis decides is taken at that value, which may
        // hold an identity element the claim leaves out: `fsum1p`'s first
        // term is its summand at the bottom of the range.
        let sig = self.sig(label).clone();
        let binding = self.read_off(&sig, binding, &variables);
        let settled = self.instanced(&sig, binding);
        let literal = reads.substitute(&settled);
        let (said, want) = (self.rpn(&literal), self.rpn(goal));
        if said == want {
            return Ok(Route::no(format!("{label} does not conclude the claim")));
        }
        let made =
            take!(self.apply_lemma(label, &literal, scope, facts, step, true, seed)?);
        Ok(match self.tidied(&made, &said, &want, scope, facts)? {
            Some(p) => Built(p),
            None => self.no(
                format!(
                    "{label} concludes {{}} and nothing drops its identity elements"
                ),
                &[&said],
            ),
        })
    }

    /// `fit`, where a pattern's operation may stand with its identity
    /// element in a hole the notation record allows it and the other hole
    /// matched against the term: ( A + C ) against 1 with A := 0.
    fn fit_tidied(
        &self,
        pattern: &Term,
        term: &Term,
        binding: &Binding,
        variables: &Vars,
    ) -> Option<Binding> {
        if let Some(found) = fit(pattern, term, binding, variables) {
            return Some(found);
        }
        if pattern.variable().is_some() {
            return None;
        }
        if pattern.label() == term.label()
            && pattern.children().len() == term.children().len()
        {
            let mut at = binding.clone();
            let all = pattern
                .children()
                .iter()
                .zip(term.children())
                .all(|(p, t)| match self.fit_tidied(p, t, &at, variables) {
                    Some(next) => {
                        at = next;
                        true
                    }
                    None => false,
                });
            if all {
                return Some(at);
            }
        }
        for law in &self.identities {
            if pattern.label() != Some(law.constructor.as_str())
                || pattern.children().len() != law.fixed.len() + 2
                || law.fixed.iter().any(|(k, token)| {
                    self.rpn(&pattern.children()[*k]).alone() != Some(token.as_str())
                })
            {
                continue;
            }
            let element = self.to_term(&super::field::numeral(law.element));
            for &hole in &law.holes {
                let (unit, kept) = if hole == 0 {
                    (law.places.0, law.places.1)
                } else {
                    (law.places.1, law.places.0)
                };
                // The element is one the instance has, a variable already
                // fixed as it: none is made up to read x as 0 + x.
                let unit = &pattern.children()[unit];
                if unit
                    .names()
                    .iter()
                    .any(|n| variables.contains(n) && !binding.contains_key(&**n))
                {
                    continue;
                }
                let Some(at) = self.fit_tidied(unit, &element, binding, variables)
                else {
                    continue;
                };
                if let Some(found) =
                    self.fit_tidied(&pattern.children()[kept], term, &at, variables)
                {
                    return Some(found);
                }
            }
        }
        None
    }

    /// Whether a lemma is in deduction form: it states ( ph -> … ) with ph a
    /// letter, and asks at least one hypothesis, every one of them
    /// ( ph -> … ) under the same ph.
    fn in_deduction_form(&self, sig: &Signature, whole: &Term) -> bool {
        if whole.label() != Some("wi") || sig.essentials.is_empty() {
            return false;
        }
        let Some(context) = whole.children()[0].variable() else {
            return false;
        };
        sig.essentials.iter().all(|e| {
            let asked = self.essential(e);
            asked.label() == Some("wi")
                && asked.children()[0].variable() == Some(context)
        })
    }

    /// Apply one set.mm lemma to reach a claim, side conditions and all.
    ///
    /// What a lemma states before the claim it reaches may be an implication
    /// or a biconditional; both are peeled, and which one each was decides
    /// how it is discharged. `seed` is what a `with` target said the lemma's
    /// variables stand for.
    #[allow(clippy::too_many_arguments)]
    pub fn apply_lemma(
        &mut self,
        label: &str,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        crossing: bool,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let sig = self.sig(label).clone();
        let whole = self.statement(label);
        let variables = names_of(&whole);
        let start = seed.cloned().unwrap_or_default();
        let mut antecedents: Vec<Term> = Vec::new();
        let mut joins: Vec<Join> = Vec::new();
        let mut reads = whole.clone();
        // A lemma in deduction form, `mpd`'s ( ph -> ch ) with every
        // hypothesis under ph, assumes ph as the scope it is used in. Its
        // statement is not the claim even where the claim is an "if": ph is
        // the scope, and what the claim says is ch.
        let mut under_context = self.in_deduction_form(&sig, &whole);
        let mut binding = loop {
            if !std::mem::take(&mut under_context) {
                if let Some(b) = fit(&reads, goal, &start, &variables) {
                    break b;
                }
            }
            if !matches!(reads.label(), Some("wi") | Some("wb")) {
                if crossing {
                    let through = self.through_existential(
                        label, &reads, goal, scope, facts, step, seed,
                    )?;
                    if !through.is_declined() {
                        return Ok(through);
                    }
                    let seeded =
                        self.as_seeded(label, &reads, goal, scope, facts, step, seed)?;
                    if !seeded.is_declined() {
                        return Ok(seeded);
                    }
                    let part = self.as_conjunct(
                        label, &whole, &reads, goal, scope, facts, step, seed,
                    )?;
                    if !part.is_declined() {
                        return Ok(part);
                    }
                    let every =
                        self.as_generalised(label, goal, scope, facts, step, seed)?;
                    if !every.is_declined() {
                        return Ok(every);
                    }
                    let other = self.in_other_words(
                        label, &whole, &reads, goal, scope, facts, step, seed,
                    )?;
                    if !other.is_declined() {
                        return Ok(other);
                    }
                    let tidy =
                        self.as_tidied(label, &reads, goal, scope, facts, step, seed)?;
                    return Ok(if tidy.is_declined() { other } else { tidy });
                }
                return Ok(Route::no(format!("{label} does not conclude the claim")));
            }
            // A biconditional says one thing and reaching it either way is
            // reaching it; tried only where the forward read has already
            // failed, and with the seed, as the forward read is.
            if reads.label() == Some("wb") {
                // Where both sides fit, the claim is the side that says more
                // of it: `A <_ B` fits any inequality, `( C x. A ) <_ ( C x.
                // B )` only a product's. On a tie it is the near side.
                let (near, far) = (&reads.children()[0], &reads.children()[1]);
                if let Some(forward) = fit(far, goal, &start, &variables).filter(|_| {
                    fit(near, goal, &start, &variables).is_none()
                        || constructors(far) > constructors(near)
                }) {
                    antecedents.push(reads.children()[0].clone());
                    joins.push(Join::Iff);
                    reads = reads.children()[1].clone();
                    break forward;
                }
                if let Some(turned) =
                    fit(&reads.children()[0], goal, &start, &variables)
                {
                    antecedents.push(reads.children()[1].clone());
                    joins.push(Join::Turned);
                    reads = reads.children()[0].clone();
                    break turned;
                }
                // The near side may be the claim said differently, and only a
                // full seed can tell.
                if crossing {
                    let near = reads.children()[0].clone();
                    let seeded =
                        self.as_seeded(label, &near, goal, scope, facts, step, seed)?;
                    if !seeded.is_declined() {
                        return Ok(seeded);
                    }
                }
                // One way of the biconditional may be the claim.
                if goal.label() == Some("wi") {
                    let taken = self.one_direction(
                        label, &reads, goal, &variables, scope, facts, step, crossing,
                        seed,
                    )?;
                    if !taken.is_declined() {
                        return Ok(taken);
                    }
                }
            }
            antecedents.push(reads.children()[0].clone());
            joins.push(if reads.label() == Some("wb") {
                Join::Iff
            } else {
                Join::Implies
            });
            reads = reads.children()[1].clone();
        };
        let _ = &reads;

        // A lemma whose hypothesis says what one of its variables is has
        // already decided it. Where the two disagree the claim is not what
        // the lemma concludes, so the lemma is proved at its own value
        // instead.
        binding = self.read_off(&sig, binding, &variables);
        let settled = self.instanced(&sig, binding.clone());
        if binding
            .iter()
            .any(|(name, stood)| self.rpn(&settled[name]) != self.rpn(stood))
        {
            return self
                .at_its_own_value(label, &sig, goal, scope, facts, step, &settled);
        }
        binding = settled;
        // Two letters the lemma binds and keeps apart, which the claim spells
        // alike, cannot both be the claim's.
        let kinds: IndexMap<&str, &str> = sig
            .floats
            .iter()
            .map(|(t, v)| (v.as_str(), t.as_str()))
            .collect();
        if sig.disjoint.iter().any(|(a, b)| {
            kinds.get(a.as_str()) == Some(&"setvar")
                && kinds.get(b.as_str()) == Some(&"setvar")
                && binding.contains_key(a)
                && binding.contains_key(b)
                && self.rpn(&binding[a]) == self.rpn(&binding[b])
        }) {
            return self.letters_apart(label, goal, scope, facts, step, crossing, seed);
        }
        // A letter the lemma binds and keeps apart from its scope, which the
        // claim never fixes, is given one nothing holds before anything else
        // could lend it one. What the lemma's other variables stand for is
        // still read off the facts, whose letters are their own
        // (`fit_respelt`).
        let before = binding.clone();
        binding = self.letters_unheld(&sig, binding);
        // A substitution the lemma asks over one of those letters was worked
        // out above in the lemma's own spelling of it: `gcntshift` asks
        // ( i = j -> ( ps <-> th ) ), and th is ps at j. It is worked out
        // again at the letter j now stands for.
        binding = self.instanced(&sig, binding);
        let fresh: Binding = binding
            .iter()
            .filter(|(k, _)| !before.contains_key(*k))
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        // A deduction's hypothesis may bind letters its conclusion never
        // names, each its own: each is the letter the line the step cites for
        // that hypothesis binds. A hypothesis that is a bare letter under the
        // context, as `mpbid` asks ( ph -> ps ), would fit any line, so it is
        // fitted to none and is fixed by the hypotheses that give it a shape.
        // A cited line of several sentences supplies each of them, and a
        // requires line of the step is a line it names as surely, so what
        // it says is offered too: `If b = 0 then c = 0` as a requires line
        // fixes modus ponens's P as it does cited.
        let mut cited: Vec<Term> = match step {
            Some(step) => step
                .just
                .refs
                .iter()
                .filter_map(|r| self.lines.get(r))
                .flat_map(|l| conjuncts_of(&self.to_term(&l.term)))
                .collect(),
            None => Vec::new(),
        };
        if let Some(step) = step {
            for r in &step.requires {
                let node = self.read_one(&r.fact)?;
                let said = self.term(&node)?;
                cited.extend(conjuncts_of(&self.to_term(&said)));
            }
        }
        for text in &sig.essentials {
            let said = self.essential(text);
            if said.label() != Some("wi") || said.children()[0].variable().is_none() {
                continue;
            }
            let said = said.children()[1].clone();
            if said.variable().is_some()
                || said.names().iter().all(|n| binding.contains_key(&**n))
            {
                continue;
            }
            let mut vars = variables.clone();
            vars.extend(said.names().iter().cloned());
            for held in &cited {
                if let Some(filled) =
                    self.fit_over_bound(&said, held, &binding, &vars, &fresh)
                {
                    binding = filled;
                    break;
                }
            }
        }
        // The scope is where a lemma's disjointness conditions can forbid it,
        // so it is chosen before anything is built.
        let (mut where_, mut frame) = self.allowed(&sig, &binding);
        if where_.is_declined() {
            // Which scope is allowed depends on what the variables stand
            // for, so what the facts decide is read and the question asked
            // again — only here, because binding early changes which fact
            // answers an antecedent.
            let keys = facts.keys();
            for slot in &antecedents {
                if slot.variable().is_some()
                    || slot.names().iter().all(|n| binding.contains_key(&**n))
                {
                    continue;
                }
                for held in &keys {
                    if let Some(filled) = fit_respelt(
                        slot,
                        &self.to_term(held),
                        &binding,
                        &variables,
                        &fresh,
                    ) {
                        binding = filled;
                        break;
                    }
                }
            }
            (where_, frame) = self.allowed(&sig, &binding);
            if let Declined(why) = where_ {
                // The claim's own bound letter may be what every frame
                // spells.
                return self.over_other_letters(
                    label, goal, scope, facts, step, crossing, seed, why,
                );
            }
        }
        // An outer frame knows less than the step does: lines written inside
        // the inner one are not there. Where the claim's own bound letter is
        // what the inner scope spells, the lemma is tried there over another
        // letter first, and the outer frame is the way taken only if that
        // does not reach the claim.
        if frame.is_some_and(|f| f + 1 < self.frames.len()) {
            let why = Decline::new("an inner scope spells the claim's letter");
            let moved = self.over_other_letters(
                label, goal, scope, facts, step, crossing, seed, why,
            )?;
            if !moved.is_declined() {
                return Ok(moved);
            }
        }
        let Built(where_) = where_ else {
            unreachable!("an allowed scope")
        };
        let frame = frame.expect("the frame of an allowed scope");
        let at_frame = self.frames_facts(frame, facts);
        let supplied = self.supplied(step, &where_, &at_frame)?;
        let known = self.with_cited(step, &where_, &supplied, None);
        self.with_implied(step, &where_, &known)?;
        // A bare `Z e. B` with Z open is answered by any line putting
        // anything in B, so every such conjunct is matched after the rest.
        let loose: Vec<Term> = antecedents
            .iter()
            .filter(|s| s.variable().is_none())
            .flat_map(conjuncts_of)
            .filter(|p| {
                p.label() == Some("wcel")
                    && p.children()[0]
                        .variable()
                        .is_some_and(|v| !binding.contains_key(v))
            })
            .collect();
        // What fills an antecedent is only what the proof being built may
        // rest on, as for `settle`: a line the step does not name cannot
        // decide a class the lemma leaves open.
        let known_keys = match &self.resting {
            Some(resting) => known
                .filtered(|_, v| v.origin.iter().all(|o| may_rest_on(resting, o)))
                .keys(),
            None => known.keys(),
        };
        let mut slots: Vec<Option<&Term>> = antecedents.iter().map(Some).collect();
        slots.push(None);
        for slot in slots {
            let pieces: Vec<Term> = match slot {
                None => loose.clone(),
                Some(s) if s.names().iter().all(|n| binding.contains_key(&**n)) => {
                    continue
                }
                Some(s) if s.variable().is_some() => {
                    binding.insert(s.variable_symbol().unwrap(), self.to_term(&where_));
                    continue;
                }
                Some(s) => conjuncts_of(s)
                    .into_iter()
                    .filter(|p| !loose.iter().any(|one| one.same_object(p)))
                    .collect(),
            };
            // What the lemma concludes need not fix everything it asks, so an
            // antecedent that is still open is matched against something the
            // step already has, one conjunct at a time.
            for piece in &pieces {
                if piece.names().iter().all(|n| binding.contains_key(&**n)) {
                    continue;
                }
                let mut filled_any = false;
                for held in &known_keys {
                    if let Some(filled) = fit_respelt(
                        piece,
                        &self.to_term(held),
                        &binding,
                        &variables,
                        &fresh,
                    ) {
                        binding = filled;
                        filled_any = true;
                        break;
                    }
                }
                if !filled_any {
                    // Or as the standard form reads the line.
                    for held in &known_keys {
                        let fact = self.to_term(held);
                        if let Some(filled) =
                            self.fits_as(piece, &fact, &variables, Some(&binding))
                        {
                            binding = filled;
                            break;
                        }
                    }
                }
            }
            if let Some(slot) = slot {
                for open in sethood(slot, &binding) {
                    binding.insert(open, self.to_term(&t!("cvv")));
                }
            }
        }
        let mut asked_all = Vec::new();
        for e in &sig.essentials {
            let asked = self.essential(e).substitute(&binding);
            asked_all.push(self.prove_essential(&asked, &where_, &known)?);
        }
        let mut essentials = Vec::new();
        for one in asked_all {
            essentials.push(take!(one));
        }
        let mut proof = self.b.ap(
            label,
            &self.spelt(&binding),
            &essentials.iter().collect::<Vec<_>>(),
        );
        let goal_rpn = self.rpn(goal);
        if antecedents.is_empty() {
            // The lemma asks nothing, so it states the claim outright and has
            // to be brought into the scope the step sits in.
            let carried = pf!(self.b; goal_rpn, where_, proof, "a1i");
            return Ok(Built(self.carry(carried, &goal_rpn, frame)));
        }
        let (mut where_, mut frame, mut known) = (where_, frame, known);
        let mut carried = false;
        let mut stood_under = false;
        for (i, slot) in antecedents.iter().enumerate() {
            let asks = slot.substitute(&binding);
            let asks_rpn = self.rpn(&asks);
            let mut is_scope = asks_rpn == where_;
            // Standing under a scope rests on every line it is made of. Where
            // the step does not name them all, as where a letter's membership
            // is said once and its line not cited, the formula is settled a
            // part at a time like any other.
            if is_scope && slot.variable().is_none() {
                if let Some(resting) = self.resting.clone() {
                    let more = self.scope_origin(&where_, &known)?;
                    if !more.iter().all(|o| may_rest_on(&resting, o)) {
                        is_scope = false;
                    }
                }
            }
            // A variable slot is the context a deduction-form lemma is stated
            // in, and uses nothing; a formula the scope happens to be is what
            // the lemma asks, and uses all of it.
            stood_under = stood_under || (is_scope && slot.variable().is_none());
            // Only a first slot the lemma implies from is the scope's own
            // place, so that the lemma then reads `scope -> claim` as it
            // stands; one it states a biconditional with, or asks after
            // another, is discharged as any is, by the scope itself (`id`).
            if is_scope && i == 0 && joins[i] == Join::Implies {
                carried = true;
                continue; // the deduction slot
            }
            let mut rest = goal_rpn.clone();
            for (later, join) in antecedents[i + 1..].iter().zip(&joins[i + 1..]).rev()
            {
                let said = self.rpn(&later.substitute(&binding));
                if said != where_ {
                    // A biconditional crossed the other way puts the claim on
                    // the left.
                    rest = if *join == Join::Turned {
                        t!(rest, said, "wb")
                    } else {
                        t!(said, rest, join_token(*join))
                    };
                }
            }
            // What decides the fold is whether what has been built so far
            // states its claim outright or states it under the scope.
            let mut first = proof.last() == label && !carried;
            let (mut x, mut y) = if joins[i] == Join::Turned && !first {
                (rest.clone(), asks_rpn.clone())
            } else {
                (asks_rpn.clone(), rest.clone())
            };
            // A "there is" the lemma asks can be given by an instance a line
            // the step cites names; only then is the step passed.
            let instanced = self
                .parts(&asks_rpn)
                .iter()
                .any(|p| self.to_term(p).label() == Some("wrex"));
            let mut under = if is_scope {
                Built(pf!(self.b; where_, "id"))
            } else if instanced && step.is_some() {
                let lines = self.lines.clone();
                self.settle(&asks, &where_, &known, 3, step, Some(&lines))?
            } else {
                self.settle(&asks, &where_, &known, 3, None, None)?
            };
            // An antecedent the lemma's frame does not hold may be one an
            // inner assumption gives, as a case that a sum is 0 gives a lemma
            // that keeps the sum's letter out of its scope: what is built so
            // far is carried in, and this antecedent and the rest are
            // discharged there.
            if under.is_declined() && frame + 1 < self.frames.len() {
                let mut remaining = goal_rpn.clone();
                for (later, join) in antecedents[i..].iter().zip(&joins[i..]).rev() {
                    let said = self.rpn(&later.substitute(&binding));
                    if said != where_ {
                        remaining = if *join == Join::Turned {
                            t!(remaining, said, "wb")
                        } else {
                            t!(said, remaining, join_token(*join))
                        };
                    }
                }
                let under_frame = if first {
                    pf!(self.b; remaining, where_, proof, "a1i")
                } else {
                    proof.clone()
                };
                proof = self.carry(under_frame, &remaining, frame);
                frame = self.frames.len() - 1;
                where_ = self.frames[frame].scope.clone();
                let supplied = self.supplied(step, &where_, facts)?;
                known = self.with_cited(step, &where_, &supplied, None);
                self.with_implied(step, &where_, &known)?;
                carried = true;
                first = false;
                (x, y) = if joins[i] == Join::Turned {
                    (rest.clone(), asks_rpn.clone())
                } else {
                    (asks_rpn.clone(), rest.clone())
                };
                under = self.settle(&asks, &where_, &known, 3, None, None)?;
            }
            let under = take!(under);
            proof = pf!(self.b; where_, x, y, under, proof, discharge(joins[i], first));
        }
        if stood_under {
            // An antecedent that is the scope is supplied by standing under
            // it, not by a fact looked up, so it rests on everything the scope
            // says.
            let more = self.scope_origin(&where_, &known)?;
            proof = proof.resting(more);
        }
        Ok(Built(self.carry(proof, &goal_rpn, frame)))
    }

    /// A lemma proved at the value its own hypothesis gives it, and the
    /// claim settled from that, where the theorem's own facts are in scope.
    #[allow(clippy::too_many_arguments)]
    fn at_its_own_value(
        &mut self,
        label: &str,
        sig: &Signature,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        settled: &Binding,
    ) -> Checked<Route<Proof>> {
        let _ = sig;
        let mut reads = self.statement(label);
        while reads.label() == Some("wi") {
            reads = reads.children()[1].clone();
        }
        let said = reads.substitute(settled);
        let proof =
            take!(self.apply_lemma(label, &said, scope, facts, step, false, None)?);
        let known = facts.copy();
        let said = self.rpn(&said);
        self.know(&known, said.clone(), proof.clone());
        let settled = self.settle(goal, scope, &known, 3, None, None)?;
        if !settled.is_declined() {
            return Ok(settled);
        }
        // The value may hold an identity element the claim leaves out: fsum1's
        // one term, the summand at k := 0, has x^(0 − 0) where the claim
        // writes x^0 (`SYNTAX.md`, the literal-instance rule).
        let want = self.rpn(goal);
        Ok(match self.tidied(&proof, &said, &want, scope, facts)? {
            Some(p) => Built(p),
            None => settled,
        })
    }

    /// One hypothesis a lemma states in full rather than asking for.
    pub fn prove_essential(
        &mut self,
        want: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let kids = want.children();
        if want.label() == Some("wceq")
            && kids.len() == 2
            && self.rpn(&kids[0]) == self.rpn(&kids[1])
        {
            // A lemma that names a thing asks for the naming as it stands
            // rather than under the scope.
            return Ok(Built(pf!(self.b; self.rpn(&kids[0]), "eqid")));
        }
        // And the very map spelt over another letter: the same naming,
        // closed.
        if want.label() == Some("wceq") && kids.len() == 2 && !self.is_wff(&kids[0]) {
            if let Some(renamed) = self.class_alpha(&kids[0], &kids[1])? {
                return Ok(Built(renamed));
            }
        }
        if want.label() != Some("wi") {
            return self.settle(want, scope, facts, 3, None, None);
        }
        let (left, right) = (&kids[0], &kids[1]);
        let under = self.rpn(left);
        if under == self.rpn(right) {
            return Ok(Built(pf!(self.b; under, "id")));
        }
        // Two sides alike say one thing whatever is assumed: a renaming whose
        // body does not hold the letter it renames asks this.
        let sides = right.children();
        if sides.len() == 2 && self.rpn(&sides[0]) == self.rpn(&sides[1]) {
            let one = self.rpn(&sides[0]);
            let alike = match right.label() {
                Some("wb") => Some(self.b.ap("biid", &binds! {"ph" => &one}, &[])),
                Some("wceq") => Some(self.b.ap("eqid", &binds! {"A" => &one}, &[])),
                _ => None,
            };
            if let Some(alike) = alike {
                return Ok(Built(pf!(self.b; self.rpn(right), under, alike, "a1i")));
            }
        }
        // A lemma may state its instance rather than ask for it, and wants
        // the body before and after tied together: the walk between them is
        // the same for terms and for formulas.
        if left.label() == Some("wceq")
            && matches!(right.label(), Some("wb") | Some("wceq"))
            && left.children()[0].label() == Some("cv")
        {
            let was = self.rpn(&left.children()[0]);
            let now = self.rpn(&left.children()[1]);
            let held = Facts::new();
            let id = pf!(self.b; under, "id");
            self.know(&held, under.clone(), id);
            let leaf = Leaf::Rows(vec![Row::Assumed {
                was,
                now,
                under: under.clone(),
            }]);
            return self.congruence(
                &right.children()[0],
                &right.children()[1],
                &under,
                &held,
                None,
                &leaf,
            );
        }
        if under == *scope {
            return self.settle(right, scope, facts, 3, None, None);
        }
        if left.label() == Some("wa") && self.rpn(&left.children()[0]) == *scope {
            let extra = self.rpn(&left.children()[1]);
            let weaken = pf!(self.b; scope, extra, "simpl");
            let wider = Facts::new();
            for (k, v) in facts.entries() {
                let carried = pf!(self.b; under, scope, k, weaken, v, "syl");
                self.know(&wider, k, carried);
            }
            let simpr = pf!(self.b; scope, extra, "simpr");
            self.know(&wider, extra.clone(), simpr);
            // A line said of every index may be a requires line of the step,
            // read here and not by the search below.
            let named = wider.copy();
            for (claim, w) in self.written.entries() {
                if let Some(lifted) = self.lifted_to(&claim, &w.proof, &w.at, scope) {
                    if !self.holds(&named, &claim) {
                        let carried =
                            pf!(self.b; under, scope, claim, weaken, lifted, "syl");
                        self.know(&named, claim, carried);
                    }
                }
            }
            if let Some(taken) =
                self.at_the_index(&left.children()[1], right, &under, &named)?
            {
                return Ok(Built(taken));
            }
            // One level deeper than `settle`'s default: what is asked of an
            // index is asked through the range it runs over.
            return self.settle(right, &under, &wider, 4, None, None);
        }
        self.settle(right, &under, &Facts::new(), 3, None, None)
    }

    /// What a lemma asks of each index, from a line saying it of all: that is
    /// the line read at k, once k is in the range, which `rspcv` does. None
    /// where no such line is in hand, which is not a decline: the caller
    /// settles what is asked another way.
    fn at_the_index(
        &mut self,
        member: &Term,
        right: &Term,
        under: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        if member.label() != Some("wcel") || member.children()[0].label() != Some("cv")
        {
            return Ok(None);
        }
        let index = member.children()[0].clone();
        let want = self.rpn(right);
        // Only what the step names, as `settle` is offered only that.
        let facts = self.restable(facts);
        for (said, proof) in facts.entries() {
            let line = self.to_term(&said);
            if line.label() != Some("wral") || line.children()[1].variable().is_none() {
                continue;
            }
            let (body, letter, over) = (
                line.children()[0].clone(),
                line.children()[1].clone(),
                line.children()[2].clone(),
            );
            let mut put = Binding::new();
            put.insert(
                letter.variable_symbol().unwrap(),
                index.children()[0].clone(),
            );
            if self.rpn(&body.substitute(&put)) != want {
                continue;
            }
            let inside = t!(self.rpn(&index), self.rpn(&over), "wcel");
            let Built(there) =
                self.settle(&self.to_term(&inside), under, &facts, 3, None, None)?
            else {
                continue;
            };
            let reads = self.to_term(&t!(
                t!(self.rpn(&letter), "cv", self.rpn(&index), "wceq"),
                t!(self.rpn(&body), want, "wb"),
                "wi"
            ));
            // The line may bind the index's own letter, and then the body at
            // the index is the body: `rsp` reads it there.
            let read = if self.rpn(&body) == want {
                let rsp = self.b.ap(
                    "rsp",
                    &binds! {"ph" => &want, "x" => self.rpn(&letter), "A" => self.rpn(&over)},
                    &[],
                );
                self.b.ap(
                    "com12",
                    &binds! {"ph" => &said, "ps" => &inside, "ch" => &want},
                    &[&rsp],
                )
            } else {
                let Built(tied) = self.prove_essential(&reads, under, &facts)? else {
                    continue;
                };
                self.b.ap(
                    "rspcv",
                    &binds! {"ph" => self.rpn(&body), "ps" => &want, "x" => self.rpn(&letter),
                    "A" => self.rpn(&index), "B" => self.rpn(&over)},
                    &[&tied],
                )
            };
            let carried =
                pf!(self.b; under, inside, t!(said, want, "wi"), there, read, "syl");
            return Ok(Some(pf!(self.b; under, said, want, proof, carried, "mpd")));
        }
        Ok(None)
    }

    /// A claim `P → Q` from a lemma saying `Q ↔ P`, or `P ↔ Q`: the
    /// biconditional is proved at what the claim fixes, and the way the
    /// claim goes is taken.
    #[allow(clippy::too_many_arguments)]
    fn one_direction(
        &mut self,
        label: &str,
        reads: &Term,
        goal: &Term,
        variables: &Vars,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        crossing: bool,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let (left, right) = (reads.children()[0].clone(), reads.children()[1].clone());
        let start = seed.cloned().unwrap_or_default();
        for ((first, then), fold) in [
            ((&left, &right), rules::ONE_WAY.0),
            ((&right, &left), rules::ONE_WAY.1),
        ] {
            let Some(fixed) = fit(
                &Term::apply("wi", vec![first.clone(), then.clone()]),
                goal,
                &start,
                variables,
            ) else {
                continue;
            };
            let said = reads.substitute(&fixed);
            let both = take!(self.apply_lemma(
                label,
                &said,
                scope,
                facts,
                step,
                crossing,
                Some(&fixed)
            )?);
            let (l, r) = (
                self.rpn(&left.substitute(&fixed)),
                self.rpn(&right.substitute(&fixed)),
            );
            return Ok(Built(pf!(self.b; scope, l, r, both, fold)));
        }
        Ok(Route::no(format!("neither way of {label} is the claim")))
    }
}

/// The token a join is written with in a statement.
fn join_token(join: Join) -> &'static str {
    match join {
        Join::Implies => "wi",
        Join::Iff | Join::Turned => "wb",
    }
}

/// How many constructors a pattern fixes: the nodes that are not variables.
fn constructors(pattern: &Term) -> usize {
    if pattern.variable().is_some() {
        return 0;
    }
    1 + pattern.children().iter().map(constructors).sum::<usize>()
}

/// Whether a shape holds the hole numbered `wanted`.
fn holds(tree: &Shape, wanted: usize) -> bool {
    match tree {
        Shape::Hole(i) => *i == wanted,
        Shape::Const(_) => false,
        Shape::App(_, _, kids) => kids.iter().any(|k| holds(k, wanted)),
    }
}

/// A shape spelt with its holes filled.
fn spell(tree: &Shape, holes: &[Rpn]) -> Rpn {
    match tree {
        Shape::Hole(i) => holes[*i].clone(),
        Shape::Const(c) => t!(c),
        Shape::App(label, wrap, kids) => {
            let parts: Vec<Rpn> = kids.iter().map(|k| spell(k, holes)).collect();
            applied(&parts, label, wrap.as_deref())
        }
    }
}

/// The parts one after another, then the constructor, then the operation it
/// wraps where it wraps one.
fn applied(parts: &[Rpn], label: &str, wrap: Option<&str>) -> Rpn {
    let mut out: Vec<Symbol> = Vec::new();
    for part in parts {
        out.extend_from_slice(part.tokens());
    }
    out.push(Symbol::of(label));
    if let Some(w) = wrap {
        out.push(Symbol::of(w));
    }
    Rpn::from(out)
}

/// Whether the tokens of `part` stand together somewhere in `whole`.
fn holds_run(whole: &Rpn, part: &Rpn) -> bool {
    part.is_empty()
        || whole
            .tokens()
            .windows(part.len())
            .any(|w| w == part.tokens())
}

/// The same equation with its sides the other way round; None for anything
/// that is not an equation, whose sides are not interchangeable.
fn turned_equation(term: &Term) -> Option<Term> {
    if term.label() != Some("wceq") || term.children().len() != 2 {
        return None;
    }
    Some(Term::apply(
        "wceq",
        vec![term.children()[1].clone(), term.children()[0].clone()],
    ))
}

/// Whether `piece` says what a function the binding fixes maps between: `F
/// : A --> B`, F bound.
fn function_fixed(piece: &Term, binding: &Binding) -> bool {
    if piece.variable().is_some()
        || !matches!(
            piece.label(),
            Some("wf") | Some("wf1") | Some("wfo") | Some("wf1o")
        )
        || piece.children().len() != 3
    {
        return false;
    }
    piece.children()[2]
        .variable()
        .is_some_and(|v| binding.contains_key(v))
}

/// The things a lemma's antecedent asks, one conjunct at a time.
pub fn conjuncts_of(slot: &Term) -> Vec<Term> {
    let mut pieces = Vec::new();
    let mut parts = std::collections::VecDeque::from([slot.clone()]);
    while let Some(part) = parts.pop_front() {
        if matches!(part.label(), Some("wa") | Some("w3a")) {
            for c in part.children().iter().rev() {
                parts.push_front(c.clone());
            }
        } else {
            pieces.push(part);
        }
    }
    pieces
}

/// The classes an antecedent asks about and nothing decides: set.mm leaves
/// such a class free so that a citation may name any class holding the
/// thing, and what it is asking is that the thing be a set.
pub fn sethood(slot: &Term, binding: &Binding) -> Vec<Symbol> {
    let mut out = Vec::new();
    let mut rest = vec![slot.clone()];
    while let Some(node) = rest.pop() {
        if matches!(node.label(), Some("wa") | Some("w3a")) {
            rest.extend(node.children().iter().cloned());
            continue;
        }
        if matches!(node.label(), Some("wral") | Some("wal")) {
            rest.push(node.children()[0].clone());
            continue;
        }
        let Some(at) = node.label().and_then(|l| lookup(rules::HELD_IN, l)) else {
            continue;
        };
        if let Some(name) = node.children()[at].variable_symbol() {
            if !binding.contains_key(&name) {
                out.push(name);
            }
        }
    }
    out
}

/// A pattern whose binders stand for whatever class fills them: a binder is
/// written `cv` over a setvar, and a claim may answer it with a term.
pub fn as_class(node: &Term, marks: &BTreeSet<String>) -> Term {
    if node.variable().is_some() {
        return node.clone();
    }
    if node.label() == Some("cv")
        && node.children()[0]
            .variable()
            .is_some_and(|v| marks.contains(v))
    {
        return node.children()[0].clone();
    }
    Term::apply(
        node.label().unwrap_or(""),
        node.children().iter().map(|c| as_class(c, marks)).collect(),
    )
}

/// Every part of a term, the whole first.
fn subterms(term: &Term) -> Vec<Term> {
    let mut out = Vec::new();
    let mut rest = std::collections::VecDeque::from([term.clone()]);
    while let Some(node) = rest.pop_front() {
        if node.variable().is_none() {
            rest.extend(node.children().iter().cloned());
        }
        out.push(node);
    }
    out
}

/// `fit` where an equation of the pattern may meet one of the term either
/// way round: what the lemma says in other words is the instance fitted,
/// and its caller carries that to the claim by `Matcher::same`, which reads
/// an equation either way round as the page does. Every other fit is the
/// kernel's, which a proof takes symbol for symbol.
fn fit_either_way(
    pattern: &Term,
    ground: &Term,
    seed: &Binding,
    variables: &Vars,
) -> Option<Binding> {
    let first = ToFit {
        pattern: pattern.clone(),
        ground: ground.clone(),
    };
    either_way(vec![first], seed.clone(), variables)
}

/// A part of a pattern and the part of the term it is fitted to.
#[derive(Clone)]
struct ToFit {
    pattern: Term,
    ground: Term,
}

/// The parts still to fit, the last fitted now: a variable bound or
/// checked against what it is bound to, an equation tried with its sides
/// as written and then turned, any other node part by part. A choice that
/// a later part does not fit is undone.
fn either_way(
    mut left: Vec<ToFit>,
    mut binding: Binding,
    variables: &Vars,
) -> Option<Binding> {
    let Some(ToFit { pattern, ground }) = left.pop() else {
        return Some(binding);
    };
    if let Some(v) = pattern.variable().filter(|v| variables.contains(*v)) {
        match binding.get(v) {
            Some(seen) if !crate::mm::kernel::same(seen, &ground) => return None,
            Some(_) => {}
            None => {
                binding.insert(Symbol::of(v), ground.clone());
            }
        }
        return either_way(left, binding, variables);
    }
    if pattern.variable().is_some() || ground.variable().is_some() {
        if pattern.variable() != ground.variable() {
            return None;
        }
        return either_way(left, binding, variables);
    }
    if pattern.label() != ground.label()
        || pattern.children().len() != ground.children().len()
    {
        return None;
    }
    let paired = |turn: bool| {
        let mut more = left.clone();
        let theirs: Vec<Term> = if turn {
            ground.children().iter().rev().cloned().collect()
        } else {
            ground.children().to_vec()
        };
        more.extend(
            pattern
                .children()
                .iter()
                .cloned()
                .zip(theirs)
                .map(|(pattern, ground)| ToFit { pattern, ground })
                .rev(),
        );
        more
    };
    let equation = pattern.label() == Some("wceq") && pattern.children().len() == 2;
    either_way(paired(false), binding.clone(), variables).or_else(|| {
        equation
            .then(|| either_way(paired(true), binding, variables))
            .flatten()
    })
}

/// The lemma carrying a class's equality up through one place of a term.
fn class_lift(label: &str, place: usize) -> Option<&'static str> {
    rules::CLASS_LIFT
        .iter()
        .find(|(l, p, _)| *l == label && *p == place)
        .map(|(_, _, lemma)| *lemma)
}
