//! Reading the rule tables: a fact the page leaves out, built by table.
//!
//! The rule tables are the fourth of the elaborator's six parts
//! (`ELABORATION.md`, "How the elaborator is built"), and `rules` holds them
//! as data. This is the code that reads them. Given what is wanted — an
//! equation lifted through a term, a term's membership of a number system, a
//! numeral's, a term's sethood — it looks up the lemma the table names for
//! that shape and builds the proof from it. Nothing here searches: what a
//! table has no entry for is declined, and left to what is tried after.

use std::collections::BTreeSet;

use indexmap::IndexMap;
use num_traits::{ToPrimitive, Zero};

use super::field::{self, Value};
use super::linear;
use super::matcher::ChainLink;
use super::provenance::{from_requires, may_rest_on, rests_on_only, MEMBERSHIP};
use super::state::{fit, names_of, Binding, Elaborator};
use super::{Facts, Lines, Written};
use crate::binds;
use crate::citing::{part_said_otherwise, OnceReason, Shape};
use crate::corpus::Step;
use crate::formula::symbol::Symbol;
use crate::formula::Node;
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::mm::Rpn;
use crate::outcome::{Built, Checked, Declined, Route};
use crate::rules::{self, lookup, numeral_label, System};
use crate::{pf, t, take};

/// One kind of difference the walk in `congruence` closes where two terms
/// are both known and differ in places.
#[derive(Clone, Debug)]
pub enum Row {
    /// An equation in hand says the two are equal.
    Held,
    /// The equation a step cites, which rewrote the place: the line says
    /// `was = now`, or `now = was` where `flip`.
    Cited {
        was: Rpn,
        now: Rpn,
        said: Rpn,
        flip: bool,
    },
    /// The equation a lemma's own hypothesis assumes.
    Assumed { was: Rpn, now: Rpn, under: Rpn },
    /// The two have one standard form.
    Standard,
    /// A term carried to its standard form.
    Toward,
    /// The two are one once an identity element is dropped where it stands,
    /// x + 0 as x: a literal instance and how the page writes it
    /// (`SYNTAX.md`). Nothing else is rewritten.
    Identity,
    /// A term and the same term with its identity elements dropped, the
    /// parts of one carried to the other's (`Elaborator::bared`).
    Bare,
}

/// What the walk asks where two terms differ.
#[derive(Clone, Debug)]
pub enum Leaf {
    /// Each row in turn; the first that closes the difference gives the
    /// proof there, and where none does the walk goes a level in.
    Rows(Vec<Row>),
    /// A piece of numerals alone that changed, proved where it stands as a
    /// closed fact: a link of a calculation naming `arithmetic`.
    Arithmetic { what: String, step: Box<Step> },
}

/// A chain of lemmas carrying a membership to what it also says: each
/// lemma, what it was bound to, and what it reaches.
#[derive(Clone)]
pub struct Link {
    pub lemma: String,
    pub binding: Option<Binding>,
    pub reached: Term,
    /// What the lemma asks besides the fact it carries: that a class is a
    /// set, as `gsspw` asks of the set a part is a part of (`made_a_set`).
    pub sets: Vec<Term>,
}

/// How a caller proves one part of a compound in a number system.
pub type Parts<'p, 'a> =
    dyn FnMut(&mut Elaborator<'a>, &Rpn, &Rpn) -> Checked<Route<Proof>> + 'p;
/// How a caller proves a divisor is not zero.
pub type Nonzero<'p, 'a> =
    dyn FnMut(&mut Elaborator<'a>, &Rpn) -> Checked<Route<Proof>> + 'p;

/// The build's kernel terms as the said-once walk reads them
/// (`citing::OnceAsk`): letters by the lines introducing them, a divisor
/// not zero by what the step wrote (`divisor_written`), and a part stated
/// by a line the step names or a sum said once. A defect met on the way is
/// kept, and stops the step once the walk is done.
struct BuildOnce<'m, 'a> {
    me: &'m mut Elaborator<'a>,
    scope: &'m Rpn,
    facts: &'m Facts,
    problem: Option<crate::outcome::Problem>,
}

impl BuildOnce<'_, '_> {
    /// What `checked` holds, or None, keeping the first defect.
    fn keep<T>(&mut self, checked: Checked<T>) -> Option<T> {
        match checked {
            Ok(value) => Some(value),
            Err(problem) => {
                if self.problem.is_none() {
                    self.problem = Some(problem);
                }
                None
            }
        }
    }
}

impl crate::citing::OnceAsk for BuildOnce<'_, '_> {
    type T = Term;

    fn shape<'t>(&self, term: &'t Term) -> Shape<'t, Term> {
        if let Built(crate::methods::field::Value::Exact(v)) =
            crate::methods::field::closed_value(term)
        {
            return Shape::Value(v);
        }
        if term.variable().is_some()
            || self.me.introduced_in(&self.me.rpn(term)).is_some()
        {
            return Shape::Letter;
        }
        let kids = term.children();
        match (term.label(), kids.len()) {
            (Some("cneg"), 1) => Shape::Negated(&kids[0]),
            (Some("co"), 3) => {
                match self.me.rpn(&kids[2]).alone().unwrap_or_default() {
                    "caddc" => Shape::Operation("caddc", &kids[0], &kids[1]),
                    "cmin" => Shape::Operation("cmin", &kids[0], &kids[1]),
                    "cmul" => Shape::Operation("cmul", &kids[0], &kids[1]),
                    "cdiv" => Shape::Operation("cdiv", &kids[0], &kids[1]),
                    "cexp" => Shape::Power(&kids[0], &kids[1]),
                    _ => Shape::Other,
                }
            }
            _ => Shape::Other,
        }
    }

    fn letter(&mut self, term: &Term) -> Option<System> {
        let (_, set) = self.me.introduced_in(&self.me.rpn(term))?;
        let system = match self.me.range_system(&set) {
            Some((system, _)) => system,
            None => set.alone()?,
        };
        System::of_label(system)
    }

    fn nonzero(&mut self, divisor: &Term) -> bool {
        let said = self.me.rpn(divisor);
        let written = self.me.divisor_written(&said, self.scope, self.facts);
        self.keep(written)
            .is_some_and(|found| matches!(found, Built(_)))
    }

    fn said(&mut self, term: &Term, system: System) -> Option<OnceReason> {
        let said = self.me.rpn(term);
        let stated =
            self.me
                .stated_within(&said, &t!(system.label()), self.scope, self.facts);
        if self.keep(stated).flatten().is_some() {
            return Some(OnceReason::Stated);
        }
        self.me.said_sums.contains(&said).then_some(OnceReason::Sum)
    }
}

impl<'a> Elaborator<'a> {
    /// Run `f` with what the step's requires lines made offered to the
    /// membership lookup and the one-lemma bridge, which read these before
    /// any search, and which a search never does. `keep` lays these over
    /// what is already offered rather than in its place.
    pub fn writing<T>(
        &mut self,
        scope: &Rpn,
        known: &Facts,
        keep: bool,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let kept = self.written.clone();
        if !keep {
            self.written = Written::new();
        }
        for (k, v) in known.entries() {
            if from_requires(&v) {
                self.write(k, scope.clone(), v);
            }
        }
        let out = f(self);
        self.written = kept;
        out
    }

    /// `said ∈ system` searched for, at the depth the caller gives.
    pub fn within(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Route<Proof>> {
        let wanted = self.to_term(&t!(said, system, "wcel"));
        self.settle(&wanted, scope, facts, depth, None, None)
    }

    /// ( scope -> given = want ), or `<->` for statements, where the walk
    /// would go under a binder whose letter the scope spells: the lemma that
    /// carries a change under a binder keeps its letter apart from the
    /// scope. Each side's letter at `place` is moved to one nothing holds,
    /// closed (`renaming` for a statement, `class_alpha` for a class), the
    /// two are walked there, and the result is moved back.
    #[allow(clippy::too_many_arguments)]
    fn over_spare_letter(
        &mut self,
        given: &Term,
        want: &Term,
        place: usize,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        leaf: &Leaf,
    ) -> Checked<Route<Proof>> {
        // Looked at, not taken: the letter stands inside this one statement
        // and nowhere else.
        let Some(fresh) = self.unheld(&[&self.to_term(scope), given, want]) else {
            return Ok(Route::no("no letter left to walk under this binder by"));
        };
        let moved_to = |term: &Term| {
            let mut put = Binding::new();
            put.insert(
                Symbol::of(term.children()[place].variable().unwrap_or("")),
                fresh.clone(),
            );
            term.substitute(&put)
        };
        let (moved, moved_want) = (moved_to(given), moved_to(want));
        let walked =
            take!(self.congruence(&moved, &moved_want, scope, facts, step, leaf)?);
        let wff = self.is_wff(given);
        let (there, back) = if wff {
            (
                self.renaming(given, &moved)?,
                self.renaming(&moved_want, want)?,
            )
        } else {
            (
                self.class_alpha(given, &moved)?,
                self.class_alpha(&moved_want, want)?,
            )
        };
        let (Some(there), Some(back)) = (there, back) else {
            return Ok(Route::no("the binder is not renamed apart from the scope"));
        };
        let join = if wff { "wb" } else { "wceq" };
        let (a, b) = (self.rpn(given), self.rpn(&moved));
        let (c, d) = (self.rpn(&moved_want), self.rpn(want));
        let first = pf!(self.b; t!(a, b, join), scope, there, "a1i");
        let last = pf!(self.b; t!(c, d, join), scope, back, "a1i");
        Ok(Built(self.chained(
            scope,
            &[
                ChainLink {
                    from: given.clone(),
                    to: moved.clone(),
                    proof: first,
                },
                ChainLink {
                    from: moved,
                    to: moved_want.clone(),
                    proof: walked,
                },
                ChainLink {
                    from: moved_want,
                    to: want.clone(),
                    proof: last,
                },
            ],
        )))
    }

    /// Carry one change up to the whole term it sits in.
    ///
    /// Two terms that differ in one place are walked in step, and the lemma
    /// that lifts each level is the one the tree names. What counts as the
    /// change, and what proves it there, is the caller's `leaf`. What it
    /// refuses is a route declining and not a defect, however it was
    /// reached.
    pub fn congruence(
        &mut self,
        given: &Term,
        want: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        leaf: &Leaf,
    ) -> Checked<Route<Proof>> {
        if let Some(found) = self.leaf(leaf, given, want, scope, facts)? {
            return Ok(found);
        }
        if given.label() != want.label()
            || given.children().len() != want.children().len()
        {
            return Ok(self.no(
                "{} and {} differ by more than the change being carried",
                &[&self.rpn(given), &self.rpn(want)],
            ));
        }
        let label = given.label().unwrap_or("").to_string();
        let g: Vec<Rpn> = given.children().iter().map(|c| self.rpn(c)).collect();
        let w: Vec<Rpn> = want.children().iter().map(|c| self.rpn(c)).collect();
        // Only the body is carried under the binder here; a domain that
        // changes with the body kept is the branch for domains below.
        if label == "wrex" && w[1..] == g[1..] {
            let kids = given.children();
            let (body, name, runs) = (&kids[0], g[1].clone(), g[2].clone());
            // `rexbidva` keeps its letter apart from the scope it carries.
            if name.alone().is_some_and(|n| scope.has(n)) {
                return self
                    .over_spare_letter(given, want, 1, scope, facts, step, leaf);
            }
            let member = t!(name, "cv", runs, "wcel");
            let other = want.children()[0].clone();
            let made = self.frames_kept(|me| {
                let (inner, lifted) = me.widen(scope, facts, &member, None);
                me.congruence(body, &other, &inner, &lifted, step, leaf)
            })?;
            let made = take!(made);
            return Ok(Built(
                pf!(self.b; scope, self.rpn(body), self.rpn(&other), name, runs, made, "rexbidva"),
            ));
        }
        // A sum's summand, or a product's factor, is carried the same way,
        // under its index's range.
        let indexed = lookup(rules::INDEXED_BODY, &label);
        if let Some((body_lemma, _)) =
            indexed.filter(|_| g[0] == w[0] && g[2] == w[2] && g[1] != w[1])
        {
            let kids = given.children();
            let (runs, body, name) = (g[0].clone(), &kids[1], g[2].clone());
            if name.alone().is_some_and(|n| scope.has(n)) {
                return self
                    .over_spare_letter(given, want, 2, scope, facts, step, leaf);
            }
            let member = t!(name, "cv", runs, "wcel");
            let other = want.children()[1].clone();
            let made = self.frames_kept(|me| {
                let (inner, lifted) = me.widen(scope, facts, &member, None);
                me.congruence(body, &other, &inner, &lifted, step, leaf)
            })?;
            let made = take!(made);
            return Ok(Built(self.b.ap(
                body_lemma,
                &binds! {"ph" => scope, "A" => &runs, "B" => self.rpn(body), "C" => self.rpn(&other), "k" => &name},
                &[&made],
            )));
        }
        // A sum whose range and summand both change, as Σ(k = 0 to m) C(m, k)
        // read at m := n: the range carried as it stands, and the summand
        // under the index's membership of the range it had (`sumeq12dv`).
        if let Some((_, both_lemma)) =
            indexed.filter(|_| g[2] == w[2] && g[0] != w[0] && g[1] != w[1])
        {
            let kids = given.children();
            let (runs, body, name) = (g[0].clone(), &kids[1], g[2].clone());
            if name.alone().is_some_and(|n| scope.has(n)) {
                return self
                    .over_spare_letter(given, want, 2, scope, facts, step, leaf);
            }
            let moved = take!(self.congruence(
                &kids[0],
                &want.children()[0],
                scope,
                facts,
                step,
                leaf
            )?);
            let member = t!(name, "cv", runs, "wcel");
            let other = want.children()[1].clone();
            let made = self.frames_kept(|me| {
                let (inner, lifted) = me.widen(scope, facts, &member, None);
                me.congruence(body, &other, &inner, &lifted, step, leaf)
            })?;
            let made = take!(made);
            return Ok(Built(self.b.ap(
                both_lemma,
                &binds! {"ph" => scope, "A" => &runs, "B" => &w[0], "C" => self.rpn(body),
                "D" => self.rpn(&other), "k" => &name},
                &[&moved, &made],
            )));
        }
        // A set-builder's condition is carried the same way, under its
        // letter's membership of the domain.
        if label == "crab" && g[1] == w[1] && g[2] == w[2] && g[0] != w[0] {
            let kids = given.children();
            let (body, name, runs) = (&kids[0], g[1].clone(), g[2].clone());
            if name.alone().is_some_and(|n| scope.has(n)) {
                // The scope holds D's own equation, which binds this letter,
                // so the condition is carried over a spare the scope does not
                // spell and the builder renamed to it and back.
                return self
                    .over_spare_letter(given, want, 1, scope, facts, step, leaf);
            }
            let member = t!(name, "cv", runs, "wcel");
            let other = want.children()[0].clone();
            let made = self.frames_kept(|me| {
                let (inner, lifted) = me.widen(scope, facts, &member, None);
                me.congruence(body, &other, &inner, &lifted, step, leaf)
            })?;
            let made = take!(made);
            return Ok(Built(self.b.ap(
                "rabbidva",
                &binds! {"ph" => scope, "ps" => self.rpn(body), "ch" => self.rpn(&other), "x" => &name, "A" => &runs},
                &[&made],
            )));
        }
        // A "for all", a "there is" or a set-builder whose domain changes,
        // its letter and its body kept.
        if (label == "wral" || label == "wrex" || label == "crab")
            && g[0] == w[0]
            && g[1] == w[1]
            && g[2] != w[2]
        {
            let kids = given.children().to_vec();
            let moved = take!(self.congruence(
                &kids[2],
                &want.children()[2],
                scope,
                facts,
                step,
                leaf
            )?);
            let lemma =
                rules::congruence(&label, &[2]).expect("a congruence for a domain");
            return Ok(Built(self.b.ap(
                lemma,
                &binds! {"ph" => scope, "ps" => &g[0], "x" => &g[1], "A" => &g[2], "B" => &w[2]},
                &[&moved],
            )));
        }
        // And its domain and body together.
        if (label == "wral" || label == "wrex")
            && g[1] == w[1]
            && g[0] != w[0]
            && g[2] != w[2]
        {
            let kids = given.children().to_vec();
            if g[1].alone().is_some_and(|n| scope.has(n)) {
                return self
                    .over_spare_letter(given, want, 1, scope, facts, step, leaf);
            }
            let over = take!(self.congruence(
                &kids[2],
                &want.children()[2],
                scope,
                facts,
                step,
                leaf
            )?);
            let said = take!(self.congruence(
                &kids[0],
                &want.children()[0],
                scope,
                facts,
                step,
                leaf
            )?);
            let lemma = rules::congruence(&label, &[0, 2])
                .expect("a congruence for a domain and a body");
            return Ok(Built(self.b.ap(
                lemma,
                &binds! {"ph" => scope, "ps" => &g[0], "ch" => &w[0], "x" => &g[1], "A" => &g[2], "B" => &w[2]},
                &[&over, &said],
            )));
        }
        // A map whose domain changes, its letter and its rule kept.
        if (label == "cmpt" || label == "ciun")
            && g[0] == w[0]
            && g[2] == w[2]
            && g[1] != w[1]
        {
            let kids = given.children().to_vec();
            let moved = take!(self.congruence(
                &kids[1],
                &want.children()[1],
                scope,
                facts,
                step,
                leaf
            )?);
            if let Some(wider) = self.domain_holding(given, want, scope, &moved) {
                return Ok(Built(wider));
            }
            let lemma = rules::congruence(&label, &[1])
                .expect("a congruence for a map's domain");
            return Ok(Built(self.b.ap(
                lemma,
                &binds! {"ph" => scope, "x" => &g[0], "A" => &g[1], "B" => &w[1], "C" => &g[2]},
                &[&moved],
            )));
        }
        // The operation or relation a term wraps stays as it is; a function
        // applied changes where a lemma says it may, as q(x) is r(x) when q
        // is r (`fveq1d`).
        let wrapped = rules::WRAPS.contains(&label.as_str())
            && (g[g.len() - 1] == w[w.len() - 1]
                || rules::congruence(&label, &[g.len() - 1]).is_none());
        let n = if wrapped { g.len() - 1 } else { g.len() };
        let kids: Vec<Term> = given.children()[..n].to_vec();
        let wants: Vec<Term> = want.children()[..n].to_vec();
        let (spelt, other) = (&g[..n], &w[..n]);
        let slots: Vec<usize> = (0..n).filter(|&i| spelt[i] != other[i]).collect();
        if slots.is_empty() {
            return Ok(Route::no("nothing changed under this term"));
        }
        // A rule by cases changes in its condition and its two values at
        // once, and `ifbieq12d` takes both old values before the new ones,
        // so it is given its parts by name; a part that stays the same is
        // carried by `biidd` or `eqidd`.
        if label == "cif" {
            let mut parts = Vec::new();
            for i in 0..3 {
                let one = if slots.contains(&i) {
                    take!(
                        self.congruence(&kids[i], &wants[i], scope, facts, step, leaf)?
                    )
                } else if i == 0 {
                    self.b
                        .ap("biidd", &binds! {"ph" => scope, "ps" => &spelt[0]}, &[])
                } else {
                    self.b
                        .ap("eqidd", &binds! {"ph" => scope, "A" => &spelt[i]}, &[])
                };
                parts.push(one);
            }
            return Ok(Built(self.b.ap(
                "ifbieq12d",
                &binds! {"ph" => scope, "ps" => &spelt[0], "ch" => &other[0], "A" => &spelt[1],
                "B" => &spelt[2], "C" => &other[1], "D" => &other[2]},
                &[&parts[0], &parts[1], &parts[2]],
            )));
        }
        // A function spelt as its define's name against the map it names:
        // `feq1d`, and `f1oeq1d` for one-to-one and onto, both deduction
        // forms (`rules::CONGRUENCE`), and for one-to-one or onto alone the
        // closed `f1eq1` or `foeq1` after the equation by `syl`
        // (`rules::FUNCTION_LAWS`). A function's type whose domain or codomain
        // changes, the function too or not: `feq123d` and `f1eq123d` take
        // the three equations, a part that stays the same carried by
        // `eqidd`.
        if matches!(label.as_str(), "wf" | "wf1") && slots != [2] {
            let mut equal = Vec::new();
            for i in [2, 0, 1] {
                let one = if slots.contains(&i) {
                    take!(
                        self.congruence(&kids[i], &wants[i], scope, facts, step, leaf)?
                    )
                } else {
                    self.b
                        .ap("eqidd", &binds! {"ph" => scope, "A" => &spelt[i]}, &[])
                };
                equal.push(one);
            }
            let lemma = if label == "wf" { "feq123d" } else { "f1eq123d" };
            return Ok(Built(self.b.ap(
                lemma,
                &binds! {"ph" => scope, "A" => &spelt[0], "B" => &other[0],
                "C" => &spelt[1], "D" => &other[1], "F" => &spelt[2], "G" => &other[2]},
                &[&equal[0], &equal[1], &equal[2]],
            )));
        }
        let typed = matches!(label.as_str(), "wf" | "wf1" | "wfo" | "wf1o");
        let deduced = rules::congruence(&label, &slots).filter(|_| typed);
        let closed = rules::function_law(&label, &slots);
        if deduced.is_some() || closed.is_some() {
            let moved =
                take!(self.congruence(&kids[2], &wants[2], scope, facts, step, leaf)?);
            let parts = binds! {"A" => &spelt[0], "B" => &spelt[1], "F" => &spelt[2], "G" => &other[2]};
            if let Some(lemma) = deduced {
                let mut all = parts.clone();
                all.insert("ph".to_string(), scope.clone());
                return Ok(Built(self.b.ap(lemma, &all, &[&moved])));
            }
            let law = self.b.ap(closed.expect("one of the two"), &parts, &[]);
            return Ok(Built(self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => t!(spelt[2], other[2], "wceq"),
                "ch" => t!(self.rpn(given), self.rpn(want), "wb")},
                &[&moved, &law],
            )));
        }
        // What lifts the change is the lemma for this constructor and these
        // places, and the operation it lifts under must be the same one.
        let lifting = rules::congruence(&label, &slots);
        let Some(lifting) =
            lifting.filter(|_| !(wrapped && g[g.len() - 1] != w[w.len() - 1]))
        else {
            return Ok(Route::no("no lemma carries this change up"));
        };
        // The lemmas that carry a change under a binder keep its letter
        // apart from the scope.
        if lookup(rules::BOUND, &label).is_some()
            && g.len() >= 2
            && g[1].alone().is_some_and(|n| scope.has(n))
        {
            return self.over_spare_letter(given, want, 1, scope, facts, step, leaf);
        }
        let mut under = Vec::new();
        for &i in &slots {
            under.push(self.congruence(&kids[i], &wants[i], scope, facts, step, leaf)?);
        }
        let mut proofs = Vec::new();
        for one in under {
            match one {
                Built(p) => proofs.push(p),
                Declined(d) => {
                    // The body of a "for all" may change only for a member
                    // of its domain, so it is carried again under that
                    // membership, as a "there is" is.
                    if label == "wral" && slots == [0] {
                        return self
                            .under_member(given, want, scope, facts, step, leaf, d);
                    }
                    return Ok(Declined(d));
                }
            }
        }
        // The lemma's letters are read off its conclusion fitted to what it
        // lifts, ( scope -> given = want ), or <-> for a statement, so the
        // order set.mm declares them in does not matter: an integral's
        // letter x is declared before every class, a sum's k after.
        let is_class = given.label().is_some_and(|l| self.typecode(l) == "class");
        let lifted = if is_class {
            t!(self.rpn(given), self.rpn(want), "wceq")
        } else {
            t!(self.rpn(given), self.rpn(want), "wb")
        };
        let target = self.to_term(&t!(scope, lifted, "wi"));
        let says = self.statement(lifting);
        let variables = names_of(&says);
        let Some(binding) = fit(&says, &target, &Binding::new(), &variables) else {
            return Ok(Route::no(
                "the lemma that carries this change up says otherwise",
            ));
        };
        let proofs: Vec<&Proof> = proofs.iter().collect();
        Ok(Built(self.b.ap(lifting, &self.spelt(&binding), &proofs)))
    }

    /// ( scope -> given = want ), a map whose domain changes to one spelling
    /// its letter, by `mpteq12dv` with its rule kept; None where neither
    /// domain spells the letter.
    pub fn domain_holding(
        &self,
        given: &Term,
        want: &Term,
        scope: &Rpn,
        moved: &Proof,
    ) -> Option<Proof> {
        if given.label() != Some("cmpt") {
            return None;
        }
        let kids: Vec<Rpn> = given.children().iter().map(|c| self.rpn(c)).collect();
        let (letter, over, rule) = (&kids[0], &kids[1], &kids[2]);
        let new = self.rpn(&want.children()[1]);
        let spells = |t: &Rpn| letter.alone().is_some_and(|l| t.has(l));
        if !spells(over) && !spells(&new) {
            return None;
        }
        let kept = self
            .b
            .ap("eqidd", &binds! {"ph" => scope, "A" => rule}, &[]);
        Some(self.b.ap(
            "mpteq12dv",
            &binds! {"ph" => scope, "x" => letter, "A" => over, "B" => rule, "C" => &new, "D" => rule},
            &[moved, &kept],
        ))
    }

    /// ( scope -> ( A. x e. A ph <-> A. x e. A ps ) ), the body carried with
    /// x ∈ A in scope (`ralbidva`); `why` where that fails too.
    #[allow(clippy::too_many_arguments)]
    fn under_member(
        &mut self,
        given: &Term,
        want: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        leaf: &Leaf,
        why: crate::outcome::Decline,
    ) -> Checked<Route<Proof>> {
        let kids = given.children().to_vec();
        let (body, variable, over) = (&kids[0], &kids[1], &kids[2]);
        let (name, runs) = (self.rpn(variable), self.rpn(over));
        if name.alone().is_some_and(|n| scope.has(n)) {
            // `ralbidva` keeps its letter apart from the scope, so where the
            // scope spells it the two are carried over a spare and renamed
            // back.
            let Some(fresh) = self.unheld(&[&self.to_term(scope), given, want]) else {
                return Ok(Declined(why));
            };
            let mut put = Binding::new();
            put.insert(Symbol::of(variable.variable().unwrap_or("")), fresh);
            let moved = given.substitute(&put);
            let moved_want = want.substitute(&put);
            let walked = self.under_member(
                &moved,
                &moved_want,
                scope,
                facts,
                step,
                leaf,
                why.clone(),
            )?;
            let there = self.renamed_apart(given, &moved)?;
            let back = self.renamed_apart(&moved_want, want)?;
            let (Built(walked), Some(there), Some(back)) = (walked, there, back) else {
                return Ok(Declined(why));
            };
            let (a, b) = (self.rpn(given), self.rpn(&moved));
            let (c, d) = (self.rpn(&moved_want), self.rpn(want));
            let first = pf!(self.b; t!(a, b, "wb"), scope, there, "a1i");
            let last = pf!(self.b; t!(c, d, "wb"), scope, back, "a1i");
            let middle = self.b.ap(
                "bitrd",
                &binds! {"ph" => scope, "ps" => &a, "ch" => &b, "th" => &c},
                &[&first, &walked],
            );
            return Ok(Built(self.b.ap(
                "bitrd",
                &binds! {"ph" => scope, "ps" => &a, "ch" => &c, "th" => &d},
                &[&middle, &last],
            )));
        }
        let member = t!(name, "cv", runs, "wcel");
        let other = want.children()[0].clone();
        let made = self.frames_kept(|me| {
            let (inner, lifted) = me.widen(scope, facts, &member, None);
            me.congruence(body, &other, &inner, &lifted, step, leaf)
        })?;
        let Built(made) = made else {
            return Ok(Declined(why));
        };
        Ok(Built(
            pf!(self.b; scope, self.rpn(body), self.rpn(&other), name, runs, made, "ralbidva"),
        ))
    }

    /// ( scope -> t e. S ), for a term built from numerals alone: a digit
    /// set.mm names in the system is its label, and anything else built only
    /// from numerals is settled from the declared closure lemmas, which is
    /// working it out and not searching.
    pub fn numeral_within(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let named = self.digit_within(goal, scope, facts)?;
        if !named.is_declined() {
            return Ok(named);
        }
        if goal.children()[1].label() == Some("cq") {
            let rational = self.rational_within(&goal.children()[0], scope, facts)?;
            if !rational.is_declined() {
                return Ok(rational);
            }
        }
        let said = self.rpn(&goal.children()[0]);
        if said.tokens().iter().any(|t| !rules::numeric(t.as_str())) {
            // A closed term that binds a letter of its own, a product over
            // a range of numerals, is worked to its numeral, and the
            // membership is the numeral's, carried back by `eqeltrrd`.
            let labels = self.b.flabel.clone();
            let Some((value, is)) =
                super::numerals::worked(&self.b, &goal.children()[0], &labels)
            else {
                return Ok(named);
            };
            let spelt = super::numerals::spell(value);
            let system = self.rpn(&goal.children()[1]);
            let at = self.to_term(&t!(&spelt, &system, "wcel"));
            let held = take!(self.numeral_within(&at, scope, facts)?);
            let back =
                self.b
                    .ap("eqcomi", &binds! {"A" => &said, "B" => &spelt}, &[&is]);
            let back = pf!(self.b; t!(&spelt, &said, "wceq"), scope, back, "a1i");
            return Ok(Built(self.b.ap(
                "eqeltrrd",
                &binds! {"ph" => scope, "A" => &spelt, "B" => &said, "C" => &system},
                &[&back, &held],
            )));
        }
        // One level deeper than `settle`'s default. Nothing in it is a
        // proof's own, so what it comes to is the same wherever it is asked
        // under this scope, and is worked out once — only where it rests on
        // nothing on the page.
        let want = self.rpn(goal);
        let key = (want.clone(), scope.clone());
        if let Some(found) = self.numbers.get(&key) {
            return Ok(found.clone());
        }
        // A membership asked again while it is being worked out, as the
        // search for 1/2 ∈ ℤ asked 1/2 ∈ ℤ of a lemma's hypothesis, would
        // start the search again at full depth, and never stop.
        if self.numbering.contains(&want) {
            return Ok(Route::no("asked again while it is being worked out"));
        }
        self.numbering.insert(want.clone());
        let found = (|| -> Checked<Route<Proof>> {
            let found = self.settle(goal, scope, &Facts::new(), 4, None, None)?;
            if !found.is_declined() {
                return Ok(found);
            }
            let found = self.by_value(goal, scope)?;
            if !found.is_declined() {
                return Ok(found);
            }
            self.within_by_value(goal, scope, facts)
        })();
        self.numbering.shift_remove(&want);
        let found = found?;
        let keep = match &found {
            Declined(_) => true,
            Built(p) => p.origin.is_empty(),
        };
        if keep {
            self.numbers.insert(key, found.clone());
        }
        Ok(found)
    }

    /// ( scope -> x e. S ) for a closed x, through its value: a value
    /// written plainly, a negation or a fraction, is in ℝ and ℂ by way of ℚ
    /// (`qre`, `qcn`); any other closed term is in S as its value is
    /// (`closed_valued`), carried back by `eleq1d`.
    fn within_by_value(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let x = &goal.children()[0];
        let (sx, system) = (self.rpn(x), self.rpn(&goal.children()[1]));
        let (_, canon, is) = take!(self.closed_valued(x, scope, facts)?);
        if canon != sx {
            let at = self.to_term(&t!(&canon, &system, "wcel"));
            let held = take!(self.numeral_within(&at, scope, facts)?);
            let iff = self.b.ap(
                "eleq1d",
                &binds! {"ph" => scope, "A" => &sx, "B" => &canon, "C" => &system},
                &[&is],
            );
            return Ok(Built(self.b.ap(
                "mpbird",
                &binds! {"ph" => scope, "ps" => t!(&sx, &system, "wcel"), "ch" => t!(&canon, &system, "wcel")},
                &[&held, &iff],
            )));
        }
        let law = match goal.children()[1].label() {
            Some("cr") => "qre",
            Some("cc") => "qcn",
            _ => return Ok(Route::no("a system other than ℝ and ℂ")),
        };
        let rational = take!(self.rational_within(x, scope, facts)?);
        let law = self.b.ap(law, &binds! {"A" => &sx}, &[]);
        Ok(Built(
            pf!(self.b; scope, t!(&sx, "cq", "wcel"), t!(&sx, &system, "wcel"), rational, law, "syl"),
        ))
    }

    /// ( scope -> x e. QQ ) for a value written plainly: a whole number by
    /// way of ℤ (`zq`), a fraction of a whole number by one of ℕ (`znq`), and
    /// a negation as what it negates (`qnegcl`).
    fn rational_within(
        &mut self,
        x: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let within = |me: &mut Self, t: &Term, system: &str| {
            let goal = me.to_term(&t!(me.rpn(t), system, "wcel"));
            me.numeral_within(&goal, scope, facts)
        };
        let sx = self.rpn(x);
        let kids = x.children().to_vec();
        Ok(match (x.label(), kids.as_slice()) {
            (Some("cneg"), [y]) => {
                let held = take!(within(self, y, "cq")?);
                let sy = self.rpn(y);
                let law = self.b.ap("qnegcl", &binds! {"A" => &sy}, &[]);
                Built(
                    pf!(self.b; scope, t!(&sy, "cq", "wcel"), t!(&sx, "cq", "wcel"), held, law, "syl"),
                )
            }
            (Some("co"), [n, m, op]) if op.label() == Some("cdiv") => {
                let whole = take!(within(self, n, "cz")?);
                let natural = take!(within(self, m, "cn")?);
                let (sn, sm) = (self.rpn(n), self.rpn(m));
                let law = self.b.ap("znq", &binds! {"A" => &sn, "B" => &sm}, &[]);
                Built(self.b.ap(
                    "syl2anc",
                    &binds! {"ph" => scope, "ps" => t!(&sn, "cz", "wcel"), "ch" => t!(&sm, "cn", "wcel"),
                    "th" => t!(&sx, "cq", "wcel")},
                    &[&whole, &natural, &law],
                ))
            }
            _ => {
                let whole = take!(within(self, x, "cz")?);
                let law = self.b.ap("zq", &binds! {"A" => &sx}, &[]);
                Built(
                    pf!(self.b; scope, t!(&sx, "cz", "wcel"), t!(&sx, "cq", "wcel"), whole, law, "syl"),
                )
            }
        })
    }

    /// ( scope -> t e. S ) for a closed t, through the digit it comes to: the
    /// equation is worked out as `arithmetic` works one out, and the
    /// membership is the digit's, carried across it by `eqeltrd`.
    fn by_value(&mut self, goal: &Term, scope: &Rpn) -> Checked<Route<Proof>> {
        let (said, system) = (goal.children()[0].clone(), goal.children()[1].clone());
        let value = take!(field::closed_value(&said));
        let digit = match value {
            Value::Exact(v)
                if v.is_integer() && v >= field::q(0) && v <= field::q(9) =>
            {
                v.to_integer().to_u32().unwrap_or(0)
            }
            _ => return Ok(Route::no("it does not come to a digit")),
        };
        let digit = numeral_label(digit).expect("a digit");
        if self.rpn(&said).alone() == Some(digit) {
            return Ok(Route::no("it is a digit already"));
        }
        let member_goal = self.to_term(&t!(digit, self.rpn(&system), "wcel"));
        let member = take!(self.digit_within(&member_goal, scope, &Facts::new())?);
        let lines = Lines::new();
        let same = take!(self.prove_field(
            None,
            &t!(self.rpn(&said), digit, "wceq"),
            scope,
            &Facts::new(),
            &lines
        )?);
        Ok(Built(self.b.ap(
            "eqeltrd",
            &binds! {"ph" => scope, "A" => self.rpn(&said), "B" => digit, "C" => self.rpn(&system)},
            &[&same, &member],
        )))
    }

    /// ( scope -> ; A B e. S ), for a numeral of more than one digit, built
    /// from the digits' labels and brought into the scope once.
    fn decimal_within(&mut self, goal: &Term, scope: &Rpn) -> Checked<Route<Proof>> {
        let (said, system) = (goal.children()[0].clone(), goal.children()[1].clone());
        // In ℕ by its digits (`numerals::nn`), as 10 is by `decnncl2`: a
        // decimal is never zero, since its digits before the last are not.
        if system.label() == Some("cn") {
            let Some(value) = super::numerals::value(&said).filter(|v| !v.is_zero())
            else {
                return Ok(Route::no("not a numeral other than zero"));
            };
            let closed = super::numerals::nn(&self.b, value);
            return Ok(Built(pf!(self.b; self.rpn(goal), scope, closed, "a1i")));
        }
        let Some(lift) = system.label().and_then(|l| lookup(rules::FROM_NN0, l)) else {
            return Ok(Route::no("a decimal is placed in ℕ, ℕ₀, ℤ, ℝ and ℂ only"));
        };
        fn whole(me: &Elaborator, term: &Term) -> Route<Proof> {
            if let Some(d) = term.label().and_then(rules::digit_of) {
                if term.children().is_empty() {
                    return Built(me.step(&format!("{d}nn0")));
                }
            }
            if term.label() != Some("cdc") {
                return Route::no("not a numeral");
            }
            let (upper, last) = (&term.children()[0], &term.children()[1]);
            let parts = [whole(me, upper), whole(me, last)];
            if let Some(d) = parts.iter().find(|p| p.is_declined()) {
                return d.clone();
            }
            let [Built(a), Built(b)] = parts else {
                unreachable!("both parts are built")
            };
            Built(me.b.ap(
                "deccl",
                &binds! {"A" => me.rpn(upper), "B" => me.rpn(last)},
                &[&a, &b],
            ))
        }
        let mut closed = take!(whole(self, &said));
        if let Some(lift) = lift {
            let s = self.rpn(&said);
            closed = self.b.ap(lift, &binds! {"A" => &s, "N" => &s}, &[&closed]);
        }
        Ok(Built(pf!(self.b; self.rpn(goal), scope, closed, "a1i")))
    }

    /// ( scope -> d e. S ), for a digit and a system set.mm names it in.
    ///
    /// `ax-1cn` is the one place the library spells such a label otherwise,
    /// and where it names none the fact is one it does not state.
    pub fn digit_within(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let _ = facts;
        let (said, system) = (goal.children()[0].clone(), goal.children()[1].clone());
        let suffix = system.label().and_then(|l| lookup(rules::SYSTEMS, l));
        let Some(suffix) = suffix.filter(|_| system.children().is_empty()) else {
            return Ok(Route::no("not a number system set.mm names digits in"));
        };
        if said.label() == Some("cdc") {
            return self.decimal_within(goal, scope);
        }
        let value = linear::numeral(&said, self.flabel());
        let digit = match value {
            Some(v) if v.is_integer() && v >= field::q(0) && v <= field::q(9) => {
                v.to_integer().to_u32().unwrap_or(0)
            }
            _ => return Ok(Route::no("what belongs is not a single digit")),
        };
        // The side must *be* its digit. One that only works out to it is a
        // computation, and this is not the method that does computations.
        let numeral = numeral_label(digit).expect("a digit");
        if self.rpn(&said).alone() != Some(numeral) {
            return Ok(Route::no(
                "a side works out to a digit but is one only after working out",
            ));
        }
        let system_label = system.label().unwrap_or("").to_string();
        let mut label = format!("{digit}{suffix}");
        if !self.b.sigs.contains_key(&label) {
            label = format!("ax-{label}");
        }
        if !self.b.sigs.contains_key(&label)
            && suffix == "z"
            && self.b.sigs.contains_key(&format!("{digit}nn0"))
        {
            // set.mm names every digit in ℕ₀ and only some in ℤ.
            let whole = self.step(&format!("{digit}nn0"));
            let closed = self.b.ap("nn0zi", &binds! {"N" => numeral}, &[&whole]);
            return Ok(Built(
                pf!(self.b; t!(numeral, system_label, "wcel"), scope, closed, "a1i"),
            ));
        }
        if !self.b.sigs.contains_key(&label) {
            return Ok(self.no("set.mm does not state {}", &[&self.rpn(goal)]));
        }
        let held = self.step(&label);
        Ok(Built(self.b.ap(
            "a1i",
            &binds! {"ph" => t!(numeral, system_label, "wcel"), "ps" => scope},
            &[&held],
        )))
    }

    /// The innermost part of `whole` whose membership of `system` nothing
    /// offered settles, through +, −, · and /, which make a number of
    /// numbers; `whole` itself where both its parts settle or it is built
    /// otherwise.
    fn unsaid_part(
        &mut self,
        whole: &Term,
        system: &str,
        scope: &Rpn,
        offered: &Facts,
    ) -> Checked<Term> {
        let kids = whole.children();
        let arithmetic = whole.variable().is_none()
            && whole.label() == Some("co")
            && kids.len() == 3
            && kids[2]
                .label()
                .is_some_and(|op| rules::ARITHMETIC.contains(&op));
        if !arithmetic {
            return Ok(whole.clone());
        }
        for part in &kids[..2] {
            let want = self.to_term(&t!(self.rpn(part), system, "wcel"));
            if self
                .settle(&want, scope, offered, 3, None, None)?
                .is_declined()
            {
                return self.unsaid_part(part, system, scope, offered);
            }
        }
        Ok(whole.clone())
    }

    /// That a term belongs to a number system, which the text writes.
    ///
    /// Membership is a dull fact the page states rather than a step's to
    /// discover, so a term whose membership nothing supplies is a line the
    /// proof owes, and saying so is what this is for. A decline here would
    /// reach the caller as the method not covering the step, which is the
    /// one thing it does not mean.
    pub fn membership(
        &mut self,
        said: &Rpn,
        system: &str,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let want = t!(said, system, "wcel");
        let set = t!(system);
        // What the step's own lines say, first; `part` says in what order.
        if let Built(p) = self.part(said, &set, scope, facts)? {
            return Ok(p);
        }
        // A finite sum is a number because its terms are (`summed`).
        let whole = self.to_term(said);
        if whole.variable().is_none() && whole.label() == Some("csu") {
            if let Built(p) = self.summed(&whole, &set, scope, facts, None)? {
                return Ok(p);
            }
        }
        // What `part` cannot build is searched for, with the step's own
        // lines laid over the scope's copies of the same claims.
        let written = facts.filtered(|_, v| from_requires(v));
        for (k, w) in self.written.entries() {
            if let Some(lifted) = self.lifted_to(&k, &w.proof, &w.at, scope) {
                self.know(&written, k, lifted);
            }
        }
        let offered = facts.with(&written);
        match self.settle(&self.to_term(&want), scope, &offered, 3, None, None)? {
            Built(p) => Ok(p),
            Declined(_) => {
                // A quotient is a number once its divisor is not zero, and
                // that is the line a reader is owed where it is missing,
                // whatever says the quotient is a number elsewhere.
                let divisor = (whole.label() == Some("co")
                    && whole.children()[2].label() == Some("cdiv"))
                .then(|| self.rpn(&whole.children()[1]));
                if let Some(divisor) = divisor {
                    let apart = self.to_term(&t!(&divisor, "cc0", "wne"));
                    if self
                        .settle(&apart, scope, &offered, 3, None, None)?
                        .is_declined()
                    {
                        return Err(self.defect(
                            self.at,
                            format!(
                                "nothing says {}, which this step needs for {}",
                                self.render(&self.rpn(&apart)),
                                self.render(said)
                            ),
                        ));
                    }
                }
                // What is named is the part nothing says is a number: 2·√a is
                // one once √a is, so it is √a the line owes.
                let missing = self.unsaid_part(&whole, system, scope, &offered)?;
                let named = self.rpn(&missing);
                // A line saying the term is real says it is complex too, and
                // a real term is what most items give: √A ∈ ℝ, never √A ∈ ℂ.
                // So an ask in ℂ names both.
                if system == "cc" {
                    return Err(self.defect(
                        self.at,
                        format!(
                            "nothing says {} ∈ ℝ or ∈ ℂ, which this step needs",
                            self.render(&named)
                        ),
                    ));
                }
                Err(self.defect(
                    self.at,
                    format!(
                        "nothing says {}, which this step needs",
                        self.render(&t!(&named, system, "wcel"))
                    ),
                ))
            }
        }
    }

    /// What a membership says of its term besides itself, as (claim, lemmas)
    /// pairs: the lemmas carry the membership to the claim one after another.
    pub fn implied_terms(&self, said: &Rpn) -> Vec<(Rpn, Vec<String>)> {
        self.implied_chains(said)
            .into_iter()
            .map(|(claim, chain)| (claim, chain.into_iter().map(|l| l.lemma).collect()))
            .collect()
    }

    /// `implied_terms` with each lemma's binding and what it reaches.
    fn implied_chains(&self, said: &Rpn) -> Vec<(Rpn, Vec<Link>)> {
        let node = self.to_term(said);
        // A part of a set and a member of its power set say each other
        // (`rules::PARTS`), where the page writes the fact in one of the two
        // forms: the checker's question, asked of the page's reading, so
        // that "g is differentiable on (a, b)", whose term is a part of a
        // set, says only itself in both tools.
        let env = crate::sorts::Env {
            g: self.g,
            scopes: self.scopes,
        };
        // The page reads `x ⊆ S` only from `wss` and `x ∈ 𝒫S` only from a
        // `wcel` whose set is a `cpw`, their notations' targets, so no other
        // term is read back to the page to ask.
        let part_shaped = match (node.label(), node.children()) {
            (Some("wss"), [_, _]) => true,
            (Some("wcel"), [_, set]) => set.label() == Some("cpw"),
            _ => false,
        };
        let written_as_part = part_shaped
            && self.page_node(&node).is_some_and(|page| {
                part_said_otherwise(&page, env, &self.sorts_now).is_some()
            });
        if written_as_part {
            for (_, _, lemma) in rules::PARTS {
                if let Some(made) = self.lemma_step(lemma, &node) {
                    return vec![(self.rpn(&made.reached), vec![made])];
                }
            }
        }
        if node.variable().is_some()
            || node.label() != Some("wcel")
            || node.children().len() != 2
        {
            return Vec::new();
        }
        // A class of more than one token is no number system, and is read
        // as a range below.
        let mut system: &str =
            self.rpn(&node.children()[1]).alone().unwrap_or_default();
        let mut head: Vec<Link> = Vec::new();
        if lookup(rules::WITHIN, system).is_none()
            && lookup(rules::IMPLIED, system).is_none()
        {
            // A range is no number system, and a line saying a term is in
            // one says nothing past itself (`SYNTAX.md`): `mun:range-integer`
            // is how a page says its member is whole. A sum's index is in
            // its range as the sum runs over it, and is a whole number there
            // (`elfznn0`), as a family's values are read.
            if self.in_family == 0 {
                return Vec::new();
            }
            let where_ = &node.children()[1];
            if where_.variable().is_some()
                || where_.label() != Some("co")
                || where_.children().len() != 3
                || self.rpn(&where_.children()[2]).alone() != Some("cfz")
            {
                return Vec::new();
            }
            let start = self.rpn(&where_.children()[0]);
            for (inside, first, lemma) in rules::RANGE_WITHIN {
                if first.is_none() || *first == start.alone() {
                    if let Some(made) = self.lemma_step(lemma, &node) {
                        head = vec![made];
                        system = inside;
                        break;
                    }
                }
            }
            if head.is_empty() {
                return Vec::new();
            }
        }
        let mut out = Vec::new();
        if let Some(first) = head.first() {
            out.push((self.rpn(&first.reached), head.clone()));
        }
        let at = head
            .last()
            .map(|l| l.reached.clone())
            .unwrap_or_else(|| node.clone());
        for (_sign, big) in rules::SYSTEM_OF {
            let Some(path) =
                rules::within_path(Some(system), Some(big)).filter(|p| !p.is_empty())
            else {
                continue;
            };
            let mut chain = head.clone();
            let mut here = at.clone();
            for lemma in path {
                let made = self.lemma_step(lemma, &here).unwrap_or_else(|| {
                    panic!("{lemma} does not take {}", self.rpn(&here))
                });
                here = made.reached.clone();
                chain.push(made);
            }
            out.push((self.rpn(&here), chain));
        }
        for (_page, lemma) in rules::implied(Some(system)) {
            let made = self
                .lemma_step(lemma, &at)
                .unwrap_or_else(|| panic!("{lemma} does not take {}", self.rpn(&at)));
            let mut chain = head.clone();
            chain.push(made.clone());
            out.push((self.rpn(&made.reached), chain.clone()));
            // The page writes k ≠ 0 as a denied equation, `nnne0` as =/=.
            if made.reached.label() == Some("wne") {
                let kids = made.reached.children().to_vec();
                let denied = Term::apply("wn", vec![Term::apply("wceq", kids)]);
                chain.push(Link {
                    lemma: "neneqd".to_string(),
                    binding: None,
                    reached: denied.clone(),
                    sets: Vec::new(),
                });
                out.push((self.rpn(&denied), chain));
            }
        }
        out
    }

    /// (lemma, binding, what it concludes) for a lemma `( P -> Q )` applied
    /// to a term matching P, or None where it does not match. A lemma
    /// `( ( X e. V /\ P ) -> Q )` is applied the same way, with V read as
    /// the class of all sets and X ∈ V left for the caller to prove (`sets`):
    /// `gsspw` takes a part of B to a member of 𝒫B where B is a set.
    fn lemma_step(&self, lemma: &str, fact: &Term) -> Option<Link> {
        let whole = self.statement(lemma);
        let premise = &whole.children()[0];
        let sethood = premise.variable().is_none()
            && premise.label() == Some("wa")
            && premise.children()[0].label() == Some("wcel")
            && premise.children()[0].children()[1].variable().is_some();
        let carried = if sethood {
            &premise.children()[1]
        } else {
            premise
        };
        let mut binding = fit(carried, fact, &Binding::new(), &names_of(&whole))?;
        let mut sets = Vec::new();
        if sethood {
            let class = premise.children()[0].children()[1].variable_symbol()?;
            binding.insert(class, Term::apply("cvv", Vec::new()));
            sets.push(premise.children()[0].substitute(&binding));
        }
        let reached = whole.children()[1].substitute(&binding);
        Some(Link {
            lemma: lemma.to_string(),
            binding: Some(binding),
            reached,
            sets,
        })
    }

    /// Each thing a membership line also says, with its proof under `scope`
    /// from the line's own `proof`. A lemma that asks a class be a set has
    /// it proved from the facts (`made_a_set`), and where it cannot be, what
    /// that lemma would give is not said.
    pub fn implied(
        &mut self,
        said: &Rpn,
        proof: &Proof,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Facts> {
        let out = Facts::new();
        'claims: for (claim, chain) in self.implied_chains(said) {
            let mut held = proof.clone();
            let mut at = said.clone();
            for link in chain {
                let after = self.rpn(&link.reached);
                // ( scope -> ( X e. _V /\ at ) ), for a lemma asking a set.
                for set in &link.sets {
                    let Built(made) = self.made_a_set(set, scope, facts)? else {
                        continue 'claims;
                    };
                    let both = t!(self.rpn(set), at, "wa");
                    held = self.b.ap(
                        "jca",
                        &binds! {"ph" => scope, "ps" => self.rpn(set), "ch" => &at},
                        &[&made, &held],
                    );
                    at = both;
                }
                if link.lemma == "neneqd" {
                    let node = self.to_term(&at);
                    let (a, b) =
                        (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
                    held = self.b.ap(
                        "neneqd",
                        &binds! {"ph" => scope, "A" => &a, "B" => &b},
                        &[&held],
                    );
                } else {
                    let binding = link.binding.as_ref().expect("a lemma's binding");
                    let binds = self.spelt(binding);
                    let law = self.b.ap(&link.lemma, &binds, &[]);
                    held = pf!(self.b; scope, at, after, held, law, "syl");
                }
                at = after;
            }
            self.know(&out, claim, held);
        }
        Ok(out)
    }

    /// What the lines a step names, and its requires lines, say by what a
    /// membership among them implies (`rules::IMPLIED`), each proved from
    /// its line: a cited `let k ∈ ℕ` says k ≥ 1 and k ≠ 0 (`ELABORATION.md`,
    /// "A line the page cites says what it states and what a membership
    /// among its sentences implies"), which a lemma's antecedent asks as
    /// surely as what the line states.
    pub fn implied_by_named(
        &mut self,
        step: Option<&Step>,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Facts> {
        let out = Facts::new();
        let Some(step) = step else {
            return Ok(out);
        };
        let lines = self.lines.clone();
        let mut said_here: Vec<(Rpn, Proof)> = Vec::new();
        for r in &step.just.refs {
            let Some(line) = lines.get(r) else {
                continue;
            };
            let carried = self.carried(r, facts, &lines);
            for (said, proof) in self.stated_by(r, scope, facts, &lines)? {
                let proof = match proof {
                    Some(p) => p,
                    None if said == line.term => carried.clone(),
                    None => continue,
                };
                said_here.push((said, proof));
            }
        }
        for req in &step.requires {
            let said = self.claim_of(&req.fact)?;
            if let Some(proof) = self.held(facts, &said, scope)? {
                said_here.push((said, proof));
            }
        }
        for (said, proof) in said_here {
            let more = self.implied(&said, &proof, scope, facts)?;
            for (k, v) in more.entries() {
                self.know(&out, k, v);
            }
        }
        Ok(out)
    }

    /// `known` with what the lines the step names imply laid in where it
    /// does not hold the claim already (`implied_by_named`), or holds it only
    /// from a line the step may not rest on: 1.3.2 above says V ∖ {a} ∈
    /// 𝒫(X ∖ {a}), and a step naming 1.3.1, V ∖ {a} ⊆ X ∖ {a}, rests on that.
    pub fn with_implied(
        &mut self,
        step: Option<&Step>,
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<()> {
        let implied = self.implied_by_named(step, scope, known)?;
        let restable = match &self.resting {
            Some(resting) => {
                known.filtered(|_, p| p.origin.iter().all(|o| may_rest_on(resting, o)))
            }
            None => known.copy(),
        };
        for (k, v) in implied.entries() {
            if !self.holds(&restable, &k) {
                self.know(known, k, v);
            }
        }
        Ok(())
    }

    /// `said ∈ system`, carried in one lemma from a membership written: only
    /// the lemmas `rules::MEMBERSHIP` declares that take a thing in one
    /// number system to another, and only one of them.
    pub fn bridged(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        written: &Facts,
    ) -> Checked<Option<Proof>> {
        for ((source, target), label) in self.bridge_labels() {
            if system.alone() != Some(target.as_str()) {
                continue;
            }
            let claim = t!(said, source, "wcel");
            let mut proof = self.held(written, &claim, scope)?;
            if proof.is_none() {
                if let Some(w) = self.written_held(&claim)? {
                    proof = self.lifted_to(&claim, &w.proof, &w.at, scope);
                }
            }
            // What a requires line wrote, or what a line being cited says.
            let Some(proof) = proof else {
                continue;
            };
            let origin = &proof.origin;
            let cited =
                !origin.is_empty() && origin.iter().all(|o| self.citing.contains(o));
            if !(from_requires(&proof) || cited) {
                continue;
            }
            let push = self.sig(&label).push()[0].to_string();
            let law = self.b.ap(&label, &binds! {push => said}, &[]);
            return Ok(Some(self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &claim, "ch" => t!(said, system, "wcel")},
                &[&proof, &law],
            )));
        }
        Ok(None)
    }

    /// The sethood of each class a statement's `let` lines introduce, in the
    /// kernel's sense, which the page never says: each goes into `facts`
    /// sealed as `sethood@<label>`, and those origins are what this gives
    /// back, for `sorts`.
    pub fn sethoods(
        &mut self,
        nodes: &[Node],
        terms: &[Rpn],
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<BTreeSet<String>> {
        let mut out = BTreeSet::new();
        let hypotheses = self.thm.hypotheses.clone();
        for ((h, node), t) in hypotheses.iter().zip(nodes).zip(terms) {
            let Some(label) = h.label.clone().filter(|l| !l.is_empty()) else {
                continue;
            };
            if h.kind != crate::corpus::Intro::Let || h.text.contains(" be a set") {
                continue;
            }
            let subject = node.leftmost().text.to_string();
            let Some(kernel) = self.names.get(&subject).cloned() else {
                continue;
            };
            let said = t!(kernel, "cvv", "wcel");
            let origin = format!("sethood@{label}");
            let membership = if node.notation() == crate::notations::MEMBERSHIP {
                self.held(facts, t, scope)?
            } else {
                None
            };
            if let Some(held) = self.held(facts, &said, scope)? {
                let sealed = self.seal(held, &origin);
                self.know(facts, said, sealed);
            } else if let Some(held) = membership {
                let parts = self.to_term(t);
                let (a, b) = (
                    self.rpn(&parts.children()[0]),
                    self.rpn(&parts.children()[1]),
                );
                let law = self.b.ap("elex", &binds! {"A" => &a, "B" => &b}, &[]);
                let made = pf!(self.b; scope, t, said, held, law, "syl");
                let sealed = self.seal(made, &origin);
                self.know(facts, said, sealed);
            } else {
                continue;
            }
            out.insert(origin);
        }
        Ok(out)
    }

    /// `term ∈ V` from the constructor at the term's head; else a decline.
    /// `SETHOOD` names the lemma, and `apply_lemma` asks what it asks — the
    /// parts' sethood — of `settle`, which comes back here for each part.
    pub fn made_a_set(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let head = &wanted.children()[0];
        let lemma = if head.variable().is_none() {
            head.label().and_then(|l| lookup(rules::SETHOOD, l))
        } else {
            None
        };
        // A digit set.mm does not say is a set in one lemma is one because
        // it is a complex number, `4cn` to `9cn`.
        let digit = head
            .label()
            .filter(|_| head.variable().is_none() && head.children().is_empty())
            .and_then(|l| rules::digit_of(l).map(|d| (l, d)));
        if let (None, Some((label, d))) = (lemma, digit) {
            let complex = self.step(&format!("{d}cn"));
            let set =
                self.b
                    .ap("elexi", &binds! {"A" => label, "B" => "cc"}, &[&complex]);
            return Ok(Built(self.b.ap(
                "a1i",
                &binds! {"ph" => t!(label, "cvv", "wcel"), "ps" => scope},
                &[&set],
            )));
        }
        let Some(lemma) = lemma else {
            return Ok(Route::no(format!(
                "no lemma makes a {} a set",
                head.label().unwrap_or("None")
            )));
        };
        self.apply_lemma(lemma, wanted, scope, facts, None, false, None)
    }

    /// A closure lemma at `vars`, from the proofs of what it asks of the
    /// parts, `asked`, each with its claim: one in deduction form takes
    /// them as its hypotheses, and one in closed form, as set.mm states
    /// ℚ's, has them as its antecedent, which `syl`, `syl2anc` or
    /// `syl3anc` discharges. `gives` is what it concludes.
    fn closure(
        &mut self,
        lemma: &str,
        vars: &[(&str, &Rpn)],
        asked: &[(Rpn, Proof)],
        gives: &Rpn,
        scope: &Rpn,
    ) -> Proof {
        let proofs: Vec<&Proof> = asked.iter().map(|(_, p)| p).collect();
        let mut binds = crate::mm::spell::Binds::new();
        for (var, term) in vars {
            binds.insert(var.to_string(), (*term).clone());
        }
        if !self.sig(lemma).essentials.is_empty() {
            binds.insert("ph".to_string(), scope.clone());
            return self.b.ap(lemma, &binds, &proofs);
        }
        let law = self.b.ap(lemma, &binds, &[]);
        let (discharge, names) = match asked.len() {
            1 => ("syl", ["ps", "ch", "", ""]),
            2 => ("syl2anc", ["ps", "ch", "th", ""]),
            _ => ("syl3anc", ["ps", "ch", "th", "ta"]),
        };
        let mut around = binds! {"ph" => scope};
        for (name, (claim, _)) in names.iter().zip(asked) {
            around.insert(name.to_string(), claim.clone());
        }
        around.insert(names[asked.len()].to_string(), gives.clone());
        let mut hyps = proofs;
        hyps.push(&law);
        self.b.ap(discharge, &around, &hyps)
    }

    /// `said ∈ system` for a compound, from its parts; else a decline.
    ///
    /// What each part is proved by is the caller's: `parts(term, system)`. A
    /// fixed table and no search, so nothing it cannot build costs more than
    /// a lookup. A quotient is built only where `nonzero(divisor)` is given
    /// to prove its divisor is not zero.
    pub fn built(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        parts: &mut Parts<'_, 'a>,
        nonzero: Option<&mut Nonzero<'_, 'a>>,
    ) -> Checked<Route<Proof>> {
        let node = self.to_term(said);
        // The tables are keyed by a number system's label; a class of more
        // than one token is in none of them.
        let system_label = system.alone().unwrap_or_default();
        if node.variable().is_none()
            && node.label() == Some("co")
            && node.children().len() == 3
        {
            let (left, right) =
                (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
            let op = self.rpn(&node.children()[2]);
            let op_label = op.alone().unwrap_or_default();
            let divided = lookup(rules::DIVIDED, system_label);
            if let (true, Some(nonzero), Some(lemma)) =
                (op_label == "cdiv", nonzero, divided)
            {
                let pa = take!(parts(self, &left, system)?);
                let pb = take!(parts(self, &right, system)?);
                let pn = take!(nonzero(self, &right)?);
                return Ok(Built(self.closure(
                    lemma,
                    &[("A", &left), ("B", &right)],
                    &[
                        (t!(left, system, "wcel"), pa),
                        (t!(right, system, "wcel"), pb),
                        (t!(right, "cc0", "wne"), pn),
                    ],
                    &t!(said, system, "wcel"),
                    scope,
                )));
            }
            // A binomial coefficient or a remainder is a whole number when
            // its parts are what `WHOLE` asks, carried to the system asked
            // by a bridge.
            if let Some(w) = rules::WHOLE.iter().find(|w| op.alone() == Some(w.op)) {
                let (left_var, left_system) = w.left;
                let (right_var, right_system) = w.right;
                let pl = take!(parts(self, &left, &t!(left_system))?);
                let pr = take!(parts(self, &right, &t!(right_system))?);
                let law = self.b.ap(
                    w.lemma,
                    &binds! {left_var => &left, right_var => &right},
                    &[],
                );
                let whole = t!(said, "cn0", "wcel");
                let made = self.b.ap(
                    "syl2anc",
                    &binds! {"ph" => scope, "ps" => t!(left, left_system, "wcel"),
                    "ch" => t!(right, right_system, "wcel"), "th" => &whole},
                    &[&pl, &pr, &law],
                );
                return self.carried_within(said, "cn0", system, made, scope);
            }
            let lemma = op
                .alone()
                .and_then(|o| system.alone().and_then(|s| rules::closed(o, s)));
            let Some(lemma) = lemma else {
                return Ok(Route::no(format!("no closure lemma for {op} in {system}")));
            };
            let pa = take!(parts(self, &left, system)?);
            let into = if op_label == "cexp" {
                t!("cn0")
            } else {
                system.clone()
            };
            let pb = take!(parts(self, &right, &into)?);
            let key = if op_label == "cexp" { "N" } else { "B" };
            return Ok(Built(self.closure(
                lemma,
                &[("A", &left), (key, &right)],
                &[
                    (t!(left, system, "wcel"), pa),
                    (t!(right, into, "wcel"), pb),
                ],
                &t!(said, system, "wcel"),
                scope,
            )));
        }
        if node.variable().is_none()
            && node.label() == Some("cneg")
            && node.children().len() == 1
        {
            let Some(lemma) = lookup(rules::NEGATED, system_label) else {
                return Ok(Route::no(format!(
                    "no closure lemma for negation in {system}"
                )));
            };
            let a = self.rpn(&node.children()[0]);
            let pa = take!(parts(self, &a, system)?);
            return Ok(Built(self.closure(
                lemma,
                &[("A", &a)],
                &[(t!(a, system, "wcel"), pa)],
                &t!(said, system, "wcel"),
                scope,
            )));
        }
        // A value by cases is in a system where the value of each case is.
        if node.variable().is_none()
            && node.label() == Some("cif")
            && node.children().len() == 3
        {
            let condition = self.rpn(&node.children()[0]);
            let (a, b) = (self.rpn(&node.children()[1]), self.rpn(&node.children()[2]));
            let pa = take!(parts(self, &a, system)?);
            let pb = take!(parts(self, &b, system)?);
            return Ok(Built(self.b.ap(
                "ifcld",
                &binds! {"ph" => scope, "ps" => &condition, "A" => &a, "B" => &b,
                "C" => system},
                &[&pa, &pb],
            )));
        }
        Ok(Route::no(
            "not a sum, difference, product, power, negation or value by cases",
        ))
    }

    /// A compound's membership of a number system, from its parts': there is
    /// one way to build a product from its factors, and the factors are
    /// smaller, so walking the term spends no depth. Each factor is settled
    /// in turn with the depth the whole was given.
    pub fn closed_under(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Route<Proof>> {
        let (said, system) = (
            self.rpn(&wanted.children()[0]),
            self.rpn(&wanted.children()[1]),
        );
        self.built(
            &said,
            &system,
            scope,
            &mut |me, term, system| {
                let goal = me.to_term(&t!(term, system, "wcel"));
                me.settle(&goal, scope, facts, depth, None, None)
            },
            Some(&mut |me, divisor| {
                let goal = me.to_term(&t!(divisor, "cc0", "wne"));
                me.settle(&goal, scope, facts, depth, None, None)
            }),
        )
    }

    /// ( scope -> d =/= 0 ) where the page says once that d is a positive
    /// integer (`SYNTAX.md`): d ∈ ℕ as `introduced_membership` builds it,
    /// k, k + 1, j·(j + 1) or 2^n, and so not zero (`nnne0d`). None for any
    /// other divisor.
    pub fn positive_divisor(
        &mut self,
        divisor: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let Built(member) =
            self.introduced_membership(divisor, &t!("cn"), scope, facts)?
        else {
            return Ok(None);
        };
        Ok(Some(self.b.ap(
            "nnne0d",
            &binds! {"ph" => scope, "A" => divisor},
            &[&member],
        )))
    }

    /// ( scope -> d =/= 0 ) from what the step wrote, or a decline: the
    /// divisor not being zero is the page's to say, in a requires line or a
    /// line the step cites, unless the page says once it is a positive
    /// integer, and is not searched for.
    pub fn divisor_written(
        &mut self,
        divisor: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let apart = t!(divisor, "cc0", "wne");
        // What the step may rest on, and nothing else in scope: a line it
        // does not name says nothing of its divisors (`GOALS.md` decision 9).
        let named = self.restable(facts);
        let facts = &named;
        // A numeral other than zero says so itself: a closed numeral fact,
        // which a method may use unwritten.
        let numeral =
            super::numerals::value(&self.to_term(divisor)).filter(|v| !v.is_zero());
        if let Some(value) = numeral {
            let closed = super::numerals::ne0(&self.b, value);
            return Ok(Built(pf!(self.b; apart, scope, closed, "a1i")));
        }
        if let Some(positive) = self.positive_divisor(divisor, scope, facts)? {
            return Ok(Built(positive));
        }
        // Held however the page wrote it: either way round, as ≠ or as the
        // denial of an equation (`held`).
        let mut found = self.held(facts, &apart, scope)?;
        if found.is_none() {
            if let Some(w) = self.written_held(&apart)? {
                found = self.lifted_to(&apart, &w.proof, &w.at, scope);
            }
        }
        if let Some(found) = found {
            return Ok(Built(found));
        }
        // A line saying the divisor is above zero, or below it, says it is
        // not zero (`gt0ne0d`, `lt0ne0d`), as a reader takes A > 0.
        for (want, lemma) in [
            (t!("cc0", divisor, "clt", "wbr"), "gt0ne0d"),
            (t!(divisor, "cc0", "clt", "wbr"), "lt0ne0d"),
        ] {
            let mut found = self.held(facts, &want, scope)?;
            if found.is_none() {
                if let Some(w) = self.written_held(&want)? {
                    found = self.lifted_to(&want, &w.proof, &w.at, scope);
                }
            }
            if let Some(found) = found {
                return Ok(Built(self.b.ap(
                    lemma,
                    &binds! {"ph" => scope, "A" => divisor},
                    &[&found],
                )));
            }
        }
        // A cited line whose membership says so: `let k ∈ ℕ` says k ≠ 0.
        let citing: Vec<String> = self.citing.iter().cloned().collect();
        for r in citing {
            let Some(line) = self.lines.get(&r) else {
                continue;
            };
            let lines = self.lines.clone();
            let carried = self.carried(&r, facts, &lines);
            let lines = self.lines.clone();
            for (said, proof) in self.stated_by(&r, scope, facts, &lines)? {
                let proof = if said == line.term {
                    Some(carried.clone())
                } else {
                    proof
                };
                let Some(proof) = proof else {
                    continue;
                };
                let more = self.implied(&said, &proof, scope, facts)?;
                if let Some(p) = self.held(&more, &apart, scope)? {
                    return Ok(Built(p));
                }
            }
        }
        // A product, a quotient or a power to a numeral is not zero when
        // its parts are not, each by this same test (`METHODS.md`).
        let node = self.to_term(divisor);
        if node.variable().is_none()
            && node.label() == Some("co")
            && node.children().len() == 3
        {
            let how = self.rpn(&node.children()[2]);
            let (a, b) = (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
            let complex = t!("cc");
            match how.alone().unwrap_or_default() {
                "cmul" | "cdiv" => {
                    let lemma = if how.alone() == Some("cmul") {
                        "mulne0d"
                    } else {
                        "divne0d"
                    };
                    let mut parts = Vec::new();
                    for one in [&a, &b] {
                        parts.push(self.part(one, &complex, scope, facts)?);
                    }
                    for one in [&a, &b] {
                        parts.push(self.divisor_written(one, scope, facts)?);
                    }
                    let mut proofs = Vec::new();
                    for one in parts {
                        proofs.push(take!(one));
                    }
                    return Ok(Built(self.b.ap(
                        lemma,
                        &binds! {"ph" => scope, "A" => &a, "B" => &b},
                        &proofs.iter().collect::<Vec<_>>(),
                    )));
                }
                "cexp" => {
                    if let Some(power) = super::numerals::value(&node.children()[1]) {
                        let base = take!(self.part(&a, &complex, scope, facts)?);
                        let apart_base = take!(self.divisor_written(&a, scope, facts)?);
                        let whole = if power.is_zero() {
                            self.b.step("0z")
                        } else {
                            let natural = super::numerals::nn(&self.b, power);
                            self.b.ap("nnzi", &binds! {"N" => &b}, &[&natural])
                        };
                        let whole =
                            pf!(self.b; t!(&b, "cz", "wcel"), scope, whole, "a1i");
                        return Ok(Built(self.b.ap(
                            "expne0d",
                            &binds! {"ph" => scope, "A" => &a, "N" => &b},
                            &[&base, &apart_base, &whole],
                        )));
                    }
                }
                _ => {}
            }
        }
        // A divisor is not zero where its negation is not (`negne0bd`): the
        // kernel writes (−q)/(−p) over p, and the page says −p ∈ ℕ.
        if node.label() != Some("cneg") {
            let negated = t!(divisor, "cneg");
            if let Built(found) = self.divisor_written(&negated, scope, facts)? {
                let number = take!(self.part(divisor, &t!("cc"), scope, facts)?);
                let turned = self.b.ap(
                    "negne0bd",
                    &binds! {"ph" => scope, "A" => divisor},
                    &[&number],
                );
                return Ok(Built(self.b.ap(
                    "mpbird",
                    &binds! {"ph" => scope, "ps" => &apart, "ch" => t!(&negated, "cc0", "wne")},
                    &[&found, &turned],
                )));
            }
        }
        Ok(self.no("nothing the step wrote says {}", &[&apart]))
    }

    /// `said ∈ system` as the page says it once (`READERS.md`, membership said
    /// once), or a decline. Whether and why is `citing::reason`'s, the rule
    /// the checker reads too: a line the step names stating it; a numeral; a
    /// letter in the number system its introducing line names, carried up
    /// `WITHIN`; a sum said once; or a term built from those by +, −, ·,
    /// negation, a power to a numeral or to a letter in ℕ or ℕ₀, and a
    /// quotient whose divisor's `≠ 0` the step writes. What is built here is
    /// the proof of the reason it gives. A letter's membership is sealed as
    /// `membership@<letter>`, which a step rests on without naming it, as it
    /// does a sort; nothing but a membership in a number system is ever proved
    /// from it, since only this route reads it.
    pub fn introduced_membership(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let Some(within) = system.alone().and_then(System::of_label) else {
            return Ok(Route::no("not a number system"));
        };
        if self.beyond_once > 0 {
            return Ok(Route::no("a part of a fact the page writes"));
        }
        // Whether and why is the rule both tools read (`citing::reason`);
        // what is built here is the proof of the reason it gives.
        let term = self.to_term(said);
        let mut ask = BuildOnce {
            me: self,
            scope,
            facts,
            problem: None,
        };
        let reason = crate::citing::reason(&mut ask, &term, within);
        if let Some(problem) = ask.problem {
            return Err(problem);
        }
        let Some(reason) = reason else {
            return Ok(Route::no(
                "not a numeral, an introduced letter, or built from them",
            ));
        };
        match reason {
            OnceReason::Numeral => {
                let goal = self.to_term(&t!(said, system, "wcel"));
                self.numeral_within(&goal, scope, facts)
            }
            OnceReason::Letter => {
                let (letter, set) = self
                    .introduced_in(said)
                    .expect("a letter the walk found introduced");
                self.letter_within(said, &letter, &set, system, scope, facts)
            }
            // A part that a line the step names puts in a number system is
            // a number there, carried up to `system`: N(n) + 1 ∈ ℝ where a
            // line says N(n) ∈ ℝ.
            OnceReason::Stated => {
                match self.stated_within(said, system, scope, facts)? {
                    Some(found) => Ok(Built(found)),
                    None => Ok(Route::no("no line the step names states it")),
                }
            }
            // A sum said once by its terms is in ℝ or ℂ by the sum's lemma,
            // its terms read from the scope at each index.
            OnceReason::Sum => self.summed(&term, system, scope, facts, None),
            // A divisor's `≠ 0` is the page's, from what the step names.
            OnceReason::Built(_) => {
                let named = self.restable(facts);
                self.built(
                    said,
                    system,
                    scope,
                    &mut |me, part, into| {
                        me.introduced_membership(part, into, scope, facts)
                    },
                    Some(&mut |me, divisor| me.divisor_written(divisor, scope, &named)),
                )
            }
        }
    }

    /// Keep, for each letter let into a number system and not yet kept, its
    /// membership as `facts` hold it under `scope`, the scope its line opens:
    /// what `introduced_membership` carries to any scope inside it.
    pub fn note_introduced(&mut self, scope: &Rpn, facts: &Facts) -> Checked<()> {
        for (letter, set) in self.sets.clone() {
            if set
                .alone()
                .and_then(|s| lookup(rules::SYSTEMS, s))
                .is_none()
                && self.range_system(&set).is_none()
            {
                continue;
            }
            let Some(kernel) = self.names.get(&letter).cloned() else {
                continue;
            };
            let claim = t!(kernel, set, "wcel");
            let kept = self.introduced.get(&letter).is_some_and(|all| {
                all.iter().any(|(c, _, at)| *c == claim && at == scope)
            });
            if kept {
                continue;
            }
            if let Some(proof) = self.held(facts, &claim, scope)? {
                self.introduced.entry(letter).or_default().push((
                    claim,
                    proof,
                    scope.clone(),
                ));
            }
        }
        Ok(())
    }

    /// `wanted` where it is a membership the page says once, or several
    /// joined by "and", as a lemma may ask its side conditions together; a
    /// decline for anything else.
    pub fn said_once_proof(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        if wanted.label() == Some("wcel") && wanted.children().len() == 2 {
            let (said, system) = (
                self.rpn(&wanted.children()[0]),
                self.rpn(&wanted.children()[1]),
            );
            return self.introduced_membership(&said, &system, scope, facts);
        }
        let joined = self.conjoined(wanted, scope, &mut |me, one| {
            me.said_once_proof(one, scope, facts)
        })?;
        Ok(joined.unwrap_or_else(|| Route::no("not a membership")))
    }

    /// `said ∈ system` from a line the step names saying `said` is in a
    /// number system inside `system`, carried up `WITHIN`; None where no
    /// such line says it.
    fn stated_within(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let named = self.restable(facts);
        for (_, set) in rules::SYSTEM_OF {
            let Some(held) = self.held(&named, &t!(said, set, "wcel"), scope)? else {
                continue;
            };
            if let Built(proof) = self.carried_within(said, set, system, held, scope)? {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    /// Keep the sums the step now being elaborated writes that the page
    /// says are numbers once (`CheckedTheorem::said_sums`), as kernel terms.
    pub fn note_said_sums(&mut self) -> Checked<()> {
        let nodes = self
            .step_now
            .and_then(|i| self.checked.said_sums.get(i))
            .cloned()
            .unwrap_or_default();
        let mut sums = BTreeSet::new();
        for node in &nodes {
            sums.insert(self.term(node)?);
        }
        self.said_sums = sums;
        Ok(())
    }

    /// The letter whose kernel term is `said`, and the number system the
    /// line introducing it put it in; None for anything else.
    fn introduced_in(&self, said: &Rpn) -> Option<(String, Rpn)> {
        self.sets.iter().find_map(|(letter, set)| {
            let ours = self.names.get(letter).is_some_and(|k| k == said);
            let counted = set
                .alone()
                .and_then(|s| lookup(rules::SYSTEMS, s))
                .is_some()
                || self.range_system(set).is_some();
            (ours && counted).then(|| (letter.clone(), set.clone()))
        })
    }

    /// The number system a range {a, …, b} puts its members in, and the
    /// lemma saying so (`rules::RANGE_WITHIN`, which the checker reads as
    /// well): ℕ from 1, ℕ₀ from 0, ℤ from anywhere. None for a set that is
    /// no range.
    pub(crate) fn range_system(
        &self,
        set: &Rpn,
    ) -> Option<(&'static str, &'static str)> {
        let range = self.to_term(set);
        if range.variable().is_some()
            || range.label() != Some("co")
            || range.children().len() != 3
            || self.rpn(&range.children()[2]).alone() != Some("cfz")
        {
            return None;
        }
        let start = self.rpn(&range.children()[0]);
        rules::RANGE_WITHIN
            .iter()
            .find(|(_, first, _)| first.is_none() || *first == start.alone())
            .map(|(system, _, lemma)| (*system, *lemma))
    }

    /// `said ∈ system` for a letter introduced in `set`, from the scope's
    /// copy of its introducing line, sealed as `membership@<letter>` and
    /// carried up `WITHIN` one lemma at a time.
    fn letter_within(
        &mut self,
        said: &Rpn,
        letter: &str,
        set: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        // A range's member is in the system the range lies in first; any
        // other set a letter is let into is a number system's label.
        let range = self.range_system(set);
        let base = range.map_or(set.alone().unwrap_or_default(), |(system, _)| system);
        if rules::within_path(Some(base), system.alone()).is_none() {
            return Ok(Route::no(format!("{set} is not inside {system}")));
        }
        let claim = t!(said, set, "wcel");
        let mut held = self.held(facts, &claim, scope)?;
        if held.is_none() {
            let all = self.introduced.get(letter).cloned().unwrap_or_default();
            held = all
                .iter()
                .rev()
                .filter(|(kept, _, _)| *kept == claim)
                .find_map(|(_, proof, at)| self.lifted_to(&claim, proof, at, scope));
        }
        let Some(held) = held else {
            return Ok(Route::no("the introducing line is not in scope"));
        };
        let mut proof = self.seal(held, &format!("{MEMBERSHIP}{letter}"));
        if let Some((inside, lemma)) = range {
            let says = self.statement(lemma);
            let Some(binding) = fit(
                &says.children()[0],
                &self.to_term(&claim),
                &Binding::new(),
                &names_of(&says),
            ) else {
                return Ok(Route::no(format!("{lemma} does not take {claim}")));
            };
            let law = self.b.ap(lemma, &self.spelt(&binding), &[]);
            proof = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &claim, "ch" => t!(said, inside, "wcel")},
                &[&proof, &law],
            );
        }
        self.carried_within(said, base, system, proof, scope)
    }

    /// ( scope -> said e. system ) from ( scope -> said e. set ), along the
    /// sets `rules::WITHIN` says lie one inside the next, a lemma for each.
    pub(crate) fn carried_within(
        &mut self,
        said: &Rpn,
        set: &str,
        system: &Rpn,
        mut proof: Proof,
        scope: &Rpn,
    ) -> Checked<Route<Proof>> {
        // `WITHIN` is keyed by a number system's label; a class of more than
        // one token is none of them.
        let target = system.alone().unwrap_or_default();
        let mut at: &str = set;
        while at != target {
            let row = lookup(rules::WITHIN, at).unwrap_or(&[]);
            let next = row
                .iter()
                .find(|(to, _)| *to == target)
                .or_else(|| {
                    row.iter().find(|(to, _)| {
                        rules::within_path(Some(to), Some(target)).is_some()
                    })
                })
                .copied();
            let Some((to, lemma)) = next else {
                return Ok(Route::no(format!("{at} is not inside {system}")));
            };
            let push = self.sig(lemma).push()[0].to_string();
            let law = self.b.ap(lemma, &binds! {push => said}, &[]);
            proof = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => t!(said, at, "wcel"),
                "ch" => t!(said, to, "wcel")},
                &[&proof, &law],
            );
            at = to;
        }
        Ok(Built(proof))
    }

    /// One part of a compound, in a number system, or a decline.
    ///
    /// The step's own line first, then that line carried by one lemma, then
    /// the part built in turn if it is a compound. A numeral is the
    /// library's. What the scope holds is last, and only exactly: it is a
    /// line the page wrote, and a step using it without naming it is what
    /// provenance is there to see.
    pub fn part(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let want = t!(said, system, "wcel");
        let found = self.held(facts, &want, scope)?;
        if let Some(f) = &found {
            if from_requires(f) {
                return Ok(Built(f.clone()));
            }
        }
        if let Some(w) = self.written_held(&want)? {
            if let Some(lifted) = self.lifted_to(&want, &w.proof, &w.at, scope) {
                return Ok(Built(lifted));
            }
        }
        // What the page says once, where the letters are introduced, before
        // a cited line: a line cited only for it is cited for nothing.
        if let Built(said_once) =
            self.introduced_membership(said, system, scope, facts)?
        {
            return Ok(Built(said_once));
        }
        if let Some(carried) = self.bridged(said, system, scope, facts)? {
            return Ok(Built(carried));
        }
        let term = self.to_term(said);
        if linear::numeral(&term, self.flabel()).is_some() {
            return self.settle(&self.to_term(&want), scope, facts, 3, None, None);
        }
        let made = self.built(
            said,
            system,
            scope,
            &mut |me, term, into| me.part(term, into, scope, facts),
            Some(&mut |me, divisor| me.divisor_written(divisor, scope, facts)),
        )?;
        if !made.is_declined() {
            return Ok(made);
        }
        if let Some(f) = found {
            return Ok(Built(f));
        }
        // A closed term `arithmetic` works out and the walk does not take
        // apart, (1 + 1)!, is in a system where its value is.
        let labels = self.b.flabel.clone();
        if let Some((value, equal)) = super::numerals::worked(&self.b, &term, &labels) {
            let spelt = super::numerals::spell(value);
            if spelt != *said {
                if let Built(inside) = self.part(&spelt, system, scope, facts)? {
                    return Ok(Built(self.b.ap(
                        "eqeltrid",
                        &binds! {"ph" => scope, "A" => said, "B" => &spelt, "C" => system},
                        &[&equal, &inside],
                    )));
                }
            }
        }
        if let Some(valued) = self.function_value(said, system, scope, facts)? {
            return Ok(Built(valued));
        }
        // A finite sum is a number because its terms are (`summed`).
        if term.variable().is_none() && term.label() == Some("csu") {
            if let Built(p) = self.summed(&term, system, scope, facts, None)? {
                return Ok(Built(p));
            }
        }
        if let Some(p) = self.equated_part(said, system, scope, facts)? {
            return Ok(Built(p));
        }
        Ok(self.no("nothing written says {}", &[&want]))
    }

    /// `said ∈ system` from an equation in hand with `said` on one side: the
    /// term is in what the other side is in (`eqeltrd`), as a reader takes
    /// a(0) = 0 to say a(0) ∈ ℝ, whatever method the step names
    /// (`METHODS.md`). The other side may not hold `said`, and a term
    /// already being read this way is not read again, so that two equations
    /// cannot send it round.
    fn equated_part(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        if self.equating.contains(said) {
            return Ok(None);
        }
        for (fact, proof) in facts.entries() {
            // An equation the step names: a line it cites or one of its own
            // requires lines. The scope holds every line above, and an
            // equation taken from one the step does not name is a reason
            // the page does not give.
            let named = proof.origin.iter().all(|o| self.citing.contains(o));
            if !named && !from_requires(&proof) {
                continue;
            }
            let node = self.to_term(&fact);
            if node.variable().is_some()
                || node.label() != Some("wceq")
                || node.children().len() != 2
            {
                continue;
            }
            let (left, right) =
                (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
            // The other side may hold the term itself, x = (√x)², and is a
            // number by its own parts; `equating` keeps the search from
            // coming back to the term through it.
            let (other, equal) = if left == *said {
                (right, proof)
            } else if right == *said {
                let turned = self.b.ap(
                    "eqcomd",
                    &binds! {"ph" => scope, "A" => &left, "B" => &right},
                    &[&proof],
                );
                (left, turned)
            } else {
                continue;
            };
            self.equating.insert(said.clone());
            let made = self.part(&other, system, scope, facts);
            self.equating.shift_remove(said);
            if let Built(inner) = made? {
                return Ok(Some(
                    pf!(self.b; scope, said, other, system, equal, inner, "eqeltrd"),
                ));
            }
        }
        Ok(None)
    }

    /// `( F ` x ) ∈ system` where a fact in hand gives F's type, F : A → B,
    /// and x is in A: a function's value at a point of its domain is in its
    /// codomain (`ffvelcdm`), carried to the system wanted by one of the
    /// lemmas `bridged` carries by.
    ///
    /// A function's type is a `let` line, a sort, and is cited for its values
    /// (`READERS.md`): a step or requires line that needs a(k) ∈ ℝ names the
    /// type. A family's values are the exception, a sum's terms or what an
    /// item asks of every member, where a(k) for a : {1, …, n} → ℝ is a
    /// number wherever k is in the range, as the summand's atoms are.
    pub(crate) fn function_value(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let term = self.to_term(said);
        if term.variable().is_some() || term.label() != Some("cfv") {
            return Ok(None);
        }
        let (point, function) =
            (self.rpn(&term.children()[0]), self.rpn(&term.children()[1]));
        for (typed, held) in facts.entries() {
            let t = self.to_term(&typed);
            if t.variable().is_some() || t.label() != Some("wf") {
                continue;
            }
            let (domain, codomain, named) = (
                self.rpn(&t.children()[0]),
                self.rpn(&t.children()[1]),
                self.rpn(&t.children()[2]),
            );
            if named != function {
                continue;
            }
            // A type the step names, by a line it cites or one of its own
            // requires lines; one only in scope is a reason the page does
            // not give, whether a `let` or a numbered step says it.
            let unnamed = !held.origin.is_empty()
                && !held.origin.iter().all(|o| self.citing.contains(o))
                && !from_requires(&held);
            if unnamed && self.in_family == 0 {
                continue;
            }
            let inside = t!(&point, &domain, "wcel");
            let Built(at) =
                self.settle(&self.to_term(&inside), scope, facts, 2, None, None)?
            else {
                continue;
            };
            let value = t!(said, &codomain, "wcel");
            let law = self.b.ap(
                "ffvelcdm",
                &binds! {"F" => &function, "A" => &domain, "B" => &codomain, "C" => &point},
                &[],
            );
            let made = self.b.ap(
                "syl2anc",
                &binds! {"ph" => scope, "ps" => &typed, "ch" => &inside, "th" => &value},
                &[&held, &at, &law],
            );
            if codomain == *system {
                return Ok(Some(made));
            }
            let (Some(from), Some(to)) = (codomain.alone(), system.alone()) else {
                continue;
            };
            let Some(label) = self
                .bridge_labels()
                .get(&(from.to_string(), to.to_string()))
                .cloned()
            else {
                continue;
            };
            let push = self.sig(&label).push()[0].to_string();
            let law = self.b.ap(&label, &binds! {push => said}, &[]);
            return Ok(Some(self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &value, "ch" => t!(said, system, "wcel")},
                &[&made, &law],
            )));
        }
        Ok(None)
    }

    /// The lemmas `rules::MEMBERSHIP` declares that take a thing in one
    /// number system to another, by the two systems.
    fn bridge_labels(&mut self) -> IndexMap<(String, String), String> {
        if self.bridges.is_none() {
            let mut bridges = IndexMap::new();
            for label in self.declared_as(super::state::Role::Carrier) {
                let whole = self.statement(&label);
                let (given, gives) = (&whole.children()[0], &whole.children()[1]);
                // Keyed by the two systems' labels: a carrier takes a thing in
                // one number system, a constant, to another.
                let (Some(from), Some(to)) = (
                    self.rpn(&given.children()[1]).alone(),
                    self.rpn(&gives.children()[1]).alone(),
                ) else {
                    continue;
                };
                bridges
                    .entry((from.to_string(), to.to_string()))
                    .or_insert(label);
            }
            self.bridges = Some(bridges);
        }
        self.bridges.clone().unwrap_or_default()
    }

    /// What a line states, sentence by sentence: its own sentences, and
    /// where it obtained names, their memberships, which the scope holds
    /// with the line as their origin.
    pub fn stated_claims(&self, r: &str, facts: &Facts, lines: &Lines) -> Vec<Rpn> {
        let term = lines.get(r).map(|l| l.term).unwrap_or_default();
        let mut out = self.parts(&term);
        for (said, proof) in facts.entries() {
            if rests_on_only(&proof, r) && !out.contains(&said) {
                out.push(said);
            }
        }
        out
    }

    /// What a line states (`stated_claims`), with each proof under `scope`
    /// where `facts` holds one.
    pub fn stated_by(
        &mut self,
        r: &str,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<IndexMap<Rpn, Option<Proof>>> {
        let mut out: IndexMap<Rpn, Option<Proof>> = IndexMap::new();
        for said in self.stated_claims(r, facts, lines) {
            let held = self.held(facts, &said, scope)?;
            out.insert(said, held);
        }
        Ok(out)
    }
}
