//! Reading the rule tables: a fact the page leaves out, built by table.
//!
//! The rule tables are the fourth of the elaborator's six parts
//! (`ELABORATION.md`, "How the elaborator is built"), and `rules` holds them
//! as data. This is the code that reads them. Given what is wanted — an
//! equation lifted through a term, a term's membership of a number system, a
//! numeral's, a term's sethood — it looks up the lemma the table names for
//! that shape and builds the proof from it. Nothing here searches: what a
//! table has no entry for is declined, and left to what is tried after.

use std::cell::OnceCell;
use std::collections::BTreeSet;

use indexmap::IndexMap;
use num_traits::{ToPrimitive, Zero};

use super::calculators::Revalued;
use super::field::{self, Value};
use super::linear;
use super::matcher::ChainLink;
use super::provenance::{from_requires, rests_on_only, MEMBERSHIP};
use super::state::{fit, names_of, Binding, Elaborator};
use super::{Facts, Lines, Written};
use crate::binds;
use crate::citing::{said_otherwise, CodomainAsk, CodomainReason, OnceReason, Shape};
use crate::corpus::Step;
use crate::formula::symbol::Symbol;
use crate::formula::Node;
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::mm::Rpn;
use crate::outcome::{Built, Checked, Declined, Route};
use crate::rules::{self, lookup, numeral_label, System};
use crate::{pf, t, take};

mod implied;
mod introduced;
mod writing;

/// Why `built` takes a term no further: it is no operation the closure
/// tables walk, and so an atom of the walk.
const NOT_BUILT: &str =
    "not a sum, difference, product, power, negation or value by cases";

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
    /// The two are one term but for the order of holes a notation puts in
    /// no order, |AB| and |BA| (`Elaborator::pairs_in_order`). Nothing else
    /// is reordered.
    InNoOrder,
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
    /// A closed piece that changed, worked out by real arithmetic where it
    /// stands: a link of a calculation naming `real arithmetic`.
    RealArithmetic { what: String },
}

/// The build's codomains as `citing::codomain_reason` asks of them: kernel
/// terms, and the parts the facts in scope state, `X ⊆ Y` or `X ∈ 𝒫Y`, as
/// pairs (small, big).
struct KernelCodomains<'p> {
    parts: &'p [(Rpn, Rpn)],
}

impl CodomainAsk for KernelCodomains<'_> {
    type T = Rpn;

    fn alike(&self, a: &Rpn, b: &Rpn) -> bool {
        a == b
    }

    fn system(&self, set: &Rpn) -> Option<rules::System> {
        set.alone().and_then(rules::System::of_label)
    }

    fn part(&self, small: &Rpn, big: &Rpn) -> bool {
        self.parts.iter().any(|(s, b)| s == small && b == big)
    }
}

/// A chain of lemmas carrying a membership to what it also says: each
/// lemma, what it was bound to, and what it reaches.
#[derive(Clone)]
pub struct Link {
    pub lemma: String,
    pub binding: Option<Binding>,
    pub reached: Term,
    /// What the lemma asks besides the fact it carries: that a class is a
    /// set, as `gsspw` asks of the set a part is a part of (`made_a_set`),
    /// or that a point is a complex number, as `glineon` asks.
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
    /// Whether a term is a letter the page gives the point sort, as
    /// `let A be a point` does.
    fn is_point(&self, term: &Term) -> bool {
        let said = self.me.rpn(term);
        self.me.names.iter().any(|(name, kernel)| {
            *kernel == said
                && self
                    .me
                    .sorts_now
                    .get(name)
                    .is_some_and(|sort| sort.is("point"))
        })
    }

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
                    "cbc" => Shape::Whole("cbc", &kids[0], &kids[1]),
                    "cgcd" => Shape::Whole("cgcd", &kids[0], &kids[1]),
                    "clcm" => Shape::Whole("clcm", &kids[0], &kids[1]),
                    _ => Shape::Other,
                }
            }
            (Some("cpi" | "ceu"), 0) => Shape::Real,
            (Some("cfv"), 2) if self.me.rpn(&kids[1]).alone() == Some("cabs") => {
                match kids[0].children() {
                    // The distance |PQ| is |P − Q| of two points; of two
                    // numbers it is an absolute value, |x − c|.
                    [p, q, op]
                        if kids[0].label() == Some("co")
                            && self.me.rpn(op).alone() == Some("cmin")
                            && self.is_point(p)
                            && self.is_point(q) =>
                    {
                        Shape::Distance(p, q)
                    }
                    // ∠PQR is | (P − Q) ang (R − Q) |.
                    [from, to, op]
                        if kids[0].label() == Some("co")
                            && self.me.rpn(op).alone() == Some("cang") =>
                    {
                        match (from.children(), to.children()) {
                            ([p, q, m1], [r, q2, m2])
                                if from.label() == Some("co")
                                    && to.label() == Some("co")
                                    && self.me.rpn(m1).alone() == Some("cmin")
                                    && self.me.rpn(m2).alone() == Some("cmin")
                                    && self.me.rpn(q) == self.me.rpn(q2) =>
                            {
                                Shape::Angle(p, q, r)
                            }
                            _ => Shape::Other,
                        }
                    }
                    _ => Shape::Absolute(&kids[0]),
                }
            }
            (Some("cfv"), 2) if self.me.rpn(&kids[1]).alone() == Some("cfa") => {
                Shape::Factorial(&kids[0])
            }
            _ if crate::methods::surds::is_root(term) => {
                match crate::methods::field::closed_value(&kids[0]) {
                    Built(crate::methods::field::Value::Exact(v))
                        if crate::citing::root_taken(&v) =>
                    {
                        Shape::Real
                    }
                    _ => Shape::Other,
                }
            }
            _ if crate::methods::reals::Trig::of(term).is_some() => {
                match crate::methods::reals::closed_value(term) {
                    Built(crate::methods::reals::Value::Exact(_)) => Shape::Real,
                    _ => Shape::Applied(&kids[0]),
                }
            }
            _ if crate::methods::surds::applies(term, "ce") => Shape::Applied(&kids[0]),
            _ if crate::methods::reals::applies(term, "clog") => {
                match crate::methods::field::closed_value(&kids[0]) {
                    Built(crate::methods::field::Value::Exact(v))
                        if crate::citing::log_taken(&v) =>
                    {
                        Shape::Real
                    }
                    _ => Shape::Other,
                }
            }
            _ => Shape::Other,
        }
    }

    fn letter(&mut self, term: &Term) -> Option<System> {
        let (_, set) = self.me.introduced_in(&self.me.rpn(term))?;
        System::of_label(self.me.introduced_system(&set)?)
    }

    /// A letter the page gives the point sort, as `let A be a point` does.
    fn point(&mut self, term: &Term) -> bool {
        self.is_point(term)
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

/// `term`, a binder, with the letter at `place` moved to `fresh` wherever
/// it binds. A "for all", a "there is" and a set-builder over a domain bind
/// their letter in their body and not in the domain, which keeps any letter
/// of its own spelt as it is; any other binder has the letter moved
/// throughout.
fn moved_letter(term: &Term, place: usize, fresh: &Term) -> Option<Term> {
    let letter = term.children()[place].variable()?.to_string();
    let over_a_domain = matches!(term.label(), Some("wral" | "wrex" | "crab"))
        && term.children().len() == 3
        && place == 1;
    let kids = term.children();
    let moved = kids
        .iter()
        .enumerate()
        .map(|(at, kid)| {
            if at == place {
                fresh.clone()
            } else if over_a_domain && at == 2 {
                kid.clone()
            } else {
                free_moved(kid, &letter, fresh)
            }
        })
        .collect();
    Some(term.with_children(moved))
}

/// `term` with each free occurrence of `letter` made `fresh`. A part that
/// binds the letter itself, which set.mm writes with the letter as an
/// operand of its own and not under `cv`, keeps it: a map given for F that
/// binds n still binds n when an outer n is moved.
fn free_moved(term: &Term, letter: &str, fresh: &Term) -> Term {
    if let Some(v) = term.variable() {
        return if v == letter {
            fresh.clone()
        } else {
            term.clone()
        };
    }
    let binds_it = term.label() != Some("cv")
        && term.children().iter().any(|c| c.variable() == Some(letter));
    if binds_it {
        return term.clone();
    }
    term.with_children(
        term.children()
            .iter()
            .map(|c| free_moved(c, letter, fresh))
            .collect(),
    )
}
