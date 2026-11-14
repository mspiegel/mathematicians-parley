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
use crate::formula::notation_id::NotationId;
use crate::formula::symbol::Symbol;
use crate::formula::{ByShape, Node};
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::mm::{Rpn, Signature};
use crate::outcome::{Built, Checked, Decline, Declined, Route};
use crate::rules::{self, discharge, lookup, Join, Side};
use crate::{pf, t, take};

mod applying;
mod classes;
mod closing;
mod facts;
mod lemmas;
mod pieces;
mod renaming;
mod rewriting;
mod standard;

use self::pieces::*;
pub use self::pieces::{as_class, conjuncts_of, sethood};

/// One rule of the standard form: its label, the side it rewrites, the side
/// it becomes, and the lemma's variables.
#[derive(Clone)]
pub struct Rewrite {
    pub label: String,
    pub given: Term,
    pub gives: Term,
    pub names: Vars,
}

/// A term with the two holes its notation puts in no order exchanged
/// (`Elaborator::pair_exchanged`).
struct PairExchanged {
    /// The lemma that exchanges them (`rules::PAIRS_EXCHANGED`).
    lemma: &'static str,
    term: Term,
    /// Whether the two stood out of the standard order.
    out_of_order: bool,
    /// The two as they stood, the first hole's and the second's.
    first: Term,
    second: Term,
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
    /// Two elements of a listed set of three or more exchanged, by the
    /// lemma of `rules::LISTED` named.
    Listed(&'static str),
    /// Two holes in no order put in order, `commutes any order of holes 1
    /// and 2`, by the lemma of `rules::PAIRS_EXCHANGED` named.
    Exchanged(&'static str),
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

// --- the facts at a scope, by standard form ---------------------------
