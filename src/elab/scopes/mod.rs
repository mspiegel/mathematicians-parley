//! Scopes: the context each line of a proof is proved under.
//!
//! This is the second of the elaborator's six parts (`ELABORATION.md`, "How
//! the elaborator is built"). Given the blocks, hypotheses, cases and
//! `define` lines, it produces the context each line is proved under,
//! carries a fact into an inner scope, and closes a block into the claim it
//! owns. This is working in deduction form.
//!
//! Every scope is a conjunction of what has been assumed, and `frames` keeps
//! one entry per assumption: the scope with it conjoined, the assumption,
//! and what was known there. A step whose lemma forbids an inner assumption
//! is proved at an outer frame and carried back in.

use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::IndexMap;

use super::elaborate::{Given, Reading, Sides};
use super::reading::CLASS_NAMES;
use super::state::{
    number_of, Binding, Block, BlockLetter, ByPart, Closer, Contradicted, DefineCloser,
    Elaborator, Frame, ObtainCloser, PartEnd, ProvedClaim,
};
use super::{Facts, Line};
use crate::checker::record::{self, CheckedTheorem};
use crate::corpus::proof::PartBy;
use crate::corpus::{
    define_parts, DefineParts, Head, Intro, Item, Justification, Kinded, Method,
    Opener, Step,
};
use crate::formula::page::{made_as, Written};
use crate::formula::symbol::Symbol;
use crate::formula::Node;
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::mm::{Rpn, Signature};
use crate::notations::{AND, EQUAL_CHAIN, FUNCTION_TYPE, IN};
use crate::outcome::{Built, Checked, Declined, Route};
use crate::rules::{self, lookup};
use crate::{binds, pf, t, take};

mod closing;
mod obtaining;
mod opening;

/// One opener of a `proof` block, as its claim says it: a name fixed over a
/// set, or over every set, or an assumption.
pub(crate) struct OpenerLayer {
    /// The lemma that gives the layer back where the block closes:
    /// `ralrimiva`, `alrimiv` or `ex`.
    pub how: &'static str,
    /// The setvar fixed, or the formula assumed.
    pub what: Rpn,
    /// The set a fixed name runs over, where there is one.
    pub over: Option<Rpn>,
}

/// A set of functions, as kernel terms: the functions from `domain` to
/// `codomain`.
struct FunctionSet {
    domain: Rpn,
    codomain: Rpn,
}

/// A contradiction block's ends, as set.mm writes them: what it supposes,
/// what it claims, and ( scope -> ( supposed -> claim ) ), which the block's
/// last step and the line it contradicts give (`supposed_otherwise`).
#[derive(Clone, Copy)]
struct Supposed<'s> {
    supposed: &'s Rpn,
    claim: &'s Rpn,
    lifted: &'s Proof,
}

/// What proves a claim under a widened scope, given the claim, the scope and
/// what is known there.
pub type Prove<'p, 'a> =
    dyn FnMut(&mut Elaborator<'a>, &Term, &Rpn, &Facts) -> Checked<Route<Proof>> + 'p;

/// A letter one statement binds and the letter the other binds in its
/// place, within the constructor that binds them (`rebound`).
struct BoundPair {
    stated: String,
    claimed: String,
}

/// `rebound` over two terms, with the pairs of letters the constructors
/// around them bind, innermost last.
fn alike_rebound(
    one: &Term,
    two: &Term,
    bound: &mut Vec<BoundPair>,
    setvar: &dyn Fn(&str) -> bool,
) -> bool {
    if one.variable().is_some() || two.variable().is_some() {
        let (Some(a), Some(b)) = (one.variable(), two.variable()) else {
            return false;
        };
        // The innermost binder of either letter decides: bound, they must be
        // its pair; free on both sides, they must be the one letter.
        return match bound.iter().rev().find(|p| p.stated == a || p.claimed == b) {
            Some(p) => p.stated == a && p.claimed == b,
            None => a == b,
        };
    }
    if one.label() != two.label() || one.children().len() != two.children().len() {
        return false;
    }
    let at = bound.len();
    if one.label() != Some("cv") {
        for (a, b) in one.children().iter().zip(two.children()) {
            if let (Some(a), Some(b)) = (a.variable(), b.variable()) {
                if setvar(a) && setvar(b) {
                    bound.push(BoundPair {
                        stated: a.to_string(),
                        claimed: b.to_string(),
                    });
                }
            }
        }
    }
    let same = one
        .children()
        .iter()
        .zip(two.children())
        .all(|(a, b)| alike_rebound(a, b, bound, setvar));
    bound.truncate(at);
    same
}

/// What on the page a block's assumption is: its label where the text gives
/// one, and where it does not, the block's own step, since that is where a
/// reader finds it.
pub fn assumption(block: &Block, label: &str) -> String {
    if !label.is_empty() {
        return label.to_string();
    }
    format!("{} assumes", number_of(&block.owner))
}

/// A conjunction's two sides, each with its proof under one scope.
struct Halves {
    left: Rpn,
    right: Rpn,
    /// Proves `left`.
    first: Proof,
    /// Proves `right`.
    second: Proof,
}

/// How many things the sentences `said` write, joined by "and" at kernel
/// level: one for a sentence, and for a chain of equations one for each
/// equation between neighbouring terms.
pub fn written_parts(said: &[Node]) -> usize {
    said.iter()
        .map(|s| match s.notation() {
            EQUAL_CHAIN => s.children.len().saturating_sub(1),
            _ => 1,
        })
        .sum()
}
