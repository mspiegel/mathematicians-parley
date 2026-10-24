//! Which power `x^y` is, settled once its sentence is read.
//!
//! `x^y` is written one way and means one of two things, as a reader takes
//! it (`GRAMMAR.md`): a product of copies where the exponent is whole,
//! set.mm's `↑`, and the principal power where it is not, set.mm's `↑𝑐`.
//! The parser reads every `^` as a power. What tells the two apart is the
//! exponent and what the lines above say of its letters, and a binder in
//! the same sentence says it of the letter it binds, so the choice is made
//! here, over the whole tree, where each binder's set is in sight.
//!
//! An exponent is whole unless it shows otherwise: it holds a division, a
//! value only `real arithmetic` works out (π, e, a root, ln, exp, sin,
//! cos), i, a letter put among numbers that need not be whole, or a function
//! said to take such values. A letter inside a function's argument does not
//! count, so 5^s(x) with x ∈ ℚ is whole.
//!
//! A root's index is read here too: ⁵√x is a root, and an index below 3 is
//! not one, √ being the square root.

use indexmap::IndexSet;

use crate::formula::notation::real_arithmetic_only;
use crate::formula::notation_id::Spelling;
use crate::formula::symbol::Symbol;
use crate::formula::{Grammar, Node, Sorts};
use crate::notations::{
    ABSOLUTE_VALUE, ADDITIVE, APPLICATION, APPLICATION_TO_TWO, CLOSED_INTERVAL,
    COMMA_CONJUNCTION, COMPLEXES, CONJUNCTION, DIVIDED, IMAGINARY_UNIT, IN,
    JUXTAPOSITION, MULTIPLICATIVE, OPEN_INTERVAL, POWER, RATIONALS, REALS, REAL_POWER,
    ROOT, SET_BUILDER, SUBSET, SUPERSCRIPT, UNARY_MINUS,
};
use crate::outcome::{Checked, Problem};

/// The sign a root is written with, whose raised index stands before it.
pub const ROOT_SIGN: &str = "√";

/// The least index a root written with one takes: √ alone is the square
/// root, and an index of 1 is no root.
const LEAST_INDEX: u32 = 3;

/// The tree with each power whose exponent is not whole made a real power,
/// or the problem with a root's index.
pub fn settled(
    node: &Node,
    g: &Grammar,
    sorts: &Sorts,
    path: &str,
    line: usize,
) -> Checked<Node> {
    let Some(real_power) = g
        .notations
        .iter()
        .find(|n| n.instead && n.key_id == REAL_POWER)
        .map(|n| n.spelling())
    else {
        return Ok(node.clone());
    };
    let mut settling = Settling {
        g,
        sorts,
        bound: Vec::new(),
        real_power,
        path,
        line,
    };
    settling.node(node)
}

/// What the lines say of the names in a claim: a number or a set put among
/// numbers that need not be whole, or a function said to take such values,
/// is added to `reals`, and one put in a set of whole numbers taken out of
/// it, since a `let` says again what a letter is.
pub fn said_of(claim: &Node, reals: &mut IndexSet<String>) {
    let id = claim.notation();
    if id == CONJUNCTION || id == COMMA_CONJUNCTION {
        for part in &claim.children {
            said_of(part, reals);
        }
        return;
    }
    let said = if claim.spelling() == IN || id == SUBSET {
        claim.children.first().zip(claim.children.get(1))
    } else if super::types_a_function(claim) {
        claim.children.first().zip(claim.children.get(2))
    } else {
        None
    };
    let Some((name, set)) = said.filter(|(name, _)| name.is_name()) else {
        return;
    };
    if needs_not_be_whole(set, &|letter| reals.contains(letter)) {
        reals.insert(name.text.to_string());
    } else {
        reals.shift_remove(name.text.as_str());
    }
}

/// Whether a set holds numbers that need not be whole: ℚ, ℝ or ℂ, an
/// interval, a name `real` says such a set, or those of one of them with a
/// property.
pub fn needs_not_be_whole(set: &Node, real: &dyn Fn(&str) -> bool) -> bool {
    let spelling = set.spelling();
    if spelling == RATIONALS || spelling == REALS || spelling == COMPLEXES {
        return true;
    }
    let id = set.notation();
    if id == CLOSED_INTERVAL || id == OPEN_INTERVAL {
        return true;
    }
    if set.is_name() {
        return real(&set.text);
    }
    if id == SET_BUILDER {
        return set
            .children
            .get(1)
            .is_some_and(|within| needs_not_be_whole(within, real));
    }
    false
}

/// A walk over one tree, with what the binders around the part reached say
/// of the letters they bind.
struct Settling<'a> {
    g: &'a Grammar,
    sorts: &'a Sorts,
    /// The letters the binders around a part bind, innermost last, each
    /// with whether its set needs not be whole.
    bound: Vec<BoundLetter>,
    real_power: Spelling,
    path: &'a str,
    line: usize,
}

/// A letter a binder around a part binds.
struct BoundLetter {
    letter: Symbol,
    /// Whether the set it ranges over holds numbers that need not be whole.
    real: bool,
}

impl Settling<'_> {
    fn node(&mut self, node: &Node) -> Checked<Node> {
        if node.notation() == ROOT {
            self.check_index(node)?;
        }
        let binds = self.g.binders().get(&node.notation()).cloned();
        let pushed = self.bound.len();
        if let Some(binds) = &binds {
            for &held in &binds.held {
                let Some(letter) = node.children.get(held).filter(|c| c.is_name())
                else {
                    continue;
                };
                let over = node
                    .children
                    .get(held + 1)
                    .filter(|_| !binds.body.contains(&(held + 1)));
                let real = over.is_some_and(|set| {
                    needs_not_be_whole(set, &|name| self.letter_real(name))
                });
                self.bound.push(BoundLetter {
                    letter: letter.text,
                    real,
                });
            }
        }
        let mut children = Vec::with_capacity(node.children.len());
        let mut changed = false;
        for child in &node.children {
            let made = self.node(child)?;
            changed |= !made.same(child);
            children.push(made);
        }
        self.bound.truncate(pushed);
        let real = node.notation() == POWER
            && children.get(1).is_some_and(|e| self.shows_not_whole(e));
        if !real && !changed {
            return Ok(node.clone());
        }
        let made = if real {
            Node::of(self.real_power, node.sort.clone(), children)
        } else {
            node.with_children(children)
        };
        if let Some((from, to)) = node.span() {
            made.set_span(from, to);
        }
        if node.grouped() {
            made.set_grouped();
        }
        Ok(made)
    }

    /// Whether a letter is a number, a set or a function that needs not be
    /// whole: as the binder around it says, or else as the lines above do.
    fn letter_real(&self, name: &str) -> bool {
        if let Some(b) = self.bound.iter().rev().find(|b| b.letter == *name) {
            return b.real;
        }
        self.sorts.reals.contains(name)
            || self
                .sorts
                .ranges
                .get(name)
                .is_some_and(|set| ["ℚ", "ℝ", "ℂ"].contains(&set.as_str()))
    }

    /// Whether an exponent shows it is not whole (the module's comment).
    fn shows_not_whole(&self, e: &Node) -> bool {
        if e.is_name() {
            return self.letter_real(&e.text);
        }
        let id = e.notation();
        if e.spelling() == DIVIDED || [IMAGINARY_UNIT, ROOT, REAL_POWER].contains(&id) {
            return true;
        }
        let by_real_arithmetic = self
            .g
            .notations
            .iter()
            .any(|n| n.key_id == id && real_arithmetic_only(&n.decided));
        if by_real_arithmetic {
            return true;
        }
        if id == APPLICATION || id == APPLICATION_TO_TWO {
            return e.children.first().is_some_and(|f| self.real_valued(f));
        }
        let arithmetic = [
            ADDITIVE,
            MULTIPLICATIVE,
            UNARY_MINUS,
            JUXTAPOSITION,
            POWER,
            SUPERSCRIPT,
            ABSOLUTE_VALUE,
        ];
        arithmetic.contains(&id) && e.children.iter().any(|c| self.shows_not_whole(c))
    }

    /// Whether a function applied takes values that need not be whole: one
    /// the theorem introduces as its lines say, and one of the library's as
    /// its record does, a value only `real arithmetic` works out.
    fn real_valued(&self, f: &Node) -> bool {
        if !f.is_name() {
            return false;
        }
        if self.sorts.introduces(&f.text) {
            return self.letter_real(&f.text);
        }
        self.g
            .functions
            .get(f.text.as_str())
            .is_some_and(|said| real_arithmetic_only(&said.decided))
    }

    /// A root's index is 3 or more.
    fn check_index(&self, root: &Node) -> Checked<()> {
        let index = root.children.first();
        let value = index.and_then(|i| i.text.parse::<u32>().ok());
        if value.is_some_and(|v| v >= LEAST_INDEX) {
            return Ok(());
        }
        let written = index.map_or(String::new(), |i| i.text.to_string());
        Err(Problem::new(
            self.path,
            self.line,
            format!(
                "a root's index is {LEAST_INDEX} or more, and this one is {written}: the square root is √x, and x itself needs no root"
            ),
        ))
    }
}
