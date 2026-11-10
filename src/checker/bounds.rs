//! What the lines in scope at each step bound below (`citing::bounds`), as
//! the checker reads them: the statement's hypotheses, and the lines a step
//! may cite (`CheckedTheorem::bounds`). A backend that writes a square root
//! or a real power as a real one where its base is at least 0 takes that
//! from here.

use crate::citing::bounds::{self, BoundsAsk, SaidBounds};
use crate::citing::{index_system, Introduced};
use crate::formula::Node;
use crate::matching::Context;
use crate::notations::{APPLICATION, INTEGER_RANGE, PRODUCT, SUM};
use crate::rules::System;

/// The checker's view for the bounds rule: the letters in scope, what the
/// lines bound, and how a sum is read.
struct ScopeAsk<'a> {
    letters: Introduced,
    said: SaidBounds,
    ctx: &'a Context,
}

impl BoundsAsk for ScopeAsk<'_> {
    fn bounds(&self) -> &SaidBounds {
        &self.said
    }

    fn same(&self, a: &Node, b: &Node) -> bool {
        crate::matching::alike_top(
            &crate::matching::standard(a, self.ctx),
            &crate::matching::standard(b, self.ctx),
            self.ctx,
        )
    }

    fn natural_letter(&self, letter: &str) -> bool {
        matches!(self.letters.get(letter), Some(System::N | System::N0))
    }

    fn summed_nonnegative(&self, node: &Node) -> bool {
        let Some(summed) = Summed::of(node) else {
            return false;
        };
        if !summed.index.is_name() {
            return false;
        }
        let mut letters = self.letters.clone();
        letters.shift_remove(&*summed.index.text);
        if let Some((from, _)) = summed.range {
            if let Some(s @ (System::N | System::N0)) = index_system(from) {
                letters.insert(summed.index.text.to_string(), s);
            }
        }
        let inner = ScopeAsk {
            said: bounds::inside_sum(self, summed.index, summed.range),
            letters,
            ctx: self.ctx,
        };
        bounds::nonnegative(&inner, summed.term)
    }

    fn exponential(&self, node: &Node) -> bool {
        node.notation() == APPLICATION
            && node.children.first().is_some_and(|f| &*f.text == "exp")
    }
}

/// A sum or a product taken apart: its index, the range it runs over where
/// it runs over one, and its term.
struct Summed<'n> {
    index: &'n Node,
    range: Option<(&'n Node, &'n Node)>,
    term: &'n Node,
}

impl<'n> Summed<'n> {
    fn of(node: &'n Node) -> Option<Summed<'n>> {
        match (node.notation(), node.children.as_slice()) {
            (SUM | PRODUCT, [index, from, to, term]) => Some(Summed {
                index,
                range: Some((from, to)),
                term,
            }),
            (_, [index, set, term])
                if matches!(&*node.notation_name(), "sum-over" | "product-over") =>
            {
                let range = match (set.notation(), set.children.as_slice()) {
                    (INTEGER_RANGE, [from, to]) => Some((from, to)),
                    _ => None,
                };
                Some(Summed { index, range, term })
            }
            _ => None,
        }
    }
}

/// What `lines` bound below, read with `letters` (`bounds::from_lines`).
pub fn said_by(lines: &[Node], letters: &Introduced, ctx: &Context) -> SaidBounds {
    let ask = ScopeAsk {
        letters: letters.clone(),
        said: SaidBounds::default(),
        ctx,
    };
    let lines: Vec<&Node> = lines.iter().collect();
    let mut out = SaidBounds::default();
    bounds::from_lines(&ask, &lines, &mut out);
    out
}

/// Whether a number is at least 1 by the letters in scope and what the lines
/// bound (`citing::bounds::least`): 2, n of an n ∈ ℕ, k + 1 of a k ∈ ℕ₀, or
/// a term a line says is at least 1. What a count given as a number must be
/// to make its set finite (`citing::finite::finite_sets`).
pub fn positive_by<'a>(
    letters: &Introduced,
    said: &SaidBounds,
    ctx: &'a Context,
) -> impl Fn(&Node) -> bool + 'a {
    let ask = ScopeAsk {
        letters: letters.clone(),
        said: said.clone(),
        ctx,
    };
    move |n: &Node| bounds::least(&ask, n).is_some_and(|least| least >= 1)
}
