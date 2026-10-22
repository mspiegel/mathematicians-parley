//! Two pairs compared coordinate by coordinate (`METHODS.md`, Pairs):
//! (a, b) = (c, d) holds where a = c and b = d, and (a, b) ≠ (c, d) where
//! a ≠ c or b ≠ d. `arithmetic`, `real arithmetic`, `algebra` and
//! `inspection` each decide the two coordinates' equations as they decide
//! any of theirs, and the build carries what they show to the pairs
//! (`crate::elab::scopes`, `pairs_equal` and `pairs_apart`).

use crate::mm::kernel::Term;

/// A relation between two terms each written as a pair, `<. a , b >.`.
pub struct PairRelation {
    /// Whether the pairs are said to differ.
    pub apart: bool,
    /// Whether a difference is spelt `A =/= B` rather than `-. A = B`.
    pub spelt_ne: bool,
    /// The left pair's coordinates, a and b.
    pub left: [Term; 2],
    /// The right pair's coordinates, c and d.
    pub right: [Term; 2],
}

/// One of a pair's two coordinates.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Coordinate {
    First,
    Second,
}

impl Coordinate {
    pub const BOTH: [Coordinate; 2] = [Coordinate::First, Coordinate::Second];

    fn at(self) -> usize {
        match self {
            Coordinate::First => 0,
            Coordinate::Second => 1,
        }
    }
}

/// The relation `claim` states between two pairs, where it is `=` or `≠`
/// with a pair on each side; None for any other claim.
pub fn relation(claim: &Term) -> Option<PairRelation> {
    let (apart, spelt_ne, equation) = match (claim.label(), claim.children()) {
        (Some("wn"), [inner]) if inner.label() == Some("wceq") => (true, false, inner),
        (Some("wne"), _) => (true, true, claim),
        (Some("wceq"), _) => (false, false, claim),
        _ => return None,
    };
    let [one, other] = equation.children() else {
        return None;
    };
    Some(PairRelation {
        apart,
        spelt_ne,
        left: coordinates(one)?,
        right: coordinates(other)?,
    })
}

/// A pair's two coordinates.
fn coordinates(term: &Term) -> Option<[Term; 2]> {
    match (term.label(), term.children()) {
        (Some("cop"), [a, b]) if term.variable().is_none() => {
            Some([a.clone(), b.clone()])
        }
        _ => None,
    }
}

impl PairRelation {
    /// The equation of the coordinates at `at`, a = c or b = d.
    pub fn equation(&self, at: Coordinate) -> Term {
        let i = at.at();
        Term::apply("wceq", vec![self.left[i].clone(), self.right[i].clone()])
    }

    /// The denial of that equation, ¬ a = c: what a coordinate's
    /// difference is, as the page's ≠ spells it.
    pub fn denial(&self, at: Coordinate) -> Term {
        Term::apply("wn", vec![self.equation(at)])
    }

    /// The left pair's coordinate at `at`.
    pub fn left_at(&self, at: Coordinate) -> &Term {
        &self.left[at.at()]
    }

    /// The right pair's coordinate at `at`.
    pub fn right_at(&self, at: Coordinate) -> &Term {
        &self.right[at.at()]
    }

    /// Whether the relation holds, given whether each coordinate's
    /// equation does.
    pub fn holds(&self, first: bool, second: bool) -> bool {
        (first && second) != self.apart
    }

    /// The coordinate a difference is shown at: the first whose equation
    /// `equal` finds false. None where it finds neither false.
    pub fn apart_at(
        &self,
        equal: &mut dyn FnMut(&Term) -> Option<bool>,
    ) -> Option<Coordinate> {
        Coordinate::BOTH
            .into_iter()
            .find(|&at| equal(&self.equation(at)) == Some(false))
    }
}
