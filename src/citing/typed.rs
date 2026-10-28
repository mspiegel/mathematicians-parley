//! The type a cited item asks of a function a `let` declares (`GRAMMAR.md`,
//! the function's type is a declaration): the item's type is not asked for
//! again, its codomain is. A function declared f : X → B has the type
//! f : X → C an item asks where B is C, a number system inside the number
//! system C, or a set a `let` puts inside C, as `let X ⊆ ℤ` puts X.
//!
//! The rule is written once, in `codomain_reason`, over a view of the two
//! codomains both tools give (`CodomainAsk`): the page's sentences in the
//! checker, and the build's kernel terms, which prove the reason given. So
//! the two tools agree on which declared types answer an item's.

use crate::rules::System;

/// Why a function declared with codomain B has the codomain C an item asks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CodomainReason {
    /// B and C are one set.
    Same,
    /// B is a number system inside the number system C, ℕ inside ℤ.
    Systems { small: System, big: System },
    /// A `let` puts B inside C: `let X ⊆ ℤ` for B = X, C = ℤ.
    Part,
}

/// What the rule asks of the two codomains, written once for both tools.
pub trait CodomainAsk {
    type T;
    /// Whether two sets are one as written.
    fn alike(&self, a: &Self::T, b: &Self::T) -> bool;
    /// The number system a set is, where it is one.
    fn system(&self, set: &Self::T) -> Option<System>;
    /// Whether a `let` puts `small` inside `big`.
    fn part(&self, small: &Self::T, big: &Self::T) -> bool;
}

/// Why a function declared with codomain `declared` has the codomain
/// `asked`; None where it need not.
pub fn codomain_reason<A: CodomainAsk>(
    ask: &A,
    declared: &A::T,
    asked: &A::T,
) -> Option<CodomainReason> {
    if ask.alike(declared, asked) {
        return Some(CodomainReason::Same);
    }
    if let (Some(small), Some(big)) = (ask.system(declared), ask.system(asked)) {
        return small
            .within(big)
            .then_some(CodomainReason::Systems { small, big });
    }
    ask.part(declared, asked).then_some(CodomainReason::Part)
}
