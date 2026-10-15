//! Each method's procedure, the half `METHODS.md` calls "The procedure":
//! what decides whether a step the method names holds. The proof each one
//! expands to, the other half, is the build's (`crate::elab`).
//!
//! The deciders read kernel terms and nothing of set.mm but the labels'
//! shapes, so the checker can run them without loading the library.

pub mod algebra;
pub mod field;
pub mod inequalities;
pub mod inspection;
pub mod linear;
pub mod membership;
pub mod numerals;
pub mod terms;
