//! Each method's procedure, the half `METHODS.md` calls "The procedure":
//! what decides whether a step the method names holds. The proof each one
//! expands to, the other half, is the build's (`crate::elab`).
//!
//! The deciders read kernel terms and nothing of set.mm but the labels'
//! shapes, so the checker can run them without loading the library.

pub mod field;
pub mod linear;
pub mod numerals;
pub mod terms;
