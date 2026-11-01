//! The Lean backend: the corpus as the checker read it, written as Lean
//! files over Mathlib (`LEAN.md`).
//!
//! The writer reads trees from the checker's record and parses nothing, as
//! the Metamath build does not; clippy denies it the parser's entry points
//! (`clippy.toml`).
#![deny(clippy::disallowed_methods)]

pub mod algebra;
pub mod coverage;
pub mod expr;
pub mod items;
pub mod names;
pub mod statement;
pub mod templates;
pub mod theorem;
