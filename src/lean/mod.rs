//! The Lean backend: the corpus as the checker read it, written as Lean
//! files over Mathlib (`LEAN.md`).
//!
//! The writer reads trees from the checker's record and parses nothing, as
//! the Metamath build does not; clippy denies it the parser's entry points
//! (`clippy.toml`).
#![deny(clippy::disallowed_methods)]

pub mod algebra;
pub mod coverage;
pub mod doc;
pub mod export;
pub mod expr;
pub mod items;
pub mod modules;
pub mod names;
pub mod readback;
pub mod sets;
pub mod statement;
pub mod tactics;
pub mod templates;
pub mod theorem;
