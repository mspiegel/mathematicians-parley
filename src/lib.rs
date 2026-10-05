//! The checker and elaborator for the readable proof layer over Metamath.
//!
//! `parley check` reads the corpus against the grammar and reports every
//! defect it finds. `parley build` elaborates every readable proof into a
//! Metamath file. `parley gate` is everything that must be green before a
//! commit: the checker, a fresh build compared with the files committed, the
//! set.mm labels the database names, that every library item is cited or
//! tested, that nothing is taken as stated unrecorded, and an external
//! verifier over every proof.

pub mod check;
pub mod citing;
pub mod corpus;
pub mod elab;
pub mod formula;
pub mod matching;
pub mod mm;
pub mod outcome;
pub mod proofs;
pub mod rules;
pub mod said;
pub mod sorts;
pub mod source;
pub mod targets;
pub mod text;
pub mod tools;

pub use outcome::{Built, Checked, Decline, Declined, Problem, Route};
