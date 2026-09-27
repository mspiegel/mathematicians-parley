//! The checker and elaborator for the readable proof layer over Metamath.
//!
//! `parley check` reads the corpus against the grammar and reports every
//! defect it finds. `parley build` elaborates every readable proof into a
//! Metamath file. `parley gate` is everything that must be green before a
//! commit: the checker, a fresh build compared with the files committed, the
//! set.mm labels the database names, that every library item is cited or
//! tested, that nothing is taken as stated unrecorded, and an external
//! verifier over every proof.

pub mod outcome;
pub mod source;
pub mod text;

pub use outcome::{Built, Checked, Decline, Declined, Problem, Route};
