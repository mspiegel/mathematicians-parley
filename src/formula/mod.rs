//! Formulas, parsed from the notations declared in `corpus/db/notation.records`.
//!
//! `GRAMMAR.md`'s "Formulas" section is the specification. Nothing here knows
//! any notation by name: the patterns, their hole sorts, their precedence
//! levels and their associativity all come from the database, so adding a
//! notation is a database entry and never a change to this module.

pub mod grammar;
pub mod node;
pub mod notation;
pub mod token;

pub use grammar::{fits, holds, parse, parse_here, Grammar, Sorts, TERM_SORTS};
pub use node::{walk, Node, NodeId, Sort, Whole};
pub use notation::{
    binds_tighter, categories_of, patterns_of, Binds, Notation, Part, Tighter,
};
