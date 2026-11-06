//! The Lean document model: what the Lean writer builds before any text.
//!
//! A term is a tree whose nodes carry their Lean type, a constant names
//! where it comes from, and a proof is a list of tactics, so that what a
//! file imports, which form a count takes and whether two statements
//! agree are read from the tree. Text is made in one place, the printer
//! (`print`), which brackets by precedence as Lean reads.

pub mod print;
pub mod skeleton;
pub mod tactic;
pub mod term;

pub use tactic::{Proof, Tactic, TacticRef};
pub use term::{
    Arg, Assoc, ConstRef, CountForm, LeanType, Op, Quant, Source, Term, TermKind,
};
