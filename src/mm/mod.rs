//! The Metamath side: reading a database's structure, the kernel's terms and
//! syntax, proofs as shared steps, and the compressed format they are
//! written in.

pub mod compress;
pub(crate) mod kernel;
pub(crate) mod library;
pub mod rpn;
pub mod spell;

pub use kernel::{FloatLabels, Syntax, Term};
pub use library::{
    read, read_texts, where_set_mm, Kind, Layered, Lookup, Signature, Signatures,
};
pub use rpn::{Rpn, Spell};
pub use spell::{Builder, Part, Proof, Step, StepRef};
