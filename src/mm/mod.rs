//! The Metamath side: reading a database's structure, the kernel's terms and
//! syntax, proofs as shared steps, and the compressed format they are
//! written in.

pub mod compress;
pub mod kernel;
pub mod library;
pub mod spell;

pub use kernel::{FloatLabels, Syntax, Term};
pub use library::{read, read_texts, where_set_mm, Kind, Signature, Signatures};
pub use spell::{Builder, Part, Proof, Step, StepRef};
