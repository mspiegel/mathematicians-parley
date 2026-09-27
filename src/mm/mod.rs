//! The Metamath side: reading a database's structure, the kernel's terms and
//! syntax, proofs as shared steps, and the compressed format they are
//! written in.

pub mod library;

pub use library::{read, read_texts, where_set_mm, Kind, Signature, Signatures};
