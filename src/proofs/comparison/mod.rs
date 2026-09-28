//! The hand-written proofs `ELABORATION.md` compares the elaborated ones
//! with.
//!
//! Each is one theorem of the corpus, or a step of one, written out as
//! Metamath by hand in reverse Polish, with each readable step a named value
//! so the correspondence between the proof text and the expansion stays
//! visible. They read nothing: every term is built here with the
//! constructors in `mm::spell`, and each file is written to
//! `corpus/elaboration/<name>.mm`.

pub mod abs_bounds;
pub mod algebra;
pub mod parity;
pub mod sqrt2;
pub mod sum_formula;

/// One comparison file: the name it is written under, and its text.
pub struct Comparison {
    pub name: &'static str,
    pub text: fn() -> String,
}

/// Every comparison, in the order they are reported.
pub const COMPARISONS: [Comparison; 5] = [
    Comparison {
        name: "abs-bounds",
        text: abs_bounds::text,
    },
    Comparison {
        name: "algebra",
        text: algebra::text,
    },
    Comparison {
        name: "parity",
        text: parity::text,
    },
    Comparison {
        name: "sqrt2",
        text: sqrt2::text,
    },
    Comparison {
        name: "sum-formula",
        text: sum_formula::text,
    },
];
