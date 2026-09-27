//! Proofs written as Metamath directly, below the readable layer.
//!
//! The corpus supplies an item in one of three ways: a set.mm label, a proof
//! file in the readable layer, or a Metamath proof here, for what set.mm does
//! not state and the readable layer cannot. `stdlib` holds those, each group
//! written in a block of its own. `comparison` holds the hand-written proofs
//! `ELABORATION.md` compares the elaborated ones with.
//!
//! Proofs are built rather than written. A Metamath proof is a flat sequence
//! of labels in reverse Polish, and `Builder::ap` assembles one from a label
//! and what it is applied to, so a statement is written once, in the
//! notation set.mm writes it in, and never transcribed into stack order by
//! hand.

pub mod stdlib;

use crate::mm::Proof;

/// One lemma: its label, its statement, its proof, and the hypotheses it
/// states, as (label, statement) pairs.
pub struct Lemma {
    pub label: String,
    pub statement: String,
    pub proof: Proof,
    pub hyps: Vec<(String, String)>,
}

impl Lemma {
    pub fn new(label: &str, statement: impl Into<String>, proof: Proof) -> Lemma {
        Lemma {
            label: label.to_string(),
            statement: statement.into(),
            proof,
            hyps: Vec::new(),
        }
    }

    pub fn with_hyps(mut self, hyps: &[(&str, &str)]) -> Lemma {
        self.hyps = hyps
            .iter()
            .map(|(l, s)| (l.to_string(), s.to_string()))
            .collect();
        self
    }
}
