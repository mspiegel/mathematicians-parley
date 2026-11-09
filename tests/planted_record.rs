//! The elaborator takes what the checker recorded and does not find it
//! again (`docs/ELABORATION.md`, what the elaborator takes from the
//! checker).
//!
//! A step's record is changed after checking, and the theorem elaborated
//! from the changed record. An elaborator that read the record builds from
//! the change, and here reports it; one that found the fact again would
//! build as before and not notice. The theorem must elaborate from its
//! record as checked, or the case tests nothing.

use std::path::Path;

use parley::corpus::Method;
use parley::elab::elaborate::Options;
use parley::source::{Disk, Memory};
use parley::tools::build::{checked_in, library, Loaded};

/// An instantiate step reads "for all x ∈ ℝ, x·0 = 0", the second sentence
/// of H3.
const THEOREM: &str =
    "tests/elaborator/reading-sentences/a-second-sentence-instantiated";

#[test]
fn the_elaborator_takes_the_instance_the_checker_recorded() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let library = library(root, None).expect(
        "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
    );
    let tree = Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap();

    let checked = checked_in(&tree, |n| n == THEOREM).expect("the theorem checks");
    if let Err(why) = Loaded::with_checked(&tree, checked).elaborate(
        THEOREM,
        &library,
        Options::default(),
    ) {
        panic!("{THEOREM} does not elaborate from its record as checked: {why}");
    }

    // The record changed: the instance is read from an equation of the
    // page, a = 1 or b·0 = 0, which reads where the step stands and is no
    // "for all".
    let mut planted = checked_in(&tree, |n| n == THEOREM).expect("the theorem checks");
    let equation = planted
        .theorems
        .get(THEOREM)
        .and_then(|t| {
            t.page
                .entries()
                .map(|(_, node)| node)
                .find(|node| node.notation() == parley::notations::EQUALITY)
                .cloned()
        })
        .expect("the page writes an equation");
    let line = planted
        .corpus
        .theorems
        .iter()
        .find(|t| t.qualified() == THEOREM)
        .and_then(|t| t.steps.iter().find(|s| s.just.head.is(Method::Instantiate)))
        .map(|s| s.just.line)
        .expect("the theorem instantiates");
    let record = planted
        .theorems
        .get_mut(THEOREM)
        .and_then(|t| t.instantiated.get_mut(&line))
        .expect("the checker recorded the instance");
    record.at.written = equation;

    match Loaded::with_checked(&tree, planted).elaborate(THEOREM, &library, Options::default()) {
        Ok(_) => panic!(
            "{THEOREM} elaborated from a record naming no \"for all\": the elaborator found the instance itself"
        ),
        Err(problem) => assert!(
            problem.to_string().contains("which says no for all there"),
            "{THEOREM} failed otherwise than by the changed record: {problem}"
        ),
    }
}
