//! What the checker records of what the lines in scope say of terms and
//! letters (`docs/CHECKER.md`, `bounds`, `statement_bounds`, `finite_at`,
//! `element_systems`, `function_systems`), as the Lean writer reads it.

use std::path::Path;

use parley::checker::record::CheckedTheorem;
use parley::checker::{checked_where, CheckedCorpus};
use parley::source::Disk;

const PRODUCT_CONSTANT: &str = "stdlib/sums/product-constant";
const BOUND_BY_ALGEBRA: &str =
    "tests/elaborator/reading-memberships/a-membership-bound-read-by-algebra";
const CONGRUENCE_CHAIN: &str = "tests/elaborator/a-congruence-chain-opening-with-an-equation/a-congruence-chain-opening-with-an-equation";
const RATIONAL_TIMES_IRRATIONAL: &str =
    "proofs/hammack/rational-times-irrational/rational-times-irrational";

/// The checker's records of these theorems, as the build reads them.
fn read(names: &[&str]) -> CheckedCorpus {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    match checked_where(&Disk::new(root.to_path_buf()), |n| names.contains(&n)) {
        Ok(read) => read,
        Err(said) => panic!("the corpus does not check:\n{}", said.complained),
    }
}

/// The index of the step numbered `number` in the theorem `name`.
fn step_index(read: &CheckedCorpus, name: &str, number: &str) -> usize {
    let thm = read
        .corpus
        .theorems
        .iter()
        .find(|t| t.qualified() == name)
        .expect("the theorem is read");
    thm.steps
        .iter()
        .position(|s| s.number.to_string() == number)
        .expect("the step is there")
}

/// Each term the bounds say is at least a number, as printed, with it.
fn bounded(
    read: &CheckedCorpus,
    said: &parley::citing::bounds::SaidBounds,
) -> Vec<(String, i64)> {
    said.terms
        .iter()
        .map(|b| (read.grammar.print(&b.term), b.least))
        .collect()
}

#[test]
fn a_hypothesis_bounds_its_letter_below() {
    let read = read(&[BOUND_BY_ALGEBRA]);
    let record: &CheckedTheorem = &read.theorems[BOUND_BY_ALGEBRA];
    // H2 says x ∈ ℕ: x is at least 1.
    let said = bounded(&read, &record.statement_bounds);
    assert!(said.contains(&("x".to_string(), 1)), "{said:?}");
    // And so at step 1, whose scope holds H2.
    let at = bounded(&read, &record.bounds[0]);
    assert!(at.contains(&("x".to_string(), 1)), "{at:?}");
}

#[test]
fn a_part_of_a_finite_set_is_finite_in_the_steps_it_is_in_scope() {
    let read = read(&[PRODUCT_CONSTANT]);
    let record = &read.theorems[PRODUCT_CONSTANT];
    // Inside the induction's step part, `let Y ⊆ X` with X finite (H2):
    // Y is finite at 1.5.
    let i = step_index(&read, PRODUCT_CONSTANT, "1.5");
    assert!(
        record.finite_at[i].contains_key("Y"),
        "{:?}",
        record.finite_at[i]
    );
    // At step 1, which owns the induction, no line in scope lets Y.
    assert!(
        !record.finite_at[0].contains_key("Y"),
        "{:?}",
        record.finite_at[0]
    );
}

#[test]
fn a_letter_in_a_set_of_numbers_takes_the_widest_system() {
    let read = read(&[RATIONAL_TIMES_IRRATIONAL]);
    let record = &read.theorems[RATIONAL_TIMES_IRRATIONAL];
    // a is let in ℝ and assumed in ℚ: ℝ is the wider.
    assert_eq!(record.element_systems.get("a").map(|s| s.sign()), Some("ℝ"));
}

#[test]
fn an_items_hypotheses_make_its_sets_finite_and_bound_its_terms() {
    let read = read(&[]);
    // finite-part asks X is finite.
    let facts = &read.library.item_facts["stdlib/counting/finite-part"];
    assert!(
        facts.iter().any(|g| g.finite.sets.contains_key("X")),
        "{:?}",
        facts.iter().map(|g| &g.finite.sets).collect::<Vec<_>>()
    );
    // real-power-positive asks its base above 0.
    let facts = &read.library.item_facts["stdlib/numbers/real-power-positive"];
    assert!(
        facts.iter().any(|g| !g.bounds.terms.is_empty()),
        "{facts:?}"
    );
}

#[test]
fn a_function_typed_between_number_systems_records_both() {
    let read = read(&[CONGRUENCE_CHAIN]);
    let record = &read.theorems[CONGRUENCE_CHAIN];
    // H4 says f : ℤ → ℝ.
    let between = record.function_systems.get("f").expect("f is typed");
    assert_eq!((between.from.sign(), between.to.sign()), ("ℤ", "ℝ"));
}
