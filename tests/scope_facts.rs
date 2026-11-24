//! What the checker records of what the lines in scope say of terms and
//! letters (`docs/CHECKER.md`, `bounds`, `statement_bounds`, `finite_at`,
//! `element_systems`, `function_systems`), as the Lean writer reads it.

use std::path::Path;

use parley::checker::record::CheckedTheorem;
use parley::checker::{checked_where, CheckedCorpus};
use parley::citing::bounds::SaidBounds;
use parley::citing::finite;
use parley::source::Disk;

const PRODUCT_CONSTANT: &str = "stdlib/sums/product-constant";
const BOUND_BY_ALGEBRA: &str =
    "tests/elaborator/reading-memberships/a-membership-bound-read-by-algebra";
const CONGRUENCE_CHAIN: &str = "tests/elaborator/a-congruence-chain-opening-with-an-equation/a-congruence-chain-opening-with-an-equation";
const BOTH_EVEN: &str =
    "proofs/hammack/both-even-from-product-and-sum/both-even-from-product-and-sum";
const REMAINDER_NONNEGATIVE: &str =
    "proofs/setmm/remainder-bounds/remainder-nonnegative";
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
fn bounded(read: &CheckedCorpus, said: &SaidBounds) -> Vec<(String, i64)> {
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
    let y = finite::name_key("Y");
    assert!(
        record.finite_at[i].contains_key(&y),
        "{:?}",
        record.finite_at[i]
    );
    // At step 1, which owns the induction, no line in scope lets Y.
    assert!(
        !record.finite_at[0].contains_key(&y),
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
        facts
            .iter()
            .any(|g| g.finite.sets.contains_key(&finite::name_key("X"))),
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

/// Where the record places `letter` at the step numbered `number`: the
/// line's reference and the sentence of it (`CheckedTheorem::introduced_at`).
fn placed_at(
    read: &CheckedCorpus,
    name: &str,
    number: &str,
    letter: &str,
) -> (String, Option<usize>) {
    let i = step_index(read, name, number);
    let at = read.theorems[name].introduced_at[i]
        .get(letter)
        .unwrap_or_else(|| panic!("{letter} has no place at step {number}"));
    (at.line.clone(), at.sentence)
}

#[test]
fn a_header_let_places_its_letter_at_its_label() {
    let read = read(&[BOTH_EVEN]);
    // H1 says a ∈ ℤ and H2 says b ∈ ℤ, each a sentence of its own.
    assert_eq!(
        placed_at(&read, BOTH_EVEN, "1", "a"),
        ("H1".to_string(), Some(0))
    );
    assert_eq!(
        placed_at(&read, BOTH_EVEN, "1", "b"),
        ("H2".to_string(), Some(0))
    );
}

#[test]
fn an_obtain_places_its_letter_at_its_step_from_the_steps_below_it() {
    let read = read(&[BOTH_EVEN]);
    // Step 2 says m ∈ ℤ in its first sentence; m is in scope from step 3.
    assert_eq!(
        placed_at(&read, BOTH_EVEN, "3", "m"),
        ("2".to_string(), Some(0))
    );
    let at_two = step_index(&read, BOTH_EVEN, "2");
    assert!(
        !read.theorems[BOTH_EVEN].introduced_at[at_two].contains_key("m"),
        "the obtain does not introduce m at its own step"
    );
}

#[test]
fn a_letter_obtained_in_each_case_is_placed_at_that_cases_obtain() {
    let read = read(&[BOTH_EVEN]);
    // Each case obtains its own j: at 3.1 in the first, at 3.5 in the second.
    assert_eq!(
        placed_at(&read, BOTH_EVEN, "3.2", "j"),
        ("3.1".to_string(), Some(0))
    );
    assert_eq!(
        placed_at(&read, BOTH_EVEN, "3.6", "j"),
        ("3.5".to_string(), Some(0))
    );
}

#[test]
fn a_kinds_define_places_its_name_at_the_defines_label() {
    let read = read(&[REMAINDER_NONNEGATIVE]);
    // D1, `let q = ⌊A/B⌋, an integer`, puts q in ℤ from the step after it.
    assert_eq!(
        placed_at(&read, REMAINDER_NONNEGATIVE, "2", "q"),
        ("D1".to_string(), Some(0))
    );
    let record = &read.theorems[REMAINDER_NONNEGATIVE];
    let at_two = step_index(&read, REMAINDER_NONNEGATIVE, "2");
    assert_eq!(
        record.introduced[at_two].get("q").map(|s| s.sign()),
        Some("ℤ"),
        "the place is of the system `introduced` gives"
    );
}
