//! What the checker records of the "for all" lines a step reads at a
//! block's letter (`docs/CHECKER.md`, `read_at`), as the Lean writer reads
//! it.

use std::path::Path;

use parley::checker::{checked_where, CheckedCorpus};
use parley::source::Disk;

const TRANSITIVITY: &str =
    "tests/elaborator/reading-block-letters/a-for-all-line-in-a-transitivity";

/// The checker's records of these theorems, as the build reads them.
fn read(names: &[&str]) -> CheckedCorpus {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    match checked_where(&Disk::new(root.to_path_buf()), |n| names.contains(&n)) {
        Ok(read) => read,
        Err(said) => panic!("the corpus does not check:\n{}", said.complained),
    }
}

#[test]
fn a_for_all_line_is_read_at_the_letter_of_the_block_around_the_step() {
    let read = read(&[TRANSITIVITY]);
    let record = &read.theorems[TRANSITIVITY];
    // Step 1.1 stands in the block letting y ∈ ℝ, and H2 says "for all x ∈
    // ℝ, x < x + 1": the step reads H2 at y.
    let at: Vec<(String, String)> = record.read_at[1]
        .iter()
        .map(|r| (read.grammar.print(&r.said), read.grammar.print(&r.letter)))
        .collect();
    assert!(
        at.iter().any(|(s, l)| s.contains("x < x + 1") && l == "y"),
        "{at:?}"
    );
    // Step 1, which owns the block, stands outside it: no line is read at y.
    assert!(
        record.read_at[0]
            .iter()
            .all(|r| read.grammar.print(&r.letter) != "y"),
        "{:?}",
        record.read_at[0].len()
    );
}
