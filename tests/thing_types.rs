//! Which of a theorem's sets hold things of one type, as the checker records
//! it (`docs/CHECKER.md`, `thing_types`) and the Lean writer gives each its
//! type variable: a product's two sides, and a pair's, are of two types
//! where nothing the page says joins them, as a map's sides are.

use std::path::Path;

use parley::checker::{checked_where, CheckedCorpus};
use parley::citing::things::Things;
use parley::source::Disk;

const PAIRS: &str = "tests/elaborator/products-of-two-types/a-set-of-pairs";
const PART: &str =
    "tests/elaborator/products-of-two-types/a-pair-of-a-member-and-a-part";

/// The checker's records of these theorems, as the build reads them.
fn read(names: &[&str]) -> CheckedCorpus {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    match checked_where(&Disk::new(root.to_path_buf()), |n| names.contains(&n)) {
        Ok(read) => read,
        Err(said) => panic!("the corpus does not check:\n{}", said.complained),
    }
}

#[test]
fn a_set_of_pairs_holds_pairs_of_its_product_s_two_types() {
    let read = read(&[PAIRS]);
    let things = &read.theorems[PAIRS].thing_types;
    // S ⊆ X × Y, (a, b) ∈ S: X and a of one type, Y and b of another.
    let (x, y) = (things.of_letter("X"), things.of_letter("Y"));
    assert_ne!(x, y);
    assert_eq!(things.of_letter("a"), x);
    assert_eq!(things.of_letter("b"), y);
    // S holds pairs of X's things and Y's.
    assert_eq!(
        things.things_of_letter("S"),
        Things::Pairs(Box::new(Things::Var(x)), Box::new(Things::Var(y)))
    );
}

#[test]
fn a_product_of_a_set_and_its_parts_keeps_one_type() {
    let read = read(&[PART]);
    let things = &read.theorems[PART].thing_types;
    // (a, B) ∈ X × 𝒫X, a ∈ X, B ⊆ X: a, B and X all of X's things, the
    // second side holding sets of them.
    let x = things.of_letter("X");
    assert_eq!(things.of_letter("a"), x);
    assert_eq!(things.of_letter("B"), x);
    assert_eq!(things.things_of_letter("X"), Things::Var(x));
}
