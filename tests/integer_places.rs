//! What the checker records of the whole numbers a step puts where a
//! notation asks one, and how it shows each is whole (`docs/CHECKER.md`,
//! `places_shown`, `members_shown`, `kind_letters`), as the Lean writer
//! reads it.
//!
//! The places come from the definitions (`Library::place_systems`): a
//! congruence and "is even" let their numbers in ℤ, so the terms a step puts
//! there are recorded with ℤ. A term beside an equation is recorded with the
//! equation, which the Lean writer turns into the term's witness.

use std::path::Path;

use parley::checker::record::{CheckedTheorem, ShownBy};
use parley::checker::{checked_where, CheckedCorpus};
use parley::source::Disk;

const WILSON: &str = "proofs/wiedijk/wilson/wilson";
const FIBONACCI: &str =
    "proofs/hammack/fibonacci-even-iff-three-divides/fibonacci-even-iff-three-divides";

/// The checker's records of these theorems, as the build reads them.
fn read(names: &[&str]) -> CheckedCorpus {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    match checked_where(&Disk::new(root.to_path_buf()), |n| names.contains(&n)) {
        Ok(read) => read,
        Err(said) => panic!("the corpus does not check:\n{}", said.complained),
    }
}

/// Each term the record says a step puts where a notation asks a number
/// system, as the page prints it, with the system's sign and whether it is
/// said, or shown beside an equation.
fn places(
    read: &CheckedCorpus,
    record: &CheckedTheorem,
) -> Vec<(String, String, bool)> {
    record
        .places_shown
        .iter()
        .flatten()
        .map(|p| {
            (
                read.grammar.print(&p.term),
                p.system.sign().to_string(),
                matches!(p.by, ShownBy::Said),
            )
        })
        .collect()
}

#[test]
fn a_congruence_asks_its_sides_whole_and_says_how() {
    let read = read(&[WILSON]);
    let record = &read.theorems[WILSON];
    // 5.7.2 puts a^(p − 1) in a congruence, said once by its requires line
    // p − 1 ∈ ℕ₀.
    let places = places(&read, record);
    assert!(
        places.contains(&("a^(p − 1)".to_string(), "ℤ".to_string(), true)),
        "{places:?}"
    );
    // 5.7.10's requires line a^(p − 1) ∈ ℤ is by `membership`, from 5.7.4
    // a^(p − 1) = a^(p − 2)·a: beside that equation.
    let beside: Vec<(String, String)> = record
        .members_shown
        .values()
        .filter_map(|p| match &p.by {
            ShownBy::Beside { equation, .. } => {
                Some((read.grammar.print(&p.term), read.grammar.print(equation)))
            }
            ShownBy::Said => None,
        })
        .collect();
    assert!(
        beside
            .iter()
            .any(|(t, e)| t == "a^(p − 1)" && e.contains("a^(p − 2)")),
        "{beside:?}"
    );
}

#[test]
fn a_function_saying_its_kind_reads_its_reason_at_its_argument() {
    let read = read(&[WILSON]);
    let record = &read.theorems[WILSON];
    // D1, f(a) = (a^(p − 2)) mod p, an integer, for a ∈ {2, …, p − 2}: its
    // reason is read with a in ℤ, as a member of its range, beside p.
    let letters = &record.kind_letters["D1"];
    assert_eq!(letters.get("a").map(|s| s.sign()), Some("ℤ"));
    assert_eq!(letters.get("p").map(|s| s.sign()), Some("ℕ"));
}

#[test]
fn even_asks_its_number_whole_and_no_membership_asks_anything() {
    let read = read(&[FIBONACCI]);
    let record = &read.theorems[FIBONACCI];
    let places = places(&read, record);
    // 5.14.8 puts F(3q + 1) under "is even", which lets its number in ℤ.
    assert!(
        places
            .iter()
            .any(|(t, s, _)| t == "F(3 · q + 1)" && s == "ℤ"),
        "{places:?}"
    );
    // The range's definition says k ∈ {a, …, b} of k ∈ ℤ, which defines the
    // range and asks nothing of what stands before ∈: no step's letter of a
    // range is recorded as put in a place.
    assert!(
        !places.iter().any(|(t, _, _)| t == "k" || t == "q"),
        "{places:?}"
    );
}
