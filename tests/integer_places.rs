//! What the checker records of the whole numbers a step puts where a
//! notation asks one, and how it shows each is whole (`docs/CHECKER.md`,
//! `places_shown`, `members_shown`), and of the numbers the lines give a
//! define (`define_values`), as the Lean writer reads it.
//!
//! The places come from the definitions (`Library::place_systems`): a
//! congruence and "is even" let their numbers in ℤ, so the terms a step puts
//! there are recorded with ℤ. A term beside an equation is recorded with the
//! equation, which the Lean writer turns into the term's witness.

use std::path::Path;

use parley::checker::record::{CheckedTheorem, LinesHold, ShownBy};
use parley::checker::{checked_where, CheckedCorpus};
use parley::source::Disk;

const WILSON: &str = "proofs/wiedijk/wilson/wilson";
const RATIONALS: &str = "proofs/wiedijk/rationals-countable/rationals-countable";
const FIBONACCI: &str =
    "proofs/hammack/fibonacci-even-iff-three-divides/fibonacci-even-iff-three-divides";
const WITNESS: &str =
    "tests/elaborator/a-divides-fold-with-its-witness/a-divides-fold-with-its-witness";

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
            ShownBy::Beside(b) => {
                Some((read.grammar.print(&p.term), read.grammar.print(&b.equation)))
            }
            ShownBy::Said | ShownBy::Typed { .. } | ShownBy::Define { .. } => None,
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
fn a_define_takes_its_numbers_from_the_lines_that_say_them() {
    let read = read(&[RATIONALS]);
    let record = &read.theorems[RATIONALS];
    let said = |name: &str| -> Vec<(String, bool)> {
        record.define_values[name]
            .iter()
            .map(|v| (v.system.sign().to_string(), v.typed))
            .collect()
    };
    // f(n) = n, for n ∈ ℕ: line 1, f : ℕ → ℚ, gives f its type, wider than
    // its rule's integers.
    assert_eq!(said("f"), vec![("ℚ".to_string(), true)]);
    // g(x) = 2^|numer(x)|·3^denom(x)·5^s(x), for x ∈ ℚ: line 5 says its
    // values are natural numbers, and line 6 gives it the type.
    assert_eq!(
        said("g"),
        vec![("ℕ".to_string(), false), ("ℕ".to_string(), true)]
    );
    // s, by cases of numerals, is given no numbers by any line.
    assert!(!record.define_values.contains_key("s"));
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

/// Each part the record says a reason's lines hold, by the reason's line:
/// the part as the page prints it, the system's sign, and the line stating
/// it, where one does.
fn held(
    read: &CheckedCorpus,
    record: &CheckedTheorem,
) -> Vec<(usize, String, String, String)> {
    record
        .held_by_lines
        .iter()
        .flat_map(|(line, held)| held.iter().map(move |h| (*line, h)))
        .map(|(line, h)| {
            let stated = match &h.by {
                LinesHold::Stated { line } => read.grammar.print(line),
                LinesHold::Beside { .. } | LinesHold::Closed => String::new(),
            };
            (
                line,
                read.grammar.print(&h.term),
                h.system.sign().to_string(),
                stated,
            )
        })
        .collect()
}

#[test]
fn a_line_a_step_names_holds_a_letter_only_in_that_step() {
    let read = read(&[WITNESS]);
    let record = &read.theorems[WITNESS];
    let held = held(&read, record);
    // Step 2's reason, `def:divides …, from H2, 1` on line 16, names H2,
    // m ∈ ℕ: there m is held in ℕ by that line, and so in ℤ.
    for system in ["ℕ", "ℤ"] {
        assert!(
            held.iter().any(|(l, t, s, by)| *l == 16
                && t == "m"
                && s == system
                && by == "m ∈ ℕ"),
            "{held:?}"
        );
    }
    // Step 3's reason, on line 19, names lines 1 and 2 and not H2: no line
    // holds m.
    assert!(
        !held.iter().any(|(l, t, _, _)| *l == 19 && t == "m"),
        "{held:?}"
    );
}

#[test]
fn a_kinds_reason_is_held_as_the_check_reads_it() {
    let read = read(&[WILSON]);
    let record = &read.theorems[WILSON];
    let held = held(&read, record);
    // D1's reason, `membership, from 5.3`, read at a member of its domain:
    // 5.3 says p − 2 ∈ ℕ, which holds it in ℕ₀ too, and the remainder is
    // whole by the closure table.
    assert!(
        held.iter()
            .any(|(_, t, s, by)| t == "p − 2" && s == "ℕ₀" && by == "p − 2 ∈ ℕ"),
        "{held:?}"
    );
    assert!(
        held.iter()
            .any(|(_, t, s, _)| t == "a^(p − 2) mod p" && s == "ℕ₀"),
        "{held:?}"
    );
}
