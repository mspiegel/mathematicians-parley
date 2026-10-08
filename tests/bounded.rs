//! A quantifier written with a bound where its set stands builds exactly
//! the tree its long form builds, so a line written one way meets an item
//! written the other.

use std::path::Path;
use std::rc::Rc;

use parley::corpus::parse_database;
use parley::formula::{parse_here, Grammar, Sorts};

fn grammar() -> Rc<Grammar> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("corpus/db/notation.records");
    let text = std::fs::read_to_string(&path).unwrap();
    let records = parse_database("corpus/db/notation.records", &text).unwrap();
    Grammar::load(&records).unwrap()
}

/// Sorts in which ε and δ range over ℝ and d over ℤ.
fn declared() -> Sorts {
    let mut sorts = Sorts::new();
    for (name, set) in [("ε", "ℝ"), ("δ", "ℝ"), ("d", "ℤ")] {
        sorts.ranges.insert(name.to_string(), set.to_string());
    }
    sorts
}

#[test]
fn each_short_form_builds_its_long_form() {
    let g = grammar();
    let sorts = declared();
    let pairs = [
        ("for all ε > 0, ε = ε", "for all ε ∈ ℝ with ε > 0, ε = ε"),
        (
            "there is δ > 0 with δ = δ",
            "there is δ ∈ ℝ with δ > 0 and δ = δ",
        ),
        (
            "there exists δ > 0 such that δ = δ",
            "there is δ ∈ ℝ with δ > 0 and δ = δ",
        ),
        // The condition goes at the far left of a run of conjunctions,
        // which group to the left, by the join the run uses there.
        (
            "there is δ > 0 with δ = δ and δ < 1 and δ ≠ 2",
            "there is δ ∈ ℝ with δ > 0 and δ = δ and δ < 1 and δ ≠ 2",
        ),
        (
            "there is d > 1 with d divides 4, and d divides 6",
            "there is d ∈ ℤ with d > 1, d divides 4, and d divides 6",
        ),
        // A bracketed body is closed, and the condition stands before it.
        (
            "there is δ > 0 with (δ = δ and δ < 1)",
            "there is δ ∈ ℝ with δ > 0 and (δ = δ and δ < 1)",
        ),
        // A negated bound is the negation the sign folds.
        ("for all ε ≠ 0, ε = ε", "for all ε ∈ ℝ with ε ≠ 0, ε = ε"),
        // A universal's condition is the `if` of an `if … then`, whichever
        // way it is written, and an `if … then` body is taken whole.
        (
            "for all ε ∈ ℝ with ε > 0, ε = ε",
            "for all ε ∈ ℝ, if ε > 0 then ε = ε",
        ),
        ("for all ε > 0, ε = ε", "for all ε ∈ ℝ, if ε > 0 then ε = ε"),
        (
            "for all ε > 0, if ε < 1 then ε = ε",
            "for all ε ∈ ℝ, if ε > 0 then if ε < 1 then ε = ε",
        ),
        (
            "for all x ∈ ℤ with x > 0 and x < 3, x = x",
            "for all x ∈ ℤ, if x > 0 and x < 3 then x = x",
        ),
        // Written after what it says, the bounded universal is the same.
        ("ε = ε for all ε > 0", "for all ε > 0, ε = ε"),
        (
            "ε = ε for all ε ≥ 1 + 1",
            "for all ε ∈ ℝ, if ε ≥ 1 + 1 then ε = ε",
        ),
        (
            "there exists δ > 0 such that δ < ε for all ε > δ",
            "there is δ ∈ ℝ with δ > 0 and for all ε ∈ ℝ with ε > δ, δ < ε",
        ),
        // Written after what it says with a condition, the universal is the
        // `if … then` it always is.
        (
            "x = x for all x ∈ ℤ with x > 0",
            "for all x ∈ ℤ, if x > 0 then x = x",
        ),
        (
            "there exists δ > 0 such that x < 1 for all x ∈ ℤ with x − 1 < δ",
            "there is δ ∈ ℝ with δ > 0 and for all x ∈ ℤ, if x − 1 < δ then x < 1",
        ),
    ];
    for (short, long) in pairs {
        let a = parse_here(short, &g, &sorts).unwrap();
        let b = parse_here(long, &g, &sorts).unwrap();
        assert_eq!(a.shape(), b.shape(), "{short:?} against {long:?}");
    }
}

#[test]
fn a_member_is_no_bound() {
    // "for all x ∈ S, …" has its one reading, whatever the ranges say.
    let g = grammar();
    let mut sorts = declared();
    sorts.ranges.insert("x".into(), "ℝ".into());
    let tree = parse_here("there is x ∈ ℤ with x = x", &g, &sorts).unwrap();
    assert!(tree.shape().starts_with("there-is:"), "{}", tree.shape());
}

#[test]
fn an_undeclared_letter_has_no_reading() {
    let g = grammar();
    for text in ["for all η > 0, η = η", "η = η for all η > 0"] {
        let problem = parse_here(text, &g, &declared()).unwrap_err();
        assert!(
            problem
                .message
                .contains("nothing says what set η belongs to"),
            "{text:?}: {}",
            problem.message
        );
    }
}

#[test]
fn a_trailing_bound_over_an_and_has_no_reading() {
    // As for any trailing universal, what it says is one relation.
    let g = grammar();
    let problem =
        parse_here("ε = ε and ε < 2 for all ε > 0", &g, &declared()).unwrap_err();
    assert!(
        problem.message.contains("not ordered"),
        "{}",
        problem.message
    );
}

#[test]
fn a_trailing_condition_over_an_and_has_no_reading() {
    // The condition stands at the right edge and is one relation.
    let g = grammar();
    let text = "x = x for all x ∈ ℤ with x > 0 and x < 3";
    let problem = parse_here(text, &g, &declared()).unwrap_err();
    assert!(
        problem.message.contains("not ordered"),
        "{}",
        problem.message
    );
}
