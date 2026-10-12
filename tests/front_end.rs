//! The one front end from text to formula: a claim is cut into the same
//! sentences however it ends, and a formula a tool makes from trees is the
//! tree the parser reads for the same text.

use std::path::Path;
use std::rc::Rc;

use parley::corpus::parse_database;
use parley::formula::page::{conjoined, Written};
use parley::formula::{Grammar, Node, Sort, Sorts, Whole};
use parley::outcome::Declined;

fn grammar() -> Rc<Grammar> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("corpus/db/notation.records");
    let text = std::fs::read_to_string(&path).unwrap();
    let records = parse_database("corpus/db/notation.records", &text).unwrap();
    Grammar::load(&records).unwrap()
}

fn read(text: &str, g: &Grammar) -> Vec<Node> {
    let sorts = Sorts::new();
    Written::new(text, "front-end", 0)
        .sentences()
        .iter()
        .map(|s| s.read(g, &sorts).unwrap())
        .collect()
}

#[test]
fn a_closing_full_stop_is_no_part_of_the_formula() {
    let g = grammar();
    for (one, other) in [
        ("x = 1", "x = 1."),
        ("x = 1. y = 2", "x = 1. y = 2."),
        ("x = 1. y = 2", "x = 1.\n    y = 2."),
    ] {
        let a: Vec<String> = read(one, &g)
            .iter()
            .map(|n| n.shape().to_string())
            .collect();
        let b: Vec<String> = read(other, &g)
            .iter()
            .map(|n| n.shape().to_string())
            .collect();
        assert_eq!(a, b, "{one:?} against {other:?}");
    }
}

#[test]
fn a_claim_of_several_sentences_is_their_conjunction_from_the_left() {
    let g = grammar();
    let made = conjoined(&g, read("x = 1. y = 2. z = 3", &g)).unwrap();
    let [written] = read("((x = 1) and (y = 2)) and (z = 3)", &g)
        .try_into()
        .unwrap();
    assert_eq!(made.shape(), written.shape());
}

/// A membership a `let` says in words, `let A = x + 1, a real number`, is
/// made from its term and its set, and is the tree of the membership
/// written out.
#[test]
fn a_membership_made_from_its_parts_is_the_one_written() {
    let g = grammar();
    let made = Written::member(
        Written::new("x + 1", "front-end", 0),
        Written::new("ℝ", "front-end", 0),
        "front-end",
        0,
    )
    .sentence()
    .unwrap()
    .read(&g, &Sorts::new())
    .unwrap();
    let [written] = read("(x + 1) ∈ ℝ", &g).try_into().unwrap();
    assert_eq!(made.shape(), written.shape());
}

/// `s(t)` is s applied to t or s times t, and nothing has said which while
/// the sorts are still being found: the reading waits, a value, and is a
/// defect only where the sorts are settled.
#[test]
fn a_reading_that_waits_on_a_sort_declines() {
    let g = grammar();
    let sentence = Written::new("s(t) ≠ t", "front-end", 0).sentence().unwrap();
    let Declined(why) = sentence.read_so_far(&g, &Sorts::new()).unwrap() else {
        panic!("s(t) read with nothing saying what s is");
    };
    let problem = sentence.read(&g, &Sorts::new()).unwrap_err();
    assert_eq!(problem.message, why.reason());
}

/// A letter bound earlier in a sentence gives its sort to a set written
/// later in it: in `for all x ∈ aH`, aH is a coset because a ∈ G.
#[test]
fn a_set_reads_with_the_sort_of_a_letter_bound_before_it() {
    let g = grammar();
    let group_set = Whole::read("set of group-element")
        .and_then(Sort::whole)
        .unwrap();
    let sorts: Sorts = [
        ("G".to_string(), group_set.clone()),
        ("H".to_string(), group_set),
    ]
    .into_iter()
    .collect();
    Written::new("For all a ∈ G, for all x ∈ aH, xH ⊆ aH", "front-end", 0)
        .sentence()
        .unwrap()
        .read(&g, &sorts)
        .unwrap();
}
