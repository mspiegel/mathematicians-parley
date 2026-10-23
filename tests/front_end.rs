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

/// A part that is one formula is one sentence; two is a defect, where a
/// claim of two is their conjunction.
#[test]
fn a_part_that_is_one_formula_refuses_two_sentences() {
    let one = Written::new("x = 1.", "front-end", 0);
    assert!(one.formula().is_ok());
    let two = Written::new("x = 1. y = 2", "front-end", 0);
    let refused = two
        .formula()
        .expect_err("two sentences are not one formula");
    let said = "is 2 sentences where one formula is written";
    assert!(refused.message.contains(said));
    assert_eq!(two.sentences().len(), 2);
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
    .formula()
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
    let sentence = Written::new("s(t) ≠ t", "front-end", 0).formula().unwrap();
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
        .formula()
        .unwrap()
        .read(&g, &sorts)
        .unwrap();
}

/// A letter a binder names takes its sort from what the binder says it
/// ranges over, with nothing above saying what it is: a part of A, or a
/// member of 𝒫A, is a set of A's sort, and so is a letter `for all sets`
/// names; so `|S|` is S's size, and `|x|` for x in a set of numbers its
/// absolute value.
#[test]
fn a_bound_letter_takes_its_sort_from_its_binder() {
    let g = grammar();
    let numbers = Whole::read("set of number").and_then(Sort::whole).unwrap();
    let sorts: Sorts = [
        ("A".to_string(), Sort::of("set")),
        ("R".to_string(), numbers),
    ]
    .into_iter()
    .collect();
    let sized = [
        "|{S ∈ 𝒫A : |S| = 1}| = 0",
        "|{S ⊆ A : |S| = 1}| = 0",
        "for all S ⊆ A, |S| ≤ |A|",
        "there is Y ⊆ A with |Y| ≤ |A|",
        "for all sets X, if |X| = 1 then X ≠ ∅",
    ];
    for text in sized {
        let tree = Written::new(text, "front-end", 0)
            .formula()
            .unwrap()
            .read(&g, &sorts)
            .unwrap();
        let shape = tree.shape().to_string();
        assert!(
            shape.contains("cardinality") && !shape.contains("absolute-value"),
            "{text}: {shape}"
        );
    }
    let tree = Written::new("for all x ∈ R, |x| ≥ 0", "front-end", 0)
        .formula()
        .unwrap()
        .read(&g, &sorts)
        .unwrap();
    let shape = tree.shape().to_string();
    assert!(
        shape.contains("absolute-value") && !shape.contains("cardinality"),
        "{shape}"
    );
}

/// A letter a binder names takes its sort from the set it ranges over
/// however that set is written: the parts of a range, `𝒫{1, …, n}`, and the
/// value of a function that gives sets of sets, `U(k)`, are read as terms,
/// so `|S|` is S's size.
#[test]
fn a_bound_letter_takes_its_sort_from_a_set_written_out() {
    let g = grammar();
    let parts = Whole::read("set of set of number")
        .and_then(Sort::whole)
        .unwrap();
    let runs = Whole::Function(
        Rc::new(Whole::read("number").unwrap()),
        Rc::new(Whole::read("set of set of number").unwrap()),
    );
    let sorts: Sorts = [
        ("n".to_string(), Sort::of("number")),
        ("k".to_string(), Sort::of("number")),
        ("P".to_string(), parts),
        ("U".to_string(), Sort::whole(runs).unwrap()),
    ]
    .into_iter()
    .collect();
    let sized = [
        "for all S ∈ 𝒫{1, …, n}, |S| ≤ n",
        "3 ∈ {|S| : S ∈ 𝒫{1, …, n}}",
        "3 ∈ {|S| : S ∈ U(k)}",
        "there is S ∈ U(k) with 3 = |S|",
        "for all S ∈ P ∪ U(k), |S| ≤ n",
    ];
    for text in sized {
        let tree = Written::new(text, "front-end", 0)
            .formula()
            .unwrap()
            .read(&g, &sorts)
            .unwrap();
        let shape = tree.shape().to_string();
        assert!(
            shape.contains("cardinality") && !shape.contains("absolute-value"),
            "{text}: {shape}"
        );
    }
}

/// A part of a set written in braces, a range {1, …, n}, is a set of
/// numbers as surely as a set named by one letter: the letter a binder
/// makes a part of it is a set, so `|d|` is d's size. So is a member of the
/// power set of one, or of a set in brackets, as a printed claim writes it.
#[test]
fn a_part_of_a_range_is_a_set() {
    let g = grammar();
    let sorts: Sorts = [
        ("n".to_string(), Sort::of("number")),
        ("X".to_string(), Sort::of("set")),
        ("a".to_string(), Sort::of("number")),
    ]
    .into_iter()
    .collect();
    for text in [
        "|{d ⊆ {1, …, n} : |d| = 1}| = 0",
        "for all d ⊆ {1, …, n + 1}, |d| ≤ n + 1",
        "|{d ∈ 𝒫{1, …, n} : |d| = 1}| = 0",
        "|{S ∈ 𝒫(X ∖ {a}) : |S| = 1}| = 0",
    ] {
        let tree = Written::new(text, "front-end", 0)
            .formula()
            .unwrap()
            .read(&g, &sorts)
            .unwrap();
        let shape = tree.shape().to_string();
        assert!(
            shape.contains("cardinality") && !shape.contains("absolute-value"),
            "{text}: {shape}"
        );
    }
}
