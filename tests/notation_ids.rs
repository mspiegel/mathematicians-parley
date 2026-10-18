//! The notations the code names by id (`parley::notations::KNOWN`) are the
//! records' own: each is a notation a record declares, under its name or as
//! one it spells, and each literal the code names is a literal of its
//! patterns, at the place the code gives it. The first four are built by
//! the tools themselves and no record declares them.

use std::path::Path;

use parley::corpus::parse_database;
use parley::formula::notation_id::{LiteralId, Spelling};
use parley::formula::Grammar;
use parley::notations::KNOWN;

/// The ones no record declares: a letter, a numeral, a term in kernel form,
/// a property a binding fills.
const BUILT_IN: usize = 4;

#[test]
fn every_notation_the_code_names_is_one_a_record_declares() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("corpus/db/notation.records");
    let text = std::fs::read_to_string(&path).expect("the notation records read");
    let records =
        parse_database("corpus/db/notation.records", &text).expect("the records parse");
    let g = Grammar::load(&records).expect("the grammar loads");
    let mut wrong = Vec::new();
    for known in &KNOWN[BUILT_IN..] {
        let patterns: Vec<_> = g
            .notations
            .iter()
            .filter(|n| n.key_id == known.id || n.record_id == known.id)
            .collect();
        if patterns.is_empty() {
            wrong.push(format!("{}: no record declares it", known.name));
            continue;
        }
        for (place, said) in known.literals {
            let there = patterns.iter().any(|n| {
                n.key_id == known.id && n.literal_id == *place && n.literal == *said
            });
            if !there {
                wrong.push(format!(
                    "{}: no pattern of it writes {said} at the place the code gives it",
                    known.name
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    // A spelling's text is the literal it was made from.
    let plus = Spelling::new(KNOWN[8].id, LiteralId::of(KNOWN[8].id, "+"));
    assert_eq!(&*plus.text(), "+");
}
