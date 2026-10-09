//! The checker and the elaborator answer alike where both answer.
//!
//! Each tool answers some questions about a line on its own: what a line
//! implies besides itself, for one. Two answers to one question are two
//! rules, and a proof the one accepts the other refuses. Every theorem is
//! elaborated with each answer compared, as kernel terms, with the checker's
//! to the same question about the same line (`Options::list_answers`).
//!
//! What a record cited by a requires line asks, and what an obtain says
//! there is, both tools answer with one matcher (`citing`), each from its
//! own reading of the page: which lines a citation names, what they say,
//! and which defines are written out. So each tool lists its answers in the
//! page's notation (`check::answers`, `Elaborator::list_asked`), and the
//! two lists are compared.
//!
//! Answers they give differently are listed in `KNOWN`, each a gap a later
//! change closes, and there are none. The test fails on any other
//! difference, and on a known one that is gone, so that the list says what
//! is so. This reads set.mm, and fails if set.mm cannot be found.

use std::collections::BTreeSet;
use std::path::Path;
use std::sync::Arc;

use parley::corpus::corpus;
use parley::elab::elaborate::Options;
use parley::elab::Library;
use parley::source::{Disk, Memory};
use parley::threads::in_order;
use parley::tools::build::{library, Loaded};

/// The differences there are, each a gap a later change closes.
const KNOWN: &[&str] = &[];

#[test]
fn the_tools_answer_alike() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let tree = Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap();
    let names: Vec<String> = corpus(&tree)
        .expect("the corpus reads")
        .theorems
        .iter()
        .map(|t| t.qualified())
        .collect();
    let options = Options {
        list_answers: true,
        ..Options::default()
    };
    // Each thread elaborates with a library of its own on set.mm read once,
    // and reads the corpus once.
    let read = library(root, None)
        .expect(
            "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
        )
        .shared();
    let answers = in_order(
        &names,
        || {
            (
                Library::new(Arc::clone(&read)),
                Loaded::new(&tree).expect("the corpus reads"),
            )
        },
        |(lib, loaded), name| {
            loaded
                .elaborate(name, lib, options)
                .unwrap_or_else(|p| panic!("{name} does not elaborate: {p}"))
                .answers
        },
    );
    let all: BTreeSet<String> = answers.into_iter().flatten().collect();
    // What a cited record asks, and what an obtain says there is: each tool
    // lists its own answer, read from the page its own way, and the two
    // lists are compared line by line. Each list is counted, so that a hook
    // that stopped running is not taken for one that agrees.
    let is_cited =
        |a: &String| a.contains(" | asked | ") || a.contains(" | obtained | ");
    let elaborator: BTreeSet<String> =
        all.iter().filter(|a| is_cited(a)).cloned().collect();
    let checker: BTreeSet<String> = parley::check::answers(&tree)
        .unwrap_or_else(|_| panic!("the corpus checks"))
        .into_iter()
        .collect();
    let count = |list: &BTreeSet<String>, kind: &str| {
        list.iter().filter(|a| a.contains(kind)).count()
    };
    println!(
        "elaborator: {} asked, {} obtained; checker: {} asked, {} obtained",
        count(&elaborator, " | asked | "),
        count(&elaborator, " | obtained | "),
        count(&checker, " | asked | "),
        count(&checker, " | obtained | "),
    );
    for list in [&elaborator, &checker] {
        assert!(
            count(list, " | asked | ") > 0 && count(list, " | obtained | ") > 0,
            "a listing hook gave no cited items"
        );
    }
    let mut found: BTreeSet<String> =
        all.into_iter().filter(|a| !is_cited(a)).collect();
    found.extend(
        elaborator
            .difference(&checker)
            .map(|a| format!("{a} | elaborator only")),
    );
    found.extend(
        checker
            .difference(&elaborator)
            .map(|a| format!("{a} | checker only")),
    );
    let known: BTreeSet<String> = KNOWN.iter().map(|s| s.to_string()).collect();
    let new: Vec<&String> = found.difference(&known).collect();
    let gone: Vec<&String> = known.difference(&found).collect();
    println!("{} theorems, {} differences", names.len(), found.len());
    assert!(
        new.is_empty() && gone.is_empty(),
        "differences not known:\n{}\n\nknown differences no longer found:\n{}",
        new.iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n"),
        gone.iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n")
    );
}
