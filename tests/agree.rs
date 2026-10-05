//! The checker and the elaborator answer alike where both answer.
//!
//! Each tool answers some questions about a line on its own: what a line
//! implies besides itself, for one. Two answers to one question are two
//! rules, and a proof the one accepts the other refuses. Every theorem is
//! elaborated with each answer compared, as kernel terms, with the checker's
//! to the same question about the same line (`Options::list_answers`).
//!
//! What an item cited by a requires line asks, and what an obtain claims,
//! both tools answer with one matcher (`citing`), and are not compared; the
//! elaborator's answers are listed and counted, so that a hook that stopped
//! running is caught.
//!
//! Answers they give differently are listed in `KNOWN`, each a gap a later
//! change closes, and there are none. The test fails on any other
//! difference, and on a known one that is gone, so that the list says what
//! is so. This reads set.mm, and fails if set.mm cannot be found.

use std::collections::BTreeSet;
use std::path::Path;
use std::sync::Mutex;

use parley::corpus::corpus;
use parley::elab::elaborate::Options;
use parley::source::{Disk, Memory};
use parley::tools::build::{elaborate_one, library};

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
    let found = Mutex::new(BTreeSet::new());
    let next = Mutex::new(names.iter());
    // Each worker loads set.mm once for itself: the library is not shared
    // between threads.
    let workers = std::thread::available_parallelism()
        .map_or(1, |n| n.get())
        .clamp(1, 8);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                let lib = library(root, None).expect(
                    "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
                );
                loop {
                    let Some(name) = next.lock().unwrap().next() else {
                        break;
                    };
                    let done = elaborate_one(&tree, name, &lib, options)
                        .unwrap_or_else(|p| panic!("{name} does not elaborate: {p}"));
                    found.lock().unwrap().extend(done.answers);
                }
            });
        }
    });
    let all: BTreeSet<String> = found.into_inner().unwrap();
    // What the elaborator answers alone, which a later change compares with
    // the shared answer: what an item cited by a requires line asks, and
    // what an obtain claims. The hook is counted, so that one that stopped
    // running is not taken for one that agrees.
    let asked = all.iter().filter(|a| a.contains(" | asked | ")).count();
    let obtained = all.iter().filter(|a| a.contains(" | obtained | ")).count();
    let unanswered: Vec<&String> = all
        .iter()
        .filter(|a| a.contains(" | asked | ") && a.contains("cannot answer"))
        .collect();
    println!(
        "{asked} hypotheses asked, {obtained} sentences obtained, {} citations the elaborator cannot answer:",
        unanswered.len()
    );
    for a in &unanswered {
        println!("  {a}");
    }
    assert!(
        asked > 0 && obtained > 0,
        "the listing hook gave no asked items"
    );
    let found: BTreeSet<String> = all
        .into_iter()
        .filter(|a| !a.contains(" | asked | ") && !a.contains(" | obtained | "))
        .collect();
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
