//! Every method and every notation is written by a proof the rewrites read.
//!
//! The rewrites of `tests/invariance.rs` turn equations round, rename
//! letters and split claims in the proofs of `proofs/`, `tests/elaborator/`,
//! `tests/stdlib/` and `tests/notations/`, and so they test a method or a
//! notation only where a proof there writes it. One no proof writes is
//! tested by nothing until a theorem needs it, which is where its faults were
//! found one at a time. So a method or notation is added with a proof that
//! writes it, a theorem, a test proof of `tests/elaborator/`, a library
//! item's own test or a notation's textbook examples, and this test fails on
//! one that has none.
//!
//! What no proof wrote when the test was written is listed in `UNWRITTEN`,
//! each to be given a proof. The test fails on one missing from the list,
//! and on one listed that a proof now writes, so that the list says what is
//! so.

use std::collections::BTreeSet;
use std::path::Path;

use parley::corpus::proof::{Head, Intro, Theorem, METHODS};
use parley::corpus::{corpus, define_parts, DefineParts};
use parley::formula::grammar::{Grammar, Sorts};
use parley::formula::node::{walk, Node};
use parley::formula::page::Written;
use parley::outcome::{Built, Declined};
use parley::sorts::introduction::Introduction;
use parley::sorts::{sorts_in_scope, Env};
use parley::source::Disk;

/// The methods and notations no proof writes yet, by the record a pattern
/// stands under and the literal it writes.
const UNWRITTEN: &[&str] = &[
    "notation collinear ,,arecollinear",
    "notation holds-of ()",
    "notation implication →",
    "notation map themapsending∈to",
    "notation map-of-two themapsending∈,∈to",
    "notation pi π",
    "notation sum-over Σ(∈)",
    "notation supremum sup",
];

/// Everything a theorem writes as a formula, read: its statement, its
/// defines' rules, and each step's claim, requires lines and opening lines.
/// A `let` line writes what its introduction asserts. What does not read
/// the checker reports.
fn formulas(thm: &Theorem, g: &Grammar, sorts: &Sorts) -> Vec<Node> {
    let read = |written: Written| -> Vec<Node> {
        written
            .sentences()
            .iter()
            .filter_map(|s| s.read(g, sorts).ok())
            .collect()
    };
    let said = |kind: Intro, body: Written| -> Vec<Node> {
        match kind {
            Intro::Let => Introduction::read(body)
                .asserted(g, sorts)
                .unwrap_or_default(),
            _ => read(body),
        }
    };
    let mut out: Vec<Node> = Vec::new();
    for h in &thm.hypotheses {
        out.extend(said(h.kind, h.body(&thm.path)));
    }
    out.extend(read(thm.stated()));
    // A define's rule, as `define_parts` reads it: the body, or each value
    // a recursion gives at the start and at a step.
    for d in &thm.defines {
        let rules = match define_parts(d.text.trim()) {
            Built(DefineParts::One(one)) => vec![one.body],
            Built(DefineParts::Recursion(r)) => {
                r.start.into_values().chain(r.step.into_values()).collect()
            }
            Declined(_) => Vec::new(),
        };
        for rule in rules {
            out.extend(read(d.formula(&rule)));
        }
    }
    for step in &thm.steps {
        out.extend(read(step.claim.clone()));
        for r in &step.requires {
            out.extend(read(r.fact.clone()));
        }
        for o in &step.openers {
            out.extend(said(o.kind, o.body(&thm.path)));
        }
    }
    out
}

#[test]
fn every_method_and_notation_is_written_by_a_proof() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let found = corpus(&Disk::new(root)).expect("the corpus reads");
    let g = Grammar::load(&found.records).expect("the grammar loads");
    let read: Vec<&Theorem> = found
        .theorems
        .iter()
        .filter(|t| {
            [
                "proofs/",
                "tests/elaborator/",
                "tests/stdlib/",
                "tests/notations/",
            ]
            .iter()
            .any(|dir| t.path.starts_with(dir))
        })
        .collect();
    let mut written: BTreeSet<String> = BTreeSet::new();
    for thm in &read {
        for step in &thm.steps {
            if let Head::Method(m) = step.just.head {
                written.insert(format!("method {}", m.as_str()));
            }
        }
        let sorts = sorts_in_scope(
            thm,
            Env {
                g: &g,
                scopes: &found.scopes,
            },
        );
        // A node is the pattern that read it: the record it stands under and
        // the literal that pattern writes, as `matching::turned` tells two
        // patterns of one record apart.
        for n in walk(&formulas(thm, &g, &sorts)) {
            written.insert(format!("notation {} {}", n.notation, n.text));
        }
    }
    let mut every: BTreeSet<String> = METHODS
        .iter()
        .map(|m| format!("method {}", m.as_str()))
        .collect();
    every.extend(
        g.notations
            .iter()
            .map(|n| format!("notation {} {}", n.stands_under, n.literal)),
    );
    let unwritten: BTreeSet<String> = every.difference(&written).cloned().collect();
    let listed: BTreeSet<String> = UNWRITTEN.iter().map(|s| s.to_string()).collect();
    let new: Vec<&String> = unwritten.difference(&listed).collect();
    let gone: Vec<&String> = listed.difference(&unwritten).collect();
    println!(
        "{} written of {}",
        every.len() - unwritten.len(),
        every.len()
    );
    assert!(
        new.is_empty() && gone.is_empty(),
        "written by no proof, and not listed: give each a proof in proofs/, tests/elaborator/, tests/stdlib/ or tests/notations/\n{}\n\n\
         listed, and now written by a proof:\n{}",
        new.iter().map(|s| format!("    \"{s}\",")).collect::<Vec<_>>().join("\n"),
        gone.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n")
    );
}
