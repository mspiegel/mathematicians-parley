//! Every method and every notation is written by a proof the rewrites read.
//!
//! The rewrites of `tests/invariance.rs` turn equations round, rename
//! letters and split claims in the proofs of `proofs/`, `tests/elaborator/`
//! and `tests/stdlib/`, and so they test a method or a notation only where a
//! proof there writes it. One no proof writes is tested by nothing until a
//! theorem needs it, which is where its faults were found one at a time. So
//! a method or notation is added with a proof that writes it, a theorem, a
//! test proof of `tests/elaborator/` or a library item's own test, and this
//! test fails on one that has none.
//!
//! What no proof wrote when the test was written is listed in `UNWRITTEN`,
//! each to be given a proof. The test fails on one missing from the list,
//! and on one listed that a proof now writes, so that the list says what is
//! so.

use std::collections::BTreeSet;
use std::path::Path;

use parley::corpus::proof::{Head, Theorem, METHODS};
use parley::corpus::{corpus, define_parts, DefineParts};
use parley::formula::grammar::{parse_here, Grammar};
use parley::formula::node::walk;
use parley::outcome::{Built, Declined};
use parley::sorts::{said_by_line, sentences, sorts_in_scope, Env};
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

/// Everything a theorem writes as a formula: its statement, and each step's
/// claim and requires lines.
fn formulas(thm: &Theorem) -> Vec<String> {
    let mut out: Vec<String> = thm
        .hypotheses
        .iter()
        .map(|h| said_by_line(h.kind, &h.text))
        .collect();
    out.push(thm.conclusion.clone());
    // A define's rule, as `define_parts` reads it: the body, or each value
    // a recursion gives at the start and at a step.
    for d in &thm.defines {
        match define_parts(d.text.trim()) {
            Built(DefineParts::One(one)) => out.push(one.body),
            Built(DefineParts::Recursion(r)) => {
                out.extend(r.start.into_values());
                out.extend(r.step.into_values());
            }
            Declined(_) => {}
        }
    }
    for step in &thm.steps {
        out.push(step.claim_text());
        out.extend(step.requires.iter().map(|r| r.fact.clone()));
        out.extend(step.openers.iter().map(|o| said_by_line(o.kind, &o.text)));
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
            ["proofs/", "tests/elaborator/", "tests/stdlib/"]
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
        for text in formulas(thm) {
            for s in sentences(&text) {
                let Ok(node) = parse_here(&s, &g, &sorts) else {
                    continue;
                };
                // A node is the pattern that read it: the record it stands
                // under and the literal that pattern writes, as
                // `matching::turned` tells two patterns of one record apart.
                for n in walk(&[node]) {
                    written.insert(format!("notation {} {}", n.notation, n.text));
                }
            }
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
        "written by no proof, and not listed: give each a proof in proofs/, tests/elaborator/ or tests/stdlib/\n{}\n\n\
         listed, and now written by a proof:\n{}",
        new.iter().map(|s| format!("    \"{s}\",")).collect::<Vec<_>>().join("\n"),
        gone.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n")
    );
}
