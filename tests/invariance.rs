//! A proof means what it says, however it spells it.
//!
//! A rule that reads the spelling of a line rather than what it says accepts
//! one proof and refuses the same proof written another way: `k ≥ 0` and
//! `0 ≤ k` are one fact, and so are `from 3, 4` and `from 4, 3`. Each change
//! here rewrites every line of the corpus's proofs it applies to, in a way
//! that keeps what each line says, and the corpus must still check with no
//! problem and every theorem in a changed file still elaborate.
//!
//! What a change breaks is listed in `KNOWN`, each a gap a later change
//! closes. The test fails on any other break, and on a known one that is
//! gone, so that the list says what is so. This reads set.mm, and fails if
//! set.mm cannot be found.

use std::collections::BTreeSet;
use std::path::Path;
use std::sync::Mutex;

use parley::corpus::corpus;
use parley::elab::elaborate::Options;
use parley::source::{Disk, Memory, Overlay, Source};
use parley::tools::build::{elaborate_one, library};

/// The breaks there are, each a gap a later change closes.
///
/// One kind, in the elaborator: a denied equation written the other way
/// round, `0 ≠ k` for `k ≠ 0` or `C ≠ A` for `A ≠ C`. Its normalizer reads
/// the two as one claim (`df-ne`, then `eqcom`), but the facts a step has
/// are kept by their kernel terms as written, and a route that looks one up
/// by its term finds only the way round it was written.
const KNOWN: &[&str] = &[
    "an equation in a requires line turned around | elaborate | proofs/angle-sum.proof:24  mun:triangle does not reach A ≠ C, which this line claims it supplies",
    "an equation in a requires line turned around | elaborate | proofs/cauchy-schwarz.proof:145  step 5.13 follows from what it cites, and inequalities cannot write its proof: nothing says vp cv is not zero",
    "an equation in a requires line turned around | elaborate | proofs/geometric-series.proof:50  nothing says ( ( -u 1 x. ( A ^ 1 ) ) + ( 1 x. 1 ) ) =/= 0, which this step needs to divide by it",
    "an equation in a requires line turned around | elaborate | proofs/harmonic.proof:67  1 / k ∈ ℝ is not built from what step 6.2 cites: nothing written says 1 / k ∈ ℝ",
    "an equation in a requires line turned around | elaborate | proofs/isosceles.proof:30  mun:triangle, from H4 does not reach C ≠ A, which this line claims it supplies",
    "an equation in a requires line turned around | elaborate | proofs/mean-value.proof:51  the requires line (f(a) − f(b))/(b − a) ∈ ℝ of step 6, read as a step citing what it cites: (f(a) − f(b)) / (b − a) ∈ ℝ is not built from what step 6 cites: nothing written says (f(a) − f(b)) / (b − a) ∈ ℝ",
    "an equation in a requires line turned around | elaborate | proofs/pythagoras.proof:116  mun:triangle does not reach A ≠ C, which this line claims it supplies",
    "an equation in a requires line turned around | elaborate | proofs/triangular-reciprocals.proof:23  from K1 does not reach 0 ≠ k, which this line claims it supplies",
];

/// One rewriting that keeps what a line says: the line rewritten, or None
/// where the change does not apply to it.
struct Change {
    name: &'static str,
    line: fn(&str) -> Option<String>,
}

fn changes() -> Vec<Change> {
    vec![
        Change {
            name: "cited lines in the other order",
            line: reversed_from,
        },
        Change {
            name: "no spaces around operators in a requires line",
            line: unspaced,
        },
        Change {
            name: "an order in a requires line turned around",
            line: order_turned,
        },
        Change {
            name: "an equation in a requires line turned around",
            line: equation_turned,
        },
    ]
}

/// `from A, B, C` as `from C, B, A`: a citation names lines, in no order.
fn reversed_from(line: &str) -> Option<String> {
    let at = line.rfind("from ")?;
    let (head, refs) = line.split_at(at + "from ".len());
    let refs: Vec<&str> = refs.trim_end().split(", ").collect();
    let names = refs.iter().all(|r| {
        !r.is_empty()
            && r.chars()
                .all(|c| c.is_alphanumeric() || c == '.' || c == '′')
    });
    if refs.len() < 2 || !names {
        return None;
    }
    let reversed: Vec<&str> = refs.into_iter().rev().collect();
    Some(format!("{head}{}", reversed.join(", ")))
}

/// A requires line taken apart: what comes before its fact, the fact, and
/// its reason from the colon on. A function type's own ` : ` comes before
/// the line's, so the reason starts at the last `: `.
fn requires_parts(line: &str) -> Option<(&str, &str, &str)> {
    let start = line.find("requires ")? + "requires ".len();
    if !line[..start - "requires ".len()].trim().is_empty() {
        return None;
    }
    let end = line.rfind(": ")?;
    (end > start).then(|| (&line[..start], &line[start..end], &line[end..]))
}

/// `c + δ/2 ∈ ℝ` as `c+δ/2∈ℝ`: a space between symbols says nothing.
fn unspaced(line: &str) -> Option<String> {
    let (head, fact, reason) = requires_parts(line)?;
    let mut out = fact.to_string();
    for op in ["+", "−", "·", "/", "=", "≠", "≤", "≥", "<", ">", "∈"] {
        out = out.replace(&format!(" {op} "), op);
    }
    (out != fact).then(|| format!("{head}{out}{reason}"))
}

/// The one relation of a fact that says nothing else, as (left, sign,
/// right): no words, no second relation, one sentence.
fn one_relation<'f>(
    fact: &'f str,
    signs: &[&'static str],
) -> Option<(&'f str, &'static str, &'f str)> {
    let all = ["=", "≠", "≤", "≥", "<", ">", "∈", "∉", "⊆", "≡", "→", ":"];
    let count: usize = all.iter().map(|s| fact.matches(s).count()).sum();
    let worded = fact
        .split(|c: char| !c.is_ascii_alphabetic())
        .any(|w| w.len() > 1);
    if count != 1 || worded || fact.contains(". ") || fact.contains(',') {
        return None;
    }
    signs.iter().find_map(|sign| {
        let (left, right) = fact.split_once(&format!(" {sign} "))?;
        Some((left, *sign, right))
    })
}

/// `x ≥ 0` as `0 ≤ x`, and `a < b` as `b > a`.
fn order_turned(line: &str) -> Option<String> {
    let (head, fact, reason) = requires_parts(line)?;
    let (left, sign, right) = one_relation(fact, &["≤", "≥", "<", ">"])?;
    let turned = match sign {
        "≤" => "≥",
        "≥" => "≤",
        "<" => ">",
        _ => "<",
    };
    Some(format!("{head}{right} {turned} {left}{reason}"))
}

/// `a = b` as `b = a`, and `a ≠ b` as `b ≠ a`.
fn equation_turned(line: &str) -> Option<String> {
    let (head, fact, reason) = requires_parts(line)?;
    let (left, sign, right) = one_relation(fact, &["=", "≠"])?;
    Some(format!("{head}{right} {sign} {left}{reason}"))
}

/// The corpus with one change made to every proof file: the tree, the
/// files changed, and how many lines.
fn changed(
    clean: &Memory,
    root: &Path,
    change: &Change,
) -> (Memory, Vec<String>, usize) {
    let mut tree = Overlay::new(clean);
    let mut files = Vec::new();
    let mut lines = 0;
    let mut paths: Vec<String> = std::fs::read_dir(root.join("proofs"))
        .expect("the proofs directory reads")
        .filter_map(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().to_string())
        .filter(|n| n.ends_with(".proof"))
        .map(|n| format!("proofs/{n}"))
        .collect();
    paths.sort();
    for path in paths {
        let text = clean.read_text(&path).expect("a proof file reads");
        let mut edited = Vec::new();
        let mut here = 0;
        for line in text.lines() {
            match (change.line)(line) {
                Some(new) => {
                    edited.push(new);
                    here += 1;
                }
                None => edited.push(line.to_string()),
            }
        }
        if here > 0 {
            let mut out = edited.join("\n");
            if text.ends_with('\n') {
                out.push('\n');
            }
            tree.write(&path, out.into_bytes());
            files.push(path);
            lines += here;
        }
    }
    let copied = Memory::copy(&tree, &["corpus", "proofs", "tests"]).unwrap();
    (copied, files, lines)
}

#[test]
fn a_proof_means_what_it_says_however_it_spells_it() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let clean = Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap();
    let base = parley::check::run(&clean);
    assert!(
        base.printed.contains("\n0 problem(s)\n"),
        "the corpus is not clean, so a change proves nothing:\n{}",
        base.printed
    );
    let changes = changes();
    let trees: Vec<(Memory, Vec<String>, usize)> =
        changes.iter().map(|c| changed(&clean, root, c)).collect();
    let found = Mutex::new(BTreeSet::new());
    // What the checker says of each changed corpus.
    for (change, (tree, _, lines)) in changes.iter().zip(&trees) {
        assert!(*lines > 0, "{} changes no line", change.name);
        println!("{}: {lines} lines", change.name);
        let said = parley::check::run(tree).printed;
        for line in said.lines().filter(|l| l.contains(".proof:")) {
            found
                .lock()
                .unwrap()
                .insert(format!("{} | check | {line}", change.name));
        }
    }
    // Every theorem of a changed file, elaborated, the work shared among
    // workers that each load set.mm once.
    let mut work: Vec<(usize, String)> = Vec::new();
    for (i, (tree, files, _)) in trees.iter().enumerate() {
        for thm in corpus(tree).expect("the changed corpus reads").theorems {
            if files.contains(&thm.path) {
                work.push((i, thm.qualified()));
            }
        }
    }
    let next = Mutex::new(work.iter());
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
                    let Some((i, name)) = next.lock().unwrap().next() else {
                        break;
                    };
                    if let Err(p) = elaborate_one(&trees[*i].0, name, &lib, Options::default()) {
                        found
                            .lock()
                            .unwrap()
                            .insert(format!("{} | elaborate | {p}", changes[*i].name));
                    }
                }
            });
        }
    });
    let found: BTreeSet<String> = found.into_inner().unwrap();
    let known: BTreeSet<String> = KNOWN.iter().map(|s| s.to_string()).collect();
    let new: Vec<&String> = found.difference(&known).collect();
    let gone: Vec<&String> = known.difference(&found).collect();
    println!("{} theorems elaborated, {} breaks", work.len(), found.len());
    assert!(
        new.is_empty() && gone.is_empty(),
        "breaks not known:\n{}\n\nknown breaks no longer found:\n{}",
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
