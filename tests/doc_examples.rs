//! Every example `SYNTAX.md` and `GRAMMAR.md` show is one the tools accept.
//!
//! An example is a fenced block, and its opening fence says what it is:
//!
//! - `proof`: text of a proof file. It is found, line by line, in a proof
//!   under `proofs/` or `tests/`, which the build checks, elaborates and
//!   verifies as it does every proof: an example quoted from a theorem is
//!   found in that theorem, and one no theorem says is given a proof of its
//!   own under `tests/docs/`. A line that is `...`, or a step number and
//!   `...`, stands for lines the example leaves out, and the lines between
//!   two such are found together and in order.
//! - `records`: text of a records file, found the same way in a records file
//!   of `corpus/`.
//! - `grammar`: productions, which describe the language and are not run.
//!
//! A block that says none of these fails, so an example added to either
//! document is given a kind, and one of the first two a home, before it is
//! committed; an example edited so that no proof says it any more fails the
//! same way. Code inside a paragraph is a fragment the prose names, not an
//! example, and is not read.

use std::fs;
use std::path::{Path, PathBuf};

const DOCUMENTS: &[&str] = &["docs/SYNTAX.md", "docs/GRAMMAR.md"];

/// Where a `proof` example is looked for, and where a `records` one is.
const PROOFS: &[&str] = &["proofs", "tests"];
const RECORDS: &[&str] = &["corpus"];

struct Example {
    document: &'static str,
    line: usize,
    kind: String,
    lines: Vec<String>,
}

/// The fenced blocks of a document, each with the line its fence opens on.
fn examples(document: &'static str, text: &str) -> Vec<Example> {
    let mut out = Vec::new();
    let mut open: Option<Example> = None;
    for (n, line) in text.lines().enumerate() {
        if let Some(info) = line.strip_prefix("```") {
            match open.take() {
                Some(done) => out.push(done),
                None => {
                    open = Some(Example {
                        document,
                        line: n + 1,
                        kind: info.trim().to_string(),
                        lines: Vec::new(),
                    })
                }
            }
            continue;
        }
        if let Some(example) = open.as_mut() {
            example.lines.push(line.to_string());
        }
    }
    out
}

/// A line with its spacing made one space, so that an example's columns
/// need not match the file's.
fn squashed(line: &str) -> String {
    line.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Whether a line stands for lines left out: `...`, or a step number and
/// `...`.
fn elided(line: &str) -> bool {
    let said = squashed(line);
    let step_number = |word: &str| {
        word.starts_with(|c: char| c.is_ascii_digit())
            && word.ends_with('.')
            && word.chars().all(|c| c.is_ascii_digit() || c == '.')
    };
    let rest = match said.split_once(' ') {
        Some((number, rest)) if step_number(number) => rest,
        _ => said.as_str(),
    };
    matches!(rest, "..." | "…")
}

/// The runs of an example: its lines between the ones left out, squashed,
/// blank lines dropped.
fn runs(lines: &[String]) -> Vec<Vec<String>> {
    let mut out = Vec::new();
    let mut run = Vec::new();
    for line in lines {
        if line.trim().is_empty() {
            continue;
        }
        if elided(line) {
            if !run.is_empty() {
                out.push(std::mem::take(&mut run));
            }
            continue;
        }
        run.push(squashed(line));
    }
    if !run.is_empty() {
        out.push(run);
    }
    out
}

/// Whether the file's lines hold each run, its lines together, the runs in
/// order.
fn holds(file: &[String], runs: &[Vec<String>]) -> bool {
    let mut from = 0;
    for run in runs {
        let found = (from..=file.len().saturating_sub(run.len()))
            .find(|&at| file.get(at..at + run.len()) == Some(run.as_slice()));
        match found {
            Some(at) => from = at + run.len(),
            None => return false,
        }
    }
    true
}

/// The files under `dir` ending in `extension`, each as its lines squashed,
/// blank lines dropped.
fn files(dir: &Path, extension: &str) -> Vec<(PathBuf, Vec<String>)> {
    let mut out = Vec::new();
    let Ok(entries) = fs::read_dir(dir) else {
        return out;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            out.extend(files(&path, extension));
        } else if path.extension().is_some_and(|e| e == extension) {
            let text = fs::read_to_string(&path).expect("a file listed can be read");
            let lines = text
                .lines()
                .filter(|l| !l.trim().is_empty())
                .map(squashed)
                .collect();
            out.push((path, lines));
        }
    }
    out
}

#[test]
fn every_example_in_the_syntax_documents_is_one_the_tools_accept() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let under = |dirs: &[&str], extension: &str| -> Vec<(PathBuf, Vec<String>)> {
        dirs.iter()
            .flat_map(|d| files(&root.join(d), extension))
            .collect()
    };
    let proofs = under(PROOFS, "proof");
    let records = under(RECORDS, "records");
    let mut faults = Vec::new();
    let mut counted = 0;
    for document in DOCUMENTS {
        let text = fs::read_to_string(root.join(document)).expect("the document reads");
        for example in examples(document, &text) {
            let at = format!("{}:{}", example.document, example.line);
            let homes = match example.kind.as_str() {
                "proof" => &proofs,
                "records" => &records,
                "grammar" => continue,
                other => {
                    faults.push(format!(
                        "{at}: the fence says {other:?}; an example is `proof`, `records` or `grammar`"
                    ));
                    continue;
                }
            };
            counted += 1;
            let runs = runs(&example.lines);
            if !homes.iter().any(|(_, lines)| holds(lines, &runs)) {
                let place = if example.kind == "proof" {
                    PROOFS
                } else {
                    RECORDS
                };
                faults.push(format!(
                    "{at}: no {} file under {} says this example",
                    example.kind,
                    place.join(" or ")
                ));
            }
        }
    }
    assert!(counted > 0, "no example was read");
    assert!(faults.is_empty(), "\n{}\n", faults.join("\n"));
}

#[test]
fn a_line_left_out_is_three_dots_alone_or_after_a_step_number() {
    assert!(elided("    ..."));
    assert!(elided("    1.1.  ..."));
    assert!(elided("  …"));
    assert!(!elided("1.1.  n² is odd"));
    assert!(!elided("for all k ∈ {1, …, n}"));
    assert!(!elided("1, 2, ..., n"));
}
