//! Two formulas are compared as one formula, not as they are spelt.
//!
//! A tool that asks whether a fact is the claim, whether a case assumes its
//! disjunct, whether a requires line says what an item asks, asks it of what
//! the formulas say: `b = a` is `a = b`, `x > 0` is `0 < x`, and a sum over k
//! is the sum over j. The checker answers with `Known::alike` and the
//! citation matcher with `matching::alike`; the elaborator carries one
//! spelling to another with `same` and finds facts with `held`. A comparison
//! of two trees' shapes asks something else, whether they are spelt alike,
//! and each such comparison in the tools found so far was a fault where it
//! asked the first question (`tests/invariance.rs`).
//!
//! So every comparison of shapes the source makes is listed here with why
//! spelling is what it means to ask. A new one fails this test until it is
//! either made a comparison of formulas or listed with its reason, and a
//! listed one that is gone fails it too, so that the list says what is so.

use std::path::Path;

use regex::Regex;

/// Each comparison of shapes the tools make on purpose: the file, a piece of
/// the line that finds it, and why spelling is the question there.
const ALLOWED: &[(&str, &str, &str)] = &[
    (
        "src/matching.rs",
        "return a.shape() == b.shape();",
        "`alike` itself: a binder over something other than a name is the same only as written",
    ),
    (
        "src/matching.rs",
        "ground.children[1].shape() == arg.shape()",
        "the matcher asking whether an application is applied to that very argument",
    ),
    (
        "src/elab/spoken.rs",
        "b.shape() == node.shape()",
        "a reading said back is the page's only where it reads back as itself, letter for letter",
    ),
    (
        "src/citing/supply.rs",
        "f.children[0].shape() == value.shape()",
        "a membership said of the very term a letter is bound to",
    ),
    (
        "src/citing/library.rs",
        "part.shape() != x.shape()",
        "a part already listed is not listed twice",
    ),
    (
        "src/citing/library.rs",
        "turned.shape() != node.shape()",
        "an equation that reads the same turned around is listed once",
    ),
    (
        "src/citing/parts.rs",
        "held.shape() == fact.shape()",
        "a letter of a form stands for one term wherever the form writes it",
    ),
    (
        "src/citing/parts.rs",
        "member.children[1].shape() != domain.shape()",
        "a membership in the set a function's type writes as its domain",
    ),
    (
        "src/check/citations.rs",
        "held.shape() != *atom",
        "an atom found among a term's parts, part by part",
    ),
    (
        "src/check/citations.rs",
        "part.shape() == *atom",
        "an atom found among a term's parts, part by part",
    ),
    (
        "src/check/citations.rs",
        "one.iter().zip(other).all(|(a, b)| a.shape() == b.shape())",
        "the surplus check skips a search only where the claim and seed are the trees its ways were found under; trees alike but spelt otherwise only cost a search",
    ),
    (
        "src/check/formulas.rs",
        "if a.shape() == b.shape() {",
        "two terms walked in step to find where they differ (`changed_closed`)",
    ),
];

fn sources(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    for entry in std::fs::read_dir(dir).expect("the source directory reads") {
        let path = entry.expect("an entry reads").path();
        if path.is_dir() {
            sources(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

#[test]
fn formulas_are_compared_as_formulas() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let comparison =
        Regex::new(r"shape\(\)\s*[!=]=|[!=]=\s*[\w.&*\[\]]*\.shape\(\)").unwrap();
    let mut files = Vec::new();
    sources(&root.join("src"), &mut files);
    files.sort();
    let mut unlisted = Vec::new();
    let mut used = vec![false; ALLOWED.len()];
    for file in files {
        let rel = file
            .strip_prefix(root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        let text = std::fs::read_to_string(&file).expect("a source file reads");
        for (n, line) in text.lines().enumerate() {
            if !comparison.is_match(line) {
                continue;
            }
            let listed = ALLOWED
                .iter()
                .position(|(path, piece, _)| *path == rel && line.contains(piece));
            match listed {
                Some(i) => used[i] = true,
                None => unlisted.push(format!("{rel}:{}  {}", n + 1, line.trim())),
            }
        }
    }
    let gone: Vec<String> = ALLOWED
        .iter()
        .zip(&used)
        .filter(|(_, u)| !**u)
        .map(|((path, piece, _), _)| format!("{path}  {piece}"))
        .collect();
    assert!(
        unlisted.is_empty() && gone.is_empty(),
        "comparisons of how formulas are spelt, not listed: compare them as formulas \
         (`Known::alike`, `matching::alike`), or list each with why spelling is the question:\n{}\n\n\
         listed comparisons no longer found:\n{}",
        unlisted.join("\n"),
        gone.join("\n")
    );
}
