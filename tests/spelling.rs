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
        "src/formula/page.rs",
        "if above.same_shape(below) {",
        "a substitute row's change is where it and the row above part as written: its reason proves that very equation, and the row above is rebuilt by it alone, so a piece spelt otherwise is part of the change",
    ),
    (
        "src/formula/page.rs",
        ".all(|p| p.was.same_shape(&first.was) && p.now.same_shape(&first.now));",
        "a row's pieces are one term put in several places only where each puts that very term for that very term, as the one equation its reason proves puts it",
    ),
    (
        "src/matching.rs",
        "if start.same_shape(was) {",
        "a place written as the equation's side is written is that place whole, where a formula comparison would also match a part of it with an identity element dropped",
    ),
    (
        "src/citing/conclude.rs",
        "if start.same_shape(was) {",
        "a place written as the equation's side is written drops no identity element, which is a question of how it is written",
    ),
    (
        "src/formula/node.rs",
        ".all(|(a, b)| a.same_shape(b)))",
        "`same_shape` itself, comparing children part by part",
    ),
    (
        "src/formula/node.rs",
        "self.0.same_shape(&other.0)",
        "`ByShape`, the key a set of formulas told apart as spelt is kept by",
    ),
    (
        "src/checker/mod.rs",
        "a.same_shape(&node)",
        "the printer's test: what it prints reads back as the very tree printed",
    ),
    (
        "src/matching.rs",
        "return a.same_shape(b);",
        "`alike` itself: a binder over something other than a name is the same only as written",
    ),
    (
        "src/matching.rs",
        "ground.children[1].same_shape(&arg)",
        "the matcher asking whether an application is applied to that very argument",
    ),
    (
        "src/elab/spoken.rs",
        "b.same_shape(&node)",
        "a reading said back is the page's only where it reads back as itself, letter for letter",
    ),
    (
        "src/citing/supply.rs",
        "f.children[0].same_shape(value)",
        "a membership said of the very term a letter is bound to",
    ),
    (
        "src/citing/supply.rs",
        "|| !f.same_shape(value)",
        "a function's type said of the very term a letter is bound to",
    ),
    (
        "src/matching.rs",
        "if instance.same_shape(ground) {",
        "a pair spelt the same has no identity element dropped between them",
    ),
    (
        "src/checker/structure.rs",
        "!set.same_shape(&over)",
        "a let puts a letter in the very set its range line writes, as written",
    ),
    (
        "src/citing/library.rs",
        "!part.same_shape(x)",
        "a part already listed is not listed twice",
    ),
    (
        "src/citing/library.rs",
        "!turned.same_shape(node)",
        "an equation that reads the same turned around is listed once",
    ),
    (
        "src/citing/parts.rs",
        "held.same_shape(fact)",
        "a letter of a form stands for one term wherever the form writes it",
    ),
    (
        "src/citing/parts.rs",
        "!member.children[1].same_shape(domain)",
        "a membership in the set a function's type writes as its domain",
    ),
    (
        "src/checker/citations.rs",
        "!as_written(&a_tree).same_shape(&as_written(&b_tree))",
        "a recursion is the term its rules build, so two rules are one only as written",
    ),
    (
        "src/checker/citations.rs",
        "!held.same_shape(atom)",
        "an atom found among a term's parts, part by part",
    ),
    (
        "src/checker/citations.rs",
        "part.same_shape(atom)",
        "an atom found among a term's parts, part by part",
    ),
    (
        "src/checker/citations.rs",
        "one.iter().zip(other).all(|(a, b)| a.same_shape(b))",
        "the surplus check skips a search only where the claim and seed are the trees its ways were found under; trees alike but spelt otherwise only cost a search",
    ),
    (
        "src/checker/formulas.rs",
        "if a.same_shape(b) {",
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
    let comparison = Regex::new(r"\.same_shape\(").unwrap();
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
