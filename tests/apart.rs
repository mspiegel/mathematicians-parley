//! A value is put into a tree apart from the tree's own letters, and a
//! citation's values are read together.
//!
//! Two faults came back again and again while the corpus was rewritten
//! (`tests/invariance.rs`). A value put under a binder that uses one of its
//! letters was caught by it: prime-factor's `there is p` at m := p! + 1. And
//! a citation's values were read one after another, so that `a := b/k,
//! b := a/k` read the second in the first's new name. Each was fixed where it
//! was found, and each lived on in another place that did the same thing its
//! own way.
//!
//! So a value is put into a tree by `substitute_apart` or
//! `substitute_apart_by`, which keep a binder's letter apart from it, and a
//! plain `substitute` stands only where it is listed here with why nothing
//! can be caught. And the elaborator reads a citation's values only through
//! `instantiated_nodes`, which reads them all before any is given.

use std::path::{Path, PathBuf};

use regex::Regex;

/// Each plain `substitute` the tools make: the file, a piece of the line,
/// and why no binder can catch a value there.
const PLAIN: &[(&str, &str, &str)] = &[
    (
        "src/matching.rs",
        ".map(|c| substitute(c, binding))",
        "`substitute` itself, going down a tree",
    ),
    (
        "src/citing/parts.rs",
        "Some(substitute(&said, &put))",
        "a bound relates x and S and binds no letter of its own",
    ),
    (
        "src/citing/parts.rs",
        "out.push(substitute(&said, &put));",
        "`f(x) ∈ S` binds nothing",
    ),
    (
        "src/citing/parts.rs",
        "return vec![substitute(&template(conclusion, env, &sets), &put)];",
        "the forms of `rules::PARTS` bind nothing",
    ),
    (
        "src/citing/parts.rs",
        ".map(|t| substitute(&template(t, env, &local), &put))",
        "each template says one thing of x and binds nothing",
    ),
];

/// Where the elaborator reads a citation's values, which is one place.
const READ: &[(&str, &str, &str)] = &[(
    "src/elab/elaborate.rs",
    "instantiation(cites)",
    "`instantiated_nodes`, which reads every value before any is given",
)];

fn sources(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).expect("the source directory reads") {
        let path = entry.expect("an entry reads").path();
        if path.is_dir() {
            sources(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

/// Each line under `dir` the pattern finds that `listed` does not, and each
/// listed line no longer found.
fn unlisted(
    dir: &str,
    pattern: &Regex,
    listed: &[(&str, &str, &str)],
) -> (Vec<String>, Vec<String>) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    sources(&root.join(dir), &mut files);
    files.sort();
    let mut new = Vec::new();
    let mut used = vec![false; listed.len()];
    for file in files {
        let rel = file
            .strip_prefix(root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        let text = std::fs::read_to_string(&file).expect("a source file reads");
        for (n, line) in text.lines().enumerate() {
            // A call, not a comment and not a function of that name being
            // defined.
            let code = line.split("//").next().unwrap_or("");
            if !pattern.is_match(code) || code.contains("fn ") {
                continue;
            }
            match listed
                .iter()
                .position(|(path, piece, _)| *path == rel && line.contains(piece))
            {
                Some(i) => used[i] = true,
                None => new.push(format!("{rel}:{}  {}", n + 1, line.trim())),
            }
        }
    }
    let gone = listed
        .iter()
        .zip(&used)
        .filter(|(_, u)| !**u)
        .map(|((path, piece, _), _)| format!("{path}  {piece}"))
        .collect();
    (new, gone)
}

#[test]
fn values_are_put_apart_from_what_a_tree_binds() {
    let plain = Regex::new(r"(^|[^_a-zA-Z.])substitute\(").unwrap();
    let (new, gone) = unlisted("src", &plain, PLAIN);
    assert!(
        new.is_empty() && gone.is_empty(),
        "a plain substitute, not listed: use substitute_apart, or list it with why no \
         binder can catch a value there:\n{}\n\nlisted, and no longer found:\n{}",
        new.join("\n"),
        gone.join("\n")
    );
}

#[test]
fn a_citations_values_are_read_in_one_place() {
    let read = Regex::new(r"(^|[^_a-zA-Z.])instantiation\(").unwrap();
    let (new, gone) = unlisted("src/elab", &read, READ);
    assert!(
        new.is_empty() && gone.is_empty(),
        "the elaborator reads a citation's values elsewhere than `instantiated_nodes`: \
         read them with it, or with `instantiated`:\n{}\n\nlisted, and no longer found:\n{}",
        new.join("\n"),
        gone.join("\n")
    );
}
