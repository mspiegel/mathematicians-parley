//! A citation's values are read together.
//!
//! A fault came back again and again while the corpus was rewritten
//! (`tests/invariance.rs`): a citation's values were read one after
//! another, so that `a := b/k, b := a/k` read the second in the first's new
//! name. It was fixed where it was found, and lived on in another place that
//! did the same thing its own way. So the elaborator reads a citation's
//! values only through `instantiated_nodes`, which reads them all before
//! any is given.
//!
//! The other fault of that kind, a value put under a binder that uses one
//! of its letters and caught by it, the compiler now rules out: the only
//! way to put a value into a tree is `substitute_apart`, which keeps it
//! apart from a binder's letter.

use std::path::{Path, PathBuf};

use regex::Regex;

/// Where the elaborator reads a citation's values, which is one place.
const READ: &[(&str, &str, &str)] = &[(
    "src/elab/elaborate.rs",
    "namings(cites,",
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
fn a_citations_values_are_read_in_one_place() {
    let read = Regex::new(r"(^|[^_a-zA-Z.])(instantiation|namings)\(").unwrap();
    let (new, gone) = unlisted("src/elab", &read, READ);
    assert!(
        new.is_empty() && gone.is_empty(),
        "the elaborator reads a citation's values elsewhere than `instantiated_nodes`: \
         read them with it, or with `instantiated`:\n{}\n\nlisted, and no longer found:\n{}",
        new.join("\n"),
        gone.join("\n")
    );
}
