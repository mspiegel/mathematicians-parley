//! What more than one test needs: numbers drawn the same way on every run
//! with one seed, and the files a verifier is handed for one elaborated
//! file.

use std::collections::BTreeSet;

use parley::source::Source;
use parley::tools::ELABORATION;

/// Numbers drawn by xorshift: a test drawing from one seed draws the same
/// on every run, so what it found is found again from the seed it prints.
pub struct Random {
    state: u64,
}

impl Random {
    pub fn new(seed: u64) -> Random {
        Random { state: seed.max(1) }
    }

    /// A number below `n`, which is at least 1.
    pub fn below(&mut self, n: u64) -> u64 {
        self.state ^= self.state << 13;
        self.state ^= self.state >> 7;
        self.state ^= self.state << 17;
        self.state % n
    }
}

/// The files `path` includes, and the files they include, by their paths in
/// the tree: what a verifier is handed to check it.
pub fn included(tree: &dyn Source, path: &str, text: &str) -> Vec<String> {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut todo: Vec<String> = vec![text.to_string()];
    seen.insert(path.to_string());
    while let Some(text) = todo.pop() {
        for part in text.split("$[").skip(1) {
            let Some(name) = part.split("$]").next().map(str::trim) else {
                continue;
            };
            let at = format!("{ELABORATION}/{name}");
            if tree.exists(&at) && seen.insert(at.clone()) {
                todo.push(tree.read_text(&at).expect("an included file reads"));
            }
        }
    }
    seen.into_iter().collect()
}
