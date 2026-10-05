//! The checker and the elaborator answer alike where both answer.
//!
//! Each tool answers some questions about a line on its own: what a line
//! implies besides itself, for one. Two answers to one question are two
//! rules, and a proof the one accepts the other refuses. Every theorem is
//! elaborated with each answer compared, as kernel terms, with the checker's
//! to the same question about the same line (`Options::list_answers`).
//!
//! The answers they give differently today are listed in `KNOWN`, each a
//! gap a later change closes. The test fails on any other difference, and on
//! a known one that is gone, so that the list says what is so. This reads
//! set.mm, and fails if set.mm cannot be found.

use std::collections::BTreeSet;
use std::path::Path;
use std::sync::Mutex;

use parley::corpus::corpus;
use parley::elab::elaborate::Options;
use parley::source::{Disk, Memory};
use parley::tools::build::{elaborate_one, library};

/// The differences there are today, of two kinds. The checker reads a part
/// of a set as a member of its power set and the other way round, and the
/// elaborator does not; the elaborator reads a member of a range of integers
/// as an integer, and the checker does not.
const KNOWN: &[&str] = &[
    "proofs/bezout.proof:98 | S ⊆ ℕ | checker only | S ∈ 𝒫ℕ",
    "proofs/cantor.proof:14 | B ⊆ A | checker only | B ∈ 𝒫A",
    "proofs/euler.proof:118 | s ∈ {0, …, n − 1} | elaborator only | 0 ≤ s",
    "proofs/euler.proof:118 | s ∈ {0, …, n − 1} | elaborator only | s ∈ ℂ",
    "proofs/euler.proof:118 | s ∈ {0, …, n − 1} | elaborator only | s ∈ ℚ",
    "proofs/euler.proof:118 | s ∈ {0, …, n − 1} | elaborator only | s ∈ ℝ",
    "proofs/euler.proof:118 | s ∈ {0, …, n − 1} | elaborator only | s ∈ ℤ",
    "proofs/euler.proof:118 | s ∈ {0, …, n − 1} | elaborator only | s ∈ ℕ₀",
    "proofs/euler.proof:121 | t ∈ {0, …, n − 1} | elaborator only | 0 ≤ t",
    "proofs/euler.proof:121 | t ∈ {0, …, n − 1} | elaborator only | t ∈ ℂ",
    "proofs/euler.proof:121 | t ∈ {0, …, n − 1} | elaborator only | t ∈ ℚ",
    "proofs/euler.proof:121 | t ∈ {0, …, n − 1} | elaborator only | t ∈ ℝ",
    "proofs/euler.proof:121 | t ∈ {0, …, n − 1} | elaborator only | t ∈ ℤ",
    "proofs/euler.proof:121 | t ∈ {0, …, n − 1} | elaborator only | t ∈ ℕ₀",
    "proofs/euler.proof:169 | r ∈ {0, …, n − 1} | elaborator only | 0 ≤ r",
    "proofs/euler.proof:169 | r ∈ {0, …, n − 1} | elaborator only | r ∈ ℂ",
    "proofs/euler.proof:169 | r ∈ {0, …, n − 1} | elaborator only | r ∈ ℚ",
    "proofs/euler.proof:169 | r ∈ {0, …, n − 1} | elaborator only | r ∈ ℝ",
    "proofs/euler.proof:169 | r ∈ {0, …, n − 1} | elaborator only | r ∈ ℤ",
    "proofs/euler.proof:169 | r ∈ {0, …, n − 1} | elaborator only | r ∈ ℕ₀",
    "proofs/euler.proof:49 | {0, …, n − 1} ⊆ ℤ | checker only | {0, …, n − 1} ∈ 𝒫ℤ",
    "proofs/euler.proof:54 | S ⊆ {0, …, n − 1} | checker only | S ∈ 𝒫{0, …, n − 1}",
    "proofs/euler.proof:60 | S ⊆ ℤ | checker only | S ∈ 𝒫ℤ",
    "proofs/euler.proof:67 | r ∈ {0, …, n − 1} | elaborator only | 0 ≤ r",
    "proofs/euler.proof:67 | r ∈ {0, …, n − 1} | elaborator only | r ∈ ℂ",
    "proofs/euler.proof:67 | r ∈ {0, …, n − 1} | elaborator only | r ∈ ℚ",
    "proofs/euler.proof:67 | r ∈ {0, …, n − 1} | elaborator only | r ∈ ℝ",
    "proofs/euler.proof:67 | r ∈ {0, …, n − 1} | elaborator only | r ∈ ℤ",
    "proofs/euler.proof:67 | r ∈ {0, …, n − 1} | elaborator only | r ∈ ℕ₀",
    "proofs/euler.proof:95 | r · a mod n ∈ {0, …, n − 1} | elaborator only | 0 ≤ r · a mod n",
    "proofs/euler.proof:95 | r · a mod n ∈ {0, …, n − 1} | elaborator only | r · a mod n ∈ ℂ",
    "proofs/euler.proof:95 | r · a mod n ∈ {0, …, n − 1} | elaborator only | r · a mod n ∈ ℚ",
    "proofs/euler.proof:95 | r · a mod n ∈ {0, …, n − 1} | elaborator only | r · a mod n ∈ ℝ",
    "proofs/euler.proof:95 | r · a mod n ∈ {0, …, n − 1} | elaborator only | r · a mod n ∈ ℤ",
    "proofs/euler.proof:95 | r · a mod n ∈ {0, …, n − 1} | elaborator only | r · a mod n ∈ ℕ₀",
    "proofs/intermediate-value.proof:44 | S ⊆ [a, b] | checker only | S ∈ 𝒫[a, b]",
    "proofs/intermediate-value.proof:47 | [a, b] ⊆ ℝ | checker only | [a, b] ∈ 𝒫ℝ",
    "proofs/intermediate-value.proof:50 | S ⊆ ℝ | checker only | S ∈ 𝒫ℝ",
    "proofs/intermediate-value.proof:89 | [a, b] ⊆ ℝ | checker only | [a, b] ∈ 𝒫ℝ",
    "proofs/lagrange.proof:129 | H ⊆ G | checker only | H ∈ 𝒫G",
    "proofs/lagrange.proof:133 | xH ⊆ aH | checker only | xH ∈ 𝒫(aH)",
    "proofs/lagrange.proof:176 | aH ⊆ G | checker only | aH ∈ 𝒫G",
    "proofs/lagrange.proof:182 | H ⊆ G | checker only | H ∈ 𝒫G",
    "proofs/lagrange.proof:191 | yH ⊆ bH | checker only | yH ∈ 𝒫(bH)",
    "proofs/lagrange.proof:194 | bH ⊆ G | checker only | bH ∈ 𝒫G",
    "proofs/lagrange.proof:203 | bH ⊆ yH | checker only | bH ∈ 𝒫(yH)",
    "proofs/lagrange.proof:223 | H ⊆ G | checker only | H ∈ 𝒫G",
    "proofs/lagrange.proof:289 | ⋃(Y ∈ K) Y ⊆ G | checker only | ⋃(Y ∈ K) Y ∈ 𝒫G",
    "proofs/lagrange.proof:296 | gH ⊆ G | checker only | gH ∈ 𝒫G",
    "proofs/lagrange.proof:314 | G ⊆ ⋃(Y ∈ K) Y | checker only | G ∈ 𝒫(⋃(Y ∈ K) Y)",
    "proofs/lagrange.proof:41 | H ⊆ G | checker only | H ∈ 𝒫G",
    "proofs/lagrange.proof:68 | gH ⊆ G | checker only | gH ∈ 𝒫G",
    "proofs/lagrange.proof:81 | H ⊆ G | checker only | H ∈ 𝒫G",
    "proofs/lagrange.proof:94 | aH ⊆ G | checker only | aH ∈ 𝒫G",
    "proofs/mean-value.proof:102 | (a, b) ⊆ [a, b] | checker only | (a, b) ∈ 𝒫[a, b]",
    "proofs/mean-value.proof:39 | [a, b] ⊆ ℝ | checker only | [a, b] ∈ 𝒫ℝ",
    "proofs/mean-value.proof:80 | (a, b) ⊆ [a, b] | checker only | (a, b) ∈ 𝒫[a, b]",
    "proofs/mean-value.proof:88 | (a, b) ⊆ [a, b] | checker only | (a, b) ∈ 𝒫[a, b]",
    "proofs/mean-value.proof:96 | (a, b) ⊆ [a, b] | checker only | (a, b) ∈ 𝒫[a, b]",
    "proofs/schroeder-bernstein.proof:118 | M(C) ⊆ A ∖ C | checker only | M(C) ∈ 𝒫(A ∖ C)",
    "proofs/schroeder-bernstein.proof:121 | C ⊆ A ∖ M(C) | checker only | C ∈ 𝒫(A ∖ M(C))",
    "proofs/schroeder-bernstein.proof:124 | A ∖ M(C) ⊆ A | checker only | A ∖ M(C) ∈ 𝒫A",
    "proofs/schroeder-bernstein.proof:127 | M(A ∖ M(C)) ⊆ M(C) | checker only | M(A ∖ M(C)) ∈ 𝒫M(C)",
    "proofs/schroeder-bernstein.proof:139 | A ∖ M(C) ⊆ C | checker only | A ∖ M(C) ∈ 𝒫C",
    "proofs/schroeder-bernstein.proof:142 | A ∖ C ⊆ M(C) | checker only | A ∖ C ∈ 𝒫M(C)",
    "proofs/schroeder-bernstein.proof:180 | A ∖ C ⊆ g[B ∖ R] | checker only | A ∖ C ∈ 𝒫g[B ∖ R]",
    "proofs/schroeder-bernstein.proof:235 | C ⊆ A | checker only | C ∈ 𝒫A",
    "proofs/schroeder-bernstein.proof:416 | B ∖ R ⊆ B | checker only | B ∖ R ∈ 𝒫B",
    "proofs/schroeder-bernstein.proof:420 | g[B ∖ R] ⊆ A ∖ C | checker only | g[B ∖ R] ∈ 𝒫(A ∖ C)",
    "proofs/schroeder-bernstein.proof:56 | f[X] ⊆ f[Y] | checker only | f[X] ∈ 𝒫f[Y]",
    "proofs/schroeder-bernstein.proof:59 | B ∖ f[Y] ⊆ B ∖ f[X] | checker only | B ∖ f[Y] ∈ 𝒫(B ∖ f[X])",
    "proofs/schroeder-bernstein.proof:62 | M(Y) ⊆ M(X) | checker only | M(Y) ∈ 𝒫M(X)",
    "proofs/schroeder-bernstein.proof:62 | X ⊆ A | checker only | X ∈ 𝒫A",
    "proofs/schroeder-bernstein.proof:62 | Y ⊆ A | checker only | Y ∈ 𝒫A",
    "proofs/schroeder-bernstein.proof:70 | C ⊆ A | checker only | C ∈ 𝒫A",
    "proofs/schroeder-bernstein.proof:73 | M(C) ⊆ A | checker only | M(C) ∈ 𝒫A",
    "proofs/schroeder-bernstein.proof:80 | X ⊆ A | checker only | X ∈ 𝒫A",
    "proofs/schroeder-bernstein.proof:86 | X ⊆ C | checker only | X ∈ 𝒫C",
    "proofs/schroeder-bernstein.proof:89 | M(C) ⊆ M(X) | checker only | M(C) ∈ 𝒫M(X)",
    "proofs/subsets.proof:111 | S ∪ {a} ⊆ X ∖ {a} | checker only | S ∪ {a} ∈ 𝒫(X ∖ {a})",
    "proofs/subsets.proof:133 | V ⊆ X | checker only | V ∈ 𝒫X",
    "proofs/subsets.proof:146 | V ∖ {a} ⊆ X ∖ {a} | checker only | V ∖ {a} ∈ 𝒫(X ∖ {a})",
    "proofs/subsets.proof:149 | V ∖ {a} ∈ 𝒫(X ∖ {a}) | checker only | V ∖ {a} ⊆ X ∖ {a}",
    "proofs/subsets.proof:169 | V ⊆ X ∖ {a} | checker only | V ∈ 𝒫(X ∖ {a})",
    "proofs/subsets.proof:172 | V ∈ 𝒫(X ∖ {a}) | checker only | V ⊆ X ∖ {a}",
    "proofs/subsets.proof:178 | 𝒫X ⊆ 𝒫(X ∖ {a}) ∪ {S ∪ {a} : S ∈ 𝒫(X ∖ {a})} | checker only | 𝒫X ∈ 𝒫(𝒫(X ∖ {a}) ∪ {S ∪ {a} : S ∈ 𝒫(X ∖ {a})})",
    "proofs/subsets.proof:181 | X ∖ {a} ⊆ X | checker only | X ∖ {a} ∈ 𝒫X",
    "proofs/subsets.proof:184 | 𝒫(X ∖ {a}) ⊆ 𝒫X | checker only | 𝒫(X ∖ {a}) ∈ 𝒫(𝒫X)",
    "proofs/subsets.proof:191 | S ⊆ X ∖ {a} | checker only | S ∈ 𝒫(X ∖ {a})",
    "proofs/subsets.proof:194 | S ⊆ X | checker only | S ∈ 𝒫X",
    "proofs/subsets.proof:197 | {a} ⊆ X | checker only | {a} ∈ 𝒫X",
    "proofs/subsets.proof:200 | S ∪ {a} ⊆ X | checker only | S ∪ {a} ∈ 𝒫X",
    "proofs/subsets.proof:203 | S ∪ {a} ∈ 𝒫X | checker only | S ∪ {a} ⊆ X",
    "proofs/subsets.proof:206 | {S ∪ {a} : S ∈ 𝒫(X ∖ {a})} ⊆ 𝒫X | checker only | {S ∪ {a} : S ∈ 𝒫(X ∖ {a})} ∈ 𝒫(𝒫X)",
    "proofs/subsets.proof:209 | 𝒫(X ∖ {a}) ∪ {S ∪ {a} : S ∈ 𝒫(X ∖ {a})} ⊆ 𝒫X | checker only | 𝒫(X ∖ {a}) ∪ {S ∪ {a} : S ∈ 𝒫(X ∖ {a})} ∈ 𝒫(𝒫X)",
    "proofs/subsets.proof:52 | S ⊆ X | checker only | S ∈ 𝒫X",
    "proofs/subsets.proof:55 | T ⊆ X | checker only | T ∈ 𝒫X",
    "tests/stdlib/calculus.proof:15 | ℝ ⊆ ℝ | checker only | ℝ ∈ 𝒫ℝ",
];

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
    let found: BTreeSet<String> = found.into_inner().unwrap();
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
