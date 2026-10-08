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
//!
//! Some changes rewrite a theorem as a whole: its letters renamed, its
//! claims' sentences joined or split, a part of a claim named by a define
//! (`invariance/rewrites.rs`). Where such a
//! change cannot tell that it keeps a theorem's meaning, a letter written
//! where no formula is read, it leaves the theorem alone and says so, and
//! the test prints how many theorems each change reached. The letters a
//! cited theorem's statement writes are left as they are: its citers name
//! them, and its elaborated statement, which they read, is not built again
//! here.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::Arc;

use parley::corpus::corpus;
use parley::elab::elaborate::Options;
use parley::elab::Library;
use parley::source::{Disk, Memory, Overlay, Source};
use parley::threads::in_order;
use parley::tools::build::{library, Loaded};

#[path = "invariance/rewrites.rs"]
mod rewrites;

use rewrites::{Context, Declined, Rewritten};

/// The breaks there are, each a gap a later change closes.
const KNOWN: &[&str] = &[];

/// How a change rewrites a proof file.
enum Rewrite {
    /// Line by line: the line rewritten, or None where the change does not
    /// apply to it.
    Line(fn(&str) -> Option<String>),
    /// The file at once, theorem by theorem.
    File(fn(&Context, &str, &str) -> Rewritten),
    /// Every proof file at once: a change to one theorem that every theorem
    /// citing it must follow.
    Corpus(EveryFile),
}

/// A rewrite of every proof file, each given and given back as `(path,
/// text)`.
type EveryFile = fn(&Context, &[(String, String)]) -> Vec<(String, Rewritten)>;

/// One rewriting that keeps what a proof says.
struct Change {
    name: &'static str,
    rewrite: Rewrite,
}

fn changes() -> Vec<Change> {
    vec![
        Change {
            name: "cited lines in the other order",
            rewrite: Rewrite::Line(reversed_from),
        },
        Change {
            name: "no spaces around operators in a requires line",
            rewrite: Rewrite::Line(unspaced),
        },
        Change {
            name: "an order in a requires line turned around",
            rewrite: Rewrite::Line(order_turned),
        },
        Change {
            name: "an equation in a requires line turned around",
            rewrite: Rewrite::Line(equation_turned),
        },
        Change {
            name: "the values of a citation in the other order",
            rewrite: Rewrite::Line(rewrites::values_reversed),
        },
        Change {
            name: "two letters of a theorem swapped",
            rewrite: Rewrite::File(rewrites::letters_swapped),
        },
        Change {
            name: "introduced letters renamed to the library's letters",
            rewrite: Rewrite::File(rewrites::letters_to_library),
        },
        Change {
            name: "an introduced letter renamed i",
            rewrite: Rewrite::File(rewrites::letter_to_i),
        },
        Change {
            name: "a conjunction claim written as sentences",
            rewrite: Rewrite::File(rewrites::claims_split),
        },
        Change {
            name: "a relation in a claim or an assumption turned around",
            rewrite: Rewrite::File(rewrites::relations_turned),
        },
        Change {
            name: "a cited theorem's letters renamed, and its citations with them",
            rewrite: Rewrite::Corpus(rewrites::statements_renamed),
        },
        Change {
            name: "a part of a claim named by a define",
            rewrite: Rewrite::File(rewrites::parts_named),
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

/// The corpus with one change made to every proof file.
struct Changed {
    tree: Memory,
    /// The files it changed.
    files: Vec<String>,
    /// How many lines it changed.
    lines: usize,
    /// The theorems it changed, where it rewrites theorem by theorem.
    theorems: Vec<String>,
    /// The theorems it left alone, and why.
    declined: Vec<Declined>,
}

/// A file rewritten a line at a time.
fn each_line(text: &str, line: fn(&str) -> Option<String>) -> Rewritten {
    let mut edited = Vec::new();
    let mut lines = 0;
    for l in text.lines() {
        match line(l) {
            Some(new) => {
                edited.push(new);
                lines += 1;
            }
            None => edited.push(l.to_string()),
        }
    }
    let mut out = edited.join("\n");
    if text.ends_with('\n') {
        out.push('\n');
    }
    Rewritten {
        text: out,
        lines,
        theorems: Vec::new(),
        declined: Vec::new(),
    }
}

fn changed(clean: &Memory, root: &Path, context: &Context, change: &Change) -> Changed {
    let mut tree = Overlay::new(clean);
    let mut files = Vec::new();
    let mut lines = 0;
    let mut theorems = Vec::new();
    let mut declined = Vec::new();
    // The corpus's proofs, the elaborator's test proofs, which are where a
    // method or notation no theorem uses yet is written first, and the
    // library's, which prove what each item says at one instance.
    let mut paths: Vec<String> = Vec::new();
    for dir in ["proofs", "tests/elaborator", "tests/stdlib"] {
        paths.extend(
            std::fs::read_dir(root.join(dir))
                .expect("a proof directory reads")
                .filter_map(|e| e.ok())
                .map(|e| e.file_name().to_string_lossy().to_string())
                .filter(|n| n.ends_with(".proof"))
                .map(|n| format!("{dir}/{n}")),
        );
    }
    paths.sort();
    let texts: Vec<(String, String)> = paths
        .into_iter()
        .map(|p| {
            let text = clean.read_text(&p).expect("a proof file reads");
            (p, text)
        })
        .collect();
    let rewritten: Vec<(String, Rewritten)> = match change.rewrite {
        Rewrite::Line(line) => texts
            .iter()
            .map(|(p, t)| (p.clone(), each_line(t, line)))
            .collect(),
        Rewrite::File(file) => texts
            .iter()
            .map(|(p, t)| (p.clone(), file(context, p, t)))
            .collect(),
        Rewrite::Corpus(all) => all(context, &texts),
    };
    for ((path, done), (_, text)) in rewritten.into_iter().zip(&texts) {
        declined.extend(done.declined);
        theorems.extend(done.theorems);
        if done.lines > 0 && done.text != *text {
            // INVARIANCE_DUMP names a directory to hold each rewritten file,
            // under the change's name, to read a break against.
            if let Ok(dir) = std::env::var("INVARIANCE_DUMP") {
                let out = Path::new(&dir)
                    .join(change.name.replace(' ', "-"))
                    .join(&path);
                std::fs::create_dir_all(out.parent().unwrap()).unwrap();
                std::fs::write(&out, &done.text).unwrap();
            }
            tree.write(&path, done.text.into_bytes());
            files.push(path);
            lines += done.lines;
        }
    }
    let copied = Memory::copy(&tree, &["corpus", "proofs", "tests"]).unwrap();
    Changed {
        tree: copied,
        files,
        lines,
        theorems,
        declined,
    }
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
    let context = Context::new(corpus(&clean).expect("the corpus reads"));
    let trees: Vec<Changed> = changes
        .iter()
        .map(|c| changed(&clean, root, &context, c))
        .collect();
    let mut found: BTreeSet<String> = BTreeSet::new();
    // What the checker says of each changed corpus.
    let checked: Vec<String> = in_order(
        &trees,
        || (),
        |_, done| parley::check::run(&done.tree).printed,
    );
    for ((change, done), said) in changes.iter().zip(&trees).zip(&checked) {
        println!(
            "{}: {} lines in {} files, {} theorems changed, {} left alone",
            change.name,
            done.lines,
            done.files.len(),
            done.theorems.len(),
            done.declined.len()
        );
        for d in &done.declined {
            println!("    left alone {}: {}", d.theorem, d.why);
        }
        assert!(done.lines > 0, "{} changes no line", change.name);
        for line in said.lines().filter(|l| l.contains(".proof:")) {
            found.insert(format!("{} | check | {line}", change.name));
        }
    }
    // Every theorem of a changed file, elaborated against set.mm read once.
    // A thread has a library of its own on what was read, and reads each
    // changed corpus it is asked a theorem of once.
    let mut work: Vec<(usize, String)> = Vec::new();
    for (i, done) in trees.iter().enumerate() {
        for thm in corpus(&done.tree)
            .expect("the changed corpus reads")
            .theorems
        {
            if done.files.contains(&thm.path) {
                work.push((i, thm.qualified()));
            }
        }
    }
    let read = library(root, None)
        .expect(
            "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
        )
        .shared();
    let broken = in_order(
        &work,
        || (Library::new(Arc::clone(&read)), BTreeMap::new()),
        |(lib, loaded): &mut (Library, BTreeMap<usize, Loaded>), (i, name)| {
            let tree = loaded.entry(*i).or_insert_with(|| {
                Loaded::new(&trees[*i].tree).expect("the changed corpus reads")
            });
            tree.elaborate(name, lib, Options::default())
                .err()
                .map(|p| format!("{} | elaborate | {p}", changes[*i].name))
        },
    );
    found.extend(broken.into_iter().flatten());
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
