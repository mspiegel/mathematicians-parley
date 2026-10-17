//! A proof means what it says, however it spells it.
//!
//! A rule that reads the spelling of a line rather than what it says accepts
//! one proof and refuses the same proof written another way: `k ≥ 0` and
//! `0 ≤ k` are one fact, and so are `a = b` and `b = a`. Each change
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

use parley::checker::{checked, CheckedCorpus};
use parley::corpus::corpus;
use parley::corpus::proof::cited_items;
use parley::elab::elaborate::Options;
use parley::elab::Library;
use parley::mm::where_set_mm;
use parley::source::{Disk, Memory, Overlay, Source};
use parley::threads::{in_order, in_order_on};
use parley::tools::build::{checked_in, library, verified, Libraries, Loaded};
use parley::tools::{path_of, verify};

#[path = "invariance/rewrites.rs"]
mod rewrites;

mod record;

use rewrites::{Context, Declined, Rewritten};

/// The breaks there are, each a gap a later change closes.
const KNOWN: &[&str] = &[];

/// How many changes' files are verified at once.
const VERIFYING: usize = 3;

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
            name: "bound letters renamed to the library's letters",
            rewrite: Rewrite::File(rewrites::bound_letters_to_library),
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
        Change {
            name: "a step that serves only requires lines written as one",
            rewrite: Rewrite::File(rewrites::dull_steps_moved),
        },
        Change {
            name: "a requires line citing an item written as a step before its own",
            rewrite: Rewrite::File(rewrites::requires_raised),
        },
        Change {
            name: "a define in a proof raised to the start of its run of steps",
            rewrite: Rewrite::File(rewrites::defines_raised),
        },
        Change {
            name: "a block made a lemma",
            rewrite: Rewrite::File(rewrites::blocks_lifted),
        },
        Change {
            name: "an obtain from an item written as a step claiming its \"there is\"",
            rewrite: Rewrite::File(rewrites::obtains_claimed),
        },
        Change {
            name: "a define in a theorem's header raised above the theorem",
            rewrite: Rewrite::File(rewrites::header_defines_raised),
        },
        Change {
            name: "a define in a proof lowered into its theorem's header",
            rewrite: Rewrite::File(rewrites::defines_lowered),
        },
        Change {
            name: "a line cited once restated by a step that joins it",
            rewrite: Rewrite::File(rewrites::cited_lines_restated),
        },
        Change {
            name: "a step citing an item written as a requires line of its citer",
            rewrite: Rewrite::File(rewrites::steps_as_requires),
        },
    ]
}

/// `line` with the lines and labels of its `from` list in the order the
/// checker asks for; a list ends where a word that cites nothing starts, as
/// `contradicting 2` does. A `transitivity` step's list is in the chain's
/// order, and is left as it is (`SYNTAX.md`, a list is in order).
fn cited_in_written_order(line: &str) -> String {
    if line.trim_start().starts_with("transitivity,") {
        return line.to_string();
    }
    let Some(at) = line.rfind("from ") else {
        return line.to_string();
    };
    let (head, rest) = line.split_at(at + "from ".len());
    let parts: Vec<&str> = rest.split(", ").collect();
    let cited = parts
        .iter()
        .take_while(|r| {
            !r.is_empty()
                && r.chars()
                    .all(|c| c.is_alphanumeric() || c == '.' || c == '′')
        })
        .count();
    let ordered = parley::checker::cited_in_order(&parts[..cited]);
    let tail = &parts[cited..];
    format!(
        "{head}{}",
        ordered
            .iter()
            .chain(tail)
            .copied()
            .collect::<Vec<_>>()
            .join(", ")
    )
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

/// Change `i`'s tree as the checker reads it, with its records of the
/// theorems a round builds and of no other: a thread reads the tree once a
/// round, and checking the whole corpus for it was half of this test's time.
fn round_checked(tree: &Memory, i: usize, jobs: &[(usize, String)]) -> CheckedCorpus {
    let wanted: BTreeSet<&str> = jobs
        .iter()
        .filter(|(j, _)| *j == i)
        .map(|(_, name)| name.as_str())
        .collect();
    checked_in(tree, |n| wanted.contains(n)).expect("the changed corpus reads")
}

fn changed(clean: &Memory, context: &Context, change: &Change) -> Changed {
    let mut tree = Overlay::new(clean);
    let mut files = Vec::new();
    let mut lines = 0;
    let mut theorems = Vec::new();
    let mut declined = Vec::new();
    // The corpus's proofs, the elaborator's test proofs, which are where a
    // method or notation no theorem uses yet is written first, the
    // library's, which prove what each item says at one instance, each
    // notation's textbook examples, and the proofs the syntax documents'
    // examples stand in. The corpus's proofs are in a directory for each
    // collection under `proofs/`.
    const DIRS: [&str; 5] = [
        "proofs/",
        "tests/elaborator/",
        "tests/stdlib/",
        "tests/notations/",
        "tests/docs/",
    ];
    let mut paths: Vec<String> = clean
        .found(".proof")
        .into_iter()
        .filter(|p| DIRS.iter().any(|d| p.starts_with(d)))
        .collect();
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
    for ((path, mut done), (_, text)) in rewritten.into_iter().zip(&texts) {
        // A rewrite that renames or adds a cited line or label writes its
        // list as the language orders it, as a writer would.
        done.text = done
            .text
            .split('\n')
            .map(cited_in_written_order)
            .collect::<Vec<_>>()
            .join("\n");
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

/// A rewrite that changes only how a line is spelt leaves what the checker
/// hands the build as it was: each theorem of a file it changed has the
/// record it had (`record::printed_but`), so the build is handed one meaning
/// however a line spells it. A requires line the rewrite changed may be
/// read under another binding that fits it as well, `triangle` at the
/// points of an equation turned round, so its own citation is left out.
/// This half checks alone, and builds nothing.
#[test]
fn a_line_spelt_otherwise_leaves_the_record_as_it_was() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let clean = Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap();
    let before = checked(&clean).unwrap_or_else(|out| panic!("{}", out.printed));
    let context = Context::new(
        corpus(&clean).expect("the corpus reads"),
        parley::checker::obtained_there(&clean).expect("the corpus reads"),
        parley::checker::bound_there(&clean).expect("the corpus reads"),
    );
    let mut compared = 0;
    let mut differ = Vec::new();
    for change in changes() {
        if !matches!(change.rewrite, Rewrite::Line(_)) {
            continue;
        }
        let done = changed(&clean, &context, &change);
        let after = checked(&done.tree).unwrap_or_else(|out| panic!("{}", out.printed));
        for thm in &after.corpus.theorems {
            if !done.files.contains(&thm.path) {
                continue;
            }
            let name = thm.qualified();
            let rewritten = rewritten_requires(&before, thm);
            let omitted = |at: &str| rewritten.contains(at);
            let (was, now) = (
                record::printed_but(&before, &name, &omitted),
                record::printed_but(&after, &name, &omitted),
            );
            compared += 1;
            if was != now {
                differ.push(format!(
                    "{} | {name}\n--- was\n{was}--- now\n{now}",
                    change.name
                ));
            }
        }
    }
    // A test over nothing says nothing.
    assert!(compared > 100, "only {compared} records were compared");
    assert!(differ.is_empty(), "{}", differ.join("\n"));
}

/// The requires lines of `after` whose fact is written otherwise than in
/// the same theorem as `before` read it, by their place in their step,
/// `requires line 1 of step 2`.
fn rewritten_requires(
    before: &CheckedCorpus,
    after: &parley::corpus::Theorem,
) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let Some(was) = before
        .corpus
        .theorems
        .iter()
        .find(|t| t.qualified() == after.qualified())
    else {
        return out;
    };
    for (old, new) in was.steps.iter().zip(&after.steps) {
        for (a, b) in old.requires.iter().zip(&new.requires) {
            if a.fact.text() != b.fact.text() {
                out.insert(record::requires_at(after, b.line));
            }
        }
    }
    out
}

#[test]
fn a_proof_means_what_it_says_however_it_spells_it() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let clean = Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap();
    let base = parley::checker::run(&clean);
    assert!(
        base.printed.contains("\n0 problem(s)\n"),
        "the corpus is not clean, so a change proves nothing:\n{}",
        base.printed
    );
    // INVARIANCE_ONLY keeps the changes whose name holds it, to work on one
    // change; the known breaks are then those of the changes kept.
    let only = std::env::var("INVARIANCE_ONLY").ok();
    let changes: Vec<Change> = changes()
        .into_iter()
        .filter(|c| only.as_ref().is_none_or(|o| c.name.contains(o.as_str())))
        .collect();
    let context = Context::new(
        corpus(&clean).expect("the corpus reads"),
        parley::checker::obtained_there(&clean).expect("the corpus reads"),
        parley::checker::bound_there(&clean).expect("the corpus reads"),
    );
    let trees: Vec<Changed> = changes
        .iter()
        .map(|c| changed(&clean, &context, c))
        .collect();
    let mut found: BTreeSet<String> = BTreeSet::new();
    // What the checker says of each changed corpus.
    let checked: Vec<String> = in_order(
        &trees,
        || (),
        |_, done| parley::checker::run(&done.tree).printed,
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
    // Each with the theorems of the same change it cites, which are built
    // first, as the build builds what a theorem cites before it: a theorem a
    // change wrote, a lemma lifted out of a block, has no file until then.
    let mut work: Vec<(usize, String, Vec<String>)> = Vec::new();
    for (i, done) in trees.iter().enumerate() {
        let thms = corpus(&done.tree)
            .expect("the changed corpus reads")
            .theorems;
        let changed: BTreeSet<String> = thms
            .iter()
            .filter(|t| done.files.contains(&t.path))
            .map(|t| t.qualified())
            .collect();
        for thm in &thms {
            if done.files.contains(&thm.path) {
                let cites: Vec<String> = cited_items(thm)
                    .into_iter()
                    .map(|(c, _)| c)
                    .filter(|c| changed.contains(c) && *c != thm.qualified())
                    .collect();
                work.push((i, thm.qualified(), cites));
            }
        }
    }
    let read = library(root, None)
        .expect(
            "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
        )
        .shared();
    // What each change built, verified as the gate verifies the tree: every
    // file the tree holds, each built one in place of the one committed.
    // Only a change that built some file otherwise than it is committed is
    // verified, since the committed files are the gate's to verify.
    let mut made: Vec<BTreeMap<String, String>> =
        trees.iter().map(|_| BTreeMap::new()).collect();
    let mut finished: Vec<BTreeSet<String>> =
        trees.iter().map(|_| BTreeSet::new()).collect();
    let mut pending: Vec<&(usize, String, Vec<String>)> = work.iter().collect();
    while !pending.is_empty() {
        let mut ready: Vec<&(usize, String, Vec<String>)> = pending
            .iter()
            .copied()
            .filter(|(i, _, cites)| cites.iter().all(|c| finished[*i].contains(c)))
            .collect();
        // Theorems citing each other round about are built as they stand.
        if ready.is_empty() {
            ready = pending.clone();
        }
        pending.retain(|w| !ready.contains(w));
        // Each change's tree with what it has built so far, where this round
        // builds any of it.
        let overlays: Vec<Option<Memory>> = trees
            .iter()
            .zip(&made)
            .enumerate()
            .map(|(i, (t, m))| {
                if !ready.iter().any(|(j, _, _)| *j == i) {
                    return None;
                }
                let mut o = Overlay::new(&t.tree);
                for (path, text) in m {
                    o.write(path, text.clone().into_bytes());
                }
                Some(Memory::copy(&o, &["corpus", "proofs", "tests"]).unwrap())
            })
            .collect();
        let jobs: Vec<(usize, String)> =
            ready.iter().map(|(i, n, _)| (*i, n.clone())).collect();
        let built = in_order(
            &jobs,
            || (Library::new(Arc::clone(&read)), BTreeMap::new()),
            |(lib, loaded): &mut (Library, BTreeMap<usize, Loaded>), (i, name)| {
                let tree = loaded.entry(*i).or_insert_with(|| {
                    let overlay =
                        overlays[*i].as_ref().expect("a tree this round builds");
                    Loaded::with_checked(overlay, round_checked(overlay, *i, &jobs))
                });
                tree.elaborate(name, lib, Options::default())
                    .map(|e| e.text)
                    .map_err(|p| format!("{} | elaborate | {p}", changes[*i].name))
            },
        );
        for ((i, name), result) in jobs.iter().zip(built) {
            finished[*i].insert(name.clone());
            match result {
                Ok(text) => {
                    let path = path_of(name);
                    if trees[*i].tree.read_text(&path).ok().as_deref()
                        != Some(text.as_str())
                    {
                        made[*i].insert(path, text);
                    }
                }
                Err(broke) => {
                    found.insert(broke);
                }
            }
        }
    }
    let libraries = Libraries::read_verifying_often(
        &where_set_mm(None, root)
            .expect("set.mm is found: say where it is with SET_MM"),
    )
    .expect("set.mm reads");
    // A few at a time: each verification runs on every core already, and
    // holds a copy of set.mm of its own.
    let to_verify: Vec<usize> =
        (0..trees.len()).filter(|&i| !made[i].is_empty()).collect();
    let verdicts = in_order_on(
        VERIFYING,
        &to_verify,
        || (),
        |_, &i| {
            let mut tree = Overlay::new(&trees[i].tree);
            for (path, text) in &made[i] {
                tree.write(path, text.clone().into_bytes());
            }
            let every = verified(&corpus(&tree).expect("the changed corpus reads"));
            verify::run(&tree, &every, Some(&libraries))
        },
    );
    for (&i, said) in to_verify.iter().zip(verdicts) {
        println!(
            "{}: {} files built otherwise, verified",
            changes[i].name,
            made[i].len()
        );
        if !said.green() {
            found.insert(format!(
                "{} | verify | {}",
                changes[i].name,
                said.printed.trim().replace('\n', " | ")
            ));
        }
    }
    let known: BTreeSet<String> = KNOWN
        .iter()
        .filter(|k| {
            changes
                .iter()
                .any(|c| k.starts_with(&format!("{} |", c.name)))
        })
        .map(|s| s.to_string())
        .collect();
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
