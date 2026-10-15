//! A wrong proof is refused somewhere, and never verified.
//!
//! Each mutant is the corpus with one edit that keeps a proof well formed
//! and, most often, makes it wrong: a numeral one more, an order turned
//! around or made strict, a cited line or item another, a line left out of
//! a citation, a hypothesis taken out of a statement, two values of a
//! citation swapped. The mutated theorem is then asked of the checker, and
//! where the checker accepts it, of the elaborator, and where the
//! elaborator builds it, of the verifier.
//!
//! A mutant the checker and the elaborator accept and the verifier refuses
//! is a fault of the tools: a step built that the kernel would not take,
//! from a page neither reader found wrong. So is an elaboration that
//! panics where it would report a defect, and a file built that assumes
//! anything. The test fails on any of these. A mutant all three accept
//! proves what its page now says, which an edit can leave true (a weaker
//! order, a surplus line dropped); it is listed for reading, with each
//! mutant the checker accepted and the elaborator refused. So is a file
//! built exactly as committed from a page whose formula changed: the
//! kernel proof does not say the line, which is right only where the line
//! says what another line already does, or the same fact. An obtain whose
//! claim was not what it obtains was found among these.
//!
//! Each file is verified with what it includes and set.mm, and no other,
//! as a reader verifying that one file would.
//!
//! The mutants are many and each the checker accepts is elaborated, so the
//! test is not run with the others. `MUTANTS` says how many to take, in an
//! order shuffled by `MUTATION_SEED`, every one where it is not set:
//!
//! ```text
//! MUTANTS=500 cargo test --release --test mutation -- --ignored --nocapture
//! ```
//!
//! `MUTATION_AT=proofs/bezout.proof:87` asks again of the mutants at the
//! lines it lists.
//!
//! This reads set.mm, and fails if set.mm cannot be found.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::Arc;

use parley::checker::{check_cuts, Cut};
use parley::citing::largest_search;
use parley::corpus::corpus;
use parley::corpus::proof::Theorem;
use parley::elab::elaborate::Options;
use parley::elab::Library;
use parley::mm::where_set_mm;
use parley::source::{Disk, Memory, Overlay, Source};
use parley::threads::{in_order, in_order_on};
use parley::tools::build::{library, Libraries, Loaded};
use parley::tools::{path_of, verify};

#[path = "shared/mod.rs"]
mod shared;

use shared::{included, Random};

/// The seed the order of the mutants is shuffled by where `MUTATION_SEED`
/// does not say another.
const SEED: u64 = 20_261_011;

/// What an elaboration that panicked is given back as, before what the
/// panic said.
const PANICKED: &str = "panicked: ";

/// How many mutants one call of the checker is asked of, reading the corpus
/// once for them.
const SHARE: usize = 50;

/// The most one citation search may ask of the mutants (`largest_search`).
/// A step citing the wrong line searches further than a right one, so this
/// is above what the corpus is held to (`tests/search_size.rs`).
const SEARCHED: usize = 4_000;

/// How long checking a share may run before the test names its mutants.
const SLOW: std::time::Duration = std::time::Duration::from_secs(60);

/// How many verifications run at once: each runs on every core already,
/// and holds a copy of set.mm of its own.
const VERIFYING: usize = 3;

/// The edit a mutant makes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Edit {
    /// A numeral of a formula one more: `k + 1` as `k + 2`.
    Numeral,
    /// An order turned the other way: `a < b` as `a > b`.
    Reversed,
    /// An order made strict, or not: `a < b` as `a ≤ b`.
    Strictness,
    /// A number system the next smaller one: `d ∈ ℤ` as `d ∈ ℕ`.
    Narrowed,
    /// One line or label left out of a `from`.
    Dropped,
    /// A cited line another line of the theorem, or a cited label another
    /// label of its statement.
    OtherLine,
    /// A cited item another item its file cites with the same prefix.
    OtherItem,
    /// A labelled hypothesis taken out of the statement, and out of every
    /// `from` that names it.
    Hypothesis,
    /// The values of two pairs of a citation swapped: `a := x, b := y` as
    /// `a := y, b := x`.
    Swapped,
}

impl Edit {
    fn name(self) -> &'static str {
        match self {
            Edit::Numeral => "a numeral one more",
            Edit::Reversed => "an order turned the other way",
            Edit::Strictness => "an order made strict or not",
            Edit::Narrowed => "a number system narrowed",
            Edit::Dropped => "a cited line left out",
            Edit::OtherLine => "another line cited",
            Edit::OtherItem => "another item cited",
            Edit::Hypothesis => "a hypothesis taken out",
            Edit::Swapped => "two values of a citation swapped",
        }
    }

    /// Whether the edit changes what a line says, rather than what it
    /// cites: built as committed, the kernel proof does not say the line,
    /// which is right only where the line says what another line already
    /// says (`requires n! ∈ ℕ: from 1`, with 1 saying it) or is the same
    /// fact (`a ≥ a` for `a ≤ a`).
    fn says(self) -> bool {
        matches!(
            self,
            Edit::Numeral | Edit::Reversed | Edit::Strictness | Edit::Narrowed
        )
    }
}

/// One mutant: a proof file with one edit made.
struct Mutant {
    edit: Edit,
    path: String,
    /// The theorem's name in its file, and its qualified name.
    theorem: String,
    qualified: String,
    /// The line edited, counting from 1, as it was and as it is.
    line: usize,
    was: String,
    now: String,
    /// What justifies the step the line sits in, `algebra` or
    /// `mun:sum-single`, or `statement` where the line is the theorem's.
    under: String,
    text: String,
}

/// What became of a mutant.
#[derive(Clone, Debug)]
enum Fate {
    /// The checker refused it.
    Checker,
    /// The checker accepted it and the elaborator refused it.
    Elaborator(String),
    /// The elaborator built what is committed: the edit changed nothing the
    /// kernel reads.
    Unchanged,
    /// The elaborator stopped with a panic, where a defect is reported.
    Panicked(String),
    /// The elaborator built a file that assumes something.
    Assumed(String),
    /// The verifier refused what was built.
    Kernel(String),
    /// Verified: the page proves what it now says.
    Survived,
}

impl Fate {
    /// The fault of the tools this fate is, if it is one.
    fn fault(&self) -> Option<String> {
        match self {
            Fate::Panicked(what) => Some(format!("the elaborator panicked: {what}")),
            Fate::Assumed(what) => Some(format!("assumes {what}")),
            Fate::Kernel(what) => Some(format!("the verifier refused it: {what}")),
            _ => None,
        }
    }

    fn column(&self) -> usize {
        match self {
            Fate::Checker => 0,
            Fate::Elaborator(_) => 1,
            Fate::Unchanged | Fate::Survived => 2,
            Fate::Panicked(_) | Fate::Assumed(_) | Fate::Kernel(_) => 3,
        }
    }
}

/// Where a mutant edits a theorem: a line, by its index in the file, and
/// the formula on it an edit of a formula is made within.
struct Formula {
    at: usize,
    text: String,
}

/// The theorem's formulas, each with the line it is on: its hypotheses and
/// conclusion, its steps' claims, the rows of its calculations and its
/// requires lines' facts.
fn formulas(thm: &Theorem, lines: &[&str]) -> Vec<Formula> {
    let mut out = Vec::new();
    for h in &thm.hypotheses {
        out.push(Formula {
            at: h.line - 1,
            text: h.text.clone(),
        });
    }
    out.push(Formula {
        at: thm.conclusion_line - 1,
        text: thm.conclusion.clone(),
    });
    for step in &thm.steps {
        // A claim may run over several lines, up to its justification's; the
        // first starts after the step's number. A claim on one line is the
        // claim as read, without a closing `, which is impossible`.
        let claimed = &lines[step.line - 1..step.just.line - 1];
        if let [_] = claimed {
            out.push(Formula {
                at: step.line - 1,
                text: step.claim_text(),
            });
        } else {
            for (at, written) in (step.line - 1..).zip(claimed) {
                let written = str::trim(written);
                let text = if at == step.line - 1 {
                    written
                        .split_once(char::is_whitespace)
                        .map_or("", |(_, c)| c)
                } else {
                    written
                };
                out.push(Formula {
                    at,
                    text: str::trim(text).to_string(),
                });
            }
        }
        for (row, line) in &step.just.chain {
            out.push(Formula {
                at: line - 1,
                text: row.clone(),
            });
        }
        for r in &step.requires {
            out.push(Formula {
                at: r.line - 1,
                text: r.fact.text().to_string(),
            });
        }
    }
    out
}

/// Each numeral of `text` one more, one at a time. A numeral is a run of
/// digits standing alone: not in `H1`, `x₁` or a line's number `1.3`.
fn numerals(text: &str) -> Vec<String> {
    let chars: Vec<(usize, char)> = text.char_indices().collect();
    let joins = |c: char| c.is_alphanumeric() || c == '_' || c == '′';
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        if !chars[i].1.is_ascii_digit() {
            i += 1;
            continue;
        }
        let start = i;
        while i < chars.len() && chars[i].1.is_ascii_digit() {
            i += 1;
        }
        let before = start.checked_sub(1).map(|b| chars[b].1);
        let after = chars.get(i).map(|c| c.1);
        let after_next = chars.get(i + 1).map(|c| c.1);
        let alone = !before.is_some_and(|c| joins(c) || c == '.')
            && !after.is_some_and(joins)
            && !(after == Some('.') && after_next.is_some_and(|c| c.is_ascii_digit()));
        if !alone {
            continue;
        }
        let from = chars[start].0;
        let to = chars.get(i).map_or(text.len(), |c| c.0);
        let Ok(n) = text[from..to].parse::<u64>() else {
            continue;
        };
        out.push(format!("{}{}{}", &text[..from], n + 1, &text[to..]));
    }
    out
}

/// Each order sign of `text` replaced as `turn` says, one at a time.
fn orders(text: &str, turn: fn(char) -> Option<char>) -> Vec<String> {
    text.char_indices()
        .filter_map(|(at, c)| {
            let to = turn(c)?;
            Some(format!("{}{to}{}", &text[..at], &text[at + c.len_utf8()..]))
        })
        .collect()
}

fn reversed(c: char) -> Option<char> {
    match c {
        '<' => Some('>'),
        '>' => Some('<'),
        '≤' => Some('≥'),
        '≥' => Some('≤'),
        _ => None,
    }
}

fn strictness(c: char) -> Option<char> {
    match c {
        '<' => Some('≤'),
        '≤' => Some('<'),
        '>' => Some('≥'),
        '≥' => Some('>'),
        _ => None,
    }
}

/// Each number system of `text` the next smaller one, one at a time: ℂ as
/// ℝ, ℝ as ℚ, ℚ as ℤ, ℤ as ℕ, ℕ₀ as ℕ.
fn narrowed(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    for (at, c) in text.char_indices() {
        let after = &text[at + c.len_utf8()..];
        let (to, rest) = match c {
            'ℂ' => ("ℝ", after),
            'ℝ' => ("ℚ", after),
            'ℚ' => ("ℤ", after),
            'ℤ' => ("ℕ", after),
            'ℕ' => match after.strip_prefix('₀') {
                Some(rest) => ("ℕ", rest),
                None => continue,
            },
            _ => continue,
        };
        out.push(format!("{}{to}{rest}", &text[..at]));
    }
    out
}

/// A `from` list on a line: where its names start, and the names.
fn from_list(line: &str) -> Option<(usize, Vec<&str>)> {
    let at = line.rfind("from ")? + "from ".len();
    let names: Vec<&str> = line[at..].trim_end().split(", ").collect();
    let all = names.iter().all(|r| {
        !r.is_empty()
            && r.chars()
                .all(|c| c.is_alphanumeric() || c == '.' || c == '′')
    });
    all.then_some((at, names))
}

/// The line with the `from` list's names `kept`, and the `from` itself
/// gone with the comma or space before it where none is kept. None where
/// the line would be left with nothing after its colon.
fn with_from(line: &str, at: usize, kept: &[&str]) -> Option<String> {
    if !kept.is_empty() {
        return Some(format!("{}{}", &line[..at], kept.join(", ")));
    }
    let head = line[..at - "from ".len()].trim_end();
    let head = head.strip_suffix(',').unwrap_or(head);
    (!head.trim().is_empty() && !head.ends_with(':')).then(|| head.to_string())
}

/// The pairs of a citation on a line, each as where its value starts and
/// ends: the commas between pairs, and not those inside brackets.
fn pair_values(line: &str) -> Vec<(usize, usize)> {
    let Some(item) = line
        .find("mun:")
        .or_else(|| line.find("thm:"))
        .or_else(|| line.find("def:"))
        .or_else(|| line.find("axi:"))
    else {
        return Vec::new();
    };
    let end = line[item..].find(" from ").map_or(line.len(), |e| item + e);
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut part = item;
    let cut = |from: usize, to: usize, out: &mut Vec<(usize, usize)>| {
        if let Some(eq) = line[from..to].find(" := ") {
            let start = from + eq + " := ".len();
            let stop = from + line[from..to].trim_end().len();
            out.push((start, stop));
        }
    };
    for (i, c) in line[item..end].char_indices() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                cut(part, item + i, &mut out);
                part = item + i + 1;
            }
            _ => {}
        }
    }
    cut(part, end, &mut out);
    out
}

/// The lines of a file a theorem's text runs over, by index: from its
/// `theorem` line to the next theorem's, or the end.
fn region(thm: &Theorem, every: &[&Theorem], lines: usize) -> std::ops::Range<usize> {
    let next = every
        .iter()
        .filter(|t| t.path == thm.path && t.line > thm.line)
        .map(|t| t.line - 1)
        .min()
        .unwrap_or(lines);
    thm.line - 1..next
}

/// What justifies the step the file line `at` (an index) sits in.
fn under(thm: &Theorem, at: usize) -> String {
    thm.steps
        .iter()
        .filter(|s| s.line - 1 <= at)
        .max_by_key(|s| s.line)
        .map_or("statement".to_string(), |s| {
            if s.just.chain.iter().any(|(_, l)| l - 1 == at) {
                format!("{} (a row)", s.just.head)
            } else {
                s.just.head.to_string()
            }
        })
}

/// Every mutant of every theorem under `proofs/`.
fn mutants(tree: &dyn Source) -> Vec<Mutant> {
    let found = corpus(tree).expect("the corpus reads");
    let theorems: Vec<&Theorem> = found
        .theorems
        .iter()
        .filter(|t| t.path.starts_with("proofs/"))
        .collect();
    let mut out = Vec::new();
    for thm in &theorems {
        let text = tree.read_text(&thm.path).expect("a proof file reads");
        let lines: Vec<&str> = text.split('\n').collect();
        let mut add = |edit: Edit, at: usize, now: String, edited: Vec<String>| {
            out.push(Mutant {
                edit,
                path: thm.path.clone(),
                theorem: thm.name.clone(),
                qualified: thm.qualified(),
                line: at + 1,
                was: lines[at].trim().to_string(),
                now: now.trim().to_string(),
                under: under(thm, at),
                text: edited.join("\n"),
            });
        };
        let one_line = |at: usize, now: &str| -> Vec<String> {
            let mut edited: Vec<String> = lines.iter().map(|l| l.to_string()).collect();
            edited[at] = now.to_string();
            edited
        };
        for f in formulas(thm, &lines) {
            let line = lines[f.at];
            let Some(start) = line.find(&f.text) else {
                continue;
            };
            let (head, tail) = (&line[..start], &line[start + f.text.len()..]);
            for (edit, made) in [
                (Edit::Numeral, numerals(&f.text)),
                (Edit::Reversed, orders(&f.text, reversed)),
                (Edit::Strictness, orders(&f.text, strictness)),
                (Edit::Narrowed, narrowed(&f.text)),
            ] {
                for m in made {
                    let now = format!("{head}{m}{tail}");
                    add(edit, f.at, now.clone(), one_line(f.at, &now));
                }
            }
        }
        let span = region(thm, &theorems, lines.len());
        let steps: Vec<String> =
            thm.steps.iter().map(|s| s.number.to_string()).collect();
        let labels: Vec<String> = thm
            .hypotheses
            .iter()
            .filter_map(|h| h.label.clone())
            .collect();
        let mut items: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for l in &lines {
            for word in l.split([' ', ',']) {
                if let Some((prefix, name)) = word.split_once(':') {
                    if ["mun", "thm", "def", "axi"].contains(&prefix)
                        && !name.is_empty()
                    {
                        items.entry(prefix).or_default().insert(word);
                    }
                }
            }
        }
        for at in span.clone() {
            let line = lines[at];
            if let Some((start, names)) = from_list(line) {
                for i in 0..names.len() {
                    let kept: Vec<&str> = names
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, n)| *n)
                        .collect();
                    if let Some(now) = with_from(line, start, &kept) {
                        add(Edit::Dropped, at, now.clone(), one_line(at, &now));
                    }
                    let other =
                        if let Some(k) = steps.iter().position(|s| s == names[i]) {
                            k.checked_sub(1).map(|k| steps[k].clone())
                        } else {
                            labels.iter().find(|l| l.as_str() != names[i]).cloned()
                        };
                    if let Some(other) = other {
                        let mut swapped: Vec<&str> = names.clone();
                        swapped[i] = &other;
                        let now = format!("{}{}", &line[..start], swapped.join(", "));
                        add(Edit::OtherLine, at, now.clone(), one_line(at, &now));
                    }
                }
            }
            for word in line.split([' ', ',']) {
                let Some((prefix, _)) = word.split_once(':') else {
                    continue;
                };
                let Some(same) = items.get(prefix) else {
                    continue;
                };
                let next = same
                    .range::<&str, _>((
                        std::ops::Bound::Excluded(word),
                        std::ops::Bound::Unbounded,
                    ))
                    .next()
                    .or_else(|| same.iter().next())
                    .filter(|n| **n != word);
                if let Some(next) = next {
                    let now = line.replacen(word, next, 1);
                    add(Edit::OtherItem, at, now.clone(), one_line(at, &now));
                }
            }
            let values = pair_values(line);
            for w in values.windows(2) {
                let (a, b) = (&line[w[0].0..w[0].1], &line[w[1].0..w[1].1]);
                if a == b {
                    continue;
                }
                let now = format!(
                    "{}{b}{}{a}{}",
                    &line[..w[0].0],
                    &line[w[0].1..w[1].0],
                    &line[w[1].1..]
                );
                add(Edit::Swapped, at, now.clone(), one_line(at, &now));
            }
        }
        for h in &thm.hypotheses {
            let Some(label) = &h.label else { continue };
            let mut edited: Vec<String> = lines.iter().map(|l| l.to_string()).collect();
            for at in span.clone() {
                let Some((start, names)) = from_list(lines[at]) else {
                    continue;
                };
                let kept: Vec<&str> =
                    names.iter().copied().filter(|n| n != label).collect();
                if kept.len() < names.len() {
                    if let Some(now) = with_from(lines[at], start, &kept) {
                        edited[at] = now;
                    }
                }
            }
            edited.remove(h.line - 1);
            add(Edit::Hypothesis, h.line - 1, String::new(), edited);
        }
    }
    out
}

/// The mutants in an order shuffled by `seed`.
fn shuffled(mut all: Vec<Mutant>, seed: u64) -> Vec<Mutant> {
    let mut random = Random::new(seed);
    for i in (1..all.len()).rev() {
        let j = random.below(i as u64 + 1) as usize;
        all.swap(i, j);
    }
    all
}

#[test]
#[ignore = "elaborates every mutant the checker accepts; run on its own"]
fn a_wrong_proof_is_refused_and_never_verified() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let clean = Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap();
    let seed = std::env::var("MUTATION_SEED")
        .ok()
        .map(|s| s.parse::<u64>().expect("MUTATION_SEED is a number"))
        .unwrap_or(SEED);
    let all = shuffled(mutants(&clean), seed);
    let total = all.len();
    let wanted = std::env::var("MUTANTS")
        .ok()
        .map(|s| s.parse::<usize>().expect("MUTANTS is a number"))
        .unwrap_or(total);
    // `MUTATION_AT` keeps the mutants at the lines it lists, `path:line`
    // with commas between, to ask again of what a run reported; each is
    // then checked on its own, so that one running away is named alone.
    let at: Option<Vec<String>> = std::env::var("MUTATION_AT")
        .ok()
        .map(|s| s.split(',').map(|p| p.trim().to_string()).collect());
    let taken: Vec<Mutant> = all
        .into_iter()
        .filter(|m| {
            at.as_ref()
                .is_none_or(|at| at.contains(&format!("{}:{}", m.path, m.line)))
        })
        .take(wanted)
        .collect();
    let share = if at.is_some() { 1 } else { SHARE };
    println!("{} of {total} mutants, seed {seed}", taken.len());

    // Checked a share at a time on every core, each share reading the corpus
    // once. A share still running after `SLOW` is named, since the test
    // cannot stop it: a checker that runs away on a page is a fault too.
    let shares: Vec<std::ops::Range<usize>> = (0..taken.len())
        .step_by(share)
        .map(|s| s..(s + share).min(taken.len()))
        .collect();
    let running: std::sync::Mutex<BTreeMap<usize, std::time::Instant>> =
        std::sync::Mutex::new(BTreeMap::new());
    let done = std::sync::atomic::AtomicBool::new(false);
    let checked: Vec<Vec<String>> = std::thread::scope(|scope| {
        scope.spawn(|| {
            let mut named: BTreeSet<usize> = BTreeSet::new();
            while !done.load(std::sync::atomic::Ordering::Relaxed) {
                std::thread::sleep(std::time::Duration::from_secs(5));
                let now = running.lock().unwrap().clone();
                for (share, began) in now {
                    if began.elapsed() > SLOW && named.insert(share) {
                        eprintln!("checking one of these has run past {SLOW:?}:");
                        for m in &taken[shares[share].clone()] {
                            eprintln!(
                                "  {}:{} ({})  {}",
                                m.path,
                                m.line,
                                m.edit.name(),
                                m.now
                            );
                        }
                    }
                }
            }
        });
        let out = in_order(
            &(0..shares.len()).collect::<Vec<usize>>(),
            || (),
            |_, &share| {
                running
                    .lock()
                    .unwrap()
                    .insert(share, std::time::Instant::now());
                let cuts: Vec<Cut> = taken[shares[share].clone()]
                    .iter()
                    .map(|m| Cut {
                        path: m.path.clone(),
                        text: m.text.clone(),
                        theorem: m.theorem.clone(),
                    })
                    .collect();
                let said = check_cuts(&clean, &cuts).expect("the corpus checks");
                running.lock().unwrap().remove(&share);
                said
            },
        );
        done.store(true, std::sync::atomic::Ordering::Relaxed);
        out.into_iter().flatten().collect()
    });
    let largest = largest_search();
    println!("the largest citation search asked {largest} hypotheses");
    assert!(
        largest <= SEARCHED,
        "a citation search asked {largest} hypotheses, more than {SEARCHED}"
    );

    let read = library(root, None)
        .expect(
            "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
        )
        .shared();
    let accepted: Vec<usize> = (0..taken.len())
        .filter(|&i| checked[i].is_empty())
        .collect();
    let built = in_order(
        &accepted,
        || Library::new(Arc::clone(&read)),
        |lib: &mut Library, &i| {
            let m = &taken[i];
            let mut tree = Overlay::new(&clean);
            tree.write(&m.path, m.text.clone().into_bytes());
            let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                Loaded::new(&tree)
                    .and_then(|loaded| {
                        loaded.elaborate(&m.qualified, lib, Options::default())
                    })
                    .map(|e| e.text)
                    .map_err(|p| p.to_string())
            }));
            run.unwrap_or_else(|panic| {
                // What the library held when it stopped is not to be trusted.
                *lib = Library::new(Arc::clone(&read));
                let said = panic
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_default();
                Err(format!("{PANICKED}{said}"))
            })
        },
    );

    let mut fates: Vec<Fate> = checked.iter().map(|_| Fate::Checker).collect();
    let mut to_verify: Vec<(usize, String)> = Vec::new();
    for (&i, result) in accepted.iter().zip(built) {
        let m = &taken[i];
        fates[i] = match result {
            Err(said) => match said.strip_prefix(PANICKED) {
                Some(said) => Fate::Panicked(said.to_string()),
                None => Fate::Elaborator(said),
            },
            Ok(text) => {
                let path = path_of(&m.qualified);
                let assumed: Vec<&str> = text
                    .lines()
                    .filter(|l| l.split_whitespace().nth(1) == Some("$a"))
                    .collect();
                if clean.read_text(&path).ok().as_deref() == Some(text.as_str()) {
                    Fate::Unchanged
                } else if !assumed.is_empty() {
                    Fate::Assumed(assumed.join(" | "))
                } else {
                    to_verify.push((i, text));
                    Fate::Survived
                }
            }
        };
    }

    let libraries = Libraries::read_verifying_often(
        &where_set_mm(None, root)
            .expect("set.mm is found: say where it is with SET_MM"),
    )
    .expect("set.mm reads");
    let verdicts = in_order_on(
        VERIFYING,
        &to_verify,
        || (),
        |_, (i, text)| {
            let m = &taken[*i];
            let path = path_of(&m.qualified);
            let mut tree = Overlay::new(&clean);
            tree.write(&path, text.clone().into_bytes());
            let files = included(&tree, &path, text);
            verify::run(&tree, &files, Some(&libraries))
        },
    );
    for ((i, _), said) in to_verify.iter().zip(verdicts) {
        if !said.green() {
            fates[*i] = Fate::Kernel(said.printed.trim().replace('\n', " | "));
        }
    }

    let mut table: BTreeMap<Edit, [usize; 4]> = BTreeMap::new();
    for (m, fate) in taken.iter().zip(&fates) {
        table.entry(m.edit).or_default()[fate.column()] += 1;
    }
    println!(
        "\n{:<36} {:>8} {:>10} {:>9} {:>7}",
        "edit", "checker", "elaborator", "verified", "faults"
    );
    for (edit, [c, e, v, f]) in &table {
        println!("{:<36} {c:>8} {e:>10} {v:>9} {f:>7}", edit.name());
    }
    let say = |m: &Mutant, what: &str| {
        format!(
            "{}:{} ({}, {}) {}\n    was: {}\n    now: {}",
            m.path,
            m.line,
            m.edit.name(),
            m.under,
            what,
            m.was,
            m.now
        )
    };
    println!("\nverified, the page proving what it now says:");
    for (m, fate) in taken.iter().zip(&fates) {
        match fate {
            Fate::Survived => println!("{}", say(m, "")),
            Fate::Unchanged if !m.edit.says() => {
                println!("{}", say(m, "(built as committed)"))
            }
            _ => {}
        }
    }
    println!(
        "\nbuilt as committed though a formula changed, right only where the line says what another does, or the same fact:"
    );
    for (m, fate) in taken.iter().zip(&fates) {
        if matches!(fate, Fate::Unchanged) && m.edit.says() {
            println!("{}", say(m, ""));
        }
    }
    println!("\naccepted by the checker and refused by the elaborator:");
    for (m, fate) in taken.iter().zip(&fates) {
        if let Fate::Elaborator(why) = fate {
            println!("{}\n    {}", say(m, ""), why.replace('\n', " "));
        }
    }
    let faults: Vec<String> = taken
        .iter()
        .zip(&fates)
        .filter_map(|(m, fate)| fate.fault().map(|f| say(m, &f)))
        .collect();
    assert!(
        faults.is_empty(),
        "mutants the checker and the elaborator accepted, and the kernel does not prove what they say:\n{}",
        faults.join("\n")
    );
}
