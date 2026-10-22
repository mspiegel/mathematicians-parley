//! A proof means what it says in any mix of spellings.
//!
//! The sweep in `invariance.rs` makes one change at a time, at every line
//! it fits. A break lives as often where two lines that say related things
//! are spelt differently, one turned and the other not, and where two
//! changes meet on one line. Here a seed draws files, and for each a
//! sequence of changes at single places: at most one change that rewrites
//! the file as a whole, first, and then up to `MOST_STEPS` changes each at
//! one line, mixed freely. The file must still check, build and verify, as
//! in the sweep. A sequence that breaks is cut down to the fewest changes
//! that still break it, and printed with the seed that draws it again, as
//! the transformation fuzzers of compilers report theirs (spirv-fuzz,
//! wasm-mutate).
//!
//! `INVARIANCE_SEED` sets the seed, `INVARIANCE_FILES` how many files are
//! drawn. A change that rewrites the corpus as a whole, a cited theorem
//! renamed with every citation of it, is the sweep's alone.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::Arc;

use parley::corpus::corpus;
use parley::corpus::module_of;
use parley::corpus::proof::cited_items;
use parley::elab::elaborate::Options;
use parley::elab::Library;
use parley::mm::where_set_mm;
use parley::source::{Disk, Memory, Overlay, Source};
use parley::threads::in_order;
use parley::tools::build::{checked_in, library, Libraries, Loaded};
use parley::tools::{path_of, verify};

use super::rewrites::Context;
use super::shared::{included, Random};
use super::{changes, proof_paths, Change, Rewrite, KNOWN};

/// The seed where `INVARIANCE_SEED` is not set.
const SEED: u64 = 20_261_022;
/// How many files are drawn where `INVARIANCE_FILES` is not set.
const FILES: usize = 80;
/// The most changes at single lines in one sequence.
const MOST_STEPS: u64 = 5;
/// One sequence in this many starts with a change to the whole file, where
/// one fits.
const WHOLE_ONE_IN: u64 = 4;

/// Where one change is made.
#[derive(Clone)]
enum Place {
    /// The whole file, as the change wrote it from the file as committed.
    Whole(String),
    /// One line, by the change's line rewrite, of the line as it stands
    /// when the change is made.
    Line(usize),
    /// One line, as the change turns it in the file as committed: made
    /// where the line still reads `from`.
    Turned {
        line: usize,
        from: String,
        to: String,
    },
}

/// One change at one place.
#[derive(Clone)]
struct Step {
    change: usize,
    place: Place,
}

/// A file and the sequence of changes drawn for it.
struct Sample {
    path: String,
    clean: String,
    steps: Vec<Step>,
}

/// What a sample found: nothing, or the fewest of its changes that still
/// break the file and what they break.
struct Broken {
    path: String,
    steps: Vec<Step>,
    text: String,
    breaks: Vec<String>,
}

/// The file `clean` with `steps` made in order, its citation lists written
/// as the language orders them, as the sweep writes them.
fn applied(all: &[Change], clean: &str, steps: &[Step]) -> String {
    let mut text = clean.to_string();
    for step in steps {
        text = made(&all[step.change], &text, &step.place);
    }
    text.split('\n')
        .map(super::cited_in_written_order)
        .collect::<Vec<_>>()
        .join("\n")
}

/// `text` with one change made at one place; as it was where the change
/// no longer fits there.
fn made(change: &Change, text: &str, place: &Place) -> String {
    let mut lines: Vec<String> = text.split('\n').map(str::to_string).collect();
    match (place, &change.rewrite) {
        (Place::Whole(whole), _) => return whole.clone(),
        (Place::Line(at), Rewrite::Line(rewrite)) => {
            if let Some(new) = lines.get(*at).and_then(|l| rewrite(l)) {
                lines[*at] = new;
            }
        }
        (Place::Turned { line, from, to }, _) if lines.get(*line) == Some(from) => {
            lines[*line] = to.clone();
        }
        _ => {}
    }
    lines.join("\n")
}

/// Each place a change at one line fits in `text`: each line a line
/// rewrite changes, and, where `committed` (no whole change made first),
/// each line a `Lines` change turns.
fn line_places(
    all: &[Change],
    context: &Context,
    path: &str,
    text: &str,
    committed: bool,
) -> Vec<Step> {
    let mut out = Vec::new();
    for (c, change) in all.iter().enumerate() {
        match change.rewrite {
            Rewrite::Line(rewrite) => {
                for (i, l) in text.split('\n').enumerate() {
                    if rewrite(l).is_some() {
                        out.push(Step {
                            change: c,
                            place: Place::Line(i),
                        });
                    }
                }
            }
            Rewrite::Lines(rewrite) if committed => {
                let done = rewrite(context, path, text);
                let (old, new): (Vec<&str>, Vec<&str>) =
                    (text.split('\n').collect(), done.text.split('\n').collect());
                if old.len() != new.len() {
                    continue;
                }
                for (i, (from, to)) in old.iter().zip(&new).enumerate() {
                    if from != to {
                        out.push(Step {
                            change: c,
                            place: Place::Turned {
                                line: i,
                                from: from.to_string(),
                                to: to.to_string(),
                            },
                        });
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// Each change that rewrites the file as a whole and changes it.
fn whole_places(
    all: &[Change],
    context: &Context,
    path: &str,
    clean: &str,
) -> Vec<Step> {
    let mut out = Vec::new();
    for (c, change) in all.iter().enumerate() {
        if let Rewrite::File(rewrite) = change.rewrite {
            let done = rewrite(context, path, clean);
            if done.lines > 0 && done.text != clean {
                out.push(Step {
                    change: c,
                    place: Place::Whole(done.text),
                });
            }
        }
    }
    out
}

/// A sequence drawn for one file: perhaps a whole change first, then up to
/// `MOST_STEPS` changes at single lines.
fn drawn(
    all: &[Change],
    context: &Context,
    path: &str,
    clean: &str,
    random: &mut Random,
) -> Vec<Step> {
    let mut steps = Vec::new();
    let mut start = clean.to_string();
    let wholes = whole_places(all, context, path, clean);
    if !wholes.is_empty() && random.below(WHOLE_ONE_IN) == 0 {
        let pick = wholes[random.below(wholes.len() as u64) as usize].clone();
        start = made(&all[pick.change], &start, &pick.place);
        steps.push(pick);
    }
    let mut places = line_places(all, context, path, &start, steps.is_empty());
    for _ in 0..1 + random.below(MOST_STEPS) {
        if places.is_empty() {
            break;
        }
        let at = random.below(places.len() as u64) as usize;
        steps.push(places.swap_remove(at));
    }
    steps
}

/// What the file `text` at `path` breaks, in the tree `clean` with it in
/// place: a problem the checker finds in its theorems, a theorem the build
/// does not build, or a file built that does not verify.
fn breaks(
    clean: &Memory,
    lib: &Library,
    libraries: &Libraries,
    path: &str,
    text: &str,
) -> Vec<String> {
    let mut tree = Overlay::new(clean);
    tree.write(path, text.as_bytes().to_vec());
    let prefix = format!("{}/", module_of(path));
    let in_file = |name: &str| name.starts_with(&prefix);
    let checked = match checked_in(&tree, in_file) {
        Ok(checked) => checked,
        Err(p) => return vec![format!("check | {p}")],
    };
    let mut out: Vec<String> = checked
        .theorems
        .values()
        .flat_map(|record| record.problems.iter().map(|p| format!("check | {p}")))
        .collect();
    if !out.is_empty() {
        return out;
    }
    let names: Vec<String> = checked.theorems.keys().cloned().collect();
    let cites: BTreeMap<String, Vec<String>> = checked
        .corpus
        .theorems
        .iter()
        .filter(|t| in_file(&t.qualified()))
        .map(|t| {
            let own = t.qualified();
            let cited = cited_items(t)
                .into_iter()
                .map(|(c, _)| c)
                .filter(|c| in_file(c) && *c != own)
                .collect();
            (own, cited)
        })
        .collect();
    let built = built_in_order(&tree, checked, &names, &cites, lib, &mut out);
    let mut verifying = Overlay::new(&tree);
    for (file, text) in &built {
        verifying.write(file, text.clone().into_bytes());
    }
    for (file, text) in &built {
        let files = included(&verifying, file, text);
        let said = verify::run(&verifying, &files, Some(libraries));
        if !said.green() {
            out.push(format!(
                "verify | {}",
                said.printed.trim().replace('\n', " | ")
            ));
        }
    }
    out
}

/// Each theorem of `names` built, a theorem the file's others cite first,
/// as the build builds what a theorem cites before it: a lemma a change
/// lifted out of a block has no file until then. What a build refuses goes
/// into `out`; what it builds otherwise than committed is given back.
fn built_in_order(
    tree: &Overlay,
    checked: parley::checker::CheckedCorpus,
    names: &[String],
    cites: &BTreeMap<String, Vec<String>>,
    lib: &Library,
    out: &mut Vec<String>,
) -> BTreeMap<String, String> {
    let mut built: BTreeMap<String, String> = BTreeMap::new();
    let mut done: BTreeSet<String> = BTreeSet::new();
    let mut first = Some(checked);
    while done.len() < names.len() {
        let mut ready: Vec<&String> = names
            .iter()
            .filter(|n| !done.contains(*n))
            .filter(|n| {
                cites
                    .get(*n)
                    .is_none_or(|c| c.iter().all(|c| done.contains(c)))
            })
            .collect();
        // Theorems citing each other round about are built as they stand.
        if ready.is_empty() {
            ready = names.iter().filter(|n| !done.contains(*n)).collect();
        }
        let mut round = Overlay::new(tree);
        for (file, text) in &built {
            round.write(file, text.clone().into_bytes());
        }
        let wanted: BTreeSet<&str> = ready.iter().map(|n| n.as_str()).collect();
        let checked = match first.take() {
            Some(checked) => checked,
            None => match checked_in(&round, |n| wanted.contains(n)) {
                Ok(checked) => checked,
                Err(p) => {
                    out.push(format!("check | {p}"));
                    return built;
                }
            },
        };
        let loaded = Loaded::with_checked(&round, checked);
        for name in ready {
            done.insert(name.clone());
            match loaded.elaborate(name, lib, Options::default()) {
                Ok(e) => {
                    let file = path_of(name);
                    if tree.read_text(&file).ok().as_deref() != Some(e.text.as_str()) {
                        built.insert(file, e.text);
                    }
                }
                Err(p) => out.push(format!("elaborate | {p}")),
            }
        }
    }
    built
}

/// A sample's sequence, cut to the fewest of its changes that still break
/// the file, by taking each away in turn and keeping the cut where the file
/// still breaks, until no one change can go; None where it breaks nothing.
fn reduced(
    all: &[Change],
    clean: &Memory,
    lib: &Library,
    libraries: &Libraries,
    sample: &Sample,
) -> Option<Broken> {
    let tools = Tools {
        all,
        clean,
        lib,
        libraries,
    };
    let mut kept = sample.steps.clone();
    let mut found = broken_by(&tools, sample, &kept);
    if found.is_empty() {
        return None;
    }
    let mut cut = true;
    while cut {
        cut = false;
        for i in (0..kept.len()).rev() {
            if kept.len() == 1 {
                break;
            }
            let mut fewer = kept.clone();
            fewer.remove(i);
            let still = broken_by(&tools, sample, &fewer);
            if !still.is_empty() {
                kept = fewer;
                found = still;
                cut = true;
            }
        }
    }
    let text = applied(all, &sample.clean, &kept);
    Some(Broken {
        path: sample.path.clone(),
        steps: kept,
        text,
        breaks: found,
    })
}

/// What a sample is asked with: the changes, the committed tree, a library
/// on set.mm read once, and the libraries a verifier reads.
struct Tools<'a> {
    all: &'a [Change],
    clean: &'a Memory,
    lib: &'a Library,
    libraries: &'a Libraries,
}

/// What `sample`'s file breaks with `steps` made.
fn broken_by(tools: &Tools, sample: &Sample, steps: &[Step]) -> Vec<String> {
    let text = applied(tools.all, &sample.clean, steps);
    breaks(tools.clean, tools.lib, tools.libraries, &sample.path, &text)
}

/// A break as `KNOWN` lists one, where its changes are all one change.
fn as_known(all: &[Change], broken: &Broken) -> Option<Vec<String>> {
    let first = broken.steps.first()?.change;
    if broken.steps.iter().any(|s| s.change != first) {
        return None;
    }
    let name = all[first].name;
    Some(
        broken
            .breaks
            .iter()
            .map(|b| format!("{name} | {b}"))
            .collect(),
    )
}

/// A break as the test prints it: the seed, the file, each change and the
/// lines it left changed, and what broke.
fn told(all: &[Change], seed: u64, clean: &str, broken: &Broken) -> String {
    let changes: Vec<&str> = broken.steps.iter().map(|s| all[s.change].name).collect();
    let mut out = format!(
        "{} (INVARIANCE_SEED={seed}): {}\n",
        broken.path,
        changes.join(", then ")
    );
    let (old, new): (Vec<&str>, Vec<&str>) = (
        clean.split('\n').collect(),
        broken.text.split('\n').collect(),
    );
    if old.len() == new.len() {
        for (i, (was, now)) in old.iter().zip(&new).enumerate() {
            if was != now {
                out.push_str(&format!(
                    "    line {}: {was}\n    now:     {now}\n",
                    i + 1
                ));
            }
        }
    } else {
        out.push_str("    (the file rewritten as a whole)\n");
    }
    for b in &broken.breaks {
        out.push_str(&format!("    {b}\n"));
    }
    out
}

fn number_from(name: &str, otherwise: u64) -> u64 {
    std::env::var(name)
        .ok()
        .map(|s| {
            s.parse::<u64>()
                .unwrap_or_else(|_| panic!("{name} is {s:?}, not a number"))
        })
        .unwrap_or(otherwise)
}

#[test]
fn a_proof_means_what_it_says_in_any_mix_of_spellings() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let clean = Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap();
    let seed = number_from("INVARIANCE_SEED", SEED);
    let wanted = number_from("INVARIANCE_FILES", FILES as u64) as usize;
    let all = changes();
    let context = Context::new(
        corpus(&clean).expect("the corpus reads"),
        parley::checker::obtained_there(&clean).expect("the corpus reads"),
        parley::checker::bound_there(&clean).expect("the corpus reads"),
    );
    // The files in an order shuffled by the seed, and a sequence drawn for
    // each until enough files have one: a file no change fits is passed by.
    let mut paths = proof_paths(&clean);
    let mut random = Random::new(seed);
    for i in (1..paths.len()).rev() {
        let j = random.below(i as u64 + 1) as usize;
        paths.swap(i, j);
    }
    let mut samples: Vec<Sample> = Vec::new();
    for path in paths {
        if samples.len() == wanted {
            break;
        }
        let text = clean.read_text(&path).expect("a proof file reads");
        let steps = drawn(&all, &context, &path, &text, &mut random);
        if !steps.is_empty() {
            samples.push(Sample {
                path,
                clean: text,
                steps,
            });
        }
    }
    let read = library(root, None)
        .expect(
            "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
        )
        .shared();
    let libraries = Libraries::read_verifying_often(
        &where_set_mm(None, root)
            .expect("set.mm is found: say where it is with SET_MM"),
    )
    .expect("set.mm reads");
    let results: Vec<Option<Broken>> = in_order(
        &samples,
        || Library::new(Arc::clone(&read)),
        |lib, sample| reduced(&all, &clean, lib, &libraries, sample),
    );
    let steps: usize = samples.iter().map(|s| s.steps.len()).sum();
    println!("{} files, {steps} changes, seed {seed}", samples.len());
    let known: BTreeSet<&str> = KNOWN.iter().copied().collect();
    let mut told_of = Vec::new();
    for (sample, result) in samples.iter().zip(&results) {
        let Some(broken) = result else { continue };
        let listed = as_known(&all, broken)
            .is_some_and(|keys| keys.iter().all(|k| known.contains(k.as_str())));
        if !listed {
            told_of.push(told(&all, seed, &sample.clean, broken));
        }
    }
    assert!(
        told_of.is_empty(),
        "{} sequences break:\n{}",
        told_of.len(),
        told_of.join("\n")
    );
}
