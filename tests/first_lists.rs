//! Every `first |` list the Lean build writes, with why no rule decides its
//! one tactic (`docs/LEAN.md`, how a line proves a statement).
//!
//! A step the record and the writer's own facts settle is closed by one
//! tactic. Where they do not, the writer names why it keeps a list
//! (`doc::ListReason`), and the build writes each list with its reason
//! (`tools::build::lean::LISTS`). The register keeps the lists by file and
//! step, with their reasons. A list the writer gives no reason, a list not
//! kept, and a kept list that is gone or kept for another reason each fail
//! this test, so that what is kept says what is so. Set
//! `PARLEY_LISTS_WRITE=1` to write the register anew from the build's.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use parley::lean::doc::file::{step_of_comment, STATEMENT};
use parley::tools::build::lean::LISTS;

/// Where the register is kept.
const REGISTER: &str = "tests/first_lists.txt";

/// A Lean file and a step of it, by the step's number in the comment the
/// writer puts above it.
type Site = (String, String);

/// How many lists a site holds, and why, each reason once.
type Kept = (usize, String);

fn lean_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    for entry in std::fs::read_dir(dir).expect("the Lean directory reads") {
        let path = entry.expect("an entry reads").path();
        if path.is_dir() {
            lean_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "lean") {
            out.push(path);
        }
    }
}

/// How many lists the Lean files write, by site.
fn written(root: &Path) -> BTreeMap<Site, usize> {
    let mut files = Vec::new();
    lean_files(&root.join("lean/Parley"), &mut files);
    files.sort();
    let mut out: BTreeMap<Site, usize> = BTreeMap::new();
    for file in files {
        let rel = file
            .strip_prefix(root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        let text = std::fs::read_to_string(&file).expect("a Lean file reads");
        let mut step = STATEMENT.to_string();
        for line in text.lines() {
            if let Some(comment) = line.trim_start().strip_prefix("-- ") {
                if let Some((number, _)) = step_of_comment(comment) {
                    step = number;
                }
                continue;
            }
            let lists = line.matches("first |").count();
            if lists > 0 {
                *out.entry((rel.clone(), step.clone())).or_default() += lists;
            }
        }
    }
    out
}

/// The lists the build gave reasons for, by site: how many, and the
/// reasons, each once.
fn reasoned(root: &Path) -> BTreeMap<Site, Kept> {
    let text = std::fs::read_to_string(root.join(LISTS))
        .expect("the build writes its lists' reasons: run `parley build lean`");
    let mut out: BTreeMap<Site, (usize, BTreeSet<String>)> = BTreeMap::new();
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let mut parts = line.splitn(3, '\t');
        let (Some(file), Some(step), Some(why)) =
            (parts.next(), parts.next(), parts.next())
        else {
            panic!("{LISTS}: a line of other than file, step and reason: {line}");
        };
        let entry = out.entry((file.to_string(), step.to_string())).or_default();
        entry.0 += 1;
        entry.1.insert(why.to_string());
    }
    out.into_iter()
        .map(|(site, (count, whys))| {
            (
                site,
                (count, whys.into_iter().collect::<Vec<_>>().join("; ")),
            )
        })
        .collect()
}

/// The register as kept: by site, how many lists and why.
fn kept(root: &Path) -> BTreeMap<Site, Kept> {
    let text = std::fs::read_to_string(root.join(REGISTER)).unwrap_or_default();
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .filter_map(|l| {
            let mut parts = l.splitn(4, '\t');
            let count = parts.next()?.parse().ok()?;
            let file = parts.next()?.to_string();
            let step = parts.next()?.to_string();
            let why = parts.next()?.to_string();
            Some(((file, step), (count, why)))
        })
        .collect()
}

#[test]
fn every_first_list_is_kept_with_its_reason() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let now = written(root);
    let reasons = reasoned(root);

    // Every list the files write is one the writer gave a reason for.
    let mut unreasoned = Vec::new();
    for (site, count) in &now {
        let given = reasons.get(site).map_or(0, |(c, _)| *c);
        if given != *count {
            unreasoned.push(format!(
                "{} step {}: {count} lists written, {given} with a reason",
                site.0, site.1
            ));
        }
    }
    for (site, (count, _)) in &reasons {
        if !now.contains_key(site) {
            unreasoned.push(format!(
                "{} step {}: {count} reasons, and no list written",
                site.0, site.1
            ));
        }
    }
    assert!(
        unreasoned.is_empty(),
        "the lists written and the build's reasons ({LISTS}) differ:\n{}",
        unreasoned.join("\n")
    );

    if std::env::var("PARLEY_LISTS_WRITE").is_ok() {
        let mut text = String::new();
        for ((file, step), (count, why)) in &reasons {
            text.push_str(&format!("{count}\t{file}\t{step}\t{why}\n"));
        }
        std::fs::write(root.join(REGISTER), text).unwrap();
        return;
    }
    let before = kept(root);
    let mut differ = Vec::new();
    for (site, now_kept) in &reasons {
        match before.get(site) {
            Some(was) if was == now_kept => {}
            Some((count, why)) => differ.push(format!(
                "{} step {}: {} lists for {}, kept {count} for {why}",
                site.0, site.1, now_kept.0, now_kept.1
            )),
            None => differ.push(format!(
                "{} step {}: {} lists for {}, none kept",
                site.0, site.1, now_kept.0, now_kept.1
            )),
        }
    }
    for site in before.keys() {
        if !reasons.contains_key(site) {
            differ.push(format!(
                "{} step {}: kept, and no list there now",
                site.0, site.1
            ));
        }
    }
    let total: usize = now.values().sum();
    assert!(
        differ.is_empty(),
        "the first-lists differ from {REGISTER} ({total} written); keep each with its reason:\n{}",
        differ.join("\n")
    );
}
