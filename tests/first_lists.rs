//! Every `first |` list the Lean build writes, with why no rule decides its
//! one tactic (`docs/LEAN.md`, how a line proves a statement).
//!
//! A step the record and the writer's own facts settle is closed by one
//! tactic. Where they do not, the step keeps the alternatives it tries, and
//! the list is kept here, by its file and step, with the reason. A list
//! not kept fails this test until it is given one, and a kept list that is
//! gone fails it too, so that what is kept says what is so. Set
//! `PARLEY_LISTS_WRITE=1` to write the register anew: a list kept before
//! keeps its reason, and a new one is given its family's.

use std::collections::BTreeMap;
use std::path::Path;

/// Where the register is kept.
const REGISTER: &str = "tests/first_lists.txt";

/// A Lean file and a step of it, by the step's number in the comment the
/// writer puts above it.
type Site = (String, String);

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

/// The lists the build wrote, by site: how many, and the method the step's
/// comment names, which gives a new list its family's reason.
fn written(root: &Path) -> BTreeMap<Site, (usize, String)> {
    let mut files = Vec::new();
    lean_files(&root.join("lean/Parley"), &mut files);
    files.sort();
    let mut out: BTreeMap<Site, (usize, String)> = BTreeMap::new();
    for file in files {
        let rel = file
            .strip_prefix(root)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        let text = std::fs::read_to_string(&file).expect("a Lean file reads");
        let mut step = ("the statement".to_string(), String::new());
        for line in text.lines() {
            let trimmed = line.trim_start();
            if let Some(comment) = trimmed.strip_prefix("-- ") {
                if let Some((number, rest)) = comment.split_once(". ") {
                    if number.chars().all(|c| c.is_ascii_digit() || c == '.') {
                        let method = rest
                            .split([' ', ','])
                            .next()
                            .unwrap_or_default()
                            .to_string();
                        step = (number.to_string(), method);
                    }
                }
                continue;
            }
            let lists = line.matches("first |").count();
            if lists > 0 {
                let entry = out
                    .entry((rel.clone(), step.0.clone()))
                    .or_insert((0, step.1.clone()));
                entry.0 += lists;
            }
        }
    }
    out
}

/// The reason a new list of a step of `method` is kept for.
fn family_reason(method: &str) -> String {
    let family = match method.split(':').next().unwrap_or_default() {
        "def" => "a definition read where Lean states it otherwise than the claim",
        "mun" | "thm" | "ax" => {
            "an item citation whose Lean types no reasoned rule settles yet"
        }
        "calculation" => "a calculation row no reasoned rule settles yet",
        "substitute" => {
            "a substitution whose equation's type in the row no rule settles yet"
        }
        "instantiate" => "an instance no reasoned rule settles yet",
        _ => "a step no reasoned rule settles yet",
    };
    family.to_string()
}

/// The register as kept: by site, how many lists and why.
fn kept(root: &Path) -> BTreeMap<Site, (usize, String)> {
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
    let before = kept(root);
    if std::env::var("PARLEY_LISTS_WRITE").is_ok() {
        let mut text = String::new();
        for ((file, step), (count, method)) in &now {
            let why = before
                .get(&(file.clone(), step.clone()))
                .map(|(_, why)| why.clone())
                .unwrap_or_else(|| family_reason(method));
            text.push_str(&format!("{count}\t{file}\t{step}\t{why}\n"));
        }
        std::fs::write(root.join(REGISTER), text).unwrap();
        return;
    }
    let mut differ = Vec::new();
    for ((file, step), (count, _)) in &now {
        match before.get(&(file.clone(), step.clone())) {
            Some((kept, _)) if kept == count => {}
            Some((kept, _)) => {
                differ.push(format!("{file} step {step}: {count} lists, {kept} kept"))
            }
            None => {
                differ.push(format!("{file} step {step}: {count} lists, none kept"))
            }
        }
    }
    for (file, step) in before.keys() {
        if !now.contains_key(&(file.clone(), step.clone())) {
            differ.push(format!("{file} step {step}: kept, and no list there now"));
        }
    }
    let total: usize = now.values().map(|(c, _)| c).sum();
    assert!(
        differ.is_empty(),
        "the first-lists differ from {REGISTER} ({total} written); keep each with its reason:\n{}",
        differ.join("\n")
    );
}
