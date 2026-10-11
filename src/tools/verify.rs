//! Every elaborated proof, checked by a verifier rather than by this project.
//!
//! The checker reads the readable layer and the elaborator writes Metamath
//! from it. Neither is evidence that what came out is a proof: an elaborator
//! that emits a wrong step emits it confidently, and the assumption count at
//! the head of each file reports a proof that assumes nothing whether or not
//! it proves what it claims. Only a verifier settles that, and it is the one
//! part of this tool that was not written for this project: `metamath-rs`,
//! the verifier of metamath-knife, which the Metamath project maintains and
//! runs over set.mm itself.
//!
//! Which files there are comes from the build, which is what knows every
//! generated file, the hand-written comparisons among them; a file left in
//! the directory that the build does not make is not one of them. Each file
//! is handed to the verifier under the name the others
//! include it by, its path under `corpus/elaboration/`, and set.mm under its own,
//! so an inclusion never reaches past what is handed over.
//!
//! Which of them to include is read off the inclusions rather than listed: a
//! proof that nothing else includes is a root, and one file including every
//! root reaches everything and reads set.mm once. A new proof is covered the
//! day it is written, where a list of roots would leave the gate green and
//! the new proof unread.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::LazyLock;
use std::time::Instant;

use annotate_snippets::Renderer;
use metamath_rs::database::DbOptions;
use metamath_rs::Database;
use regex::Regex;

use crate::said::Said;
use crate::source::Source;
use crate::tools::build::Libraries;

static INCLUDE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"\$\[\s*(\S+)\s*\$\]").expect("a valid pattern"));
/// A labelled `$p`, which is what there is one of per theorem proved.
static PROVES: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"(?m)^\s*(\S+)\s+\$p\s").expect("a valid pattern"));

/// A labelled statement, by its label.
static DECLARES: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?m)^\s*(\S+)\s+\$[apef]\s").expect("a valid pattern")
});
/// A proof, by the label it proves and what stands between `$=` and `$.`.
static PROOF: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?ms)^\s*(\S+)\s+\$p\s.*?\$=(.*?)\$\.").expect("a valid pattern")
});

/// The file the verifier starts from, which includes every root.
const JOINED: &str = "everything.mm";

/// How a file including this one names it: its path under
/// `corpus/elaboration/`.
fn included_as(path: &str) -> &str {
    path.strip_prefix(super::ELABORATION)
        .and_then(|rest| rest.strip_prefix('/'))
        .unwrap_or(path)
}

/// The files nothing else includes, which reach everything between them.
///
/// Read off the inclusions so that a proof added later is covered without
/// this being edited. set.mm is included too and is not one of these files,
/// so it falls out of the difference on its own.
fn roots(built: &[(String, String)]) -> Vec<String> {
    let here: BTreeSet<&str> = built.iter().map(|(p, _)| included_as(p)).collect();
    let mut included: BTreeSet<&str> = BTreeSet::new();
    for (_, text) in built {
        for c in INCLUDE.captures_iter(text) {
            let name = c.get(1).map_or("", |m| m.as_str());
            if here.contains(name) {
                included.insert(name);
            }
        }
    }
    here.difference(&included).map(|s| s.to_string()).collect()
}

/// The labels a text declares: each `$a`, `$p`, `$e` and `$f`.
fn declared(text: &str) -> BTreeSet<&str> {
    DECLARES
        .captures_iter(text)
        .filter_map(|c| c.get(1).map(|m| m.as_str()))
        .collect()
}

/// The labels each proof of a text uses, by the label it proves: a
/// compressed proof's list, or an uncompressed proof's steps.
fn used(text: &str) -> Vec<(&str, Vec<&str>)> {
    PROOF
        .captures_iter(text)
        .map(|c| {
            let label = c.get(1).map_or("", |m| m.as_str());
            let body = c.get(2).map_or("", |m| m.as_str()).trim_start();
            let labels = match body.strip_prefix('(') {
                Some(rest) => rest.split(')').next().unwrap_or("").split_whitespace(),
                None => body.split_whitespace(),
            };
            (label, labels.filter(|l| *l != "?").collect())
        })
        .collect()
}

/// Each proof using a label that neither set.mm nor any file its own file
/// reaches through its inclusions declares.
fn unreached(texts: &[(String, String)], setmm: &str) -> Vec<String> {
    let by_name: BTreeMap<&str, &str> = texts
        .iter()
        .map(|(p, t)| (included_as(p), t.as_str()))
        .collect();
    let base = declared(setmm);
    let mut out = Vec::new();
    for (path, text) in texts {
        let mut reached: BTreeSet<&str> = BTreeSet::new();
        let mut todo: Vec<&str> = vec![text];
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        while let Some(here) = todo.pop() {
            reached.extend(declared(here));
            for c in INCLUDE.captures_iter(here) {
                let name = c.get(1).map_or("", |m| m.as_str());
                if let Some(next) = by_name.get(name) {
                    if seen.insert(name) {
                        todo.push(next);
                    }
                }
            }
        }
        for (proves, labels) in used(text) {
            let missing: Vec<&str> = labels
                .into_iter()
                .filter(|l| !base.contains(l) && !reached.contains(l))
                .collect();
            if !missing.is_empty() {
                out.push(format!(
                    "{path}: the proof of {proves} uses {}, which nothing the file includes declares",
                    missing.join(", ")
                ));
            }
        }
    }
    out
}

/// Verify the files at `built`, paths in `source`, against set.mm as
/// `libraries` read it.
pub fn run(
    source: &dyn Source,
    built: &[String],
    libraries: Option<&Libraries>,
) -> Said {
    let mut said = Said::default();
    let Some(libraries) = libraries else {
        said.printed =
            "set.mm not found; say where it is with SET_MM, or leave a copy or \
                        a link at the root of the working tree\n"
                .into();
        said.status = 2;
        return said;
    };
    let missing: Vec<&String> = built.iter().filter(|p| !source.exists(p)).collect();
    if !missing.is_empty() {
        for path in missing {
            said.printed += &format!("not built: {path}\n");
        }
        said.printed += "\nrun parley build\n";
        said.status = 2;
        return said;
    }
    let mut texts = Vec::new();
    for path in built {
        match source.read_text(path) {
            Ok(text) => texts.push((path.clone(), text)),
            Err(e) => {
                said.printed += &format!("{path}: {e}\n");
                said.status = 2;
                return said;
            }
        }
    }
    let setmm = libraries.setmm.as_bytes().to_vec();

    // Verified together, every file sees every other's labels; each must
    // reach the ones it uses through its own inclusions, as a reader
    // verifying that one file does.
    let unreached = unreached(&texts, &libraries.setmm);
    if !unreached.is_empty() {
        for u in &unreached {
            said.printed += &format!("{u}\n");
        }
        said.printed += &format!(
            "\n{} proof(s) use a label nothing their file includes declares\n",
            unreached.len()
        );
        said.status = 1;
        return said;
    }

    let top = roots(&texts);
    let proved: usize = texts.iter().map(|(_, t)| PROVES.find_iter(t).count()).sum();
    said.printed += &format!(
        "{proved} proofs in {} files, reached from {}\n",
        built.len(),
        top.join(", ")
    );

    let joined: String = top.iter().map(|name| format!("$[ {name} $]\n")).collect();
    let mut files: Vec<(String, Vec<u8>)> = vec![
        ("set.mm".to_string(), setmm),
        (JOINED.to_string(), joined.into_bytes()),
    ];
    files.extend(
        texts
            .into_iter()
            .map(|(path, text)| (included_as(&path).to_string(), text.into_bytes())),
    );

    let began = Instant::now();
    let problems = verified(files);
    let spent = began.elapsed().as_secs_f64();
    if !problems.is_empty() {
        for p in &problems {
            said.printed += &format!("\n{p}\n");
        }
        said.printed += &format!(
            "\nmetamath-rs rejected the proofs: {} problem(s)\n",
            problems.len()
        );
        said.status = 1;
        return said;
    }
    said.printed += &format!("\nall {proved} verify, in {spent:.0}s\n");
    said
}

/// Every problem the verifier finds in the files, starting from the joined
/// one, each written out with the statement it is in.
pub fn verified(files: Vec<(String, Vec<u8>)>) -> Vec<String> {
    // metamath-rs works segment by segment, and set.mm read whole is one
    // segment on one thread: split at its chapters, it is checked on every
    // core at once.
    let options = DbOptions {
        autosplit: true,
        jobs: std::thread::available_parallelism().map_or(1, |n| n.get()),
        ..DbOptions::default()
    };
    let mut db = Database::new(options);
    db.parse(JOINED.to_string(), files);
    db.verify_pass();
    let diags = db.diag_notations();
    // Plain, without colour: the gate's report is read as text.
    db.render_diags(diags, |message| {
        Renderer::plain().render(message).to_string()
    })
}
