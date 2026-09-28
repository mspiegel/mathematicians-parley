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
//! Which files there are comes from the build, which is what finds every
//! generated file. Reading the directory instead would be simpler and wrong:
//! the hand-written comparisons sit in it beside them and are not among
//! them. Each file is handed to the verifier under the name the others
//! include it by, its path under `corpus/elaboration/`, and set.mm under its own,
//! so an inclusion never reaches past what is handed over.
//!
//! Which of them to include is read off the inclusions rather than listed: a
//! proof that nothing else includes is a root, and one file including every
//! root reaches everything and reads set.mm once. A new proof is covered the
//! day it is written, where a list of roots would leave the gate green and
//! the new proof unread.

use std::collections::BTreeSet;
use std::path::Path;
use std::sync::LazyLock;
use std::time::Instant;

use annotate_snippets::display_list::DisplayList;
use metamath_rs::database::DbOptions;
use metamath_rs::Database;
use regex::Regex;

use crate::said::Said;

static INCLUDE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"\$\[\s*(\S+)\s*\$\]").expect("a valid pattern"));
/// A labelled `$p`, which is what there is one of per theorem proved.
static PROVES: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"(?m)^\s*(\S+)\s+\$p\s").expect("a valid pattern"));

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

/// Verify the files at `built`, paths from `root`, against the library at
/// `setmm`.
pub fn run(root: &Path, built: &[String], setmm: Option<&Path>) -> Said {
    let mut said = Said::default();
    let Some(library) = setmm else {
        said.printed =
            "set.mm not found; say where it is with SET_MM, or leave a copy or \
                        a link at the root of the working tree\n"
                .into();
        said.status = 2;
        return said;
    };
    let missing: Vec<&String> =
        built.iter().filter(|p| !root.join(p).exists()).collect();
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
        match std::fs::read_to_string(root.join(path)) {
            Ok(text) => texts.push((path.clone(), text)),
            Err(e) => {
                said.printed += &format!("{path}: {e}\n");
                said.status = 2;
                return said;
            }
        }
    }
    let setmm = match std::fs::read(library) {
        Ok(bytes) => bytes,
        Err(e) => {
            said.printed += &format!("{}: {e}\n", library.display());
            said.status = 2;
            return said;
        }
    };

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
fn verified(files: Vec<(String, Vec<u8>)>) -> Vec<String> {
    let mut db = Database::new(DbOptions::default());
    db.parse(JOINED.to_string(), files);
    db.verify_pass();
    let diags = db.diag_notations();
    db.render_diags(diags, |mut snippet| {
        // The library asks for colour; the gate's report is read as text.
        snippet.opt.color = false;
        DisplayList::from(snippet).to_string()
    })
}
