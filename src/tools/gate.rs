//! Everything about the corpus that must be green before a commit.
//!
//! Whether the tool itself is right is `cargo test`; this is whether the
//! corpus is. Six stages, in the order they are printed:
//!
//! 1. the checker over the whole corpus;
//! 2. every artifact built afresh in memory and compared with the file in
//!    the tree, so that a broken elaborator with the old files left in place
//!    fails here rather than passing every stage after;
//! 3. every set.mm label the database names;
//! 4. every library item cited by a proof or tested in `tests/stdlib/`;
//! 5. no step taken as stated that `ELABORATION.md` does not record;
//! 6. a verifier not written for this project (`metamath-rs`, the verifier
//!    of metamath-knife) over every proof the elaborator has written.
//!
//! The last is the only one that is evidence the elaborator is right rather
//! than consistent. The ones before it read the corpus against itself or
//! against a list of names; a proof that assumes nothing and proves the
//! wrong thing would pass all of them.
//!
//! The fourth is there because an item's statement is written by hand beside
//! the lemma it names, and only a citation that elaborates asks whether the
//! two agree. The fifth is there because a step taken as stated verifies:
//! the verifier reads it as an axiom, so the last stage cannot see one.
//!
//! Three stages need set.mm, which belongs to metamath and is not committed:
//! say where it is with `SET_MM`, or leave a copy or a link at the root of
//! the working tree. A gate that skipped them would be saying green about a
//! thing it had not looked at.

use std::path::Path;

use crate::corpus::corpus;
use crate::mm::library::where_set_mm;
use crate::said::Said;
use crate::source::Disk;

use super::build::{artifacts, verified, waves, Artifact, Maker};
use super::{assumed, labels, tested, verify};

/// Where a label missing from a rule table is said to be written.
const TABLES_AT: &str = "src/rules.rs";

/// Every artifact made afresh and compared with its file in the tree.
fn as_built(root: &Path, setmm: Option<&Path>) -> Said {
    let mut said = Said::default();
    let source = Disk::new(root.to_path_buf());
    let found = match corpus(&source) {
        Ok(found) => found,
        Err(problem) => {
            said.complained = format!("{problem}\n");
            said.status = 2;
            return said;
        }
    };
    let Some(setmm) = setmm else {
        said.printed =
            "set.mm not found; say where it is with SET_MM, or leave a copy or a \
                        link at the root of the working tree\n"
                .into();
        said.status = 2;
        return said;
    };
    let every = artifacts(&found);
    let mut maker = match Maker::new(&source, &found, setmm) {
        Ok(maker) => maker,
        Err(problem) => {
            said.complained = format!("{problem}\n");
            said.status = 2;
            return said;
        }
    };
    let all: Vec<&Artifact> = every.iter().collect();
    let mut differ = 0;
    for wave in waves(&all) {
        for artifact in wave {
            let path = artifact.path();
            match maker.make(artifact) {
                Ok(made) => match std::fs::read_to_string(root.join(&path)) {
                    Ok(there) if there == made => {}
                    Ok(_) => {
                        said.printed +=
                            &format!("{path}  differs from what the build makes\n");
                        differ += 1;
                    }
                    Err(_) => {
                        said.printed += &format!("{path}  is not in the tree\n");
                        differ += 1;
                    }
                },
                Err(problem) => {
                    said.printed += &format!("{path}  cannot be built: {problem}\n");
                    differ += 1;
                }
            }
        }
    }
    said.printed += &format!(
        "\n{} artifacts built, {differ} not as the tree has them\n",
        every.len()
    );
    if differ > 0 {
        said.printed += "\nrun parley build\n";
        said.status = 1;
    }
    said
}

fn verified_files(root: &Path) -> Result<Vec<String>, Said> {
    match corpus(&Disk::new(root.to_path_buf())) {
        Ok(found) => Ok(verified(&found)),
        Err(problem) => Err(Said {
            printed: String::new(),
            complained: format!("{problem}\n"),
            status: 2,
        }),
    }
}

/// Run every stage over the tree at `root`.
pub fn run(root: &Path) -> Said {
    let source = Disk::new(root.to_path_buf());
    let setmm = where_set_mm(None, root);
    let setmm = setmm.as_deref();

    type Stage<'s> = Box<dyn Fn() -> Said + 's>;
    let stages: Vec<(&str, Stage)> = vec![
        ("checker", Box::new(|| crate::check::run(&source))),
        (
            "every artifact is what a fresh build makes",
            Box::new(|| as_built(root, setmm)),
        ),
        (
            "set.mm labels",
            Box::new(|| labels::run(&source, setmm, TABLES_AT)),
        ),
        (
            "every library item is cited or tested",
            Box::new(|| tested::run(&source)),
        ),
        (
            "nothing is taken as stated unrecorded",
            Box::new(|| assumed::run(&source)),
        ),
        (
            "the proofs verify",
            Box::new(|| match verified_files(root) {
                Ok(built) => verify::run(root, &built, setmm),
                Err(said) => said,
            }),
        ),
    ];

    let mut out = Said::default();
    let mut failed = Vec::new();
    for (what, stage) in &stages {
        let said = stage();
        out.printed += &format!("\n=== {what}\n{}{}", said.printed, said.complained);
        if !said.green() {
            failed.push(*what);
        }
    }
    out.printed.push('\n');
    if failed.is_empty() {
        out.printed += "green\n";
    } else {
        out.printed += &format!("NOT GREEN: {}\n", failed.join(", "));
        out.status = 1;
    }
    out
}
