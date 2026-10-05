//! Everything about the corpus that must be green before a commit.
//!
//! Whether the tool itself is right is `cargo test`; this is whether the
//! corpus is. Eight stages, in the order they are printed:
//!
//! 1. the checker over the whole corpus;
//! 2. every artifact built afresh in memory and compared with the file in
//!    the tree, so that a broken elaborator with the old files left in place
//!    fails here rather than passing every stage after;
//! 3. every set.mm label the database names;
//! 4. every library item cited by a proof or tested in `tests/stdlib/`;
//! 5. no step taken as stated that `ELABORATION.md` does not record;
//! 6. a verifier not written for this project (`metamath-rs`, the verifier
//!    of metamath-knife) over every proof the elaborator has written;
//! 7. every library item with a target restated as a theorem citing it,
//!    built and verified the same way (`restated`), and each item it cannot
//!    restate listed in `ELABORATION.md`;
//! 8. every requires line needed: each taken away in turn, and its theorem
//!    checked and elaborated without it (`needed`).
//!
//! The verifier stages are the only evidence the elaborator is right rather
//! than consistent. The others read the corpus against itself or
//! against a list of names; a proof that assumes nothing and proves the
//! wrong thing would pass all of them.
//!
//! The fourth is there because an item's statement is written by hand beside
//! the lemma it names, and only a citation that elaborates asks whether the
//! two agree. The fifth is there because a step taken as stated verifies:
//! the verifier reads it as an axiom, so the last stage cannot see one. The
//! build writes none, so the stage guards the files from anything else that
//! writes them.
//!
//! Three stages need set.mm, which belongs to metamath and is not committed:
//! say where it is with `SET_MM`, or leave a copy or a link at the root of
//! the working tree. A gate that skipped them would be saying green about a
//! thing it had not looked at.

use std::path::Path;

use crate::corpus::corpus;
use crate::mm::library::where_set_mm;
use crate::said::Said;
use crate::source::{Disk, Source};

use super::build::{artifacts, verified, waves, Artifact, Maker};
use super::{assumed, labels, needed, restated, tested, verify};

/// Where a label missing from a rule table is said to be written.
const TABLES_AT: &str = "src/rules.rs";

/// Every artifact made afresh and compared with its file in the tree.
pub fn as_built(source: &dyn Source, setmm: Option<&Path>) -> Said {
    let mut said = Said::default();
    let found = match corpus(source) {
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
    let mut maker = match Maker::new(source, &found, setmm) {
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
                Ok(made) => match source.read_text(&path) {
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

/// Every artifact the tree holds, given to the verifier.
pub fn verifies(source: &dyn Source, setmm: Option<&Path>) -> Said {
    match corpus(source) {
        Ok(found) => verify::run(source, &verified(&found), setmm),
        Err(problem) => Said {
            printed: String::new(),
            complained: format!("{problem}\n"),
            status: 2,
        },
    }
}

/// Run every stage over the tree at `root`.
pub fn run(root: &Path) -> Said {
    let source = Disk::new(root.to_path_buf());
    let setmm = where_set_mm(None, root);
    let setmm = setmm.as_deref();

    type Stage<'s> = Box<dyn Fn() -> Said + Send + Sync + 's>;
    let stages: Vec<(&str, Stage)> = vec![
        ("checker", Box::new(|| crate::check::run(&source))),
        (
            "every artifact is what a fresh build makes",
            Box::new(|| as_built(&source, setmm)),
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
        ("the proofs verify", Box::new(|| verifies(&source, setmm))),
        (
            "every library item gives its target what it asks",
            Box::new(|| restated::run(&source, setmm)),
        ),
        (
            "every requires line is needed",
            Box::new(|| needed::run(&source, setmm)),
        ),
    ];

    // No stage reads what another writes, so they run side by side and are
    // printed in the order above.
    let results: Vec<Said> = std::thread::scope(|scope| {
        let running: Vec<_> =
            stages.iter().map(|(_, stage)| scope.spawn(stage)).collect();
        running
            .into_iter()
            .map(|handle| handle.join().expect("a gate stage panicked"))
            .collect()
    });
    let mut out = Said::default();
    let mut failed = Vec::new();
    for ((what, _), said) in stages.iter().zip(results) {
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
