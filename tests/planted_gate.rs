//! The gate's stages catch things.
//!
//! The checker and the elaborator have planted defects of their own. The
//! gate's other stages each exist to catch one kind of thing, and a stage
//! that had stopped catching it would still say green. So each case below
//! takes the tree, makes one edit that stage exists for, and requires that
//! the stage is red and says so. Before any edit, every stage must be green
//! over the tree as it stands, or a red one proves nothing.
//!
//! The tree is read into memory once, and each case edits it through an
//! overlay of its own. This reads set.mm, and fails if set.mm cannot be
//! found: a test that skipped would say green about a thing it had not
//! looked at.

use std::path::{Path, PathBuf};

use parley::mm::where_set_mm;
use parley::said::Said;
use parley::source::{Disk, Memory, Overlay, Source};
use parley::tools::gate::{as_built, verifies};
use parley::tools::{assumed, labels, needed, restated, tested};

/// One of the gate's stages, run over a tree with set.mm where it is.
type Stage = fn(&dyn Source, &Path) -> Said;

fn labels_stage(tree: &dyn Source, setmm: &Path) -> Said {
    labels::run(tree, Some(setmm), "src/rules.rs")
}

fn tested_stage(tree: &dyn Source, _: &Path) -> Said {
    tested::run(tree)
}

fn assumed_stage(tree: &dyn Source, _: &Path) -> Said {
    assumed::run(tree)
}

fn as_built_stage(tree: &dyn Source, setmm: &Path) -> Said {
    as_built(tree, Some(setmm))
}

fn verify_stage(tree: &dyn Source, setmm: &Path) -> Said {
    verifies(tree, Some(setmm))
}

fn restated_stage(tree: &dyn Source, setmm: &Path) -> Said {
    restated::run(tree, Some(setmm))
}

/// The proof file the requires-line case edits.
const NEEDED_FILE: &str = "proofs/sum-formula.proof";

/// Whether every requires line is needed, asked of the one file the case
/// edits: a line planted there is caught there, and the gate asks it of
/// every file.
fn needed_stage(tree: &dyn Source, setmm: &Path) -> Said {
    needed::run_over(tree, Some(setmm), &[NEEDED_FILE.to_string()])
}

const STAGES: [(&str, Stage); 7] = [
    ("set.mm labels", labels_stage),
    ("cited or tested", tested_stage),
    ("taken as stated", assumed_stage),
    ("a fresh build", as_built_stage),
    ("the proofs verify", verify_stage),
    ("items restated", restated_stage),
    ("requires lines needed", needed_stage),
];

/// One planted defect: the stage that must catch it, the file, the text
/// replaced (its first occurrence), what replaces it, and what the stage
/// must say.
struct Case {
    name: &'static str,
    stage: Stage,
    file: &'static str,
    old: &'static str,
    new: &'static str,
    expect: &'static str,
}

/// The built file the cases that change a proof change.
const CANTOR: &str = "corpus/elaboration/proofs/cantor/cantor.mm";
/// Its statement, and the statement with its negation taken away.
const CANTOR_SAYS: &str = "E. m e. ~P A A. x e. A -. ( B ` x ) = m ) $=";
const CANTOR_WRONG: &str = "E. m e. ~P A A. x e. A ( B ` x ) = m ) $=";

fn cases() -> Vec<Case> {
    vec![
        Case {
            name: "a target names a label set.mm does not have",
            stage: labels_stage,
            file: "corpus/stdlib/numbers.records",
            old: "  target      nnrecl\n",
            new: "  target      nnreclzz\n",
            expect: "names nnreclzz, which set.mm does not have",
        },
        Case {
            name: "a library item nothing cites",
            stage: tested_stage,
            file: "corpus/stdlib/sets.records",
            old: "mundane theorem union-self\n",
            new: "mundane theorem union-self-again\n  then        Y ∪ Y = Y\n  metamath    unidm\n  target      unidm\n\nmundane theorem union-self\n",
            expect: "stdlib/sets/union-self-again is cited by no proof and has no test",
        },
        Case {
            name: "a built proof takes a step as stated that is not recorded",
            stage: assumed_stage,
            file: CANTOR,
            old: "\n$}",
            new: "\n  planted $a |- ph $.\n$}",
            expect: "planted is taken as stated, and ELABORATION.md does not record it",
        },
        Case {
            name: "a step recorded as taken as stated that no file takes",
            stage: assumed_stage,
            file: "docs/ELABORATION.md",
            old: "None: every step of every proof and every library test is built.\n",
            new: "- `corpus/elaboration/proofs/cantor/cantor.mm` `ghost`: planted.\n",
            expect: "records ghost in corpus/elaboration/proofs/cantor/cantor.mm, which that file no longer takes as stated",
        },
        Case {
            name: "a built file that is not what the build makes",
            stage: as_built_stage,
            file: CANTOR,
            old: CANTOR_SAYS,
            new: CANTOR_WRONG,
            expect: "proofs/cantor/cantor.mm  differs from what the build makes",
        },
        Case {
            name: "a library proof step that does not follow",
            stage: as_built_stage,
            file: "corpus/proved/divisors.proved",
            old: "  8 1gcd |- ( C e. ZZ -> ( 1 gcd C ) = 1 )\n",
            new: "  8 1gcd |- ( C e. ZZ -> ( 1 gcd C ) = 2 )\n",
            expect: "1gcd does not prove what the step says",
        },
        Case {
            name: "a proof whose statement it does not prove",
            stage: verify_stage,
            file: CANTOR,
            old: CANTOR_SAYS,
            new: CANTOR_WRONG,
            expect: "rejected the proofs",
        },
        Case {
            name: "an item no proof restates that ELABORATION.md does not list",
            stage: restated_stage,
            file: "docs/ELABORATION.md",
            old: "`stdlib/reasoning/or-right`",
            new: "or-right",
            expect: "stdlib/reasoning/or-right states a schema no proof restates, and ELABORATION.md does not list it",
        },
        Case {
            name: "an item listed as not restated that is restated",
            stage: restated_stage,
            file: "docs/ELABORATION.md",
            old: "`stdlib/counting/count-last-fails`.",
            new: "`stdlib/counting/count-last-fails`, `stdlib/sets/union-self`.",
            expect: "ELABORATION.md lists stdlib/sets/union-self as not restated, and it is restated",
        },
        Case {
            name: "a requires line the step is checked and built without",
            stage: needed_stage,
            file: NEEDED_FILE,
            old: "          algebra\n          requires k ∈ ℝ: from K\n",
            new: "          algebra\n          requires 2 ≠ 0: arithmetic\n          requires k ∈ ℝ: from K\n",
            expect: "says 2 ≠ 0: arithmetic, and the step is checked and built without it",
        },
    ]
}

/// The tree as it stands: what the stages read.
fn clean() -> Memory {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests", "docs"]).unwrap()
}

fn set_mm() -> PathBuf {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    where_set_mm(None, root).expect(
        "set.mm not found; say where it is with SET_MM, or leave a copy or a link at the root of the working tree",
    )
}

/// What one case says, and whether it missed: its edit could not be planted,
/// or the stage stayed green, or said something other than it should.
fn outcome(case: &Case, clean: &Memory, setmm: &Path) -> (String, bool) {
    let mut tree = Overlay::new(clean);
    let text = match tree.read_text(case.file) {
        Ok(text) => text,
        Err(e) => return (format!("  SETUP FAILED  {}\n      {e}", case.name), true),
    };
    if !text.contains(case.old) {
        return (
            format!(
                "  SETUP FAILED  {}\n      anchor not found in {}",
                case.name, case.file
            ),
            true,
        );
    }
    tree.write(case.file, text.replacen(case.old, case.new, 1).into_bytes());
    let said = (case.stage)(&tree, setmm);
    let all = format!("{}{}", said.printed, said.complained);
    if !said.green() && all.contains(case.expect) {
        return (format!("  caught        {}", case.name), false);
    }
    let got: String = all
        .lines()
        .collect::<Vec<_>>()
        .join(" | ")
        .chars()
        .take(240)
        .collect();
    (
        format!(
            "  NOT CAUGHT    {}\n      expected a red stage saying {:?}\n      got (status {}): {got}",
            case.name, case.expect, said.status
        ),
        true,
    )
}

#[test]
fn the_gate_catches_every_planted_defect() {
    let clean = clean();
    let setmm = set_mm();
    let cases = cases();
    // Whether every stage over the tree as it stands is green is asked before
    // anything a case says counts.
    let unplanted: Vec<(&str, Said)> = STAGES
        .iter()
        .map(|(name, stage)| (*name, stage(&clean, &setmm)))
        .collect();
    let results: Vec<_> = cases
        .iter()
        .map(|case| outcome(case, &clean, &setmm))
        .collect();
    for (name, said) in unplanted {
        assert!(
            said.green(),
            "the stage {name} is not green over the tree as it stands, so a planted defect proves nothing:\n{}{}",
            said.printed,
            said.complained
        );
    }
    let missed = results.iter().filter(|(_, missed)| *missed).count();
    let said: Vec<&str> = results.iter().map(|(line, _)| line.as_str()).collect();
    println!("{}", said.join("\n"));
    println!(
        "\n{} caught, {missed} missed, of {} planted defects",
        cases.len() - missed,
        cases.len()
    );
    assert_eq!(missed, 0, "{}", said.join("\n"));
}
