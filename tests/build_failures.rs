//! A build is the check with a backend after it, and both backends meet a
//! failure the same way: it is reported, what depends on it is not built
//! and is reported as such, everything else is built, and the build exits
//! with status 1. The old file of what is not built is removed, so that what
//! is on disk is what the run made. A problem outside every theorem has every
//! theorem depending on it, and the build ends with the check.
//!
//! The Metamath cases build a small tree on disk: the library and two proof
//! files, one of whose theorems cites the other. The Lean cases ask the
//! Lean build what it makes of the whole corpus held in memory, so that the
//! module table answers every file and no Lean process is started.

use std::path::{Path, PathBuf};

use parley::source::{Disk, Memory, Overlay, Source};
use parley::tools::build::artifacts;

/// The file whose two theorems the cases use: `successor-at-zero` cites
/// `successor-sum`.
const CITING: &str = "tests/elaborator/a-cited-hypothesis-an-identity.proof";
/// A file citing neither.
const APART: &str = "tests/elaborator/powers.proof";

const CITED: &str = "tests/elaborator/a-cited-hypothesis-an-identity/successor-sum";
const CITER: &str = "tests/elaborator/a-cited-hypothesis-an-identity/successor-at-zero";
const OTHER: &str = "tests/elaborator/powers/a-power-of-powers";

fn repo() -> Disk {
    Disk::new(PathBuf::from(env!("CARGO_MANIFEST_DIR")))
}

/// The library's files, which every tree holds.
const LIBRARY: [&str; 4] = [
    "corpus/db",
    "corpus/stdlib",
    "corpus/lean-bridges",
    "corpus/metamath-bridges",
];

/// A tree on disk, its own for the case `name`: the library, the two proof
/// files with `edit` made to `CITING`, and set.mm beside them as the build
/// finds it.
fn small_tree(name: &str, edit: Option<(&str, &str)>) -> PathBuf {
    let root = std::env::temp_dir().join(format!(
        "parley-build-failures-{name}-{}",
        std::process::id()
    ));
    if root.exists() {
        std::fs::remove_dir_all(&root).unwrap();
    }
    let from = repo();
    for rel in from.files() {
        let wanted = LIBRARY
            .iter()
            .any(|dir| rel.starts_with(&format!("{dir}/")))
            || rel == CITING
            || rel == APART;
        if !wanted {
            continue;
        }
        let mut text = from.read_text(&rel).unwrap();
        if let (true, Some((old, new))) = (rel == CITING, edit) {
            assert!(text.contains(old), "{CITING} holds {old:?}");
            text = text.replacen(old, new, 1);
        }
        let path = root.join(&rel);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, text).unwrap();
    }
    std::os::unix::fs::symlink(from.root().join("set.mm"), root.join("set.mm"))
        .unwrap();
    root
}

/// The path under the tree of the Metamath file the theorem `name` is built
/// into.
fn built_file(root: &Path, name: &str) -> PathBuf {
    let checked = parley::checker::checked(&Disk::new(root.to_path_buf()))
        .unwrap_or_else(|out| panic!("{}{}", out.printed, out.complained));
    let every = artifacts(&checked.corpus);
    let artifact = every.iter().find(|a| a.name == name).unwrap();
    root.join(artifact.path())
}

#[test]
fn a_refused_theorem_and_what_cites_it_are_not_built_and_the_rest_is() {
    let root = small_tree("refused", None);
    // A clean build first, so that each file has an old copy to remove.
    let clean = parley::tools::build::metamath::run(&root, None);
    assert_eq!(clean.status, 0, "{}{}", clean.printed, clean.complained);
    let (cited, citer, other) = (
        built_file(&root, CITED),
        built_file(&root, CITER),
        built_file(&root, OTHER),
    );
    assert!(cited.exists() && citer.exists() && other.exists());

    // The line H3 is cited as H9, which no line is.
    let text = std::fs::read_to_string(root.join(CITING)).unwrap();
    std::fs::write(
        root.join(CITING),
        text.replacen("algebra, from H3", "algebra, from H9", 1),
    )
    .unwrap();
    let check = parley::checker::run(&Disk::new(root.clone()));
    assert_eq!(check.status, 1, "the planted defect is a problem");
    let built = parley::tools::build::metamath::run(&root, None);

    assert!(
        built.printed.starts_with(&check.printed),
        "the build begins with the check:\n{}",
        built.printed
    );
    assert_eq!(built.status, 1);
    assert!(
        built.complained.contains(&format!("{CITED}: failed")),
        "{}",
        built.complained
    );
    assert!(
        built
            .complained
            .contains(&format!("{CITER}: not built, as {CITED} was not")),
        "{}",
        built.complained
    );
    assert!(!cited.exists(), "the refused theorem's old file is removed");
    assert!(!citer.exists(), "what cites it has its old file removed");
    assert!(other.exists(), "everything else is built");
    std::fs::remove_dir_all(&root).unwrap();
}

#[test]
fn a_problem_outside_every_theorem_ends_the_build_with_the_check() {
    // A second theorem of the same name in one file is a problem of the
    // file, outside every theorem.
    let root = small_tree(
        "outside",
        Some((
            "theorem successor-at-zero",
            "theorem successor-sum\n  then 1 = 1\n\n1.  1 = 1\n    arithmetic\n\ntheorem successor-at-zero",
        )),
    );
    let check = parley::checker::run(&Disk::new(root.clone()));
    assert_eq!(check.status, 1, "{}", check.printed);
    let built = parley::tools::build::metamath::run(&root, None);
    assert_eq!(built.status, 1);
    assert_eq!(built.printed, check.printed, "the build is the check alone");
    assert!(
        !root.join("corpus/elaboration").exists(),
        "nothing is built"
    );
    std::fs::remove_dir_all(&root).unwrap();
}

/// The corpus in memory, as the Lean build reads it.
fn whole_corpus() -> Memory {
    Memory::copy(&repo(), &["corpus", "proofs", "tests", "lean"]).unwrap()
}

#[test]
fn every_lean_failure_is_found_in_one_run_and_the_rest_is_built() {
    let clean = whole_corpus();
    let mut tree = Overlay::new(&clean);
    // A refused theorem, as in the Metamath case.
    let text = clean.read_text(CITING).unwrap();
    tree.write(
        CITING,
        text.replacen("algebra, from H3", "algebra, from H9", 1)
            .into_bytes(),
    );
    // Two library modules Lean is said not to read: their entries in the
    // module table carry an error in place of their modules.
    let table_path = parley::lean::modules::TABLE;
    let table = clean.read_text(table_path).unwrap();
    let mut rejected = Vec::new();
    let lines: Vec<String> = table
        .lines()
        .map(|line| {
            let mut entry: serde_json::Value = serde_json::from_str(line).unwrap();
            let key = entry["key"].as_str().unwrap_or_default().to_string();
            let module = key
                .strip_prefix("namespace ")
                .and_then(|rest| rest.lines().next())
                .filter(|m| m.starts_with("Parley.Items.Stdlib."));
            match module {
                Some(module) if rejected.len() < 2 => {
                    rejected.push(module.to_string());
                    let map = entry.as_object_mut().unwrap();
                    map.remove("modules");
                    map.insert("error".into(), "planted".into());
                    entry.to_string()
                }
                _ => line.to_string(),
            }
        })
        .collect();
    assert_eq!(rejected.len(), 2, "the table has two library modules");
    tree.write(table_path, (lines.join("\n") + "\n").into_bytes());

    let checked = parley::checker::checked(&tree)
        .unwrap_or_else(|out| panic!("{}{}", out.printed, out.complained));
    let table = parley::lean::modules::ModuleTable::read(&tree).unwrap();
    let made = parley::tools::build::lean::make(&checked, &table).unwrap();

    assert_eq!(
        made.failed.get(CITED).map(String::as_str),
        Some("the checker refuses it"),
        "{:?}",
        made.failed
    );
    assert_eq!(
        made.failed.get(CITER).map(String::as_str),
        Some(format!("it cites {CITED}, which was not built").as_str()),
        "{:?}",
        made.failed
    );
    for module in &rejected {
        let why = made.failed.get(module).unwrap_or_else(|| {
            panic!("{module} is reported: {:?}", made.failed.keys())
        });
        assert!(why.contains("planted"), "{module}: {why}");
    }
    use parley::lean::names::{module_of, path_of_module};
    for module in &rejected {
        assert!(
            !made.files.contains_key(&path_of_module(module)),
            "{module} is not written"
        );
    }
    assert!(
        made.files.contains_key(&path_of_module(&module_of(OTHER))),
        "everything else is built: {OTHER}"
    );
}
