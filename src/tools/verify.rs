//! Every elaborated proof, checked by a verifier rather than by this project.
//!
//! The checker reads the readable layer and the elaborator writes Metamath
//! from it. Neither is evidence that what came out is a proof: an elaborator
//! that emits a wrong step emits it confidently, and the assumption count at
//! the head of each file reports a proof that assumes nothing whether or not
//! it proves what it claims. Only a verifier settles that, and it is the one
//! tool here that was not written for this project.
//!
//! Verifying the proofs one at a time costs about eighteen seconds each, and
//! almost all of it is reading set.mm. `mmverify.py` resolves an inclusion
//! against the working directory and keeps the set of files it has opened,
//! so including them all from one file reads set.mm once.
//!
//! Which files there are comes from the build, which is what finds every
//! generated file. Reading the directory instead would be simpler and wrong:
//! the hand-written comparisons sit in it beside them and are not among
//! them. Each file is placed in a directory of its own at the path the
//! others include it by, its path under `elaboration/`.
//!
//! Which of them to include is read off the inclusions rather than listed: a
//! proof that nothing else includes is a root, and including every root
//! reaches everything. A new proof is covered the day it is written, where a
//! list of roots would leave the gate green and the new proof unread.
//!
//! mmverify.py belongs to metamath and is not vendored, for the reason set.mm
//! is not: say where it is with `MMVERIFY`, or leave a copy or a link at the
//! root of the working tree.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::LazyLock;
use std::time::Instant;

use regex::Regex;

use crate::said::Said;

static INCLUDE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"\$\[\s*(\S+)\s*\$\]").expect("a valid pattern"));
/// A labelled `$p`, which is what there is one of per theorem proved.
static PROVES: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"(?m)^\s*(\S+)\s+\$p\s").expect("a valid pattern"));

/// The verifier, said in the environment, at the root, or on PATH.
pub fn where_mmverify(root: &Path) -> Option<PathBuf> {
    let on_path = std::env::var_os("PATH").and_then(|paths| {
        std::env::split_paths(&paths)
            .map(|dir| dir.join("mmverify.py"))
            .find(|p| p.exists())
    });
    [
        std::env::var_os("MMVERIFY").map(PathBuf::from),
        Some(root.join("mmverify.py")),
        on_path,
    ]
    .into_iter()
    .flatten()
    .find(|p| !p.as_os_str().is_empty() && p.exists())
}

/// How a file including this one names it: its path under `elaboration/`.
fn included_as(path: &str) -> &str {
    path.strip_prefix("elaboration/").unwrap_or(path)
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
/// `setmm` with the verifier at `verifier`.
pub fn run(
    root: &Path,
    built: &[String],
    setmm: Option<&Path>,
    verifier: Option<&Path>,
) -> Said {
    let mut said = Said::default();
    let Some(verifier) = verifier else {
        said.printed =
            "mmverify.py not found; say where it is with MMVERIFY, or leave a \
                        copy or a link at the root of the working tree\n"
                .into();
        said.status = 2;
        return said;
    };
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

    let top = roots(&texts);
    let proved: usize = texts.iter().map(|(_, t)| PROVES.find_iter(t).count()).sum();
    said.printed += &format!(
        "{proved} proofs in {} files, reached from {}\n",
        built.len(),
        top.join(", ")
    );

    let ran = joined_and_verified(root, built, library, verifier, &top);
    let (done, spent) = match ran {
        Ok(ran) => ran,
        Err(e) => {
            said.printed += &format!("\ncould not run {}: {e}\n", verifier.display());
            said.status = 2;
            return said;
        }
    };
    said.printed += &String::from_utf8_lossy(&done.stdout);
    said.complained += &String::from_utf8_lossy(&done.stderr);
    let name = verifier
        .file_name()
        .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
    if !done.status.success() {
        said.printed += &format!("\n{name} rejected a proof\n");
        said.status = 1;
        return said;
    }
    said.printed += &format!("\nall {proved} verify, in {spent:.0}s\n");
    said
}

/// Each file placed at the path the others include it by, one file including
/// every root, and the verifier run over it. Linked rather than copied:
/// set.mm is 51 MB.
fn joined_and_verified(
    root: &Path,
    built: &[String],
    library: &Path,
    verifier: &Path,
    top: &[String],
) -> std::io::Result<(std::process::Output, f64)> {
    use std::os::unix::fs::symlink;
    let tmp = tempfile::tempdir()?;
    let at = tmp.path();
    let absolute = |p: &Path| std::fs::canonicalize(p);
    for path in built {
        let link = at.join(included_as(path));
        if let Some(dir) = link.parent() {
            std::fs::create_dir_all(dir)?;
        }
        symlink(absolute(&root.join(path))?, &link)?;
    }
    let library = absolute(library)?;
    let name = library
        .file_name()
        .map_or_else(|| "set.mm".into(), |n| n.to_os_string());
    symlink(&library, at.join(&name))?;
    if name != "set.mm" {
        symlink(&library, at.join("set.mm"))?;
    }
    let joined: String = top.iter().map(|name| format!("$[ {name} $]\n")).collect();
    std::fs::write(at.join("everything.mm"), joined)?;
    let began = Instant::now();
    let done = std::process::Command::new("python3")
        .arg(absolute(verifier)?)
        .arg("everything.mm")
        .current_dir(at)
        .output()?;
    Ok((done, began.elapsed().as_secs_f64()))
}
