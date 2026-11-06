//! The gate's Lean stages.
//!
//! The first asks whether every Lean file in the tree is what a fresh
//! `parley build lean` makes, and needs no Lean. The second asks Lean: it
//! builds `lean/` with `lake build`, and reports each error against the
//! theorem and the step of the page its line was written for. It then
//! reads back what Lean proved, through lean4export: each statement does
//! the page's arithmetic in a type that computes as the page does
//! (`lean::readback`), and each rests on no axiom beyond Lean's own, so a
//! proof left as `sorry` is red. Mathlib is not committed; where it has not
//! been downloaded the second stage is red and says how to download it,
//! since a stage that skipped would call green what it had not looked at.

use std::path::Path;
use std::process::Command;

use super::build::lean::{make, Made};
use crate::lean::export::{Export, STANDARD_AXIOMS};
use crate::lean::readback::differences;
use crate::lean::theorem::Spot;
use crate::said::Said;
use crate::source::{Disk, Source};

/// The Lean project, under the root of the tree.
const PROJECT: &str = "lean";

/// One `lake` at a time in the project: two at once contend for the git
/// lock of its packages, and one fails.
static LAKE: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// lean4export, as Lake builds it, from the Lean project.
const EXPORTER: &str = ".lake/packages/lean4export/.lake/build/bin/lean4export";

/// A problem that stops the build, as the gate says it.
fn refused(problem: crate::outcome::Problem) -> Said {
    Said {
        printed: String::new(),
        complained: format!("{problem}\n"),
        status: 2,
    }
}

/// What the Lean build makes of the tree, or what stops it.
fn made(source: &dyn Source) -> Result<Made, Said> {
    let checked = crate::checker::checked(source)?;
    let table = crate::lean::modules::ModuleTable::read(source).map_err(refused)?;
    let made = make(&checked, &table).map_err(refused)?;
    // The gate asks Lean nothing: a module the table lacks would change
    // the files a fresh build writes.
    match made.unanswered.first() {
        None => Ok(made),
        Some(l) => Err(refused(crate::outcome::Problem::new(
            crate::lean::modules::TABLE,
            1,
            format!(
                "the table has no modules for the {} `{}`: run parley build lean",
                l.kind(),
                l.key()
            ),
        ))),
    }
}

/// Every Lean file in the tree is what a fresh build makes, and nothing the
/// build does not make is left in the generated part of `lean/`.
pub fn fresh(root: &Path) -> Said {
    fresh_in(&Disk::new(root.to_path_buf()))
}

/// `fresh` of a tree a source holds, which a planted-defect test edits in
/// memory.
pub fn fresh_in(source: &dyn Source) -> Said {
    let made = match made(source) {
        Ok(made) => made,
        Err(said) => return said,
    };
    let mut said = Said::default();
    for (path, text) in &made.files {
        match source.read_text(path) {
            Ok(have) if have == *text => {}
            Ok(_) => {
                said.complained +=
                    &format!("{path} differs from what a fresh build makes\n")
            }
            Err(_) => said.complained += &format!("{path} is not in the tree\n"),
        }
    }
    let generated = source
        .files()
        .into_iter()
        .filter(|f| f.starts_with("lean/Parley/") && f.ends_with(".lean"));
    for path in generated {
        if !made.files.contains_key(&path) {
            said.complained += &format!("{path} is no longer made by the build\n");
        }
    }
    for (name, why) in &made.gaps {
        said.complained += &format!(
            "{name}: the Lean build cannot yet write this, which the checker accepts: {why}\n"
        );
    }
    if !said.complained.is_empty() {
        said.printed += "run parley build lean\n";
        said.status = 1;
    }
    said.printed += &format!(
        "{} files, {} theorems left out of the Lean build\n",
        made.files.len(),
        made.left_out.len()
    );
    said
}

/// Whether Lean and Mathlib are where the build needs them; what to do
/// where they are not.
fn ready(project: &Path) -> Result<(), String> {
    let lake = Command::new("lake").arg("--version").output();
    if !lake.is_ok_and(|o| o.status.success()) {
        return Err(
            "lake is not installed: install elan, which installs it".to_string()
        );
    }
    let mathlib =
        project.join(".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean");
    if !mathlib.exists() {
        return Err(format!(
            "Mathlib has not been downloaded: run `lake exe cache get` in {}",
            project.display()
        ));
    }
    Ok(())
}

/// Lean accepts every file, and each statement it proved is the page's,
/// on Lean's own axioms.
pub fn accepted(root: &Path) -> Said {
    let mut said = Said::default();
    let project = root.join(PROJECT);
    if let Err(why) = ready(&project) {
        said.complained = format!("{why}\n");
        said.status = 1;
        return said;
    }
    let source = Disk::new(root.to_path_buf());
    let made = match made(&source) {
        Ok(made) => made,
        Err(said) => return said,
    };
    let build = Command::new("lake")
        .arg("build")
        .current_dir(&project)
        .output();
    let build = match build {
        Ok(out) => out,
        Err(e) => {
            said.complained = format!("lake build did not run: {e}\n");
            said.status = 1;
            return said;
        }
    };
    let output = format!(
        "{}{}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    let refused = refusals(&output, &made);
    for r in &refused {
        said.complained += &format!("{}\n", r.said);
    }
    if !build.status.success() && refused.is_empty() {
        said.complained += "lake build failed:\n";
        said.complained += &output;
        said.status = 1;
        return said;
    }
    let failed =
        with_dependents(refused.iter().map(|r| r.module.clone()).collect(), &made);
    if failed.is_empty() {
        said.printed += &format!("Lean accepts all {} files\n", made.files.len());
    } else {
        said.printed += &format!(
            "Lean refuses {} of {} files\n",
            failed.len(),
            made.files.len()
        );
        said.status = 1;
    }
    // What Lean accepted is read back, whatever it refused.
    let checked: Vec<&String> = made
        .statements
        .keys()
        .filter(|decl| !failed.contains(module_of_decl(decl)))
        .collect();
    match read_back(&project, &made, &checked) {
        Ok(lines) if lines.is_empty() => {
            said.printed += &format!(
                "each of {} statements read back does the page's arithmetic, on Lean's own axioms\n",
                checked.len()
            );
        }
        Ok(lines) => {
            for l in lines {
                said.complained += &format!("{l}\n");
            }
            said.status = 1;
        }
        Err(why) => {
            said.complained += &format!("{why}\n");
            said.status = 1;
        }
    }
    said
}

/// `accepted` of the Lean files a planted-defect test edited, each checked
/// against what the tree has built (`lake env lean`, the file read from
/// stdin) and every error and `sorry` said against the page; a full `lake
/// build` of the tree for each case would take most of an hour.
pub fn accepted_edited(source: &dyn Source, edited: &[String]) -> Said {
    let mut said = Said::default();
    let project = source.root().join(PROJECT);
    if let Err(why) = ready(&project) {
        said.complained = format!("{why}\n");
        said.status = 1;
        return said;
    }
    let made = match made(source) {
        Ok(made) => made,
        Err(said) => return said,
    };
    let lean_files: Vec<&String> = edited
        .iter()
        .filter(|f| f.starts_with("lean/Parley/") && f.ends_with(".lean"))
        .collect();
    let mut refused = Vec::new();
    for file in &lean_files {
        let Ok(text) = source.read_text(file) else {
            said.complained += &format!("{file} is not in the tree\n");
            said.status = 1;
            continue;
        };
        let _one = LAKE
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let checked = Command::new("lake")
            .args(["env", "lean", "--stdin"])
            .current_dir(&project)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .and_then(|mut child| {
                if let Some(mut stdin) = child.stdin.take() {
                    use std::io::Write;
                    stdin.write_all(text.as_bytes())?;
                }
                child.wait_with_output()
            });
        let out = match checked {
            Ok(out) => out,
            Err(e) => {
                said.complained += &format!("lean did not run on {file}: {e}\n");
                said.status = 1;
                continue;
            }
        };
        let output = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let in_project = file.trim_start_matches(&format!("{PROJECT}/"));
        refused.extend(refusals(&as_built_by_lake(&output, in_project), &made));
    }
    for r in &refused {
        said.complained += &format!("{}\n", r.said);
    }
    if refused.is_empty() {
        said.printed +=
            &format!("Lean accepts the {} files edited\n", lean_files.len());
    } else {
        said.status = 1;
    }
    said
}

/// Lean's messages of a file read from stdin, `<stdin>:15:4: error: …`,
/// as `lake build` writes them of the file, `error: Parley/…/X.lean:15:4:
/// …`, which `refusals` reads.
fn as_built_by_lake(output: &str, file: &str) -> String {
    let mut out = String::new();
    for line in output.lines() {
        let Some(rest) = line.strip_prefix("<stdin>:") else {
            out.push_str(line);
            out.push('\n');
            continue;
        };
        let mut parts = rest.splitn(3, ':');
        let (Some(at), Some(col), Some(message)) =
            (parts.next(), parts.next(), parts.next())
        else {
            continue;
        };
        let message = message.trim_start();
        let (kind, said) = match (
            message.strip_prefix("error: "),
            message.strip_prefix("warning: "),
        ) {
            (Some(m), _) => ("error", m),
            (None, Some(m)) => ("warning", m),
            (None, None) => continue,
        };
        out.push_str(&format!("{kind}: {file}:{at}:{col}: {said}\n"));
    }
    out
}

/// The modules refused, with every module that imports one of them, which
/// Lean could not build either.
fn with_dependents(
    mut failed: std::collections::BTreeSet<String>,
    made: &Made,
) -> std::collections::BTreeSet<String> {
    // Each file's module, and the modules the build gave it to import.
    let imports: Vec<(String, Vec<String>)> = made
        .imports
        .iter()
        .map(|(path, imported)| {
            let module = path
                .trim_start_matches(&format!("{PROJECT}/"))
                .trim_end_matches(".lean")
                .replace('/', ".");
            (module, imported.clone())
        })
        .collect();
    loop {
        let more: Vec<String> = imports
            .iter()
            .filter(|(m, i)| {
                !failed.contains(m) && i.iter().any(|x| failed.contains(x))
            })
            .map(|(m, _)| m.clone())
            .collect();
        if more.is_empty() {
            return failed;
        }
        failed.extend(more);
    }
}

/// The module a declaration is in: its name without its last part.
fn module_of_decl(decl: &str) -> &str {
    decl.rsplit_once('.').map_or(decl, |(module, _)| module)
}

/// One thing Lean refused: the module, and what it refused said against
/// the page.
struct Refusal {
    module: String,
    said: String,
}

/// Each error and each `sorry` Lean reports, said against the page: the
/// theorem, the step and the line of the proof file its Lean line was
/// written for.
fn refusals(output: &str, made: &Made) -> Vec<Refusal> {
    let mut out = Vec::new();
    for line in output.lines() {
        let (error, rest) = if let Some(rest) = line.strip_prefix("error: ") {
            (true, rest)
        } else if let Some(rest) = line.strip_prefix("warning: ") {
            (false, rest)
        } else {
            continue;
        };
        let sorry = rest.contains("declaration uses `sorry`");
        if !error && !sorry {
            continue;
        }
        // `Parley/Proofs/…/X.lean:15:4: message`.
        let mut parts = rest.splitn(4, ':');
        let (Some(file), Some(at), Some(_col), Some(message)) =
            (parts.next(), parts.next(), parts.next(), parts.next())
        else {
            if error && !rest.starts_with("build failed") {
                out.push(Refusal {
                    module: String::new(),
                    said: rest.to_string(),
                });
            }
            continue;
        };
        let path = format!("{PROJECT}/{file}");
        let module = file.trim_end_matches(".lean").replace('/', ".");
        let Ok(at) = at.parse::<usize>() else {
            out.push(Refusal {
                module,
                said: rest.to_string(),
            });
            continue;
        };
        let message = message.trim();
        let said = match made.origins.get(&path) {
            Some(origins) => {
                let origin = origins.lines.iter().rev().find(|o| o.line <= at);
                let (spot, page_line) = match origin {
                    Some(o) => (
                        match &o.spot {
                            Spot::Step(n) => format!("step {n}"),
                            Spot::Statement => "the statement".to_string(),
                        },
                        o.page_line,
                    ),
                    None => ("the statement".to_string(), 0),
                };
                format!(
                    "{} {spot} ({}:{page_line}): the build cannot yet prove this in Lean, which the checker accepts: {message}",
                    origins.theorem, origins.page
                )
            }
            None => format!("{path}:{at}: {message}"),
        };
        out.push(Refusal { module, said });
    }
    out
}

/// Each statement Lean proved, read back through lean4export: what differs
/// from the page's arithmetic, and each axiom beyond Lean's own, said
/// against the declaration.
fn read_back(
    project: &Path,
    made: &Made,
    decls: &[&String],
) -> Result<Vec<String>, String> {
    if decls.is_empty() {
        return Ok(Vec::new());
    }
    let export = project.join(EXPORTER);
    if !export.exists() {
        let built = Command::new("lake")
            .args(["build", "lean4export"])
            .current_dir(project)
            .output()
            .map_err(|e| format!("lake build lean4export did not run: {e}"))?;
        if !built.status.success() {
            return Err("lake build lean4export failed".to_string());
        }
    }
    // Each module of a declaration read back, and then the declarations.
    let modules: std::collections::BTreeSet<&str> =
        decls.iter().map(|d| module_of_decl(d)).collect();
    // lake runs in the project, so the program is named from there.
    let mut args: Vec<String> = vec!["env".to_string(), EXPORTER.to_string()];
    args.extend(modules.iter().map(|m| m.to_string()));
    args.push("--".to_string());
    args.extend(decls.iter().map(|d| d.to_string()));
    let out = Command::new("lake")
        .args(&args)
        .current_dir(project)
        .output()
        .map_err(|e| format!("lean4export did not run: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "lean4export failed: {}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let text = String::from_utf8_lossy(&out.stdout);
    let read = Export::read(&text)?;
    let mut lines = Vec::new();
    for decl in decls {
        let Some(page) = made.statements.get(*decl) else {
            continue;
        };
        if !read.decls.contains_key(decl.as_str()) {
            lines.push(format!("{decl}: not in what Lean proved"));
            continue;
        }
        for d in differences(page, &read.arithmetic(decl)) {
            lines.push(format!("{decl}: statement differs: {d}"));
        }
        let beyond: Vec<String> = read
            .axioms(decl)
            .into_iter()
            .filter(|a| !STANDARD_AXIOMS.contains(&a.as_str()))
            .collect();
        if !beyond.is_empty() {
            lines.push(format!("{decl}: rests on {}", beyond.join(", ")));
        }
    }
    Ok(lines)
}
