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

use super::build::lean::{generated_in_tree, make, Made};
use crate::lean::export::{Export, STANDARD_AXIOMS};
use crate::lean::readback::differences;
use crate::lean::theorem::Spot;
use crate::said::Said;
use crate::source::{Disk, Source};

/// The Lean project, under the root of the tree.
const PROJECT: &str = "lean";

/// lean4export, as Lake builds it, from the Lean project.
const EXPORTER: &str = ".lake/packages/lean4export/.lake/build/bin/lean4export";

/// What the Lean build makes of the tree, or what stops it.
fn made(source: &dyn Source) -> Result<Made, Said> {
    let checked = crate::checker::checked(source)?;
    make(&checked).map_err(|problem| Said {
        printed: String::new(),
        complained: format!("{problem}\n"),
        status: 2,
    })
}

/// Every Lean file in the tree is what a fresh build makes, and nothing the
/// build does not make is left in the generated part of `lean/`.
pub fn fresh(root: &Path) -> Said {
    let source = Disk::new(root.to_path_buf());
    let made = match made(&source) {
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
    for path in generated_in_tree(root) {
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
    let failed: std::collections::BTreeSet<String> =
        refused.iter().map(|r| r.module.clone()).collect();
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
        let sorry = rest.contains("declaration uses 'sorry'");
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
