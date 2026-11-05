//! `parley build lean`: every theorem the Lean build covers, written as a
//! Lean file over Mathlib under `lean/`.
//!
//! The build writes three kinds of file. Each module of the library with a
//! record that has a `lean-proof` field becomes `lean/Parley/Items/…`, a theorem
//! for each sentence an item concludes. Each theorem the build covers
//! (`lean::coverage`) becomes a file of its own, which imports the items
//! and the theorems it cites. `lean/Parley.lean` imports them all, so that
//! `lake build` checks exactly what this build made. A generated file the
//! build no longer makes is removed. The Lean bridges, written by hand, are
//! in `corpus/lean-bridges/`, a library of their own that every file
//! imports.
//!
//! The build only writes. The gate asks Lean whether the files prove what
//! they say.

use std::collections::BTreeSet;
use std::path::Path;

use indexmap::IndexMap;

use super::{write_changed, Written};
use crate::checker::CheckedCorpus;
use crate::corpus::{cited_items, RecordKind};
use crate::lean::coverage::{coverage, Covered};
use crate::lean::expr::Writer;
use crate::lean::items::{declaration, item, items_module, Item};
use crate::lean::names::{module_of, path_of_module};
use crate::lean::templates::Templates;
use crate::lean::theorem::{as_item, theorem, Sources};
use crate::outcome::Route;
use crate::said::Said;
use crate::source::Disk;

/// The Lean bridges, a library of their own in `corpus/lean-bridges/`,
/// written by hand: the module importing them all.
pub const LIBRARY: &str = "LeanBridges";

/// What a Lean build makes: each file's path and text, the theorems left
/// out and why, and what could not be written.
#[derive(Default)]
pub struct Made {
    /// Each file, by its path from the root of the tree.
    pub files: IndexMap<String, String>,
    /// Each theorem left out, and why.
    pub left_out: IndexMap<String, String>,
    /// Each item or theorem in the build that could not be written, and
    /// why: a gap of the Lean writer's.
    pub gaps: IndexMap<String, String>,
    /// Each declaration written, by its full Lean name, with the arithmetic
    /// the page writes in its statement, which the gate's read-back
    /// compares with what Lean elaborated.
    pub statements: IndexMap<String, std::collections::BTreeMap<String, usize>>,
    /// Each theorem's file, by its path, with where on the page each of its
    /// lines was written for.
    pub origins: IndexMap<String, Origins>,
}

/// Where a theorem's Lean file comes from, line by line.
pub struct Origins {
    /// The theorem, by its full name.
    pub theorem: String,
    /// The proof file it is written in.
    pub page: String,
    /// Each line of the Lean file, from 1, with the place on the page it
    /// was written for.
    pub lines: Vec<crate::lean::theorem::Origin>,
}

/// A theorem the build wrote that imports a module it could not write.
struct Unwritten {
    /// The theorem's module.
    module: String,
    /// The theorem, by its full name.
    theorem: String,
    /// The module it imports that was not written.
    import: String,
}

/// The bridge module of tactics every generated file uses.
const TACTICS: &str = "Tactics";

/// The module of the tactics a proof about sets uses beside the others.
const SET_TACTICS: &str = "SetTactics";

/// Each tactic outside `Tactics` and `SetTactics`, and the module that
/// holds it, which a file naming the tactic imports. Every file importing a
/// module is rebuilt when it changes, so a family most files do not call is
/// a module of its own; the layout, and where a new tactic or case goes, is
/// set out at the head of `corpus/lean-bridges/Tactics.lean`.
/// `parley_subst` names `parley_subst_at` too, which is in the same module.
const TACTIC_MODULES: &[(&str, &str)] = &[
    ("parley_clear", "AlgebraTactics"),
    ("parley_ring", "AlgebraTactics"),
    ("parley_field", "AlgebraTactics"),
    ("parley_subst", "SubstTactics"),
    ("parley_put_at", "SubstTactics"),
    ("parley_order", "OrderTactics"),
    ("parley_int_power", "PowerTactics"),
    ("parley_cast_toNat", "PowerTactics"),
    ("parley_of_complex", "ComplexTactics"),
    ("parley_arith", "ArithTactics"),
    ("parley_suppose", "ArithTactics"),
    ("parley_real", "RealTactics"),
    ("parley_whole_side", "WholeTactics"),
];

/// Modules that tag definitions into the tactics' simp set `parley_unfold`,
/// by what a file's Lean text writes that they apply to: a file that writes
/// a factorial or a binomial coefficient imports the module that tags them
/// (`FactorialTactics`), and no other file does.
const RULE_MODULES: &[(&str, &str)] = &[
    ("LeanBridges.Counting.factorial", "FactorialTactics"),
    ("LeanBridges.Counting.choose", "FactorialTactics"),
];

/// The tactic a step leaves its side conditions to, and the one a proof
/// about sets leaves them to, which tries the first and then the ways of
/// sets.
const SIDE: &str = "parley_side";
const SET_SIDE: &str = "parley_set_side";

/// Whether a proof's Lean text is about sets: it writes Lean's `Set` or
/// counts one.
fn uses_sets(text: &str) -> bool {
    text.contains("Set ") || text.contains("Set.") || text.contains(".encard")
}

/// The modules of the library a generated file imports: the tactics every
/// file uses, the module of each other tactic its Lean text names, and each
/// bridge module it names, `Counting` for a `LeanBridges.Counting.…`. A file
/// imports no module it does not use, so that a change in one rebuilds only
/// the files that use it.
fn library_imports(text: &str) -> BTreeSet<String> {
    let prefix = format!("{LIBRARY}.");
    let mut out = BTreeSet::from([TACTICS.to_string()]);
    for (written, module) in TACTIC_MODULES.iter().chain(RULE_MODULES) {
        if text.contains(written) {
            out.insert(module.to_string());
        }
    }
    for (at, _) in text.match_indices(&prefix) {
        let rest = &text[at + prefix.len()..];
        let subject: String = rest
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect();
        if !subject.is_empty() {
            out.insert(subject);
        }
    }
    out
}

/// The header every generated file opens with.
fn header(imports: &[String], from: &str) -> String {
    let mut out = String::from("module\n\n");
    for i in imports {
        out.push_str(&format!("public import {i}\n"));
    }
    out.push_str(&format!(
        "\n/-! Written from {from} by parley build lean. -/\n\n"
    ));
    out
}

/// Everything the Lean build makes of the corpus as the checker read it.
pub fn make(checked: &CheckedCorpus) -> Result<Made, crate::outcome::Problem> {
    let templates = Templates::read(&checked.corpus.records)?;
    let targets =
        crate::methods::terms::Targets::of(&checked.grammar, &checked.corpus.records);
    let ctx = crate::matching::Context::new(
        &checked.grammar.notations,
        &checked.corpus.records,
    );
    let mut made = Made::default();
    let writer = Writer::new(&checked.grammar, &templates);

    // The library's items with a lean field, by full name, and each
    // module's declarations.
    let mut items: IndexMap<String, Item> = IndexMap::new();
    let mut modules: IndexMap<String, (String, Vec<String>)> = IndexMap::new();
    for record in &checked.corpus.records {
        if record.kind == RecordKind::Notation || record.lean_target().is_none() {
            continue;
        }
        let full = format!("{}/{}", record.module(), record.name);
        match item(&writer, checked, record) {
            Route::Built(it) => {
                let entry = modules
                    .entry(items_module(record))
                    .or_insert_with(|| (record.path.clone(), Vec::new()));
                for (s, proof) in it.sentences.iter().zip(&it.proofs) {
                    entry.1.push(declaration(s, proof));
                    made.statements.insert(s.decl.clone(), s.arithmetic.clone());
                }
                items.insert(full, it);
            }
            // A phrase's definition is made from its define, its proof
            // `Iff.rfl` wherever the meaning can be stated: one that cannot
            // is left out, and what cites it with it (`coverage`). Any
            // other record that gives a Lean proof claims its statement is
            // one the build writes.
            Route::Declined(d) if record.phrase.is_some() => {
                made.left_out.insert(full, d.reason());
            }
            Route::Declined(d) => {
                made.gaps.insert(full, d.reason());
            }
        }
    }
    for (module, (path, decls)) in &modules {
        let body = decls.join("\n\n");
        let imports: Vec<String> = library_imports(&body).into_iter().collect();
        let mut text = header(&imports, path);
        text.push_str(&format!("public section\n\nnamespace {module}\n\n"));
        for d in decls {
            text.push_str(d);
            text.push_str("\n\n");
        }
        text.push_str(&format!("end {module}\n"));
        made.files.insert(path_of_module(module), text);
    }

    // The theorems the build covers, first as items a citation names. A
    // record the Lean build proves by a Parley proof is cited as that proof.
    let stated: BTreeSet<String> = items.keys().cloned().collect();
    let covered = coverage(checked, &templates, &stated);
    let mut proves: IndexMap<&str, Vec<String>> = IndexMap::new();
    for record in &checked.corpus.records {
        let proof = record
            .lean_provided()
            .and_then(crate::corpus::records::Provided::proof);
        if let Some(proof) = proof {
            proves.entry(proof).or_default().push(record.qualified());
        }
    }
    let mut theorems = Vec::new();
    for thm in &checked.corpus.theorems {
        let name = thm.qualified();
        match covered.get(&name) {
            Some(Covered::In) => {}
            Some(Covered::Out { reason }) => {
                made.left_out.insert(name, reason.clone());
                continue;
            }
            None => continue,
        }
        let Some(rec) = checked.theorems.get(&name) else {
            continue;
        };
        let sources = Sources {
            checked,
            templates: &templates,
            targets: &targets,
            items: &items,
            ctx: &ctx,
        };
        match as_item(&sources, thm, rec) {
            Route::Built(it) => {
                theorems.push((thm, rec));
                for record in proves.get(name.as_str()).into_iter().flatten() {
                    items.insert(record.clone(), it.clone());
                }
                // A theorem whose record gives its own Lean proof, from
                // Mathlib, is cited as that record's item; the Parley
                // proof is written beside it all the same.
                items.entry(name).or_insert(it);
            }
            Route::Declined(d) => {
                made.gaps.insert(name, d.reason());
            }
        }
    }
    let mut written: Vec<String> = modules.keys().cloned().collect();
    // Each theorem's module, with the theorem and the modules it imports.
    let mut imported: IndexMap<String, (String, Vec<String>)> = IndexMap::new();
    for (thm, rec) in theorems {
        let name = thm.qualified();
        let sources = Sources {
            checked,
            templates: &templates,
            targets: &targets,
            items: &items,
            ctx: &ctx,
        };
        let file = match theorem(&sources, thm, rec) {
            Route::Built(f) => f,
            Route::Declined(d) => {
                made.gaps.insert(name, d.reason());
                continue;
            }
        };
        let module = module_of(&name);
        // The modules of the items it cites, which must be written for it
        // to be, and beside them the library it uses.
        let mut cited: BTreeSet<String> = BTreeSet::new();
        for (full, _) in cited_items(thm) {
            if let Some(it) = items.get(&full) {
                if it.module != module {
                    cited.insert(it.module.clone());
                }
            }
        }
        let cited: Vec<String> = cited.into_iter().collect();
        imported.insert(module.clone(), (name.clone(), cited.clone()));
        // A proof about sets leaves its reader the ways of sets as well,
        // from their own module (`SetTactics`).
        let of_sets = uses_sets(&file.text);
        let body = match of_sets {
            true => file.text.replace(SIDE, SET_SIDE),
            false => file.text.clone(),
        };
        let mut library = library_imports(&body);
        if of_sets {
            library.insert(SET_TACTICS.to_string());
        }
        let imports: Vec<String> = library.into_iter().chain(cited).collect();
        let mut text = header(&imports, &thm.path);
        text.push_str(&format!("public section\n\nnamespace {module}\n\n"));
        let above = text.lines().count();
        text.push_str(&body);
        text.push_str(&format!("\nend {module}\n"));
        let origins = file
            .origins
            .into_iter()
            .map(|o| crate::lean::theorem::Origin {
                line: o.line + above,
                ..o
            })
            .collect();
        let path = path_of_module(&module);
        made.origins.insert(
            path.clone(),
            Origins {
                theorem: name.clone(),
                page: thm.path.clone(),
                lines: origins,
            },
        );
        if let Some(s) = items.get(&name).and_then(|it| it.sentences.first()) {
            made.statements.insert(s.decl.clone(), s.arithmetic.clone());
        }
        made.files.insert(path, text);
        written.push(module);
    }

    // A theorem citing one the build could not write cannot be written
    // either, and nor can one citing it.
    loop {
        let missing: Vec<Unwritten> = imported
            .iter()
            .filter(|(m, _)| written.contains(m))
            .filter_map(|(m, (name, imports))| {
                imports
                    .iter()
                    .find(|i| !written.contains(i))
                    .map(|i| Unwritten {
                        module: m.clone(),
                        theorem: name.clone(),
                        import: i.clone(),
                    })
            })
            .collect();
        if missing.is_empty() {
            break;
        }
        for Unwritten {
            module,
            theorem: name,
            import,
        } in missing
        {
            written.retain(|w| *w != module);
            let path = path_of_module(&module);
            made.files.shift_remove(&path);
            made.origins.shift_remove(&path);
            if let Some(s) = items.get(&name).and_then(|it| it.sentences.first()) {
                made.statements.shift_remove(&s.decl);
            }
            made.gaps.insert(
                name,
                format!("it cites {import}, which the Lean build cannot yet write"),
            );
        }
    }

    let mut root = String::from("module\n\n");
    root.push_str(&format!("public import {LIBRARY}\n"));
    for m in &written {
        root.push_str(&format!("public import {m}\n"));
    }
    made.files.insert("lean/Parley.lean".to_string(), root);
    Ok(made)
}

/// Every `.lean` file under `lean/Parley/` the build wrote before.
pub fn generated_in_tree(root: &Path) -> Vec<String> {
    let mut out = Vec::new();
    let mut stack = vec![root.join("lean/Parley")];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for e in entries.flatten() {
            let path = e.path();
            let rel = path
                .strip_prefix(root)
                .map(|p| p.to_string_lossy().to_string())
                .unwrap_or_default();
            if path.is_dir() {
                stack.push(path);
            } else if rel.ends_with(".lean") {
                out.push(rel);
            }
        }
    }
    out.sort();
    out
}

/// Build the Lean files of the tree at `root`, writing each file that
/// changed. Every file is made each time, since `lean/Parley.lean` imports
/// them all; a theorem `wanted` that is not in the build is reported, with
/// why, and nothing is written.
pub fn run(root: &Path, wanted: Option<&str>) -> Said {
    let mut said = Said::default();
    let source = Disk::new(root.to_path_buf());
    let checked = match crate::checker::checked(&source) {
        Ok(checked) => checked,
        Err(out) => return out,
    };
    let made = match make(&checked) {
        Ok(made) => made,
        Err(problem) => {
            said.complained = format!("{problem}\n");
            said.status = 2;
            return said;
        }
    };
    if let Some(name) = wanted {
        if !made.files.contains_key(&path_of_module(&module_of(name))) {
            said.complained = match made.left_out.get(name).or(made.gaps.get(name)) {
                Some(why) => format!("{name} is not in the Lean build: {why}\n"),
                None => format!("no theorem {name}\n"),
            };
            said.status = 2;
            return said;
        }
    }
    let mut changed = 0;
    let mut failed = false;
    for (path, text) in &made.files {
        match write_changed(root, path, text) {
            Ok(Written::Changed) => {
                changed += 1;
                said.printed += &format!("* {path}\n");
            }
            Ok(Written::Same) => said.printed += &format!("  {path}\n"),
            Err(problem) => {
                said.complained += &format!("{problem}\n");
                failed = true;
            }
        }
    }
    for path in generated_in_tree(root) {
        if !made.files.contains_key(&path) {
            match std::fs::remove_file(root.join(&path)) {
                Ok(()) => {
                    changed += 1;
                    said.printed += &format!("- {path}\n");
                }
                Err(e) => {
                    said.complained += &format!("{path}: {e}\n");
                    failed = true;
                }
            }
        }
    }
    if !made.left_out.is_empty() {
        said.printed += "\nleft out of the Lean build:\n";
        for (name, why) in &made.left_out {
            said.printed += &format!("  {name}: {why}\n");
        }
    }
    if !made.gaps.is_empty() {
        said.printed +=
            "\nthe Lean build cannot yet write these, which the checker accepts:\n";
        for (name, why) in &made.gaps {
            said.printed += &format!("  {name}: {why}\n");
        }
        failed = true;
    }
    said.printed += &format!(
        "\n{} built, {changed} changed, {} left out\n",
        made.files.len(),
        made.left_out.len()
    );
    if failed {
        said.status = 1;
    }
    said
}
