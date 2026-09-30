//! The whole corpus, read from the working tree.

use indexmap::IndexMap;

use super::define::define_parts;
use super::proof::{parse_proof, FileScope, ItemKind, ScopeId, Theorem};
use super::records::{parse_database, Record, RecordKind};
use crate::outcome::{Built, Checked, Problem};
use crate::source::Source;
use crate::text::check_encoding;

/// The database: notation and methods in corpus/db/, items in the library.
pub fn record_files(source: &dyn Source) -> Vec<String> {
    let mut out = source.listed(&format!("{}/db", super::CORPUS), ".records");
    out.extend(
        source.listed(&format!("{}/{}", super::CORPUS, super::STDLIB), ".records"),
    );
    out
}

/// Every readable proof under the root, wherever it is kept.
pub fn proof_files(source: &dyn Source) -> Vec<String> {
    source.found(".proof")
}

/// Every record and every readable proof, with the scope of each proof file.
#[derive(Clone, Debug, Default)]
pub struct Corpus {
    pub records: Vec<Record>,
    pub theorems: Vec<Theorem>,
    pub scopes: Vec<FileScope>,
}

fn read(source: &dyn Source, rel: &str) -> Checked<String> {
    let raw = source
        .read(rel)
        .map_err(|e| Problem::new(rel, 1, format!("cannot be read: {e}")))?;
    check_encoding(rel, &raw)
}

/// Every record and every readable proof, read from the working tree.
pub fn corpus(source: &dyn Source) -> Checked<Corpus> {
    let mut out = Corpus::default();
    for rel in record_files(source) {
        let text = read(source, &rel)?;
        out.records.extend(parse_database(&rel, &text)?);
    }
    for rel in proof_files(source) {
        let text = read(source, &rel)?;
        let (scope, theorems) = parse_proof(&rel, &text, out.scopes.len())?;
        out.scopes.push(scope);
        out.theorems.extend(theorems);
    }
    // What does not resolve is the checker's to report; here a definition
    // import that names nothing is simply one that brings nothing in.
    let _ = link_definitions(&out.theorems, &mut out.scopes);
    Ok(out)
}

/// Point every definition import at the define it names, and say what does
/// not resolve: (path, line, message) for each.
pub fn link_definitions(
    theorems: &[Theorem],
    scopes: &mut [FileScope],
) -> Vec<(String, usize, String)> {
    let mut by_module: IndexMap<String, ScopeId> = IndexMap::new();
    for thm in theorems {
        by_module
            .entry(thm.module().to_string())
            .or_insert(thm.scope);
    }
    let mut problems = Vec::new();
    for &id in by_module.values() {
        let mut linked = IndexMap::new();
        for import in scopes[id].imports.clone() {
            let keyword = import.kind.record_kind();
            let Some(&src) = by_module.get(&import.module) else {
                problems.push((
                    scopes[id].path.clone(),
                    import.line,
                    format!(
                        "import {keyword} {}/{} names no proof file",
                        import.module, import.name
                    ),
                ));
                continue;
            };
            let Some(d) = scopes[src].written(&import.name).cloned() else {
                problems.push((
                    scopes[id].path.clone(),
                    import.line,
                    format!(
                        "import {keyword} {}/{}: {} defines no {} outside its theorems",
                        import.module, import.name, import.module, import.name
                    ),
                ));
                continue;
            };
            // A define with an argument is a function and one without is a
            // definition, and the keyword says which.
            let takes = matches!(
                define_parts(&d.text),
                Built(said) if said.one().is_some_and(|one| one.param.is_some())
            );
            let is = if takes {
                ItemKind::Function
            } else {
                ItemKind::Definition
            };
            if import.kind != is {
                problems.push((
                    scopes[id].path.clone(),
                    import.line,
                    format!(
                        "import {keyword} {}/{}: {} is a {}, since it takes {}",
                        import.module,
                        import.name,
                        import.name,
                        is.record_kind(),
                        if takes { "an argument" } else { "no argument" }
                    ),
                ));
            }
            linked.insert(import.alias.clone(), (src, d));
        }
        scopes[id].linked = linked;
    }
    problems
}

/// An item a proof may cite: a record of the library, or a theorem a proof
/// of this corpus proves.
#[derive(Clone, Copy, Debug)]
pub enum Item<'a> {
    Record(&'a Record),
    Theorem(&'a Theorem),
}

impl<'a> Item<'a> {
    /// What it is, as a citation's prefix is checked against: a proved
    /// theorem is a theorem.
    pub fn kind(&self) -> &'static str {
        match self {
            Item::Record(r) => r.kind.as_str(),
            Item::Theorem(_) => RecordKind::Theorem.as_str(),
        }
    }

    pub fn path(&self) -> &'a str {
        match self {
            Item::Record(r) => &r.path,
            Item::Theorem(t) => &t.path,
        }
    }

    /// Whether it is proved by a readable proof of this corpus.
    pub fn proved(&self) -> bool {
        matches!(self, Item::Theorem(_))
    }
}

/// Every definition and theorem by its full name.
///
/// A theorem of a proof file is its own entry: the proof holds its
/// statement. Where two share a name the first is kept, and the checker is
/// what says there are two.
pub fn index<'a>(
    records: &'a [Record],
    theorems: &'a [Theorem],
) -> IndexMap<String, Item<'a>> {
    let mut out = IndexMap::new();
    for r in records {
        if r.kind.is_item() {
            out.entry(r.qualified()).or_insert(Item::Record(r));
        }
    }
    for t in theorems {
        out.entry(t.qualified()).or_insert(Item::Theorem(t));
    }
    out
}
