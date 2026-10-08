//! The whole corpus, read from the working tree.

use indexmap::IndexMap;

use super::proof::{
    parse_proof, FileScope, FunctionImport, ItemKind, ScopeId, Theorem,
};
use super::records::{parse_database, Record, RecordKind};
use crate::outcome::{Checked, Problem};
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
    let _ = link_functions(&out.records, &mut out.scopes);
    let _ = link_definitions(&out.theorems, &mut out.scopes);
    Ok(out)
}

/// Set apart, in each file, the imports that name a library function: a
/// definition with `sort` and `builds` lines, which a formula applies by its
/// name. Its words are read as any item's are, so they are not what tell a
/// function apart; the record is. Say what is wrong with such an import:
/// (path, line, message) for each.
pub fn link_functions(
    records: &[Record],
    scopes: &mut [FileScope],
) -> Vec<(String, usize, String)> {
    let functions: IndexMap<String, &Record> = records
        .iter()
        .filter(|r| r.is_function())
        .map(|r| (r.qualified(), r))
        .collect();
    let mut problems = Vec::new();
    for scope in scopes.iter_mut() {
        let (named, items): (Vec<_>, Vec<_>) = std::mem::take(&mut scope.items)
            .into_iter()
            .partition(|i| functions.contains_key(&i.full()));
        scope.items = items;
        for i in named {
            let r = functions[&i.full()];
            let (keyword, whole) = (i.said.as_str(), i.full());
            if i.alias != i.name {
                problems.push((
                    scope.path.clone(),
                    i.line,
                    format!(
                        "import {keyword} {whole}: a library function is imported by its name alone, with no `as`"
                    ),
                ));
            }
            if i.said != r.header() {
                problems.push((
                    scope.path.clone(),
                    i.line,
                    format!(
                        "import {keyword} {whole}: {whole} is {}; import it as `import {} {whole}`",
                        Item::Record(r).described(),
                        r.header()
                    ),
                ));
            }
            scope.functions.push(FunctionImport {
                kind: i.kind,
                module: i.module,
                name: i.name,
                line: i.line,
            });
        }
    }
    problems
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
            let Some(&src) = by_module.get(&import.module) else {
                problems.push((
                    scopes[id].path.clone(),
                    import.line,
                    format!(
                        "import definition {}/{} names no proof file",
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
                        "import definition {}/{}: {} defines no {} outside its theorems",
                        import.module, import.name, import.module, import.name
                    ),
                ));
                continue;
            };
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
    /// What a citation of it writes, as its prefix is checked against: `mun:`
    /// for a record marked mundane, and its kind's prefix otherwise. A proved
    /// theorem is a theorem.
    pub fn cited_as(&self) -> ItemKind {
        match self {
            Item::Record(r) => ItemKind::of_record(r),
            Item::Theorem(_) => ItemKind::Theorem,
        }
    }

    /// Its header's words before its name, as a message names what it is:
    /// `mundane theorem`, `axiom`.
    pub fn header(&self) -> String {
        match self {
            Item::Record(r) => r.header(),
            Item::Theorem(_) => RecordKind::Theorem.to_string(),
        }
    }

    /// What it is, as a message says it: `a mundane theorem`, `an axiom`.
    pub fn described(&self) -> String {
        let header = self.header();
        let article = if header.starts_with(['a', 'e', 'i', 'o', 'u']) {
            "an"
        } else {
            "a"
        };
        format!("{article} {header}")
    }

    /// Whether a step citing it unfolds it: a definition. This is read from
    /// the record and not from the citation, since a mundane definition is
    /// cited `mun:`.
    pub fn unfolds(&self) -> bool {
        matches!(self, Item::Record(r) if r.kind.unfolds())
    }

    /// Whether what it concludes says "for all" anywhere. Every universal
    /// the notation database has is spelt with those words, so the text
    /// answers what reading each conclusion would. A step claiming "for all
    /// k ∈ X, P" applies an item that does not at a member of X, and reads
    /// one that does as written (`SYNTAX.md`, a step said of every member).
    ///
    /// A conclusion that is one letter alone is a formula letter, as
    /// `modus-ponens` concludes Q, and stands for whatever formula the
    /// citation makes it, a "for all" among them, so it counts as one.
    pub fn says_for_all(&self) -> bool {
        let said = |text: &str| {
            let text = str::trim(text);
            text.to_lowercase().contains("for all")
                || (!text.is_empty() && text.chars().all(char::is_alphabetic))
        };
        match self {
            Item::Record(r) => r.conclusions.iter().any(|(text, _)| said(text)),
            Item::Theorem(t) => said(&t.conclusion),
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
