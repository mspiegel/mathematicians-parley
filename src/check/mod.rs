//! Checking the corpus against `GRAMMAR.md`.
//!
//! Reports the grammar, the numbering, block structure, pointer resolution,
//! the scope of every citation, calculation chains, that every formula on
//! the page parses one way, that a citation supplies the hypotheses of what
//! it cites, and that its claim is what that item concludes. It does not
//! build the kernel proof; that needs the elaborator.

mod citations;
mod database;
mod formulas;
mod library;
mod structure;

use indexmap::{IndexMap, IndexSet};

use crate::corpus::{
    index, link_definitions, parse_database, parse_proof, proof_files, record_files,
    FileScope, Record, RecordKind, Theorem,
};
use crate::formula::Grammar;
use crate::kinds;
use crate::outcome::{At, Problem};
use crate::sorts::{sorts_of_record, Env};
use crate::source::Source;
use crate::text::check_encoding;

pub use library::{Known, Library};

/// Methods whose steps this checker accepts without examining them.
pub const CLOSURE: [&str; 5] = [
    "algebra",
    "arithmetic",
    "inequalities",
    "join",
    "membership",
];

/// A variable may be a Greek letter and may carry a subscript or a prime.
/// These are not notation and have no record of their own; see `GRAMMAR.md`.
const IDENTIFIER_CHARACTERS: &str =
    "αβγδεζηθικλμνξοπρστυφχψωΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ₀₁₂₃₄₅₆₇₈₉′";

/// The relations a calculation's lines join by.
const RELATIONS: [&str; 3] = ["=", "≤", "<"];

/// What a run found: every defect, and every step accepted without being
/// examined because it rests on a closure method.
#[derive(Default)]
pub struct Report {
    pub problems: Vec<Problem>,
    /// (method, step number) of each step resting on a closure method.
    pub trusted: Vec<(String, String)>,
}

impl Report {
    pub fn say(&mut self, path: &str, line: impl Into<At>, message: impl Into<String>) {
        self.problems.push(Problem::new(path, line, message));
    }
}

/// What the check printed, and the status it exits with.
pub use crate::said::Said as Outcome;

/// Check the corpus under the source's root.
pub fn run(source: &dyn Source) -> Outcome {
    let mut report = Report::default();
    let db_files = record_files(source);
    let proofs = proof_files(source);
    if db_files.is_empty() || proofs.is_empty() {
        return Outcome {
            printed: String::new(),
            complained: format!("no corpus under {}\n", source.root().display()),
            status: 2,
        };
    }

    let mut texts: IndexMap<String, String> = IndexMap::new();
    for rel in db_files.iter().chain(proofs.iter()) {
        let raw = match source.read(rel) {
            Ok(raw) => raw,
            Err(e) => {
                report.say(rel, 1, format!("cannot be read: {e}"));
                continue;
            }
        };
        match check_encoding(rel, &raw) {
            Ok(text) => {
                texts.insert(rel.clone(), text);
            }
            Err(p) => report.problems.push(p),
        }
    }

    let mut records: Vec<Record> = Vec::new();
    for rel in &db_files {
        let Some(text) = texts.get(rel) else { continue };
        match parse_database(rel, text) {
            Ok(found) => records.extend(found),
            Err(p) => report.problems.push(p),
        }
    }

    let mut methods: IndexMap<String, usize> = IndexMap::new();
    for (i, r) in records.iter().enumerate() {
        if r.kind == RecordKind::Method {
            methods.insert(r.name.clone(), i);
        }
    }
    let mut allowed: IndexSet<char> = IndexSet::new();
    for r in records.iter().filter(|r| r.kind == RecordKind::Notation) {
        for value in r.fields.values() {
            allowed.extend(value.chars());
        }
    }
    allowed.extend(IDENTIFIER_CHARACTERS.chars());

    database::check_database(&mut report, &records);
    database::check_notation(&mut report, &records);
    let words = structure::declared_words(&records);

    let mut theorems: Vec<Theorem> = Vec::new();
    let mut scopes: Vec<FileScope> = Vec::new();
    for rel in &proofs {
        let Some(text) = texts.get(rel) else { continue };
        database::check_characters(&mut report, rel, text, &allowed);
        match parse_proof(rel, text, scopes.len()) {
            Ok((scope, found)) => {
                scopes.push(scope);
                theorems.extend(found);
            }
            Err(p) => report.problems.push(p),
        }
    }

    let items = index(&records, &theorems);
    let mut seen: IndexMap<String, usize> = IndexMap::new();
    for thm in &theorems {
        let name = thm.qualified();
        if let Some(at) = seen.get(&name) {
            report.say(
                &thm.path,
                thm.line,
                format!("theorem {} is already proved at line {at}", thm.name),
            );
        }
        seen.entry(name).or_insert(thm.line);
    }
    for (path, no, message) in link_definitions(&theorems, &mut scopes) {
        report.say(&path, no, message);
    }
    structure::check_imports(&mut report, &theorems, &scopes);
    structure::check_definitions(&mut report, &theorems, &scopes);

    let steps: usize = theorems.iter().map(|t| t.steps.len()).sum();
    let counts = (theorems.len(), steps, items.len(), methods.len());

    // Nothing is read without the grammar, so a notation it cannot be built
    // from ends the run here.
    let grammar = match Grammar::load(&records) {
        Ok(g) => g,
        Err(p) => {
            report.problems.push(p);
            return summary(report, counts);
        }
    };
    let env = Env {
        g: &grammar,
        scopes: &scopes,
    };
    // What each item's own lines say its names are, read once. Records are
    // told apart by where they stand, as two may share a name
    // (`check_database` reports that).
    let record_sorts: IndexMap<usize, crate::formula::Sorts> = records
        .iter()
        .enumerate()
        .filter(|(_, r)| r.kind.is_item())
        .map(|(i, r)| (i, sorts_of_record(r, env)))
        .collect();
    database::check_statements(&mut report, &records, env, &record_sorts);
    database::check_unsorted(&mut report, &records, env, &record_sorts);
    database::check_symbols(&mut report, &records);

    let known: Vec<Known> = theorems.iter().map(|t| Known::new(t, env)).collect();
    let library = Library::new(&records, &record_sorts, &known, env);

    let mut store = kinds::Store::default();
    let statements =
        formulas::statement_kinds(env, &records, &record_sorts, &known, &mut store);
    formulas::check_item_kinds(&mut report, &statements, &items);
    let methods: IndexMap<String, &Record> = methods
        .iter()
        .map(|(name, &i)| (name.clone(), &records[i]))
        .collect();
    for (thm, k) in theorems.iter().zip(known.iter()) {
        formulas::check_formulas(&mut report, thm, env, k);
        structure::check_defined_below(&mut report, thm, &scopes);
        formulas::check_kinds(&mut report, thm, env, &statements, k, &mut store);
        formulas::check_contradiction(&mut report, thm, env, k);
        formulas::check_closed_arithmetic(&mut report, thm, env, k);
        formulas::check_membership_claims(&mut report, thm, env, k);
        citations::check_hypotheses(&mut report, thm, &library, k);
        citations::check_conclusion(&mut report, thm, &library, k);
        formulas::check_define_citation(&mut report, thm, &library, k, &scopes);
        citations::check_obtained(&mut report, thm, &library, k);
        citations::check_requires(&mut report, thm, &library, k);
        citations::check_surplus(&mut report, thm, &library, k);
        formulas::check_chain_links(&mut report, thm, &library, k, &scopes);
        structure::check_last_step(&mut report, thm);
        structure::check_readings(&mut report, thm);
        database::check_introductions(&mut report, thm, env, k);
        formulas::check_recursions(&mut report, thm, env, k);
        structure::check_sorts(&mut report, thm);
        structure::check_capture(&mut report, thm, &structure::claims_of(thm));
        structure::check_run_together(&mut report, thm, &words);
        structure::check_numbering(&mut report, thm);
        structure::check_blocks(&mut report, thm, &methods);
        for step in &thm.steps {
            structure::check_justification_form(&mut report, &thm.path, &step.just);
            structure::check_chain(&mut report, thm, step);
        }
        structure::check_citations(&mut report, thm, &items, &methods, &scopes);
    }
    summary(report, counts)
}

/// What the run found, as printed, and the exit status.
fn summary(report: Report, counts: (usize, usize, usize, usize)) -> Outcome {
    let mut problems = report.problems;
    problems.sort_by(|a, b| a.path.cmp(&b.path).then(a.line.cmp(&b.line)));
    let mut out = String::new();
    for p in &problems {
        out.push_str(&format!("{p}\n"));
    }
    out.push('\n');
    let (theorems, steps, items, methods) = counts;
    out.push_str(&format!(
        "{theorems} theorems, {steps} steps, {items} items, {methods} methods\n"
    ));
    out.push_str(&format!("{} problem(s)\n", problems.len()));
    let mut by_method: IndexMap<&str, usize> = IndexMap::new();
    for (method, _) in &report.trusted {
        *by_method.entry(method.as_str()).or_insert(0) += 1;
    }
    let total: usize = by_method.values().sum();
    out.push_str(&format!(
        "{total} step(s) accepted without checking, resting on a closure method:\n"
    ));
    for method in CLOSURE {
        if let Some(n) = by_method.get(method) {
            out.push_str(&format!("    {n:4}  {method}\n"));
        }
    }
    Outcome {
        printed: out,
        complained: String::new(),
        status: if problems.is_empty() { 0 } else { 1 },
    }
}
