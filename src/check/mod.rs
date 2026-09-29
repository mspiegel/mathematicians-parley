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
    written_text, FileScope, Intro, Record, RecordKind, Theorem,
};
use crate::formula::Grammar;
use crate::formula::Sorts;
use crate::outcome::{At, Problem};
use crate::sorts::infer;
use crate::sorts::{settled, Env};
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
    // The library files a proof may import: those whose items it may cite.
    let library: IndexSet<String> = records
        .iter()
        .filter(|r| r.kind.is_item())
        .map(|r| r.module().to_string())
        .collect();
    structure::check_imports(&mut report, &theorems, &scopes, &library);
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
    structure::check_function_names(
        &mut report,
        &theorems,
        &scopes,
        &grammar.functions,
    );
    structure::check_function_imports(
        &mut report,
        &theorems,
        &scopes,
        &grammar.functions,
    );
    database::check_functions(&mut report, &grammar);
    // A library function's name of several letters reads as one, as a word
    // does, so two names run together into it are caught as into a word.
    let mut words = words;
    words.extend(
        grammar
            .functions
            .keys()
            .filter(|n| n.chars().count() > 1)
            .cloned(),
    );
    // Each item's own lines, read once: what they say its names are, and
    // what its statement says to a step citing it. Records are told apart by
    // where they stand, as two may share a name (`check_database` reports
    // that). One store holds every kind, since a citation copies the kinds
    // of what it cites into the reading of the proof citing it.
    let mut store = infer::Store::default();
    let mut statements: IndexMap<String, infer::Reader> = IndexMap::new();
    let mut record_sorts: IndexMap<usize, Sorts> = IndexMap::new();
    for (i, r) in records.iter().enumerate().filter(|(_, r)| r.kind.is_item()) {
        let reader = infer::read_record(r, env, &mut store);
        record_sorts.insert(i, settled(&reader, &store));
        statements.insert(r.qualified(), reader);
    }
    for (i, r) in records
        .iter()
        .enumerate()
        .filter(|(_, r)| !r.ranges.is_empty())
    {
        let lets: Vec<(&str, usize)> = r
            .hypotheses
            .iter()
            .filter(|h| h.kind == Intro::Let)
            .map(|h| (h.text.as_str(), h.line))
            .collect();
        let mut text: Vec<&str> =
            r.hypotheses.iter().map(|h| h.text.as_str()).collect();
        text.extend(r.conclusions.iter().map(|(c, _)| c.as_str()));
        structure::check_ranges(
            &mut report,
            &r.path,
            &r.ranges,
            &lets,
            &text.join(" "),
            env,
            &record_sorts[&i],
        );
    }
    database::check_statements(&mut report, &records, env, &record_sorts);
    database::check_unsorted(&mut report, &records, env, &record_sorts);
    database::check_symbols(&mut report, &records);

    // Each theorem's lines, read once, after every statement it may cite.
    for thm in &theorems {
        statements.insert(thm.qualified(), infer::read_statement(thm, env, &mut store));
    }
    let mut known: Vec<Known> = Vec::new();
    let mut clashes: Vec<Vec<infer::Clash>> = Vec::new();
    for thm in &theorems {
        let reader = formulas::read_with_citations(thm, env, &statements, &mut store);
        known.push(Known::new(thm, env, settled(&reader, &store)));
        clashes.push(reader.clashes);
    }
    let library = Library::new(&records, &record_sorts, &known, env);

    formulas::check_item_clashes(&mut report, &statements, &items);
    let methods: IndexMap<String, &Record> = methods
        .iter()
        .map(|(name, &i)| (name.clone(), &records[i]))
        .collect();
    for ((thm, k), clashes) in theorems.iter().zip(known.iter()).zip(&clashes) {
        formulas::check_formulas(&mut report, thm, env, k);
        structure::check_defined_below(&mut report, thm, &scopes);
        formulas::check_clashes(&mut report, thm, clashes);
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
        let lets: Vec<(&str, usize)> = thm
            .hypotheses
            .iter()
            .filter(|h| h.kind == Intro::Let)
            .map(|h| (h.text.as_str(), h.line))
            .chain(thm.steps.iter().flat_map(|s| {
                s.openers
                    .iter()
                    .filter(|o| o.kind == Intro::Let)
                    .map(|o| (o.text.as_str(), o.line))
            }))
            .collect();
        structure::check_ranges(
            &mut report,
            &thm.path,
            &thm.ranges,
            &lets,
            &written_text(thm),
            env,
            &k.sorts,
        );
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
