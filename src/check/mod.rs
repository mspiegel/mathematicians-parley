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

use std::collections::BTreeSet;

use indexmap::{IndexMap, IndexSet};

use crate::citing::{Library, Proved};
use crate::corpus::{
    index, link_definitions, link_functions, module_of, parse_database, parse_proof,
    proof_files, record_files, written_text, FileScope, Intro, Item, Record,
    RecordKind, Theorem,
};
use crate::formula::Grammar;
use crate::formula::Sorts;
use crate::matching::Context;
use crate::outcome::{At, Problem};
use crate::sorts::infer;
use crate::sorts::{settled, Env};
use crate::source::Source;
use crate::text::check_encoding;

pub use library::{statements_in_scope, Known};

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
    let checked = prepared(source, |report, c| {
        for (i, thm) in c.theorems.iter().enumerate() {
            check_theorem(report, c, thm, &c.known[i], &c.clashes[i]);
        }
    });
    match checked {
        Ok((report, counts, ())) => summary(report, counts),
        Err(out) => out,
    }
}

/// Check the corpus under the source's root, after the files `edited` were
/// changed, with only the theorems an edit to them can reach checked
/// (`Checking::reached_from`). What is checked of the corpus as a whole is
/// checked, and the counts are the whole corpus's.
///
/// A theorem's problems depend on the corpus as read and on nothing another
/// theorem's check did, so what this reports is what `run` reports less the
/// problems of the theorems it passes over. It is for asking whether an edit
/// is reported, which it answers as `run` does; whether nothing is reported
/// is `run`'s to answer.
pub fn run_edited(source: &dyn Source, edited: &[String]) -> Outcome {
    let checked = prepared(source, |report, c| {
        let reached = c.reached_from(edited);
        for (i, thm) in c.theorems.iter().enumerate() {
            if reached.contains(thm.path.as_str()) {
                check_theorem(report, c, thm, &c.known[i], &c.clashes[i]);
            }
        }
    });
    match checked {
        Ok((report, counts, ())) => summary(report, counts),
        Err(out) => out,
    }
}

/// The corpus read once, which every theorem's checks are given.
pub struct Checking<'a> {
    theorems: &'a [Theorem],
    known: &'a [Known<'a>],
    clashes: &'a [Vec<infer::Clash>],
    env: Env<'a>,
    library: &'a Library<'a>,
    scopes: &'a [FileScope],
    words: &'a IndexSet<String>,
    methods: &'a IndexMap<String, &'a Record>,
    items: &'a IndexMap<String, Item<'a>>,
    statements: &'a IndexMap<String, infer::Reader>,
    store: infer::Store,
}

/// One proof file's text with an edit made, and the theorem in it the edit
/// is inside.
pub struct Cut {
    pub path: String,
    pub text: String,
    pub theorem: String,
}

/// What the checker says of each cut's theorem, the cut file read in place
/// of the file on disk and the rest of the corpus as it stands: the problems
/// it finds in that theorem. The corpus is read once for every cut.
pub fn check_cuts(
    source: &dyn Source,
    cuts: &[Cut],
) -> Result<Vec<Vec<String>>, Outcome> {
    prepared(source, |_, c| {
        cuts.iter().map(|cut| c.check_cut(cut)).collect()
    })
    .map(|(_, _, said)| said)
}

impl<'a> Checking<'a> {
    /// The proof files an edit to `edited` can change what is said of: the
    /// edited files, and every file importing from one of them, and every
    /// file importing from one of those. Where a file edited is not a proof
    /// file, a record or a notation, every theorem reads it, and every proof
    /// file is reached.
    fn reached_from(&self, edited: &[String]) -> BTreeSet<&'a str> {
        let every: BTreeSet<&'a str> =
            self.scopes.iter().map(|s| s.path.as_str()).collect();
        let mut reached: BTreeSet<&'a str> = BTreeSet::new();
        for path in edited {
            match every.get(path.as_str()) {
                Some(&proof) => {
                    reached.insert(proof);
                }
                None => return every,
            }
        }
        loop {
            let modules: BTreeSet<&str> =
                reached.iter().map(|p| module_of(p)).collect();
            let importing: Vec<&'a str> = self
                .scopes
                .iter()
                .filter(|s| !reached.contains(s.path.as_str()))
                .filter(|s| {
                    let mut from = s
                        .imports
                        .iter()
                        .map(|i| i.module.as_str())
                        .chain(s.items.iter().map(|i| i.module.as_str()))
                        .chain(s.functions.iter().map(|f| f.module.as_str()));
                    from.any(|m| modules.contains(m))
                })
                .map(|s| s.path.as_str())
                .collect();
            if importing.is_empty() {
                return reached;
            }
            reached.extend(importing);
        }
    }

    /// The problems one cut's theorem has, read from the cut's text. What a
    /// requires line says does not change what the theorem states, so the
    /// rest of the corpus is read as it was.
    fn check_cut(&mut self, cut: &Cut) -> Vec<String> {
        let Some(at) = self.scopes.iter().position(|s| s.path == cut.path) else {
            return vec![format!("{} is not a proof file of the corpus", cut.path)];
        };
        let theorems = match parse_proof(&cut.path, &cut.text, at) {
            Ok((_, found)) => found,
            Err(p) => return vec![p.to_string()],
        };
        let Some(thm) = theorems.iter().find(|t| t.name == cut.theorem) else {
            return vec![format!("{} has no theorem {}", cut.path, cut.theorem)];
        };
        let reader = formulas::read_with_citations(
            thm,
            self.env,
            self.statements,
            &mut self.store,
        );
        let library = self.library;
        let k = Known::new(thm, self.env, settled(&reader, &self.store), &library.ctx);
        let mut report = Report::default();
        check_theorem(&mut report, self, thm, &k, &reader.clashes);
        report.problems.iter().map(|p| p.to_string()).collect()
    }
}

/// What each record a requires line or an obtain cites asks or says there,
/// as the checker reads the page (`citations::answers`), for every theorem:
/// what `tests/agree.rs` compares with the elaborator's answers.
pub fn answers(source: &dyn Source) -> Result<Vec<String>, Outcome> {
    prepared(source, |_, c| {
        c.theorems
            .iter()
            .zip(c.known)
            .flat_map(|(thm, k)| citations::answers(thm, c.library, k))
            .collect()
    })
    .map(|(_, _, said)| said)
}

/// Every sentence a step claims or requires, printed from its tree and read
/// again, where the two trees differ: `Grammar::print` is right exactly when
/// this is empty. Each entry is the sentence, what it printed as, and where;
/// with them, how many sentences were read and printed.
pub fn printed_back(source: &dyn Source) -> Result<(usize, Vec<String>), Outcome> {
    prepared(source, |_, c| {
        let mut out = Vec::new();
        let mut read_count = 0;
        for (thm, k) in c.theorems.iter().zip(c.known) {
            for step in &thm.steps {
                let texts = crate::sorts::sentences(&step.claim_text())
                    .into_iter()
                    .chain(step.requires.iter().map(|r| r.fact.clone()));
                // Read as written, defined names and all, as a reader reads.
                let read = |text: &str| {
                    crate::formula::parse_here(text, c.env.g, &k.sorts).ok()
                };
                for text in texts {
                    let Some(node) = read(&text) else {
                        continue;
                    };
                    read_count += 1;
                    let printed = c.env.g.print(&node);
                    let again = read(&printed);
                    if again.as_ref().map(|a| a.shape()) != Some(node.shape()) {
                        out.push(format!(
                            "{}:{}  {text}  printed as  {printed}",
                            thm.path, step.line
                        ));
                    }
                }
            }
        }
        (read_count, out)
    })
    .map(|(_, _, out)| out)
}

/// Read the corpus, check what is checked of the corpus as a whole, and give
/// what was read to `then`; or the outcome where nothing can be read.
#[allow(clippy::type_complexity)]
fn prepared<T>(
    source: &dyn Source,
    then: impl FnOnce(&mut Report, &mut Checking<'_>) -> T,
) -> Result<(Report, (usize, usize, usize, usize), T), Outcome> {
    let mut report = Report::default();
    let db_files = record_files(source);
    let proofs = proof_files(source);
    if db_files.is_empty() || proofs.is_empty() {
        return Err(Outcome {
            printed: String::new(),
            complained: format!("no corpus under {}\n", source.root().display()),
            status: 2,
        });
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
    // A method written in words, `both directions`, names its record with
    // a hyphen between them, as every record's name is one word.
    for (i, r) in records.iter().enumerate() {
        if r.kind == RecordKind::Method {
            methods.insert(r.name.replace('-', " "), i);
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
    for (path, no, message) in link_functions(&records, &mut scopes)
        .into_iter()
        .chain(link_definitions(&theorems, &mut scopes))
    {
        report.say(&path, no, message);
    }
    // The library files a proof may import: those whose items it may cite.
    let library: IndexSet<String> = records
        .iter()
        .filter(|r| r.kind.is_item())
        .map(|r| r.module().to_string())
        .collect();
    structure::check_imports(&mut report, &theorems, &scopes, &items, &library);
    structure::check_definitions(&mut report, &theorems, &scopes);

    let steps: usize = theorems.iter().map(|t| t.steps.len()).sum();
    let counts = (theorems.len(), steps, items.len(), methods.len());

    // Nothing is read without the grammar, so a notation it cannot be built
    // from ends the run here.
    let grammar = match Grammar::load(&records) {
        Ok(g) => g,
        Err(p) => {
            report.problems.push(p);
            return Err(summary(report, counts));
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
    structure::check_function_imports(&mut report, &theorems, &scopes);
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
    let ctx = Context::new(&env.g.notations, &records);
    let mut known: Vec<Known> = Vec::new();
    let mut clashes: Vec<Vec<infer::Clash>> = Vec::new();
    for thm in &theorems {
        let reader = formulas::read_with_citations(thm, env, &statements, &mut store);
        known.push(Known::new(thm, env, settled(&reader, &store), &ctx));
        clashes.push(reader.clashes);
    }
    let proved = known
        .iter()
        .map(|k| {
            let at = Proved {
                thm: k.thm,
                sorts: &k.sorts,
            };
            (k.thm.qualified(), at)
        })
        .collect();
    let library = Library::new(&records, record_sorts.clone(), proved, env);

    formulas::check_item_clashes(&mut report, &statements, &items);
    let methods: IndexMap<String, &Record> = methods
        .iter()
        .map(|(name, &i)| (name.clone(), &records[i]))
        .collect();
    let mut checking = Checking {
        theorems: &theorems,
        known: &known,
        clashes: &clashes,
        env,
        library: &library,
        scopes: &scopes,
        words: &words,
        methods: &methods,
        items: &items,
        statements: &statements,
        store,
    };
    let out = then(&mut report, &mut checking);
    Ok((report, counts, out))
}

/// Everything checked of one theorem, given the corpus read once.
fn check_theorem(
    report: &mut Report,
    c: &Checking<'_>,
    thm: &Theorem,
    k: &Known<'_>,
    clashes: &[infer::Clash],
) {
    let (env, library, scopes) = (c.env, c.library, c.scopes);
    formulas::check_formulas(report, thm, env, k);
    structure::check_defined_below(report, thm, scopes);
    formulas::check_clashes(report, thm, clashes);
    formulas::check_contradiction(report, thm, env, k);
    formulas::check_contradicting(report, thm, env, k);
    formulas::check_impossible(report, thm, k);
    formulas::check_both_directions(report, thm, k);
    formulas::check_claimed_cases(report, thm, k);
    formulas::check_cases_cited(report, thm, k);
    formulas::check_closed_arithmetic(report, thm, env, k);
    formulas::check_closed_by_arithmetic(report, thm, env, k);
    formulas::check_membership_claims(report, thm, env, k);
    citations::check_hypotheses(report, thm, library, k);
    citations::check_conclusion(report, thm, library, k);
    formulas::check_define_citation(report, thm, library, k, scopes);
    citations::check_obtained(report, thm, library, k);
    citations::check_requires(report, thm, library, k);
    citations::check_surplus(report, thm, library, k, scopes);
    citations::check_repeated(report, thm, library, k);
    citations::check_exhibited(report, thm, library, k);
    citations::check_instantiated(report, thm, library, k);
    citations::check_define_domains(report, thm, library, k, scopes);
    formulas::check_chain_links(report, thm, library, k, scopes);
    structure::check_last_step(report, thm);
    structure::check_readings(report, thm);
    database::check_introductions(report, thm, env, k);
    formulas::check_recursions(report, thm, env, k);
    structure::check_sorts(report, thm);
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
        report,
        &thm.path,
        &thm.ranges,
        &lets,
        &written_text(thm),
        env,
        &k.sorts,
    );
    structure::check_capture(report, thm, &structure::claims_of(thm));
    structure::check_run_together(report, thm, c.words);
    structure::check_numbering(report, thm);
    structure::check_blocks(report, thm, c.methods);
    for step in &thm.steps {
        structure::check_justification_form(report, &thm.path, &step.just);
        structure::check_chain(report, thm, step);
    }
    structure::check_citations(report, thm, c.items, c.methods, scopes);
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
