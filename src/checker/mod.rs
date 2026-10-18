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
pub mod record;
mod structure;

use std::collections::BTreeSet;

use indexmap::{IndexMap, IndexSet};

use crate::citing::{Library, Proved};
use crate::corpus::{
    index, link_definitions, link_functions, module_of, parse_database, parse_proof,
    proof_files, record_files, Corpus, FileScope, Intro, Item, Method, Record,
    RecordKind, Step, Theorem,
};
use crate::formula::notation_id::Spelling;
use crate::formula::page::{Sentence, Written};
use crate::formula::Grammar;
use crate::formula::Sorts;
use crate::matching::Context;
use crate::outcome::{At, Problem, Route};
use crate::sorts::infer;
use crate::sorts::{settled, Env};
use crate::source::Source;
use crate::text::check_encoding;

pub use library::{statements_in_scope, Known};
pub use record::CheckedTheorem;
pub use structure::{cited_in_order, out_of_reach, unresolved};

/// A variable may be a Greek letter and may carry a subscript or a prime.
/// These are not notation and have no record of their own; see `GRAMMAR.md`.
const IDENTIFIER_CHARACTERS: &str =
    "αβγδεζηθικλμνξοπρστυφχψωΑΒΓΔΕΖΗΘΙΚΛΜΝΞΟΠΡΣΤΥΦΧΨΩ₀₁₂₃₄₅₆₇₈₉′";

/// The relations a calculation's lines join by, as the skeleton cuts them.
const RELATIONS: [&str; 6] = crate::corpus::proof::CHAIN_RELATIONS;

/// What a run found: every defect.
#[derive(Default)]
pub struct Report {
    pub problems: Vec<Problem>,
}

impl Report {
    pub fn say(&mut self, path: &str, line: impl Into<At>, message: impl Into<String>) {
        self.problems.push(Problem::new(path, line, message));
    }

    /// A step resting on `method` that its decider settles neither way: the
    /// checker examines every closure step (`methods`), so a claim the
    /// method cannot decide is one the step may not rest on it for.
    pub fn undecided(
        &mut self,
        path: &str,
        method: Method,
        step: &crate::corpus::Step,
    ) {
        self.say(
            path,
            step.just.line,
            format!(
                "step {} names {}, which does not decide what it claims",
                crate::corpus::fmt(&step.number),
                method.as_str()
            ),
        );
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

/// Every theorem as the checker reads it, by its qualified name: its shape,
/// its sorts and what the checker reports in it. The build is handed these
/// and builds only a theorem with no problem, so that it refuses exactly
/// what the checker refuses and says it as the checker does. What the
/// checker reports of the corpus as a whole, outside every theorem, is
/// `run`'s to say.
pub fn checked(source: &dyn Source) -> Result<CheckedCorpus, Outcome> {
    checked_where(source, |_| true)
}

/// The corpus as the checker read it, which the build builds from, and the
/// checker's record of each theorem it was asked for.
pub struct CheckedCorpus {
    pub corpus: Corpus,
    /// The grammar the corpus's records declare, which the checker read with.
    pub grammar: std::rc::Rc<Grammar>,
    pub theorems: IndexMap<String, CheckedTheorem>,
}

/// `checked` of the theorems whose full name `wanted` holds, and of no
/// other: a theorem's record depends on the corpus as read and on nothing
/// another theorem's check did, so each is what `checked` makes of it. A
/// file that does not read or parse is the outcome, as nothing of the
/// corpus can be built without all of it.
pub fn checked_where(
    source: &dyn Source,
    wanted: impl Fn(&str) -> bool,
) -> Result<CheckedCorpus, Outcome> {
    let read = read_corpus(source)?;
    if !read.whole {
        let counts = counts_of(&read.corpus);
        return Err(summary(read.report, counts));
    }
    let checked = prepared_in(&read.corpus, read.report, |_, c| {
        let mut out = IndexMap::new();
        for (i, thm) in c.theorems.iter().enumerate() {
            if !wanted(&thm.qualified()) {
                continue;
            }
            let mut own = Report::default();
            check_theorem(&mut own, c, thm, &c.known[i], &c.clashes[i]);
            let mut record = CheckedTheorem::of(thm);
            record.sorts = c.known[i].sorts.clone();
            record.problems = own.problems;
            record.typed = thm
                .steps
                .iter()
                .map(|step| library::typed_in_scope(&c.known[i], step))
                .collect();
            record.said_sums = thm
                .steps
                .iter()
                .map(|step| library::sums_said_once(&c.known[i], step))
                .collect();
            record.cited = thm
                .steps
                .iter()
                .map(|step| citations::cited(step, c.library, &c.known[i]))
                .collect();
            record.cited_requires =
                citations::requires_cited(thm, c.library, &c.known[i]);
            record.links = formulas::transitivity_links(thm, &c.known[i]);
            // A block whose goals are a defect owes nothing here: the defect
            // is among the record's problems (`check_block_ends`), and the
            // build builds no theorem with one.
            for block in &mut record.blocks {
                let owed = formulas::block_owes(&thm.steps[block.owner], &c.known[i]);
                block.owes = owed
                    .unwrap_or_default()
                    .into_iter()
                    .map(|o| record::Owed {
                        part: o.part,
                        claim: o.claim,
                    })
                    .collect();
            }
            out.insert(thm.qualified(), record);
        }
        out
    });
    let (_, _, theorems) = checked?;
    // The grammar the checks read with: a grammar is kept for the records it
    // was loaded from (`Grammar::load`), and `prepared_in` loaded it.
    let grammar = Grammar::load(&read.corpus.records).map_err(|p| {
        let mut report = Report::default();
        report.problems.push(p);
        summary(report, counts_of(&read.corpus))
    })?;
    Ok(CheckedCorpus {
        corpus: read.corpus,
        grammar,
        theorems,
    })
}

/// How many theorems, steps, items and methods the corpus holds, which a
/// summary ends on.
fn counts_of(corpus: &Corpus) -> (usize, usize, usize, usize) {
    let steps: usize = corpus.theorems.iter().map(|t| t.steps.len()).sum();
    let items = index(&corpus.records, &corpus.theorems).len();
    let methods = corpus
        .records
        .iter()
        .filter(|r| r.kind == RecordKind::Method)
        .count();
    (corpus.theorems.len(), steps, items, methods)
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
    /// Each definition's word, and the methods its record says decide it.
    defined: &'a IndexMap<Spelling, formulas::DefinedWord>,
    /// Each operation a notation declares, and whether arithmetic works it out.
    operations: &'a IndexMap<String, bool>,
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
        // A proof file the reader refused has no theorems, and its problem is
        // the reader's, said already; what imports it is reached still. A
        // record reaches every theorem, as what any of them reads may change.
        let mut refused: BTreeSet<&str> = BTreeSet::new();
        for path in edited {
            match every.get(path.as_str()) {
                Some(&proof) => {
                    reached.insert(proof);
                }
                None if path.ends_with(".proof") => {
                    refused.insert(module_of(path));
                }
                None => return every,
            }
        }
        loop {
            let mut modules: BTreeSet<&str> =
                reached.iter().map(|p| module_of(p)).collect();
            modules.extend(refused.iter().copied());
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

/// What the item each obtain cites says there is, at the step
/// (`citations::obtained_there`).
pub struct ObtainedThere {
    pub path: String,
    /// The line of the obtain's step.
    pub line: usize,
    /// The item's statements, in the page's notation.
    pub said: Route<Vec<String>>,
}

/// What the item each obtain of every theorem cites says there is, where
/// it is an item and not a definition that unfolds.
pub fn obtained_there(source: &dyn Source) -> Result<Vec<ObtainedThere>, Outcome> {
    prepared(source, |_, c| {
        let mut out = Vec::new();
        for (thm, k) in c.theorems.iter().zip(c.known) {
            for step in &thm.steps {
                if let Some(said) = citations::obtained_there(step, c.library, k) {
                    out.push(ObtainedThere {
                        path: thm.path.clone(),
                        line: step.line,
                        said: said.map(|s| s.iter().map(|n| k.print(n)).collect()),
                    });
                }
            }
        }
        out
    })
    .map(|(_, _, said)| said)
}

/// What a step citing an item makes each of its letters
/// (`citations::bound_there`).
pub struct BoundThere {
    pub path: String,
    /// The line of the citing step.
    pub line: usize,
    /// Each letter of the cited theorem, and what it stands for there, in
    /// the page's notation.
    pub letters: Vec<(String, String)>,
}

/// What each citation of an item, in every theorem, makes the cited item's
/// letters.
pub fn bound_there(source: &dyn Source) -> Result<Vec<BoundThere>, Outcome> {
    prepared(source, |_, c| {
        let mut out = Vec::new();
        for (thm, k) in c.theorems.iter().zip(c.known) {
            for step in &thm.steps {
                if let Some(bound) = citations::bound_there(step, c.library, k) {
                    out.push(BoundThere {
                        path: thm.path.clone(),
                        line: step.line,
                        letters: bound
                            .iter()
                            .map(|(name, node)| (name.clone(), k.print(node)))
                            .collect(),
                    });
                }
            }
        }
        out
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
                let sentences = step
                    .claim
                    .sentences()
                    .into_iter()
                    .chain(step.requires.iter().flat_map(|r| r.fact.sentences()));
                // Read as written, defined names and all, as a reader reads.
                // What does not read is `check_formulas`'s to report.
                let read = |sentence: &Sentence| sentence.read(c.env.g, &k.sorts).ok();
                for sentence in sentences {
                    let text = sentence.text();
                    let Some(node) = read(&sentence) else {
                        continue;
                    };
                    read_count += 1;
                    // What the printer wrote, read back where the sentence
                    // is written, to test the printer.
                    let printed = c.env.g.print(&node);
                    let again =
                        Written::new(&printed, sentence.path(), sentence.line());
                    let again = again.sentence().ok();
                    let again = again.as_ref().and_then(read);
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

/// The corpus as the checker reads it, and what reading it found wrong.
struct Read {
    corpus: Corpus,
    report: Report,
    /// Whether every file read and parsed, so that `corpus` is all of it:
    /// a file that does not is reported and left out.
    whole: bool,
}

/// Read every record file and proof file under the source's root, and link
/// each file's imports of library functions and definitions; or the
/// outcome where there is no corpus to read.
fn read_corpus(source: &dyn Source) -> Result<Read, Outcome> {
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

    let mut whole = true;
    let mut texts: IndexMap<String, String> = IndexMap::new();
    for rel in db_files.iter().chain(proofs.iter()) {
        let raw = match source.read(rel) {
            Ok(raw) => raw,
            Err(e) => {
                report.say(rel, 1, format!("cannot be read: {e}"));
                whole = false;
                continue;
            }
        };
        match check_encoding(rel, &raw) {
            Ok(text) => {
                texts.insert(rel.clone(), text);
            }
            Err(p) => {
                report.problems.push(p);
                whole = false;
            }
        }
    }

    let mut records: Vec<Record> = Vec::new();
    for rel in &db_files {
        let Some(text) = texts.get(rel) else { continue };
        match parse_database(rel, text) {
            Ok(found) => records.extend(found),
            Err(p) => {
                report.problems.push(p);
                whole = false;
            }
        }
    }

    let mut allowed: IndexSet<char> = IndexSet::new();
    for r in records.iter().filter(|r| r.kind == RecordKind::Notation) {
        for value in r.fields.values() {
            allowed.extend(value.chars());
        }
        // A pattern writing a raised numeral takes every raised digit.
        if r.field("pattern")
            .is_some_and(|p| p.contains(crate::formula::RAISED_HOLE))
        {
            allowed.extend(crate::formula::token::RAISED);
        }
    }
    allowed.extend(IDENTIFIER_CHARACTERS.chars());

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
            Err(p) => {
                report.problems.push(p);
                whole = false;
            }
        }
    }
    for (path, no, message) in link_functions(&records, &mut scopes)
        .into_iter()
        .chain(link_definitions(&theorems, &mut scopes))
    {
        report.say(&path, no, message);
    }
    Ok(Read {
        corpus: Corpus {
            records,
            theorems,
            scopes,
        },
        report,
        whole,
    })
}

/// Read the corpus, check what is checked of the corpus as a whole, and give
/// what was read to `then`; or the outcome where nothing can be read.
#[allow(clippy::type_complexity)]
fn prepared<T>(
    source: &dyn Source,
    then: impl FnOnce(&mut Report, &mut Checking<'_>) -> T,
) -> Result<(Report, (usize, usize, usize, usize), T), Outcome> {
    let read = read_corpus(source)?;
    prepared_in(&read.corpus, read.report, then)
}

/// `prepared` of a corpus already read, with what reading it found.
#[allow(clippy::type_complexity)]
fn prepared_in<T>(
    corpus: &Corpus,
    mut report: Report,
    then: impl FnOnce(&mut Report, &mut Checking<'_>) -> T,
) -> Result<(Report, (usize, usize, usize, usize), T), Outcome> {
    let Corpus {
        records,
        theorems,
        scopes,
    } = corpus;
    let mut methods: IndexMap<String, usize> = IndexMap::new();
    // A method written in words, `both directions`, names its record with
    // a hyphen between them, as every record's name is one word.
    for (i, r) in records.iter().enumerate() {
        if r.kind == RecordKind::Method {
            methods.insert(r.name.replace('-', " "), i);
        }
    }
    database::check_database(&mut report, records);
    database::check_notation(&mut report, records);
    let words = structure::declared_words(records);

    let items = index(records, theorems);
    let mut seen: IndexMap<String, usize> = IndexMap::new();
    for thm in theorems {
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
    // The library files a proof may import: those whose items it may cite.
    let library: IndexSet<String> = records
        .iter()
        .filter(|r| r.kind.is_item())
        .map(|r| r.module().to_string())
        .collect();
    structure::check_imports(&mut report, theorems, scopes, &items, &library);

    let counts = counts_of(corpus);

    // Nothing is read without the grammar, so a notation it cannot be built
    // from ends the run here.
    let grammar = match Grammar::load(records) {
        Ok(g) => g,
        Err(p) => {
            report.problems.push(p);
            return Err(summary(report, counts));
        }
    };
    let env = Env {
        g: &grammar,
        scopes,
    };
    structure::check_function_names(&mut report, theorems, scopes, &grammar.functions);
    // Which names a file writes is read off its formulas' tokens, which the
    // grammar lexes.
    structure::check_definitions(&mut report, theorems, scopes, &grammar);
    structure::check_function_imports(&mut report, theorems, scopes, &grammar);
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
        let parts = crate::sorts::record_formulas(r);
        structure::check_ranges(
            &mut report,
            &r.path,
            &r.ranges,
            &lets,
            &crate::sorts::written_tokens(&parts, &grammar),
            env,
            &record_sorts[&i],
        );
    }
    database::check_statements(&mut report, records, env, &record_sorts);
    database::check_unsorted(&mut report, records, env, &record_sorts);
    database::check_symbols(&mut report, records);
    let defined = formulas::defined_words(&mut report, records, env, &record_sorts);
    let operations = formulas::operations(records);

    // Each theorem's lines, read once, after every statement it may cite.
    for thm in theorems {
        statements.insert(thm.qualified(), infer::read_statement(thm, env, &mut store));
    }
    let ctx = Context::new(&env.g.notations, records);
    let mut known: Vec<Known> = Vec::new();
    let mut clashes: Vec<Vec<infer::Clash>> = Vec::new();
    for thm in theorems {
        let reader = formulas::read_with_citations(thm, env, &statements, &mut store);
        known.push(Known::new(thm, env, settled(&reader, &store), &ctx));
        clashes.push(reader.clashes);
    }
    let proved = known
        .iter()
        .map(|k| {
            let at = Proved {
                thm: k.thm,
                sorts: std::borrow::Cow::Borrowed(&k.sorts),
            };
            (k.thm.qualified(), at)
        })
        .collect();
    let library = Library::new(records, record_sorts.clone(), proved, env);

    formulas::check_item_clashes(&mut report, &statements, &items);
    let methods: IndexMap<String, &Record> = methods
        .iter()
        .map(|(name, &i)| (name.clone(), &records[i]))
        .collect();
    let mut checking = Checking {
        theorems,
        known: &known,
        clashes: &clashes,
        env,
        library: &library,
        scopes,
        words: &words,
        defined: &defined,
        operations: &operations,
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
    check_passes(report, c, thm, k, clashes);
    formulas::check_ends_numbered(report, thm, k, c.library);
    check_requires_work(report, c, thm, k, clashes);
}

/// A requires line does work (`SYNTAX.md`, requires; `DATABASE.md`, a named
/// thing doing no work is an error): with it taken away, the checks find
/// something wrong with its step that they do not find with it there, a
/// fact the step's method or citation needs, or one a requires line below
/// rests on, left unsaid. One rule for every method: the step is checked as
/// a theorem of that one step, under what `k` knows of the whole theorem,
/// once as written and once with each requires line taken away, so that
/// what the one step's theorem lacks is found alike both times. A step the
/// checks already find something wrong with is asked nothing here.
fn check_requires_work(
    report: &mut Report,
    c: &Checking<'_>,
    thm: &Theorem,
    k: &Known<'_>,
    clashes: &[infer::Clash],
) {
    for (i, step) in thm.steps.iter().enumerate() {
        if step.requires.is_empty() {
            continue;
        }
        let end = thm.steps.get(i + 1).map_or(usize::MAX, |next| next.line);
        let reported = report
            .problems
            .iter()
            .any(|p| p.path == thm.path && (step.line..end).contains(&p.line.line));
        if reported {
            continue;
        }
        let found = found_alone(c, thm, step, k, clashes);
        for (r, req) in step.requires.iter().enumerate() {
            let mut lighter = step.clone();
            lighter.requires.remove(r);
            let without = found_alone(c, thm, &lighter, k, clashes);
            if without.is_subset(&found) {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of step {} says {}, and the step neither uses nor asks for it",
                        step.number,
                        str::trim(req.fact.text())
                    ),
                );
            }
        }
    }
}

/// What the checks find of `step` checked as a theorem of that one step.
fn found_alone(
    c: &Checking<'_>,
    thm: &Theorem,
    step: &Step,
    k: &Known<'_>,
    clashes: &[infer::Clash],
) -> BTreeSet<String> {
    let alone = Theorem {
        steps: vec![step.clone()],
        ..thm.clone()
    };
    let mut seen = Report::default();
    check_passes(&mut seen, c, &alone, k, clashes);
    // What the step owes where it ends a part of a block or the proof is
    // read in the whole theorem, which the one step's theorem has not.
    formulas::ends_unnumbered(&mut seen, thm, step, k, c.library);
    seen.problems.iter().map(|p| p.to_string()).collect()
}

/// The checks of one theorem, each asked once.
fn check_passes(
    report: &mut Report,
    c: &Checking<'_>,
    thm: &Theorem,
    k: &Known<'_>,
    clashes: &[infer::Clash],
) {
    let (env, library, scopes) = (c.env, c.library, c.scopes);
    formulas::check_formulas(report, thm, env, k);
    formulas::check_letters_introduced(report, thm, env, k);
    formulas::check_statement_names(report, thm, env, k);
    formulas::check_structure_parts(report, thm, k, &library.targets);
    structure::check_defined_below(report, thm, scopes, env.g);
    formulas::check_clashes(report, thm, clashes);
    formulas::check_contradiction(report, thm, env, k);
    formulas::check_contradicting(report, thm, env, k);
    formulas::check_impossible(report, thm, k, &library.targets);
    formulas::check_decided_words(report, thm, k, c.defined, c.operations);
    formulas::check_chain_congruences(report, thm);
    formulas::check_congruence_integers(report, thm, k, &library.targets);
    formulas::check_both_directions(report, thm, k);
    formulas::check_block_ends(report, thm, k);
    formulas::check_claimed_cases(report, thm, k);
    formulas::check_cases_cited(report, thm, k);
    formulas::check_closed_arithmetic(report, thm, k);
    formulas::check_closed_by_arithmetic(report, thm, k);
    let targets = &library.targets;
    formulas::check_arithmetic_holds(report, thm, k, targets);
    formulas::check_algebra_holds(report, thm, k, targets);
    formulas::check_inequalities_holds(report, thm, k, targets);
    formulas::check_inequality_rows(report, thm, k, targets);
    formulas::check_requires_manipulations(report, thm, k, targets);
    formulas::check_transitivity(report, thm, k, targets);
    formulas::check_antisymmetry(report, thm, k, targets);
    formulas::check_membership_holds(report, thm, k, targets);
    formulas::check_inspection_holds(report, thm, k, targets);
    formulas::check_membership_claims(report, thm, k);
    citations::check_hypotheses(report, thm, library, k);
    citations::check_conclusion(report, thm, library, k);
    citations::check_subjects(report, thm, library, k);
    citations::check_joins(report, thm, library, k);
    citations::check_substitutes(report, thm, library, k);
    citations::check_function_types(report, thm, library, k, scopes);
    formulas::check_define_citation(report, thm, library, k, scopes);
    formulas::check_define_names(report, thm, k, scopes);
    citations::check_obtained(report, thm, library, k);
    citations::check_obtained_claims(report, thm, library, k);
    citations::check_requires(report, thm, library, k);
    citations::check_kinds(report, thm, library, k);
    formulas::check_kind_methods(report, thm, k, &library.targets);
    citations::check_surplus(report, thm, library, k, scopes);
    citations::check_defined_types(report, thm, library, k, scopes);
    // After the surplus of what a requires line cites, which says more of
    // the line than that its term is not the step's.
    formulas::check_requires_combined(report, thm, k, targets);
    citations::check_repeated(report, thm, library, k);
    citations::check_from_lines(report, thm, library, k, scopes);
    citations::check_exhibited(report, thm, library, k);
    citations::check_instantiated(report, thm, library, k);
    citations::check_instance_claimed(report, thm, library, k);
    citations::check_define_domains(report, thm, library, k, scopes);
    formulas::check_method_cites_used(report, thm, library, k, scopes);
    formulas::check_chain_links(report, thm, library, k, scopes);
    structure::check_last_step(report, thm, k);
    structure::check_steps_used(report, thm);
    structure::check_readings(report, thm);
    database::check_introductions(report, thm, env, k);
    formulas::check_recursions(report, thm, env, k);
    structure::check_sorts(report, thm, k);
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
        &crate::sorts::theorem_tokens(thm, env.g),
        env,
        &k.sorts,
    );
    structure::check_capture(report, thm, k);
    structure::check_run_together(report, thm, c.words, c.env.g);
    structure::check_numbering(report, thm);
    structure::check_blocks(report, thm, c.methods, k);
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
    Outcome {
        printed: out,
        complained: String::new(),
        status: if problems.is_empty() { 0 } else { 1 },
    }
}
