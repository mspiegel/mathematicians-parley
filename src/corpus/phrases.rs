//! The records a define of a phrase stands for.
//!
//! `define triangular-number: n is a triangular number means …` gives a new
//! way to say something, which the reader learns from a notation record, and
//! an item another file cites, which is a definition record. So each define
//! of a phrase is made into the two records a database file would write for
//! it: a notation whose patterns are the phrase and its negation, and a
//! definition whose statement is the phrase and its meaning. The notation
//! says what its slots take only once the meaning is read
//! (`sorts::settle_phrases`); until then each slot takes a sort of its own
//! left open.

use indexmap::IndexMap;

use super::define::{define_parts, DefineParts, Phrase};
use super::module_of;
use super::proof::{DefineLine, FileScope};
use super::records::{Record, RecordKind};
use crate::outcome::Built;

/// A define of a phrase as the records are made from: the define, what it
/// says, and the `reads` line under it.
pub struct PhraseDefine<'s> {
    pub line: &'s DefineLine,
    pub said: Phrase,
    pub reads: Option<String>,
}

/// Every define of a phrase the files write, read into its parts. A define
/// that does not read is the file reader's to report, and it stops there.
pub fn phrase_defines(scopes: &[FileScope]) -> Vec<PhraseDefine<'_>> {
    let mut out = Vec::new();
    for scope in scopes {
        for d in &scope.phrases {
            let Built(DefineParts::Phrase(said)) = define_parts(&d.text) else {
                continue;
            };
            let reads = scope.readings.get(&d.label).map(|(r, _)| r.clone());
            out.push(PhraseDefine {
                line: d,
                said,
                reads,
            });
        }
    }
    out
}

/// The name of the notation a phrase's define makes: its item's full name,
/// `stdlib/calculus/upper-bound`, which no notation of the database has,
/// since theirs are one word.
pub fn notation_name(d: &DefineLine, said: &Phrase) -> String {
    format!("{}/{}", module_of(&d.path), said.name)
}

/// The `sort` line of a phrase whose slots are left open, each a sort of
/// its own: `α, β → formula`.
pub fn open_sort(said: &Phrase) -> String {
    let vars: Vec<String> = ['α', 'β', 'γ']
        .iter()
        .take(said.slots().len())
        .map(|c| c.to_string())
        .collect();
    format!("{} → formula", vars.join(", "))
}

/// The level a phrase's notation stands at: a word predicate's, or, where
/// its own words write "and" or "or", the level the precedence order leaves
/// unordered against the connectives, so that beside them it is bracketed
/// (`GRAMMAR.md`, "Precedence and nesting").
fn level(said: &Phrase) -> &'static str {
    if said.words().iter().any(|w| *w == "and" || *w == "or") {
        "betweenness"
    } else {
        "predicate"
    }
}

/// The notation record a phrase's define stands for, with `sort` as given:
/// the phrase and its negation, the second the first wrapped in `not`.
pub fn notation_record(p: &PhraseDefine<'_>, sort: &str) -> Record {
    let d = p.line;
    let mut fields = IndexMap::new();
    fields.insert(
        "pattern".to_string(),
        format!("{}  {}", p.said.pattern(), p.said.negated_pattern()),
    );
    fields.insert(
        "negates".to_string(),
        "pattern 2 is logical-not of pattern 1".to_string(),
    );
    fields.insert("sort".to_string(), sort.to_string());
    let level = level(&p.said);
    fields.insert("level".to_string(), format!("{level}, {level}"));
    if let Some(reads) = &p.reads {
        fields.insert("reads".to_string(), reads.clone());
    }
    made(RecordKind::Notation, notation_name(d, &p.said), fields, d)
}

/// The definition record a phrase's define stands for: an item of its
/// file's module, cited `def:`, whose statement is the phrase and its meaning and whose set.mm lemma is
/// `biid`. The meaning is bracketed, since it may be any statement and `↔`
/// is unordered against some.
pub fn definition_record(p: &PhraseDefine<'_>) -> Record {
    let d = p.line;
    let mut fields = IndexMap::new();
    // The phrase is written out as its meaning wherever it stands, so the
    // two sides are one formula, as for the database's definitions whose
    // notation's target is the formula they define.
    fields.insert(
        "metamath".to_string(),
        "biid, since the phrase is written out as its meaning".to_string(),
    );
    fields.insert("target".to_string(), "biid".to_string());
    if let Some(reads) = &p.reads {
        fields.insert("reads".to_string(), reads.clone());
    }
    let mut record = made(RecordKind::Definition, p.said.name.clone(), fields, d);
    record.conclusions = vec![(
        format!("{} ↔ ({})", p.said.written(), p.said.meaning),
        d.line,
    )];
    record
}

/// Add to the records the two each define of a phrase stands for, each slot
/// taking a sort of its own until the meaning is read. A phrase whose
/// pattern, or its negation's, another notation already writes gets no
/// notation, so that it changes how nothing else reads; the checker says why
/// (`structure::check_phrases`).
pub fn add_phrase_records(records: &mut Vec<Record>, scopes: &[FileScope]) {
    let mut written: Vec<String> = records
        .iter()
        .filter(|r| r.kind == RecordKind::Notation)
        .flat_map(|r| patterns_written(r.field_or_empty("pattern")))
        .collect();
    for p in phrase_defines(scopes) {
        let (said, denied) = (p.said.pattern(), p.said.negated_pattern());
        if !written.contains(&said) && !written.contains(&denied) {
            records.push(notation_record(&p, &open_sort(&p.said)));
            written.push(said);
            written.push(denied);
        }
        records.push(definition_record(&p));
    }
}

/// The patterns a notation record's `pattern` field writes, two spaces or
/// more apart.
fn patterns_written(field: &str) -> Vec<String> {
    field
        .split("  ")
        .map(str::trim)
        .filter(|p| !p.is_empty())
        .map(String::from)
        .collect()
}

/// A record made from the define `d`, at its line. Neither a notation nor a
/// definition is ever mundane.
fn made(
    kind: RecordKind,
    name: String,
    fields: IndexMap<String, String>,
    d: &DefineLine,
) -> Record {
    let lines = fields.keys().map(|k| (k.clone(), d.line)).collect();
    Record {
        kind,
        mundane: false,
        name,
        fields,
        hypotheses: Vec::new(),
        ranges: Vec::new(),
        conclusions: Vec::new(),
        repeats: Vec::new(),
        lines,
        line: d.line,
        path: d.path.clone(),
        phrase: Some(d.label.clone()),
    }
}
