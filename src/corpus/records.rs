//! Records of `corpus/db/*.records` and `corpus/stdlib/*.records`.

use std::fmt;
use std::fmt::{Display, Formatter};

use indexmap::IndexMap;

use super::lines::read_lines;
use super::module_of;
use super::proof::{Hypothesis, Intro, Range};
use super::skeleton::{is_name, label_at_end};
use crate::formula::page::Written;
use crate::outcome::{Checked, Problem};
use crate::text::repr;

/// What a record is.
///
/// An item of the library is one of three kinds, and the kind says what a
/// reader is to take it to be (`DATABASE.md`, "Record kinds"): an axiom is
/// given, a theorem is proved, and a definition is where a word or a symbol
/// gets its meaning. Whether a proof takes the item for granted is a mark
/// beside the kind, `Record::mundane`, and not a kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RecordKind {
    Notation,
    Method,
    Axiom,
    Theorem,
    Definition,
    Precedence,
}

impl RecordKind {
    pub fn parse(word: &str) -> Option<RecordKind> {
        Some(match word {
            "notation" => RecordKind::Notation,
            "method" => RecordKind::Method,
            "axiom" => RecordKind::Axiom,
            "theorem" => RecordKind::Theorem,
            "definition" => RecordKind::Definition,
            "precedence" => RecordKind::Precedence,
            _ => return None,
        })
    }

    pub fn as_str(self) -> &'static str {
        match self {
            RecordKind::Notation => "notation",
            RecordKind::Method => "method",
            RecordKind::Axiom => "axiom",
            RecordKind::Theorem => "theorem",
            RecordKind::Definition => "definition",
            RecordKind::Precedence => "precedence",
        }
    }

    /// An item a proof may cite: every kind of the library's.
    pub fn is_item(self) -> bool {
        self.is_fact() || self.unfolds()
    }

    /// An axiom or a theorem: a statement a step applies.
    pub fn is_fact(self) -> bool {
        matches!(self, RecordKind::Axiom | RecordKind::Theorem)
    }

    /// A definition: what a step citing it unfolds.
    pub fn unfolds(self) -> bool {
        self == RecordKind::Definition
    }

    /// Whether a record of this kind may be marked `mundane`: only a theorem,
    /// one that is there for the prover and that no textbook would cite. An
    /// axiom and a definition give meaning, and a pedantic textbook cites
    /// them; a method is named on the line that uses it; a notation and the
    /// precedence table are never cited at all.
    pub fn may_be_mundane(self) -> bool {
        self == RecordKind::Theorem
    }
}

impl Display for RecordKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The fields each kind of record may carry, as the header of each records
/// file describes them. A field outside its kind's list is refused: the tools
/// read fields by name, so a misspelt `metamath-proof` is not one, and the item
/// it belongs to would stop the build wherever it is cited. A precedence
/// record is not listed, because its fields are the levels it declares.
pub fn allowed_fields(kind: RecordKind) -> Option<&'static [&'static str]> {
    FIELDS
        .iter()
        .find(|(k, _)| *k == kind)
        .map(|(_, fields)| *fields)
}

/// The set.mm syntax constructor a notation is, `wceq` for `=`: the checker
/// sorts notations by its first word (`matching`). A notation's field only.
pub const METAMATH_SYNTAX: &str = "metamath-syntax";
/// What the Metamath build proves an item or a method's step with
/// (`Provided`).
pub const METAMATH_PROOF: &str = "metamath-proof";
/// The set.mm template the Metamath build writes a notation, or a library
/// function applied, with.
pub const METAMATH_BUILDS: &str = "metamath-builds";
/// What the Lean build proves an item with (`Provided`).
pub const LEAN_PROOF: &str = "lean-proof";
/// How each `then` sentence of an item is read off its lemma's conclusion
/// (`LemmaReading`).
pub const METAMATH_READS: &str = "metamath-reads";
/// The item's hypotheses in the order its lemma asks for them.
pub const METAMATH_HYPOTHESES: &str = "metamath-hypotheses";

/// Which side of a lemma's `↔` a sentence is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Side {
    Left,
    Right,
}

/// How one `then` sentence of an item is read off the conclusion of the
/// lemma its `metamath-proof` names (`DATABASE.md`, "How the lemma meets the
/// item"): the conclusion as it stands, a side of its `↔`, a part of its
/// "and", or the conclusion turned. `right side part 2` is the second part of
/// the right side.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LemmaReading {
    /// The side of the lemma's `↔` the sentence is; None for the whole.
    pub side: Option<Side>,
    /// The part of the lemma's "and" the sentence is, counted from 0; None
    /// for the whole.
    pub part: Option<usize>,
    /// Whether the lemma writes the equation, or the `↔`, the other way
    /// round.
    pub turned: bool,
    /// Whether the lemma writes each product of two factors the other way
    /// round, k·d where the page writes d·k.
    pub factors_swapped: bool,
    /// Whether the sentence is a "there is" whose witness the target's
    /// `with` names, and each lemma gives one part of what it says of the
    /// witness: `completeness` at c := sup S, from suprcl, suprub and
    /// suprleub.
    pub witness: bool,
}

impl LemmaReading {
    /// One entry of `metamath-reads`; None where it says none of the forms.
    pub fn read(entry: &str) -> Option<LemmaReading> {
        let words: Vec<&str> = entry.split_whitespace().collect();
        if words == ["as", "stated"] {
            return Some(LemmaReading::default());
        }
        if words == ["witness"] {
            return Some(LemmaReading {
                witness: true,
                ..LemmaReading::default()
            });
        }
        let mut out = LemmaReading::default();
        let mut rest = words.as_slice();
        if let [which @ ("left" | "right"), "side", more @ ..] = rest {
            out.side = Some(if *which == "left" {
                Side::Left
            } else {
                Side::Right
            });
            rest = more;
        }
        if let ["part", n, more @ ..] = rest {
            let n: usize = n.parse().ok().filter(|n| *n >= 1)?;
            out.part = Some(n - 1);
            rest = more;
        }
        if let ["turned", more @ ..] = rest {
            out.turned = true;
            rest = more;
        }
        if let ["factors", "swapped", more @ ..] = rest {
            out.factors_swapped = true;
            rest = more;
        }
        (rest.is_empty() && out != LemmaReading::default()).then_some(out)
    }

    /// Whether the sentence read so is the next part of the same lemma as
    /// the sentence before it, read `before`, and so takes no lemma of its
    /// own: `part 2` after `part 1`.
    pub fn continues(&self, before: &LemmaReading) -> bool {
        match (self.part, before.part) {
            (Some(p), Some(q)) => p == q + 1 && self.side == before.side,
            _ => false,
        }
    }
}
/// A proof field's value for a build that has nothing to prove: the record
/// states nothing, or its two sides are one formula in that library.
pub const NOTHING_TO_PROVE: &str = "none";
/// A proof field's value for a build that cannot use the record yet.
pub const NOT_YET: &str = "not yet implemented";

/// What a record's `metamath-proof` or `lean-proof` says.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Provided<'a> {
    /// What the build cites: the library's own statement, or a bridge's
    /// full name.
    By(&'a str),
    /// A Parley proof of the standard library, by its full name,
    /// `stdlib/numbers/abs-bounds`, which the build builds and cites.
    Proof(&'a str),
    /// `none`: the build has nothing to prove.
    Nothing,
    /// `not yet implemented`: the build cannot use the record yet.
    NotYet,
}

/// Where the full name of a Parley proof of the standard library begins.
pub const STDLIB: &str = "stdlib/";

impl<'a> Provided<'a> {
    /// A proof field's value read.
    pub fn read(value: &'a str) -> Provided<'a> {
        match value.trim() {
            NOTHING_TO_PROVE => Provided::Nothing,
            NOT_YET => Provided::NotYet,
            other
                if other.starts_with(STDLIB)
                    && !other.contains(char::is_whitespace) =>
            {
                Provided::Proof(other)
            }
            other => Provided::By(other),
        }
    }

    /// What the build cites, where it cites the library or a bridge.
    pub fn by(self) -> Option<&'a str> {
        match self {
            Provided::By(v) => Some(v),
            _ => None,
        }
    }

    /// The Parley proof's full name, where the build proves it by one.
    pub fn proof(self) -> Option<&'a str> {
        match self {
            Provided::Proof(v) => Some(v),
            _ => None,
        }
    }
}
/// The Lean template the Lean build writes a notation, or a library
/// function applied, with.
pub const LEAN_BUILDS: &str = "lean-builds";

pub const FIELDS: [(RecordKind, &[&str]); 5] = [
    (
        RecordKind::Notation,
        &[
            "pattern",
            "sort",
            "level",
            "assoc",
            "commutes",
            "identity",
            "negates",
            "spells",
            "places",
            "nests",
            "bounds",
            "joins",
            "wraps",
            "fills",
            "repeats",
            "shadowed",
            "wanted",
            "instead",
            "binds",
            "reads",
            "member",
            METAMATH_BUILDS,
            METAMATH_SYNTAX,
            "decided",
            LEAN_BUILDS,
            "note",
        ],
    ),
    (
        RecordKind::Method,
        &[
            "form",
            "block",
            "parts",
            "parts-repeat",
            "part-opens",
            "checks",
            "decides",
            "hypotheses",
            "specified-in",
            METAMATH_PROOF,
            "note",
        ],
    ),
    (
        RecordKind::Definition,
        &[
            "sort",
            METAMATH_BUILDS,
            "reads",
            METAMATH_PROOF,
            METAMATH_READS,
            METAMATH_HYPOTHESES,
            "symbol",
            "defines",
            "decided",
            LEAN_PROOF,
            LEAN_BUILDS,
            "note",
        ],
    ),
    (
        RecordKind::Axiom,
        &[
            METAMATH_PROOF,
            METAMATH_READS,
            METAMATH_HYPOTHESES,
            LEAN_PROOF,
            "note",
        ],
    ),
    (
        RecordKind::Theorem,
        &[
            METAMATH_PROOF,
            METAMATH_READS,
            METAMATH_HYPOTHESES,
            LEAN_PROOF,
            "note",
        ],
    ),
];

/// One record of a database file.
#[derive(Clone, Debug)]
pub struct Record {
    pub kind: RecordKind,
    /// Whether its header opens with `mundane`: a theorem a human proof takes
    /// for granted, using it without naming it.
    pub mundane: bool,
    pub name: String,
    pub fields: IndexMap<String, String>,
    /// Each `let` or `assume`, its text without the keyword.
    pub hypotheses: Vec<Hypothesis>,
    /// Each `ε, δ range over ℝ` of its statement.
    pub ranges: Vec<Range>,
    /// Each `then`, with the line it is on.
    pub conclusions: Vec<(String, usize)>,
    /// A field said twice, and the line of the second.
    pub repeats: Vec<(String, usize)>,
    /// The line each field is first said on.
    pub lines: IndexMap<String, usize>,
    pub line: usize,
    pub path: String,
    /// The label of the define of a phrase the record is made from, where a
    /// proof file wrote it and no database file did (`corpus::phrases`).
    pub phrase: Option<String>,
    /// What the define of a phrase the record is made from says its slots
    /// are, in its `where` part: kinds, which its meaning is read with, and
    /// no hypotheses.
    pub slot_kinds: Vec<super::define::SlotKind>,
}

impl Record {
    pub fn module(&self) -> &str {
        module_of(&self.path)
    }

    /// Each `then` line's formula as written, with where.
    pub fn stated(&self) -> Vec<Written> {
        self.conclusions
            .iter()
            .map(|(text, line)| Written::new(text, &self.path, *line))
            .collect()
    }

    /// Its full name: its file's module, then its own name.
    pub fn qualified(&self) -> String {
        format!("{}/{}", self.module(), self.name)
    }

    pub fn field(&self, name: &str) -> Option<&str> {
        self.fields.get(name).map(String::as_str)
    }

    /// A field, or the empty text where the record does not say it.
    pub fn field_or_empty(&self, name: &str) -> &str {
        self.field(name).unwrap_or("")
    }

    /// What the Metamath build writes for the record: a notation's set.mm
    /// template, `metamath-builds`, and an item's or a method's proof,
    /// `metamath-proof`, where it has one; None where it says `none` or
    /// `not yet implemented`.
    pub fn metamath_target(&self) -> Option<&str> {
        match self.kind {
            RecordKind::Notation => self.field(METAMATH_BUILDS),
            _ => self.metamath_provided().and_then(Provided::by),
        }
    }

    /// How many sentences its `then` lines say together.
    pub fn sentence_count(&self) -> usize {
        self.stated().iter().map(|w| w.sentences().len()).sum()
    }

    /// How each `then` sentence is read off its lemma (`metamath-reads`),
    /// one entry to a sentence in order; each as stated where the record
    /// says nothing. Err with what is wrong where the field is not one
    /// reading to a sentence.
    pub fn metamath_reads(&self) -> Result<Vec<LemmaReading>, String> {
        let count = self.sentence_count();
        let Some(value) = self.field(METAMATH_READS) else {
            return Ok(vec![LemmaReading::default(); count]);
        };
        let mut out = Vec::new();
        for entry in value.split(',') {
            match LemmaReading::read(entry) {
                Some(reading) => out.push(reading),
                None => {
                    return Err(format!(
                        "{} is no reading: say `as stated`, `left side`, `right side`, `part N`, `turned`, `factors swapped` or `witness`, or a side, a part, `turned` and `factors swapped` together, in that order",
                        repr(entry.trim())
                    ))
                }
            }
        }
        if out.len() != count {
            return Err(format!(
                "it gives {} readings, and the item says {count} sentences: one reading to a sentence",
                out.len()
            ));
        }
        Ok(out)
    }

    /// The labels of its hypotheses in the order its lemma asks for them
    /// (`metamath-hypotheses`); empty where the record says nothing, and the
    /// lemma asks for them in the item's order. Err with what is wrong where
    /// a label is none of the item's hypotheses, or is said twice.
    pub fn metamath_hypotheses(&self) -> Result<Vec<String>, String> {
        let Some(value) = self.field(METAMATH_HYPOTHESES) else {
            return Ok(Vec::new());
        };
        let mut out: Vec<String> = Vec::new();
        for entry in value.split(',').map(str::trim) {
            if !self
                .hypotheses
                .iter()
                .any(|h| h.label.as_deref() == Some(entry))
            {
                return Err(format!(
                    "{} is none of its hypotheses' labels",
                    repr(entry)
                ));
            }
            if out.iter().any(|o| o == entry) {
                return Err(format!("{} is said twice", repr(entry)));
            }
            out.push(entry.to_string());
        }
        Ok(out)
    }

    /// What its `metamath-proof` says; None where it has none.
    pub fn metamath_provided(&self) -> Option<Provided<'_>> {
        self.field(METAMATH_PROOF).map(Provided::read)
    }

    /// What its `lean-proof` says; None where it has none.
    pub fn lean_provided(&self) -> Option<Provided<'_>> {
        self.field(LEAN_PROOF).map(Provided::read)
    }

    /// `metamath_target`, or the empty text where the record does not say it.
    pub fn metamath_target_or_empty(&self) -> &str {
        self.metamath_target().unwrap_or("")
    }

    /// What the Lean build writes for the record: a notation's Lean template,
    /// `lean-builds`, and an item's proof, `lean-proof`, where it has one;
    /// None where it says `none` or `not yet implemented`, or names a
    /// Parley proof, which the build writes as a theorem of its own.
    pub fn lean_target(&self) -> Option<&str> {
        match self.kind {
            RecordKind::Notation => self.field(LEAN_BUILDS),
            _ => self.lean_provided().and_then(Provided::by),
        }
    }

    /// The Parley proofs its two proof fields name, each once.
    pub fn parley_proofs(&self) -> Vec<&str> {
        let mut out: Vec<&str> = Vec::new();
        for said in [self.metamath_provided(), self.lean_provided()] {
            if let Some(name) = said.and_then(Provided::proof) {
                if !out.contains(&name) {
                    out.push(name);
                }
            }
        }
        out
    }

    /// The set.mm syntax constructor a notation is, `metamath-syntax`, or
    /// the empty text where it does not say.
    pub fn syntax(&self) -> &str {
        self.field_or_empty(METAMATH_SYNTAX)
    }

    /// Its header's words before its name, as a message names the record:
    /// `mundane theorem`, `axiom`.
    pub fn header(&self) -> String {
        if self.mundane {
            format!("mundane {}", self.kind)
        } else {
            self.kind.to_string()
        }
    }

    /// Whether it declares a function a formula applies, `gcd(a, b)`: a
    /// definition with a `sort` line. Such a definition also says what it
    /// builds in set.mm, `metamath-builds`, and `library_functions` refuses
    /// one that does not.
    pub fn is_function(&self) -> bool {
        self.kind == RecordKind::Definition && self.fields.contains_key("sort")
    }
}

enum Last {
    Field(String),
    Hypothesis,
    Conclusion,
}

/// Records of a database file. A record begins at column 0; its fields are
/// indented. `let`, `assume` and `then` lines carry an item's statement.
pub fn parse_database(path: &str, text: &str) -> Checked<Vec<Record>> {
    let mut records: Vec<Record> = Vec::new();
    // A field sits at the record's field indent. Anything indented further
    // continues the field above it, which is how a long `note` is wrapped.
    let mut field_indent: Option<usize> = None;
    let mut last: Option<Last> = None;
    for line in read_lines(text) {
        // The first word, and the rest after it: a record's kind and name, or
        // a field's key and value.
        let said = line.text.trim();
        let (word, rest) = said
            .split_once(char::is_whitespace)
            .map_or((said, ""), |(w, r)| (w, r.trim()));
        if line.indent == 0 {
            // `mundane` is a mark that stands before the kind, and is no kind
            // of its own.
            let mundane = word == "mundane";
            let (word, name) = if mundane {
                rest.split_once(char::is_whitespace)
                    .map_or((rest, ""), |(w, r)| (w, r.trim()))
            } else {
                (word, rest)
            };
            let Some(kind) = RecordKind::parse(word) else {
                return Err(Problem::new(
                    path,
                    line.no,
                    if mundane && name.is_empty() {
                        format!(
                            "mundane {word} has no kind: a record's header says \
                             `mundane theorem` before its name"
                        )
                    } else {
                        format!("unknown record kind {}", repr(word))
                    },
                ));
            };
            if mundane && !kind.may_be_mundane() {
                return Err(Problem::new(
                    path,
                    line.no,
                    match kind {
                        RecordKind::Axiom | RecordKind::Definition => format!(
                            "mundane {kind}: an axiom or a definition gives meaning, and a \
                             pedantic textbook cites it, so it is never mundane; only a \
                             theorem is"
                        ),
                        RecordKind::Method => format!(
                            "mundane {kind}: a method is named on the line that uses it, \
                             so it is never mundane; only a theorem is"
                        ),
                        _ => format!(
                            "mundane {kind}: a {kind} is never cited, so nothing takes it \
                             for granted"
                        ),
                    },
                ));
            }
            if !is_name(name) {
                return Err(Problem::new(
                    path,
                    line.no,
                    "record has no well-formed name",
                ));
            }
            records.push(Record {
                kind,
                mundane,
                name: name.to_string(),
                fields: IndexMap::new(),
                hypotheses: Vec::new(),
                ranges: Vec::new(),
                conclusions: Vec::new(),
                repeats: Vec::new(),
                lines: IndexMap::new(),
                line: line.no,
                path: path.to_string(),
                phrase: None,
                slot_kinds: Vec::new(),
            });
            field_indent = None;
            last = None;
            continue;
        }
        let Some(cur) = records.last_mut() else {
            return Err(Problem::new(path, line.no, "field outside any record"));
        };
        match field_indent {
            None => field_indent = Some(line.indent),
            Some(indent) if line.indent > indent => {
                match &last {
                    None => {
                        return Err(Problem::new(
                            path,
                            line.no,
                            "continuation before any field",
                        ))
                    }
                    Some(Last::Field(key)) => {
                        let before = cur.fields.get(key).cloned().unwrap_or_default();
                        let joined = format!("{before} {}", line.text);
                        cur.fields
                            .insert(key.clone(), str::trim(&joined).to_string());
                    }
                    Some(Last::Hypothesis) => {
                        let h = cur.hypotheses.last_mut().unwrap();
                        let joined = format!("{} {}", h.text, line.text);
                        h.text = str::trim(&joined).to_string();
                        // A wrapped hypothesis carries its label at the end
                        // of its last line.
                        if let Some(label) = label_at_end(&line.text) {
                            h.label = Some(label.to_string());
                        }
                    }
                    Some(Last::Conclusion) => {
                        let c = cur.conclusions.last_mut().unwrap();
                        let joined = format!("{} {}", c.0, line.text);
                        c.0 = str::trim(&joined).to_string();
                    }
                }
                continue;
            }
            Some(_) => {}
        }
        let (key, value) = (word, rest);
        if let Some(range) = Range::read(said, line.no) {
            last = None;
            cur.ranges.push(range);
        } else if key == "let" || key == "assume" {
            last = Some(Last::Hypothesis);
            let label = label_at_end(&line.text).map(String::from);
            cur.hypotheses.push(Hypothesis {
                kind: if key == "let" {
                    Intro::Let
                } else {
                    Intro::Assume
                },
                text: value.to_string(),
                label,
                line: line.no,
            });
        } else if key == "then" {
            last = Some(Last::Conclusion);
            cur.conclusions.push((value.to_string(), line.no));
        } else {
            last = Some(Last::Field(key.to_string()));
            // A field said twice is joined to the first, which is what a
            // wrapped line does and is not what a second field line means.
            // The join is kept so the record still reads, and the repeat is
            // recorded for the checker to refuse.
            if cur.fields.contains_key(key) {
                cur.repeats.push((key.to_string(), line.no));
            }
            cur.lines.entry(key.to_string()).or_insert(line.no);
            let joined = match cur.fields.get(key) {
                Some(before) => format!("{before} {value}"),
                None => value.to_string(),
            };
            cur.fields.insert(key.to_string(), joined);
        }
    }
    Ok(records)
}
