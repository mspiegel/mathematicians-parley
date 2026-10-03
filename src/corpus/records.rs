//! Records of `corpus/db/*.records` and `corpus/stdlib/*.records`.

use indexmap::IndexMap;

use super::lines::read_lines;
use super::proof::{Hypothesis, Intro, Range};
use super::{full, module_of};
use crate::outcome::{Checked, Problem};
use crate::regex;
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

    /// Whether a record of this kind may be marked `mundane`: an item, or a
    /// method, which a proof may take for granted. A notation and the
    /// precedence table are never cited, so nothing takes them for granted.
    pub fn may_be_mundane(self) -> bool {
        self.is_item() || self == RecordKind::Method
    }
}

impl std::fmt::Display for RecordKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The fields each kind of record may carry, as the header of each records
/// file describes them. A field outside its kind's list is refused: the tools
/// read fields by name, so a misspelt `target` is not a target, and the item
/// it belongs to would be taken as stated wherever it is cited. A precedence
/// record is not listed, because its fields are the levels it declares.
pub fn allowed_fields(kind: RecordKind) -> Option<&'static [&'static str]> {
    FIELDS
        .iter()
        .find(|(k, _)| *k == kind)
        .map(|(_, fields)| *fields)
}

pub const FIELDS: [(RecordKind, &[&str]); 5] = [
    (
        RecordKind::Notation,
        &[
            "pattern", "sort", "level", "assoc", "commutes", "negates", "spells",
            "places", "nests", "bounds", "joins", "wraps", "fills", "binds", "reads",
            "target", "metamath", "note",
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
            "metamath",
            "note",
        ],
    ),
    (
        RecordKind::Definition,
        &[
            "sort", "builds", "reads", "metamath", "target", "open", "symbol",
            "defines", "note",
        ],
    ),
    (RecordKind::Axiom, &["metamath", "target", "open", "note"]),
    (RecordKind::Theorem, &["metamath", "target", "open", "note"]),
];

/// One record of a database file.
#[derive(Clone, Debug)]
pub struct Record {
    pub kind: RecordKind,
    /// Whether its header opens with `mundane`: a human proof takes it for
    /// granted, using it without naming it.
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
}

impl Record {
    pub fn module(&self) -> &str {
        module_of(&self.path)
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
    /// `builds`, and `library_functions` refuses one that does not.
    pub fn is_function(&self) -> bool {
        self.kind == RecordKind::Definition && self.fields.contains_key("sort")
    }
}

regex!(RECORD_NAME, super::NAME);
regex!(LABEL_AT_END, r"\(([A-Z]+[0-9]*)\)$");

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
                             `mundane axiom`, `mundane theorem`, `mundane definition` \
                             or `mundane method` before its name"
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
                    format!(
                        "mundane {kind}: a {kind} is never cited, so nothing takes it \
                         for granted"
                    ),
                ));
            }
            if !full(&RECORD_NAME, name) {
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
                        if let Some(c) = LABEL_AT_END.captures(&line.text) {
                            h.label = Some(c[1].to_string());
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
            let label = LABEL_AT_END.captures(&line.text).map(|c| c[1].to_string());
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
