//! Proof skeletons: the `.proof` files.

use std::fmt;
use std::sync::Arc;

use indexmap::{IndexMap, IndexSet};

use super::define::{define_parts, naming, DefineParts, Naming, Param, RuleText};
use super::lines::{read_lines, Line};
use super::records::{Record, RecordKind};
use super::skeleton::{
    self, cut_reason, is_justification, item_kind, Place, Slots, Source,
};
use super::values::Values;
use super::{cited_name, in_stdlib, module_of};
use crate::formula::page::Written;
use crate::outcome::{Built, Checked, Problem};
use crate::text::{prefix, repr};

/// How a line introduces what it introduces.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Intro {
    Let,
    Assume,
    Suppose,
}

impl Intro {
    pub fn parse(word: &str) -> Option<Intro> {
        Some(match word {
            "let" => Intro::Let,
            "assume" => Intro::Assume,
            "suppose" => Intro::Suppose,
            _ => return None,
        })
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Intro::Let => "let",
            Intro::Assume => "assume",
            Intro::Suppose => "suppose",
        }
    }
}

impl fmt::Display for Intro {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A `let` or `assume` line of a statement.
///
/// In a record the text is what follows the keyword; in a proof file it is
/// the whole line, keyword and label included, as written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hypothesis {
    pub kind: Intro,
    pub text: String,
    pub label: Option<String>,
    pub line: usize,
}

impl Hypothesis {
    /// What the line says after its keyword, its label taken off: the
    /// formula of an `assume`, the introduction of a `let`. `path` is the
    /// file the line is in.
    pub fn body(&self, path: &str) -> Written {
        Written::new(body_text(self.kind, &self.text), path, self.line)
    }
}

impl Opener {
    /// What the line says after its keyword, its label taken off
    /// (`Hypothesis::body`).
    pub fn body(&self, path: &str) -> Written {
        Written::new(body_text(self.kind, &self.text), path, self.line)
    }
}

/// A `let`, `assume` or `suppose` line after its keyword, without its label.
/// A record's hypothesis is kept without its keyword, and a proof file's
/// with it.
fn body_text(kind: Intro, text: &str) -> String {
    let rest = match text.strip_prefix(kind.as_str()) {
        Some(rest) if rest.starts_with(char::is_whitespace) => rest,
        _ => text,
    };
    str::trim(&crate::sorts::unlabel(rest)).to_string()
}

/// A statement's `ε, δ range over ℝ`: the set each of those letters belongs
/// to wherever a quantifier in the theorem writes a bound in place of the
/// set, "for all ε > 0". It introduces nothing and is not a hypothesis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Range {
    pub names: Vec<String>,
    pub set: String,
    /// The line as written, for a restatement to copy.
    pub text: String,
    pub line: usize,
}

impl Range {
    /// The line read as a range (`skeleton::range_line`), or None where it
    /// is some other line.
    pub fn read(text: &str, line: usize) -> Option<Range> {
        let said = skeleton::range_line(text)?;
        Some(Range {
            names: said.letters.iter().map(|l| l.to_string()).collect(),
            set: said.set.to_string(),
            text: text.to_string(),
            line,
        })
    }
}

/// A line opening a block: `suppose`, `let` or `assume`, with its label and
/// the part of the block it opens, where the block has parts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Opener {
    pub kind: Intro,
    pub text: String,
    pub label: String,
    pub line: usize,
    pub part: Option<usize>,
    /// The line says `, which is the claim`: a case whose assumption is what
    /// the block claims, and which has no steps. The words are not in `text`.
    pub is_claim: bool,
    /// The line says `step N is true for k, the induction hypothesis`: the
    /// step part of induction N assumes N's statement at k, which is what
    /// the tree of N's claim "for all k ∈ X, …" says after the comma. The
    /// line writes no formula of its own; `text` holds its words.
    pub is_hypothesis: bool,
    /// The letter the induction hypothesis says it is for, the k of `true
    /// for k`; None for any other line.
    pub hypothesis_for: Option<String>,
}

/// A `define` or naming `let` line as written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefineLine {
    pub text: String,
    pub label: String,
    /// The file the line is written in.
    pub path: String,
    pub line: usize,
    /// For a let that says what kind of number its name is, the line under
    /// it giving the reason the term it names is one.
    pub reason: Option<Reason>,
}

/// The reason under a let that says a kind of number: a method or an item,
/// as a requires line's reason is written, and the line it is on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reason {
    /// The reason as written, for a message.
    pub how: String,
    pub line: usize,
    /// The reason as the skeleton reader cut it, as a requires line's is
    /// (`Requires::by`).
    pub by: Checked<Justification>,
}

impl Reason {
    /// The item the reason heads with, as a requires line's
    /// (`Requires::cited_item`).
    pub fn cited_item(&self) -> Option<(String, ItemKind)> {
        match &self.by {
            Ok(by) => by.head_item(),
            Err(_) => None,
        }
    }

    /// The lines and labels its `from` slot names, as a requires line's
    /// (`Requires::lines`).
    pub fn lines(&self) -> &[String] {
        match &self.by {
            Ok(by) => &by.from,
            Err(_) => &[],
        }
    }

    /// The values it gives what it cites, as a requires line's
    /// (`Requires::values`).
    pub fn values(&self) -> &Values {
        static NONE: Values = Values::NONE;
        match &self.by {
            Ok(by) => &by.values,
            Err(_) => &NONE,
        }
    }

    /// The reason as a requires line's, with no fact of its own written:
    /// what `fact` says it shows.
    pub fn shown(&self, fact: Written) -> Requires {
        Requires {
            fact,
            how: self.how.clone(),
            line: self.line,
            by: self.by.clone(),
        }
    }
}

/// A let that says what kind of number its name is, read with the sets the
/// notation records name a member of (`Grammar::members`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Kinded {
    pub label: String,
    pub name: String,
    /// The set its kind is the members of, as a formula writes it: ℕ.
    pub set: String,
    /// What its reason shows, the term the let names in that set, as a
    /// requires line says it: `gcd(s, w) ∈ ℕ`.
    pub shown: Requires,
}

impl DefineLine {
    /// A part of the line that is formula text, its rule or a domain, as
    /// the skeleton reader cut it out (`define_parts`).
    pub fn formula(&self, part: &str) -> Written {
        Written::new(part, &self.path, self.line)
    }

    /// A rule of the line, one term or a term by cases, as the formula it
    /// is: a rule by cases is made from each case's value and condition.
    pub fn rule(&self, rule: &RuleText) -> Written {
        rule.written(&self.path, self.line)
    }

    /// The set an argument of the line runs over, as the formula it is:
    /// the set written, or for `X ⊆ A` the parts of A, made from A.
    pub fn domain(&self, p: &Param) -> Written {
        p.domain_written(&self.path, self.line)
    }

    /// The let read with its kind of number, where it says one; None where
    /// it says none. A kind no record names a member of is a defect.
    pub fn kinded(
        &self,
        path: &str,
        members: &IndexMap<String, String>,
    ) -> Checked<Option<Kinded>> {
        let Built(DefineParts::One(one)) = define_parts(&self.text) else {
            return Ok(None);
        };
        let (Some(kind), Some(reason)) = (&one.kind, &self.reason) else {
            return Ok(None);
        };
        let Some(set) = members.get(kind) else {
            let known: Vec<&str> = members.keys().map(String::as_str).collect();
            return Err(Problem::new(
                path,
                self.line,
                format!(
                    "let {} says its name is {}, and the kinds of number are {}",
                    self.label,
                    repr(kind),
                    known.join("; ")
                ),
            ));
        };
        Ok(Some(Kinded {
            label: self.label.clone(),
            name: one.name.clone(),
            set: set.clone(),
            shown: reason.shown(Written::member(
                self.rule(&one.body),
                Written::new(set, path, self.line),
                path,
                reason.line,
            )),
        }))
    }
}

/// An import of a define from a proof file: `import definition
/// proofs/tri/T as U (D1)`. Its label is what a line of the importing file
/// cites it by, as it cites a define of its own, and a file that never
/// writes the define out gives none.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Import {
    pub module: String,
    pub name: String,
    pub alias: String,
    pub line: usize,
    pub label: Option<String>,
}

/// An import of a library function the file applies, by its name, from the
/// library file that declares it: `import definition
/// stdlib/divisibility/gcd`. Its words are read as any item's are, and it
/// is a function because the
/// definition it names has `sort` and `builds` lines (`link_functions`). It
/// takes no `as`, since the library's name for it is the one every formula
/// reads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionImport {
    /// The kind its keyword says.
    pub kind: ItemKind,
    pub module: String,
    pub name: String,
    pub line: usize,
}

/// An import of an item a step cites by its prefix and name: a library
/// axiom, theorem or definition, marked mundane or not, or a theorem of a
/// proof file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemImport {
    /// What a citation of it writes, which its keywords say: `mun:` where
    /// they open with `mundane`, and the kind's prefix otherwise.
    pub kind: ItemKind,
    /// Its keywords as one text, which is the header of the record it names
    /// before the name: `mundane theorem`, `axiom`.
    pub said: String,
    pub module: String,
    pub name: String,
    /// The name the file cites it by: its own, or the one after `as`.
    pub alias: String,
    pub line: usize,
}

impl ItemImport {
    pub fn full(&self) -> String {
        format!("{}/{}", self.module, self.name)
    }
}

/// What each name a proof file cites stands for.
///
/// An import says where an item comes from, so a citation writes only its
/// name: `thm:prime-factor` is the item imported under that name, and a name
/// no import gives is a theorem of the citing file.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Names {
    pub module: String,
    /// Each imported item, by the name the file cites it by, with its full
    /// name. Where two imports give one name the first is kept, and the
    /// checker is what says there are two.
    pub imported: IndexMap<String, String>,
}

impl Names {
    /// The full name a citation written in the file means, `thm:x` or bare.
    /// Whether anything has that name is the caller's to ask.
    pub fn full(&self, cited: &str) -> String {
        let name = cited_name(cited);
        match self.imported.get(name) {
            Some(full) => full.clone(),
            None => format!("{}/{name}", self.module),
        }
    }
}

/// A `requires` line: the fact, and how it is justified.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Requires {
    pub fact: Written,
    /// The reason as written, for a message.
    pub how: String,
    pub line: usize,
    /// The reason as the skeleton reader cut it (`skeleton::cut_reason`):
    /// a justification as a step's, or the lines it rests on; a defect
    /// where it is neither, which the checker reports (`check_reason`).
    pub by: Checked<Justification>,
}

impl Requires {
    /// The item the reason heads with, `mun:x`, and the kind its prefix
    /// says; None for a reason that is a method or its lines, and for one
    /// the reader could not cut, which the checker reports.
    pub fn cited_item(&self) -> Option<(String, ItemKind)> {
        match &self.by {
            Ok(by) => by.head_item(),
            Err(_) => None,
        }
    }

    /// The reason, or the defect it is.
    pub fn by(&self) -> Checked<&Justification> {
        self.by.as_ref().map_err(Clone::clone)
    }

    /// The lines and labels the reason's `from` slot names, in order; none
    /// for a reason the reader could not cut, which the checker reports.
    pub fn lines(&self) -> &[String] {
        match &self.by {
            Ok(by) => &by.from,
            Err(_) => &[],
        }
    }

    /// Everything the reason cites (`Justification::refs`); none for a
    /// reason the reader could not cut.
    pub fn refs(&self) -> &[String] {
        match &self.by {
            Ok(by) => &by.refs,
            Err(_) => &[],
        }
    }

    /// Whether the reason is the method `method`.
    pub fn is(&self, method: Method) -> bool {
        self.by.as_ref().is_ok_and(|by| by.head.is(method))
    }

    /// Whether the reason names lines and nothing else, `from 8`.
    pub fn is_lines(&self) -> bool {
        self.by.as_ref().is_ok_and(|by| by.head == Head::Lines)
    }

    /// The values the reason gives what it cites; none for a reason the
    /// reader could not cut.
    pub fn values(&self) -> &Values {
        static NONE: Values = Values::NONE;
        match &self.by {
            Ok(by) => &by.values,
            Err(_) => &NONE,
        }
    }
}

/// A step's number, as the text writes it: 3.1.2.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StepNo(pub Vec<u32>);

impl StepNo {
    pub fn parent(&self) -> StepNo {
        StepNo(self.0[..self.0.len() - 1].to_vec())
    }

    pub fn prefix(&self, k: usize) -> StepNo {
        StepNo(self.0[..k.min(self.0.len())].to_vec())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn last(&self) -> u32 {
        self.0[self.0.len() - 1]
    }

    /// Parsed from a reference such as `3.1`.
    pub fn parse(text: &str) -> StepNo {
        StepNo(text.split('.').map(|x| x.parse().unwrap_or(0)).collect())
    }
}

impl fmt::Display for StepNo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, n) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(".")?;
            }
            write!(f, "{n}")?;
        }
        Ok(())
    }
}

/// A step number written as the text writes it.
pub fn fmt(number: &StepNo) -> String {
    number.to_string()
}

/// What a citation's prefix or an import's keyword says of the item it names:
/// that a proof takes it for granted, `mun:`, or otherwise its kind. Only a
/// theorem is ever taken for granted, so `mun:` names a theorem.
///
/// The elaborator reads whether a step unfolds what it cites from the
/// record, not from this (`DATABASE.md`, "Record kinds").
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ItemKind {
    Axiom,
    Theorem,
    Mundane,
    Definition,
}

pub const ITEM_KINDS: [ItemKind; 4] = [
    ItemKind::Axiom,
    ItemKind::Theorem,
    ItemKind::Mundane,
    ItemKind::Definition,
];

impl ItemKind {
    /// What a citation writes before the item's name.
    pub fn prefix(self) -> &'static str {
        match self {
            ItemKind::Axiom => "axi",
            ItemKind::Theorem => "thm",
            ItemKind::Mundane => "mun",
            ItemKind::Definition => "def",
        }
    }

    pub fn from_prefix(prefix: &str) -> Option<ItemKind> {
        ITEM_KINDS.into_iter().find(|k| k.prefix() == prefix)
    }

    /// What a citation of a library record writes: `mun:` where its header
    /// is marked mundane, and its kind's prefix otherwise.
    pub fn of_record(r: &Record) -> ItemKind {
        if r.mundane {
            return ItemKind::Mundane;
        }
        match r.kind {
            RecordKind::Axiom => ItemKind::Axiom,
            RecordKind::Definition => ItemKind::Definition,
            _ => ItemKind::Theorem,
        }
    }
}

/// The methods a justification may open with, in the order a line is tried
/// against them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Method {
    Obtain,
    Exhibit,
    Substitute,
    Instantiate,
    Algebra,
    Arithmetic,
    RealArithmetic,
    Inequalities,
    Transitivity,
    Antisymmetry,
    Membership,
    Inspection,
    Join,
    /// `join` of one line (`SYNTAX.md`): read as `join` reads it.
    Restate,
    Contradiction,
    Proof,
    Induction,
    Cases,
    BothDirections,
    Calculation,
}

pub const METHODS: [Method; 20] = [
    Method::Obtain,
    Method::Exhibit,
    Method::Substitute,
    Method::Instantiate,
    Method::Algebra,
    Method::Arithmetic,
    Method::RealArithmetic,
    Method::Inequalities,
    Method::Transitivity,
    Method::Antisymmetry,
    Method::Membership,
    Method::Inspection,
    Method::Join,
    Method::Restate,
    Method::Contradiction,
    Method::Proof,
    Method::Induction,
    Method::Cases,
    Method::BothDirections,
    Method::Calculation,
];

impl Method {
    pub fn as_str(self) -> &'static str {
        match self {
            Method::Obtain => "obtain",
            Method::Exhibit => "exhibit",
            Method::Substitute => "substitute",
            Method::Instantiate => "instantiate",
            Method::Algebra => "algebra",
            Method::Arithmetic => "arithmetic",
            Method::RealArithmetic => "real arithmetic",
            Method::Inequalities => "inequalities",
            Method::Transitivity => "transitivity",
            Method::Antisymmetry => "antisymmetry",
            Method::Membership => "membership",
            Method::Inspection => "inspection",
            Method::Join => "join",
            Method::Restate => "restate",
            Method::Contradiction => "contradiction",
            Method::Proof => "proof",
            Method::Induction => "induction",
            Method::Cases => "cases",
            Method::BothDirections => "both directions",
            Method::Calculation => "calculation",
        }
    }

    /// Whether this method opens a block of steps.
    pub fn takes_block(self) -> bool {
        matches!(
            self,
            Method::Contradiction
                | Method::Proof
                | Method::Induction
                | Method::Cases
                | Method::BothDirections
                | Method::Calculation
        )
    }
}

/// What a justification opens with.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Head {
    /// An item, with the name as the citation writes it.
    Item {
        kind: ItemKind,
        cited: String,
    },
    Method(Method),
    /// A define, cited by its label.
    Define,
    /// A requires line's reason that names lines and nothing else, `from 8`:
    /// the fact is one of them, or what they say together.
    Lines,
    /// A requires line's reason that names one manipulation of the one line
    /// it cites, `weakening, from 2.1` (`METHODS.md`, inequalities, Rows).
    Manipulation(Manipulation),
}

/// A manipulation of one relation, as a requires line names it: what a row
/// of an `inequalities` step's rows names (`RowReason`), but for the line it
/// writes out. The term `adding` and `multiplying by` write is kept as
/// written, and read where the line is checked.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Manipulation {
    Adding(String),
    Multiplying(String),
    Restate,
    Weakening,
}

impl Manipulation {
    /// The manipulation a reason opens with, and the rest of it after the
    /// words: `weakening, from 2.1` is weakening and `, from 2.1`. None for
    /// a reason that opens otherwise.
    pub fn opening(reason: &str) -> Option<(Manipulation, &str)> {
        let reason = str::trim(reason);
        // `algebra, from L` is the method, which rewrites an equation's or a
        // disequality's sides itself.
        for (word, made) in [
            ("restate", Manipulation::Restate),
            ("weakening", Manipulation::Weakening),
        ] {
            if let Some(rest) = reason.strip_prefix(word) {
                if rest.is_empty() || rest.starts_with(',') {
                    return Some((made, rest));
                }
            }
        }
        for word in ["adding ", "multiplying by "] {
            let Some(rest) = reason.strip_prefix(word) else {
                continue;
            };
            let (term, after) = match rest.find(", from") {
                Some(at) => (&rest[..at], &rest[at..]),
                None => (rest, ""),
            };
            let term = str::trim(term).to_string();
            let made = if word == "adding " {
                Manipulation::Adding(term)
            } else {
                Manipulation::Multiplying(term)
            };
            return Some((made, after));
        }
        None
    }

    /// The row reason this is, its term read at `path`'s `line`.
    pub fn as_row(&self, path: &str, line: usize) -> RowReason {
        match self {
            Manipulation::Adding(t) => RowReason::Adding(Written::new(t, path, line)),
            Manipulation::Multiplying(c) => {
                RowReason::Multiplying(Written::new(c, path, line))
            }
            Manipulation::Restate => RowReason::Restate,
            Manipulation::Weakening => RowReason::Weakening,
        }
    }
}

impl fmt::Display for Manipulation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Manipulation::Adding(t) => write!(f, "adding {t}"),
            Manipulation::Multiplying(c) => write!(f, "multiplying by {c}"),
            Manipulation::Restate => f.write_str("restate"),
            Manipulation::Weakening => f.write_str("weakening"),
        }
    }
}

impl Head {
    pub fn is_item(&self) -> bool {
        matches!(self, Head::Item { .. })
    }

    pub fn is(&self, method: Method) -> bool {
        *self == Head::Method(method)
    }

    pub fn method(&self) -> Option<Method> {
        match self {
            Head::Method(m) => Some(*m),
            _ => None,
        }
    }

    /// Whether this head opens a block of steps.
    pub fn takes_block(&self) -> bool {
        self.method().is_some_and(Method::takes_block)
    }
}

impl fmt::Display for Head {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Head::Item { kind, cited } => write!(f, "{}:{cited}", kind.prefix()),
            Head::Method(m) => f.write_str(m.as_str()),
            Head::Define => f.write_str("define"),
            Head::Lines => f.write_str("from"),
            Head::Manipulation(m) => write!(f, "{m}"),
        }
    }
}

/// A step's justification, or a requires line's reason, as the skeleton
/// reader cut it (`skeleton::cut`): its head and the slots it fills.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Justification {
    pub head: Head,
    /// The text cut, for a message.
    pub text: String,
    pub line: usize,
    /// Everything cited, in order (`Slots::refs`), and each line a
    /// calculation's chain cites.
    pub refs: Vec<String>,
    /// An instantiate's `in …`.
    pub target: Option<String>,
    /// The values the justification gives what it cites.
    pub values: Values,
    /// Each line of a calculation's chain, with the line it is on.
    pub chain: Vec<(String, usize)>,
    /// Each row of an `inequalities` step with no `from`, with the line it
    /// is on (`GRAMMAR.md`, inequality rows).
    pub rows: Vec<(String, usize)>,
    /// What the names its file cites stand for.
    pub names: Arc<Names>,
    /// The define's label, where the head is a define.
    pub defined: Option<String>,
    /// The line this step's claim is the opposite of, `contradicting 3.6`,
    /// which closes a contradiction block or ends a case that cannot occur.
    pub contradicting: Option<String>,
    /// What an `obtain` names, in order.
    pub obtained: Vec<String>,
    /// The item an `obtain` takes its objects from, `thm:x`.
    pub obtained_from: Option<String>,
    /// The `from` slot's lines and labels, in order.
    pub from: Vec<String>,
    /// A substitute's equation, as written.
    pub equation: Option<Written>,
    /// Where a substitute takes its equation from.
    pub source: Option<Source>,
    /// The line or label a substitute puts its equation into.
    pub into: Option<Place>,
    /// The letter an induction is on.
    pub on: Option<String>,
    /// Where an induction starts, `starting at m`.
    pub start: Option<String>,
    /// Why the justification matches no production of `GRAMMAR.md`; None
    /// where it matches one. Both tools read a justification only once it
    /// matches, so each refuses the same text in the same words.
    pub unproduced: Option<String>,
}

impl Justification {
    /// A justification as the skeleton reader cut it, read in a file whose
    /// citations mean what `names` says.
    pub fn of(slots: Slots, line: usize, names: &Arc<Names>) -> Justification {
        Justification {
            refs: slots.refs(),
            values: Values::of(&slots.values),
            head: slots.head,
            text: slots.text,
            line,
            target: slots.target,
            chain: Vec::new(),
            rows: Vec::new(),
            names: names.clone(),
            defined: slots.defined,
            contradicting: slots.contradicting,
            obtained: slots.obtained,
            obtained_from: slots.obtained_from,
            from: slots.from,
            equation: slots.equation,
            source: slots.source,
            into: slots.into,
            on: slots.on,
            start: slots.start,
            unproduced: slots.unproduced,
        }
    }

    /// The full name a citation written in this justification's file means.
    pub fn item(&self, cited: &str) -> String {
        self.names.full(cited)
    }

    /// The item the justification cites, as `thm:x` or another prefix:
    /// either the head is the item, or the step obtains from one. `obtain
    /// c: axi:completeness S := S, from 5, 2, 7` owes the item's hypotheses
    /// as surely as a step headed by it does.
    pub fn cited_item(&self) -> Option<String> {
        match &self.head {
            Head::Item { .. } => Some(self.head.to_string()),
            _ => self.obtained_from.clone(),
        }
    }

    /// The item a reason heads with, `mun:x`, and the kind its prefix says;
    /// None for a reason that is a method or its lines.
    pub fn head_item(&self) -> Option<(String, ItemKind)> {
        match &self.head {
            Head::Item { kind, .. } => Some((self.head.to_string(), *kind)),
            _ => None,
        }
    }
}

/// One numbered step of a proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub number: StepNo,
    pub claim: Written,
    pub just: Justification,
    pub requires: Vec<Requires>,
    /// The part markers of the block it owns, with their lines.
    pub parts: Vec<(String, usize)>,
    pub openers: Vec<Opener>,
    pub line: usize,
    /// Which part of its parent's block this step sits in.
    pub part: Option<usize>,
    /// What the block it opens does, with the line it is said on.
    pub note: Option<(String, usize)>,
    /// What each part of its block does, by the part's index.
    pub part_notes: IndexMap<usize, (String, usize)>,
    /// The claim says `, which is impossible`: a closed fact `arithmetic`
    /// shows false, which ends a contradiction block on this step.
    pub impossible: bool,
}

impl Step {
    pub fn claim_text(&self) -> String {
        self.claim.text().to_string()
    }

    /// The requires lines written above the one on `line`, which it rests on
    /// besides what it cites (`SYNTAX.md`: a requires line rests on its
    /// reason and on the requires lines above it). A line below is not yet
    /// established. Both tools read a requires line's ground from here; what
    /// of it a method combines is the method's (`METHODS.md`).
    pub fn requires_above(&self, line: usize) -> impl Iterator<Item = &Requires> {
        self.requires.iter().take_while(move |o| o.line != line)
    }
}

/// Which file's scope a theorem is read in.
pub type ScopeId = usize;

/// What a proof file holds outside its theorems: the definitions it writes
/// between them, and what it imports from other files, one item to a line.
///
/// A theorem sees the definitions written above it and every one its file
/// imports (`visible`). An imported one is read in the file that wrote it,
/// which is why each carries the scope it comes from.
#[derive(Clone, Debug)]
pub struct FileScope {
    pub path: String,
    pub defines: Vec<DefineLine>,
    /// Its defines of phrases (`define <name>: <phrase> means <meaning>`),
    /// which give no name a formula writes and are kept apart from those
    /// that do.
    pub phrases: Vec<DefineLine>,
    /// A define's label, and what its `reads` line says.
    pub readings: IndexMap<String, (String, usize)>,
    /// The defines it imports from proof files.
    pub imports: Vec<Import>,
    /// The items it imports that a step cites by prefix and name.
    pub items: Vec<ItemImport>,
    /// Each definition import, by its alias, and the define it names in the
    /// scope that wrote it (`link_definitions`).
    pub linked: IndexMap<String, (ScopeId, DefineLine)>,
    /// The library functions it imports, which are in scope in it and in no
    /// file that does not import them.
    pub functions: Vec<FunctionImport>,
    /// The line each of its theorems is written on, by the theorem's name:
    /// what a theorem of the file is stated over (`sorts::stated_over`).
    pub theorems: IndexMap<String, usize>,
}

impl FileScope {
    pub fn new(path: &str) -> Self {
        FileScope {
            path: path.to_string(),
            defines: Vec::new(),
            phrases: Vec::new(),
            readings: IndexMap::new(),
            imports: Vec::new(),
            items: Vec::new(),
            linked: IndexMap::new(),
            functions: Vec::new(),
            theorems: IndexMap::new(),
        }
    }

    /// The names of the library functions it imports.
    pub fn function_names(&self) -> IndexSet<String> {
        self.functions.iter().map(|f| f.name.clone()).collect()
    }

    pub fn module(&self) -> &str {
        module_of(&self.path)
    }

    /// What each name its citations write stands for: the items it imports
    /// and the library functions, which a line unfolding one cites.
    pub fn names(&self) -> Names {
        let mut imported: IndexMap<String, String> = IndexMap::new();
        for i in &self.items {
            imported.entry(i.alias.clone()).or_insert_with(|| i.full());
        }
        for f in &self.functions {
            imported
                .entry(f.name.clone())
                .or_insert_with(|| format!("{}/{}", f.module, f.name));
        }
        Names {
            module: self.module().to_string(),
            imported,
        }
    }

    /// The label the import writing a definition as `alias` carries, where it
    /// gives one.
    pub fn import_label(&self, alias: &str) -> Option<&str> {
        self.imports
            .iter()
            .find(|i| i.alias == alias)
            .and_then(|i| i.label.as_deref())
    }

    /// The define this file writes at file level under `name`.
    pub fn written(&self, name: &str) -> Option<&DefineLine> {
        self.defines.iter().find(|d| match define_parts(&d.text) {
            Built(said) => said.name() == Some(name),
            _ => false,
        })
    }
}

/// (name, define, the scope it is read in) for every definition a line of
/// the file of scope `id` at `line` may use.
pub fn visible(
    scopes: &[FileScope],
    id: ScopeId,
    line: usize,
) -> Vec<(String, DefineLine, ScopeId)> {
    let scope = &scopes[id];
    let mut out: Vec<(String, DefineLine, ScopeId)> = scope
        .linked
        .iter()
        .map(|(alias, (src, d))| (alias.clone(), d.clone(), *src))
        .collect();
    for d in &scope.defines {
        if d.line < line {
            if let Built(said) = define_parts(&d.text) {
                // A recursion is never written at file level, and has no
                // one name to be found by.
                if let Some(name) = said.name() {
                    out.push((name.to_string(), d.clone(), id));
                }
            }
        }
    }
    out
}

/// One theorem of a proof file.
#[derive(Clone, Debug)]
pub struct Theorem {
    pub name: String,
    /// Whether its header says `mundane theorem`: a fact a proof takes for
    /// granted and cites `mun:`, as a mundane record is. Only a theorem of
    /// the standard library is marked so, since only the library holds
    /// what proofs reach for as known.
    pub mundane: bool,
    pub hypotheses: Vec<Hypothesis>,
    pub ranges: Vec<Range>,
    pub conclusion: String,
    /// The line of the `then`: a define above it is the statement's, and
    /// the statement is read with it.
    pub conclusion_line: usize,
    pub defines: Vec<DefineLine>,
    /// A define's label, and what its `reads` line says.
    pub readings: IndexMap<String, (String, usize)>,
    pub steps: Vec<Step>,
    pub line: usize,
    pub path: String,
    /// `metamath` and `note`, where it says them.
    pub fields: IndexMap<String, String>,
    pub scope: ScopeId,
    /// What the names its file cites stand for.
    pub names: Arc<Names>,
}

impl Theorem {
    pub fn module(&self) -> &str {
        module_of(&self.path)
    }

    /// The `then` line's formula as written, with where.
    pub fn stated(&self) -> Written {
        Written::new(&self.conclusion, &self.path, self.conclusion_line)
    }

    pub fn qualified(&self) -> String {
        format!("{}/{}", self.module(), self.name)
    }

    /// Whether `line` of the theorem's file is one of its own: from its
    /// header to the last line anything in it is written on. A file's
    /// theorems never interleave, so no other theorem's line is among them.
    pub fn owns_line(&self, line: usize) -> bool {
        (self.line..=self.last_line()).contains(&line)
    }

    /// The last line anything in the theorem is written on.
    fn last_line(&self) -> usize {
        let steps = self.steps.iter().flat_map(|s| {
            let just = &s.just;
            [s.line, just.line]
                .into_iter()
                .chain(s.requires.iter().map(|r| r.line))
                .chain(s.openers.iter().map(|o| o.line))
                .chain(s.parts.iter().map(|(_, l)| *l))
                .chain(just.chain.iter().map(|(_, l)| *l))
                .chain(just.rows.iter().map(|(_, l)| *l))
        });
        let heads = self
            .hypotheses
            .iter()
            .map(|h| h.line)
            .chain(self.defines.iter().map(|d| d.line));
        steps
            .chain(heads)
            .chain([self.line, self.conclusion_line])
            .max()
            .unwrap_or(self.line)
    }

    /// Each define by recursion above the `then`, which the statement is
    /// read with, and its line. One that does not read is left out, and is
    /// `check_recursions`'s to report.
    pub fn stated_recursions(&self) -> Vec<(usize, super::define::Recursion)> {
        self.defines
            .iter()
            .filter(|d| d.line < self.conclusion_line)
            .filter_map(|d| match define_parts(&d.text) {
                Built(DefineParts::Recursion(r)) => Some((d.line, r)),
                _ => None,
            })
            .collect()
    }

    /// Each let that says what kind of number its name is, read
    /// (`DefineLine::kinded`).
    pub fn kinded(&self, members: &IndexMap<String, String>) -> Checked<Vec<Kinded>> {
        let mut out = Vec::new();
        for d in &self.defines {
            if let Some(k) = d.kinded(&self.path, members)? {
                out.push(k);
            }
        }
        Ok(out)
    }

    /// The step a let's reason is read under, as a requires line is read
    /// under its step (`requires_as_step`): the first step below the let,
    /// whose scope the let stands in. None for a let below every step.
    pub fn step_after(&self, line: usize) -> Option<&Step> {
        self.steps.iter().find(|s| s.line > line)
    }
}

/// Everything a theorem's lines say, as one run of text: the statement, its
/// defines, and every step's claim, openers, requires lines and
/// justification.
pub fn written_text(thm: &Theorem) -> String {
    let mut parts: Vec<&str> = thm.hypotheses.iter().map(|h| h.text.as_str()).collect();
    parts.push(&thm.conclusion);
    parts.extend(thm.defines.iter().map(|d| d.text.as_str()));
    parts.extend(
        thm.defines
            .iter()
            .filter_map(|d| d.reason.as_ref().map(|r| r.how.as_str())),
    );
    for step in &thm.steps {
        parts.push(step.claim.text());
        parts.extend(step.openers.iter().map(|o| o.text.as_str()));
        parts.extend(step.requires.iter().map(|r| r.fact.text()));
        parts.push(&step.just.text);
        parts.extend(step.just.chain.iter().map(|(t, _)| t.as_str()));
    }
    parts.join(" ")
}

/// Where a chain's first line puts its relation: the first time the symbol
/// stands outside every bracket; None where it stands only inside.
///
/// A sum binds its index with the same `=` a chain relates by, so
/// `x·(Σ(k = 0 to m) t(k)) = …` has an `=` inside the sum before the one the
/// chain means.
pub fn outermost(words: &[&str], relation: &str) -> Option<usize> {
    let mut depth: i64 = 0;
    for (at, word) in words.iter().enumerate() {
        if depth == 0 && *word == relation {
            return Some(at);
        }
        let opens = word.chars().filter(|c| "({[".contains(*c)).count() as i64;
        let closes = word.chars().filter(|c| ")}]".contains(*c)).count() as i64;
        depth += opens - closes;
    }
    None
}

fn parse_justification(
    path: &str,
    line: &Line,
    labels: &skeleton::Labels,
    names: &Arc<Names>,
) -> Checked<Justification> {
    // A malformed justification is reported by the checker, not raised here
    // (`Justification::unproduced`): one bad line must not cost the reader
    // every later line in the file.
    let slots = skeleton::cut(&line.text, path, line.no, labels)?;
    Ok(Justification::of(slots, line.no, names))
}

/// The label of each define of a phrase the file has written so far, with
/// the item a line citing it cites: `def:` and its name.
fn phrase_labels(scope: &FileScope) -> Vec<skeleton::PhraseLabel> {
    scope
        .phrases
        .iter()
        .filter_map(|d| match define_parts(&d.text) {
            Built(DefineParts::Phrase(p)) => Some(skeleton::PhraseLabel {
                label: d.label.clone(),
                kind: ItemKind::Definition,
                name: p.name,
            }),
            _ => None,
        })
        .collect()
}

/// Every item a theorem's steps cite, by full name, with its line.
pub fn cited_items(thm: &Theorem) -> Vec<(String, usize)> {
    let mut out = Vec::new();
    for step in &thm.steps {
        let just = &step.just;
        if let Some(item) = just.cited_item() {
            out.push((just.item(&item), just.line));
        }
        if let Some(target) = &just.target {
            if item_kind(target).is_some() {
                out.push((just.item(target), just.line));
            }
        }
        for req in &step.requires {
            if let Some((cited, _)) = req.cited_item() {
                out.push((just.item(&cited), req.line));
            }
        }
    }
    // A let's reason is written as a requires line's is.
    for reason in thm.defines.iter().filter_map(|d| d.reason.as_ref()) {
        if let Some((cited, _)) = reason.cited_item() {
            out.push((thm.names.full(&cited), reason.line));
        }
    }
    out
}

enum Imported {
    Item(ItemImport),
    Define(Import),
}

/// One `import` line: one item, with the words its record's header says
/// before its name, `mundane` for a theorem a proof takes for granted and
/// then its kind.
///
/// `import theorem stdlib/divisibility/prime-factor` brings in an item a step
/// cites, `thm:prime-factor`, or by the name after `as`, and
/// `import mundane theorem stdlib/numbers/int-closure` one it cites
/// `mun:int-closure`. A library function is read here as any library item
/// is, and `link_functions` sets it apart once the records are read. A define
/// of a proof file is brought in as a `definition`, under one letter, with
/// the label a line of this file cites it by where a line does. Whether the
/// words are the header of what the line names is the checker's to ask,
/// since it wants the item.
fn importing(path: &str, no: usize, text: &str) -> Checked<Imported> {
    let Some(m) = skeleton::import_line(text) else {
        return Err(Problem::new(
            path,
            no,
            "an import says `import <kind> <file>/<name>`, as `import theorem stdlib/divisibility/prime-factor` does",
        ));
    };
    let mundane = m.mundane;
    let word = m.kind;
    let Some(record_kind) = RecordKind::parse(word).filter(|k| k.is_item()) else {
        return Err(Problem::new(
            path,
            no,
            format!(
                "import {word}: an import says the header of the item it names, its kind, axiom, theorem or definition, with mundane before a theorem taken for granted, as `import mundane theorem stdlib/numbers/int-closure`"
            ),
        ));
    };
    if mundane && record_kind != RecordKind::Theorem {
        return Err(Problem::new(
            path,
            no,
            format!(
                "import mundane {word} {}: an axiom or a definition gives meaning, and a pedantic textbook cites it, so it is never mundane; import it as `import {word} {}`",
                m.full, m.full
            ),
        ));
    }
    let kind = if mundane {
        ItemKind::Mundane
    } else {
        match record_kind {
            RecordKind::Axiom => ItemKind::Axiom,
            RecordKind::Definition => ItemKind::Definition,
            _ => ItemKind::Theorem,
        }
    };
    let keyword = if mundane {
        format!("mundane {word}")
    } else {
        word.to_string()
    };
    let whole = m.full;
    let (module, name) = match whole.rfind('/') {
        Some(at) => (&whole[..at], &whole[at + 1..]),
        None => ("", whole),
    };
    if module.is_empty() {
        return Err(Problem::new(
            path,
            no,
            format!("import {keyword} {whole} names no file"),
        ));
    }
    let alias = m.alias.unwrap_or(name);
    let label = m.label.map(String::from);
    let from_library = in_stdlib(whole);
    // A define of a proof file is written in formulas, and cited by the
    // label its import gives it, as one the file defines is: a calculation
    // link writing S(k + 1) out cites the equation. A file that never writes
    // it out gives it no label. A define of a phrase is named by a word, as
    // an item is, and is imported and cited as one, `def:<name>`.
    if !from_library
        && record_kind == RecordKind::Definition
        && super::define::is_one_name(name)
    {
        if !super::define::is_one_name(alias) {
            return Err(Problem::new(
                path,
                no,
                format!(
                    "a define is imported under one letter, perhaps with a subscript or a prime, and {} is not one",
                    repr(alias)
                ),
            ));
        }
        return Ok(Imported::Define(Import {
            module: module.to_string(),
            name: name.to_string(),
            alias: alias.to_string(),
            line: no,
            label,
        }));
    }
    // Everything else is written only in a justification, by its prefix and
    // the name it is imported under.
    if label.is_some() {
        return Err(Problem::new(
            path,
            no,
            format!(
                "import {keyword} {whole}: only a define of a proof file carries a label"
            ),
        ));
    }
    for said in [name, alias] {
        if !skeleton::is_name(said) {
            return Err(Problem::new(
                path,
                no,
                format!(
                    "import {keyword} {whole}: {} is not an item's name",
                    repr(said)
                ),
            ));
        }
    }
    Ok(Imported::Item(ItemImport {
        kind,
        said: keyword,
        module: module.to_string(),
        name: name.to_string(),
        alias: alias.to_string(),
        line: no,
    }))
}

/// A chain line's citation, read from the right end of the line rather than
/// from the whitespace that happens to separate it (`skeleton::chain_cite`).
///
/// A link relating numerals alone may name `arithmetic` in place of a line,
/// and then it cites nothing: the fact is worked out where it stands.
fn chain_citation(path: &str, line: &Line) -> Checked<Vec<String>> {
    if skeleton::chain_cite(&line.text).is_none() {
        return Err(Problem::new(
            path,
            line.no,
            "chain line names no line or label; a chain only joins, so every line must cite a numbered step, a label, `arithmetic` for a link of numerals alone, or `real arithmetic` for a closed link with a square root",
        ));
    }
    Ok(chain_cited(&line.text).into_iter().collect())
}

/// The line or label a chain line cites, read from its right end; None for
/// a link that names `arithmetic` or `real arithmetic`, or a line that
/// names nothing.
pub fn chain_cited(text: &str) -> Option<String> {
    skeleton::chain_cite(text)
        .filter(|cite| !matches!(*cite, "arithmetic" | "real arithmetic"))
        .map(String::from)
}

/// The relations a chain line joins by (`GRAMMAR.md`, calculation chains).
pub const CHAIN_RELATIONS: [&str; 6] = ["=", "≤", "<", "≥", ">", "≡"];

/// Each order a chain going down joins by, with the one it is read as going
/// up: `a ≥ b` is `b ≤ a`.
const DOWNWARD: [(&str, &str); 2] = [("≥", "≤"), (">", "<")];

/// One line of a calculation, cut as `GRAMMAR.md`'s chain productions cut
/// it: the relation it joins by, the term it reaches, the modulus a `≡`
/// line says, and what it cites.
#[derive(Clone, Debug)]
pub struct ChainLine {
    pub relation: String,
    pub term: Written,
    pub modulus: Option<Written>,
    /// The line, label, `arithmetic` or `real arithmetic` it cites, the
    /// line's last word or, for `real arithmetic`, its last two.
    pub cite: String,
    pub line: usize,
}

impl ChainLine {
    /// The line or label the link cites; None where it names `arithmetic`
    /// and cites nothing.
    pub fn cited(&self) -> Option<&str> {
        skeleton::is_ref(&self.cite).then_some(self.cite.as_str())
    }

    /// The link as the page writes it, from the term `from` before it, for
    /// a message to quote: `1 = 1(1 + 1)/3`. It is never read.
    pub fn quoted(&self, from: &Written) -> String {
        let modulus = match &self.modulus {
            Some(n) => format!(" (mod {n})"),
            None => String::new(),
        };
        format!("{from} {} {}{modulus}", self.relation, self.term)
    }
}

/// A calculation: the term its first line starts from, and each line's
/// link from the term before it.
#[derive(Clone, Debug)]
pub struct Chain {
    pub start: Written,
    pub lines: Vec<ChainLine>,
}

impl Chain {
    /// The chain read going up: one whose orders go down, t₀ ≥ t₁ > t₂,
    /// is the same links read from its last term, t₂ < t₁ ≤ t₀, and
    /// concludes the same, since t₀ > t₂ is t₂ < t₀. A chain going up is
    /// itself.
    pub fn upward(&self) -> Chain {
        let down = |r: &str| DOWNWARD.iter().find(|(d, _)| *d == r).map(|(_, u)| *u);
        if !self.lines.iter().any(|l| down(&l.relation).is_some()) {
            return self.clone();
        }
        let terms: Vec<&Written> = std::iter::once(&self.start)
            .chain(self.lines.iter().map(|l| &l.term))
            .collect();
        let lines = (0..self.lines.len())
            .rev()
            .map(|i| {
                let l = &self.lines[i];
                ChainLine {
                    relation: down(&l.relation).unwrap_or(&l.relation).to_string(),
                    term: terms[i].clone(),
                    modulus: None,
                    cite: l.cite.clone(),
                    line: l.line,
                }
            })
            .collect();
        Chain {
            start: terms[terms.len() - 1].clone(),
            lines,
        }
    }
}

/// What a row of an `inequalities` step names as its reason (`METHODS.md`,
/// inequalities, Rows).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RowReason {
    /// The line the first row writes out, by its reference.
    Cited(String),
    /// A term added to both sides.
    Adding(Written),
    /// Both sides multiplied by a number.
    Multiplying(Written),
    /// A relation turned round: an equation's two sides swapped, or an order
    /// or a `≠` read from its other side.
    Restate,
    /// A relation weakened.
    Weakening,
    /// A side written as the same number another way.
    Algebra,
}

/// One row of an `inequalities` step: the formula, the reason, and the line.
#[derive(Clone, Debug)]
pub struct Row {
    pub formula: Written,
    pub reason: RowReason,
    pub line: usize,
}

/// The words a row's reason opens with that a term follows.
const ROW_WORDS: [&str; 2] = ["adding", "multiplying by"];

/// The rows an `inequalities` step writes, each cut as `GRAMMAR.md`'s
/// inequality rows cut it, from the right: a last word that is a reference,
/// `restate`, `weakening` or `algebra`, or `adding` or `multiplying by` and
/// a term. None for a step with no rows; a row with no reason is a defect,
/// and so is one ending in `symmetry`, a word kept back for later.
pub fn rows(just: &Justification, path: &str) -> Option<Checked<Vec<Row>>> {
    if just.rows.is_empty() {
        return None;
    }
    let mut out = Vec::new();
    for (text, no) in &just.rows {
        let whole = str::trim(text);
        // A formula writes neither `adding` nor `multiplying by`, so where a
        // row does, its reason starts there and the term after it may be
        // anything, a lone letter that would read as a label among them.
        let worded = ROW_WORDS
            .iter()
            .filter_map(|w| whole.rfind(&format!(" {w} ")).map(|at| (at, *w)))
            .max_by_key(|(at, _)| *at)
            .map(|(at, w)| {
                let term =
                    Written::new(str::trim(&whole[at + w.len() + 2..]), path, *no);
                let reason = if w == "adding" {
                    RowReason::Adding(term)
                } else {
                    RowReason::Multiplying(term)
                };
                (str::trim(&whole[..at]), reason)
            });
        let last = whole.rsplit(char::is_whitespace).next().unwrap_or(whole);
        let before_last = str::trim(&whole[..whole.len() - last.len()]);
        if last == "symmetry" {
            return Some(Err(Problem::new(
                path,
                *no,
                "`symmetry` is kept back for later; a row turning a relation round is `restate`",
            )));
        }
        let word = match last {
            "restate" => Some(RowReason::Restate),
            "weakening" => Some(RowReason::Weakening),
            "algebra" => Some(RowReason::Algebra),
            _ if skeleton::is_ref(last) => Some(RowReason::Cited(last.to_string())),
            _ => None,
        };
        let cut = worded.or(word.map(|reason| (before_last, reason)));
        let Some((formula, reason)) = cut.filter(|(f, _)| !f.is_empty()) else {
            return Some(Err(Problem::new(
                path,
                *no,
                "a row gives no reason: it ends in the line it writes out, `adding` or `multiplying by` and a term, `restate`, `weakening` or `algebra`",
            )));
        };
        out.push(Row {
            formula: Written::new(formula, path, *no),
            reason,
            line: *no,
        });
    }
    Some(Ok(out))
}

/// The chain a calculation writes, cut by the skeleton; None for a
/// justification that is not a calculation. The first line's relation is
/// the first of `CHAIN_RELATIONS` it writes outside brackets, and one with
/// none is a defect.
pub fn chain(just: &Justification, path: &str) -> Option<Checked<Chain>> {
    if !just.head.is(Method::Calculation) || just.chain.is_empty() {
        return None;
    }
    let mut start = None;
    let mut lines = Vec::new();
    for (i, (text, no)) in just.chain.iter().enumerate() {
        let whole = str::trim(text);
        // The citation is read off the right end, so that `real arithmetic`
        // is cut whole and the term does not end in "real".
        let (body, cite) = match skeleton::chain_cite(whole) {
            Some(cite) => (str::trim(&whole[..whole.len() - cite.len()]), cite),
            None => match whole.rfind(char::is_whitespace) {
                Some(at) => (str::trim(&whole[..at]), str::trim(&whole[at..])),
                None => ("", whole),
            },
        };
        let words: Vec<&str> = body.split_whitespace().collect();
        // A link cites one line (`SYNTAX.md`), so one written `1, 2` has its
        // first citation end the term with a comma.
        if words.last().is_some_and(|w| w.ends_with(',')) {
            let named = words
                .iter()
                .rev()
                .take_while(|w| w.ends_with(','))
                .map(|w| w.trim_end_matches(','))
                .collect::<Vec<_>>();
            let mut named: Vec<&str> = named.into_iter().rev().collect();
            named.push(cite);
            return Some(Err(Problem::new(
                path,
                *no,
                format!(
                    "a calculation line cites one line or label, and this one cites {}; a step with several cites them, and its line cites that step",
                    named.join(", ")
                ),
            )));
        }
        let at = if i == 0 {
            let found = (0..words.len()).find(|&at| {
                CHAIN_RELATIONS.contains(&words[at])
                    && outermost(&words, words[at]) == Some(at)
            });
            let Some(at) = found else {
                return Some(Err(Problem::new(
                    path,
                    *no,
                    "a chain's first line writes no =, ≤, <, ≥, > or ≡ outside brackets",
                )));
            };
            start = Some(Written::new(words[..at].join(" "), path, *no));
            at
        } else {
            0
        };
        let Some(relation) = words.get(at).map(|w| w.to_string()) else {
            return Some(Err(Problem::new(
                path,
                *no,
                "a chain line writes no relation",
            )));
        };
        let rest = words.get(at + 1..).unwrap_or(&[]).join(" ");
        let (term, modulus) = skeleton::chain_modulus(&rest);
        let modulus = modulus.map(|m| Written::new(str::trim(m), path, *no));
        lines.push(ChainLine {
            relation,
            term: Written::new(term, path, *no),
            modulus,
            cite: cite.to_string(),
            line: *no,
        });
    }
    // A chain goes one way: a ≤ b ≥ c says nothing of a against c.
    let up = lines
        .iter()
        .find(|l| l.relation == "≤" || l.relation == "<");
    let down = lines
        .iter()
        .find(|l| l.relation == "≥" || l.relation == ">");
    if let (Some(up), Some(down)) = (up, down) {
        let later = if up.line > down.line { up } else { down };
        let earlier = if up.line > down.line { down } else { up };
        return Some(Err(Problem::new(
            path,
            later.line,
            format!(
                "a chain goes one way, and this line says {} after one saying {}; {} after {} says nothing of the first term against the last",
                later.relation, earlier.relation, later.relation, earlier.relation
            ),
        )));
    }
    Some(Ok(Chain {
        start: start.expect("a first line"),
        lines,
    }))
}

/// A step being read, whose justification may not have arrived yet.
struct DraftStep {
    step: Step,
    has_just: bool,
}

struct DraftTheorem {
    thm: Theorem,
    steps: Vec<DraftStep>,
}

const THEOREM_FIELDS: [&str; 2] = ["metamath", "note"];

fn label_at_end(text: &str) -> Option<String> {
    skeleton::label_at_end(text).map(String::from)
}

/// A requires line read as the step it would be: its fact claimed, its
/// reason the justification, at its own line, under the step it sits in and
/// with no requires lines of its own. A reason that is a method or an item
/// is proved this way, so a requires line and a step are one thing to the
/// elaborator (`ELABORATION.md`, R2).
pub fn requires_as_step(step: &Step, req: &Requires) -> Checked<Step> {
    Ok(reason_as_step(step, req, req.by()?))
}

/// `requires_as_step`, with the reason `by` the line was cut into.
pub fn reason_as_step(step: &Step, req: &Requires, by: &Justification) -> Step {
    Step {
        claim: req.fact.clone(),
        just: by.clone(),
        requires: Vec::new(),
        parts: Vec::new(),
        openers: Vec::new(),
        line: req.line,
        note: None,
        part_notes: IndexMap::new(),
        impossible: false,
        ..step.clone()
    }
}

/// The step with `, which is impossible` taken off the end of its claim and
/// said by `impossible` instead.
fn impossible(mut step: Step) -> Step {
    let claim = &step.claim;
    if let Some(said) = skeleton::which_is_impossible(claim.text()) {
        step.claim = Written::new(said, claim.path(), claim.line());
        step.impossible = true;
    }
    step
}

/// What to say of a line that opens as a step does with a number that is
/// not one: None for any other line.
fn misnumbered(text: &str) -> Option<String> {
    let number = skeleton::misnumbered(text)?;
    Some(format!(
        "`{number}.` is no step number: a step is numbered by whole numbers joined by dots, as 1.6 or 1.6.2"
    ))
}

/// What a step holds until its justification line is read.
fn placeholder_justification() -> Justification {
    Justification::of(Slots::new(Head::Define, ""), 0, &Arc::default())
}

/// A line opening a theorem: `theorem <name>`, or `mundane theorem <name>`
/// for a fact of the standard library a proof takes for granted.
struct TheoremHeader<'t> {
    mundane: bool,
    /// The rest of the line, the name before it is trimmed and checked.
    name: &'t str,
}

/// The header a line opens a theorem with; None for any other line.
fn theorem_header(t: &str) -> Option<TheoremHeader<'_>> {
    if let Some(name) = t.strip_prefix("mundane theorem ") {
        return Some(TheoremHeader {
            mundane: true,
            name,
        });
    }
    t.strip_prefix("theorem ").map(|name| TheoremHeader {
        mundane: false,
        name,
    })
}

/// The theorems of a proof file, and what the file holds outside them.
/// Structure comes from the step number; indentation is presentation and is
/// not consulted.
pub fn parse_proof(
    path: &str,
    text: &str,
    scope_id: ScopeId,
) -> Checked<(FileScope, Vec<Theorem>)> {
    let mut theorems: Vec<Theorem> = Vec::new();
    let mut scope = FileScope::new(path);
    let mut thm: Option<DraftTheorem> = None;
    // Whether the step being read still waits for its justification: the
    // index of the draft step in the theorem being read.
    let mut step: Option<usize> = None;
    let mut just_defined: Option<DefineLine> = None;
    // A let saying what kind of number its name is, whose reason is the
    // next line.
    let mut awaiting_reason: Option<DefineLine> = None;
    // What the file's citations name, settled at its first theorem: every
    // import comes before it.
    let mut names: Option<Arc<Names>> = None;
    // Between a theorem line and its statement a theorem may carry fields,
    // and a line there that opens no field continues the one above it.
    let mut header = false;
    let mut last_field: Option<(String, usize)> = None;
    // A part marker or a block opener appears before the sub-steps it governs,
    // so it is held until the next step arrives and is then attached to that
    // step's parent, which is the step that owns the block.
    // Each held marker, its line, and the note said under it.
    type Said = (String, usize);
    let mut pending_markers: Vec<(String, usize, Option<Said>)> = Vec::new();
    let mut pending_openers: Vec<(Intro, String, String, usize)> = Vec::new();
    let mut part_no: IndexMap<StepNo, usize> = IndexMap::new();
    let mut by_number: IndexMap<StepNo, usize> = IndexMap::new();

    /// The first marker held, by its word and line.
    fn first_marker(held: &[(String, usize, Option<Said>)]) -> Option<(&str, usize)> {
        held.first().map(|(marker, at, _)| (marker.as_str(), *at))
    }

    /// The first opener held, by its label and line.
    fn first_opener(held: &[(Intro, String, String, usize)]) -> Option<(&str, usize)> {
        held.first().map(|(_, _, label, at)| (label.as_str(), *at))
    }

    fn close_step(
        path: &str,
        thm: &Option<DraftTheorem>,
        step: &mut Option<usize>,
    ) -> Checked<()> {
        if let (Some(at), Some(t)) = (*step, thm.as_ref()) {
            let draft = &t.steps[at];
            if !draft.has_just {
                return Err(Problem::new(
                    path,
                    draft.step.line,
                    format!("step {} has no justification", draft.step.number),
                ));
            }
        }
        *step = None;
        Ok(())
    }

    /// Held markers and openers given to the step that owns their block,
    /// `owner`, numbered `parent`; what comes back is the part they open.
    #[allow(clippy::too_many_arguments)]
    fn attach(
        path: &str,
        draft: &mut DraftTheorem,
        owner: Option<usize>,
        parent: &StepNo,
        markers: &mut Vec<(String, usize, Option<Said>)>,
        openers: &mut Vec<(Intro, String, String, usize)>,
        part_no: &mut IndexMap<StepNo, usize>,
    ) -> Checked<Option<usize>> {
        for (marker, no, note) in markers.drain(..) {
            let Some(owner) = owner else {
                return Err(Problem::new(
                    path,
                    no,
                    format!("part marker {} outside any block", repr(&marker)),
                ));
            };
            draft.steps[owner].step.parts.push((marker, no));
            let index = part_no.get(parent).map_or(0, |n| n + 1);
            part_no.insert(parent.clone(), index);
            if let Some(note) = note {
                draft.steps[owner].step.part_notes.insert(index, note);
            }
        }
        let current = part_no.get(parent).copied();
        for (kind, text, label, no) in openers.drain(..) {
            let Some(owner) = owner else {
                return Err(Problem::new(
                    path,
                    no,
                    format!("{kind} line outside any block"),
                ));
            };
            let hypothesis_for = match skeleton::induction_hypothesis(&text) {
                Some(said) => Some(induction_hypothesis(
                    path,
                    &draft.steps[owner].step,
                    &said,
                    no,
                )?),
                None => None,
            };
            draft.steps[owner].step.openers.push(Opener {
                kind,
                text: text.clone(),
                label,
                line: no,
                part: current,
                is_claim: false,
                is_hypothesis: hypothesis_for.is_some(),
                hypothesis_for,
            });
        }
        Ok(current)
    }

    /// The letter `assume step N is true for k, the induction hypothesis`
    /// says it is for. N is the induction the line opens the step part of;
    /// that k is the letter N's claim binds, and the hypothesis N's
    /// statement at it, is read off the claim's tree by the tools.
    fn induction_hypothesis(
        path: &str,
        owner: &Step,
        said: &skeleton::InductionHypothesis,
        no: usize,
    ) -> Checked<String> {
        if !owner.just.head.is(Method::Induction) {
            return Err(Problem::new(
                path,
                no,
                "an induction hypothesis outside the step part of an induction",
            ));
        }
        if said.step != fmt(&owner.number) {
            return Err(Problem::new(
                path,
                no,
                format!(
                    "the induction hypothesis names step {}, and the induction is step {}",
                    said.step,
                    fmt(&owner.number)
                ),
            ));
        }
        Ok(said.letter.to_string())
    }

    /// A define after a theorem's last step is the file's, for the theorems
    /// below it: that theorem could never use it.
    fn settle(
        path: &str,
        thm: Option<DraftTheorem>,
        scope: &mut FileScope,
        theorems: &mut Vec<Theorem>,
    ) -> Checked<()> {
        let Some(mut draft) = thm else { return Ok(()) };
        let last = draft
            .steps
            .iter()
            .map(|s| s.step.line)
            .max()
            .unwrap_or(draft.thm.line);
        // A name the theorem gives is a let, and one below its last step is
        // the file's and a define (`SYNTAX.md`).
        for d in &draft.thm.defines {
            if d.reason.is_some() && d.line < draft.thm.conclusion_line {
                return Err(Problem::new(
                    path,
                    d.line,
                    "a let in a theorem's statement says no kind of number: the statement is what the theorem assumes, and a reason is a step of its proof",
                ));
            }
            let outside = d.line > last;
            match (naming(&d.text), outside) {
                (Some(Naming::Define), false) => {
                    return Err(Problem::new(
                        path,
                        d.line,
                        "a define inside a theorem: a name one theorem gives is a let, `let <name> = <term>`, and a define is the file's, outside the theorems",
                    ));
                }
                (Some(Naming::Let), true) => {
                    return Err(Problem::new(
                        path,
                        d.line,
                        "a let below a theorem's last step names a thing for the file, which a define does",
                    ));
                }
                _ => {}
            }
        }
        let moved: Vec<DefineLine> = draft
            .thm
            .defines
            .iter()
            .filter(|d| d.line > last)
            .cloned()
            .collect();
        for d in moved {
            draft.thm.defines.retain(|x| x != &d);
            if let Some(reading) = draft.thm.readings.shift_remove(&d.label) {
                scope.readings.insert(d.label.clone(), reading);
            }
            match define_parts(&d.text) {
                Built(DefineParts::Phrase(_)) => scope.phrases.push(d),
                _ => scope.defines.push(d),
            }
        }
        draft.thm.steps = draft
            .steps
            .into_iter()
            .map(|s| impossible(s.step))
            .collect();
        scope
            .theorems
            .insert(draft.thm.name.clone(), draft.thm.line);
        theorems.push(draft.thm);
        Ok(())
    }

    for line in read_lines(text) {
        let t = line.text.clone();
        // A `reads` line belongs to the define immediately above it, so what
        // a define leaves behind survives exactly one line.
        let previous = just_defined.take();
        if let Some(d) = awaiting_reason.take() {
            let head = t.split_whitespace().next().unwrap_or_default();
            if line.indent == 0
                || head == "reads"
                || skeleton::step_line(&t).is_some()
                || naming(&t).is_some()
            {
                return Err(Problem::new(
                    path,
                    d.line,
                    format!(
                        "let {} says what kind of number its name is, and the line under it gives no reason",
                        d.label
                    ),
                ));
            }
            let names = thm
                .as_ref()
                .map(|d| d.thm.names.clone())
                .unwrap_or_default();
            let reason = Reason {
                how: str::trim(&t).to_string(),
                line: line.no,
                by: cut_reason(&t, path, line.no)
                    .map(|slots| Justification::of(slots, line.no, &names)),
            };
            if let Some(draft) = thm.as_mut() {
                for written in draft.thm.defines.iter_mut().filter(|x| x.line == d.line)
                {
                    written.reason = Some(reason.clone());
                }
            }
            just_defined = Some(DefineLine {
                reason: Some(reason),
                ..d
            });
            continue;
        }
        let opened = theorem_header(&t).filter(|_| line.indent == 0);
        if let Some(TheoremHeader { mundane, name }) = opened {
            close_step(path, &thm, &mut step)?;
            held_at_end(
                path,
                first_marker(&pending_markers),
                first_opener(&pending_openers),
            )?;
            settle(path, thm.take(), &mut scope, &mut theorems)?;
            let name = str::trim(name).to_string();
            if !skeleton::is_name(&name) {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!("theorem name {} is malformed", repr(&name)),
                ));
            }
            if mundane && !in_stdlib(module_of(path)) {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!(
                        "mundane theorem {name}: only a theorem of the standard library is taken for granted; a proof elsewhere states `theorem {name}`"
                    ),
                ));
            }
            thm = Some(DraftTheorem {
                thm: Theorem {
                    name,
                    mundane,
                    hypotheses: Vec::new(),
                    ranges: Vec::new(),
                    conclusion: String::new(),
                    conclusion_line: 0,
                    defines: Vec::new(),
                    readings: IndexMap::new(),
                    steps: Vec::new(),
                    line: line.no,
                    path: path.to_string(),
                    fields: IndexMap::new(),
                    scope: scope_id,
                    names: names.get_or_insert_with(|| Arc::new(scope.names())).clone(),
                },
                steps: Vec::new(),
            });
            pending_markers.clear();
            pending_openers.clear();
            part_no.clear();
            by_number.clear();
            header = true;
            last_field = None;
            continue;
        }
        let Some(draft) = thm.as_mut() else {
            if t.starts_with("import ") {
                if !scope.defines.is_empty() || !scope.phrases.is_empty() {
                    return Err(Problem::new(
                        path,
                        line.no,
                        "an import below a define; imports come first",
                    ));
                }
                match importing(path, line.no, &t)? {
                    Imported::Item(import) => scope.items.push(import),
                    Imported::Define(import) => scope.imports.push(import),
                }
                continue;
            }
            // A define before any theorem is the file's, for every theorem; a
            // let names a thing within one theorem, and none is open here.
            if naming(&t) == Some(Naming::Let) {
                return Err(Problem::new(
                    path,
                    line.no,
                    "a let names a thing within a theorem; a name the whole file gives, and another may import, is a define",
                ));
            }
            if naming(&t) == Some(Naming::Define) {
                let Some(label) = label_at_end(&t) else {
                    return Err(Problem::new(
                        path,
                        line.no,
                        "define line carries no label",
                    ));
                };
                let d = DefineLine {
                    text: t.clone(),
                    label,
                    path: path.to_string(),
                    line: line.no,
                    reason: None,
                };
                match define_parts(&t) {
                    crate::outcome::Declined(d) => {
                        return Err(d.into_problem(path, line.no));
                    }
                    Built(DefineParts::Recursion(_)) => {
                        return Err(Problem::new(
                            path,
                            line.no,
                            "a define by recursion is written in the theorem that uses it, in its statement or its proof",
                        ));
                    }
                    Built(DefineParts::Phrase(_)) => scope.phrases.push(d.clone()),
                    Built(DefineParts::One(_)) => scope.defines.push(d.clone()),
                }
                just_defined = Some(d);
                continue;
            }
            if let (Some(rest), Some(d)) = (t.strip_prefix("reads"), &previous) {
                scope
                    .readings
                    .insert(d.label.clone(), (str::trim(rest).to_string(), line.no));
                continue;
            }
            return Err(Problem::new(
                path,
                line.no,
                "text before any theorem header that is neither an import nor a define",
            ));
        };

        let head = t.split_whitespace().next().unwrap_or_default().to_string();
        if header && THEOREM_FIELDS.contains(&head.as_str()) {
            if draft.thm.fields.contains_key(&head) {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!("theorem {} says {head} twice", draft.thm.name),
                ));
            }
            draft
                .thm
                .fields
                .insert(head.clone(), str::trim(&t[head.len()..]).to_string());
            last_field = Some((head, line.indent));
            continue;
        }
        if header {
            if let Some((field, indent)) = &last_field {
                if line.indent > *indent {
                    let value = draft.thm.fields.get_mut(field).unwrap();
                    value.push(' ');
                    value.push_str(&t);
                    continue;
                }
            }
        }
        header = false;

        if let Some(said) = skeleton::step_line(&t) {
            close_step(path, &thm, &mut step)?;
            let draft = thm.as_mut().unwrap();
            let number = StepNo::parse(said.number);
            // Resolve held markers and openers against the owner of the block
            // that this step sits in, and say which part it sits in.
            let parent = number.parent();
            let owner = by_number.get(&parent).copied();
            // A `case` held for a step whose block takes no cases is the last
            // case of the `cases` block open above, which has no steps: one
            // with none says it is the claim (`SYNTAX.md`).
            let cases_owner =
                |i: usize| draft.steps[i].step.just.head.is(Method::Cases);
            if let Some((_, at, _)) =
                pending_markers.iter().find(|(m, _, _)| m == "case")
            {
                if !owner.is_some_and(cases_owner) {
                    let last = draft.steps.last().map(|s| s.step.number.clone());
                    let open = last.and_then(|n| {
                        (1..=n.len())
                            .rev()
                            .map(|k| n.prefix(k))
                            .find(|p| by_number.get(p).is_some_and(|&i| cases_owner(i)))
                    });
                    if let Some(open) = open {
                        return Err(Problem::new(
                            path,
                            *at,
                            format!(
                                "this case of step {} has no steps, and its assumption does not say it is the claim; write its steps, or end the line `, which is the claim`",
                                fmt(&open)
                            ),
                        ));
                    }
                }
            }
            let current = attach(
                path,
                draft,
                owner,
                &parent,
                &mut pending_markers,
                &mut pending_openers,
                &mut part_no,
            )?;
            draft.steps.push(DraftStep {
                step: Step {
                    number: number.clone(),
                    claim: Written::new(said.claim, path, line.no),
                    just: placeholder_justification(),
                    requires: Vec::new(),
                    parts: Vec::new(),
                    openers: Vec::new(),
                    line: line.no,
                    part: current,
                    note: None,
                    part_notes: IndexMap::new(),
                    impossible: false,
                },
                has_just: false,
            });
            let at = draft.steps.len() - 1;
            by_number.insert(number, at);
            step = Some(at);
            continue;
        }

        if step.is_none() {
            if let Some(range) = Range::read(&t, line.no) {
                draft.thm.ranges.push(range);
                continue;
            }
        }
        // A naming line, read before a `let` that takes a member, which it
        // also opens with. Which word it may open with is settled once the
        // theorem's last step is known (`settle`).
        if naming(&t).is_some() {
            let Some(label) = label_at_end(&t) else {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!("{} line carries no label", head),
                ));
            };
            let says_kind = match define_parts(&t) {
                crate::outcome::Declined(d) => {
                    return Err(d.into_problem(path, line.no))
                }
                Built(parts) => parts.one().is_some_and(|one| one.kind.is_some()),
            };
            // A define names an object and is in scope from where it stands on.
            let d = DefineLine {
                text: t.clone(),
                label,
                path: path.to_string(),
                line: line.no,
                reason: None,
            };
            draft.thm.defines.push(d.clone());
            if says_kind {
                awaiting_reason = Some(d);
            } else {
                just_defined = Some(d);
            }
            continue;
        }
        let intro = Intro::parse(&head);
        if matches!(intro, Some(Intro::Let | Intro::Assume)) && step.is_none() {
            draft.thm.hypotheses.push(Hypothesis {
                kind: intro.unwrap(),
                text: t.clone(),
                label: label_at_end(&t),
                line: line.no,
            });
            continue;
        }
        if head == "then" && step.is_none() {
            draft.thm.conclusion = str::trim(&t["then".len()..]).to_string();
            draft.thm.conclusion_line = line.no;
            continue;
        }
        if head == "reads" {
            let Some(d) = &previous else {
                return Err(Problem::new(
                    path,
                    line.no,
                    "reads line that does not follow a define",
                ));
            };
            draft.thm.readings.insert(
                d.label.clone(),
                (str::trim(&t["reads".len()..]).to_string(), line.no),
            );
            continue;
        }
        if head == "note" {
            let said = (str::trim(&t["note".len()..]).to_string(), line.no);
            // Under a part marker, the note says what that part does; the
            // marker is still held, because the step owning it is found only
            // when the part's first step arrives.
            if let Some((marker, _no, held)) = pending_markers.last_mut() {
                if held.is_some() {
                    return Err(Problem::new(
                        path,
                        line.no,
                        format!("the {} part already carries a note", repr(marker)),
                    ));
                }
                if !pending_openers.is_empty() {
                    return Err(Problem::new(
                        path,
                        line.no,
                        format!(
                            "a note on the {} part goes directly under its marker, before its openers",
                            repr(marker)
                        ),
                    ));
                }
                *held = Some(said);
                continue;
            }
            match step {
                Some(at) if draft.steps[at].has_just => {
                    draft.steps[at].step.note = Some(said);
                }
                _ => {
                    return Err(Problem::new(
                        path,
                        line.no,
                        "note line outside a block",
                    ));
                }
            }
            continue;
        }
        if super::PART_MARKERS.contains(&t.as_str()) {
            pending_markers.push((t.clone(), line.no, None));
            continue;
        }
        if let Some(kind) = intro {
            let Some(label) = label_at_end(&t) else {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!("{head} line carries no label"),
                ));
            };
            let Some(said) = skeleton::which_is_the_claim(&t) else {
                pending_openers.push((kind, t.clone(), label, line.no));
                continue;
            };
            // A case that is the claim has no step to say which block it is
            // in, so it is in the innermost `cases` block open at this line.
            let draft = thm.as_mut().unwrap();
            let last = draft.steps.last().map(|s| s.step.number.clone());
            let owner = last.and_then(|n| {
                (1..=n.len()).rev().map(|k| n.prefix(k)).find(|p| {
                    by_number.get(p).is_some_and(|&i| {
                        draft.steps[i].step.just.head.is(Method::Cases)
                    })
                })
            });
            let Some(parent) = owner else {
                return Err(Problem::new(
                    path,
                    line.no,
                    "a line saying it is the claim outside any `cases` block",
                ));
            };
            let at = by_number[&parent];
            let current = attach(
                path,
                draft,
                Some(at),
                &parent,
                &mut pending_markers,
                &mut pending_openers,
                &mut part_no,
            )?;
            draft.steps[at].step.openers.push(Opener {
                kind,
                text: format!("{said} ({label})"),
                label,
                line: line.no,
                part: current,
                is_claim: true,
                is_hypothesis: false,
                hypothesis_for: None,
            });
            continue;
        }
        if head == "requires" {
            // A let written between the step and this line stands between
            // them: the line would be read as the step's, which it is not
            // written under. Before any step, it is the let's or nothing's.
            let since = step.map_or(0, |at| draft.steps[at].step.line);
            if let Some(d) = draft
                .thm
                .defines
                .iter()
                .rfind(|d| d.line > since && d.line < line.no)
            {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!(
                        "requires line under let {}, which carries none: the reason under a let is one line, and what it needs is a step above the let that the reason cites",
                        d.label
                    ),
                ));
            }
            let Some(at) = step else {
                return Err(Problem::new(
                    path,
                    line.no,
                    "requires line outside a step",
                ));
            };
            let body = str::trim(&t["requires".len()..]);
            // The fact ends at the first colon written against the word
            // before it. A colon inside a fact stands apart, as in `g : [a,
            // b] → ℝ` and `{x ∈ ℕ : x > 1}`.
            let chars: Vec<(usize, char)> = body.char_indices().collect();
            let split = chars.iter().enumerate().find_map(|(i, &(at, c))| {
                (c == ':' && i > 0 && !chars[i - 1].1.is_whitespace())
                    .then(|| (&body[..at], &body[at + 1..]))
            });
            let Some((fact, how)) = split else {
                return Err(Problem::new(
                    path,
                    line.no,
                    "requires line has no justification",
                ));
            };
            let by = cut_reason(how, path, line.no)
                .map(|slots| Justification::of(slots, line.no, &draft.thm.names));
            draft.steps[at].step.requires.push(Requires {
                fact: Written::new(str::trim(fact), path, line.no),
                how: str::trim(how).to_string(),
                line: line.no,
                by,
            });
            continue;
        }
        if let Some(at) = step {
            if !draft.steps[at].has_just {
                let mut defines: Vec<String> = Vec::new();
                for d in scope.defines.iter().chain(draft.thm.defines.iter()) {
                    if !defines.contains(&d.label) {
                        defines.push(d.label.clone());
                    }
                }
                for label in scope.imports.iter().filter_map(|i| i.label.as_ref()) {
                    if !defines.contains(label) {
                        defines.push(label.clone());
                    }
                }
                let labels = skeleton::Labels {
                    defines,
                    phrases: phrase_labels(&scope),
                };
                if is_justification(&t, &labels) {
                    draft.steps[at].step.just =
                        parse_justification(path, &line, &labels, &draft.thm.names)?;
                    draft.steps[at].has_just = true;
                } else {
                    draft.steps[at].step.claim.continued(&t);
                }
                continue;
            }
            // An `inequalities` step with no `from` may write its rows; the
            // first row's reason is the line the step cites, and its only
            // citation (`GRAMMAR.md`, inequality rows).
            let just = &draft.steps[at].step.just;
            if just.head.is(Method::Inequalities)
                && (!just.rows.is_empty() || just.refs.is_empty())
            {
                let first = just.rows.is_empty();
                let just = &mut draft.steps[at].step.just;
                if first {
                    just.refs.extend(chain_cited(&line.text));
                }
                just.rows.push((line.text.clone(), line.no));
                continue;
            }
            if draft.steps[at].step.just.head.is(Method::Calculation) {
                let cited = chain_citation(path, &line)?;
                let just = &mut draft.steps[at].step.just;
                just.refs.extend(cited);
                just.chain.push((line.text.clone(), line.no));
                continue;
            }
            if let Some(said) = misnumbered(&t) {
                return Err(Problem::new(path, line.no, said));
            }
            return Err(Problem::new(
                path,
                line.no,
                format!(
                    "unexpected line after a justification: {}",
                    repr(prefix(&t, 48))
                ),
            ));
        }
        if let Some(said) = misnumbered(&t) {
            return Err(Problem::new(path, line.no, said));
        }
        return Err(Problem::new(
            path,
            line.no,
            format!("unexpected line {}", repr(prefix(&t, 48))),
        ));
    }
    if let Some(d) = awaiting_reason {
        return Err(Problem::new(
            path,
            d.line,
            format!(
                "let {} says what kind of number its name is, and the line under it gives no reason",
                d.label
            ),
        ));
    }
    close_step(path, &thm, &mut step)?;
    held_at_end(
        path,
        first_marker(&pending_markers),
        first_opener(&pending_openers),
    )?;
    settle(path, thm.take(), &mut scope, &mut theorems)?;
    Ok((scope, theorems))
}

/// A part marker or an opener is held for the step after it, so one the
/// theorem ends under has nothing in it: the last case of a `cases` block
/// with no steps, which only a case saying it is the claim may be. Each is
/// given by the first of its kind still held, with its line.
fn held_at_end(
    path: &str,
    marker: Option<(&str, usize)>,
    opener: Option<(&str, usize)>,
) -> Checked<()> {
    if let Some((marker, at)) = marker {
        let claim = if marker == "case" {
            ", or end its assumption `, which is the claim`"
        } else {
            ""
        };
        return Err(Problem::new(
            path,
            at,
            format!("this {marker} has no steps, and the theorem ends under it; write its steps{claim}"),
        ));
    }
    if let Some((label, at)) = opener {
        return Err(Problem::new(
            path,
            at,
            format!(
                "{label} opens a part with no steps, and the theorem ends under it"
            ),
        ));
    }
    Ok(())
}
