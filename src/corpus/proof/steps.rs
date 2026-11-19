//! The lines of a proof: introductions, reasons, methods and steps.

use super::*;
use crate::sorts;

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
pub(super) fn body_text(kind: Intro, text: &str) -> String {
    let rest = match text.strip_prefix(kind.as_str()) {
        Some(rest) if rest.starts_with(char::is_whitespace) => rest,
        _ => text,
    };
    str::trim(&sorts::unlabel(rest)).to_string()
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
    /// The line stands after its part's `by` line (`PartBy`): it opens the
    /// block of the method `by` names, not the part itself.
    pub after_by: bool,
}

/// A `by <method>` line in a part of a block, after the part's own openers
/// and before its first step: the part's steps prove what the part owes by
/// the block of that method, whose openers follow the line (`SYNTAX.md`,
/// Blocks). The method is `proof` or `contradiction`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartBy {
    /// The part, as `Opener::part` numbers it; None for a block with no
    /// parts.
    pub part: Option<usize>,
    pub method: Method,
    pub line: usize,
}

/// The openers of one part of a block, split at the part's `by` line.
pub struct PartOpening<'a> {
    /// The part's own openers, those its owner's method asks for.
    pub own: Vec<&'a Opener>,
    /// The part's `by` line, if it has one.
    pub by: Option<&'a PartBy>,
    /// The openers after the `by` line, which open its method's block.
    pub inner: Vec<&'a Opener>,
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
    /// The requires lines under the reason, giving what its item asks for.
    /// The reason is read as a requires line of the step below the let with
    /// these above it (`Reason::under`; `GRAMMAR.md`, a naming let with a
    /// kind).
    pub requires: Vec<Requires>,
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

    /// The step the reason of the let `label` is read under: `after`, the
    /// step below the let, with the let's requires lines and then the
    /// reason, showing `fact`, as its requires lines.
    pub fn under(&self, label: &str, after: &Step, fact: Written) -> Step {
        let mut requires = self.requires.clone();
        requires.push(self.shown(fact));
        Step {
            requires,
            reason_of: Some(label.to_string()),
            ..after.clone()
        }
    }
}

/// A requires line, `requires <fact>: <reason>`, cut into its fact and its
/// reason. The fact ends at the first colon written against the word before
/// it; a colon inside a fact stands apart, as in `g : [a, b] → ℝ` and
/// `{x ∈ ℕ : x > 1}`.
pub(super) fn requires_line(
    t: &str,
    path: &str,
    no: usize,
    names: &Arc<Names>,
) -> Checked<Requires> {
    let body = str::trim(&t["requires".len()..]);
    let chars: Vec<(usize, char)> = body.char_indices().collect();
    let split = chars.iter().enumerate().find_map(|(i, &(at, c))| {
        (c == ':' && i > 0 && !chars[i - 1].1.is_whitespace())
            .then(|| (&body[..at], &body[at + 1..]))
    });
    let Some((fact, how)) = split else {
        return Err(Problem::new(path, no, "requires line has no justification"));
    };
    Ok(Requires {
        fact: Written::new(str::trim(fact), path, no),
        how: str::trim(how).to_string(),
        line: no,
        by: cut_reason(how, path, no).map(|slots| {
            Justification::of(slots, no, names).shifted(skeleton::offset(t, how))
        }),
    })
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
        // A function's define says no kind: the numbers its values are
        // among are its rule's, and a later line says any other, wider or
        // narrower, with its own reason (`SYNTAX.md`).
        if !one.params.is_empty() {
            return Err(Problem::new(
                path,
                self.line,
                format!(
                    "let {} says a kind of number of a function; a function's define says none, and a line below it says which numbers its values are among, as `for all x ∈ D, {}(x) ∈ ℤ` or `{} : D → ℝ`",
                    self.label, one.name, one.name
                ),
            ));
        }
        let shown = Written::member(
            self.rule(&one.body),
            Written::new(set, path, self.line),
            path,
            reason.line,
        );
        Ok(Some(Kinded {
            label: self.label.clone(),
            name: one.name.clone(),
            set: set.clone(),
            shown: reason.shown(shown),
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
/// definition it names has `sort` and `metamath-builds` lines
/// (`link_functions`). It
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

/// A `forbid` line: an item the file does not import, named as an import of
/// it would name it, `forbid theorem stdlib/geometry/law-of-cosines`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Forbid {
    /// Its keywords as one text, which is the header of the record it names
    /// before the name: `mundane theorem`, `axiom`.
    pub said: String,
    pub module: String,
    pub name: String,
    pub line: usize,
}

impl Forbid {
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

/// A step's number, as the text writes it: 3.1.2. It has at least one
/// part, which `StepNo::new` holds, so its first and last parts are always
/// there to read; the step a theorem proved `by` a method is has no number,
/// and is `StepPlace::Theorem`, not a `StepNo`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StepNo(Vec<u32>);

impl StepNo {
    /// The number with these parts; None where there are none.
    pub fn new(parts: Vec<u32>) -> Option<StepNo> {
        (!parts.is_empty()).then_some(StepNo(parts))
    }

    /// A step at the top level, numbered `n`.
    pub fn top(n: u32) -> StepNo {
        StepNo(vec![n])
    }

    /// Step `n` in this step's block: 3.1 of 3.
    pub fn child(&self, n: u32) -> StepNo {
        self.joined(&[n])
    }

    /// This number with `rest` after it: 3.1.2 of 3 and [1, 2].
    pub fn joined(&self, rest: &[u32]) -> StepNo {
        let mut parts = self.0.clone();
        parts.extend_from_slice(rest);
        StepNo(parts)
    }

    pub fn parts(&self) -> &[u32] {
        &self.0
    }

    /// This number with its part `at` set to `value`: 4.5.1 of 4.2.1 for
    /// at = 1, value = 5.
    pub fn with(&self, at: usize, value: u32) -> StepNo {
        let mut parts = self.0.clone();
        parts[at] = value;
        StepNo(parts)
    }

    /// The place of the step whose block this one is in: the theorem's own
    /// step for a step at the top level.
    pub fn parent(&self) -> StepPlace {
        match StepNo::new(self.0[..self.0.len() - 1].to_vec()) {
            Some(number) => StepPlace::Step(number),
            None => StepPlace::Theorem,
        }
    }

    /// The first `k` parts, at least one: 3.1 of 3.1.2 for k = 2.
    pub fn prefix(&self, k: usize) -> StepNo {
        StepNo(self.0[..k.clamp(1, self.0.len())].to_vec())
    }

    /// How many parts the number has: 1 for a top-level step.
    pub fn depth(&self) -> usize {
        self.0.len()
    }

    /// The top-level step this one is in, or is: 3 of 3.1.2.
    pub fn first(&self) -> u32 {
        self.0[0]
    }

    pub fn last(&self) -> u32 {
        self.0[self.0.len() - 1]
    }

    /// Whether this number is `other` or a step in its block, at any depth.
    pub fn starts_with(&self, other: &StepNo) -> bool {
        self.0.starts_with(&other.0)
    }

    /// Parsed from a reference such as `3.1`; None where `text` is not a
    /// step number (`skeleton::is_number`).
    pub fn parse(text: &str) -> Option<StepNo> {
        if !skeleton::is_number(text) {
            return None;
        }
        let parts: Option<Vec<u32>> = text.split('.').map(|x| x.parse().ok()).collect();
        StepNo::new(parts?)
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

/// Where a step stands: the step a theorem proved `by` a method is, which
/// the page gives no number, or a numbered step. The theorem's step comes
/// before every numbered one, and every top-level step is in its block.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum StepPlace {
    Theorem,
    Step(StepNo),
}

impl StepPlace {
    /// The step's number; None for the theorem's own step.
    pub fn number(&self) -> Option<&StepNo> {
        match self {
            StepPlace::Theorem => None,
            StepPlace::Step(number) => Some(number),
        }
    }

    pub fn is_theorem(&self) -> bool {
        matches!(self, StepPlace::Theorem)
    }

    /// How deep the step stands: 0 for the theorem's own step, 1 for a
    /// top-level step.
    pub fn depth(&self) -> usize {
        self.number().map_or(0, StepNo::depth)
    }

    /// The place `k` levels down the way to this step: the theorem's own
    /// step for k = 0, the top-level step for k = 1.
    pub fn prefix(&self, k: usize) -> StepPlace {
        match self {
            StepPlace::Step(number) if k > 0 => StepPlace::Step(number.prefix(k)),
            _ => StepPlace::Theorem,
        }
    }

    /// The place of the step whose block this one is in; the theorem's own
    /// step is in no block, and is given its own place again.
    pub fn parent(&self) -> StepPlace {
        match self {
            StepPlace::Theorem => StepPlace::Theorem,
            StepPlace::Step(number) => number.parent(),
        }
    }

    /// Step `n` in this step's block: step `n` at the top level for the
    /// theorem's own step.
    pub fn child(&self, n: u32) -> StepNo {
        match self {
            StepPlace::Theorem => StepNo::top(n),
            StepPlace::Step(number) => number.child(n),
        }
    }

    /// Whether the step at `other` is this one or in its block, at any depth:
    /// every step is in the theorem's.
    pub fn contains(&self, other: &StepPlace) -> bool {
        match (self, other) {
            (StepPlace::Theorem, _) => true,
            (StepPlace::Step(_), StepPlace::Theorem) => false,
            (StepPlace::Step(mine), StepPlace::Step(theirs)) => {
                theirs.starts_with(mine)
            }
        }
    }
}

impl PartialEq<StepNo> for StepPlace {
    fn eq(&self, other: &StepNo) -> bool {
        self.number() == Some(other)
    }
}

impl From<StepNo> for StepPlace {
    fn from(number: StepNo) -> StepPlace {
        StepPlace::Step(number)
    }
}

/// A numbered step as its number; the theorem's own step, which the page
/// gives none, as `the theorem`.
impl fmt::Display for StepPlace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StepPlace::Theorem => f.write_str("the theorem"),
            StepPlace::Step(number) => number.fmt(f),
        }
    }
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
    /// Every line and label it names, `contradicting`'s among them, each
    /// with where it is written in the text the reader was given: the
    /// step's line, from `line` on, or a requires line's reason.
    pub cited: Vec<Cite>,
}

impl Justification {
    /// A justification as the skeleton reader cut it, read in a file whose
    /// citations mean what `names` says.
    pub fn of(slots: Slots, line: usize, names: &Arc<Names>) -> Justification {
        Justification {
            refs: slots.refs(),
            cited: slots.cited,
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

    /// The justification read from text that starts `by` bytes into its
    /// line, with what it cites placed in the line.
    pub fn shifted(mut self, by: usize) -> Justification {
        for c in &mut self.cited {
            c.at += by;
        }
        self
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

/// One step of a proof: a numbered one, or the step a theorem proved `by` a
/// method is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub number: StepPlace,
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
    /// The `by` lines of its block's parts, at most one a part.
    pub by_lines: Vec<PartBy>,
    /// The claim says `, which is impossible`: a closed fact `arithmetic`
    /// shows false, which ends a contradiction block on this step.
    pub impossible: bool,
    /// The label of the let whose reason this is, read as the step it would
    /// be (`Reason::under`), so that a message names the let; None for a step
    /// the proof writes.
    pub reason_of: Option<String>,
}

impl Step {
    pub fn claim_text(&self) -> String {
        self.claim.text().to_string()
    }

    /// The step as a message names it: `step 4`, `let D1` for a let's
    /// reason read as a step, or `the theorem` for the step a theorem proved
    /// `by` a method is (`proves_theorem`).
    pub fn called(&self) -> String {
        match &self.reason_of {
            Some(label) => format!("let {label}"),
            None if self.proves_theorem() => "the theorem".to_string(),
            None => format!("step {}", self.number),
        }
    }

    /// The openers of `part` of its block (None for a block with no parts),
    /// split at the part's `by` line.
    pub fn opening(&self, part: Option<usize>) -> PartOpening<'_> {
        let (inner, own) = self
            .openers
            .iter()
            .filter(|o| o.part == part)
            .partition(|o| o.after_by);
        PartOpening {
            own,
            by: self.by_lines.iter().find(|b| b.part == part),
            inner,
        }
    }

    /// A part of its block as a message names it: `case 2 of step 4`, `the
    /// step part of step 3`, `direction 1 of the theorem`; for a block with
    /// no parts, `the proof block of step 4`, or the step itself.
    pub fn part_called(&self, part: Option<usize>) -> String {
        let called = self.called();
        let Some(index) = part else {
            return if self.just.head.is(Method::Proof) {
                format!("the proof block of {called}")
            } else {
                called
            };
        };
        let Some((marker, _)) = self.parts.get(index) else {
            return called;
        };
        let nth = self.parts[..=index]
            .iter()
            .filter(|(m, _)| m == marker)
            .count();
        match marker.as_str() {
            "case" | "direction" => format!("{marker} {nth} of {called}"),
            _ => format!("the {marker} part of {called}"),
        }
    }

    /// The method whose block `part` of its block ends: the part's `by`
    /// method, or else the step's own.
    pub fn closing(&self, part: Option<usize>) -> Option<Method> {
        match self.by_lines.iter().find(|b| b.part == part) {
            Some(by) => Some(by.method),
            None => self.just.head.method(),
        }
    }

    /// Whether this is the step a theorem proved `by` a method is: at
    /// `StepPlace::Theorem`, its claim the theorem's conclusion, and every
    /// step of the proof in its block.
    pub fn proves_theorem(&self) -> bool {
        self.number.is_theorem() && self.reason_of.is_none()
    }

    /// What the step is, in a message: `step`, or `let`.
    pub fn kind_word(&self) -> &'static str {
        if self.reason_of.is_some() {
            "let"
        } else {
            "step"
        }
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
