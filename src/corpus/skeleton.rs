//! The skeleton reader's cut of a justification (`GRAMMAR.md`,
//! Justifications): its head, and the slots that head admits, read word by
//! word by the productions. A justification is cut here once, and what
//! leaves is its slots: nothing after this reads a justification's text.
//!
//! The words of a justification are whole words. `into` is the word before
//! a substitute's destination and never the end of an item's name, as in
//! `mun:function-into`, and `algebra` is a head where `algebraic` is not.

use super::proof::{Head, ItemKind, Manipulation, Method, StepNo, METHODS};
use super::values::Given;
use crate::formula::page::Written;
use crate::matching::split_commas;
use crate::outcome::{Checked, Problem};
use crate::text::{prefix, repr};

/// A line or a label a slot names: `line 3` or `H4`, or a slip, a number
/// with no `line` or `line` before a label, which names its word and cites
/// nothing, since the line matches no production.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Place {
    Line(String),
    Label(String),
    Slip(String),
}

impl Place {
    /// The number or label as the line writes it.
    pub fn named(&self) -> &str {
        match self {
            Place::Line(w) | Place::Label(w) | Place::Slip(w) => w,
        }
    }

    /// The line or label cited, where the place is no slip.
    pub fn cited(&self) -> Option<&str> {
        match self {
            Place::Line(w) | Place::Label(w) => Some(w),
            Place::Slip(_) => None,
        }
    }
}

/// Where a substitute takes its equation from: a line or a label,
/// `(arithmetic)` for an equation of numerals alone, or `(real arithmetic)`
/// for a closed equation with a square root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Source {
    At(Place),
    Arithmetic,
    RealArithmetic,
}

impl Source {
    /// The line or label the equation comes from, as the line writes it;
    /// the method's name for an equation worked out where it stands.
    pub fn named(&self) -> &str {
        match self {
            Source::At(place) => place.named(),
            Source::Arithmetic => "arithmetic",
            Source::RealArithmetic => "real arithmetic",
        }
    }
}

/// A justification as the productions cut it: the head, and each slot the
/// line fills. A line that matches no production still has the slots its
/// words fill, so that a check reading one of them reports what it finds,
/// and says why in `unproduced`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Slots {
    pub head: Head,
    /// The text cut, without a `, contradicting N` after it.
    pub text: String,
    /// The define's label, where the head is one.
    pub defined: Option<String>,
    /// What an `obtain` names, in order.
    pub obtained: Vec<String>,
    /// The item an `obtain` takes its objects from, `thm:x`.
    pub obtained_from: Option<String>,
    /// The values given what the justification cites, in order.
    pub(crate) values: Vec<Given>,
    /// The `from` slot's lines and labels, in order: the one line of `from
    /// line N`, or the list.
    pub from: Vec<String>,
    /// What is wrong with a line that matches no production, where the
    /// reader can say: the `from` entry that is neither a line nor a label.
    hint: Option<String>,
    /// A substitute's equation, as written.
    pub equation: Option<Written>,
    /// Where a substitute takes its equation from.
    pub source: Option<Source>,
    /// The line or label a substitute puts its equation into.
    pub into: Option<Place>,
    /// An instantiate's `in …`: a line, a label, or an item.
    pub target: Option<String>,
    /// The letter an induction is on.
    pub on: Option<String>,
    /// Where an induction starts, `starting at m`.
    pub start: Option<String>,
    /// A `join`'s lines and labels.
    pub joined: Vec<String>,
    /// The line the step's claim is the opposite of, `contradicting 3.6`.
    pub contradicting: Option<String>,
    /// Why the justification matches no production; None where it matches
    /// one.
    pub unproduced: Option<String>,
    /// Every line and label the justification names, `contradicting`'s
    /// among them, each with where it is written in the text the reader was
    /// given (`cut`, `cut_reason`).
    pub cited: Vec<Cite>,
    origin: Origin,
}

/// What a citation names: a step, by its number, or a labelled line, by
/// its label, `H3`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Cited {
    Line(StepNo),
    Label(String),
}

/// A line or label a reading names, and where it is written: `len` bytes
/// from `at` in the text the reader was given.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cite {
    pub cited: Cited,
    pub at: usize,
    pub len: usize,
}

/// `written`, a citation found `at` bytes into its text: a step where it is
/// a number, and a labelled line otherwise.
pub fn cite_at(written: &str, at: usize) -> Cite {
    let cited = if is_number(written) {
        Cited::Line(StepNo::parse(written))
    } else {
        Cited::Label(written.to_string())
    };
    Cite {
        cited,
        at,
        len: written.len(),
    }
}

/// Where in memory the text a reading was cut from starts. Every slot is cut
/// from a slice of that text, so a slot's own address less this one is
/// where the slot is written. Two readings of one text are one reading
/// wherever the text is held, so the address takes no part in comparing
/// them.
#[derive(Clone, Copy)]
struct Origin(usize);

impl PartialEq for Origin {
    fn eq(&self, _: &Origin) -> bool {
        true
    }
}

impl Eq for Origin {}

impl std::fmt::Debug for Origin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Origin")
    }
}

impl Slots {
    /// A head with every slot empty, over `text`.
    pub(crate) fn new(head: Head, text: &str) -> Slots {
        Slots {
            origin: Origin(text.as_ptr() as usize),
            cited: Vec::new(),
            head,
            text: text.to_string(),
            defined: None,
            obtained: Vec::new(),
            obtained_from: None,
            values: Vec::new(),
            from: Vec::new(),
            hint: None,
            equation: None,
            source: None,
            into: None,
            target: None,
            on: None,
            start: None,
            joined: Vec::new(),
            contradicting: None,
            unproduced: None,
        }
    }

    /// Note that the reading names `piece`, a slice of the text it was cut
    /// from, where it is written.
    fn cite(&mut self, piece: &str) {
        let at = (piece.as_ptr() as usize)
            .checked_sub(self.origin.0)
            .expect("a cited piece is a slice of the text cut");
        self.cited.push(cite_at(piece, at));
    }

    /// A `from` entry, noted as cited.
    fn push_from(&mut self, piece: &str) {
        self.from.push(piece.to_string());
        self.cite(piece);
    }

    /// The citations of a reading cut from a slice of this one's text, each
    /// placed in this one's.
    fn absorb(&mut self, inner: &Slots) {
        let by = inner.origin.0 - self.origin.0;
        self.cited.extend(inner.cited.iter().map(|c| Cite {
            at: c.at + by,
            ..c.clone()
        }));
    }

    /// Each citation placed in `given`, the text the reader was handed, of
    /// which the text cut is a slice.
    fn placed_in(mut self, given: &str) -> Slots {
        let by = self.origin.0 - given.as_ptr() as usize;
        for c in &mut self.cited {
            c.at += by;
        }
        self.origin = Origin(given.as_ptr() as usize);
        self
    }

    /// Every line and label the justification names, in the order it names
    /// them: a define's label, the `from` slot, a substitute's source and
    /// destination, an instantiate's target where it is no item, and a
    /// `join`'s list.
    pub fn refs(&self) -> Vec<String> {
        let mut out: Vec<String> = self.defined.iter().cloned().collect();
        out.extend(self.from.iter().cloned());
        if let Some(Source::At(place)) = &self.source {
            out.extend(place.cited().map(String::from));
        }
        out.extend(self.into.as_ref().and_then(Place::cited).map(String::from));
        if let Some(t) = &self.target {
            if item_kind(t).is_none() {
                out.push(t.clone());
            }
        }
        out.extend(self.joined.iter().cloned());
        out
    }

    /// The line does not match its head's production, with what is wrong,
    /// unless an earlier finding already says so.
    fn unproduced(&mut self, hint: Option<String>) {
        if self.unproduced.is_some() {
            return;
        }
        self.hint.clone_from(&hint);
        let text = repr(prefix(&self.text, 64));
        self.unproduced = Some(match hint {
            Some(hint) => {
                format!(
                    "justification matches no production in GRAMMAR.md: {text}; {hint}"
                )
            }
            None => {
                format!("justification matches no production in GRAMMAR.md: {text}")
            }
        });
    }
}

/// Whether a word is a step's number, `3.1.2`.
pub fn is_number(word: &str) -> bool {
    !word.is_empty()
        && word
            .split('.')
            .all(|part| !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()))
}

/// Whether a word is a label, `H2` or `IH`: capitals, then digits.
pub fn is_label(word: &str) -> bool {
    let capitals = word.bytes().take_while(u8::is_ascii_uppercase).count();
    capitals > 0 && word.bytes().skip(capitals).all(|b| b.is_ascii_digit())
}

/// Whether a word names a line a citation may name: a number or a label.
pub fn is_ref(word: &str) -> bool {
    is_number(word) || is_label(word)
}

/// Whether a word is an item's or a theorem's name: a letter, then letters,
/// digits and hyphens. It may open with a Greek letter, since a library
/// function is named by its record and a formula writes it, as σ.
pub fn is_name(word: &str) -> bool {
    let mut chars = word.chars();
    match chars.next() {
        Some(first) if first.is_ascii_alphabetic() || ('α'..='ω').contains(&first) => {
            chars.all(|c| c.is_ascii_alphanumeric() || c == '-')
        }
        _ => false,
    }
}

/// Whether a word is what follows an item's prefix: a name, or a path of
/// names, so that a citation written by its path is read as one.
fn is_cited(word: &str) -> bool {
    word.split('/').all(is_name)
}

/// The kind a citation's prefix names, `thm:x` a theorem; None for a word
/// with no prefix of an item.
pub fn item_kind(word: &str) -> Option<ItemKind> {
    let (prefix, _) = word.split_once(':')?;
    ItemKind::from_prefix(prefix)
}

/// The method a word is the head of; `both` is one only before
/// `directions`.
fn method_of(first: &str, second: Option<&str>) -> Option<Method> {
    METHODS.iter().copied().find(|m| {
        let mut words = m.as_str().split(' ');
        words.next() == Some(first) && words.next().is_none_or(|w| Some(w) == second)
    })
}

/// Whether a line opens a justification: its first word is an item's
/// prefix with a name, or a method (`GRAMMAR.md`, the heads).
pub fn starts_with_head(text: &str) -> bool {
    let mut words = text.split_whitespace();
    let Some(first) = words.next() else {
        return false;
    };
    // A comma may end a head's last word, `real arithmetic, from 2`, as it
    // may end a head of one word.
    let first = first.trim_end_matches(',');
    let second = words.next().map(|w| w.trim_end_matches(','));
    item_kind(first).is_some() || method_of(first, second).is_some()
}

/// An induction's hypothesis as its line writes it, `assume step N is true
/// for k, the induction hypothesis (IH)`: the induction's step, and the
/// letter it is for.
pub struct InductionHypothesis<'t> {
    pub step: &'t str,
    pub letter: &'t str,
}

/// The line read as an induction's hypothesis; None for any other line.
pub fn induction_hypothesis(text: &str) -> Option<InductionHypothesis<'_>> {
    let (said, rest) = text.split_once(',')?;
    let ["assume", "step", step, "is", "true", "for", letter] =
        said.split_whitespace().collect::<Vec<_>>()[..]
    else {
        return None;
    };
    let ["the", "induction", "hypothesis", label] =
        rest.split_whitespace().collect::<Vec<_>>()[..]
    else {
        return None;
    };
    label_at_end(label)?;
    Some(InductionHypothesis { step, letter })
}

/// What a case's line says before `, which is the claim (C1)`: a case that
/// is the claim of the block it opens; None for any other line.
pub fn which_is_the_claim(text: &str) -> Option<&str> {
    let pieces = split_commas(text);
    let [.., last] = pieces.as_slice() else {
        return None;
    };
    if pieces.len() < 2 {
        return None;
    }
    let ["which", "is", "the", "claim", label] =
        last.split_whitespace().collect::<Vec<_>>()[..]
    else {
        return None;
    };
    label_at_end(label)?;
    let before = text[..offset(text, last)].trim_end();
    Some(str::trim(before.strip_suffix(',').unwrap_or(before)))
}

/// Whether a word is one letter, Latin or Greek, with any subscript or
/// prime: what a range line ranges and a `let` may put in a set.
pub fn is_letter_name(word: &str) -> bool {
    let mut chars = word.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    let a_letter = first.is_ascii_alphabetic() || ('α'..='ω').contains(&first);
    a_letter && chars.all(|c| ('₀'..='₉').contains(&c) || c == '′')
}

/// A range line, `ε, δ range over ℝ`: the letters it ranges, and the set.
pub struct RangeLine<'t> {
    pub letters: Vec<&'t str>,
    pub set: &'t str,
}

/// The line read as a range; None for any other line.
pub fn range_line(text: &str) -> Option<RangeLine<'_>> {
    let text = text.trim();
    let mut words = text.split_whitespace().peekable();
    while let Some(word) = words.next() {
        if !matches!(word, "range" | "ranges") || words.peek() != Some(&"over") {
            continue;
        }
        let at = offset(text, word);
        let letters: Vec<&str> = text[..at].split(',').map(str::trim).collect();
        let set = after_words(&text[at..], 2);
        let named = at > 0 && letters.iter().all(|l| is_letter_name(l));
        return (named && !set.is_empty()).then_some(RangeLine { letters, set });
    }
    None
}

/// What `text` writes after its first `n` words, from the next word on.
fn after_words(text: &str, n: usize) -> &str {
    let mut rest = text.trim_start();
    for _ in 0..n {
        let end = rest.find(char::is_whitespace).unwrap_or(rest.len());
        rest = rest[end..].trim_start();
    }
    rest
}

/// An `import` line: `import [mundane] <kind> <module>/<name> [as <alias>]
/// [(<label>)]`.
pub struct ImportLine<'t> {
    pub mundane: bool,
    /// The header word of what it names, as the line writes it.
    pub kind: &'t str,
    /// The module and the name, `stdlib/divisibility/prime-factor`.
    pub full: &'t str,
    pub alias: Option<&'t str>,
    pub label: Option<&'t str>,
}

/// The line read as an import; None where it takes no import's shape. The
/// words after `import` are read with `mundane` as the mark first, and as
/// the kind where the line reads no other way.
pub fn import_line(text: &str) -> Option<ImportLine<'_>> {
    let words: Vec<&str> = text.split_whitespace().collect();
    let ["import", rest @ ..] = words.as_slice() else {
        return None;
    };
    if let ["mundane", after @ ..] = rest {
        if let Some(import) = import_rest(after, true) {
            return Some(import);
        }
    }
    import_rest(rest, false)
}

/// The words after `import` and its mark: the kind, the path, and an alias
/// and a label where the line gives them.
fn import_rest<'t>(words: &[&'t str], mundane: bool) -> Option<ImportLine<'t>> {
    let [kind, full, rest @ ..] = words else {
        return None;
    };
    let (alias, rest) = match rest {
        ["as", alias, rest @ ..] if !alias.contains(['(', ')']) => (Some(*alias), rest),
        _ => (None, rest),
    };
    let label = match rest {
        [] => None,
        [label] => Some(label_at_end(label)?),
        _ => return None,
    };
    imported_path(full).then_some(ImportLine {
        mundane,
        kind,
        full,
        alias,
        label,
    })
}

/// Whether a path names what an import brings in: modules by item names,
/// and last the name, which for a define is the one letter a formula writes
/// and may be Greek, with digits, subscripts, primes and hyphens after it.
fn imported_path(full: &str) -> bool {
    let (modules, last) = match full.rsplit_once('/') {
        Some((modules, last)) => (Some(modules), last),
        None => (None, full),
    };
    let mut chars = last.chars();
    let opens = chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || ('α'..='ω').contains(&c));
    let rest = chars.all(|c| {
        c.is_ascii_alphanumeric()
            || ('α'..='ω').contains(&c)
            || ('₀'..='₉').contains(&c)
            || c == '′'
            || c == '-'
    });
    opens && rest && modules.is_none_or(|m| m.split('/').all(is_name))
}

/// A step's first line, `3.1.  x = 2`: its number, and its claim as far as
/// the line writes it.
pub struct StepLine<'t> {
    pub number: &'t str,
    pub claim: &'t str,
}

/// The line read as a step's first line; None for any other line.
pub fn step_line(text: &str) -> Option<StepLine<'_>> {
    let first = text.split_whitespace().next()?;
    let rest = text.strip_prefix(first)?;
    let number = first.strip_suffix('.')?;
    (is_number(number) && rest.starts_with(char::is_whitespace)).then(|| StepLine {
        number,
        claim: rest.trim_start(),
    })
}

/// A claim without `, which is impossible` after it: a closed fact
/// `arithmetic` shows false, which ends a contradiction block on the step;
/// None for a claim that says no such thing.
pub fn which_is_impossible(text: &str) -> Option<&str> {
    let pieces = split_commas(text);
    let [.., last] = pieces.as_slice() else {
        return None;
    };
    if pieces.len() < 2 || last.split_whitespace().ne(["which", "is", "impossible"]) {
        return None;
    }
    let before = text[..offset(text, last)].trim_end();
    Some(str::trim(before.strip_suffix(',').unwrap_or(before)))
}

/// The number a line opens with where it opens as a step does, a word
/// ending in a full stop, and the number has letters in it, `1.6a.`, which
/// no step has; None for any other line.
pub fn misnumbered(text: &str) -> Option<&str> {
    let first = text.split_whitespace().next()?;
    let number = first.strip_suffix('.')?;
    let digits = number
        .find(|c: char| !c.is_ascii_digit() && c != '.')
        .unwrap_or(number.len());
    let opens = number.starts_with(|c: char| c.is_ascii_digit());
    let lettered = number[digits..].starts_with(|c: char| c.is_ascii_alphabetic());
    (opens && lettered).then_some(number)
}

/// The label a line closes on, `(H2)`: its last word, which stands apart
/// from what it labels, so `M(X)` ending a line is M applied to X and not
/// a line labelled X.
pub fn label_at_end(text: &str) -> Option<&str> {
    let last = text.split_whitespace().last()?;
    let label = last.strip_prefix('(')?.strip_suffix(')')?;
    is_label(label).then_some(label)
}

/// The line without the label it closes on, and without the space before
/// it; the line as it is where it closes on none.
pub fn without_label(text: &str) -> &str {
    if label_at_end(text).is_none() {
        return text;
    }
    let body = text.trim_end();
    let last = body.split_whitespace().last().unwrap_or_default();
    body[..body.len() - last.len()].trim_end()
}

/// The words that open a reason a calculation's line gives other than a
/// line or a label (`GRAMMAR.md`, calculation chains). None of them is
/// ever a word of a term, so the first of them a line writes after its
/// term is where its reason starts.
const CHAIN_REASONS: [&str; 4] = ["algebra", "arithmetic", "substitute", "instantiate"];

/// A calculation line's reason, as written after its term (`GRAMMAR.md`,
/// calculation chains). It starts at the line's first word, after the
/// first, that opens a reason a chain line gives: `algebra`, `arithmetic`,
/// `real arithmetic`, `substitute`, `instantiate`, or an item's citation,
/// `mun:x`. A line writing none of these gives a line or a label, its last
/// word. None where it gives neither.
pub fn chain_reason(text: &str) -> Option<&str> {
    let body = text.trim_end();
    let words: Vec<(usize, &str)> = body
        .split_whitespace()
        .map(|w| (offset(body, w), w))
        .collect();
    for (i, &(at, word)) in words.iter().enumerate().skip(1) {
        let word = word.trim_end_matches(',');
        let next = words.get(i + 1).map(|(_, w)| w.trim_end_matches(','));
        let opens = CHAIN_REASONS.contains(&word)
            || (word == "real" && next == Some("arithmetic"))
            || item_kind(word).is_some();
        if opens {
            return Some(&body[at..]);
        }
    }
    let &(at, last) = words.last()?;
    is_ref(last).then_some(&body[at..])
}

/// A chain line's term and the modulus a `≡` line says after it, `1·10
/// (mod 3)`: the term before the first `(mod`, and what the line closes
/// the bracket on.
pub fn chain_modulus(rest: &str) -> (&str, Option<&str>) {
    let Some(inner) = rest.strip_suffix(')') else {
        return (rest, None);
    };
    let Some(at) = inner.find("(mod") else {
        return (rest, None);
    };
    match after_word(&inner[at + 1..], "mod") {
        Some(modulus) if !modulus.is_empty() => (inner[..at].trim_end(), Some(modulus)),
        _ => (rest, None),
    }
}

/// Whether a line is a justification: it opens with a head, or it is a
/// define's label in scope, alone or with `from` (`GRAMMAR.md`, Steps). A
/// claim runs until the first such line.
pub fn is_justification(text: &str, labels: &Labels) -> bool {
    starts_with_head(text)
        || cites_define(text, &labels.defines)
        || cited_phrase(text, labels).is_some()
}

/// Whether a line is headed by a define's label: the label of a define in
/// scope, alone or with `from`, since a claim may begin with a capital as a
/// label does.
fn cites_define(text: &str, defines: &[String]) -> bool {
    let pieces: Vec<&str> = split_commas(text).into_iter().map(str::trim).collect();
    let Some((first, rest)) = pieces.split_first() else {
        return false;
    };
    is_label(first)
        && defines.iter().any(|d| d == first)
        && rest.first().is_none_or(|p| after_word(p, "from").is_some())
}

/// What follows `word` at the start of `text`, where `text` opens with that
/// whole word.
fn after_word<'t>(text: &'t str, word: &str) -> Option<&'t str> {
    let rest = text.strip_prefix(word)?;
    if rest.is_empty() {
        return Some(rest);
    }
    rest.starts_with(char::is_whitespace)
        .then(|| rest.trim_start())
}

/// Where `piece`, a slice of `text`, starts in it.
pub(crate) fn offset(text: &str, piece: &str) -> usize {
    piece.as_ptr() as usize - text.as_ptr() as usize
}

/// The labels a justification may open with: those of the defines in scope,
/// each cited alone or with `from`, and those of the file's defines of
/// phrases, each cited as the item its define stands for.
#[derive(Clone, Debug, Default)]
pub struct Labels {
    pub defines: Vec<String>,
    pub phrases: Vec<PhraseLabel>,
}

/// A define of a phrase's label, and the item a line opening with it cites:
/// `D1` cites `def:triangular-number`.
#[derive(Clone, Debug)]
pub struct PhraseLabel {
    pub label: String,
    pub kind: ItemKind,
    pub name: String,
}

/// The phrase label a justification opens with, followed by a space, a
/// comma or nothing; None where it opens otherwise.
fn cited_phrase<'l>(text: &str, labels: &'l Labels) -> Option<&'l PhraseLabel> {
    let first = text.split([' ', ',']).next()?;
    labels.phrases.iter().find(|p| p.label == first)
}

/// Cut a justification, on `line` of `path`, into its head and slots.
/// `labels` are the labels of the defines in scope, which a line headed
/// by one cites. A line opening with no head is a defect of the file.
pub fn cut(given: &str, path: &str, line: usize, labels: &Labels) -> Checked<Slots> {
    let text = str::trim(given);
    // A step reaching the opposite of an earlier line says so after its
    // reasons, `inequalities, from 3.1, contradicting 3.6`; the rest is
    // read as any other line.
    let pieces = split_commas(text);
    let (said, contradicting) = match pieces.as_slice() {
        [.., last] if pieces.len() > 1 => {
            match after_word(str::trim(last), "contradicting") {
                Some(r) if is_ref(r) => {
                    let before = text[..offset(text, last)].trim_end();
                    let before = str::trim(before.strip_suffix(',').unwrap_or(before));
                    (before, Some(r))
                }
                _ => (text, None),
            }
        }
        _ => (text, None),
    };
    let mut slots = head_and_slots(said, path, line, labels)?;
    if let Some(r) = contradicting {
        slots.contradicting = Some(r.to_string());
        slots.cite(r);
    }
    Ok(slots.placed_in(given))
}

/// Cut a requires line's reason, or a let's: a justification as a step's,
/// or the lines it rests on and nothing else, `from 8`.
pub fn cut_reason(given: &str, path: &str, line: usize) -> Checked<Slots> {
    let text = str::trim(given);
    // A manipulation of the one line it cites, `weakening, from 2.1`
    // (`GRAMMAR.md`, requires lines).
    if let Some((made, rest)) = Manipulation::opening(text) {
        let rest = str::trim(rest.strip_prefix(',').unwrap_or(rest));
        let pieces: Vec<&str> = split_commas(rest).into_iter().map(str::trim).collect();
        let mut slots = Slots::new(Head::Manipulation(made), text);
        from_slot(&pieces, &mut slots);
        if slots.from.len() != 1 {
            slots.unproduced(None);
        }
        return Ok(slots.placed_in(given));
    }
    if after_word(text, "from").is_some() {
        let pieces: Vec<&str> = split_commas(text).into_iter().map(str::trim).collect();
        let mut slots = Slots::new(Head::Lines, text);
        from_slot(&pieces, &mut slots);
        return Ok(slots.placed_in(given));
    }
    cut(given, path, line, &Labels::default())
}

fn head_and_slots(
    text: &str,
    path: &str,
    line: usize,
    labels: &Labels,
) -> Checked<Slots> {
    let no_head = || {
        Problem::new(
            path,
            line,
            format!("no justification head in {}", repr(prefix(text, 40))),
        )
    };
    let pieces: Vec<&str> = split_commas(text).into_iter().map(str::trim).collect();
    let Some(&first) = pieces.first() else {
        return Err(no_head());
    };
    let mut words = first.split_whitespace();
    let word = words.next().unwrap_or_default();
    let second = words.next();
    if item_kind(word).is_some() {
        let mut slots = Slots::new(Head::Define, text);
        let head = item(text, path, line, &mut slots).ok_or_else(no_head)?;
        slots.head = head;
        return Ok(slots);
    }
    if let Some(method) = method_of(word, second) {
        let mut slots = Slots::new(Head::Method(method), text);
        method_slots(method, text, &pieces, path, line, &mut slots);
        return Ok(slots);
    }
    if cites_define(text, &labels.defines) {
        let mut slots = Slots::new(Head::Define, text);
        slots.defined = Some(first.to_string());
        slots.cite(first);
        from_slot(&pieces[1..], &mut slots);
        return Ok(slots);
    }
    // A phrase's label cites the item its define stands for, with values
    // and lines as a citation of the item writes them.
    if let Some(p) = cited_phrase(text, labels) {
        let mut slots = Slots::new(Head::Define, text);
        let head =
            item_given(text, word, p.kind, p.name.clone(), path, line, &mut slots);
        slots.head = head;
        return Ok(slots);
    }
    Err(no_head())
}

/// The slots of a citation of an item, `prefix:cited [values] [, from …]`,
/// written in `text`: the head it reads, or None where the prefix names no
/// item. An obtain's citation is read here too, after its names.
fn item(text: &str, path: &str, line: usize, slots: &mut Slots) -> Option<Head> {
    let pieces: Vec<&str> = split_commas(text).into_iter().map(str::trim).collect();
    let first = pieces.first()?;
    let word = first.split_whitespace().next()?;
    let (prefix, name) = word.split_once(':')?;
    let kind = ItemKind::from_prefix(prefix)?;
    let cited: String = name
        .chars()
        .take_while(|c| {
            c.is_ascii_alphanumeric()
                || *c == '-'
                || *c == '/'
                || ('α'..='ω').contains(c)
        })
        .collect();
    if cited.is_empty() || !is_cited(&cited) {
        return None;
    }
    if cited.len() != name.len() {
        slots.unproduced(None);
    }
    Some(item_given(text, word, kind, cited, path, line, slots))
}

/// The slots of a citation of an item whose head, `word`, the caller has
/// read as citing `cited` of `kind`: the values after it and the lines
/// after `from`.
fn item_given(
    text: &str,
    word: &str,
    kind: ItemKind,
    cited: String,
    path: &str,
    line: usize,
    slots: &mut Slots,
) -> Head {
    let pieces: Vec<&str> = split_commas(text).into_iter().map(str::trim).collect();
    let from_at = pieces
        .iter()
        .position(|p| after_word(p, "from").is_some())
        .unwrap_or(pieces.len())
        .max(1);
    let values_start = offset_in(text, word) + word.len();
    let values_end = pieces
        .get(from_at)
        .map_or(text.len(), |p| offset_in(text, p));
    let values = text[values_start..values_end].trim().trim_end_matches(',');
    namings(values, path, line, slots);
    from_slot(&pieces[from_at..], slots);
    Head::Item { kind, cited }
}

/// Where `part`, a slice of `base`, starts in it.
fn offset_in(base: &str, part: &str) -> usize {
    part.as_ptr() as usize - base.as_ptr() as usize
}

/// Whether a piece of a justification opens a naming, `v := …`: a name
/// and nothing else before `:=`.
fn opens_naming(piece: &str) -> bool {
    piece.split_once(":=").is_some_and(|(name, _)| {
        let name = name.trim();
        !name.is_empty() && !name.contains(char::is_whitespace)
    })
}

/// `values` cut into its namings, at each comma outside brackets that opens
/// the next one: a comma that does not belongs to the value before it, so
/// `P := A, B, C are collinear, Q := x = 1` is two namings (`GRAMMAR.md`,
/// Justifications).
pub fn naming_pieces(values: &str) -> Vec<&str> {
    let mut spans: Vec<std::ops::Range<usize>> = Vec::new();
    for piece in split_commas(values) {
        let start = offset_in(values, piece);
        let end = start + piece.len();
        match spans.last_mut() {
            Some(span) if !opens_naming(piece) => span.end = end,
            _ => spans.push(start..end),
        }
    }
    spans.into_iter().map(|span| values[span].trim()).collect()
}

/// The values a line gives, each `v := t`; a piece of another shape is
/// left out, and the line matches no production.
fn namings(values: &str, path: &str, line: usize, slots: &mut Slots) {
    for piece in naming_pieces(values) {
        match piece.split_once(":=") {
            Some((name, value))
                if !str::trim(name).is_empty()
                    && !str::trim(name).contains(char::is_whitespace)
                    && !str::trim(value).is_empty() =>
            {
                slots.values.push(Given {
                    name: str::trim(name).to_string(),
                    value: Written::new(str::trim(value), path, line),
                });
            }
            _ => slots.unproduced(None),
        }
    }
}

/// The `from` slot, as the pieces after the rest of a line write it: `from
/// line N`, or `from` and a list of lines and labels. Nothing at all is no
/// `from` slot; anything else matches no production.
fn from_slot(pieces: &[&str], slots: &mut Slots) {
    let Some((first, rest)) = pieces.split_first() else {
        return;
    };
    let Some(first) = after_word(first, "from") else {
        slots.unproduced(None);
        return;
    };
    if let Some(number) = after_word(first, "line") {
        if is_number(number) && rest.is_empty() {
            slots.push_from(number);
            return;
        }
    }
    for entry in std::iter::once(first).chain(rest.iter().copied()) {
        if is_ref(entry) {
            slots.push_from(entry);
        } else {
            slots.unproduced(Some(format!(
                "`from` names {}, which is neither a line nor a label",
                repr(entry)
            )));
            return;
        }
    }
    if slots.from.is_empty() {
        slots.unproduced(None);
    }
}

/// A line or a label after `in` or `into`, as the productions write one:
/// `line N`, or a label alone. A number with no `line`, or `line` before a
/// label, is the slip most often made, and is named as one.
fn place(after: &str, word: &str, slots: &mut Slots) -> Option<Place> {
    if let Some(number) = after_word(after, "line") {
        if is_number(number) {
            slots.cite(number);
            return Some(Place::Line(number.to_string()));
        }
        if is_label(number) {
            slots.unproduced(Some(format!(
                "a label never carries the word \"line\": `{word} {number}`"
            )));
            slots.cite(number);
            return Some(Place::Slip(number.to_string()));
        }
    }
    if is_label(after) {
        slots.cite(after);
        return Some(Place::Label(after.to_string()));
    }
    if is_number(after) {
        slots.unproduced(Some(format!(
            "a line number after `{word}` carries the word \"line\": `{word} line {after}`"
        )));
        slots.cite(after);
        return Some(Place::Slip(after.to_string()));
    }
    slots.unproduced(None);
    None
}

fn method_slots(
    method: Method,
    text: &str,
    pieces: &[&str],
    path: &str,
    line: usize,
    slots: &mut Slots,
) {
    let head = method.as_str();
    let rest = after_word(text, head).unwrap_or_default();
    match method {
        Method::Obtain => obtain(rest, path, line, slots),
        Method::Substitute => substitute(rest, path, line, slots),
        Method::Instantiate => instantiate(rest, pieces, path, line, slots),
        Method::Join | Method::Restate => {
            let listed = after_word(pieces[0], head).unwrap_or_default();
            for entry in std::iter::once(listed).chain(pieces[1..].iter().copied()) {
                if is_ref(entry) {
                    slots.joined.push(entry.to_string());
                    slots.cite(entry);
                } else {
                    slots.unproduced(None);
                }
            }
            if slots.joined.is_empty() {
                slots.unproduced(None);
            }
        }
        Method::Induction => {
            let words: Vec<&str> = rest.split_whitespace().collect();
            match words.as_slice() {
                ["on", letter, "starting", "at", start] => {
                    slots.on = Some(letter.to_string());
                    slots.start = Some(start.trim_end_matches(',').to_string());
                }
                _ => {
                    if let ["on", letter, ..] = words.as_slice() {
                        slots.on = Some(letter.to_string());
                    }
                    if let Some(i) =
                        words.windows(2).position(|w| w == ["starting", "at"])
                    {
                        slots.start = words
                            .get(i + 2)
                            .map(|s| s.trim_end_matches(',').to_string());
                    }
                    slots.unproduced(None);
                }
            }
        }
        // A method that takes nothing.
        Method::Arithmetic
        | Method::RealArithmetic
        | Method::Contradiction
        | Method::Proof
        | Method::BothDirections
        | Method::Calculation => {
            if pieces.len() > 1 || pieces[0] != head {
                slots.unproduced(None);
            }
        }
        // A method that takes a `from` slot, which `exhibit` and `cases`
        // must have.
        Method::Exhibit
        | Method::Cases
        | Method::Transitivity
        | Method::Antisymmetry
        | Method::Algebra
        | Method::Inequalities
        | Method::Membership
        | Method::Inspection => {
            let own = after_word(pieces[0], head).unwrap_or_default();
            if own.is_empty() {
                from_slot(&pieces[1..], slots);
            } else {
                // `algebra from 1` wants its comma, and its list is read
                // as the list it would be.
                let mut list = vec![own];
                list.extend(pieces[1..].iter().copied());
                from_slot(&list, slots);
                slots.unproduced(None);
            }
            let needs_from = matches!(
                method,
                Method::Exhibit
                    | Method::Cases
                    | Method::Transitivity
                    | Method::Antisymmetry
            );
            if needs_from && slots.from.is_empty() {
                slots.unproduced(None);
            }
        }
    }
}

/// `obtain` names its objects and says where they come from: with a colon
/// and an item, `obtain q, r: thm:division-algorithm …`, or from one line,
/// `obtain q, r from line 1`.
fn obtain(rest: &str, path: &str, line: usize, slots: &mut Slots) {
    let colon = rest
        .char_indices()
        .find(|&(i, c)| c == ':' && !rest[i + 1..].starts_with('='))
        .map(|(i, _)| i);
    if let Some(at) = colon {
        let names = &rest[..at];
        if names.contains(":=") || names.split_whitespace().any(|w| w == "from") {
            return obtain_from_line(rest, slots);
        }
        names_into(names, slots);
        let cited = str::trim(&rest[at + 1..]);
        let mut inner = Slots::new(Head::Define, cited);
        match item(cited, path, line, &mut inner) {
            Some(head) => {
                slots.obtained_from = Some(head.to_string());
                slots.absorb(&inner);
                slots.values = inner.values;
                slots.from = inner.from;
                if inner.unproduced.is_some() {
                    slots.unproduced(inner.hint);
                }
            }
            None => slots.unproduced(None),
        }
        return;
    }
    obtain_from_line(rest, slots)
}

/// The second form, `obtain q, r from line 1`, or `from` a label.
fn obtain_from_line(rest: &str, slots: &mut Slots) {
    let words: Vec<&str> = rest.split_whitespace().collect();
    let Some(at) = words.iter().rposition(|w| *w == "from") else {
        slots.unproduced(None);
        return;
    };
    names_into(&words[..at].join(" "), slots);
    match &words[at + 1..] {
        ["line", number] if is_number(number) => slots.push_from(number),
        [label] if is_label(label) => slots.push_from(label),
        [number] if is_number(number) => {
            slots.push_from(number);
            slots.unproduced(Some(format!(
                "an obtain naming no item takes its line with the word \"line\": `from line {number}`"
            )));
        }
        _ => slots.unproduced(None),
    }
}

/// The names an `obtain` takes, `q, r`, each one word.
fn names_into(names: &str, slots: &mut Slots) {
    for name in names.split(',').map(str::trim) {
        if name.is_empty() || name.contains(char::is_whitespace) {
            slots.unproduced(None);
        } else {
            slots.obtained.push(name.to_string());
        }
    }
    if slots.obtained.is_empty() {
        slots.unproduced(None);
    }
}

/// `substitute <equation> (<source>) [into <destination>]`. The source is
/// the bracket closing the equation that the line ends with, or that only
/// `into` and its destination follow; a bracket of the equation's own,
/// `f(y)`, is followed by more of it.
fn substitute(rest: &str, path: &str, line: usize, slots: &mut Slots) {
    // `substitute line 3` and `substitute H3` write no equation: it is the
    // one the line says, and the move it makes is seen between the two
    // terms it is written between, a chain's or a row's.
    let short = match after_word(rest, "line") {
        Some(number) if is_number(number) => {
            Some((Place::Line(number.to_string()), number))
        }
        _ => is_label(rest).then(|| (Place::Label(rest.to_string()), rest)),
    };
    if let Some((place, written)) = short {
        slots.source = Some(Source::At(place));
        slots.cite(written);
        return;
    }
    // `substitute` alone writes its rows below it (`GRAMMAR.md`, substitute
    // rows): each row's reason says what it puts for what.
    if rest.trim().is_empty() {
        return;
    }
    let mut found = None;
    for (open, c) in rest.char_indices() {
        if c != '(' {
            continue;
        }
        let Some(close) = rest[open + 1..].find([')', '(']).map(|i| open + 1 + i)
        else {
            continue;
        };
        if !rest[close..].starts_with(')') {
            continue;
        }
        let tail = &rest[close + 1..];
        let into = tail
            .starts_with(char::is_whitespace)
            .then(|| after_word(tail.trim_start(), "into"))
            .flatten()
            .filter(|d| !d.is_empty());
        if tail.trim().is_empty() || into.is_some() {
            found = Some((open, close, into));
            break;
        }
    }
    let Some((open, close, into)) = found else {
        slots.unproduced(None);
        return;
    };
    let equation = rest[..open].trim_end();
    slots.equation = Some(Written::new(equation, path, line));
    let group = str::trim(&rest[open + 1..close]);
    slots.source = if group == "arithmetic" {
        Some(Source::Arithmetic)
    } else if group == "real arithmetic" {
        Some(Source::RealArithmetic)
    } else if let Some(number) = after_word(group, "line") {
        if is_number(number) {
            slots.cite(number);
            Some(Source::At(Place::Line(number.to_string())))
        } else if is_label(number) {
            slots.unproduced(Some(format!(
                "a label never carries the word \"line\": `({number})`"
            )));
            slots.cite(number);
            Some(Source::At(Place::Slip(number.to_string())))
        } else {
            slots.unproduced(None);
            None
        }
    } else if is_label(group) {
        slots.cite(group);
        Some(Source::At(Place::Label(group.to_string())))
    } else {
        slots.unproduced(None);
        None
    };
    if let Some(destination) = into {
        slots.into = place(destination, "into", slots);
    }
    // A substitute takes one equation from one source: a second would be
    // read as part of the equation, which no formula writes.
    let sources = slots.text.matches("(arithmetic)").count()
        + slots.text.matches("(real arithmetic)").count()
        + slots
            .text
            .match_indices("(line ")
            .filter(|(i, m)| {
                slots.text[i + m.len()..].starts_with(|c: char| c.is_ascii_digit())
            })
            .count();
    if sources > 1 || equation.is_empty() {
        slots.unproduced(None);
    }
}

/// `instantiate <values> in <target> [, from …]`: the values run to the
/// first `in` that a line, a label or an item follows.
fn instantiate(
    rest: &str,
    pieces: &[&str],
    path: &str,
    line: usize,
    slots: &mut Slots,
) {
    let from_at = pieces
        .iter()
        .position(|p| after_word(p, "from").is_some())
        .unwrap_or(pieces.len());
    let end = pieces.get(from_at).map_or(rest.len(), |p| offset(rest, p));
    let region = str::trim(rest[..end].trim_end().trim_end_matches(','));
    let words: Vec<(usize, &str)> = region
        .split_whitespace()
        .map(|w| (offset(region, w), w))
        .collect();
    let mut at_in = None;
    for (k, (i, w)) in words.iter().enumerate() {
        if *w != "in" || k == 0 {
            continue;
        }
        let after = str::trim(&region[i + 2..]);
        let lands = after_word(after, "line").is_some()
            || item_kind(after).is_some()
            || words.get(k + 1).is_some_and(|(_, next)| is_label(next));
        if lands {
            at_in = Some((*i, after));
            break;
        }
    }
    let (values, target) = match at_in {
        Some((i, after)) => (region[..i].trim_end(), Some(after)),
        None => (region, None),
    };
    namings(values, path, line, slots);
    if slots.values.is_empty() {
        slots.unproduced(None);
    }
    match target {
        Some(after) if item_kind(after).is_some() => {
            slots.target =
                Some(after.split_whitespace().next().unwrap_or(after).to_string());
            slots.unproduced(None);
        }
        Some(after) => {
            slots.target =
                place(after, "in", slots).and_then(|p| p.cited().map(String::from))
        }
        None => slots.unproduced(None),
    }
    from_slot(&pieces[from_at..], slots);
}
