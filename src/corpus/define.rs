//! What a `define` line says.

use indexmap::IndexMap;

use crate::formula::page::{Case, Written};
use crate::outcome::{Built, Declined, Route};
use crate::text::{repr, squash};

/// What a `define` line says: a name, and the term it stands for.
///
/// A name with a parameter is a function, as a reader writes
/// "S(m) = 1 + 2 + … + m": `define S(m) := Σ(j = 1 to m) j, for m ∈ ℕ`. Its
/// domain is said with it, because a rule without one says what S does and
/// not where S is defined. A function of two arguments says each one's
/// domain in order: `define G(a, n) := Σ(j = 0 to n) a^j, for a ∈ ℝ, n ∈
/// ℕ₀`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Define {
    pub name: String,
    pub body: RuleText,
    /// The arguments, in the order the name takes them; none for a name
    /// that stands for a term.
    pub params: Vec<Param>,
    /// What kind of number a let says its name is, in a reader's words:
    /// `let m = gcd(s, w), a natural number`. The reason is the line under
    /// it (`DefineLine::reason`).
    pub kind: Option<String>,
}

/// One argument of a defined function, and the set it runs over.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    /// The set written after `∈` or `⊆`.
    pub domain: String,
    /// Whether the argument is a member of the set written, or one of its
    /// parts: `for X ⊆ A` runs X over 𝒫A.
    pub within: Within,
    /// The `for` piece as written, `X ⊆ A`.
    pub said: String,
}

/// How a define's argument runs over the set its `for` piece writes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Within {
    /// `for x ∈ A`: over the members of A.
    Members,
    /// `for X ⊆ A`: over the parts of A, the members of 𝒫A.
    Parts,
}

impl Param {
    /// The set written, where the argument runs over its members; None
    /// where it runs over its parts.
    pub fn member_of(&self) -> Option<&str> {
        (self.within == Within::Members).then_some(self.domain.as_str())
    }

    /// The set the argument runs over, as the formula it is, written at
    /// `line` of `path`: the set written, read where a set is wanted, or
    /// for `X ⊆ A` the parts of A, made from the tree of A.
    pub fn domain_written(&self, path: &str, line: usize) -> Written {
        let set = Written::set(Written::new(self.domain.as_str(), path, line));
        match self.within {
            Within::Members => set,
            Within::Parts => Written::parts(self.said.as_str(), set, path, line),
        }
    }
}

/// A define's rule as written: one term, or a term by cases.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuleText {
    /// One term, its lines joined where the comma rule wraps it.
    Term(String),
    /// A term by cases, one case to a line and the last taken `otherwise`
    /// (`SYNTAX.md`).
    Cases(Cases),
}

/// The lines of a define by cases.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cases {
    /// The lines as written, joined, for a message.
    pub written: String,
    /// Each case before the last, in order.
    pub cases: Vec<CaseText>,
    /// The value taken otherwise.
    pub otherwise: String,
}

/// One case of a define by cases, `value if condition`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaseText {
    pub value: String,
    pub condition: String,
}

impl RuleText {
    /// The rule as written, for a message.
    pub fn text(&self) -> &str {
        match self {
            RuleText::Term(t) => t,
            RuleText::Cases(c) => &c.written,
        }
    }

    /// The rule as the formula it is, written at `line` of `path`: a rule
    /// by cases is made from each case's value and condition.
    pub fn written(&self, path: &str, line: usize) -> Written {
        let at = |text: &str| Written::new(text, path, line);
        match self {
            RuleText::Term(t) => at(t),
            RuleText::Cases(c) => Written::cases(
                c.written.as_str(),
                c.cases
                    .iter()
                    .map(|case| Case {
                        value: at(&case.value),
                        condition: at(&case.condition),
                    })
                    .collect(),
                at(&c.otherwise),
                path,
                line,
            ),
        }
    }
}

/// What a `define` of sequences by recursion says: each name's value at 0,
/// and its value at k + 1 in terms of the values at k.
///
/// `define a(0) := M, b(0) := N, a(k + 1) := b(k), b(k + 1) := a(k) mod
/// b(k), for k ∈ ℕ₀` defines two sequences together, as a textbook writes
/// Euclid's algorithm; one name alone is the same form with one sequence.
/// `start` and `step` hold each name's rule as written, a term or by cases
/// as a `Define`'s is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Recursion {
    pub names: Vec<String>,
    pub index: String,
    pub domain: String,
    pub start: IndexMap<String, RuleText>,
    pub step: IndexMap<String, RuleText>,
}

/// What a define of a phrase says: `define triangular-number: n is a
/// triangular number means n ∈ ℕ and there is k ∈ ℕ with n = k(k + 1)/2`.
/// The phrase is a new way to say something, and the meaning is what it
/// says (`SYNTAX.md`, "A define may name a phrase").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Phrase {
    /// The name it is imported and cited by, `triangular-number`.
    pub name: String,
    /// Whether it is taken for granted, which only the library's are.
    pub mundane: bool,
    /// The phrase as written, one piece to a word.
    pub pieces: Vec<Piece>,
    /// The meaning as written, its lines joined.
    pub meaning: String,
}

/// One piece of a phrase: a slot, a slot joined to the word after it by a
/// hyphen, or a word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Piece {
    /// A letter standing where a term stands: n in "n is a triangular
    /// number".
    Slot(String),
    /// A letter joined to the word after it, which takes only a letter or a
    /// numeral: p in "p-subgroup".
    Attached {
        slot: String,
        word: String,
    },
    Word(String),
}

impl Phrase {
    /// The slots in the order the phrase writes them.
    pub fn slots(&self) -> Vec<&str> {
        self.pieces
            .iter()
            .filter_map(|p| match p {
                Piece::Slot(s) | Piece::Attached { slot: s, .. } => Some(s.as_str()),
                Piece::Word(_) => None,
            })
            .collect()
    }

    /// The pattern a notation record writes for it, `_ is a triangular
    /// number`, each slot a hole.
    pub fn pattern(&self) -> String {
        self.pieces
            .iter()
            .map(|p| match p {
                Piece::Slot(_) => "_".to_string(),
                Piece::Attached { word, .. } => format!("_-{word}"),
                Piece::Word(w) => w.clone(),
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// The pattern of its negation, `_ is not a triangular number`: "not"
    /// after the "is" every phrase opens with.
    pub fn negated_pattern(&self) -> String {
        self.pattern().replacen(" is ", " is not ", 1)
    }

    /// The phrase as written, with its own letters in its slots.
    pub fn written(&self) -> String {
        self.pieces
            .iter()
            .map(|p| match p {
                Piece::Slot(s) => s.clone(),
                Piece::Attached { slot, word } => format!("{slot}-{word}"),
                Piece::Word(w) => w.clone(),
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// The words between its slots, for a message and for the reads line
    /// of its notation: `is a triangular number`.
    pub fn words(&self) -> Vec<&str> {
        self.pieces
            .iter()
            .filter_map(|p| match p {
                Piece::Word(w) | Piece::Attached { word: w, .. } => Some(w.as_str()),
                Piece::Slot(_) => None,
            })
            .collect()
    }
}

/// A define read into its parts: one name, sequences by recursion, or a
/// phrase.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefineParts {
    One(Define),
    Recursion(Recursion),
    Phrase(Phrase),
}

impl DefineParts {
    /// The names the define gives: a phrase gives none, since what it gives
    /// is a way of saying something.
    pub fn names(&self) -> Vec<String> {
        match self {
            DefineParts::One(d) => vec![d.name.clone()],
            DefineParts::Recursion(r) => r.names.clone(),
            DefineParts::Phrase(_) => Vec::new(),
        }
    }

    /// The one define, where this is not a recursion.
    pub fn one(&self) -> Option<&Define> {
        match self {
            DefineParts::One(d) => Some(d),
            DefineParts::Recursion(_) | DefineParts::Phrase(_) => None,
        }
    }

    pub fn recursion(&self) -> Option<&Recursion> {
        match self {
            DefineParts::Recursion(r) => Some(r),
            DefineParts::One(_) | DefineParts::Phrase(_) => None,
        }
    }

    pub fn phrase(&self) -> Option<&Phrase> {
        match self {
            DefineParts::Phrase(p) => Some(p),
            DefineParts::One(_) | DefineParts::Recursion(_) => None,
        }
    }

    /// The name, where there is one: a recursion has no one name, and none
    /// of its callers asks one of it.
    pub fn name(&self) -> Option<&str> {
        self.one().map(|d| d.name.as_str())
    }
}

/// A naming line cut into its parts: `define T(k) := k(k + 1)/2, for k ∈ ℕ`
/// names T, takes k, and says its rule and its domain.
struct NamingLine<'t> {
    name: &'t str,
    /// What the brackets after the name hold, where it takes arguments.
    params: Option<&'t str>,
    /// The rule, up to the first `, for`.
    body: &'t str,
    /// What follows `, for`, where the line says a domain.
    fors: Option<&'t str>,
}

/// The line read as a naming line, `define` or `let` and a name, perhaps
/// applied, then `:=` or `=` and a rule; None for any other line. Which
/// sign it gives with is `define_parts`'s to ask of the whole line.
fn naming_line(text: &str) -> Option<NamingLine<'_>> {
    let rest = ["define", "let"].iter().find_map(|word| {
        text.strip_prefix(word)
            .filter(|r| r.starts_with(char::is_whitespace))
    })?;
    let rest = rest.trim_start();
    let name_end = rest
        .find(|c: char| c.is_whitespace() || c == '(')
        .unwrap_or(rest.len());
    let (name, mut rest) = rest.split_at(name_end);
    let mut params = None;
    if let Some(inside) = rest.strip_prefix('(') {
        let close = inside.find([')', '('])?;
        if !inside[close..].starts_with(')') || close == 0 {
            return None;
        }
        params = Some(&inside[..close]);
        rest = &inside[close + 1..];
    }
    let rest = rest.trim_start();
    let gives = if rest.starts_with(":=") { ":=" } else { "=" };
    let rest = rest.strip_prefix(gives)?.trim_start();
    if name.is_empty() || rest.is_empty() {
        return None;
    }
    let (body, fors) = match for_clause(rest) {
        Some((body, fors)) => (body, Some(fors)),
        None => (rest, None),
    };
    Some(NamingLine {
        name,
        params,
        body,
        fors,
    })
}

/// Where a rule's `, for` clause begins: a comma, then the word `for` and
/// what follows it; the rule before it and the clause after `for`.
fn for_clause(text: &str) -> Option<(&str, &str)> {
    text.match_indices(',').find_map(|(at, _)| {
        let after = text[at + 1..].trim_start().strip_prefix("for")?;
        let fors = after.strip_prefix(char::is_whitespace)?.trim_start();
        (at > 0 && !fors.is_empty()).then_some((&text[..at], fors))
    })
}

/// One argument's domain in a define's `for` clause, `m ∈ ℕ₀` or `X ⊆ A`.
struct ForOne<'t> {
    over: &'t str,
    /// `∈` or `⊆`.
    how: char,
    domain: &'t str,
}

/// A `for` piece read as one argument's domain; None for any other piece.
fn for_one(piece: &str) -> Option<ForOne<'_>> {
    let at = piece.find(['∈', '⊆'])?;
    let how = piece[at..].chars().next()?;
    let over = piece[..at].trim();
    let domain = piece[at + how.len_utf8()..].trim();
    let one_word = !over.is_empty() && !over.contains(char::is_whitespace);
    (one_word && !domain.is_empty()).then_some(ForOne { over, how, domain })
}

/// A case of a define by cases, `value if condition`.
struct CaseLine<'t> {
    value: &'t str,
    condition: &'t str,
}

/// A line read as a case, at its first word `if`; None for any other line.
fn case_of(line: &str) -> Option<CaseLine<'_>> {
    let word = line.split_whitespace().skip(1).find(|w| *w == "if")?;
    let at = word.as_ptr() as usize - line.as_ptr() as usize;
    let value = line[..at].trim_end();
    let condition = line[at + 2..].trim_start();
    (!value.is_empty() && !condition.is_empty())
        .then_some(CaseLine { value, condition })
}

/// The value of a define's last case, the one taken `otherwise`; None for
/// a line that does not end so.
fn otherwise_of(line: &str) -> Option<&str> {
    let value = line.strip_suffix("otherwise")?;
    let value = value.strip_suffix(char::is_whitespace)?.trim_end();
    (!value.is_empty()).then_some(value)
}

/// The head of one rule of a recursion, `a(k + 1) :=`: where it starts, at
/// the start of the rules or at the comma before it, where its rule starts,
/// the sequence's name, and the index it is said at.
struct RuleHead<'t> {
    start: usize,
    end: usize,
    name: &'t str,
    at: &'t str,
}

/// Every rule head a recursion's rules write, in order; a rule runs from
/// its head to the next.
fn rule_heads(body: &str) -> Vec<RuleHead<'_>> {
    let mut out: Vec<RuleHead> = Vec::new();
    let starts = std::iter::once(0).chain(body.match_indices(',').map(|(i, _)| i));
    for start in starts {
        if out.last().is_some_and(|h| start < h.end) {
            continue;
        }
        let from = if start == 0 && !body.starts_with(',') {
            0
        } else {
            start + 1
        };
        if let Some(head) = rule_head(body, start, from) {
            out.push(head);
        }
    }
    out
}

/// The rule head written at `from` in `body`, its match starting at
/// `start`; None where none is written there.
fn rule_head(body: &str, start: usize, from: usize) -> Option<RuleHead<'_>> {
    let text = &body[from..];
    let lead = text.len() - text.trim_start().len();
    let text = text.trim_start();
    let open = text.find('(')?;
    let name = &text[..open];
    if !super::skeleton::is_letter_name(name) {
        return None;
    }
    let inside = &text[open + 1..];
    let close = inside.find([')', '('])?;
    if !inside[close..].starts_with(')') {
        return None;
    }
    let after = &inside[close + 1..];
    let gap = after.len() - after.trim_start().len();
    let gives = after.trim_start();
    let gives_len = if gives.starts_with(":=") {
        2
    } else if gives.starts_with('=') {
        1
    } else {
        return None;
    };
    let end = from + lead + open + 1 + close + 1 + gap + gives_len;
    Some(RuleHead {
        start,
        end,
        name,
        at: &inside[..close],
    })
}

/// A recursion's closing `, for k ∈ ℕ₀`: where it starts, the index and the
/// domain.
struct RecursionFor<'t> {
    start: usize,
    index: &'t str,
    domain: &'t str,
}

/// The closing `for` of a recursion's text; None where it ends otherwise.
fn recursion_for(said: &str) -> Option<RecursionFor<'_>> {
    said.match_indices(',').find_map(|(start, _)| {
        let after = said[start + 1..].trim_start().strip_prefix("for")?;
        let after = after.strip_prefix(char::is_whitespace)?;
        let (index, domain) = after.split_once('∈')?;
        let (index, domain) = (index.trim(), domain.trim());
        (one_word(index) && one_word(domain)).then_some(RecursionFor {
            start,
            index,
            domain,
        })
    })
}

/// Whether `text` is one word.
fn one_word(text: &str) -> bool {
    !text.is_empty() && !text.contains(char::is_whitespace)
}

/// Whether a `let` line names: a name, perhaps applied, and `=`, or the
/// `:=` a let does not take, which `define_parts` then reports. Any other
/// `let` takes a member of a set, or a letter of a sort.
fn let_names_a_term(text: &str) -> bool {
    let Some(rest) = text
        .strip_prefix("let")
        .filter(|r| r.starts_with(char::is_whitespace))
    else {
        return false;
    };
    let rest = rest.trim_start();
    let name_end = rest
        .find(|c: char| c.is_whitespace() || "(=∈∉⊆:".contains(c))
        .unwrap_or(rest.len());
    if name_end == 0 {
        return false;
    }
    let mut rest = &rest[name_end..];
    if let Some(inside) = rest.strip_prefix('(') {
        let Some(close) = inside.find([')', '(']) else {
            return false;
        };
        if !inside[close..].starts_with(')') {
            return false;
        }
        rest = &inside[close + 1..];
    }
    let rest = rest.trim_start();
    let rest = rest.strip_prefix(':').unwrap_or(rest);
    rest.strip_prefix('=')
        .and_then(|after| after.chars().next())
        .is_some_and(|c| c != '=')
}

/// Whether a define opens a recursion: its first rule is said at 0,
/// `define a(0) := …`.
fn opens_recursion(said: &str) -> bool {
    let Some(rest) = ["define", "let"].iter().find_map(|word| {
        said.strip_prefix(word)
            .filter(|r| r.starts_with(char::is_whitespace))
    }) else {
        return false;
    };
    rule_head(rest, 0, 0).is_some_and(|head| head.at == "0")
}

/// Which word a naming line opens with (`SYNTAX.md`): `define`, for a name
/// the file gives and another may import, written outside every theorem; or
/// `let` followed by `=`, for a name one theorem gives, written inside it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Naming {
    Define,
    Let,
}

impl Naming {
    /// The word itself.
    pub fn word(self) -> &'static str {
        match self {
            Naming::Define => "define",
            Naming::Let => "let",
        }
    }

    /// What the word puts between a name and what it names.
    pub fn gives(self) -> &'static str {
        match self {
            Naming::Define => ":=",
            Naming::Let => "=",
        }
    }
}

/// The word a naming line opens with, or None for a line that names
/// nothing: `let x ∈ ℝ` takes any member and is no naming line.
pub fn naming(text: &str) -> Option<Naming> {
    if text.starts_with("define ") || text.starts_with("mundane define ") {
        return Some(Naming::Define);
    }
    let_names_a_term(text).then_some(Naming::Let)
}

/// A define's `for` clause split at the commas that separate its arguments,
/// and not at those inside a domain: `a ∈ ℝ, x ∈ [a, b]` is two pieces. An
/// application's arguments split the same way: `G(a, f(x, y))` takes two.
pub fn for_pieces(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut piece = String::new();
    for c in text.chars() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ => {}
        }
        if c == ',' && depth == 0 {
            out.push(str::trim(&piece).to_string());
            piece.clear();
        } else {
            piece.push(c);
        }
    }
    out.push(str::trim(&piece).to_string());
    out
}
/// The lines of a define by cases: each value and its condition, and the
/// value otherwise; or a decline saying which line is not a case.
fn by_cases(lines: &[&str]) -> Route<RuleText> {
    let Some(last) = otherwise_of(lines[lines.len() - 1]) else {
        return Route::no(
            "the last line of a define by cases is its value `otherwise`",
        );
    };
    let mut cases = Vec::new();
    for line in &lines[..lines.len() - 1] {
        let Some(case) = case_of(line) else {
            return Route::no(format!(
                "{} is not a case: write the value, then `if` and the condition it is taken under",
                repr(line)
            ));
        };
        cases.push(CaseText {
            value: case.value.to_string(),
            condition: case.condition.to_string(),
        });
    }
    Built(RuleText::Cases(Cases {
        written: lines.join(" "),
        cases,
        otherwise: last.to_string(),
    }))
}

/// One rule as written: its lines joined, or by cases where its last line
/// is taken `otherwise`.
fn rule_term(text: &str) -> Route<RuleText> {
    let trimmed = str::trim(text).trim_end_matches(',');
    let pieces: Vec<&str> = trimmed.split('\n').map(str::trim).collect();
    if pieces.len() > 1 && otherwise_of(pieces[pieces.len() - 1]).is_some() {
        return by_cases(&pieces);
    }
    Built(RuleText::Term(pieces.join(" ")))
}

/// The index value at which an argument is a recursion's step: `a(m + 1)`
/// is the step rule at m (`SYNTAX.md`: a value at 0 and a rule from k to
/// k + 1). None for any other argument, the value at 0 among them. A rule
/// is read by this, and so is an application of the sequence.
pub fn step_index(arg: &str) -> Option<String> {
    squash(arg)
        .strip_suffix(" + 1")
        .map(|index| str::trim(index).to_string())
}

/// A define of sequences by recursion, without its label, read into its
/// parts; or a decline saying what is wrong with it.
fn recursion_parts(said: &str) -> Route<DefineParts> {
    let Some(closing) = recursion_for(said) else {
        return Route::no(
            "a define by recursion ends `, for k ∈ ℕ₀`, naming the index its rules are written in",
        );
    };
    let index = closing.index.to_string();
    let domain = closing.domain.to_string();
    if domain != "ℕ₀" {
        return Route::no(format!(
            "a define by recursion starts at 0, so its index runs over ℕ₀, not {domain}"
        ));
    }
    let word = naming(said).map_or("define", Naming::word);
    let body = &said[word.len()..closing.start];
    let heads = rule_heads(body);
    let mut names: Vec<String> = Vec::new();
    let mut start: IndexMap<String, RuleText> = IndexMap::new();
    let mut step: IndexMap<String, RuleText> = IndexMap::new();
    for (i, head) in heads.iter().enumerate() {
        let name = head.name.to_string();
        let at = squash(head.at);
        let end = heads.get(i + 1).map(|after| after.start);
        let from = head.end;
        let text = match end {
            Some(end) => &body[from..end],
            None => &body[from..],
        };
        let rule = match rule_term(text) {
            Built(rule) => rule,
            Declined(d) => return Declined(d),
        };
        let table = if at == "0" {
            &mut start
        } else if step_index(&at).as_deref() == Some(index.as_str()) {
            &mut step
        } else {
            return Route::no(format!(
                "{name}({at}) is neither {name}(0) nor {name}({index} + 1): a rule gives a value at 0 or at the step"
            ));
        };
        if table.contains_key(&name) {
            return Route::no(format!("{name}({at}) is given twice"));
        }
        table.insert(name.clone(), rule);
        if !names.contains(&name) {
            names.push(name);
        }
    }
    for name in &names {
        if !start.contains_key(name) {
            return Route::no(format!("{name} has no value at 0"));
        }
        if !step.contains_key(name) {
            return Route::no(format!("{name} has no rule for {name}({index} + 1)"));
        }
    }
    Built(DefineParts::Recursion(Recursion {
        names,
        index,
        domain,
        start,
        step,
    }))
}

// What a define may be called: one name as the lexer reads one, a letter
// with perhaps a subscript or a prime. A longer name is read as several.
/// Whether a define, or a definition imported under another name, may be
/// called this (`skeleton::is_letter_name`).
pub fn is_one_name(name: &str) -> bool {
    super::skeleton::is_letter_name(name)
}

/// A `define` line, without its label, read into its parts; or a decline
/// saying what is wrong with it. A define whose first rule is said at 0 is
/// a recursion; any other is one name.
pub fn define_parts(text: &str) -> Route<DefineParts> {
    let said = str::trim(super::skeleton::without_label(text));
    if let Some(head) = phrase_head(said) {
        return phrase_parts(head);
    }
    if said.starts_with("mundane ") {
        return Route::no(
            "only a define of a phrase is marked mundane: `mundane define <name>: <phrase> means <meaning>`",
        );
    }
    // A define gives its name with `:=` and a let with `=`, as a textbook's
    // "let x₁ = …" does.
    match naming(said) {
        Some(Naming::Let) if said.contains(":=") => {
            return Route::no("a let names with `=`, and `:=` is a define's");
        }
        Some(Naming::Define) if !said.contains(":=") => {
            return Route::no("a define names with `:=`, and `=` is a let's");
        }
        _ => {}
    }
    if opens_recursion(said) {
        return recursion_parts(said);
    }
    let m = match naming_line(said) {
        Some(m) if !str::trim(m.body).is_empty() => m,
        _ => {
            return Route::no(
                "a naming line says `let <name> = <term>`, or `define <name> := <term>` outside the theorems",
            )
        }
    };
    let name = m.name.to_string();
    // Every name on the page is a letter, so `avg(x)` is three names and never
    // the function a define called `avg` would give.
    if !is_one_name(&name) {
        return Route::no(format!(
            "a define names one letter, perhaps with a subscript or a prime, and {} is not one",
            repr(&name)
        ));
    }
    let names: Vec<String> = m
        .params
        .map(|p| p.split(',').map(|n| str::trim(n).to_string()).collect())
        .unwrap_or_default();
    let fors: Vec<String> = m.fors.map(for_pieces).unwrap_or_default();
    let (body, kind) = match kind_said(str::trim(m.body)) {
        Some((body, kind)) => (body, Some(kind)),
        None => (str::trim(m.body), None),
    };
    if kind.is_some() && naming(said) == Some(Naming::Define) {
        return Route::no(
            "a define says no kind of number: a let says one, with its reason on the line under it",
        );
    }
    if kind.is_some() && !names.is_empty() {
        return Route::no(format!(
            "let {name}({}) says a kind of number, and a function is no number",
            names.join(", ")
        ));
    }
    // A define over several lines is either one term wrapped by the comma
    // rule, or a function by cases, one case to a line.
    let pieces: Vec<&str> = body.split('\n').map(str::trim).collect();
    let body = if pieces.len() > 1 && otherwise_of(pieces[pieces.len() - 1]).is_some() {
        match by_cases(&pieces) {
            Built(rule) => rule,
            Declined(d) => return Declined(d),
        }
    } else {
        RuleText::Term(pieces.join(" "))
    };
    let said = names.join(", ");
    if let Some(bad) = names.iter().find(|n| !is_one_name(n)) {
        return Route::no(format!(
            "define {name}({said}) takes {}, which is not one letter",
            repr(bad)
        ));
    }
    if names.is_empty() && !fors.is_empty() {
        return Route::no(format!(
            "define {name} gives a domain and takes no argument"
        ));
    }
    if !names.is_empty() && fors.is_empty() {
        let first = &names[0];
        return Route::no(format!(
            "define {name}({said}) says no domain: write `, for {first} ∈ …` after its rule"
        ));
    }
    let mut params = Vec::new();
    for (at, piece) in fors.iter().enumerate() {
        let Some(f) = for_one(piece) else {
            return Route::no(format!(
                "define {name}({said}) says `for {piece}`, which is not `x ∈ D`"
            ));
        };
        if names.get(at).map(String::as_str) != Some(f.over) {
            return Route::no(format!(
                "define {name}({said}) gives the domain of {}",
                f.over
            ));
        }
        // `for X ⊆ A` is `for X ∈ 𝒫A`: X runs over the parts of A.
        let within = if f.how == '⊆' {
            Within::Parts
        } else {
            Within::Members
        };
        params.push(Param {
            name: f.over.to_string(),
            domain: squash(f.domain),
            within,
            said: piece.clone(),
        });
    }
    if params.len() != names.len() {
        return Route::no(format!(
            "define {name}({said}) says the domain of {} of its {} arguments",
            params.len(),
            names.len()
        ));
    }
    if params.len() > 2 {
        return Route::no(format!(
            "define {name}({said}) takes {} arguments, and a function here takes one or two",
            params.len()
        ));
    }
    Built(DefineParts::One(Define {
        name,
        body,
        params,
        kind,
    }))
}

/// The opening of a define of a phrase: whether it is marked mundane, its
/// name, and what follows the colon after the name.
struct PhraseHead<'t> {
    mundane: bool,
    name: &'t str,
    rest: &'t str,
}

/// The line read as a define of a phrase, `define <name>: …`, where the
/// define's first word is a name closed by a colon; None for any other
/// line. A define of a term names a letter, which takes no colon.
fn phrase_head(said: &str) -> Option<PhraseHead<'_>> {
    let (mundane, rest) = match said.strip_prefix("mundane ") {
        Some(rest) => (true, rest.trim_start()),
        None => (false, said),
    };
    let rest = rest.strip_prefix("define")?;
    let rest = rest.strip_prefix(char::is_whitespace)?.trim_start();
    let first = rest.split_whitespace().next()?;
    let name = first.strip_suffix(':')?;
    super::skeleton::is_name(name).then_some(PhraseHead {
        mundane,
        name,
        rest: rest[first.len()..].trim_start(),
    })
}

/// A define of a phrase read into its parts; or a decline saying what is
/// wrong with it. The phrase opens with a slot, `is` and `a` or `an`, then a
/// word or an attached slot; a word of two letters or more is a word, a
/// letter a slot, and a letter joined to the word after it by a hyphen an
/// attached slot. Slots are never side by side, and there are one, two or
/// three of them. Which letters the meaning uses is the checker's to compare, since
/// only a reading of the meaning says so.
fn phrase_parts(head: PhraseHead<'_>) -> Route<DefineParts> {
    let name = head.name;
    let words: Vec<&str> = head.rest.split_whitespace().collect();
    let Some(at) = words.iter().position(|w| *w == "means") else {
        return Route::no(format!(
            "define {name} says no `means`: a phrase define is `define {name}: <phrase> means <meaning>`"
        ));
    };
    let meaning = words[at + 1..].join(" ");
    if meaning.is_empty() {
        return Route::no(format!("define {name} says nothing after `means`"));
    }
    let said = &words[..at];
    let phrase = said.join(" ");
    let opens = said.len() >= 4
        && is_one_name(said[0])
        && said[1] == "is"
        && (said[2] == "a" || said[2] == "an");
    if !opens {
        return Route::no(format!(
            "define {name}: {} is not a phrase of the form `<letter> is a …` or `<letter> is an …`",
            repr(&phrase)
        ));
    }
    let mut pieces = vec![
        Piece::Slot(said[0].to_string()),
        Piece::Word("is".to_string()),
        Piece::Word(said[2].to_string()),
    ];
    for &w in &said[3..] {
        let Some(piece) = phrase_piece(w) else {
            return Route::no(format!(
                "define {name}: {} in its phrase is neither a word, a letter, nor a letter joined to a word by a hyphen",
                repr(w)
            ));
        };
        pieces.push(piece);
    }
    if matches!(pieces[3], Piece::Slot(_)) {
        return Route::no(format!(
            "define {name}: a word follows `{}` before any slot, as in `n is a triangular number`, or a slot joined to one, as in `z is an n-th root of w`",
            said[2]
        ));
    }
    let adjacent = pieces
        .windows(2)
        .any(|w| matches!(w[0], Piece::Slot(_)) && !matches!(w[1], Piece::Word(_)));
    if adjacent {
        return Route::no(format!(
            "define {name}: two slots stand side by side in {}, and a word goes between them",
            repr(&phrase)
        ));
    }
    let made = Phrase {
        name: name.to_string(),
        mundane: head.mundane,
        pieces,
        meaning,
    };
    let slots = made.slots();
    if slots.len() > 3 {
        return Route::no(format!(
            "define {name}: {} has {} slots, and a phrase has one, two or three",
            repr(&phrase),
            slots.len()
        ));
    }
    if let Some(twice) = slots
        .iter()
        .enumerate()
        .find(|(i, s)| slots[..*i].contains(s))
    {
        return Route::no(format!(
            "define {name}: the letter {} stands in two slots of its phrase",
            twice.1
        ));
    }
    Built(DefineParts::Phrase(made))
}

/// One word of a phrase after its article as the piece it is: a letter is a
/// slot, a letter joined to a word by a hyphen an attached slot, and a run
/// of letters a word (hyphens inside it, as in one-to-one, allowed); None
/// for anything else.
fn phrase_piece(w: &str) -> Option<Piece> {
    if is_one_name(w) {
        return Some(Piece::Slot(w.to_string()));
    }
    if let Some((slot, word)) = w.split_once('-') {
        if is_one_name(slot) && is_phrase_word(word) {
            return Some(Piece::Attached {
                slot: slot.to_string(),
                word: word.to_string(),
            });
        }
    }
    is_phrase_word(w).then(|| Piece::Word(w.to_string()))
}

/// Whether `w` is a word a phrase may write: letters, two or more, with
/// hyphens only between letters.
fn is_phrase_word(w: &str) -> bool {
    w.chars().count() >= 2
        && w.split('-')
            .all(|part| !part.is_empty() && part.chars().all(char::is_alphabetic))
}

/// The term a let gives and the kind of number it says its name is, where
/// the last piece after a comma outside brackets opens with `a` or `an`: `let
/// m = gcd(s, w), a natural number`. None where the line says no kind.
fn kind_said(body: &str) -> Option<(&str, String)> {
    let mut depth = 0i32;
    let mut cut = None;
    for (at, c) in body.char_indices() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => cut = Some(at),
            _ => {}
        }
    }
    let at = cut?;
    let kind = squash(&body[at + 1..]);
    (kind.starts_with("a ") || kind.starts_with("an "))
        .then(|| (str::trim(&body[..at]), kind))
}
