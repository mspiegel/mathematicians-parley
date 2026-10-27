//! Rewrites of a whole proof file that keep what each theorem says.
//!
//! A rewrite finds the formulas of a theorem with the readers the tools use:
//! the proof parser says which line is a hypothesis, a claim, a requires
//! line, a justification or a link of a chain, and the tokeniser says which
//! characters of a formula are a letter. Only those characters change. A
//! rewrite that cannot tell it keeps the meaning, a letter written where no
//! formula is read, a formula that does not read, declines the theorem and
//! says why; it never guesses.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use indexmap::IndexSet;
use parley::checker::{statements_in_scope, BoundThere, CheckedTheorem, ObtainedThere};
use parley::corpus::proof::{
    chain, chain_cited, parse_proof, rows, Head, Intro, Method, RowReason, Theorem,
};
use parley::corpus::{define_parts, naming_pieces, Corpus, DefineParts, Values};
use parley::formula::grammar::{Grammar, Sorts};
use parley::formula::node::Node;
use parley::formula::page::{conjoined, made_as, Written};
use parley::formula::token::{is_letter, is_mark, tokenise, Token, TokenKind};
use parley::matching::free_names;
use parley::outcome::{Built, Route};
use parley::sorts::introduction::Introduction;
use parley::sorts::{sorts_in_scope, Env};
use regex::Regex;

/// What every rewrite reads: the corpus, its grammar, and what the corpus
/// says about letters.
pub struct Context {
    pub corpus: Corpus,
    pub g: Rc<Grammar>,
    /// The library's function names of more than one letter, which the
    /// tokeniser reads whole.
    long_names: IndexSet<String>,
    /// The theorems another theorem cites, by qualified name. Its citers
    /// name its letters, so its own are not renamed.
    cited: BTreeSet<String>,
    /// Every single letter a notation's pattern spells: `i`, `π`, and the
    /// `a` of "is a point". Such a letter is not renamed, nor made.
    constants: BTreeSet<String>,
    /// The letters the library's items bind, most used first.
    library_letters: Vec<String>,
    /// What the item each obtain cites says there is, as the checker reads
    /// it at the step, by the step's file and line.
    obtained: BTreeMap<(String, usize), Route<Vec<String>>>,
    /// What each step citing an item makes its letters, as the checker
    /// reads it at the step, by the step's file and line.
    bound: BTreeMap<(String, usize), BTreeMap<String, String>>,
}

/// A theorem a rewrite left alone, and why.
pub struct Declined {
    pub theorem: String,
    pub why: String,
}

/// A file as a rewrite left it.
pub struct Rewritten {
    pub text: String,
    /// How many lines it changed.
    pub lines: usize,
    /// The theorems it changed, where it reads theorem by theorem.
    pub theorems: Vec<String>,
    pub declined: Vec<Declined>,
}

/// One sentence, read by the front end every tool reads by.
fn read_one(
    sentence: &str,
    g: &Grammar,
    sorts: &Sorts,
) -> parley::outcome::Checked<Node> {
    Written::new(sentence, "rewritten", 0)
        .formula()?
        .read(g, sorts)
}

/// The sentences of a text the test rewrites, as the front end's splitter
/// cuts them.
fn sentences(text: &str) -> Vec<String> {
    Written::new(text, "rewritten", 0)
        .sentences()
        .iter()
        .map(|s| s.text().to_string())
        .collect()
}

/// The compiled `pattern`, compiled once: the rewrites ask for the same few
/// patterns on every line of every theorem, and compiling them each time
/// took 8% of the test's run.
fn re(pattern: &str) -> Regex {
    thread_local! {
        static COMPILED: RefCell<BTreeMap<String, Regex>> =
            const { RefCell::new(BTreeMap::new()) };
    }
    COMPILED.with(|compiled| {
        compiled
            .borrow_mut()
            .entry(pattern.to_string())
            .or_insert_with(|| Regex::new(pattern).expect("the pattern compiles"))
            .clone()
    })
}

/// A letter as the tokeniser reads one: a letter and its marks, `x₁`, `f′`.
fn is_one_letter(text: &str) -> bool {
    let mut chars = text.chars();
    chars.next().is_some_and(is_letter) && chars.all(is_mark)
}

/// Which alphabet and case a letter is in. A letter is renamed only within
/// its class: the corpus writes points and sets in capitals, numbers in
/// lower case.
fn class(letter: &str) -> u8 {
    let c = letter.chars().next().unwrap_or(' ');
    if c.is_ascii_lowercase() {
        0
    } else if c.is_ascii_uppercase() {
        1
    } else if c.is_lowercase() {
        2
    } else {
        3
    }
}

/// A reason a theorem writes, and the values it gives what it cites.
struct Reasoned<'t> {
    text: &'t str,
    values: &'t Values,
}

/// Every reason a theorem writes: each step's justification, each requires
/// line's, and each let's under it.
fn reasons(thm: &Theorem) -> Vec<Reasoned<'_>> {
    let mut out = Vec::new();
    for step in &thm.steps {
        out.push(Reasoned {
            text: &step.just.text,
            values: &step.just.values,
        });
        out.extend(step.requires.iter().map(|r| Reasoned {
            text: &r.how,
            values: r.values(),
        }));
    }
    out.extend(thm.defines.iter().filter_map(|d| {
        d.reason.as_ref().map(|r| Reasoned {
            text: &r.how,
            values: r.values(),
        })
    }));
    out
}

/// The items a justification or requires line cites, by full name.
fn cites(thm: &Theorem, text: &str) -> Vec<String> {
    let names = &thm.names;
    re(r"\b[a-z]+:([A-Za-z0-9′-]+)")
        .captures_iter(text)
        .map(|m| names.full(&m[1]))
        .collect()
}

/// The single letter a `let` body introduces, `let a ∈ ℕ` or `let f : X → Y`.
fn let_letter(body: &str) -> Option<String> {
    let first = body.split([' ', '∈', ':']).next()?.trim();
    is_one_letter(first).then(|| first.to_string())
}

impl Context {
    pub fn new(
        corpus: Corpus,
        obtained: Vec<ObtainedThere>,
        bound: Vec<BoundThere>,
    ) -> Context {
        let g = Grammar::load(&corpus.records).expect("the grammar loads");
        let long_names: IndexSet<String> = g
            .functions
            .keys()
            .filter(|k| k.chars().count() > 1)
            .cloned()
            .collect();
        let mut cited = BTreeSet::new();
        let theorems: BTreeSet<String> =
            corpus.theorems.iter().map(|t| t.qualified()).collect();
        for thm in &corpus.theorems {
            for reason in reasons(thm) {
                for full in cites(thm, reason.text) {
                    if theorems.contains(&full) && full != thm.qualified() {
                        cited.insert(full);
                    }
                }
            }
        }
        // The letters a pattern spells, as the grammar reads its parts: the
        // d of ∫(_ to _) _ d_ is written against its hole, and is a literal
        // all the same.
        let mut constants = BTreeSet::new();
        for notation in &g.notations {
            for literal in notation.parts.iter().filter_map(|p| p.literal()) {
                if is_one_letter(literal) {
                    constants.insert(literal.to_string());
                }
            }
        }
        let mut counts: BTreeMap<String, usize> = BTreeMap::new();
        let mut context = Context {
            corpus,
            g,
            long_names,
            cited,
            constants,
            library_letters: Vec::new(),
            obtained: obtained
                .into_iter()
                .map(|o| ((o.path, o.line), o.said))
                .collect(),
            bound: bound
                .into_iter()
                .map(|b| ((b.path, b.line), b.letters.into_iter().collect()))
                .collect(),
        };
        for record in &context.corpus.records {
            let mut texts: Vec<&str> =
                record.hypotheses.iter().map(|h| h.text.as_str()).collect();
            texts.extend(record.conclusions.iter().map(|(c, _)| c.as_str()));
            for text in texts {
                for letter in context.letters_of(text) {
                    *counts.entry(letter).or_default() += 1;
                }
            }
        }
        let mut ranked: Vec<(String, usize)> = counts.into_iter().collect();
        ranked.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        context.library_letters = ranked.into_iter().map(|(l, _)| l).collect();
        context
    }

    /// The tokens of a formula, a sentence at a time as the readers take
    /// it: a full stop followed by a space or the end closes a sentence and
    /// is no token. Each token's place counts from the start of `text`.
    fn tokens(&self, text: &str) -> Option<Vec<Token>> {
        let c = chars(text);
        let mut out = Vec::new();
        let mut start = 0;
        let mut i = 0;
        while i <= c.len() {
            let ends = i == c.len()
                || (c[i] == '.' && (i + 1 == c.len() || c[i + 1].is_whitespace()));
            if ends {
                let piece: String = c[start..i].iter().collect();
                if !piece.trim().is_empty() {
                    let tokens = tokenise(
                        &piece,
                        &self.g.words,
                        &self.long_names,
                        &self.g.symbols,
                        "",
                        0,
                    )
                    .ok()?;
                    out.extend(tokens.into_iter().map(|t| Token {
                        at: t.at + start,
                        ..t
                    }));
                }
                start = i + 1;
            }
            i += 1;
        }
        Some(out)
    }

    /// The single letters a formula writes, where it tokenises.
    fn letters_of(&self, text: &str) -> Vec<String> {
        self.tokens(text)
            .unwrap_or_default()
            .into_iter()
            .filter(|t| t.kind == TokenKind::Name && is_one_letter(&t.text))
            .map(|t| t.text)
            .collect()
    }
}

/// Characters `from..to` of a line, which hold a formula.
#[derive(Clone)]
struct Region {
    line: usize,
    from: usize,
    to: usize,
}

/// Where a theorem's formulas are, and what else its lines write.
struct Layout {
    regions: Vec<Region>,
    /// Each line whose every letter means something, as it is outside its
    /// formulas: a letter found here would not be renamed with the rest.
    outside: Vec<(usize, String)>,
    /// Each step's claim: the lines it is written on, the first holding the
    /// region that starts it.
    claims: Vec<Claim>,
}

struct Claim {
    /// The step, by its index in the theorem.
    step: usize,
    lines: Vec<usize>,
    /// Where on the first line the claim starts.
    from: usize,
}

fn chars(s: &str) -> Vec<char> {
    s.chars().collect()
}

fn char_find(line: &[char], from: usize, needle: &str) -> Option<usize> {
    let n = chars(needle);
    (from..=line.len().saturating_sub(n.len())).find(|&i| line[i..].starts_with(&n))
}

fn char_rfind(line: &[char], needle: &str) -> Option<usize> {
    let n = chars(needle);
    (0..=line.len().saturating_sub(n.len()))
        .rev()
        .find(|&i| line[i..].starts_with(&n))
}

/// The end of a line's text, before trailing space.
fn trimmed_end(line: &[char]) -> usize {
    let mut end = line.len();
    while end > 0 && line[end - 1].is_whitespace() {
        end -= 1;
    }
    end
}

fn first_text(line: &[char]) -> usize {
    line.iter()
        .position(|c| !c.is_whitespace())
        .unwrap_or(line.len())
}

/// A hypothesis or opener line's formula: after its keyword, before its
/// label, and before ` be ` where a `let` gives a property in words.
fn introduction(line: &[char], label: Option<&str>) -> Option<(usize, usize)> {
    let start = first_text(line);
    let keyword_end = (start..line.len()).find(|&i| line[i].is_whitespace())?;
    let from = keyword_end + 1;
    let mut to = trimmed_end(line);
    if let Some(label) = label {
        let written = format!("({label})");
        if let Some(at) = char_rfind(line, &written) {
            if at >= from {
                to = to.min(at);
            }
        }
    }
    for cut in [" be ", ", which is the claim"] {
        if let Some(at) = char_find(line, from, cut) {
            to = to.min(at);
        }
    }
    while to > from && line[to - 1].is_whitespace() {
        to -= 1;
    }
    (to > from).then_some((from, to))
}

/// The formulas of a justification written from `start` on its line: the
/// values of `name := value`, the names an `obtain` takes, what a
/// `substitute` substitutes, and the letter of `induction on`.
fn justification(line: &[char], start: usize) -> Vec<(usize, usize)> {
    let text: String = line[start..].iter().collect();
    let at = |byte: usize| start + text[..byte].chars().count();
    let mut out = Vec::new();
    if let Some(m) = re(r"^obtain\s+(.+?)(?::|\s+from\b)").captures(&text) {
        let g = m.get(1).unwrap();
        out.push((at(g.start()), at(g.end())));
    }
    if let Some(m) =
        re(r"^substitute\s+(.+)\s+\((?:line\s+)?[A-Za-z0-9.′]+\)(?:\s+into\b.*)?\s*$")
            .captures(&text)
    {
        let g = m.get(1).unwrap();
        out.push((at(g.start()), at(g.end())));
    }
    if let Some(m) = re(r"^induction\s+on\s+(\S+)").captures(&text) {
        let g = m.get(1).unwrap();
        out.push((at(g.start()), at(g.end())));
    }
    if let Some(first) = re(r"[^\s,:]+\s*:=").find(&text) {
        let tail_end = values_end(&text, first.start()).unwrap_or(text.len());
        let tail = &text[first.start()..tail_end];
        let own = instantiates_own(&text);
        for piece in naming_pieces(tail) {
            let offset = piece.as_ptr() as usize - text.as_ptr() as usize;
            if let Some(m) = re(r"^\s*([^\s,]+)\s*:=\s*(.+?)\s*$").captures(piece) {
                let g = m.get(2).unwrap();
                out.push((at(offset + g.start()), at(offset + g.end())));
                if own {
                    let n = m.get(1).unwrap();
                    out.push((at(offset + n.start()), at(offset + n.end())));
                }
            }
        }
    }
    out
}

/// Where the values of a citation end, after `from`: at its `, from` or
/// `, contradicting`, or at an `instantiate`'s `in line L` or `in H3`, as
/// `corpus::Values` cuts them.
fn values_end(text: &str, from: usize) -> Option<usize> {
    re(r",\s*(?:from|contradicting)\b|\s+in\s+(?:line\b|[A-Z][A-Za-z]*[0-9]*′?\b)")
        .find_at(text, from)
        .map(|m| m.start())
}

/// Whether an `instantiate` takes a line or hypothesis of the theorem
/// itself, `in line 2` or `in H2`, whose bound letters are the theorem's.
fn instantiates_own(justification: &str) -> bool {
    justification.trim_start().starts_with("instantiate")
        && re(r"\s+in\s+(?:line\b|[A-Z][A-Za-z]*[0-9]*′?\b)").is_match(justification)
}

/// The `name` of each `name := value` that is the cited item's letter and
/// not the proof's.
fn assigned_names(line: &[char]) -> Vec<(usize, usize)> {
    let text: String = line.iter().collect();
    if instantiates_own(&text) {
        return Vec::new();
    }
    re(r"([^\s,:]+)\s*:=")
        .captures_iter(&text)
        .map(|m| {
            let g = m.get(1).unwrap();
            (
                text[..g.start()].chars().count(),
                text[..g.end()].chars().count(),
            )
        })
        .collect()
}

/// The lines a justification or requires line on `l` goes on to: each
/// after one ending in a comma, as the proof reader joins them.
fn continued(lines: &[String], l: usize, end: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut at = l;
    while lines[at].trim_end().ends_with(',')
        && at + 1 < end
        && !lines[at + 1].trim().is_empty()
    {
        at += 1;
        out.push(at);
    }
    out
}

fn layout(thm: &Theorem, lines: &[String], end: usize) -> Layout {
    let mut regions: Vec<Region> = Vec::new();
    let mut checked: BTreeSet<usize> = BTreeSet::new();
    let mut claims = Vec::new();
    let at = |no: usize| no - 1;
    let push =
        |regions: &mut Vec<Region>, line: usize, span: Option<(usize, usize)>| {
            if let Some((from, to)) = span {
                regions.push(Region { line, from, to });
            }
        };
    for h in &thm.hypotheses {
        let l = at(h.line);
        push(
            &mut regions,
            l,
            introduction(&chars(&lines[l]), h.label.as_deref()),
        );
        checked.insert(l);
    }
    for (i, line) in lines.iter().enumerate().take(end).skip(at(thm.line)) {
        let c = chars(line);
        let start = first_text(&c);
        let rest: String = c[start..].iter().collect();
        if rest.starts_with("then ") {
            push(&mut regions, i, Some((start + 5, trimmed_end(&c))));
            checked.insert(i);
        }
        // `ε, δ range over ℝ`: the letters it names are the theorem's.
        if parley::corpus::proof::Range::read(rest.trim(), 0).is_some() {
            let to = char_find(&c, start, " range").unwrap_or(start);
            push(&mut regions, i, Some((start, to)));
            checked.insert(i);
        }
    }
    // `let B = {x ∈ A : x ∉ f(x)} (D1)`: the name defined and its rule.
    for d in &thm.defines {
        let l = at(d.line);
        let c = chars(&lines[l]);
        let word = parley::corpus::define::naming(lines[l].trim())
            .map_or("define", |w| w.word());
        let from = first_text(&c) + word.chars().count() + 1;
        let mut to = trimmed_end(&c);
        if let Some(cut) = char_rfind(&c, &format!("({})", d.label)) {
            to = cut;
        }
        // The kind of number a let says its name is, `, a natural number`,
        // is words.
        if let Built(DefineParts::One(one)) = define_parts(&d.text) {
            let phrase = one.kind.map(|kind| format!(", {kind}"));
            if let Some(cut) = phrase.and_then(|p| char_rfind(&c, &p)) {
                to = to.min(cut);
            }
        }
        while to > from && c[to - 1].is_whitespace() {
            to -= 1;
        }
        push(&mut regions, l, Some((from, to)));
        checked.insert(l);
        // A rule laid out as a table goes on over every line indented past
        // its naming line, up to the line that says what it `reads`.
        let indent = first_text(&c);
        for (next, line) in lines.iter().enumerate().take(end).skip(l + 1) {
            let n = chars(line);
            let start = first_text(&n);
            let rest: String = n[start..].iter().collect();
            if rest.is_empty() || start <= indent || rest.starts_with("reads ") {
                break;
            }
            // A let's reason is written as a requires line's is.
            if d.reason.as_ref().is_some_and(|r| at(r.line) == next) {
                for span in justification(&n, start) {
                    push(&mut regions, next, Some(span));
                }
                checked.insert(next);
                continue;
            }
            let mut to = trimmed_end(&n);
            if let Some(cut) = char_rfind(&n, &format!("({})", d.label)) {
                to = cut;
            }
            while to > start && n[to - 1].is_whitespace() {
                to -= 1;
            }
            push(&mut regions, next, Some((start, to)));
            checked.insert(next);
        }
    }
    for (index, step) in thm.steps.iter().enumerate() {
        for o in &step.openers {
            let l = at(o.line);
            let c = chars(&lines[l]);
            let span = if o.is_hypothesis {
                char_find(&c, 0, "true for ").and_then(|from| {
                    let from = from + "true for ".len();
                    char_find(&c, from, ",").map(|to| (from, to))
                })
            } else {
                introduction(&c, Some(&o.label))
            };
            push(&mut regions, l, span);
            checked.insert(l);
        }
        let first = at(step.line);
        let c = chars(&lines[first]);
        let number = re(r"^\s*[0-9][0-9.]*\.?\s+")
            .find(&lines[first])
            .map(|m| lines[first][..m.end()].chars().count());
        if let Some(from) = number {
            let mut claim_lines = vec![first];
            let mut to = trimmed_end(&c);
            if let Some(cut) = char_find(&c, from, ", which is impossible") {
                to = cut;
            }
            push(&mut regions, first, Some((from, to)));
            checked.insert(first);
            for (l, line) in lines
                .iter()
                .enumerate()
                .take(at(step.just.line))
                .skip(first + 1)
            {
                let c = chars(line);
                if c.iter().all(|ch| ch.is_whitespace()) {
                    continue;
                }
                let mut to = trimmed_end(&c);
                if let Some(cut) = char_find(&c, 0, ", which is impossible") {
                    to = cut;
                }
                push(&mut regions, l, Some((first_text(&c), to)));
                checked.insert(l);
                claim_lines.push(l);
            }
            claims.push(Claim {
                step: index,
                lines: claim_lines,
                from,
            });
        }
        let j = at(step.just.line);
        let c = chars(&lines[j]);
        for span in justification(&c, first_text(&c)) {
            push(&mut regions, j, Some(span));
        }
        checked.insert(j);
        for l in continued(lines, j, end) {
            let c = chars(&lines[l]);
            for span in justification(&c, first_text(&c)) {
                push(&mut regions, l, Some(span));
            }
            checked.insert(l);
        }
        for (_, no) in &step.just.chain {
            let l = at(*no);
            let c = chars(&lines[l]);
            let from = first_text(&c);
            let end = trimmed_end(&c);
            let to = (from..end)
                .rev()
                .find(|&i| i + 1 < end && c[i] == ' ' && c[i + 1] == ' ')
                .map(|i| {
                    let mut t = i;
                    while t > from && c[t - 1] == ' ' {
                        t -= 1;
                    }
                    t
                })
                .unwrap_or(end);
            push(&mut regions, l, Some((from, to)));
            checked.insert(l);
        }
        // A row writes a formula and, after `adding` or `multiplying by`, a
        // term: those hold what the proof writes of its letters. The reason's
        // words and label are none of them, and a word like `restate`
        // would be read a letter at a time.
        for (_, no) in &step.just.rows {
            let l = at(*no);
            let c = chars(&lines[l]);
            let (from, end) = (first_text(&c), trimmed_end(&c));
            let worded = ["adding ", "multiplying by "]
                .iter()
                .filter_map(|w| {
                    char_rfind(&c, &format!(" {w}")).map(|at| (at, w.chars().count()))
                })
                .max_by_key(|(at, _)| *at);
            match worded {
                Some((at, length)) => {
                    push(&mut regions, l, Some((from, at)));
                    push(&mut regions, l, Some((at + 1 + length, end)));
                }
                None => {
                    let last = (from..end).rev().find(|&i| c[i] == ' ').unwrap_or(from);
                    push(&mut regions, l, Some((from, last)));
                }
            }
            checked.insert(l);
        }
        for r in &step.requires {
            let l = at(r.line);
            let c = chars(&lines[l]);
            let start = first_text(&c);
            if let Some(colon) = char_rfind(&c, ": ") {
                let from = start + "requires ".len();
                if colon > from {
                    push(&mut regions, l, Some((from, colon)));
                }
                for span in justification(&c, colon + 2) {
                    push(&mut regions, l, Some(span));
                }
            }
            checked.insert(l);
            for next in continued(lines, l, end) {
                let c = chars(&lines[next]);
                for span in justification(&c, first_text(&c)) {
                    push(&mut regions, next, Some(span));
                }
                checked.insert(next);
            }
        }
    }
    // A line ending in a comma goes on: what follows is more of its formula.
    let mut more = true;
    while more {
        more = false;
        for l in at(thm.line)..end.saturating_sub(1) {
            let ends_formula = regions
                .iter()
                .any(|r| r.line == l && r.to >= trimmed_end(&chars(&lines[l])))
                && lines[l].trim_end().ends_with(',');
            let next = l + 1;
            if ends_formula
                && !checked.contains(&next)
                && !lines[next].trim().is_empty()
            {
                let c = chars(&lines[next]);
                let mut to = trimmed_end(&c);
                if let Some(h) = thm.hypotheses.iter().find(|h| at(h.line) == l) {
                    if let Some(label) = &h.label {
                        if let Some(cut) = char_rfind(&c, &format!("({label})")) {
                            to = cut;
                        }
                    }
                }
                regions.push(Region {
                    line: next,
                    from: first_text(&c),
                    to,
                });
                checked.insert(next);
                if let Some(claim) =
                    claims.iter_mut().find(|cl| cl.lines.last() == Some(&l))
                {
                    claim.lines.push(next);
                }
                more = true;
            }
        }
    }
    let mut outside = Vec::new();
    for l in checked {
        let mut c = chars(&lines[l]);
        for r in regions.iter().filter(|r| r.line == l) {
            for ch in c.iter_mut().take(r.to).skip(r.from) {
                *ch = ' ';
            }
        }
        for (from, to) in assigned_names(&chars(&lines[l])) {
            for ch in c.iter_mut().take(to).skip(from) {
                *ch = ' ';
            }
        }
        outside.push((l, c.into_iter().collect()));
    }
    Layout {
        regions,
        outside,
        claims,
    }
}

/// The letters written standing alone in text no formula is read from: not
/// a run of letters, not a label's letter before its digit.
fn loose_letters(text: &str) -> BTreeSet<String> {
    let c = chars(text);
    let mut out = BTreeSet::new();
    let mut i = 0;
    while i < c.len() {
        if is_letter(c[i])
            && (i == 0
                || !(is_letter(c[i - 1])
                    || c[i - 1].is_ascii_digit()
                    || c[i - 1] == '_'
                    || c[i - 1] == ':'
                    || c[i - 1] == '-'))
        {
            let mut j = i + 1;
            while j < c.len() && is_mark(c[j]) {
                j += 1;
            }
            let joined = j < c.len()
                && (is_letter(c[j])
                    || c[j].is_ascii_digit()
                    || c[j] == '-'
                    || c[j] == ':');
            if !joined {
                out.insert(c[i..j].iter().collect());
            }
            i = j;
        } else {
            i += 1;
        }
    }
    out
}

/// What a theorem reads as its letters: every letter in its formulas, and
/// any written loose elsewhere on its lines.
fn letters_used(
    ctx: &Context,
    lines: &[String],
    lay: &Layout,
) -> Result<BTreeSet<String>, String> {
    let mut used = BTreeSet::new();
    for r in &lay.regions {
        let text: String = chars(&lines[r.line])[r.from..r.to].iter().collect();
        let tokens = ctx
            .tokens(&text)
            .ok_or_else(|| format!("line {} does not tokenise: {text}", r.line + 1))?;
        used.extend(
            tokens
                .into_iter()
                .filter(|t| t.kind == TokenKind::Name && is_one_letter(&t.text))
                .map(|t| t.text),
        );
    }
    for (_, text) in &lay.outside {
        used.extend(loose_letters(text));
    }
    Ok(used)
}

/// A name as `map` renames it: the letter itself, or a letter with primes,
/// `f′`, which is something made of the letter, its derivative, and is
/// renamed with it. A subscript makes a letter of its own, `x₁`, and is not.
fn renamed_name(map: &BTreeMap<String, String>, name: &str) -> Option<String> {
    if let Some(new) = map.get(name) {
        return Some(new.clone());
    }
    let base = name.trim_end_matches('′');
    (base != name)
        .then(|| map.get(base))
        .flatten()
        .map(|new| format!("{new}{}", &name[base.len()..]))
}

/// The theorem's lines with each letter renamed by `map`, in every formula.
/// It declines where a letter it renames is written outside a formula, or
/// where a formula would read as other tokens once renamed.
fn rename(
    ctx: &Context,
    lines: &mut [String],
    lay: &Layout,
    map: &BTreeMap<String, String>,
) -> Result<usize, String> {
    for (l, text) in &lay.outside {
        for letter in loose_letters(text) {
            if map.contains_key(&letter) {
                return Err(format!(
                    "{letter} is written outside a formula on line {}",
                    l + 1
                ));
            }
        }
    }
    let mut by_line: BTreeMap<usize, Vec<&Region>> = BTreeMap::new();
    for r in &lay.regions {
        by_line.entry(r.line).or_default().push(r);
    }
    let mut changed = 0;
    for (l, mut regions) in by_line {
        regions.sort_by_key(|r| std::cmp::Reverse(r.from));
        let mut c = chars(&lines[l]);
        let before = lines[l].clone();
        for r in regions {
            let text: String = c[r.from..r.to].iter().collect();
            let tokens = ctx
                .tokens(&text)
                .ok_or_else(|| format!("line {} does not tokenise: {text}", l + 1))?;
            let mut out: Vec<char> = chars(&text);
            for t in tokens.iter().rev() {
                if t.kind != TokenKind::Name {
                    continue;
                }
                if let Some(new) = renamed_name(map, &t.text) {
                    let len = t.text.chars().count();
                    out.splice(t.at..t.at + len, new.chars());
                }
            }
            let new: String = out.iter().collect();
            let again = ctx.tokens(&new).ok_or_else(|| {
                format!("line {} renamed does not tokenise: {new}", l + 1)
            })?;
            let same = again.len() == tokens.len()
                && again.iter().zip(&tokens).all(|(a, t)| {
                    a.kind == t.kind
                        && (a.text == t.text
                            || renamed_name(map, &t.text).as_ref() == Some(&a.text))
                });
            if !same {
                return Err(format!("line {} reads otherwise renamed: {new}", l + 1));
            }
            c.splice(r.from..r.to, out);
        }
        lines[l] = c.into_iter().collect();
        if lines[l] != before {
            changed += 1;
        }
    }
    Ok(changed)
}

/// The letters a theorem introduces: by `let`, before its steps or opening a
/// block, and by `obtain`.
fn introduced(thm: &Theorem) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut add = |l: Option<String>| {
        if let Some(l) = l {
            if !out.contains(&l) {
                out.push(l);
            }
        }
    };
    for h in &thm.hypotheses {
        if h.kind == Intro::Let {
            add(let_letter(&parley::sorts::body_of(h.text.trim(), "let")));
        }
    }
    for step in &thm.steps {
        for o in &step.openers {
            if o.kind == Intro::Let && !o.is_hypothesis {
                add(let_letter(&parley::sorts::body_of(o.text.trim(), "let")));
            }
        }
        if let Some(m) = re(r"^obtain\s+(.+?)(?::|\s+from\b)").captures(&step.just.text)
        {
            for name in m[1].split(',') {
                let name = name.trim();
                if is_one_letter(name) {
                    add(Some(name.to_string()));
                }
            }
        }
    }
    out
}

/// The letters of a theorem no rename may touch: the library's constants;
/// those a citation of a corpus theorem leaves to stand for the cited
/// theorem's letter of the same name; and, where another theorem cites this
/// one, every letter its statement writes, which the citer names and whose
/// elaborated statement the test does not build again. The letters such a
/// theorem introduces among its steps are its own, and are renamed.
fn held(ctx: &Context, thm: &Theorem) -> BTreeSet<String> {
    let mut out = held_own(ctx, thm);
    if ctx.cited.contains(&thm.qualified()) {
        for h in &thm.hypotheses {
            out.extend(ctx.letters_of(h.body(&thm.path).text()));
        }
        out.extend(ctx.letters_of(&thm.conclusion));
    }
    out
}

/// The letters of a theorem no rename may touch whoever cites it: the
/// library's constants, and those a citation of a corpus theorem leaves to
/// stand for the cited theorem's letter of the same name.
fn held_own(ctx: &Context, thm: &Theorem) -> BTreeSet<String> {
    let mut out = ctx.constants.clone();
    for reason in reasons(thm) {
        let named: BTreeSet<String> = reason.values.names().map(String::from).collect();
        for full in cites(thm, reason.text) {
            if let Some(other) =
                ctx.corpus.theorems.iter().find(|t| t.qualified() == full)
            {
                for h in &other.hypotheses {
                    if h.kind != Intro::Let {
                        continue;
                    }
                    if let Some(l) =
                        let_letter(&parley::sorts::body_of(h.text.trim(), "let"))
                    {
                        if !named.contains(&l) {
                            out.insert(l);
                        }
                    }
                }
            }
        }
    }
    out
}

/// Each theorem of a file, last first, so that a rewrite that drops lines
/// leaves the lines of those above where they were.
fn theorems_of<'c>(
    ctx: &'c Context,
    path: &str,
    count: usize,
) -> Vec<(&'c Theorem, usize)> {
    let mut thms: Vec<&Theorem> = ctx
        .corpus
        .theorems
        .iter()
        .filter(|t| t.path == path)
        .collect();
    thms.sort_by_key(|t| t.line);
    let mut out = Vec::new();
    for (i, t) in thms.iter().enumerate() {
        let end = thms.get(i + 1).map_or(count, |n| n.line - 1);
        out.push((*t, end));
    }
    out.reverse();
    out
}

fn joined(lines: Vec<String>, text: &str) -> String {
    let mut out = lines.join("\n");
    if text.ends_with('\n') {
        out.push('\n');
    }
    out
}

/// How a renaming rewrite picks its letters: from the theorem, the letters
/// it writes, and those it may not touch, the old letter to the new.
type Choose = fn(
    &Context,
    &Theorem,
    &BTreeSet<String>,
    &BTreeSet<String>,
) -> Option<BTreeMap<String, String>>;

/// A rewrite that renames letters of one theorem at a time: `choose` picks
/// the renaming from the theorem, its letters, and those it may not touch.
fn renaming(ctx: &Context, path: &str, text: &str, choose: Choose) -> Rewritten {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let mut count = 0;
    let mut theorems = Vec::new();
    let mut declined = Vec::new();
    for (thm, end) in theorems_of(ctx, path, lines.len()) {
        let lay = layout(thm, &lines, end);
        let used = match letters_used(ctx, &lines, &lay) {
            Ok(used) => used,
            Err(why) => {
                declined.push(Declined {
                    theorem: thm.qualified(),
                    why,
                });
                continue;
            }
        };
        let Some(map) = choose(ctx, thm, &used, &held(ctx, thm)) else {
            continue;
        };
        if makes_pairs_for_themselves(thm, &map) {
            declined.push(Declined {
                theorem: thm.qualified(),
                why: "the renaming gives a cited letter itself, `B := A` as `B := B`, \
                      a pair no proof writes where matching finds the letter"
                    .to_string(),
            });
            continue;
        }
        let mut attempt = lines.clone();
        match rename(ctx, &mut attempt, &lay, &map) {
            Ok(n) => {
                subjects_named(ctx, thm, &mut attempt, &map);
                lines = attempt;
                count += n;
                if n > 0 {
                    theorems.push(thm.qualified());
                }
            }
            Err(why) => declined.push(Declined {
                theorem: thm.qualified(),
                why,
            }),
        }
    }
    Rewritten {
        text: joined(lines, text),
        lines: count,
        theorems,
        declined,
    }
}

/// Whether renaming by `map` turns a pair of `thm`'s citations into one
/// naming a letter for itself: `B := A`, with A renamed B. A proof written
/// with B does not write `B := B` where matching finds B (`SYNTAX.md`, no
/// pair says what goes without saying), so the renamed proof is not one
/// written with those letters.
fn makes_pairs_for_themselves(thm: &Theorem, map: &BTreeMap<String, String>) -> bool {
    let reasons = thm.steps.iter().flat_map(|s| {
        std::iter::once(&s.just)
            .chain(s.requires.iter().filter_map(|r| r.by.as_ref().ok()))
    });
    reasons.flat_map(|j| j.values.pairs()).any(|(name, value)| {
        map.get(value.text().trim())
            .is_some_and(|renamed| renamed == name)
    })
}

/// The pair a renaming has to write back. A definition cited with no pair
/// for its subject is about the proof's letter of that name (`SYNTAX.md`)
/// where the step says something of that letter, as "u ∈ aH" cited from
/// `coset` does; where the step does not write it, matching finds the
/// subject, as it finds u for "Y ⊆ G" from `part-builder`. So where the
/// checker made the subject the proof's letter of its name, and the
/// renaming changed that letter, the citation is given the pair `u := w`
/// and means what it meant. A letter written inside the term matching
/// fills the subject with, the x of "x(n) + C → L + C" cited from
/// `tends-to`, is no pin of it. A requires line, whose binding the checker
/// does not keep, is given the pair where its claim opens with the letter.
fn subjects_named(
    ctx: &Context,
    thm: &Theorem,
    lines: &mut [String],
    map: &BTreeMap<String, String>,
) {
    let item = re(r"\b[a-z]+:([A-Za-z0-9′-]+)");
    // Each citing line, what it claims, and the step's line where the
    // checker keeps what the citation makes the item's letters.
    let mut cited: Vec<(usize, String, Option<usize>)> = Vec::new();
    for step in &thm.steps {
        cited.push((step.just.line, step.claim_text(), Some(step.line)));
        cited.extend(
            step.requires
                .iter()
                .map(|r| (r.line, r.fact.text().to_string(), None)),
        );
    }
    for (no, claim, step_line) in cited {
        let Some(line) = no.checked_sub(1).and_then(|i| lines.get_mut(i)) else {
            continue;
        };
        let Some(m) = item.captures(line) else {
            continue;
        };
        let full = thm.names.full(&m[1]);
        let Some(record) = ctx.corpus.records.iter().find(|r| {
            r.qualified() == full && r.kind == parley::corpus::RecordKind::Definition
        }) else {
            continue;
        };
        let Some((said, _)) = record.conclusions.first() else {
            continue;
        };
        let left = said.split(" ↔ ").next().unwrap_or("");
        let Some(subject) = ctx.tokens(left).and_then(|t| {
            t.into_iter()
                .find(|t| t.kind == TokenKind::Name)
                .map(|t| t.text)
        }) else {
            continue;
        };
        let Some(new) = map.get(&subject) else {
            continue;
        };
        let bound = step_line.and_then(|l| ctx.bound.get(&(thm.path.clone(), l)));
        let written = match bound {
            Some(letters) => letters.get(&subject) == Some(&subject),
            None => ctx.tokens(&claim).is_some_and(|t| {
                t.first()
                    .is_some_and(|t| t.kind == TokenKind::Name && t.text == subject)
            }),
        };
        let at = m.get(0).expect("the whole match").end();
        if !written || line[at..].contains(&format!("{subject} :=")) {
            continue;
        }
        let pair = if line[at..].is_empty() || line[at..].starts_with(',') {
            format!(" {subject} := {new}")
        } else {
            format!(" {subject} := {new},")
        };
        line.insert_str(at, &pair);
    }
}

/// The first two letters a theorem introduces in one alphabet and case,
/// swapped everywhere the theorem writes them. A swap is a renaming that
/// takes no letter from outside, so it keeps the meaning whatever the two
/// letters are; the two need not be of one sort.
fn swap(
    _: &Context,
    thm: &Theorem,
    _: &BTreeSet<String>,
    held: &BTreeSet<String>,
) -> Option<BTreeMap<String, String>> {
    let free: Vec<String> = introduced(thm)
        .into_iter()
        .filter(|l| !held.contains(l))
        .collect();
    let (a, b) = free.iter().enumerate().find_map(|(i, a)| {
        free[i + 1..]
            .iter()
            .find(|b| class(b) == class(a))
            .map(|b| (a.clone(), b.clone()))
    })?;
    Some(BTreeMap::from([(a.clone(), b.clone()), (b, a)]))
}

/// The letters the items a theorem cites bind, then the rest of the
/// library's, most used first.
fn library_pool(ctx: &Context, thm: &Theorem) -> Vec<String> {
    let mut pool: Vec<String> = Vec::new();
    for reason in reasons(thm) {
        for full in cites(thm, reason.text) {
            if let Some(r) = ctx.corpus.records.iter().find(|r| r.qualified() == full) {
                let mut texts: Vec<&str> =
                    r.hypotheses.iter().map(|h| h.text.as_str()).collect();
                texts.extend(r.conclusions.iter().map(|(c, _)| c.as_str()));
                for t in texts {
                    for l in ctx.letters_of(t) {
                        if !pool.contains(&l) {
                            pool.push(l);
                        }
                    }
                }
            }
        }
    }
    for l in &ctx.library_letters {
        if !pool.contains(l) {
            pool.push(l.clone());
        }
    }
    pool
}

/// Every letter the theorem introduces, renamed to a letter the library
/// binds that the theorem does not write, in the same alphabet and case.
fn to_library(
    ctx: &Context,
    thm: &Theorem,
    used: &BTreeSet<String>,
    held: &BTreeSet<String>,
) -> Option<BTreeMap<String, String>> {
    renamed_to_library(ctx, thm, introduced(thm), used, held)
}

/// Every letter a binder in the theorem's formulas binds, `for all k`,
/// `there is x`, `Σ(j = …)`, `{t ∈ … | …}`, renamed to a letter the library
/// binds that the theorem does not write. The items a theorem cites come
/// first in the pool, so a bound letter becomes the letter the cited
/// lemma binds itself, where a value put under one is caught by the other.
fn bound_to_library(
    ctx: &Context,
    thm: &Theorem,
    used: &BTreeSet<String>,
    held: &BTreeSet<String>,
) -> Option<BTreeMap<String, String>> {
    renamed_to_library(ctx, thm, bound(ctx, thm), used, held)
}

/// The letters the binders in a theorem's formulas bind, in the order the
/// theorem writes them.
fn bound(ctx: &Context, thm: &Theorem) -> Vec<String> {
    let sorts = sorts_in_scope(
        thm,
        Env {
            g: &ctx.g,
            scopes: &ctx.corpus.scopes,
        },
    );
    // What each line says, read: a `let` line what its introduction
    // asserts, any other its sentences; what does not read the checker
    // reports.
    let said = |kind: Intro, body: Written| -> Vec<Node> {
        match kind {
            Intro::Let => Introduction::read(body)
                .asserted(&ctx.g, &sorts)
                .unwrap_or_default(),
            _ => body
                .sentences()
                .iter()
                .filter_map(|s| s.read(&ctx.g, &sorts).ok())
                .collect(),
        }
    };
    let mut trees: Vec<Node> = Vec::new();
    for h in &thm.hypotheses {
        trees.extend(said(h.kind, h.body(&thm.path)));
    }
    trees.extend(said(Intro::Assume, thm.stated()));
    for step in &thm.steps {
        trees.extend(said(Intro::Assume, step.claim.clone()));
        for r in &step.requires {
            trees.extend(said(Intro::Assume, r.fact.clone()));
        }
        for o in step.openers.iter().filter(|o| !o.is_hypothesis) {
            trees.extend(said(o.kind, o.body(&thm.path)));
        }
    }
    let binders = ctx.g.binders();
    let mut out: Vec<String> = Vec::new();
    for tree in trees {
        {
            for node in tree.walk() {
                let Some(binds) = binders.get(&node.notation()) else {
                    continue;
                };
                for &at in &binds.held {
                    let Some(letter) = node.children.get(at) else {
                        continue;
                    };
                    if letter.is_name()
                        && is_one_letter(&letter.text)
                        && !out.iter().any(|o| *o == letter.text)
                    {
                        out.push(letter.text.to_string());
                    }
                }
            }
        }
    }
    out
}

/// `letters` renamed each to a letter the library binds that the theorem
/// does not write, in the same alphabet and case.
fn renamed_to_library(
    ctx: &Context,
    thm: &Theorem,
    letters: Vec<String>,
    used: &BTreeSet<String>,
    held: &BTreeSet<String>,
) -> Option<BTreeMap<String, String>> {
    let pool = library_pool(ctx, thm);
    let mut map = BTreeMap::new();
    let mut taken: BTreeSet<String> = BTreeSet::new();
    for letter in letters {
        if held.contains(&letter) {
            continue;
        }
        let target = pool.iter().find(|t| {
            class(t) == class(&letter)
                && !t.contains('′')
                && !used.iter().any(|u| u.trim_end_matches('′') == t.as_str())
                && !held.contains(*t)
                && !taken.contains(*t)
                && !ctx.g.functions.contains_key(*t)
        });
        if let Some(t) = target {
            taken.insert(t.clone());
            map.insert(letter, t.clone());
        }
    }
    (!map.is_empty()).then_some(map)
}

/// The first lower-case letter the theorem introduces, renamed `i`, which a
/// name the text introduces shadows.
fn to_i(
    _: &Context,
    thm: &Theorem,
    used: &BTreeSet<String>,
    held: &BTreeSet<String>,
) -> Option<BTreeMap<String, String>> {
    if used.contains("i") {
        return None;
    }
    let letter = introduced(thm)
        .into_iter()
        .find(|l| class(l) == 0 && !held.contains(l))?;
    Some(BTreeMap::from([(letter, "i".to_string())]))
}

pub fn letters_swapped(ctx: &Context, path: &str, text: &str) -> Rewritten {
    renaming(ctx, path, text, swap)
}

pub fn letters_to_library(ctx: &Context, path: &str, text: &str) -> Rewritten {
    renaming(ctx, path, text, to_library)
}

pub fn bound_letters_to_library(ctx: &Context, path: &str, text: &str) -> Rewritten {
    renaming(ctx, path, text, bound_to_library)
}

pub fn letter_to_i(ctx: &Context, path: &str, text: &str) -> Rewritten {
    renaming(ctx, path, text, to_i)
}

/// `a := x, b := y` as `b := y, a := x`: values are given at once, in no
/// order.
///
/// Only a citation written on one line is turned around: a line that ends
/// in a comma goes on, and a line that starts with a value is the rest of
/// one.
pub fn values_reversed(line: &str) -> Option<String> {
    if line.trim_end().ends_with(',') || re(r"^\s*[^\s,:]+\s*:=").is_match(line) {
        return None;
    }
    let first = re(r"[^\s,:]+\s*:=").find(line)?;
    let tail_end = values_end(line, first.start()).unwrap_or(line.trim_end().len());
    let tail = &line[first.start()..tail_end];
    let pieces: Vec<&str> = naming_pieces(tail);
    let assign = re(r"^[^\s,]+\s*:=\s*\S");
    if pieces.len() < 2 || !pieces.iter().all(|p| assign.is_match(p)) {
        return None;
    }
    let reversed: Vec<&str> = pieces.into_iter().rev().collect();
    Some(format!(
        "{}{}{}",
        &line[..first.start()],
        reversed.join(", "),
        &line[tail_end..]
    ))
}

/// `a := x, b := y` as `a := (x), b := (y)`: brackets around a value group
/// it and say nothing more.
///
/// Only a citation written on one line is bracketed, as `values_reversed`
/// turns only one; a `define` line's `:=` gives no value.
pub fn values_bracketed(line: &str) -> Option<String> {
    if line.trim_end().ends_with(',')
        || re(r"^\s*[^\s,:]+\s*:=").is_match(line)
        || re(r"^\s*define\b").is_match(line)
    {
        return None;
    }
    let first = re(r"[^\s,:]+\s*:=").find(line)?;
    let tail_end = values_end(line, first.start()).unwrap_or(line.trim_end().len());
    let tail = &line[first.start()..tail_end];
    let assign = re(r"^([^\s,]+)\s*:=\s*(\S.*)$");
    let mut bracketed = Vec::new();
    for piece in naming_pieces(tail) {
        let m = assign.captures(piece)?;
        bracketed.push(format!("{} := ({})", &m[1], &m[2]));
    }
    Some(format!(
        "{}{}{}",
        &line[..first.start()],
        bracketed.join(", "),
        &line[tail_end..]
    ))
}

/// A claim rewritten in place: `new` in place of its text, its other lines
/// dropped.
fn replace_claim(lines: &mut Vec<String>, claim: &Claim, region_end: usize, new: &str) {
    let first = claim.lines[0];
    let c = chars(&lines[first]);
    let head: String = c[..claim.from].iter().collect();
    let last = *claim.lines.last().unwrap();
    let lc = chars(&lines[last]);
    let tail: String = if last == first {
        c[region_end..].iter().collect()
    } else {
        let mut to = trimmed_end(&lc);
        if let Some(cut) = char_find(&lc, 0, ", which is impossible") {
            to = cut;
        }
        lc[to..].iter().collect()
    };
    lines[first] = format!("{head}{new}{tail}");
    for l in claim.lines[1..].iter().rev() {
        lines.remove(*l);
    }
}

/// A rewrite of one step's claim at a time: `rewrite` gives the claim's new
/// text from its sentences, read with the theorem's sorts, or None where it
/// does not apply.
fn claims(
    ctx: &Context,
    path: &str,
    text: &str,
    rewrite: fn(&Context, &[Node]) -> Option<String>,
) -> Rewritten {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let mut count = 0;
    let mut theorems = Vec::new();
    let mut declined = Vec::new();
    for (thm, end) in theorems_of(ctx, path, lines.len()) {
        let lay = layout(thm, &lines, end);
        let sorts = sorts_in_scope(
            thm,
            Env {
                g: &ctx.g,
                scopes: &ctx.corpus.scopes,
            },
        );
        let mut todo: Vec<&Claim> = lay.claims.iter().collect();
        todo.sort_by(|a, b| b.lines[0].cmp(&a.lines[0]));
        for claim in todo {
            let step = &thm.steps[claim.step];
            if step.impossible {
                continue;
            }
            let read: Result<Vec<Node>, String> = sentences(&step.claim_text())
                .iter()
                .map(|s| {
                    read_one(s, &ctx.g, &sorts)
                        .map_err(|p| format!("step {} does not read: {p}", step.number))
                })
                .collect();
            let read = match read {
                Ok(r) => r,
                Err(why) => {
                    declined.push(Declined {
                        theorem: thm.qualified(),
                        why,
                    });
                    continue;
                }
            };
            let Some(new) = rewrite(ctx, &read) else {
                continue;
            };
            // The new claim must read as the old one did, sentence by sentence
            // or conjunct by conjunct.
            let again: Result<Vec<Node>, _> = sentences(&new)
                .iter()
                .map(|s| read_one(s, &ctx.g, &sorts))
                .collect();
            let fold = |nodes: &[Node]| -> Vec<String> {
                let mut out = Vec::new();
                for n in nodes {
                    flatten(n, &mut out, &ctx.g);
                }
                out
            };
            match again {
                Ok(again) if fold(&again) == fold(&read) => {}
                _ => {
                    declined.push(Declined {
                        theorem: thm.qualified(),
                        why: format!(
                            "step {} rewritten reads otherwise: {new}",
                            step.number
                        ),
                    });
                    continue;
                }
            }
            let first = &lay
                .regions
                .iter()
                .find(|r| r.line == claim.lines[0] && r.from == claim.from);
            let Some(first) = first else { continue };
            replace_claim(&mut lines, claim, first.to, &new);
            count += 1;
            if !theorems.contains(&thm.qualified()) {
                theorems.push(thm.qualified());
            }
        }
    }
    Rewritten {
        text: joined(lines, text),
        lines: count,
        theorems,
        declined,
    }
}

/// The conjuncts of a formula, each printed: a conjunction is its parts, in
/// order, however it is grouped.
fn flatten(node: &Node, out: &mut Vec<String>, g: &Grammar) {
    if is_conjunction(node) {
        for child in &node.children {
            flatten(child, out, g);
        }
    } else {
        out.push(g.print(node));
    }
}

fn is_conjunction(node: &Node) -> bool {
    matches!(
        node.notation(),
        parley::notations::CONJUNCTION | parley::notations::COMMA_CONJUNCTION
    ) && node.children.len() == 2
}

/// `A and B` as `A. B`: `SYNTAX.md` writes a conjunction as sentences, and
/// several sentences mean their conjunction. The other way round is not a
/// change here, since a long "and" is a way the language says not to write.
fn conjunction_split(ctx: &Context, read: &[Node]) -> Option<String> {
    let [only] = read else { return None };
    if !is_conjunction(only) {
        return None;
    }
    Some(format!(
        "{}. {}",
        ctx.g.print(&only.children[0]),
        ctx.g.print(&only.children[1])
    ))
}

pub fn claims_split(ctx: &Context, path: &str, text: &str) -> Rewritten {
    claims(ctx, path, text, conjunction_split)
}

/// A sentence that is one relation and nothing else, turned around: `a = b`
/// as `b = a`, `x ≤ y` as `y ≥ x`. None for any other sentence: one with
/// words, a comma, or a second relation.
fn relation_turned(sentence: &str) -> Option<String> {
    let all = [
        "=", "≠", "≤", "≥", "<", ">", "∈", "∉", "⊆", "≡", "→", "↔", ":", "∥", "∣",
    ];
    let count: usize = all.iter().map(|s| sentence.matches(s).count()).sum();
    let worded = sentence
        .split(|c: char| !c.is_alphabetic())
        .any(|w| w.chars().count() > 1 && !w.chars().all(|c| c.is_uppercase()));
    if count != 1 || worded || sentence.contains(',') {
        return None;
    }
    let turns = [
        ("=", "="),
        ("≠", "≠"),
        ("≤", "≥"),
        ("≥", "≤"),
        ("<", ">"),
        (">", "<"),
    ];
    turns.iter().find_map(|(sign, turned)| {
        let (left, right) = sentence.split_once(&format!(" {sign} "))?;
        Some(format!("{} {turned} {}", right.trim(), left.trim()))
    })
}

/// A formula's sentences, each that is one relation turned around, or None
/// where none is.
fn sentences_turned(text: &str) -> Option<String> {
    let ends = text.trim_end().ends_with('.');
    let mut changed = false;
    let mut out = Vec::new();
    for s in sentences(text) {
        match relation_turned(&s) {
            Some(t) => {
                changed = true;
                out.push(t);
            }
            None => out.push(s),
        }
    }
    let mut joined = out.join(". ");
    if ends {
        joined.push('.');
    }
    changed.then_some(joined)
}

/// Every equation, disequation and order a claim, an assumption or a
/// statement writes as a sentence of its own, turned around: `a = b` and
/// `b = a` are one claim, as `x < y` and `y > x` are. A claim written over
/// several lines, and the statement of a theorem another cites, are left as
/// they are: the citer reads the statement the corpus elaborated, which this
/// test does not build again.
pub fn relations_turned(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let mut count = 0;
    let mut theorems = Vec::new();
    for (thm, end) in theorems_of(ctx, path, lines.len()) {
        let lay = layout(thm, &lines, end);
        let cited = ctx.cited.contains(&thm.qualified());
        let written = written_out_by_rows(thm);
        let mut spans: Vec<Region> = Vec::new();
        for claim in &lay.claims {
            let step = &thm.steps[claim.step];
            if claim.lines.len() == 1
                && !step.impossible
                && !written.contains(&step.number.to_string())
                && rows(&step.just, &thm.path).is_none()
            {
                if let Some(r) = lay
                    .regions
                    .iter()
                    .find(|r| r.line == claim.lines[0] && r.from == claim.from)
                {
                    spans.push(r.clone());
                }
            }
        }
        let assumed: Vec<usize> = thm
            .hypotheses
            .iter()
            .filter(|h| h.kind != Intro::Let && !cited)
            .filter(|h| h.label.as_ref().is_none_or(|l| !written.contains(l)))
            .map(|h| h.line - 1)
            .chain(thm.steps.iter().flat_map(|s| {
                s.openers
                    .iter()
                    .filter(|o| o.kind != Intro::Let && !o.is_hypothesis && !o.is_claim)
                    .filter(|o| !written.contains(&o.label))
                    .map(|o| o.line - 1)
            }))
            .collect();
        for l in assumed {
            if let Some(r) = lay.regions.iter().find(|r| r.line == l) {
                spans.push(r.clone());
            }
        }
        if !cited {
            for (l, line) in lines.iter().enumerate().take(end).skip(thm.line - 1) {
                if line.trim_start().starts_with("then ")
                    && !line.trim_end().ends_with(',')
                {
                    if let Some(r) = lay.regions.iter().find(|r| r.line == l) {
                        spans.push(r.clone());
                    }
                }
            }
        }
        spans.sort_by_key(|r| std::cmp::Reverse((r.line, r.from)));
        let mut changed = false;
        for r in spans {
            let c = chars(&lines[r.line]);
            let old: String = c[r.from..r.to].iter().collect();
            let Some(new) = sentences_turned(&old) else {
                continue;
            };
            let head: String = c[..r.from].iter().collect();
            let tail: String = c[r.to..].iter().collect();
            lines[r.line] = format!("{head}{new}{tail}");
            count += 1;
            changed = true;
        }
        if changed {
            theorems.push(thm.qualified());
        }
    }
    Rewritten {
        text: joined(lines, text),
        lines: count,
        theorems,
        declined: Vec::new(),
    }
}

/// The lines a step's rows write out as their first row, and the lines a
/// requires line names a manipulation of, by label or step number. Rows and
/// manipulations keep each relation the way round it is written, a turn
/// being a restate row of its own (`METHODS.md`, inequalities, Rows), so
/// such a line, and a claim a step's rows end on, are not spelt otherwise
/// by turning them round alone.
fn written_out_by_rows(thm: &Theorem) -> BTreeSet<String> {
    let first_rows = thm
        .steps
        .iter()
        .filter_map(|s| rows(&s.just, &thm.path)?.ok())
        .filter_map(|written| match written.first().map(|r| &r.reason) {
            Some(RowReason::Cited(r)) => Some(r.clone()),
            _ => None,
        });
    let manipulated = thm
        .steps
        .iter()
        .flat_map(|s| &s.requires)
        .filter(|r| matches!(&r.by, Ok(by) if matches!(by.head, Head::Manipulation(_))))
        .flat_map(|r| r.lines().to_vec());
    first_rows.chain(manipulated).collect()
}

/// The lines a step's citation is written on, from 0: its justification and
/// the lines it goes on to, or a requires line and the lines it goes on to.
struct Citation {
    lines: Vec<usize>,
    /// The values it gives what it cites, as the proof parser cut them from
    /// the justification or a requires line's reason.
    values: Values,
    /// The line of the step whose justification it is; None for a requires
    /// line's reason.
    step: Option<usize>,
}

fn citations_of(thm: &Theorem, lines: &[String], end: usize) -> Vec<Citation> {
    let mut out = Vec::new();
    for step in &thm.steps {
        let j = step.just.line - 1;
        let mut at = vec![j];
        at.extend(continued(lines, j, end));
        out.push(Citation {
            lines: at,
            values: step.just.values.clone(),
            step: Some(step.line),
        });
        for r in &step.requires {
            let l = r.line - 1;
            let mut at = vec![l];
            at.extend(continued(lines, l, end));
            out.push(Citation {
                lines: at,
                values: r.values().clone(),
                step: None,
            });
        }
    }
    out
}

/// The statement letters of every theorem another cites, renamed, and every
/// citation of it said again to match: a value given a renamed letter by
/// name is given it under the new name, and a letter a citation left to mean
/// the citer's own letter of that name is given that letter by name, since
/// the names no longer agree. Each such theorem's `let` letters are renamed
/// to letters the library binds that the theorem does not write. Its
/// elaborated statement, which a citer reads, numbers its classes by the
/// order of the `let` lines and so says the same either way.
pub fn statements_renamed(
    ctx: &Context,
    files: &[(String, String)],
) -> Vec<(String, Rewritten)> {
    let mut texts: BTreeMap<String, Vec<String>> = files
        .iter()
        .map(|(p, t)| (p.clone(), t.lines().map(str::to_string).collect()))
        .collect();
    let mut declined = Vec::new();
    // The renaming of each cited theorem, where its own lines take it.
    let mut renamings: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
    for (path, lines) in &texts {
        for (thm, end) in theorems_of(ctx, path, lines.len()) {
            if !ctx.cited.contains(&thm.qualified()) {
                continue;
            }
            let lay = layout(thm, lines, end);
            let used = match letters_used(ctx, lines, &lay) {
                Ok(used) => used,
                Err(why) => {
                    declined.push(Declined {
                        theorem: thm.qualified(),
                        why,
                    });
                    continue;
                }
            };
            let held = held_own(ctx, thm);
            let pool = library_pool(ctx, thm);
            let mut map = BTreeMap::new();
            let mut taken: BTreeSet<String> = BTreeSet::new();
            for h in thm.hypotheses.iter().filter(|h| h.kind == Intro::Let) {
                let Some(letter) =
                    let_letter(&parley::sorts::body_of(h.text.trim(), "let"))
                else {
                    continue;
                };
                if held.contains(&letter) {
                    continue;
                }
                let target = pool.iter().find(|t| {
                    class(t) == class(&letter)
                        && !t.contains('′')
                        && !used.iter().any(|u| u.trim_end_matches('′') == t.as_str())
                        && !held.contains(*t)
                        && !taken.contains(*t)
                        && !ctx.g.functions.contains_key(*t)
                });
                if let Some(t) = target {
                    taken.insert(t.clone());
                    map.insert(letter, t.clone());
                }
            }
            if map.is_empty() {
                continue;
            }
            if makes_pairs_for_themselves(thm, &map) {
                declined.push(Declined {
                    theorem: thm.qualified(),
                    why:
                        "the renaming gives a cited letter itself, `P := A` as `P := P`"
                            .to_string(),
                });
                continue;
            }
            let mut attempt = lines.clone();
            match rename(ctx, &mut attempt, &lay, &map) {
                Ok(_) => {
                    renamings.insert(thm.qualified(), map);
                }
                Err(why) => declined.push(Declined {
                    theorem: thm.qualified(),
                    why,
                }),
            }
        }
    }
    let item = re(r"\bthm:([A-Za-z0-9′-]+)");
    // A renaming that would give a cited letter itself, `A := P` as
    // `P := P`, is not made: no proof writes that pair where matching finds
    // the letter (`SYNTAX.md`, no pair says what goes without saying).
    for (path, lines) in &texts {
        for (thm, end) in theorems_of(ctx, path, lines.len()) {
            for citation in citations_of(thm, lines, end) {
                let Some(m) = item.captures(&lines[citation.lines[0]]) else {
                    continue;
                };
                let full = thm.names.full(&m[1]);
                let Some(map) = renamings.get(&full) else {
                    continue;
                };
                // The citer's letters are renamed too where it is cited
                // itself: `n := p` is `b := b` with n and p both renamed b.
                let own = renamings.get(&thm.qualified());
                let itself = citation.values.pairs().any(|(name, value)| {
                    let value = value.text().trim();
                    let value =
                        own.and_then(|o| o.get(value)).map_or(value, String::as_str);
                    map.get(name).is_some_and(|new| new == value)
                });
                if itself {
                    renamings.remove(&full);
                    declined.push(Declined {
                        theorem: full,
                        why: "a citation's pair would name a letter for itself"
                            .to_string(),
                    });
                }
            }
        }
    }
    let mut changed: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    let mut theorems: BTreeMap<String, Vec<String>> = BTreeMap::new();
    // Each citation of a renamed theorem, said again under its new names.
    for (path, lines) in texts.iter_mut() {
        for (thm, end) in theorems_of(ctx, path, lines.len()) {
            for citation in citations_of(thm, lines, end) {
                let first = citation.lines[0];
                let Some(m) = item.captures(&lines[first]) else {
                    continue;
                };
                let Some(map) = renamings.get(&thm.names.full(&m[1])) else {
                    continue;
                };
                let named: BTreeSet<String> =
                    citation.values.names().map(String::from).collect();
                for &l in &citation.lines {
                    let mut c = chars(&lines[l]);
                    let mut spans = assigned_names(&c);
                    spans.sort_by_key(|s| std::cmp::Reverse(s.0));
                    for (from, to) in spans {
                        let name: String = c[from..to].iter().collect();
                        if let Some(new) = map.get(&name) {
                            c.splice(from..to, new.chars());
                        }
                    }
                    let new: String = c.into_iter().collect();
                    if new != lines[l] {
                        lines[l] = new;
                        changed.entry(path.clone()).or_default().insert(l);
                    }
                }
                // A letter the citation leaves to the matcher is given what
                // the matcher makes it there, under its new name; one the
                // matcher does not fix meant the citer's letter of its name.
                // Where that is the citer's letter of the new name, the
                // names agree again and the citation still leaves it.
                let bound = citation
                    .step
                    .and_then(|l| ctx.bound.get(&(path.clone(), l)));
                let left: Vec<String> = map
                    .iter()
                    .filter(|(old, _)| !named.contains(*old))
                    .filter_map(|(old, new)| {
                        let value = bound.and_then(|b| b.get(old)).unwrap_or(old);
                        (value != new).then(|| format!("{new} := {value}"))
                    })
                    .collect();
                if left.is_empty() {
                    continue;
                }
                let at = item.find(&lines[first]).map(|m| m.end()).unwrap();
                let rest = lines[first][at..].to_string();
                let pairs = left.join(", ");
                let joint = if rest.trim().is_empty() || rest.starts_with(',') {
                    format!(" {pairs}")
                } else {
                    format!(" {pairs},")
                };
                lines[first] = format!("{}{joint}{rest}", &lines[first][..at]);
                changed.entry(path.clone()).or_default().insert(first);
            }
        }
    }
    // Each renamed theorem's own letters, throughout it.
    for (path, lines) in texts.iter_mut() {
        for (thm, end) in theorems_of(ctx, path, lines.len()) {
            let Some(map) = renamings.get(&thm.qualified()) else {
                continue;
            };
            let lay = layout(thm, lines, end);
            let before = lines.clone();
            match rename(ctx, lines, &lay, map) {
                Ok(_) => {
                    for (l, line) in lines.iter().enumerate() {
                        if *line != before[l] {
                            changed.entry(path.clone()).or_default().insert(l);
                        }
                    }
                    theorems
                        .entry(path.clone())
                        .or_default()
                        .push(thm.qualified());
                }
                Err(why) => {
                    *lines = before;
                    declined.push(Declined {
                        theorem: thm.qualified(),
                        why,
                    });
                }
            }
        }
    }
    let mut out = Vec::new();
    for (path, text) in files {
        let lines = &texts[path];
        let n = changed.get(path).map_or(0, BTreeSet::len);
        let here: Vec<Declined> = Vec::new();
        out.push((
            path.clone(),
            Rewritten {
                text: joined(lines.clone(), text),
                lines: n,
                theorems: theorems.remove(path).unwrap_or_default(),
                declined: here,
            },
        ));
    }
    if let Some((_, first)) = out.first_mut() {
        first.declined = declined;
    }
    out
}

/// A part of a claim a define names: what it is written as, and where it is
/// first written.
struct Part {
    text: String,
    /// The step whose claim writes it first, by its index in the theorem.
    step: usize,
    /// Whether it is a set, which the corpus names with a capital, or a
    /// number, which it names in lower case.
    set: bool,
}

/// A part the rewrite names, and what naming it changes.
struct Named {
    part: String,
    name: String,
    label: String,
    /// The line the define goes above, from 0: the first line of the step
    /// that writes the part first.
    at: usize,
    /// The step number that step is written as, for the `reads` line.
    step: String,
    /// The last line of each citation that now cites the define, from 0,
    /// with whether it already says `from`.
    cite: Vec<(usize, bool)>,
}

/// Every part of a claim written out, named by a define: `define t := …`
/// above the first step that writes it, `t` written for it from there on, and
/// the define cited by each step that cites an item for a formula the name
/// now stands in. A defined name is what it names (`SYNTAX.md`), so each
/// theorem says what it said. A define's body binds letters of its own, so a
/// cited lemma that binds one letter at two places, as `count-shift` binds i
/// on both sides, now meets two spellings of it, and an equation inside the
/// body is ordered with that letter bound as the page's is.
///
/// A part is named only where the rewrite can tell the theorem still reads
/// the same: a number or a set that binds a letter of its own, first written
/// in the claim of a step outside any block, whose other letters mean the
/// same on every line from there on, and which is written only in formulas
/// the rewrite reads and never in a requires line's fact or a define. Every
/// step that writes it, or cites a line that does, must still follow with the
/// name in its place: a step citing an item cites the define as well, unless
/// it both writes the part and cites a line that does; a step that carries
/// what its cited lines say, a substitution, an instance, a link of a
/// calculation, writes the part exactly where what it cites does; a block's
/// claim follows its last step, which writes the part where the claim does.
/// A part some step needs in any other way, as an `algebra` step would look
/// inside the name or a requires line rest on a line that names it, is left
/// written out everywhere. Parts that contain one another are not both
/// named.
pub fn parts_named(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let mut count = 0;
    let mut theorems = Vec::new();
    let mut declined = Vec::new();
    for (thm, end) in theorems_of(ctx, path, lines.len()) {
        let lay = layout(thm, &lines, end);
        let mut taken = match letters_used(ctx, &lines, &lay) {
            Ok(used) => used,
            Err(why) => {
                declined.push(Declined {
                    theorem: thm.qualified(),
                    why,
                });
                continue;
            }
        };
        let scope = &ctx.corpus.scopes[thm.scope];
        let mut number = 1 + thm
            .defines
            .iter()
            .chain(&scope.defines)
            .filter_map(|d| d.label.strip_prefix('D')?.parse::<usize>().ok())
            .max()
            .unwrap_or(0);
        for d in &scope.defines {
            if let Some(name) = d.text.split_whitespace().next() {
                taken.insert(name.to_string());
            }
        }
        let parts = match parts_of(ctx, thm) {
            Ok(parts) => parts,
            Err(why) => {
                declined.push(Declined {
                    theorem: thm.qualified(),
                    why,
                });
                continue;
            }
        };
        let mut chosen: Vec<Named> = Vec::new();
        for part in parts {
            if chosen
                .iter()
                .any(|c| c.part.contains(&part.text) || part.text.contains(&c.part))
            {
                continue;
            }
            let Some(cite) = naming_follows(ctx, thm, &lines, end, &lay, &part) else {
                continue;
            };
            let Some(name) = fresh_name(ctx, part.set, &taken) else {
                continue;
            };
            taken.insert(name.clone());
            let step = &thm.steps[part.step];
            chosen.push(Named {
                part: part.text,
                name,
                label: format!("D{number}"),
                at: step.line - 1,
                step: step.number.to_string(),
                cite,
            });
            number += 1;
        }
        if chosen.is_empty() {
            continue;
        }
        let mut changed: BTreeSet<usize> = BTreeSet::new();
        for c in &chosen {
            for (l, line) in lines.iter_mut().enumerate().take(end).skip(c.at) {
                if line.contains(&c.part) {
                    *line = line.replace(&c.part, &c.name);
                    changed.insert(l);
                }
            }
        }
        let mut cites: BTreeMap<usize, (bool, Vec<String>)> = BTreeMap::new();
        for c in &chosen {
            for &(l, from) in &c.cite {
                cites
                    .entry(l)
                    .or_insert((from, Vec::new()))
                    .1
                    .push(c.label.clone());
            }
        }
        for (l, (from, labels)) in cites {
            let joint = if from { ", " } else { ", from " };
            let line = lines[l].trim_end().to_string();
            lines[l] = format!("{line}{joint}{}", labels.join(", "));
            changed.insert(l);
        }
        let mut inserts: Vec<&Named> = chosen.iter().collect();
        inserts.sort_by_key(|c| std::cmp::Reverse(c.at));
        for c in inserts {
            let head = format!("let {} = {}", c.name, c.part);
            let pad = 70usize.saturating_sub(head.chars().count()).max(1);
            let define = format!("{head}{}({})", " ".repeat(pad), c.label);
            let reads = format!("       reads the part step {} writes out", c.step);
            lines.splice(c.at..c.at, [define, reads, String::new()]);
        }
        count += changed.len() + 2 * chosen.len();
        theorems.push(thm.qualified());
    }
    Rewritten {
        text: joined(lines, text),
        lines: count,
        theorems,
        declined,
    }
}

/// The parts a define could name, in the order the theorem first writes
/// them: each number or set that binds a letter of its own, written in the
/// claim of a step outside any block, whose free letters no binder of the
/// claim holds and only the theorem's header introduces.
fn parts_of(ctx: &Context, thm: &Theorem) -> Result<Vec<Part>, String> {
    let sorts = sorts_in_scope(
        thm,
        Env {
            g: &ctx.g,
            scopes: &ctx.corpus.scopes,
        },
    );
    let binders = ctx.g.binders();
    // A letter a block or an `obtain` introduces is not in scope above the
    // step where the define goes.
    let header: BTreeSet<String> = thm
        .hypotheses
        .iter()
        .filter(|h| h.kind == Intro::Let)
        .filter_map(|h| let_letter(&parley::sorts::body_of(h.text.trim(), "let")))
        .collect();
    let blocked: BTreeSet<String> = introduced(thm)
        .into_iter()
        .filter(|l| !header.contains(l))
        .collect();
    let mut out: Vec<Part> = Vec::new();
    for (index, step) in thm.steps.iter().enumerate() {
        if step.number.0.len() != 1 || step.impossible {
            continue;
        }
        for sentence in sentences(&step.claim_text()) {
            let tree = read_one(&sentence, &ctx.g, &sorts)
                .map_err(|p| format!("step {} does not read: {p}", step.number))?;
            let nodes = tree.walk();
            // A part free in a letter some binder of the sentence holds may
            // stand where that binder gives the letter its meaning, which a
            // define above the step would not, so it is not named.
            let held: BTreeSet<String> = nodes
                .iter()
                .filter_map(|n| binders.get(&n.notation()).map(|b| (n, b)))
                .flat_map(|(n, b)| {
                    b.held
                        .iter()
                        .filter_map(|&h| n.children.get(h))
                        .filter(|h| h.is_name())
                        .map(|h| h.text.to_string())
                        .collect::<Vec<_>>()
                })
                .collect();
            for node in nodes.iter().skip(1) {
                let term = node.sort.is("number") || node.sort.is("set");
                // Only a part the parser read from the sentence is cut from
                // it: a node it built without reading has no text of its own
                // to name.
                let read = node.span().is_some();
                let binds = node
                    .walk()
                    .iter()
                    .any(|n| binders.contains_key(&n.notation()));
                if !(term && read && binds) {
                    continue;
                }
                let Some(text) = node.written(&sentence) else {
                    continue;
                };
                let free = free_names(node, &binders);
                if free.iter().any(|f| held.contains(f) || blocked.contains(f)) {
                    continue;
                }
                let text = text.trim().to_string();
                if !out.iter().any(|p| p.text == text) {
                    out.push(Part {
                        text,
                        step: index,
                        set: node.sort.is("set"),
                    });
                }
            }
        }
    }
    Ok(out)
}

/// Where each `needle` starts in `line`, in characters.
fn char_places(line: &str, needle: &str) -> Vec<usize> {
    line.match_indices(needle)
        .map(|(byte, _)| line[..byte].chars().count())
        .collect()
}

/// The citations that cite the define where `part` is named from the step
/// that first writes it on, as `Named::cite` holds them; None where some
/// line would no longer follow, or the part is written where the rewrite
/// cannot tell what it is.
fn naming_follows(
    ctx: &Context,
    thm: &Theorem,
    lines: &[String],
    end: usize,
    lay: &Layout,
    part: &Part,
) -> Option<Vec<(usize, bool)>> {
    let first = thm.steps[part.step].line - 1;
    if !lines[first].contains(&part.text) {
        return None;
    }
    if lines[thm.line - 1..first]
        .iter()
        .any(|l| l.contains(&part.text))
    {
        return None;
    }
    // Written only in formulas, and never in a define or a requires line's
    // fact, which the rewrite does not cite the define for.
    let mut barred: BTreeSet<usize> = BTreeSet::new();
    for d in &thm.defines {
        let mut l = d.line - 1;
        while l < end && !lines[l].trim_start().starts_with("reads ") {
            barred.insert(l);
            l += 1;
        }
    }
    for step in &thm.steps {
        for r in &step.requires {
            barred.insert(r.line - 1);
            barred.extend(continued(lines, r.line - 1, end));
        }
    }
    let width = part.text.chars().count();
    for (l, line) in lines.iter().enumerate().take(end).skip(first) {
        for at in char_places(line, &part.text) {
            let inside = lay
                .regions
                .iter()
                .any(|r| r.line == l && r.from <= at && at + width <= r.to);
            if !inside || barred.contains(&l) {
                return None;
            }
        }
    }
    let writes = |l: &usize| lines[*l].contains(&part.text);
    let mut cite = Vec::new();
    for step in &thm.steps {
        if step.line - 1 < first {
            continue;
        }
        let j = step.just.line - 1;
        let claim: Vec<usize> = (step.line - 1..j).collect();
        let mut citation = vec![j];
        citation.extend(continued(lines, j, end));
        let links: Vec<usize> = step.just.chain.iter().map(|(_, no)| no - 1).collect();
        // What each line the step may cite says, as the checker reads it: a
        // line that writes the part will write the name in its place.
        let scope = statements_in_scope(
            thm,
            &CheckedTheorem::of(thm),
            step,
            Env {
                g: &ctx.g,
                scopes: &ctx.corpus.scopes,
            },
        );
        let says_part =
            |r: &str| scope.get(r).is_some_and(|t| t.text().contains(&part.text));
        let cites_part = step.just.refs.iter().any(|r| says_part(r));
        let writes_part = claim.iter().any(writes)
            || citation.iter().any(writes)
            || links.iter().any(writes);
        if !writes_part && !cites_part {
            continue;
        }
        // A requires line cites no define here, so one resting on a line that
        // will write the name could not say what the name is.
        if step
            .requires
            .iter()
            .any(|r| r.lines().iter().any(|c| says_part(c)))
        {
            return None;
        }
        match &step.just.head {
            // An item is read through the define wherever its own words or
            // what it cites hold the name, unless a cited line and the claim
            // both write it, which needs no define and might not use one.
            Head::Item { .. } => {
                if step.just.contradicting.is_some() || (writes_part && cites_part) {
                    return None;
                }
                let last = *citation.last().unwrap();
                let from = !step.just.from.is_empty();
                cite.push((last, from));
            }
            Head::Define | Head::Lines | Head::Manipulation(_) => return None,
            Head::Method(m) => match m {
                Method::Proof
                | Method::Contradiction
                | Method::Induction
                | Method::BothDirections => {}
                // Each link carries one line: it writes the name exactly where
                // the line it cites does.
                Method::Calculation => {
                    for &l in &links {
                        let cited =
                            chain_cited(&lines[l]).is_some_and(|r| says_part(&r));
                        if writes(&l) != cited {
                            return None;
                        }
                    }
                }
                Method::Substitute
                | Method::Join
                | Method::Restate
                | Method::Instantiate
                | Method::Exhibit
                | Method::Obtain
                | Method::Cases => {
                    if writes_part != cites_part {
                        return None;
                    }
                }
                // A chain's lines meet as they are written, so naming a part
                // in some of them and not others parts what met.
                Method::Algebra
                | Method::Arithmetic
                | Method::RealArithmetic
                | Method::Inequalities
                | Method::Transitivity
                | Method::Antisymmetry
                | Method::Membership
                | Method::Inspection => return None,
            },
        }
    }
    Some(cite)
}

/// A letter for the name of a part that nothing in reach writes: a capital
/// for a set, as the corpus writes sets, and a lower-case letter for a
/// number.
fn fresh_name(ctx: &Context, set: bool, taken: &BTreeSet<String>) -> Option<String> {
    let want = if set { 1 } else { 0 };
    let alphabet: Vec<String> = ('a'..='z')
        .chain('A'..='Z')
        .map(|c| c.to_string())
        .collect();
    ctx.library_letters
        .iter()
        .chain(&alphabet)
        .find(|l| {
            class(l) == want
                && is_one_letter(l)
                && l.chars().count() == 1
                && !taken.iter().any(|t| t.trim_end_matches('′') == l.as_str())
                && !ctx.constants.contains(*l)
                && !ctx.g.functions.contains_key(*l)
        })
        .cloned()
}

/// A citation's text with each step number `map` names said as the new
/// number, where a citation names a line: in a `from`, `join` or `restate`
/// list, and
/// after `line`, `contradicting`, `into` or `in`, as `references` and the
/// proof reader read them. A number anywhere else belongs to a formula.
fn renumbered_refs(text: &str, map: &BTreeMap<String, String>) -> String {
    let swap = |r: &str| map.get(r).cloned().unwrap_or_else(|| r.to_string());
    let lists =
        re(r"\b(from|join|restate)(\s+)([A-Za-z0-9.′]+(?:\s*,\s*[A-Za-z0-9.′]+)*)");
    let text = lists.replace_all(text, |c: &regex::Captures| {
        let items: Vec<String> = c[3]
            .split(',')
            .map(|item| {
                let lead = &item[..item.len() - item.trim_start().len()];
                format!("{lead}{}", swap(item.trim()))
            })
            .collect();
        format!("{}{}{}", &c[1], &c[2], items.join(","))
    });
    let single = re(r"\b(line|contradicting|into|in)(\s+)([0-9]+(?:\.[0-9]+)*)\b");
    single
        .replace_all(&text, |c: &regex::Captures| {
            format!("{}{}{}", &c[1], &c[2], swap(&c[3]))
        })
        .into_owned()
}

/// Whether line `l` goes on with a `from`, `join` or `restate` list the line above it
/// leaves open: the line above ends in a comma inside such a list, or is
/// itself nothing but more of one. The proof reader joins the two, so the
/// lines and labels on `l` are cited as surely as those before the break.
fn goes_on_list(lines: &[String], l: usize) -> bool {
    let Some(above) = l.checked_sub(1).map(|a| lines[a].trim()) else {
        return false;
    };
    let Some(listed) = above.strip_suffix(',') else {
        return false;
    };
    let opened =
        re(r"\b(?:from|join|restate)\s+([A-Za-z0-9.′]+(?:\s*,\s*[A-Za-z0-9.′]+)*)$");
    opened.is_match(listed)
        || (listed.split(',').all(|item| is_cited_name(item.trim()))
            && goes_on_list(lines, l - 1))
}

/// Whether `item` is written as a cited line or label is: a step number, `H1`,
/// `IH`, `2′`.
fn is_cited_name(item: &str) -> bool {
    !item.is_empty()
        && item
            .chars()
            .all(|c| c.is_alphanumeric() || c == '.' || c == '′')
}

/// Line `l` as a citation rewrite reads it: one going on with a list from
/// the line above (`goes_on_list`) is given the `from` it continues, which
/// `listed_back` takes away again.
fn as_listed(lines: &[String], l: usize) -> (String, bool) {
    let line = &lines[l];
    if !goes_on_list(lines, l) {
        return (line.clone(), false);
    }
    let lead = line.len() - line.trim_start().len();
    (format!("{}from {}", &line[..lead], &line[lead..]), true)
}

/// A line `as_listed` gave a `from`, rewritten, with that `from` taken away.
fn listed_back(text: String, given: bool) -> String {
    if !given {
        return text;
    }
    let lead = text.len() - text.trim_start().len();
    let rest = text[lead..].strip_prefix("from ").unwrap_or(&text[lead..]);
    format!("{}{rest}", &text[..lead])
}

/// Line `l`'s citations said as `map` says them, a line going on with a
/// list from the line above read as more of that list.
fn renumbered_line(
    lines: &[String],
    l: usize,
    map: &BTreeMap<String, String>,
) -> String {
    let (text, given) = as_listed(lines, l);
    listed_back(renumbered_refs(&text, map), given)
}

/// A step's induction hypothesis said as `map` says it: the hypothesis
/// names the step it is the hypothesis of, `assume step 2 is true for m`.
/// The lines changed.
fn renumbered_hypothesis(
    step: &parley::corpus::Step,
    lines: &mut [String],
    map: &BTreeMap<String, String>,
) -> usize {
    let hypothesis = re(r"\b(assume\s+step\s+)([0-9]+(?:\.[0-9]+)*)(\s+is\s+true\b)");
    let mut changed = 0;
    for o in &step.openers {
        let l = o.line - 1;
        let new = hypothesis
            .replace(&lines[l], |c: &regex::Captures| {
                let number =
                    map.get(&c[2]).cloned().unwrap_or_else(|| c[2].to_string());
                format!("{}{number}{}", &c[1], &c[3])
            })
            .into_owned();
        if new != lines[l] {
            lines[l] = new;
            changed += 1;
        }
    }
    changed
}

/// A chain line with the line it cites at its right end (`chain_cited`)
/// said as `map` says it.
fn renumbered_link(line: &str, map: &BTreeMap<String, String>) -> String {
    let end = line.trim_end().len();
    let start = line[..end].rfind(char::is_whitespace).map_or(0, |i| i + 1);
    match map.get(&line[start..end]) {
        Some(new) => format!("{}{new}{}", &line[..start], &line[end..]),
        None => line.to_string(),
    }
}

/// Whether `fact` says the term `claim` says is in a number system, of a
/// system holding that one: `|A| ∈ ℝ` of `|A| ∈ ℕ₀`.
fn widened(fact: &str, claim: &str) -> bool {
    match (membership_of(fact), membership_of(claim)) {
        (Some(wide), Some(narrow)) => {
            wide.term == narrow.term && narrow.system <= wide.system
        }
        _ => false,
    }
}

/// The number systems, each inside the next.
const SYSTEMS: [&str; 6] = ["ℕ", "ℕ₀", "ℤ", "ℚ", "ℝ", "ℂ"];

/// A membership in a number system as a line writes it: the term, and the
/// system by its place among `SYSTEMS`.
struct Membership {
    term: String,
    system: usize,
}

/// `t ∈ S` read off a fact with S a number system; None for any other.
fn membership_of(said: &str) -> Option<Membership> {
    let (term, set) = said.trim().trim_end_matches('.').split_once(" ∈ ")?;
    let system = SYSTEMS.iter().position(|s| *s == set.trim())?;
    Some(Membership {
        term: term.trim().to_string(),
        system,
    })
}

/// `from 2, 17` without 17, and `membership, from 14` without 14 as
/// `membership`; None where nothing would be left.
fn without_ref(how: &str, gone: &str) -> Option<String> {
    let how = how.trim();
    let at = how.rfind("from ")?;
    let head = how[..at].trim_end().trim_end_matches(',').trim_end();
    let kept: Vec<&str> = how[at + "from ".len()..]
        .split(',')
        .map(str::trim)
        .filter(|r| *r != gone)
        .collect();
    match (head.is_empty(), kept.is_empty()) {
        (true, true) => None,
        (false, true) => Some(head.to_string()),
        (true, false) => Some(format!("from {}", kept.join(", "))),
        (false, false) => Some(format!("{head}, from {}", kept.join(", "))),
    }
}

/// The methods a requires line may name as its one citation, as a step may.
const REQUIRES_METHODS: [Method; 4] = [
    Method::Membership,
    Method::Arithmetic,
    Method::Inequalities,
    Method::Algebra,
];

/// A step that serves only requires lines, written as a requires line of
/// each step that rests on it: `READERS.md`'s dull fact, which konigsberg's
/// walk-parity moved by hand and so found the checker calling a needed line
/// surplus twice. The step's claim and justification become `requires
/// claim: justification`, its own requires lines go with it above, as a
/// requires line may rest on those above it (`SYNTAX.md`), each requires
/// line that cited it cites it no more, one that only restated it goes,
/// and the steps after it are numbered again, with every citation of them.
///
/// A step moves only where the move is one the syntax allows and leaves
/// nothing to guess: its claim is one sentence on one line, its
/// justification one citation on one line, a cited item or a method a
/// requires line may name, it opens no block and is not the last of its
/// run, nothing cites it but requires lines, and a step it moves into does
/// not already state one of the facts it carries. The first such step of
/// each theorem moves.
pub fn dull_steps_moved(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let mut count = 0;
    let mut theorems = Vec::new();
    for (thm, end) in theorems_of(ctx, path, lines.len()) {
        if let Some(changed) = dull_step_moved(thm, &mut lines, end) {
            count += changed;
            theorems.push(thm.qualified());
        }
    }
    Rewritten {
        text: joined(lines, text),
        lines: count,
        theorems,
        declined: Vec::new(),
    }
}

/// A step's one requires line, citing an item, written as a numbered step
/// just before it, which the step cites in its `from` list: a fact that
/// needs a citation of its own may be a numbered step before the step that
/// needs it (`SYNTAX.md`), and is the hypothesis of the step's item a cited
/// line supplies. The item the requires line cites is then cited before the
/// step's own, which changes the order a theorem cites what it cites:
/// konigsberg's odd-vertices cited walk-parity in a step and degree-by-walk
/// in its requires line, and its files were included in that order, though
/// walk-parity rests on degree-by-walk. The steps from there on are numbered
/// again, with every citation of them.
///
/// Only a requires line that is its step's only one moves, so nothing rests
/// on it or is rested on unseen; its fact is one sentence and its reason one
/// line; and the step cites an item on one line, ending in its `from` list
/// and not in `contradicting`, so the new step's number joins that list.
/// The first such line of each theorem moves.
pub fn requires_raised(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let mut count = 0;
    let mut theorems = Vec::new();
    for (thm, end) in theorems_of(ctx, path, lines.len()) {
        if let Some(changed) = requires_raised_in(thm, &mut lines, end) {
            count += changed;
            theorems.push(thm.qualified());
        }
    }
    Rewritten {
        text: joined(lines, text),
        lines: count,
        theorems,
        declined: Vec::new(),
    }
}

/// The first requires line of `thm` that can be raised to a step, raised;
/// the number of lines it changed, or None where none can.
fn requires_raised_in(
    thm: &Theorem,
    lines: &mut Vec<String>,
    end: usize,
) -> Option<usize> {
    let single = |l: usize| !lines[l - 1].trim_end().ends_with(',');
    for step in &thm.steps {
        let [req] = step.requires.as_slice() else {
            continue;
        };
        // The claim's first line, after the step's number.
        let claim = str::trim(
            lines[step.line - 1]
                .trim()
                .split_once(char::is_whitespace)?
                .1,
        )
        .to_string();
        // A claim saying "for all x ∈ L, …" binds x for its requires lines
        // too, f(x) ∈ ℤ under "for all x ∈ L, f(x) ∈ ℝ", and a step of its
        // own above it would leave x unbound.
        let quantified = claim.starts_with("For all ") || claim.starts_with("for all ");
        if quantified
            || !step.just.head.is_item()
            || step.just.target.is_some()
            || step.just.contradicting.is_some()
            || !step.just.chain.is_empty()
            || req.cited_item().is_none()
            || req.fact.text().contains(". ")
            || !single(step.just.line)
            || !single(req.line)
            || !lines[step.line - 1].contains(claim.as_str())
        {
            continue;
        }
        let raised = step.number.to_string();
        let heading = step.line - 1;
        let prefix: String = {
            let at = lines[heading].find(claim.as_str())?;
            lines[heading][..at].to_string()
        };
        let reason_indent: String = lines[step.just.line - 1]
            .chars()
            .take_while(|c| c.is_whitespace())
            .collect();
        // The new step takes the step's number.
        let changed = moved_down(thm, lines, end, step);
        // The step cites the new one, and its requires line goes.
        let reason = step.just.line - 1;
        let cites = if step.just.from.is_empty() {
            format!("{}, from {raised}", lines[reason].trim_end())
        } else {
            format!("{}, {raised}", lines[reason].trim_end())
        };
        lines[reason] = cites;
        lines.remove(req.line - 1);
        // The heading as the step was written, before it was numbered again,
        // carries the number the new step takes.
        let new_step = vec![
            format!("{prefix}{}", req.fact.text().trim()),
            format!("{reason_indent}{}", req.how.trim()),
            String::new(),
        ];
        for (i, line) in new_step.into_iter().enumerate() {
            lines.insert(heading + i, line);
        }
        return Some(changed + 4);
    }
    None
}

/// `step` and the rest of its run moved down one number, with every line
/// citing them; the number of lines changed. The heading of `step` itself
/// carries its new number too, so a step written in its place is written
/// whole.
fn moved_down(
    thm: &Theorem,
    lines: &mut [String],
    end: usize,
    step: &parley::corpus::Step,
) -> usize {
    let map = run_shifted(thm, step, |n| n >= step.number.0[step.number.len() - 1], 1);
    renumbered(thm, lines, end, &map)
}

/// The numbers of `step`'s run, and of the steps inside them, that `moves`
/// picks by their place in the run, each moved by `by`.
fn run_shifted(
    thm: &Theorem,
    step: &parley::corpus::Step,
    moves: impl Fn(u32) -> bool,
    by: i32,
) -> BTreeMap<String, String> {
    let depth = step.number.len();
    let mut map: BTreeMap<String, String> = BTreeMap::new();
    for other in &thm.steps {
        let v = &other.number.0;
        if v.len() >= depth
            && v[..depth - 1] == step.number.0[..depth - 1]
            && moves(v[depth - 1])
        {
            let mut w = v.clone();
            w[depth - 1] = w[depth - 1].saturating_add_signed(by);
            map.insert(
                other.number.to_string(),
                parley::corpus::proof::StepNo(w).to_string(),
            );
        }
    }
    map
}

/// Every step of `thm` numbered as `map` says, with every line citing one;
/// the number of lines changed.
fn renumbered(
    thm: &Theorem,
    lines: &mut [String],
    end: usize,
    map: &BTreeMap<String, String>,
) -> usize {
    let mut changed = 0;
    for other in &thm.steps {
        let at = other.line - 1;
        if let Some(new) = map.get(&other.number.to_string()) {
            let old = format!("{}.", other.number);
            if let Some(i) = lines[at].find(&old) {
                lines[at].replace_range(i..i + old.len(), &format!("{new}."));
                changed += 1;
            }
        }
        let mut cited: Vec<usize> = vec![other.just.line - 1];
        cited.extend(continued(lines, other.just.line - 1, end));
        for r in &other.requires {
            cited.push(r.line - 1);
            cited.extend(continued(lines, r.line - 1, end));
        }
        for l in cited {
            let new = renumbered_line(lines, l, map);
            if new != lines[l] {
                lines[l] = new;
                changed += 1;
            }
        }
        // A chain line cites a line at its right end, and so does the first
        // row of an inequalities step; a later row names a manipulation,
        // whose `adding 1` is no line.
        for (_, at) in other.just.chain.iter().chain(other.just.rows.first()) {
            let new = renumbered_link(&lines[at - 1], map);
            if new != lines[at - 1] {
                lines[at - 1] = new;
                changed += 1;
            }
        }
        changed += renumbered_hypothesis(other, lines, map);
    }
    // A define's reason cites lines as a step's does.
    for reason in thm.defines.iter().filter_map(|d| d.reason.as_ref()) {
        let mut cited = vec![reason.line - 1];
        cited.extend(continued(lines, reason.line - 1, end));
        for l in cited {
            let new = renumbered_line(lines, l, map);
            if new != lines[l] {
                lines[l] = new;
                changed += 1;
            }
        }
    }
    changed
}

/// Every define in a proof raised to the start of its run of steps: above
/// each step before it in the same run and part that introduces no letter,
/// writes no name the define gives and is no define. Konigsberg moved its
/// defines to where each is first used; a define written higher says the
/// same, since nothing it reads is introduced in between and nothing in
/// between reads what it names (`SYNTAX.md`: a definition is used only
/// below where it is written). A define giving more than one name stays.
pub fn defines_raised(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let mut count = 0;
    let mut theorems = Vec::new();
    for (thm, _) in theorems_of(ctx, path, lines.len()) {
        let mut defines: Vec<&parley::corpus::proof::DefineLine> = thm
            .defines
            .iter()
            .filter(|d| d.line > thm.conclusion_line)
            .collect();
        // From the bottom, so each define's lines are where they were read.
        defines.sort_by_key(|d| std::cmp::Reverse(d.line));
        let mut changed = false;
        for d in defines {
            if let Some(n) = define_raised(thm, d, &mut lines) {
                count += n;
                changed = true;
            }
        }
        if changed {
            theorems.push(thm.qualified());
        }
    }
    Rewritten {
        text: joined(lines, text),
        lines: count,
        theorems,
        declined: Vec::new(),
    }
}

/// One define of `thm` raised as `defines_raised` says; the lines it moved,
/// or None where it stays.
fn define_raised(
    thm: &Theorem,
    d: &parley::corpus::proof::DefineLine,
    lines: &mut Vec<String>,
) -> Option<usize> {
    // One name, read as the tools read it; sequences by recursion stay.
    let parts = parley::corpus::define::define_parts(&d.text);
    let parley::outcome::Built(parley::corpus::define::DefineParts::One(one)) = parts
    else {
        return None;
    };
    let name = one.name;
    let reads = d.line;
    if !lines.get(reads)?.trim_start().starts_with("reads ") {
        return None;
    }
    let next = thm.steps.iter().find(|s| s.line > d.line)?;
    let parent = next.number.parent();
    let run: Vec<&parley::corpus::proof::Step> = thm
        .steps
        .iter()
        .filter(|s| {
            s.number.parent() == parent && s.line < d.line && s.part == next.part
        })
        .collect();
    let named = |from: usize, to: usize| {
        lines[from..to].iter().any(|l| {
            if name.chars().count() == 1 {
                loose_letters(l).contains(&name)
            } else {
                re(&format!(r"\b{}\b", regex::escape(&name))).is_match(l)
            }
        })
    };
    let mut target: Option<usize> = None;
    let mut below = d.line - 1;
    for s in run.iter().rev() {
        let introduces =
            s.just.head.is(Method::Obtain) || s.just.head.is(Method::Exhibit);
        let define_between = thm
            .defines
            .iter()
            .any(|o| o.line != d.line && o.line > s.line && o.line < below + 1);
        if introduces || define_between || named(s.line - 1, below) {
            break;
        }
        target = Some(s.line - 1);
        below = s.line - 1;
    }
    let target = target?;
    let mut taken: Vec<String> = vec![lines[d.line - 1].clone(), lines[reads].clone()];
    let mut gone = 2;
    if lines.get(reads + 1).is_some_and(|l| l.trim().is_empty()) {
        gone += 1;
    }
    for _ in 0..gone {
        lines.remove(d.line - 1);
    }
    taken.push(String::new());
    for (i, line) in taken.into_iter().enumerate() {
        lines.insert(target + i, line);
    }
    Some(3)
}

/// One edit to `lines`: what goes at a line, from 0, or a line taken out.
enum LineEdit {
    Insert(usize, Vec<String>),
    Remove(usize),
}

/// The first step of `thm` that serves only requires lines, moved into them;
/// the number of lines it changed, or None where no step can move.
fn dull_step_moved(
    thm: &Theorem,
    lines: &mut Vec<String>,
    end: usize,
) -> Option<usize> {
    let single = |l: usize| !lines[l - 1].trim_end().ends_with(',');
    let numbers: BTreeSet<String> =
        thm.steps.iter().map(|s| s.number.to_string()).collect();
    for (n, step) in thm.steps.iter().enumerate() {
        let no = step.number.to_string();
        // A claim on one line, the one its number is on.
        if step.just.line != step.line + 1 {
            continue;
        }
        let claim = &step.claim_text();
        let head_ok = match &step.just.head {
            Head::Item { .. } => true,
            Head::Method(m) => REQUIRES_METHODS.contains(m),
            Head::Define | Head::Lines | Head::Manipulation(_) => false,
        };
        let mut next = step.number.0.clone();
        *next.last_mut()? += 1;
        let next = parley::corpus::proof::StepNo(next).to_string();
        let opens = numbers
            .iter()
            .any(|other| other.starts_with(&format!("{no}.")));
        if !head_ok
            || step.just.target.is_some()
            || !step.just.values.is_empty()
            || !step.just.chain.is_empty()
            // A requires line has one reason and no rows under it.
            || !step.just.rows.is_empty()
            || step.just.contradicting.is_some()
            || step.just.unproduced.is_some()
            || !step.parts.is_empty()
            || !step.openers.is_empty()
            || step.note.is_some()
            || step.impossible
            || opens
            || !numbers.contains(&next)
            || claim.contains(". ")
            || re(r"\S:").is_match(claim)
            || !lines[step.line - 1].contains(claim.as_str())
            || !single(step.just.line)
            || step.requires.iter().any(|r| !single(r.line))
        {
            continue;
        }
        // Who cites it: only requires lines may.
        let mut citers: Vec<(usize, usize)> = Vec::new();
        let mut otherwise = false;
        for (s, other) in thm.steps.iter().enumerate() {
            if s == n {
                continue;
            }
            otherwise |= other.just.refs.contains(&no)
                || other.just.contradicting.as_deref() == Some(no.as_str());
            for (k, r) in other.requires.iter().enumerate() {
                // A manipulation, `weakening, from 5`, names the one line
                // it manipulates, and with it gone names none.
                let manipulates =
                    r.by.as_ref()
                        .is_ok_and(|by| matches!(by.head, Head::Manipulation(_)));
                if r.lines().contains(&no) {
                    otherwise |= manipulates;
                    citers.push((s, k));
                }
            }
        }
        if otherwise || citers.is_empty() {
            continue;
        }
        let carried: Vec<String> = step
            .requires
            .iter()
            .map(|r| format!("requires {}: {}", r.fact, r.how))
            .chain(std::iter::once(format!(
                "requires {claim}: {}",
                step.just.text
            )))
            .collect();
        let carried_facts: BTreeSet<&str> = step
            .requires
            .iter()
            .map(|r| r.fact.text())
            .chain(std::iter::once(claim.as_str()))
            .collect();
        // Each citing line said again, or taken out where it only restated
        // the step.
        let mut said: Vec<(usize, Option<String>)> = Vec::new();
        let mut fits = true;
        for &(s, k) in &citers {
            let r = &thm.steps[s].requires[k];
            let line = &lines[r.line - 1];
            let Some(at) = line.rfind(r.how.trim()) else {
                fits = false;
                break;
            };
            if !single(r.line) {
                fits = false;
                break;
            }
            // A line saying what the step says, or that its term is in a
            // number system holding the step's, |A| ∈ ℝ from |A| ∈ ℕ₀, says
            // nothing the moved line does not, and goes with the move.
            if r.fact.text().trim() == claim.trim() || widened(r.fact.text(), claim) {
                said.push((r.line - 1, None));
                continue;
            }
            match without_ref(&r.how, &no) {
                Some(how) => {
                    said.push((r.line - 1, Some(format!("{}{how}", &line[..at]))))
                }
                None => {
                    fits = false;
                    break;
                }
            }
        }
        let gone: BTreeSet<usize> = said
            .iter()
            .filter(|(_, new)| new.is_none())
            .map(|(l, _)| *l)
            .collect();
        // A line that goes may be the only one citing its item, whose import
        // would then cite nothing; such a step is left where it is.
        let item = re(r"\b[a-z]+:[A-Za-z0-9′-]+");
        let orphaned = gone.iter().any(|&l| {
            item.find(&lines[l]).is_some_and(|m| {
                let cited = m.as_str();
                !lines
                    .iter()
                    .enumerate()
                    .any(|(k, other)| !gone.contains(&k) && other.contains(cited))
            })
        });
        fits &= !orphaned;
        let resting: BTreeSet<usize> = citers.iter().map(|(s, _)| *s).collect();
        for &s in &resting {
            let restated = thm.steps[s].requires.iter().any(|r| {
                !gone.contains(&(r.line - 1))
                    && carried_facts.contains(r.fact.text().trim())
            });
            fits &= !restated;
        }
        if !fits {
            continue;
        }
        // The steps after it, numbered again.
        let depth = step.number.len();
        let mut map: BTreeMap<String, String> = BTreeMap::new();
        for other in &thm.steps {
            let v = &other.number.0;
            if v.len() >= depth
                && v[..depth - 1] == step.number.0[..depth - 1]
                && v[depth - 1] > step.number.0[depth - 1]
            {
                let mut w = v.clone();
                w[depth - 1] -= 1;
                map.insert(
                    other.number.to_string(),
                    parley::corpus::proof::StepNo(w).to_string(),
                );
            }
        }
        for (l, new) in &said {
            if let Some(new) = new {
                lines[*l] = new.clone();
            }
        }
        let mut changed = said.len();
        for (s, other) in thm.steps.iter().enumerate() {
            if s == n {
                continue;
            }
            let heading = other.line - 1;
            if let Some(new) = map.get(&other.number.to_string()) {
                let old = format!("{}.", other.number);
                if let Some(at) = lines[heading].find(&old) {
                    lines[heading]
                        .replace_range(at..at + old.len(), &format!("{new}."));
                    changed += 1;
                }
            }
            let mut cited: Vec<usize> = vec![other.just.line - 1];
            cited.extend(continued(lines, other.just.line - 1, end));
            for r in &other.requires {
                cited.push(r.line - 1);
                cited.extend(continued(lines, r.line - 1, end));
            }
            for l in cited {
                let new = renumbered_line(lines, l, &map);
                if new != lines[l] {
                    lines[l] = new;
                    changed += 1;
                }
            }
            // As `renumbered` does: a chain line's cited line, and the first
            // row's.
            for (_, at) in other.just.chain.iter().chain(other.just.rows.first()) {
                let new = renumbered_link(&lines[at - 1], &map);
                if new != lines[at - 1] {
                    lines[at - 1] = new;
                    changed += 1;
                }
            }
            changed += renumbered_hypothesis(other, lines, &map);
        }
        // The carried lines go above the first line of each step that cited
        // the step, and the step's own lines go.
        let mut edits: Vec<LineEdit> = Vec::new();
        for &s in &resting {
            let first = citers
                .iter()
                .filter(|(t, _)| *t == s)
                .map(|&(t, k)| thm.steps[t].requires[k].line - 1)
                .min()?;
            let indent: String = lines[first]
                .chars()
                .take_while(|c| c.is_whitespace())
                .collect();
            edits.push(LineEdit::Insert(
                first,
                carried.iter().map(|c| format!("{indent}{c}")).collect(),
            ));
            changed += carried.len();
        }
        edits.extend(gone.iter().map(|&l| LineEdit::Remove(l)));
        let last = std::iter::once(step.just.line)
            .chain(step.requires.iter().map(|r| r.line))
            .max()?
            - 1;
        let mut own: Vec<usize> = (step.line - 1..=last).collect();
        if lines.get(last + 1).is_some_and(|l| l.trim().is_empty()) {
            own.push(last + 1);
        }
        changed += own.len();
        edits.extend(own.into_iter().map(LineEdit::Remove));
        // From the bottom up, so that each edit's line is where it was read;
        // at one line a removal goes before what is put there.
        let place = |e: &LineEdit| match e {
            LineEdit::Insert(l, _) => (*l, 0),
            LineEdit::Remove(l) => (*l, 1),
        };
        edits.sort_by_key(|e| std::cmp::Reverse(place(e)));
        for e in edits {
            match e {
                LineEdit::Insert(l, new) => {
                    for (i, line) in new.into_iter().enumerate() {
                        lines.insert(l + i, line);
                    }
                }
                LineEdit::Remove(l) => {
                    lines.remove(l);
                }
            }
        }
        return Some(changed);
    }
    None
}

/// Each step a theorem numbers at the top that has a block, lifted out as a
/// theorem of the same file and cited where it was: a block made a lemma.
/// The lemma states the step's claim and proves it by the block, numbered
/// again under step 1. Its hypotheses are the theorem's `let` lines whose
/// letters it writes, and what the block cites from outside it: a
/// hypothesis keeps its label, and a step above is assumed, a sentence to a
/// line, under a label of its own, its names introduced by `let` where it
/// obtained them. The step then cites the lemma, from each line it assumes
/// and each `let` a citation asks for (`citing::library`, `facts`): a
/// membership not in a number system, a part, a function being something.
///
/// Every statement the corpus proves in a block becomes one a citation must
/// reach, written with every binder, define and introduction the corpus
/// has. A block is left where it is where lifting it cannot be read off the
/// text: it writes a name the theorem defines, a define sits beside it, or
/// it cites a line above in a place only one label can stand.
pub fn blocks_lifted(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let mut count = 0;
    let mut theorems = Vec::new();
    let mut declined = Vec::new();
    for (thm, end) in theorems_of(ctx, path, lines.len()) {
        match lifted(ctx, thm, &lines, end) {
            Ok(Some(lift)) => {
                count += lift.changed;
                theorems.push(thm.qualified());
                lines.splice(thm.line - 1..end, lift.region);
            }
            Ok(None) => {}
            Err(why) => declined.push(Declined {
                theorem: thm.qualified(),
                why,
            }),
        }
    }
    Rewritten {
        text: joined(lines, text),
        lines: count,
        theorems,
        declined,
    }
}

/// A theorem's lines with its blocks lifted: the lemmas, then the theorem.
struct Lifted {
    region: Vec<String>,
    changed: usize,
}

/// One block made a lemma: the lemma's lines, the lines of the theorem the
/// step's block took up, and what the step is written as instead.
struct Lemma {
    lines: Vec<String>,
    from: usize,
    to: usize,
    citing: Vec<String>,
}

/// One hypothesis of a lemma: its line's text after the keyword's place,
/// `let n ∈ ℕ` or `assume n² is even`, and its label.
struct Assumed {
    text: String,
    label: String,
    /// The names it writes, read.
    names: BTreeSet<String>,
}

fn lifted(
    ctx: &Context,
    thm: &Theorem,
    lines: &[String],
    end: usize,
) -> Result<Option<Lifted>, String> {
    let tops: Vec<&parley::corpus::Step> =
        thm.steps.iter().filter(|s| s.number.0.len() == 1).collect();
    let has_block = |s: &parley::corpus::Step| {
        thm.steps
            .iter()
            .any(|o| o.number.0.len() > 1 && o.number.0[0] == s.number.0[0])
    };
    let blocks: Vec<&parley::corpus::Step> =
        tops.iter().copied().filter(|s| has_block(s)).collect();
    if blocks.is_empty() {
        return Ok(None);
    }
    let named = names_given(thm);
    let sorts = sorts_in_scope(
        thm,
        Env {
            g: &ctx.g,
            scopes: &ctx.corpus.scopes,
        },
    );
    let mut why = Vec::new();
    let mut lemmas = Vec::new();
    for step in blocks {
        match lemma_of(ctx, thm, lines, end, step, &tops, &named, &sorts) {
            Ok(lemma) => lemmas.push(lemma),
            Err(e) => why.push(format!("step {}: {e}", step.number)),
        }
    }
    if lemmas.is_empty() {
        return Err(why.join("; "));
    }
    let mut region = Vec::new();
    let mut changed = 0;
    for lemma in &lemmas {
        changed += lemma.lines.len() + lemma.citing.len();
        region.extend(lemma.lines.iter().cloned());
        region.push(String::new());
    }
    let mut i = thm.line - 1;
    while i < end {
        match lemmas.iter().find(|l| l.from == i) {
            Some(lemma) => {
                region.extend(lemma.citing.iter().cloned());
                i = lemma.to;
            }
            None => {
                region.push(lines[i].clone());
                i += 1;
            }
        }
    }
    Ok(Some(Lifted { region, changed }))
}

/// The names a theorem's defines give, as the define reader reads them:
/// its defines, recursions and named numbers, which a lemma could not
/// write without giving them again.
fn names_given(thm: &Theorem) -> BTreeSet<String> {
    thm.defines
        .iter()
        .filter_map(|d| match define_parts(&d.text) {
            Built(parts) => Some(parts.names()),
            parley::outcome::Declined(_) => None,
        })
        .flatten()
        .collect()
}

/// Formula text read by the front end, each sentence a tree; a sentence
/// that does not read leaves the block where it is.
fn read_all(
    ctx: &Context,
    sorts: &Sorts,
    written: &Written,
) -> Result<Vec<Node>, String> {
    written
        .sentences()
        .iter()
        .map(|s| {
            s.read(&ctx.g, sorts)
                .map_err(|p| format!("`{}` does not read: {}", s.text(), p.message))
        })
        .collect()
}

/// Every formula a step writes, as the skeleton reader cuts it, but for the
/// values its citations name, which are read only together (`Values`): its
/// claim, its requires lines, a substitution's equation, a chain's terms,
/// and what its opening lines say. An induction hypothesis writes no
/// formula of its own.
fn formulas_written(
    thm: &Theorem,
    step: &parley::corpus::Step,
) -> Result<Vec<Written>, String> {
    let path = &thm.path;
    let mut written: Vec<Written> = vec![step.claim.clone()];
    for r in &step.requires {
        written.push(r.fact.clone());
    }
    written.extend(step.just.equation.clone());
    if let Some(read) = chain(&step.just, path) {
        let read =
            read.map_err(|p| format!("step {}'s chain: {}", step.number, p.message))?;
        written.push(read.start);
        for link in read.lines {
            written.push(link.term);
            written.extend(link.modulus);
        }
    }
    for o in step.openers.iter().filter(|o| !o.is_hypothesis) {
        let body = o.body(path);
        match o.kind {
            Intro::Let => written.extend(Introduction::read(body).parts()),
            _ => written.push(body),
        }
    }
    Ok(written)
}

/// Whether formula text writes a quantifier that leaves `name`'s set to a
/// range line: `for all ε > 0`, `there is δ > 0`. Read as the checker reads
/// it (`check_ranges`), by its tokens, since its tree is the long form's.
fn leaves_set_out(ctx: &Context, written: &Written, name: &str) -> bool {
    const ORDERS: [&str; 5] = [">", "≥", "<", "≤", "≠"];
    written.sentences().iter().any(|s| {
        ctx.tokens(s.text()).is_some_and(|tokens| {
            tokens.windows(4).any(|w| {
                matches!(
                    (w[0].text.as_str(), w[1].text.as_str()),
                    ("for", "all") | ("there", "is") | ("there", "exists")
                ) && w[2].kind == TokenKind::Name
                    && w[2].text == name
                    && ORDERS.contains(&w[3].text.as_str())
            })
        })
    })
}

/// What a hypothesis of the theorem writes, read: a `let` line's parts, as
/// its introduction cuts them, and any other line's sentences.
fn hypothesis_read(
    ctx: &Context,
    sorts: &Sorts,
    thm: &Theorem,
    h: &parley::corpus::Hypothesis,
) -> Result<Vec<Node>, String> {
    let body = h.body(&thm.path);
    let parts = match h.kind {
        Intro::Let => Introduction::read(body).parts(),
        _ => vec![body],
    };
    let mut out = Vec::new();
    for w in &parts {
        out.extend(read_all(ctx, sorts, w)?);
    }
    Ok(out)
}

/// Every name the trees write.
fn names_in(trees: &[Node]) -> BTreeSet<String> {
    trees.iter().flat_map(|t| t.names()).collect()
}

/// Whether a citation of a lemma is asked to supply what its `let` says, as
/// `citing::library` reads a hypothesis: a sort, a set, a point, a function's
/// type and a membership in a number system it is not.
fn let_asked(
    ctx: &Context,
    sorts: &Sorts,
    path: &str,
    body: &str,
) -> Result<bool, String> {
    use parley::sorts::introduction::Form;
    let written = Written::new(body, path, 0);
    let introduced = Introduction::read(written.clone());
    Ok(match introduced.form {
        Form::Set(_)
        | Form::Point(_)
        | Form::Function
        | Form::Element(_)
        | Form::Group { .. }
        | Form::Graph(_) => false,
        // A membership is said once where its set is a number system.
        Form::Member => !read_all(ctx, sorts, &written)?.iter().all(|m| {
            m.notation() == parley::notations::MEMBERSHIP
                && m.children.get(1).is_some_and(|set| {
                    set.notation() == parley::notations::NUMBER_SYSTEMS
                })
        }),
        _ => true,
    })
}

#[allow(clippy::too_many_arguments)]
fn lemma_of(
    ctx: &Context,
    thm: &Theorem,
    lines: &[String],
    end: usize,
    step: &parley::corpus::Step,
    tops: &[&parley::corpus::Step],
    named: &BTreeSet<String>,
    sorts: &Sorts,
) -> Result<Lemma, String> {
    let top = step.number.0[0];
    let inner: Vec<&parley::corpus::Step> =
        thm.steps.iter().filter(|o| o.number.0[0] == top).collect();
    let start = step.line - 1;
    let next = tops
        .iter()
        .map(|t| t.line - 1)
        .filter(|&l| l > start)
        .min()
        .unwrap_or(end);
    if thm
        .defines
        .iter()
        .any(|d| d.line - 1 > start && d.line - 1 < next)
    {
        return Err("a define sits in or after the block".into());
    }
    let mut stop = next;
    while stop > start && lines[stop - 1].trim().is_empty() {
        stop -= 1;
    }
    // What the block writes, read.
    let mut block_written: Vec<Written> = Vec::new();
    for s in &inner {
        block_written.extend(formulas_written(thm, s)?);
    }
    let mut block_trees: Vec<Node> = Vec::new();
    for w in &block_written {
        block_trees.extend(read_all(ctx, sorts, w)?);
    }
    for s in &inner {
        let values = std::iter::once(&s.just.values)
            .chain(s.requires.iter().map(|r| r.values()));
        for v in values {
            let read = v.read(&ctx.g, sorts).map_err(|p| {
                format!("step {}'s values do not read: {}", s.number, p.message)
            })?;
            block_trees.extend(read.into_iter().map(|v| v.value));
        }
    }
    let mut used = names_in(&block_trees);
    if let Some(name) = used.iter().find(|u| named.contains(*u)) {
        return Err(format!("it writes {name}, which the theorem defines"));
    }
    // What the block cites, and which of it is outside the block.
    let mut internal: BTreeSet<String> = BTreeSet::new();
    for s in &inner {
        internal.insert(s.number.to_string());
        for o in &s.openers {
            internal.insert(o.label.clone());
        }
    }
    let mut outside: Vec<String> = Vec::new();
    for s in &inner {
        let mut refs = s.just.refs.clone();
        refs.extend(s.just.contradicting.clone());
        for r in &s.requires {
            refs.extend(r.lines().iter().cloned());
        }
        for r in refs {
            if r != "arithmetic" && !internal.contains(&r) && !outside.contains(&r) {
                outside.push(r);
            }
        }
    }
    let hypothesis = |label: &str| {
        thm.hypotheses
            .iter()
            .find(|h| h.label.as_deref() == Some(label))
    };
    // A label for each line a step above gives, past every H the theorem uses.
    let taken: BTreeSet<String> = thm
        .hypotheses
        .iter()
        .filter_map(|h| h.label.clone())
        .chain(internal.iter().cloned())
        .collect();
    let mut fresh = (1..)
        .map(|n| format!("H{n}"))
        .filter(move |l| !taken.contains(l));
    let obtained = re(r"^obtain\s+(.+?)(?::|\s+from\b)");
    let mut map: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut above: Vec<Assumed> = Vec::new();
    let mut cite: Vec<String> = Vec::new();
    for t in tops.iter().filter(|t| t.line - 1 < start) {
        let number = t.number.to_string();
        let names: Vec<String> = obtained
            .captures(&t.just.text)
            .map(|m| m[1].split(',').map(|n| n.trim().to_string()).collect())
            .unwrap_or_default();
        let is_cited = outside.contains(&number);
        let names_used = names.iter().any(|n| used.contains(n));
        if !is_cited && !names_used {
            continue;
        }
        // A name the step obtains is introduced by `let`, as its membership,
        // its function's type or its sort. What the step says is assumed in
        // one line, as the step says it in one, memberships and all: a
        // citation of the step stands for that line, and a method citing it
        // has the bounds a membership gives, as it had from the step.
        let mut labels = Vec::new();
        let mut asks = false;
        let mut said_all: Vec<Node> = Vec::new();
        for sentence in t.claim.sentences() {
            let said = sentence.read(&ctx.g, sorts).map_err(|p| {
                format!("step {} does not read: {}", t.number, p.message)
            })?;
            said_all.push(said.clone());
            // A sentence introducing an obtained name: its membership or
            // its function's type, which a `let` writes as the step does,
            // or its sort, which a `let` writes with `be`.
            let Some(name) = said
                .children
                .first()
                .filter(|c| c.is_name() && names.iter().any(|n| *n == c.text))
            else {
                continue;
            };
            let polynomial = said.notation() == parley::notations::IS_A_POLYNOMIAL
                || said.children.get(1).is_some_and(|set| {
                    set.notation() == parley::notations::POLYNOMIALS
                });
            let introduced = match said.notation() {
                _ if polynomial => format!("{} be a polynomial", name.text),
                parley::notations::MEMBERSHIP | parley::notations::FUNCTION_TYPE => {
                    ctx.g.print(&said)
                }
                _ => continue,
            };
            asks |= let_asked(ctx, sorts, &thm.path, &introduced)?;
            above.push(Assumed {
                text: format!("let {introduced}"),
                label: fresh.next().expect("labels without end"),
                names: said.names(),
            });
        }
        // A line saying only that a term other than a letter is a number,
        // `|c| + 1 ∈ ℝ`, may be one the citation of the lemma builds from
        // the lines it cites besides (`SYNTAX.md`, a term a line puts in a
        // number system), and then citing it does no work.
        let only_memberships = !said_all.is_empty()
            && said_all.iter().all(|s| {
                s.notation() == parley::notations::MEMBERSHIP
                    && s.children.first().is_some_and(|t| !t.is_name())
                    && s.children.get(1).is_some_and(|set| {
                        set.notation() == parley::notations::NUMBER_SYSTEMS
                    })
            });
        if is_cited && only_memberships {
            return Err(format!(
                "it cites {number}, which says only that a term is a number, as the lemma's citation may build it"
            ));
        }
        if is_cited {
            let label = fresh.next().expect("labels without end");
            labels.push(label.clone());
            let names = names_in(&said_all);
            let whole = conjoined(&ctx.g, said_all)
                .ok_or_else(|| format!("step {} says nothing", t.number))?;
            above.push(Assumed {
                text: format!("assume {}", ctx.g.print(&whole)),
                label,
                names,
            });
        }
        if is_cited || asks {
            cite.push(number.clone());
        }
        if is_cited {
            map.insert(number, labels);
        }
    }
    // Each line cited from outside is a hypothesis of the theorem or a step
    // above, now assumed.
    for r in &outside {
        if hypothesis(r).is_none() && !map.contains_key(r) {
            return Err(format!(
                "it cites {r}, which is no hypothesis nor a step above"
            ));
        }
    }
    for a in &above {
        used.extend(a.names.iter().cloned());
    }
    // The theorem's `let` lines the lemma needs, and the names those write.
    let mut read_hypotheses: Vec<BTreeSet<String>> = Vec::new();
    for h in &thm.hypotheses {
        read_hypotheses.push(names_in(&hypothesis_read(ctx, sorts, thm, h)?));
    }
    // An `assume` is needed where the block cites it, and where it is what
    // gives a name the lemma writes its sort, as `assume H is a subgroup of
    // G` gives H, which no `let` writes.
    let by_let: BTreeSet<String> = thm
        .hypotheses
        .iter()
        .zip(&read_hypotheses)
        .filter(|(h, _)| h.kind == Intro::Let)
        .flat_map(|(_, writes)| writes.iter().cloned())
        .collect();
    let mut kept: BTreeSet<usize> = BTreeSet::new();
    loop {
        let before = kept.len();
        for (i, h) in thm.hypotheses.iter().enumerate() {
            let writes = &read_hypotheses[i];
            let needed = match h.kind {
                Intro::Let => writes.iter().any(|l| used.contains(l)),
                _ => {
                    h.label.as_ref().is_some_and(|l| outside.contains(l))
                        || writes
                            .iter()
                            .any(|l| used.contains(l) && !by_let.contains(l))
                }
            };
            if needed && kept.insert(i) {
                used.extend(writes.iter().cloned());
            }
        }
        if kept.len() == before {
            break;
        }
    }
    let name = format!("{}-{}", thm.name, step.number);
    if ctx
        .corpus
        .theorems
        .iter()
        .any(|t| t.path == thm.path && t.name == name)
    {
        return Err(format!("the file already has a theorem {name}"));
    }
    // The lemma's lines.
    let claim = step.claim.text().trim().to_string();
    // A range line belongs to a statement that leaves the set out, which
    // the step's claim may not do though its block does.
    let mut out = vec![format!("theorem {name}")];
    for r in &thm.ranges {
        if r.names.iter().any(|n| leaves_set_out(ctx, &step.claim, n)) {
            out.push(format!("  {}", r.text.trim()));
        } else if r
            .names
            .iter()
            .any(|n| block_written.iter().any(|w| leaves_set_out(ctx, w, n)))
        {
            return Err(format!(
                "its block leans on `{}`, which its claim does not",
                r.text.trim()
            ));
        }
    }
    let hyp_line = |text: &str, label: &str| format!("  {:<66}  ({label})", text);
    for (i, h) in thm.hypotheses.iter().enumerate() {
        if !kept.contains(&i) {
            continue;
        }
        // The line as the parser cut it: its keyword and its body, with its
        // label apart.
        let body = h.body(&thm.path);
        let text = format!("{} {}", h.kind.as_str(), body.text());
        match &h.label {
            Some(l) => {
                out.push(hyp_line(&text, l));
                // A `let` is cited where a citation asks what it says, and
                // every `assume` the lemma keeps.
                let asked = match h.kind {
                    Intro::Let => let_asked(ctx, sorts, &thm.path, body.text())?,
                    _ => true,
                };
                if asked {
                    cite.insert(0, l.clone());
                }
            }
            None => out.push(format!("  {text}")),
        }
    }
    for a in &above {
        out.push(hyp_line(&a.text, &a.label));
    }
    out.push(format!("  then {claim}"));
    out.push(String::new());
    // The block, numbered again under step 1, its citations of lines above
    // said by the labels they now have.
    for s in &inner {
        let mut v = s.number.0.clone();
        v[0] = 1;
        map.insert(
            s.number.to_string(),
            vec![parley::corpus::proof::StepNo(v).to_string()],
        );
    }
    let mut reasons: BTreeSet<usize> = BTreeSet::new();
    let mut links: BTreeSet<usize> = BTreeSet::new();
    let mut headings: BTreeSet<usize> = BTreeSet::new();
    for s in &inner {
        headings.insert(s.line - 1);
        reasons.insert(s.just.line - 1);
        reasons.extend(continued(lines, s.just.line - 1, end));
        for r in &s.requires {
            reasons.insert(r.line - 1);
            reasons.extend(continued(lines, r.line - 1, end));
        }
        for o in &s.openers {
            reasons.insert(o.line - 1);
        }
        // A chain line and the first row of an inequalities step each cite a
        // line at their right end.
        for (_, at) in s.just.chain.iter().chain(s.just.rows.first()) {
            links.insert(at - 1);
        }
    }
    for (i, line) in lines[start..stop].iter().enumerate() {
        let at = start + i;
        let new = if headings.contains(&at) {
            renumbered_heading(line, &map)
        } else if links.contains(&at) {
            relabelled_link(line, &map)?
        } else if reasons.contains(&at) {
            let (text, given) = as_listed(lines, at);
            listed_back(relabelled_refs(&text, &map)?, given)
        } else {
            line.clone()
        };
        out.push(new);
    }
    // The step as it is cited instead.
    let indent: String = lines[step.just.line - 1]
        .chars()
        .take_while(|c| c.is_whitespace())
        .collect();
    let mut citing: Vec<String> = lines[start..step.just.line - 1].to_vec();
    let mut seen = BTreeSet::new();
    cite.retain(|c| seen.insert(c.clone()));
    citing.push(if cite.is_empty() {
        format!("{indent}thm:{name}")
    } else {
        format!("{indent}thm:{name}, from {}", cite.join(", "))
    });
    citing.extend(lines[stop..next].iter().cloned());
    Ok(Lemma {
        lines: out,
        from: start,
        to: next,
        citing,
    })
}

/// A step's heading with its number said as `map` says it, the claim kept
/// in its column.
fn renumbered_heading(line: &str, map: &BTreeMap<String, Vec<String>>) -> String {
    let lead = line.len() - line.trim_start().len();
    let rest = &line[lead..];
    let Some(dot) = rest.find(char::is_whitespace) else {
        return line.to_string();
    };
    let number = rest[..dot].trim_end_matches('.');
    match map.get(number).and_then(|v| v.first()) {
        Some(new) => {
            let said = format!("{new}.");
            let width = dot.max(said.len());
            format!("{}{:<width$}{}", &line[..lead], said, &rest[dot..])
        }
        None => line.to_string(),
    }
}

/// The one label `map` gives a reference standing where one line goes.
fn one_label(
    map: &BTreeMap<String, Vec<String>>,
    r: &str,
) -> Result<Option<String>, String> {
    match map.get(r).map(Vec::as_slice) {
        None => Ok(None),
        Some([one]) => Ok(Some(one.clone())),
        Some(_) => Err(format!(
            "{r} is cited where one line stands, and says several"
        )),
    }
}

/// A justification, requires or opening line with each line it cites said
/// as `map` says it: in a `from` or `join` list, a reference may become
/// several; after `line`, `contradicting`, and in `step N is true`, it must
/// stay one. A step number given a label loses its `line`.
fn relabelled_refs(
    text: &str,
    map: &BTreeMap<String, Vec<String>>,
) -> Result<String, String> {
    let lists =
        re(r"\b(from|join|restate)(\s+)([A-Za-z0-9.′]+(?:\s*,\s*[A-Za-z0-9.′]+)*)");
    let text = lists
        .replace_all(text, |c: &regex::Captures| {
            let items: Vec<String> = c[3]
                .split(',')
                .map(|item| {
                    let lead = &item[..item.len() - item.trim_start().len()];
                    match map.get(item.trim()) {
                        Some(new) => format!("{lead}{}", new.join(", ")),
                        None => item.to_string(),
                    }
                })
                .collect();
            format!("{}{}{}", &c[1], &c[2], items.join(","))
        })
        .into_owned();
    let mut fault = None;
    let numbered = |s: &str| s.chars().all(|c| c.is_ascii_digit() || c == '.');
    let line = re(r"\bline(\s+)([0-9]+(?:\.[0-9]+)*)\b");
    let text = line
        .replace_all(&text, |c: &regex::Captures| match one_label(map, &c[2]) {
            Ok(Some(new)) if numbered(&new) => format!("line{}{new}", &c[1]),
            Ok(Some(new)) => new,
            Ok(None) => c[0].to_string(),
            Err(e) => {
                fault = Some(e);
                c[0].to_string()
            }
        })
        .into_owned();
    let single = re(r"\b(contradicting|step)(\s+)([A-Za-z0-9.′]+?)(\.?)(\s|$)");
    let text = single
        .replace_all(&text, |c: &regex::Captures| {
            match one_label(map, c[3].trim_end_matches('.')) {
                Ok(Some(new)) => format!("{}{}{new}{}{}", &c[1], &c[2], &c[4], &c[5]),
                Ok(None) => c[0].to_string(),
                Err(e) => {
                    fault = Some(e);
                    c[0].to_string()
                }
            }
        })
        .into_owned();
    match fault {
        Some(e) => Err(e),
        None => Ok(text),
    }
}

/// A chain line with the line it cites at its right end said as `map` says
/// it, which must be one.
fn relabelled_link(
    line: &str,
    map: &BTreeMap<String, Vec<String>>,
) -> Result<String, String> {
    let end = line.trim_end().len();
    let start = line[..end].rfind(char::is_whitespace).map_or(0, |i| i + 1);
    Ok(match one_label(map, &line[start..end])? {
        Some(new) => format!("{}{new}{}", &line[..start], &line[end..]),
        None => line.to_string(),
    })
}

/// Each step obtaining from an item written as two: a step claiming the
/// item's "there is", cited as a step citing it is, and an obtain from that
/// line (`SYNTAX.md`, `obtain`). The "there is" is what the item says, each
/// letter as the checker reads it at the step (`checker::obtained_there`).
/// From a definition that unfolds it is the one the obtain's claim states
/// (`ELABORATION.md`): each name runs over the set its membership sentence
/// gives, in the order the obtain names them, and the other sentences are
/// what is said of them, in the order written. The
/// corpus obtains from items far more often than it claims their "there
/// is", so this puts each such fact on the route a proof meets least.
pub fn obtains_claimed(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut text = text.to_string();
    let mut count = 0;
    let mut theorems = Vec::new();
    let mut declined = Vec::new();
    let Some(scope) = ctx
        .corpus
        .theorems
        .iter()
        .find(|t| t.path == path)
        .map(|t| t.scope)
    else {
        return Rewritten {
            text,
            lines: 0,
            theorems,
            declined,
        };
    };
    // The file read again after each obtain is rewritten. The last is
    // rewritten first, so every one above it is on the line the checker
    // read it on, and is as many obtains from the top as it was.
    let mut at = None;
    loop {
        let (_, mut thms) = parse_proof(path, &text, scope).expect("the file reads");
        thms.sort_by_key(|t| t.line);
        let lines: Vec<String> = text.lines().map(str::to_string).collect();
        let mut obtains = Vec::new();
        for (i, thm) in thms.iter().enumerate() {
            let end = thms.get(i + 1).map_or(lines.len(), |n| n.line - 1);
            for step in &thm.steps {
                if step.just.head.is(Method::Obtain) && step.just.cited_item().is_some()
                {
                    obtains.push((thm, end, step));
                }
            }
        }
        let next = match at {
            None => obtains.len(),
            Some(i) => i,
        };
        if next == 0 {
            break;
        }
        at = Some(next - 1);
        let (thm, end, step) = obtains[next - 1];
        let mut lines = lines;
        match obtain_claimed(ctx, path, thm, &mut lines, end, step) {
            Ok(changed) => {
                count += changed;
                if !theorems.contains(&thm.qualified()) {
                    theorems.push(thm.qualified());
                }
                text = joined(lines, &text);
            }
            Err(why) => declined.push(Declined {
                theorem: thm.qualified(),
                why: format!("step {}: {why}", step.number),
            }),
        }
    }
    Rewritten {
        text,
        lines: count,
        theorems,
        declined,
    }
}

/// The names an obtain introduces, as its justification lists them before
/// the item: `obtain p, q: thm:x` names p and q.
fn obtained_names(how: &str) -> Option<Vec<String>> {
    let names = re(r"^obtain\s+([^:]+):").captures(how.trim())?;
    Some(names[1].split(',').map(|n| n.trim().to_string()).collect())
}

/// The "there is" an obtain's claim states, as a tree: each name over the
/// set its membership sentence gives, or the functions its type gives, and
/// what the other sentences say of them.
fn existence_of(
    ctx: &Context,
    sorts: &Sorts,
    claim: &Written,
    names: &[String],
) -> Result<Node, String> {
    let read = read_all(ctx, sorts, claim)?;
    let made = |pattern: &str, children: Vec<Node>| {
        made_as(&ctx.g, pattern, children)
            .ok_or_else(|| format!("no notation is written {pattern}"))
    };
    let mut over: BTreeMap<String, (Node, Node)> = BTreeMap::new();
    let mut said = Vec::new();
    for node in read {
        let named = |n: &Node| {
            n.is_name()
                && names.iter().any(|m| *m == n.text)
                && !over.contains_key(n.text.as_str())
        };
        match (node.notation(), node.spelling(), node.children.as_slice()) {
            // "There is f : X → Y" runs over the functions from X to Y.
            (parley::notations::FUNCTION_TYPE, _, [f, from, to]) if named(f) => {
                let functions =
                    made("the functions from _ to _", vec![from.clone(), to.clone()])?;
                over.insert(f.text.to_string(), (f.clone(), functions));
            }
            (_, parley::notations::IN, [x, set]) if named(x) => {
                over.insert(x.text.to_string(), (x.clone(), set.clone()));
            }
            _ => said.push(node),
        }
    }
    let mut body =
        conjoined(&ctx.g, said).ok_or("the claim says nothing of what it obtains")?;
    for name in names.iter().rev() {
        let (x, set) = over
            .get(name)
            .ok_or_else(|| format!("the claim states no membership of {name}"))?;
        body = made("there is _ ∈ _ with _", vec![x.clone(), set.clone(), body])?;
    }
    Ok(body)
}

/// One obtain written as a step claiming its "there is" and an obtain from
/// that step's line; the number of lines changed.
fn obtain_claimed(
    ctx: &Context,
    path: &str,
    thm: &Theorem,
    lines: &mut Vec<String>,
    end: usize,
    step: &parley::corpus::Step,
) -> Result<usize, String> {
    let names = obtained_names(&step.just.text).ok_or("the obtain names nothing")?;
    let original = ctx
        .corpus
        .theorems
        .iter()
        .find(|t| t.qualified() == thm.qualified())
        .ok_or("the theorem is not in the corpus")?;
    let sorts = sorts_in_scope(
        original,
        Env {
            g: &ctx.g,
            scopes: &ctx.corpus.scopes,
        },
    );
    // What the item says there is, where the obtain asks it of the item; a
    // definition that unfolds gives the existence the claim states.
    let there_is = match ctx.obtained.get(&(path.to_string(), step.line)) {
        Some(Built(said)) => match said.as_slice() {
            [one] => one.clone(),
            _ => return Err("the item says more than its \"there is\"".into()),
        },
        Some(Route::Declined(why)) => return Err(why.reason()),
        None => ctx
            .g
            .print(&existence_of(ctx, &sorts, &step.claim, &names)?),
    };
    // A step reading a defined name as what it names cites the define
    // (`SYNTAX.md`), and an obtain from a line cites nothing else.
    let binders = ctx.g.binders();
    let free = |trees: Vec<Node>| -> BTreeSet<String> {
        trees.iter().flat_map(|t| free_names(t, &binders)).collect()
    };
    let claimed = free(read_all(ctx, &sorts, &step.claim)?);
    let stated = free(read_all(
        ctx,
        &sorts,
        &Written::new(there_is.clone(), path, step.line),
    )?);
    let defined: Vec<&String> = claimed
        .iter()
        .filter(|n| !stated.contains(*n) && !names.contains(n))
        .collect();
    if !defined.is_empty() {
        return Err(format!(
            "the claim writes {}, which the \"there is\" writes out, and an obtain from a line cites no define",
            defined.iter().map(|n| n.as_str()).collect::<Vec<_>>().join(", ")
        ));
    }
    let heading = step.line - 1;
    let reason = step.just.line - 1;
    let number = format!("{}.", step.number);
    let at = lines[heading]
        .find(&number)
        .ok_or("the step's number is not where it is read")?;
    let claim_at = at
        + number.len()
        + lines[heading][at + number.len()..]
            .chars()
            .take_while(|c| c.is_whitespace())
            .map(char::len_utf8)
            .sum::<usize>();
    let prefix = lines[heading][..claim_at].to_string();
    let claim_lines: Vec<String> = lines[heading..reason].to_vec();
    let mut last = continued(lines, reason, end)
        .last()
        .copied()
        .unwrap_or(reason);
    for r in &step.requires {
        let l = r.line - 1;
        last = last.max(continued(lines, l, end).last().copied().unwrap_or(l));
    }
    let reason_indent: String = lines[reason]
        .chars()
        .take_while(|c| c.is_whitespace())
        .collect();
    let from = lines[reason]
        .find("obtain ")
        .ok_or("the obtain is not where it is read")?;
    let item_at = from
        + lines[reason][from..]
            .find(':')
            .ok_or("the obtain names no item")?
        + 1;
    let cited = lines[reason][item_at..].trim_start().to_string();
    let mut changed = moved_down(thm, lines, end, step);
    // The obtain, under the number the run moved it to, from the new line.
    let mut obtain: Vec<String> = vec![String::new()];
    obtain.extend(claim_lines);
    obtain[1] = lines[heading].clone();
    obtain.push(format!(
        "{reason_indent}obtain {} from line {}",
        names.join(", "),
        step.number
    ));
    // The step claiming the "there is", under the obtain's own number.
    let claimed = vec![
        format!("{prefix}{there_is}"),
        format!("{}{cited}", &lines[reason][..from]),
    ];
    changed += obtain.len() + claimed.len();
    // The reason's continued lines and the requires lines stay with the
    // step that cites the item.
    let after: Vec<String> = lines.drain(last + 1..).collect();
    let kept: Vec<String> = lines.drain(reason + 1..).collect();
    lines.truncate(heading);
    lines.extend(claimed);
    lines.extend(kept);
    lines.extend(obtain);
    lines.extend(after);
    Ok(changed)
}

/// A define of one name, on one line with its `reads` line under it, and
/// the names its term writes free beside its own arguments, read by the
/// front end with the theorem's sorts. A recursion, a define over several
/// lines and one saying a kind of number, which a reason under it proves,
/// are declined.
struct Movable {
    name: String,
    /// The line, from 0, the define is written on; its `reads` line is the
    /// next.
    at: usize,
    label: String,
    uses: BTreeSet<String>,
}

fn movable(
    ctx: &Context,
    sorts: &Sorts,
    d: &parley::corpus::proof::DefineLine,
    lines: &[String],
) -> Result<Movable, String> {
    let parts = parley::corpus::define::define_parts(&d.text);
    let Built(DefineParts::One(one)) = parts else {
        return Err(format!("{} is a recursion", d.label));
    };
    if one.kind.is_some() || d.reason.is_some() {
        return Err(format!("{} says a kind of number", d.label));
    }
    let at = d.line - 1;
    if !lines[at].trim_start().starts_with("let ")
        || !lines
            .get(at + 1)
            .is_some_and(|l| l.trim_start().starts_with("reads "))
    {
        return Err(format!("{} is written over several lines", d.label));
    }
    let binders = ctx.g.binders();
    let mut uses: BTreeSet<String> = read_all(ctx, sorts, &d.rule(&one.body))?
        .iter()
        .flat_map(|t| free_names(t, &binders))
        .collect();
    // A domain names what it is over as the rule does: `for k ∈ {1, …, N}`
    // names N.
    for p in &one.params {
        uses.extend(
            read_all(ctx, sorts, &d.domain(p))?
                .iter()
                .flat_map(|t| free_names(t, &binders)),
        );
    }
    for p in &one.params {
        uses.remove(&p.name);
    }
    Ok(Movable {
        name: one.name,
        at,
        label: d.label.clone(),
        uses,
    })
}

/// The names a theorem's header gives or writes: what its hypotheses say,
/// read, and the names its header defines give.
fn header_names(
    ctx: &Context,
    sorts: &Sorts,
    thm: &Theorem,
) -> Result<BTreeSet<String>, String> {
    let mut out = BTreeSet::new();
    for h in &thm.hypotheses {
        out.extend(names_in(&hypothesis_read(ctx, sorts, thm, h)?));
    }
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        if let Built(parts) = define_parts(&d.text) {
            out.extend(parts.names());
        }
    }
    for r in &thm.ranges {
        out.extend(ctx.letters_of(&r.text));
    }
    Ok(out)
}

/// The names the defines above a file's first theorem give.
fn file_names(ctx: &Context, thm: &Theorem) -> BTreeSet<String> {
    ctx.corpus.scopes[thm.scope]
        .defines
        .iter()
        .filter_map(|d| match define_parts(&d.text) {
            Built(parts) => Some(parts.names()),
            parley::outcome::Declined(_) => None,
        })
        .flatten()
        .collect()
}

/// Whether `name` is written on any of `lines`.
fn writes(lines: &[String], name: &str) -> bool {
    lines.iter().any(|l| {
        if name.chars().count() == 1 {
            loose_letters(l).contains(name)
        } else {
            re(&format!(r"\b{}\b", regex::escape(name))).is_match(l)
        }
    })
}

/// Each define in a theorem's header over nothing the theorem names raised
/// above the file's first theorem, where it is the file's (`SYNTAX.md`): a
/// naming `let` written as a `define`, `:=` for `=`. The statement and the
/// steps then speak of a define from outside the theorem, which the
/// statement means written out, as it meant the header's. A define whose
/// name another theorem of the file writes stays, and one whose label the
/// file gives elsewhere takes a label the file does not give.
pub fn header_defines_raised(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let mut count = 0;
    let mut theorems = Vec::new();
    let mut declined = Vec::new();
    let mut raised: Vec<String> = Vec::new();
    let thms = theorems_of(ctx, path, lines.len());
    let Some(first) = thms.iter().map(|(t, _)| t.line).min() else {
        return Rewritten {
            text: text.to_string(),
            lines: 0,
            theorems,
            declined,
        };
    };
    // Every label the file gives, so a raised define takes a new one where
    // its own is given elsewhere.
    let label_re = re(r"\(([A-Z])(\d+)\)\s*$");
    let mut given: BTreeMap<String, usize> = BTreeMap::new();
    for l in &lines {
        if let Some(c) = label_re.captures(l) {
            *given.entry(format!("{}{}", &c[1], &c[2])).or_default() += 1;
        }
    }
    let mut next_label = given
        .keys()
        .filter_map(|l| l.strip_prefix('D').and_then(|n| n.parse::<usize>().ok()))
        .max()
        .unwrap_or(0)
        + 1;
    for (thm, end) in &thms {
        let sorts = sorts_in_scope(
            thm,
            Env {
                g: &ctx.g,
                scopes: &ctx.corpus.scopes,
            },
        );
        let header: Vec<&parley::corpus::proof::DefineLine> = thm
            .defines
            .iter()
            .filter(|d| d.line < thm.conclusion_line)
            .collect();
        if header.is_empty() {
            continue;
        }
        let own = match header_names(ctx, &sorts, thm) {
            Ok(n) => n,
            Err(why) => {
                declined.push(Declined {
                    theorem: thm.qualified(),
                    why,
                });
                continue;
            }
        };
        let files = file_names(ctx, thm);
        let elsewhere: Vec<String> = lines[..thm.line - 1]
            .iter()
            .chain(lines[*end..].iter())
            .cloned()
            .collect();
        let mut moved: Vec<(Movable, String)> = Vec::new();
        let mut why = Vec::new();
        for d in header {
            let m = match movable(ctx, &sorts, d, &lines) {
                Ok(m) => m,
                Err(e) => {
                    why.push(e);
                    continue;
                }
            };
            let named: Vec<&String> = m
                .uses
                .iter()
                .filter(|n| own.contains(*n) && !files.contains(*n))
                .collect();
            if !named.is_empty() {
                why.push(format!(
                    "{} names {}, which the theorem gives",
                    m.label,
                    named
                        .iter()
                        .map(|n| n.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
                continue;
            }
            if writes(&elsewhere, &m.name) {
                why.push(format!("another theorem of the file writes {}", m.name));
                continue;
            }
            let label = if given.get(&m.label).copied().unwrap_or(0) > 1 {
                let fresh = format!("D{next_label}");
                next_label += 1;
                fresh
            } else {
                m.label.clone()
            };
            moved.push((m, label));
        }
        if !why.is_empty() {
            declined.push(Declined {
                theorem: thm.qualified(),
                why: why.join("; "),
            });
        }
        if moved.is_empty() {
            continue;
        }
        // The theorem's lines without the raised defines, each cited by the
        // label it now has.
        let mut region: Vec<String> = Vec::new();
        for (i, was) in lines.iter().enumerate().take(*end).skip(thm.line - 1) {
            if moved.iter().any(|(m, _)| i == m.at || i == m.at + 1) {
                continue;
            }
            let mut line = was.clone();
            for (m, label) in &moved {
                if *label != m.label && i >= thm.conclusion_line {
                    line = re(&format!(r"\b{}\b", regex::escape(&m.label)))
                        .replace_all(&line, label.as_str())
                        .into_owned();
                }
            }
            if line != *was {
                count += 1;
            }
            region.push(line);
        }
        for (m, label) in &moved {
            let written = lines[m.at].trim_start();
            let rest = written.strip_prefix("let ").unwrap_or(written);
            let defined = rest.replacen(" = ", " := ", 1);
            let defined = label_re
                .replace(&defined, format!("({label})").as_str())
                .into_owned();
            raised.push(format!("define {defined}"));
            raised.push(format!("       {}", lines[m.at + 1].trim_start()));
            raised.push(String::new());
            count += 2;
        }
        lines.splice(thm.line - 1..*end, region);
        theorems.push(thm.qualified());
    }
    // Above the file's first theorem, which no theorem's lines moved.
    lines.splice(first - 1..first - 1, raised);
    Rewritten {
        text: joined(lines, text),
        lines: count,
        theorems,
        declined,
    }
}

/// How many times each line of `thm` is cited: by a step's reason, its
/// requires lines, its chain, or a define's reason.
fn citations_counted(thm: &Theorem) -> BTreeMap<String, usize> {
    let mut out: BTreeMap<String, usize> = BTreeMap::new();
    let mut add = |r: &str| *out.entry(r.to_string()).or_default() += 1;
    for step in &thm.steps {
        step.just.refs.iter().for_each(|r| add(r));
        for r in &step.requires {
            r.lines().iter().for_each(|r| add(r));
        }
        for (text, _) in &step.just.chain {
            if let Some(r) = chain_cited(text) {
                add(&r);
            }
        }
    }
    for reason in thm.defines.iter().filter_map(|d| d.reason.as_ref()) {
        reason.lines().iter().for_each(|r| add(r));
    }
    out
}

/// Whether `r` is one of the lines a `from` list ending `line` names, a
/// list of lines and labels and nothing after it.
fn in_from_list(line: &str, r: &str) -> bool {
    line.rfind("from ").is_some_and(|at| {
        let items: Vec<&str> = line[at + "from ".len()..]
            .split(',')
            .map(str::trim)
            .collect();
        items.iter().all(|i| {
            !i.is_empty()
                && i.chars()
                    .all(|c| c.is_alphanumeric() || c == '.' || c == '′')
        }) && items.contains(&r)
    })
}

/// A file read again, as `parse_proof` reads it, with each theorem's end.
fn reread<'t>(
    path: &str,
    text: &str,
    scope: parley::corpus::ScopeId,
    thms: &'t mut Vec<Theorem>,
) -> Vec<(&'t Theorem, usize)> {
    let (_, read) = parse_proof(path, text, scope).expect("the file reads");
    *thms = read;
    thms.sort_by_key(|t| t.line);
    let count = text.lines().count();
    let mut out = Vec::new();
    for (i, t) in thms.iter().enumerate() {
        let end = thms.get(i + 1).map_or(count, |n| n.line - 1);
        out.push((t, end));
    }
    out
}

/// The step of `thms` whose heading is on `line`, with its theorem's end.
fn step_on<'t>(
    thms: &[(&'t Theorem, usize)],
    line: usize,
) -> Option<(&'t Theorem, usize, &'t parley::corpus::Step)> {
    thms.iter().find_map(|(t, end)| {
        t.steps
            .iter()
            .find(|s| s.line == line)
            .map(|s| (*t, *end, s))
    })
}

/// Each line cited once, by a step's `from` list, first restated by a step
/// of its own that `restate`s it, written just above the citing step, which
/// cites the new step instead (`SYNTAX.md`: `restate`'s claim is its one
/// cited line). A step citing several such lines restates the last.
pub fn cited_lines_restated(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut text = text.to_string();
    let mut count = 0;
    let mut theorems = Vec::new();
    let Some(scope) = ctx
        .corpus
        .theorems
        .iter()
        .find(|t| t.path == path)
        .map(|t| t.scope)
    else {
        return Rewritten {
            text,
            lines: 0,
            theorems,
            declined: Vec::new(),
        };
    };
    // Each citing step's line and the line it restates, from the file as
    // it was. Done from the bottom, so each is where it was read.
    let mut pending: Vec<(usize, String)> = Vec::new();
    let mut thms = Vec::new();
    for (thm, _) in reread(path, &text, scope, &mut thms) {
        let counted = citations_counted(thm);
        let numbers: BTreeSet<String> =
            thm.steps.iter().map(|s| s.number.to_string()).collect();
        for step in &thm.steps {
            if !step.just.chain.is_empty() {
                continue;
            }
            // A line in another block than the citing step's is read there
            // at the letters of the blocks between (`SYNTAX.md`, a "for all"
            // at a block's letter), which a restatement written inside the
            // citing step's block would not be: only a line of its own block
            // is restated.
            let block = |n: &str| n.rsplit_once('.').map(|(b, _)| b.to_string());
            let here = block(&step.number.to_string());
            let restated = step.just.refs.iter().rev().find(|r| {
                numbers.contains(*r)
                    && block(r) == here
                    && counted.get(*r) == Some(&1)
                    && in_from_list(&step.just.text, r)
                    && thm
                        .steps
                        .iter()
                        .find(|s| s.number.to_string() == **r)
                        // An obtain's memberships are said there once, and no
                        // later step writes them (`SYNTAX.md`).
                        .is_some_and(|s| {
                            !s.impossible && !s.just.head.is(Method::Obtain)
                        })
            });
            if let Some(r) = restated {
                pending.push((step.line, r.clone()));
            }
        }
    }
    pending.sort_by_key(|(line, _)| std::cmp::Reverse(*line));
    for (line, restated) in pending {
        let mut thms = Vec::new();
        let read = reread(path, &text, scope, &mut thms);
        let Some((thm, end, step)) = step_on(&read, line) else {
            continue;
        };
        let Some(cited) = thm.steps.iter().find(|s| s.number.to_string() == restated)
        else {
            continue;
        };
        let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
        let number = step.number.to_string();
        let heading = step.line - 1;
        let prefix: String = lines[heading]
            .chars()
            .take_while(|c| c.is_whitespace())
            .collect();
        let indent: String = lines[step.just.line - 1]
            .chars()
            .take_while(|c| c.is_whitespace())
            .collect();
        count += moved_down(thm, &mut lines, end, step);
        let map = BTreeMap::from([(restated.clone(), number.clone())]);
        let mut reason = vec![step.just.line - 1];
        reason.extend(continued(&lines, step.just.line - 1, end));
        for l in reason {
            lines[l] = renumbered_line(&lines, l, &map);
        }
        let claim = cited
            .claim
            .text()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        let new_step = vec![
            format!("{prefix}{number}.  {claim}"),
            format!("{indent}restate {restated}"),
            String::new(),
        ];
        count += new_step.len() + 1;
        lines.splice(heading..heading, new_step);
        if !theorems.contains(&thm.qualified()) {
            theorems.push(thm.qualified());
        }
        text = joined(lines, &text);
    }
    Rewritten {
        text,
        lines: count,
        theorems,
        declined: Vec::new(),
    }
}

/// Each step citing an item, cited once and by a later step of its run,
/// written as a requires line of that step: its claim the line's fact and
/// its reason the line's (`SYNTAX.md`: a requires line is justified as a
/// step is). The reverse of `requires_raised`. A step of one line saying
/// one sentence is moved, under a step whose reason is one line and that
/// opens no block.
pub fn steps_as_requires(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut text = text.to_string();
    let mut count = 0;
    let mut theorems = Vec::new();
    let Some(scope) = ctx
        .corpus
        .theorems
        .iter()
        .find(|t| t.path == path)
        .map(|t| t.scope)
    else {
        return Rewritten {
            text,
            lines: 0,
            theorems,
            declined: Vec::new(),
        };
    };
    let lone = |lines: &[String], l: usize| !lines[l].trim_end().ends_with(',');
    // An item whose hypotheses its requires lines state: not a definition,
    // which unfolds the line a step cites rather than asking it.
    let asks = |just: &parley::corpus::proof::Justification| {
        just.cited_item().is_some_and(|cited| {
            let full = just.item(&cited);
            !ctx.corpus
                .records
                .iter()
                .any(|r| r.qualified() == full && r.kind.unfolds())
        })
    };
    let movable = |thm: &Theorem, x: &parley::corpus::Step, lines: &[String]| {
        let opens = thm.steps.iter().any(|o| {
            o.number.len() > x.number.len()
                && o.number.0[..x.number.len()] == x.number.0[..]
        });
        // A requires line holds for its own step only, and a statement
        // applying a define is carried to from the proof's outermost lines,
        // one of which may say an argument is in the define's domain
        // (`checker::citations::check_conclusion_domains`): such a line, a
        // membership or a part, stays a line.
        let says_domain = ctx
            .tokens(x.claim.text())
            .is_some_and(|t| t.iter().any(|t| t.text == "∈" || t.text == "⊆"));
        let carried_from =
            x.number.len() == 1 && says_domain && applies_a_define(ctx, thm);
        // A part, X ⊆ A, is cited for what it says of its members as well,
        // "for all x ∈ X, x ∈ A" (`SYNTAX.md`, a subset as its members),
        // which no hypothesis asks in that form: it stays a line.
        let a_part = ctx
            .tokens(x.claim.text())
            .is_some_and(|t| t.iter().any(|t| t.text == "⊆"));
        !carried_from
            && !a_part
            && x.just.head.is_item()
            && asks(&x.just)
            && x.just.target.is_none()
            && x.just.contradicting.is_none()
            && x.just.chain.is_empty()
            && x.requires.is_empty()
            && x.openers.is_empty()
            && !opens
            && x.claim.sentences().len() == 1
            && x.just.line == x.line + 1
            && lone(lines, x.just.line - 1)
    };
    // The citer of `x`: the one step citing it, later in its run.
    let citer = |thm: &'_ Theorem, x: &parley::corpus::Step, lines: &[String]| {
        let r = x.number.to_string();
        if citations_counted(thm).get(&r) != Some(&1) {
            return None;
        }
        thm.steps
            .iter()
            .find(|s| s.just.refs.contains(&r))
            .filter(|s| {
                s.number.parent() == x.number.parent()
                    && s.part == x.part
                    && s.line > x.line
                    && in_from_list(&lines[s.just.line - 1], &r)
                    && s.just.contradicting.is_none()
                    && asks(&s.just)
                    && s.just.chain.is_empty()
                    // A requires line goes after a step's rows, and a row
                    // cites a line and never a requires line.
                    && s.just.rows.is_empty()
                    && s.openers.is_empty()
                    && !s.just.head.takes_block()
                    && lone(lines, s.just.line - 1)
            })
            .cloned()
    };
    let mut pending: Vec<usize> = Vec::new();
    let mut thms = Vec::new();
    let lines: Vec<String> = text.lines().map(str::to_string).collect();
    for (thm, _) in reread(path, &text, scope, &mut thms) {
        for x in &thm.steps {
            if movable(thm, x, &lines) && citer(thm, x, &lines).is_some() {
                pending.push(x.line);
            }
        }
    }
    pending.sort_by_key(|line| std::cmp::Reverse(*line));
    for line in pending {
        let mut thms = Vec::new();
        let read = reread(path, &text, scope, &mut thms);
        let Some((thm, end, x)) = step_on(&read, line) else {
            continue;
        };
        let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
        let Some(s) = citer(thm, x, &lines) else {
            continue;
        };
        // The citer no longer cites the step, and then the steps after it
        // move up one.
        let at = s.just.line - 1;
        let indent: String = lines[at]
            .chars()
            .take_while(|c| c.is_whitespace())
            .collect();
        let Some(rest) = without_ref(&lines[at], &x.number.to_string()) else {
            continue;
        };
        lines[at] = format!("{indent}{rest}");
        let n = x.number.0[x.number.len() - 1];
        let map = run_shifted(thm, x, |m| m > n, -1);
        count += renumbered(thm, &mut lines, end, &map);
        let fact = x.claim.text().trim().trim_end_matches('.').to_string();
        lines.insert(
            at + 1,
            format!("{indent}requires {fact}: {}", x.just.text.trim()),
        );
        // The step's heading and reason, and a blank line after them.
        let mut gone = 2;
        if lines.get(x.line + 1).is_some_and(|l| l.trim().is_empty()) {
            gone += 1;
        }
        lines.drain(x.line - 1..x.line - 1 + gone);
        count += 2 + gone;
        if !theorems.contains(&thm.qualified()) {
            theorems.push(thm.qualified());
        }
        text = joined(lines, &text);
    }
    Rewritten {
        text,
        lines: count,
        theorems,
        declined: Vec::new(),
    }
}

/// Whether `thm`'s statement applies a define of its own or of its file,
/// as `G(m − 1, n)` applies G: a name a define gives, written with a
/// bracket after it, as the tokeniser cuts the statement.
fn applies_a_define(ctx: &Context, thm: &Theorem) -> bool {
    let mut names = file_names(ctx, thm);
    for d in &thm.defines {
        if let Built(parts) = define_parts(&d.text) {
            names.extend(parts.names());
        }
    }
    let tokens = ctx.tokens(thm.stated().text()).unwrap_or_default();
    tokens
        .windows(2)
        .any(|w| names.contains(&w[0].text) && w[1].text == "(")
}

/// Each define in a proof over nothing but what the theorem's header gives
/// lowered into the header, above `then` (`SYNTAX.md`: a define may stand
/// where the proof first needs it, or in the header). A define whose name
/// the proof gives twice, as two cases might, stays.
pub fn defines_lowered(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let mut count = 0;
    let mut theorems = Vec::new();
    let mut declined = Vec::new();
    for (thm, end) in theorems_of(ctx, path, lines.len()) {
        let sorts = sorts_in_scope(
            thm,
            Env {
                g: &ctx.g,
                scopes: &ctx.corpus.scopes,
            },
        );
        let proof: Vec<&parley::corpus::proof::DefineLine> = thm
            .defines
            .iter()
            .filter(|d| d.line > thm.conclusion_line)
            .collect();
        if proof.is_empty() {
            continue;
        }
        let own = match header_names(ctx, &sorts, thm) {
            Ok(n) => n,
            Err(why) => {
                declined.push(Declined {
                    theorem: thm.qualified(),
                    why,
                });
                continue;
            }
        };
        let files = file_names(ctx, thm);
        let given: Vec<String> = proof
            .iter()
            .filter_map(|d| match define_parts(&d.text) {
                Built(parts) => Some(parts.names()),
                parley::outcome::Declined(_) => None,
            })
            .flatten()
            .collect();
        let mut written_above: Vec<String> = vec![thm.conclusion.clone()];
        written_above.extend(thm.hypotheses.iter().map(|h| h.text.clone()));
        let mut moved: Vec<Movable> = Vec::new();
        let mut why = Vec::new();
        for d in proof {
            let m = match movable(ctx, &sorts, d, &lines) {
                Ok(m) => m,
                Err(e) => {
                    why.push(e);
                    continue;
                }
            };
            let outside: Vec<&String> = m
                .uses
                .iter()
                .filter(|n| !own.contains(*n) && !files.contains(*n))
                .collect();
            if !outside.is_empty() {
                why.push(format!(
                    "{} names {}, which the header does not give",
                    m.label,
                    outside
                        .iter()
                        .map(|n| n.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
                continue;
            }
            if given.iter().filter(|n| **n == m.name).count() > 1 {
                why.push(format!("the proof gives {} twice", m.name));
                continue;
            }
            // The statement is in the header's scope, and a letter it binds
            // would be the define's name there.
            if writes(&written_above, &m.name) {
                why.push(format!("the header writes {}", m.name));
                continue;
            }
            moved.push(m);
        }
        if !why.is_empty() {
            declined.push(Declined {
                theorem: thm.qualified(),
                why: why.join("; "),
            });
        }
        if moved.is_empty() {
            continue;
        }
        let mut region: Vec<String> = Vec::new();
        let mut i = thm.line - 1;
        while i < end {
            if i == thm.conclusion_line - 1 {
                for m in &moved {
                    region.push(format!("  {}", lines[m.at].trim_start()));
                    region.push(format!("         {}", lines[m.at + 1].trim_start()));
                    count += 2;
                }
            }
            if let Some(m) = moved.iter().find(|m| m.at == i) {
                // The define, its reads line, and a blank line after them.
                i = m.at + 2;
                if lines.get(i).is_some_and(|l| l.trim().is_empty()) {
                    i += 1;
                }
                continue;
            }
            region.push(lines[i].clone());
            i += 1;
        }
        lines.splice(thm.line - 1..end, region);
        theorems.push(thm.qualified());
    }
    Rewritten {
        text: joined(lines, text),
        lines: count,
        theorems,
        declined,
    }
}
