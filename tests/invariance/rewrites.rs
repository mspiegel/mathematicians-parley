//! Rewrites of a whole proof file that keep what each theorem says.
//!
//! A rewrite finds the formulas of a theorem with the readers the tools use:
//! the proof parser says which line is a hypothesis, a claim, a requires
//! line, a justification or a link of a chain, and the tokeniser says which
//! characters of a formula are a letter. Only those characters change. A
//! rewrite that cannot tell it keeps the meaning, a letter written where no
//! formula is read, a formula that does not read, declines the theorem and
//! says why; it never guesses.

use std::collections::{BTreeMap, BTreeSet};

use indexmap::IndexSet;
use parley::corpus::proof::{Intro, Theorem};
use parley::corpus::Corpus;
use parley::formula::grammar::{parse_here, Grammar};
use parley::formula::node::Node;
use parley::formula::token::{is_letter, is_mark, tokenise, Token, TokenKind};
use parley::matching::{instantiation, split_commas};
use parley::sorts::{sentences, sorts_in_scope, Env};
use regex::Regex;

/// What every rewrite reads: the corpus, its grammar, and what the corpus
/// says about letters.
pub struct Context {
    pub corpus: Corpus,
    pub g: Grammar,
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

fn re(pattern: &str) -> Regex {
    Regex::new(pattern).expect("the pattern compiles")
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
    pub fn new(corpus: Corpus) -> Context {
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
            for step in &thm.steps {
                let mut texts = vec![step.just.text.clone()];
                texts.extend(step.requires.iter().map(|r| r.how.clone()));
                for text in texts {
                    for full in cites(thm, &text) {
                        if theorems.contains(&full) && full != thm.qualified() {
                            cited.insert(full);
                        }
                    }
                }
            }
        }
        let mut constants = BTreeSet::new();
        for record in &corpus.records {
            if let Some(pattern) = record.field("pattern") {
                for token in pattern.split_whitespace() {
                    if is_one_letter(token) {
                        constants.insert(token.to_string());
                    }
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
        for piece in split_commas(tail) {
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

/// Where the values of a citation end, after `from`: at its `, from`, or at
/// an `instantiate`'s `in line L` or `in H3`, as `matching::instantiation`
/// reads them.
fn values_end(text: &str, from: usize) -> Option<usize> {
    re(r",\s*from\b|\s+in\s+(?:line\b|[A-Z][A-Za-z]*[0-9]*′?\b)")
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
    // `define B := {x ∈ A : x ∉ f(x)} (D1)`: the name defined and its rule.
    for d in &thm.defines {
        let l = at(d.line);
        let c = chars(&lines[l]);
        let from = first_text(&c) + "define ".len();
        let mut to = trimmed_end(&c);
        if let Some(cut) = char_rfind(&c, &format!("({})", d.label)) {
            to = cut;
        }
        while to > from && c[to - 1].is_whitespace() {
            to -= 1;
        }
        push(&mut regions, l, Some((from, to)));
        checked.insert(l);
        // A rule laid out as a table goes on over every line indented past
        // its `define`, up to the line that says what it `reads`.
        let indent = first_text(&c);
        for (next, line) in lines.iter().enumerate().take(end).skip(l + 1) {
            let n = chars(line);
            let start = first_text(&n);
            let rest: String = n[start..].iter().collect();
            if rest.is_empty() || start <= indent || rest.starts_with("reads ") {
                break;
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
    let mut out = ctx.constants.clone();
    if ctx.cited.contains(&thm.qualified()) {
        for h in &thm.hypotheses {
            out.extend(ctx.letters_of(&parley::sorts::said_by_line(h.kind, &h.text)));
        }
        out.extend(ctx.letters_of(&thm.conclusion));
    }
    for step in &thm.steps {
        let mut texts = vec![step.just.text.clone()];
        texts.extend(step.requires.iter().map(|r| r.how.clone()));
        for text in texts {
            let named: BTreeSet<String> =
                instantiation(&text).into_iter().map(|(n, _)| n).collect();
            for full in cites(thm, &text) {
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
        let mut attempt = lines.clone();
        match rename(ctx, &mut attempt, &lay, &map) {
            Ok(n) => {
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

/// The first two letters a theorem's `let` lines put in one set, swapped.
fn swap(
    _: &Context,
    thm: &Theorem,
    _: &BTreeSet<String>,
    held: &BTreeSet<String>,
) -> Option<BTreeMap<String, String>> {
    let mut by_set: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for h in &thm.hypotheses {
        if h.kind != Intro::Let {
            continue;
        }
        let body = parley::sorts::body_of(h.text.trim(), "let");
        let Some((letter, set)) = body.split_once(" ∈ ") else {
            continue;
        };
        let letter = letter.trim();
        if is_one_letter(letter) && !held.contains(letter) {
            by_set
                .entry(set.trim().to_string())
                .or_default()
                .push(letter.to_string());
        }
    }
    let mut pairs: Vec<&Vec<String>> =
        by_set.values().filter(|v| v.len() >= 2).collect();
    pairs.sort_by_key(|v| {
        thm.hypotheses
            .iter()
            .position(|h| h.text.contains(&format!("let {} ", v[0])))
            .unwrap_or(usize::MAX)
    });
    let pair = pairs.first()?;
    let (a, b) = (pair[0].clone(), pair[1].clone());
    Some(BTreeMap::from([(a.clone(), b.clone()), (b, a)]))
}

/// The letters the items a theorem cites bind, then the rest of the
/// library's, most used first.
fn library_pool(ctx: &Context, thm: &Theorem) -> Vec<String> {
    let mut pool: Vec<String> = Vec::new();
    for step in &thm.steps {
        let mut texts = vec![step.just.text.clone()];
        texts.extend(step.requires.iter().map(|r| r.how.clone()));
        for text in texts {
            for full in cites(thm, &text) {
                if let Some(r) =
                    ctx.corpus.records.iter().find(|r| r.qualified() == full)
                {
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
    let pool = library_pool(ctx, thm);
    let mut map = BTreeMap::new();
    let mut taken: BTreeSet<String> = BTreeSet::new();
    for letter in introduced(thm) {
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
    let pieces: Vec<&str> = split_commas(tail).into_iter().map(str::trim).collect();
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
                    parse_here(s, &ctx.g, &sorts)
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
                .map(|s| parse_here(s, &ctx.g, &sorts))
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
    matches!(node.notation.as_str(), "conjunction" | "comma-conjunction")
        && node.children.len() == 2
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
