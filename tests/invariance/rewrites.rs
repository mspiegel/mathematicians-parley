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
use parley::check::statements_in_scope;
use parley::corpus::proof::{chain_cited, references, Head, Intro, Method, Theorem};
use parley::corpus::Corpus;
use parley::formula::grammar::{parse_here, Grammar};
use parley::formula::node::Node;
use parley::formula::token::{is_letter, is_mark, tokenise, Token, TokenKind};
use parley::matching::{free_names, instantiation, split_commas};
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
    let mut out = held_own(ctx, thm);
    if ctx.cited.contains(&thm.qualified()) {
        for h in &thm.hypotheses {
            out.extend(ctx.letters_of(&parley::sorts::said_by_line(h.kind, &h.text)));
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
        let mut spans: Vec<Region> = Vec::new();
        for claim in &lay.claims {
            if claim.lines.len() == 1 && !thm.steps[claim.step].impossible {
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
            .map(|h| h.line - 1)
            .chain(thm.steps.iter().flat_map(|s| {
                s.openers
                    .iter()
                    .filter(|o| o.kind != Intro::Let && !o.is_hypothesis && !o.is_claim)
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

/// The lines a step's citation is written on, from 0: its justification and
/// the lines it goes on to, or a requires line and the lines it goes on to.
struct Citation {
    lines: Vec<usize>,
    /// What it says, as the proof parser joined it: the justification, or a
    /// requires line's reason.
    said: String,
}

fn citations_of(thm: &Theorem, lines: &[String], end: usize) -> Vec<Citation> {
    let mut out = Vec::new();
    for step in &thm.steps {
        let j = step.just.line - 1;
        let mut at = vec![j];
        at.extend(continued(lines, j, end));
        out.push(Citation {
            lines: at,
            said: step.just.text.clone(),
        });
        for r in &step.requires {
            let l = r.line - 1;
            let mut at = vec![l];
            at.extend(continued(lines, l, end));
            out.push(Citation {
                lines: at,
                said: r.how.clone(),
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
    let mut changed: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    let mut theorems: BTreeMap<String, Vec<String>> = BTreeMap::new();
    // Each citation of a renamed theorem, said again under its new names.
    let item = re(r"\bthm:([A-Za-z0-9′-]+)");
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
                let named: BTreeSet<String> = instantiation(&citation.said)
                    .into_iter()
                    .map(|(n, _)| n)
                    .collect();
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
                let left: Vec<String> = map
                    .iter()
                    .filter(|(old, _)| !named.contains(*old))
                    .map(|(old, new)| format!("{new} := {old}"))
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
            let head = format!("define {} := {}", c.name, c.part);
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
            let tree = parse_here(&sentence, &ctx.g, &sorts)
                .map_err(|p| format!("step {} does not read: {p}", step.number))?;
            let nodes = tree.walk();
            // A part free in a letter some binder of the sentence holds may
            // stand where that binder gives the letter its meaning, which a
            // define above the step would not, so it is not named.
            let held: BTreeSet<String> = nodes
                .iter()
                .filter_map(|n| binders.get(&n.notation).map(|b| (n, b)))
                .flat_map(|(n, b)| {
                    b.held
                        .iter()
                        .filter_map(|&h| n.children.get(h))
                        .filter(|h| h.is_name())
                        .map(|h| h.text.clone())
                        .collect::<Vec<_>>()
                })
                .collect();
            for node in nodes.iter().skip(1) {
                let term = node.sort.is("number") || node.sort.is("set");
                // Only a part the parser read from the sentence, forwards, is
                // cut from it: a node it built without reading has no text of
                // its own to name.
                let read = node.span().is_some_and(|(from, to)| from < to);
                let binds = node
                    .walk()
                    .iter()
                    .any(|n| binders.contains_key(&n.notation));
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
            step,
            Env {
                g: &ctx.g,
                scopes: &ctx.corpus.scopes,
            },
        );
        let says_part = |r: &str| scope.get(r).is_some_and(|t| t.contains(&part.text));
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
            .any(|r| references(&r.how).0.iter().any(|c| says_part(c)))
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
                let from = re(r"\bfrom\b").is_match(&step.just.text);
                cite.push((last, from));
            }
            Head::Define => return None,
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
                | Method::Instantiate
                | Method::Exhibit
                | Method::Obtain
                | Method::Cases => {
                    if writes_part != cites_part {
                        return None;
                    }
                }
                Method::Algebra
                | Method::Arithmetic
                | Method::Inequalities
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
