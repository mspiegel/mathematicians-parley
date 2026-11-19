//! Reading a proof's layout: regions, claims and letters.

use std::cmp::Reverse;

use parley::corpus::define;
use parley::corpus::proof::Range;
use parley::sorts;

use super::*;

/// Characters `from..to` of a line, which hold a formula.
#[derive(Clone)]
pub(super) struct Region {
    pub(super) line: usize,
    pub(super) from: usize,
    pub(super) to: usize,
}

/// Where a theorem's formulas are, and what else its lines write.
pub(super) struct Layout {
    pub(super) regions: Vec<Region>,
    /// Each line whose every letter means something, as it is outside its
    /// formulas: a letter found here would not be renamed with the rest.
    pub(super) outside: Vec<(usize, String)>,
    /// Each step's claim: the lines it is written on, the first holding the
    /// region that starts it.
    pub(super) claims: Vec<Claim>,
}

pub(super) struct Claim {
    /// The step, by its index in the theorem.
    pub(super) step: usize,
    pub(super) lines: Vec<usize>,
    /// Where on the first line the claim starts.
    pub(super) from: usize,
}

pub(super) fn chars(s: &str) -> Vec<char> {
    s.chars().collect()
}

pub(super) fn char_find(line: &[char], from: usize, needle: &str) -> Option<usize> {
    let n = chars(needle);
    (from..=line.len().saturating_sub(n.len())).find(|&i| line[i..].starts_with(&n))
}

pub(super) fn char_rfind(line: &[char], needle: &str) -> Option<usize> {
    let n = chars(needle);
    (0..=line.len().saturating_sub(n.len()))
        .rev()
        .find(|&i| line[i..].starts_with(&n))
}

/// The end of a line's text, before trailing space.
pub(super) fn trimmed_end(line: &[char]) -> usize {
    let mut end = line.len();
    while end > 0 && line[end - 1].is_whitespace() {
        end -= 1;
    }
    end
}

pub(super) fn first_text(line: &[char]) -> usize {
    line.iter()
        .position(|c| !c.is_whitespace())
        .unwrap_or(line.len())
}

/// A hypothesis or opener line's formula: after its keyword, before its
/// label, and before ` be ` where a `let` gives a property in words.
pub(super) fn introduction(
    line: &[char],
    label: Option<&str>,
) -> Option<(usize, usize)> {
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
pub(super) fn justification(line: &[char], start: usize) -> Vec<(usize, usize)> {
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
pub(super) fn values_end(text: &str, from: usize) -> Option<usize> {
    re(r",\s*(?:from|contradicting)\b|\s+in\s+(?:line\b|[A-Z][A-Za-z]*[0-9]*′?\b)")
        .find_at(text, from)
        .map(|m| m.start())
}

/// Whether an `instantiate` takes a line or hypothesis of the theorem
/// itself, `in line 2` or `in H2`, whose bound letters are the theorem's.
pub(super) fn instantiates_own(justification: &str) -> bool {
    justification.trim_start().starts_with("instantiate")
        && re(r"\s+in\s+(?:line\b|[A-Z][A-Za-z]*[0-9]*′?\b)").is_match(justification)
}

/// The `name` of each `name := value` that is the cited item's letter and
/// not the proof's.
pub(super) fn assigned_names(line: &[char]) -> Vec<(usize, usize)> {
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
pub(super) fn continued(lines: &[String], l: usize, end: usize) -> Vec<usize> {
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

pub(super) fn layout(thm: &Theorem, lines: &[String], end: usize) -> Layout {
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
        if Range::read(rest.trim(), 0).is_some() {
            let to = char_find(&c, start, " range").unwrap_or(start);
            push(&mut regions, i, Some((start, to)));
            checked.insert(i);
        }
    }
    // `let B = {x ∈ A : x ∉ f(x)} (D1)`: the name defined and its rule.
    for d in &thm.defines {
        let l = at(d.line);
        let c = chars(&lines[l]);
        let word = define::naming(lines[l].trim()).map_or("define", |w| w.word());
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
            // A requires line under a let's reason is laid out with every
            // requires line, below.
            let under = d
                .reason
                .as_ref()
                .is_some_and(|r| r.requires.iter().any(|q| at(q.line) == next));
            if under {
                continue;
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
        // A chain line, and a row of a bare `substitute`, writes a formula
        // and then its reason, which is read as a justification is: its
        // values hold the proof's letters, `def:abs x := a + b, from C2`.
        let substituted = if step.just.head == Head::Method(Method::Substitute) {
            &step.just.rows[..]
        } else {
            &[][..]
        };
        for (_, no) in step.just.chain.iter().chain(substituted) {
            let l = at(*no);
            let c = chars(&lines[l]);
            let from = first_text(&c);
            let end = trimmed_end(&c);
            let text: String = c[..end].iter().collect();
            let reason_at =
                chain_reason(&text).map_or(end, |r| end - r.chars().count());
            let mut to = reason_at;
            while to > from && c[to - 1] == ' ' {
                to -= 1;
            }
            push(&mut regions, l, Some((from, to)));
            for span in justification(&c, reason_at) {
                push(&mut regions, l, Some(span));
            }
            checked.insert(l);
        }
        // A row of an inequalities step writes a formula and, after `adding`
        // or `multiplying by`, a term: those hold what the proof writes of
        // its letters. The reason's words and label are none of them, and a
        // word like `restate` would be read a letter at a time.
        let inequality_rows = if substituted.is_empty() {
            &step.just.rows[..]
        } else {
            &[][..]
        };
        for (_, no) in inequality_rows {
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
    }
    // A step's requires lines, and those under a let's reason.
    for r in thm
        .steps
        .iter()
        .flat_map(|s| &s.requires)
        .chain(thm.let_requires())
    {
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
pub(super) fn loose_letters(text: &str) -> BTreeSet<String> {
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
pub(super) fn letters_used(
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
pub(super) fn renamed_name(
    map: &BTreeMap<String, String>,
    name: &str,
) -> Option<String> {
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
pub(super) fn rename(
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
        regions.sort_by_key(|r| Reverse(r.from));
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
pub(super) fn introduced(thm: &Theorem) -> Vec<String> {
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
            add(let_letter(&sorts::body_of(h.text.trim(), "let")));
        }
    }
    for step in &thm.steps {
        for o in &step.openers {
            if o.kind == Intro::Let && !o.is_hypothesis {
                add(let_letter(&sorts::body_of(o.text.trim(), "let")));
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
pub(super) fn held(ctx: &Context, thm: &Theorem) -> BTreeSet<String> {
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
pub(super) fn held_own(ctx: &Context, thm: &Theorem) -> BTreeSet<String> {
    let mut out = ctx.constants.clone();
    for reason in reasons(thm) {
        let named: BTreeSet<String> = reason.values.names().map(String::from).collect();
        for full in cites(thm, &reason.text) {
            if let Some(other) =
                ctx.corpus.theorems.iter().find(|t| t.qualified() == full)
            {
                for h in &other.hypotheses {
                    if h.kind != Intro::Let {
                        continue;
                    }
                    if let Some(l) = let_letter(&sorts::body_of(h.text.trim(), "let")) {
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
pub(super) fn theorems_of<'c>(
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

pub(super) fn joined(lines: Vec<String>, text: &str) -> String {
    let mut out = lines.join("\n");
    if text.ends_with('\n') {
        out.push('\n');
    }
    out
}
