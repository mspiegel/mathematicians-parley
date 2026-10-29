//! `parley fold DIR`: the proofs under DIR rewritten so that a calculation
//! shows its working (`SYNTAX.md`, "A calculation shows its working").
//!
//! A step whose one use is a line of a calculation's chain moves onto that
//! line: its reason is written there in place of its number, its requires
//! lines go under the calculation, and the steps after it are numbered
//! again. A step whose one use is the equation of a `substitute … into
//! line L` becomes the second row of a bare `substitute`, under line L
//! written out. A step that opens a block, names something, runs over more
//! than one line, or gives a reason a chain line cannot give stays.
//!
//! Every theorem rewritten is checked afterwards, and one the checker finds
//! a problem in is put back as it was and listed.
//!
//! The command is a one-off for the move to calculations that show their
//! working, and goes once the corpus is rewritten.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use regex::Regex;

use crate::corpus::proof::{
    chain_cited, parse_proof, Head, Method, Step, StepNo, Theorem,
};
use crate::corpus::skeleton::{chain_reason, is_ref, Place, Source};
use crate::said::Said;
use crate::source::Disk;

/// What one theorem's rewrite did.
#[derive(Default)]
struct Folds {
    links: usize,
    rows: usize,
}

/// Where a step's one use is.
enum Use {
    /// A chain line of the step at this index, on this line, cites it.
    Link { by: usize, line: usize },
    /// The step at this index substitutes its equation into a line.
    Row { by: usize },
}

pub fn run(root: &Path, dir: &str) -> Said {
    let mut files = Vec::new();
    proof_files(&root.join(dir), &mut files);
    files.sort();
    let mut printed = String::new();
    let mut complained = String::new();
    let mut originals: BTreeMap<String, String> = BTreeMap::new();
    let mut folded: BTreeMap<(String, String), Folds> = BTreeMap::new();
    for file in &files {
        let path = relative(root, file);
        let Ok(text) = std::fs::read_to_string(file) else {
            complained.push_str(&format!("{path}: does not read\n"));
            continue;
        };
        let (new, done) = folded_file(&path, &text);
        if new != text {
            if std::fs::write(file, &new).is_err() {
                complained.push_str(&format!("{path}: could not be written\n"));
                continue;
            }
            originals.insert(path.clone(), text);
            for (thm, f) in done {
                folded.insert((path.clone(), thm), f);
            }
        }
    }
    // Each theorem rewritten that no longer checks is put back, until what
    // is left checks clean.
    let mut put_back: Vec<(String, String, String)> = Vec::new();
    for _ in 0..3 {
        let changed: BTreeSet<(String, String)> = folded.keys().cloned().collect();
        let wanted = |t: &Theorem| changed.contains(&(t.path.clone(), t.name.clone()));
        let problems =
            match crate::checker::problems(&Disk::new(root.to_path_buf()), &wanted) {
                Ok(p) => p,
                Err(out) => {
                    complained.push_str(&out.printed);
                    complained.push_str(&out.complained);
                    return Said {
                        printed,
                        complained,
                        status: 1,
                    };
                }
            };
        let mut failing: BTreeMap<(String, String), String> = BTreeMap::new();
        for p in problems {
            let Some(text) = std::fs::read_to_string(root.join(&p.path)).ok() else {
                continue;
            };
            let Ok((_, thms)) = parse_proof(&p.path, &text, 0) else {
                continue;
            };
            let owner = thms
                .iter()
                .filter(|t| t.line <= p.line.line)
                .max_by_key(|t| t.line);
            if let Some(t) = owner {
                failing
                    .entry((p.path.clone(), t.name.clone()))
                    .or_insert_with(|| format!("{}  {}", p.line.line, p.message));
            }
        }
        if failing.is_empty() {
            break;
        }
        let by_file: BTreeSet<String> =
            failing.keys().map(|(p, _)| p.clone()).collect();
        for path in by_file {
            let names: BTreeSet<String> = failing
                .keys()
                .filter(|(p, _)| *p == path)
                .map(|(_, n)| n.clone())
                .collect();
            let Some(original) = originals.get(&path) else {
                complained
                    .push_str(&format!("{path}: a problem in a file not rewritten\n"));
                continue;
            };
            let now = std::fs::read_to_string(root.join(&path)).unwrap_or_default();
            let restored = restored(&path, &now, original, &names);
            if std::fs::write(root.join(&path), restored).is_err() {
                complained.push_str(&format!("{path}: could not be written\n"));
            }
            for name in names {
                let why = failing
                    .get(&(path.clone(), name.clone()))
                    .cloned()
                    .unwrap_or_default();
                folded.remove(&(path.clone(), name.clone()));
                put_back.push((path.clone(), name, why));
            }
        }
    }
    let links: usize = folded.values().map(|f| f.links).sum();
    let rows: usize = folded.values().map(|f| f.rows).sum();
    printed.push_str(&format!(
        "{links} step(s) moved onto chain lines, {rows} into substitute rows, in {} theorem(s)\n",
        folded.len()
    ));
    if !put_back.is_empty() {
        printed.push_str(&format!(
            "{} theorem(s) put back as they were:\n",
            put_back.len()
        ));
        for (path, name, why) in &put_back {
            printed.push_str(&format!("  {path}  {name}: {why}\n"));
        }
    }
    Said {
        printed,
        complained,
        status: 0,
    }
}

fn proof_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            proof_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "proof") {
            out.push(path);
        }
    }
}

fn relative(root: &Path, file: &Path) -> String {
    file.strip_prefix(root)
        .unwrap_or(file)
        .to_string_lossy()
        .trim_start_matches("./")
        .to_string()
}

/// The lines of `text` from the theorem on line `line` (1-based) to the line
/// before the next theorem, as indices.
fn region(thms: &[Theorem], line: usize, count: usize) -> (usize, usize) {
    let next = thms
        .iter()
        .map(|t| t.line)
        .filter(|&l| l > line)
        .min()
        .map_or(count, |l| l - 1);
    (line - 1, next)
}

/// `now` with each theorem `names` lists written as `original` writes it.
fn restored(path: &str, now: &str, original: &str, names: &BTreeSet<String>) -> String {
    let (Ok((_, new_thms)), Ok((_, old_thms))) =
        (parse_proof(path, now, 0), parse_proof(path, original, 0))
    else {
        return original.to_string();
    };
    let mut lines: Vec<String> = now.lines().map(str::to_string).collect();
    let old_lines: Vec<String> = original.lines().map(str::to_string).collect();
    let mut targets: Vec<&Theorem> = new_thms
        .iter()
        .filter(|t| names.contains(&t.name))
        .collect();
    targets.sort_by_key(|t| std::cmp::Reverse(t.line));
    for t in targets {
        let Some(old) = old_thms.iter().find(|o| o.name == t.name) else {
            continue;
        };
        let (a, b) = region(&new_thms, t.line, lines.len());
        let (c, d) = region(&old_thms, old.line, old_lines.len());
        lines.splice(a..b, old_lines[c..d].iter().cloned());
    }
    joined(lines, now)
}

fn joined(lines: Vec<String>, text: &str) -> String {
    let mut out = lines.join("\n");
    if text.ends_with('\n') {
        out.push('\n');
    }
    out
}

/// The file with every step that can fold folded, one at a time, read
/// again after each; with what each theorem had folded.
fn folded_file(path: &str, text: &str) -> (String, BTreeMap<String, Folds>) {
    let mut text = text.to_string();
    let mut done: BTreeMap<String, Folds> = BTreeMap::new();
    let mut refused: BTreeSet<(String, String)> = BTreeSet::new();
    loop {
        let Ok((_, thms)) = parse_proof(path, &text, 0) else {
            break;
        };
        let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
        let mut any = false;
        'theorems: for thm in &thms {
            let (_, end) = region(&thms, thm.line, lines.len());
            for (i, step) in thm.steps.iter().enumerate() {
                let key = (thm.name.clone(), step.number.to_string());
                if refused.contains(&key) {
                    continue;
                }
                let Some(used) = one_use(thm, i) else {
                    continue;
                };
                let row = matches!(used, Use::Row { .. });
                let Some(reason) = carried_reason(thm, step, &lines, row) else {
                    continue;
                };
                let made = match used {
                    Use::Link { by, line } => {
                        fold_link(thm, &mut lines, end, i, by, line, &reason)
                    }
                    Use::Row { by } => fold_row(thm, &mut lines, end, i, by, &reason),
                };
                if made {
                    let f = done.entry(thm.name.clone()).or_default();
                    if row {
                        f.rows += 1;
                    } else {
                        f.links += 1;
                    }
                    any = true;
                    break 'theorems;
                }
                refused.insert(key);
            }
        }
        if !any {
            break;
        }
        text = joined(lines, &text);
    }
    (text, done)
}

/// How often the theorem cites step `i`, and where, when that is once: by a
/// chain line citing it by number, or as a substitute's equation put into
/// a line.
fn one_use(thm: &Theorem, i: usize) -> Option<Use> {
    let no = thm.steps[i].number.to_string();
    let mut count = 0;
    let mut tally = |refs: &[String], contradicting: Option<&String>| {
        count += refs.iter().filter(|r| **r == no).count();
        count += usize::from(contradicting == Some(&no));
    };
    for s in &thm.steps {
        tally(&s.just.refs, s.just.contradicting.as_ref());
        for r in &s.requires {
            let by = r.by.as_ref().ok()?;
            tally(&by.refs, by.contradicting.as_ref());
        }
        // An induction's hypothesis names its step.
        if s.openers
            .iter()
            .any(|o| o.text.contains(&format!("step {no} ")))
        {
            return None;
        }
    }
    for d in &thm.defines {
        if let Some(reason) = &d.reason {
            let by = reason.by.as_ref().ok()?;
            tally(&by.refs, by.contradicting.as_ref());
        }
    }
    if count != 1 {
        return None;
    }
    for (by, s) in thm.steps.iter().enumerate() {
        if s.just.head == Head::Method(Method::Calculation) {
            for (text, line) in &s.just.chain {
                if chain_cited(text.trim()).as_deref() == Some(no.as_str()) {
                    return Some(Use::Link { by, line: *line });
                }
            }
        }
        if s.just.head == Head::Method(Method::Substitute)
            && s.just.into.is_some()
            && s.just.equation.is_some()
            && matches!(&s.just.source, Some(Source::At(Place::Line(n))) if *n == no)
        {
            return Some(Use::Row { by });
        }
    }
    None
}

/// The reason step `step` gives, as a chain line or a row writes it; None
/// for a step that cannot move.
fn carried_reason(
    thm: &Theorem,
    step: &Step,
    lines: &[String],
    row: bool,
) -> Option<String> {
    let j = &step.just;
    let no = step.number.to_string();
    let opens = thm
        .steps
        .iter()
        .any(|s| s.number.to_string().starts_with(&format!("{no}.")));
    let single = |l: usize| !lines[l - 1].trim_end().ends_with(',');
    if j.line != step.line + 1
        || !single(j.line)
        || step
            .requires
            .iter()
            .any(|r| !single(r.line) || r.by.is_err())
        || opens
        || !step.parts.is_empty()
        || !step.openers.is_empty()
        || step.note.is_some()
        || step.impossible
        || j.contradicting.is_some()
        || !j.rows.is_empty()
        || !j.chain.is_empty()
        || j.unproduced.is_some()
        || !j.obtained.is_empty()
        || step.claim.sentences().len() != 1
    {
        return None;
    }
    let written = lines[j.line - 1].trim().to_string();
    match &j.head {
        Head::Method(Method::Algebra) if j.from.is_empty() => {
            Some("algebra".to_string())
        }
        Head::Method(Method::Arithmetic) => Some("arithmetic".to_string()),
        Head::Method(Method::RealArithmetic) => Some("real arithmetic".to_string()),
        Head::Method(Method::Substitute)
            if j.into.is_none() && j.equation.is_some() =>
        {
            match &j.source {
                Some(Source::At(Place::Line(n))) => {
                    Some(format!("substitute line {n}"))
                }
                Some(Source::At(Place::Label(l))) => Some(format!("substitute {l}")),
                // A chain line names `real arithmetic` only where its terms
                // are closed (`GRAMMAR.md`, calculation chains), so a
                // closed equation put among letters stays a step.
                Some(Source::Arithmetic) => Some("arithmetic".to_string()),
                _ => None,
            }
        }
        Head::Method(Method::Instantiate) => Some(written),
        Head::Item { .. } => Some(written),
        Head::Define if !row && j.from.is_empty() => j.defined.clone(),
        _ => None,
    }
}

/// The numbers of the steps after step `i` in its run, each one less.
fn shifted(thm: &Theorem, i: usize) -> BTreeMap<String, String> {
    let step = &thm.steps[i];
    let depth = step.number.len();
    let mut map = BTreeMap::new();
    for other in &thm.steps {
        let v = &other.number.0;
        if v.len() >= depth
            && v[..depth - 1] == step.number.0[..depth - 1]
            && v[depth - 1] > step.number.0[depth - 1]
        {
            let mut w = v.clone();
            w[depth - 1] -= 1;
            map.insert(other.number.to_string(), StepNo(w).to_string());
        }
    }
    map
}

/// The last line (index) of a step: its justification, chain, rows and
/// requires lines, with what each continues onto.
fn last_line(step: &Step, lines: &[String], end: usize) -> usize {
    let mut last = step.just.line - 1;
    last = last.max(*continued(lines, last, end).last().unwrap_or(&last));
    for (_, l) in step.just.chain.iter().chain(&step.just.rows) {
        last = last.max(l - 1);
    }
    for r in &step.requires {
        let l = r.line - 1;
        last = last.max(*continued(lines, l, end).last().unwrap_or(&l));
    }
    last
}

fn indent_of(line: &str) -> String {
    line.chars().take_while(|c| c.is_whitespace()).collect()
}

/// Step `i`'s requires lines, numbered as `map` says, that step `by` does
/// not already write.
fn carried_requires(
    thm: &Theorem,
    lines: &[String],
    i: usize,
    by: usize,
    map: &BTreeMap<String, String>,
) -> Vec<String> {
    let has: BTreeSet<String> = thm.steps[by]
        .requires
        .iter()
        .map(|r| renumbered_refs(lines[r.line - 1].trim(), map))
        .collect();
    let mut out = Vec::new();
    for r in &thm.steps[i].requires {
        let text = renumbered_refs(lines[r.line - 1].trim(), map);
        if !has.contains(&text) && !out.contains(&text) {
            out.push(text);
        }
    }
    out
}

/// The lines (indices) of step `i` to take away: from its number to its
/// last line, and the blank line after it.
fn own_lines(
    thm: &Theorem,
    lines: &[String],
    end: usize,
    i: usize,
) -> std::ops::Range<usize> {
    let step = &thm.steps[i];
    let last = last_line(step, lines, end);
    let after = if lines.get(last + 1).is_some_and(|l| l.trim().is_empty()) {
        last + 2
    } else {
        last + 1
    };
    step.line - 1..after
}

/// Step `i` moved onto the chain line on `line` of step `by`.
fn fold_link(
    thm: &Theorem,
    lines: &mut Vec<String>,
    end: usize,
    i: usize,
    by: usize,
    line: usize,
    reason: &str,
) -> bool {
    let map = shifted(thm, i);
    let reason = renumbered_refs(reason, &map);
    let carried = carried_requires(thm, lines, i, by, &map);
    let target = &thm.steps[by];
    let last = last_line(target, lines, end);
    let indent = indent_of(&lines[target.just.line - 1]);
    let own = own_lines(thm, lines, end, i);
    renumbered(thm, lines, end, &map, Some(i));
    let at = line - 1;
    let text = lines[at].trim_end().to_string();
    let Some(start) = text.rfind(char::is_whitespace).map(|k| k + 1) else {
        return false;
    };
    lines[at] = format!("{}{reason}", &text[..start]);
    for (k, r) in carried.into_iter().enumerate() {
        lines.insert(last + 1 + k, format!("{indent}{r}"));
    }
    lines.drain(own);
    true
}

/// Step `i` made the second row of step `by`, a substitute putting its
/// equation into a line: the line written out, then the claim, by the
/// step's reason.
fn fold_row(
    thm: &Theorem,
    lines: &mut Vec<String>,
    end: usize,
    i: usize,
    by: usize,
    reason: &str,
) -> bool {
    let target = &thm.steps[by];
    let j = &target.just;
    if target.just.line != target.line + 1
        || lines[j.line - 1].trim_end().ends_with(',')
        || target.claim.sentences().len() != 1
        || target
            .requires
            .iter()
            .any(|r| lines[r.line - 1].trim_end().ends_with(','))
    {
        return false;
    }
    let Some(into) = &j.into else {
        return false;
    };
    let first = match into {
        Place::Line(n) => {
            let Some(s) = thm.steps.iter().find(|s| s.number.to_string() == *n) else {
                return false;
            };
            if s.claim.sentences().len() != 1 || s.just.line != s.line + 1 {
                return false;
            }
            s.claim_text()
        }
        Place::Label(l) => {
            let Some(h) = thm
                .hypotheses
                .iter()
                .find(|h| h.label.as_deref() == Some(l))
            else {
                return false;
            };
            let body = h.body(&thm.path);
            if body.sentences().len() != 1 {
                return false;
            }
            body.text().to_string()
        }
        Place::Slip(_) => return false,
    };
    let map = shifted(thm, i);
    let reason = renumbered_refs(reason, &map);
    let named = map
        .get(into.named())
        .cloned()
        .unwrap_or(into.named().to_string());
    let claim = target.claim_text();
    let first = first.trim().to_string();
    let claim = claim.trim().trim_end_matches('.').to_string();
    let first = first.trim_end_matches('.').to_string();
    let width = first.chars().count().max(claim.chars().count()) + 6;
    let pad = |s: &str| format!("{s}{}", " ".repeat(width - s.chars().count()));
    let indent = indent_of(&lines[j.line - 1]);
    let rows = vec![
        format!("{indent}substitute"),
        format!("{indent}  {}{named}", pad(&first)),
        format!("{indent}  {}{reason}", pad(&claim)),
    ];
    let carried = carried_requires(thm, lines, i, by, &map);
    let last = last_line(target, lines, end);
    let own = own_lines(thm, lines, end, i);
    renumbered(thm, lines, end, &map, Some(i));
    for (k, r) in carried.into_iter().enumerate() {
        lines.insert(last + 1 + k, format!("{indent}{r}"));
    }
    let at = j.line - 1;
    lines.splice(at..at + 1, rows);
    lines.drain(own);
    true
}

fn re(pattern: &str) -> Regex {
    Regex::new(pattern).expect("the pattern compiles")
}

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

/// A justification's citations said as `map` says them: the lines of a
/// `from`, `join` or `restate` list, and a number after `line`,
/// `contradicting`, `into` or `in`.
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

/// Whether line `l` goes on with a `from`, `join` or `restate` list the line
/// above leaves open.
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
        || (listed.split(',').all(|item| {
            let item = item.trim();
            !item.is_empty()
                && item
                    .chars()
                    .all(|c| c.is_alphanumeric() || c == '.' || c == '′')
        }) && goes_on_list(lines, l - 1))
}

/// Line `l`'s citations said as `map` says them.
fn renumbered_line(
    lines: &[String],
    l: usize,
    map: &BTreeMap<String, String>,
) -> String {
    let line = &lines[l];
    if !goes_on_list(lines, l) {
        return renumbered_refs(line, map);
    }
    let lead = line.len() - line.trim_start().len();
    let given = format!("{}from {}", &line[..lead], &line[lead..]);
    let text = renumbered_refs(&given, map);
    let lead = text.len() - text.trim_start().len();
    let rest = text[lead..].strip_prefix("from ").unwrap_or(&text[lead..]);
    format!("{}{rest}", &text[..lead])
}

/// A chain line or a substitute row with its reason said as `map` says: the
/// line or label it cites, or the citations of a reason of its own.
fn renumbered_reasoned(line: &str, map: &BTreeMap<String, String>) -> String {
    let end = line.trim_end().len();
    let Some(reason) = chain_reason(&line[..end]) else {
        return line.to_string();
    };
    let start = end - reason.len();
    let new = if is_ref(reason) {
        map.get(reason)
            .cloned()
            .unwrap_or_else(|| reason.to_string())
    } else {
        renumbered_refs(reason, map)
    };
    format!("{}{new}{}", &line[..start], &line[end..])
}

/// The first row of an inequalities step, its cited line said as `map` says.
fn renumbered_first_row(line: &str, map: &BTreeMap<String, String>) -> String {
    let end = line.trim_end().len();
    let start = line[..end].rfind(char::is_whitespace).map_or(0, |i| i + 1);
    match map.get(&line[start..end]) {
        Some(new) => format!("{}{new}{}", &line[..start], &line[end..]),
        None => line.to_string(),
    }
}

/// Every step of `thm` but `skip` numbered as `map` says, with every line
/// citing one.
fn renumbered(
    thm: &Theorem,
    lines: &mut [String],
    end: usize,
    map: &BTreeMap<String, String>,
    skip: Option<usize>,
) {
    let hypothesis = re(r"\b(assume\s+step\s+)([0-9]+(?:\.[0-9]+)*)(\s+is\s+true\b)");
    for (s, other) in thm.steps.iter().enumerate() {
        if Some(s) == skip {
            continue;
        }
        let at = other.line - 1;
        if let Some(new) = map.get(&other.number.to_string()) {
            let old = format!("{}.", other.number);
            let lead = lines[at].len() - lines[at].trim_start().len();
            if lines[at][lead..].starts_with(&old) {
                // The claim stays in its column: a shorter number takes
                // the spaces after it.
                let rest = &lines[at][lead + old.len()..];
                let gap = rest.len() - rest.trim_start().len();
                let wanted = (gap + old.len()).saturating_sub(new.len() + 1).max(1);
                let claim = rest.trim_start().to_string();
                lines[at] = format!(
                    "{}{new}.{}{claim}",
                    &lines[at][..lead],
                    " ".repeat(wanted)
                );
            }
        }
        let mut cited: Vec<usize> = vec![other.just.line - 1];
        cited.extend(continued(lines, other.just.line - 1, end));
        for r in &other.requires {
            cited.push(r.line - 1);
            cited.extend(continued(lines, r.line - 1, end));
        }
        for l in cited {
            lines[l] = renumbered_line(lines, l, map);
        }
        for (_, l) in &other.just.chain {
            lines[l - 1] = renumbered_reasoned(&lines[l - 1], map);
        }
        if other.just.head == Head::Method(Method::Substitute) {
            for (_, l) in &other.just.rows {
                lines[l - 1] = renumbered_reasoned(&lines[l - 1], map);
            }
        } else if let Some((_, l)) = other.just.rows.first() {
            lines[l - 1] = renumbered_first_row(&lines[l - 1], map);
        }
        for o in &other.openers {
            let l = o.line - 1;
            lines[l] = hypothesis
                .replace(&lines[l], |c: &regex::Captures| {
                    let n = map.get(&c[2]).cloned().unwrap_or_else(|| c[2].to_string());
                    format!("{}{n}{}", &c[1], &c[3])
                })
                .into_owned();
        }
    }
    for reason in thm.defines.iter().filter_map(|d| d.reason.as_ref()) {
        let l = reason.line - 1;
        lines[l] = renumbered_line(lines, l, map);
    }
}
