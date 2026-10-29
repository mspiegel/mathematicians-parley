//! `parley renumber`: shift a run of one theorem's steps forward or back,
//! with their sub-steps and every citation of them in that theorem, so a
//! proof has room for a step to be added, or a gap closed.
//!
//! The steps moved are siblings under one parent, `4.2..4.9`, `4.2..` (to
//! the end of the block) or `4.2`, and each number's last part moves by the
//! shift. The result may skip numbers; `parley check` reports a gap until a
//! step fills it. A move landing on a number another step keeps, or below
//! 1, is refused and nothing is written.
//!
//! A citation is found where the proof reader finds one: a number after
//! `from`, `join` or `restate` and each that continues its list, after
//! `line`, `in`, `into`, `contradicting` or `step`, and a chain line's or a
//! row's reason (`skeleton::chain_reason`). A number anywhere else, in a
//! formula among them, is not touched.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use crate::corpus::proof::{rows, RowReason, StepNo};
use crate::corpus::skeleton::{chain_reason, is_number};
use crate::corpus::{corpus, Theorem};
use crate::said::Said;
use crate::source::Disk;

/// The words after which the next word is a cited line.
const BEFORE_ONE: [&str; 5] = ["line", "in", "into", "contradicting", "step"];

/// The words opening a list of cited lines.
const OPENS_LIST: [&str; 3] = ["from", "join", "restate"];

/// The run of sibling steps a renumber moves: under `parent`, from `first`
/// to `last`, or to the end of the block where there is no last.
#[derive(Debug, PartialEq, Eq)]
pub struct Run {
    parent: Vec<u32>,
    first: u32,
    last: Option<u32>,
}

impl Run {
    /// `4.2..4.9`, `4.2..` or `4.2`; None where it is none of these, or its
    /// two ends are not siblings in order.
    pub fn parse(text: &str) -> Option<Run> {
        let (from, to) = match text.split_once("..") {
            Some((from, to)) => (from, Some(to)),
            None => (text, None),
        };
        let first = number(from)?;
        let (parent, at) = first.split_at(first.len() - 1);
        let last = match to {
            None => Some(at[0]),
            Some("") => None,
            Some(to) => {
                let last = number(to)?;
                let (same, end) = last.split_at(last.len() - 1);
                if same != parent || end[0] < at[0] {
                    return None;
                }
                Some(end[0])
            }
        };
        Some(Run {
            parent: parent.to_vec(),
            first: at[0],
            last,
        })
    }

    /// The place in `number` this run moves, where it moves it.
    fn moves(&self, number: &[u32]) -> Option<usize> {
        let depth = self.parent.len();
        let inside = number.len() > depth
            && number[..depth] == self.parent[..]
            && number[depth] >= self.first
            && self.last.is_none_or(|last| number[depth] <= last);
        inside.then_some(depth)
    }
}

/// A step number's parts, where `text` is one.
fn number(text: &str) -> Option<Vec<u32>> {
    if !is_number(text) {
        return None;
    }
    text.split('.').map(|p| p.parse().ok()).collect()
}

/// The shift, `+n` or `-n`.
pub fn shift(text: &str) -> Option<i64> {
    let (sign, digits) = text.split_at(text.chars().next()?.len_utf8());
    let by: i64 = digits.parse().ok()?;
    match sign {
        "+" => Some(by),
        "-" => Some(-by),
        _ => None,
    }
}

/// Renumber the theorem `name` names, as `run` and `by` say, writing its
/// file unless `dry`.
pub fn run(root: &Path, name: &str, run: &Run, by: i64, dry: bool) -> Said {
    let refused = |why: String| Said {
        printed: String::new(),
        complained: format!("{why}\n"),
        status: 2,
    };
    let tree = Disk::new(root.to_path_buf());
    let found = match corpus(&tree) {
        Ok(found) => found,
        Err(p) => return refused(p.to_string()),
    };
    let Some(thm) = found.theorems.iter().find(|t| t.qualified() == name) else {
        return refused(format!("no theorem {name}"));
    };
    let map = match moved(thm, run, by) {
        Ok(map) => map,
        Err(why) => return refused(why),
    };
    if map.is_empty() {
        return refused(format!("no step of {name} is in that run"));
    }
    let file = root.join(&thm.path);
    let text = match std::fs::read_to_string(&file) {
        Ok(text) => text,
        Err(e) => return refused(format!("{}: {e}", thm.path)),
    };
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let end = region_end(&found.theorems, thm, lines.len());
    let old = lines.clone();
    renumber(thm, &mut lines, end, &map);
    let changed: Vec<usize> = (0..lines.len()).filter(|&i| lines[i] != old[i]).collect();
    let mut printed = String::new();
    for &i in &changed {
        printed += &format!("{}:{}\n  - {}\n  + {}\n", thm.path, i + 1, old[i], lines[i]);
    }
    let quoted = quoted_lines(root, &changed.iter().map(|&i| old[i].trim()).collect::<Vec<_>>());
    for (line, place) in &quoted {
        printed += &format!("quoted in {place}: {line}\n");
    }
    printed += &format!(
        "{} step(s) moved, {} line(s) changed{}\n",
        map.len(),
        changed.len(),
        if dry { ", nothing written (dry run)" } else { "" }
    );
    if !dry {
        let mut out = lines.join("\n");
        if text.ends_with('\n') {
            out.push('\n');
        }
        if let Err(e) = std::fs::write(&file, out) {
            return refused(format!("{}: {e}", thm.path));
        }
    }
    Said {
        printed,
        complained: String::new(),
        status: 0,
    }
}

/// Each moved step's number and its new one, sub-steps included; or why the
/// move is refused: a number below 1, or one another step keeps.
fn moved(thm: &Theorem, run: &Run, by: i64) -> Result<BTreeMap<String, String>, String> {
    let mut map = BTreeMap::new();
    let mut landed: BTreeSet<Vec<u32>> = BTreeSet::new();
    for s in &thm.steps {
        let n = &s.number.0;
        let Some(at) = run.moves(n) else {
            continue;
        };
        let new = i64::from(n[at]) + by;
        let Ok(new) = u32::try_from(new).map_err(|_| ()).and_then(|v| if v == 0 { Err(()) } else { Ok(v) }) else {
            return Err(format!("step {} would be numbered below 1", s.number));
        };
        let mut to = n.clone();
        to[at] = new;
        if to.len() == at + 1 {
            landed.insert(to.clone());
        }
        map.insert(s.number.to_string(), StepNo(to).to_string());
    }
    for s in &thm.steps {
        let n = &s.number.0;
        if run.moves(n).is_none() && landed.contains(n) {
            return Err(format!(
                "step {} would land on step {}, which stays where it is",
                map.iter()
                    .find(|(_, to)| **to == s.number.to_string())
                    .map_or_else(String::new, |(from, _)| from.clone()),
                s.number
            ));
        }
    }
    Ok(map)
}

/// The line after the theorem's last: where the next theorem of its file
/// opens, or the file's end.
fn region_end(theorems: &[Theorem], thm: &Theorem, lines: usize) -> usize {
    theorems
        .iter()
        .filter(|t| t.path == thm.path && t.line > thm.line)
        .map(|t| t.line - 1)
        .min()
        .unwrap_or(lines)
}

/// Every line of the theorem with its moved steps numbered as `map` says:
/// each moved step's number where its claim opens, and every citation.
fn renumber(thm: &Theorem, lines: &mut [String], end: usize, map: &BTreeMap<String, String>) {
    let mut edits: BTreeMap<usize, Vec<(usize, usize, String)>> = BTreeMap::new();
    // A chain line's or a substitute row's reason may be a bare number; of
    // an inequalities step's rows, only one the reader reads as citing a
    // line, since `multiplying by 2` ends in a number that is no line.
    let mut reasoned: BTreeSet<usize> = BTreeSet::new();
    for s in &thm.steps {
        reasoned.extend(s.just.chain.iter().map(|(_, l)| l - 1));
        match rows(&s.just, &thm.path) {
            Some(Ok(read)) => reasoned.extend(
                read.iter()
                    .filter(|r| matches!(r.reason, RowReason::Cited(_)))
                    .map(|r| r.line - 1),
            ),
            Some(Err(_)) => {}
            None => reasoned.extend(s.just.rows.iter().map(|(_, l)| l - 1)),
        }
    }
    for &l in &reasoned {
        let line = &lines[l];
        let Some(reason) = chain_reason(line) else {
            continue;
        };
        if let Some(new) = map.get(reason) {
            let at = reason.as_ptr() as usize - line.as_ptr() as usize;
            edits.entry(l).or_default().push((at, at + reason.len(), new.clone()));
        }
    }
    let claims: BTreeSet<usize> = thm.steps.iter().map(|s| s.line - 1).collect();
    let (mut one, mut listing) = (false, false);
    let last = end.min(lines.len());
    for (l, line) in lines.iter().enumerate().take(last).skip(thm.line - 1) {
        for (start, word) in words(line) {
            // A step's own number, where its claim opens.
            if claims.contains(&l) && start == line.len() - line.trim_start().len() {
                if let Some(new) = word.strip_suffix('.').and_then(|n| map.get(n)) {
                    edits.entry(l).or_default().push((start, start + word.len() - 1, new.clone()));
                }
                continue;
            }
            let core = word.trim_start_matches('(').trim_end_matches([',', ')']);
            let lead = word.len() - word.trim_start_matches('(').len();
            if one || listing {
                if let Some(new) = map.get(core) {
                    let at = start + lead;
                    edits.entry(l).or_default().push((at, at + core.len(), new.clone()));
                }
            }
            listing = OPENS_LIST.contains(&core) || (listing && word.ends_with(','));
            one = BEFORE_ONE.contains(&core);
        }
    }
    // A chain line's or row's reason citing by `from` or `line` is found by
    // the words above, and one that is a bare number by its line; the two
    // never find the same word twice, and a word found twice is cut once.
    for (l, mut cut) in edits {
        cut.sort_by_key(|c| std::cmp::Reverse(c.0));
        cut.dedup_by(|a, b| a.0 == b.0);
        let line = &mut lines[l];
        let header = claims.contains(&l);
        for (from, to, new) in cut {
            let old_len = to - from;
            line.replace_range(from..to, &new);
            // A claim keeps its column: the spaces after its number take
            // up the difference.
            if header && from == line.len() - line.trim_start().len() {
                let after = from + new.len() + 1;
                let gap = line[after..].len() - line[after..].trim_start().len();
                let wanted = (gap as i64 + old_len as i64 - new.len() as i64).max(1) as usize;
                line.replace_range(after..after + gap, &" ".repeat(wanted));
            }
        }
    }
}

/// Each word of a line, where it starts.
fn words(line: &str) -> Vec<(usize, &str)> {
    let mut out = Vec::new();
    let mut start = None;
    for (i, c) in line.char_indices() {
        match (c.is_whitespace(), start) {
            (true, Some(s)) => {
                out.push((s, &line[s..i]));
                start = None;
            }
            (false, None) => start = Some(i),
            _ => {}
        }
    }
    if let Some(s) = start {
        out.push((s, &line[s..]));
    }
    out
}

/// Each changed line that a planted test or a design document quotes, with
/// where: those quotes no longer match.
fn quoted_lines(root: &Path, old: &[&str]) -> Vec<(String, String)> {
    let mut places: Vec<(String, String)> = Vec::new();
    let planted = root.join("tests/planted_check.rs");
    if let Ok(text) = std::fs::read_to_string(&planted) {
        places.push(("tests/planted_check.rs".to_string(), text));
    }
    if let Ok(dir) = std::fs::read_dir(root.join("docs")) {
        for entry in dir.flatten() {
            let path = entry.path();
            if path.extension().is_some_and(|e| e == "md") {
                if let Ok(text) = std::fs::read_to_string(&path) {
                    let shown = format!("docs/{}", entry.file_name().to_string_lossy());
                    places.push((shown, text));
                }
            }
        }
    }
    let mut out = Vec::new();
    for line in old.iter().filter(|l| l.len() > 8) {
        for (place, text) in &places {
            if text.contains(line) {
                out.push((line.to_string(), place.clone()));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_run_reads_its_three_forms() {
        assert_eq!(
            Run::parse("4.2..4.9"),
            Some(Run { parent: vec![4], first: 2, last: Some(9) })
        );
        assert_eq!(Run::parse("4.2.."), Some(Run { parent: vec![4], first: 2, last: None }));
        assert_eq!(Run::parse("5"), Some(Run { parent: vec![], first: 5, last: Some(5) }));
        assert_eq!(Run::parse("4.2..5.1"), None);
        assert_eq!(Run::parse("4.9..4.2"), None);
        assert_eq!(shift("+2"), Some(2));
        assert_eq!(shift("-1"), Some(-1));
        assert_eq!(shift("2"), None);
    }
}
