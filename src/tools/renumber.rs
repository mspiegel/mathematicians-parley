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
//! What is renumbered is what the proof reader read as a step number or a
//! citation, where it read it (`proof::references`): a step's own number,
//! and every line a justification, a requires line, a chain line, a row or
//! an induction hypothesis cites. A number anywhere else, in a formula or a
//! value, is not touched.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use crate::corpus::lines::physical;
use crate::corpus::proof::{references, Reference, StepNo};
use crate::corpus::skeleton::{is_number, Cited};
use crate::corpus::{corpus, Theorem};
use crate::said::Said;
use crate::source::Disk;

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
    if let Err(why) = renumber(thm, &mut lines, &map) {
        return refused(why);
    }
    let changed: Vec<usize> =
        (0..lines.len()).filter(|&i| lines[i] != old[i]).collect();
    let mut printed = String::new();
    for &i in &changed {
        printed +=
            &format!("{}:{}\n  - {}\n  + {}\n", thm.path, i + 1, old[i], lines[i]);
    }
    let quoted = quoted_lines(
        root,
        &thm.path,
        &old[thm.line.saturating_sub(1)..end],
        &changed.iter().map(|&i| old[i].trim()).collect::<Vec<_>>(),
    );
    for (line, place) in &quoted {
        printed += &format!("quoted in {place}: {line}\n");
    }
    for named in notes_naming(thm, &old[thm.line.saturating_sub(1)..end], &map) {
        printed += &format!(
            "note at {}:{} writes {}, a step this moves to {}; the note is not changed\n",
            thm.path, named.line, named.was, named.now
        );
    }
    printed += &format!(
        "{} step(s) moved, {} line(s) changed{}\n",
        map.len(),
        changed.len(),
        if dry {
            ", nothing written (dry run)"
        } else {
            ""
        }
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
fn moved(
    thm: &Theorem,
    run: &Run,
    by: i64,
) -> Result<BTreeMap<StepNo, StepNo>, String> {
    let mut map = BTreeMap::new();
    let mut landed: BTreeSet<Vec<u32>> = BTreeSet::new();
    for s in &thm.steps {
        let n = &s.number.0;
        let Some(at) = run.moves(n) else {
            continue;
        };
        let new = i64::from(n[at]) + by;
        let Ok(new) = u32::try_from(new).map_err(|_| ()).and_then(|v| {
            if v == 0 {
                Err(())
            } else {
                Ok(v)
            }
        }) else {
            return Err(format!("step {} would be numbered below 1", s.number));
        };
        let mut to = n.clone();
        to[at] = new;
        if to.len() == at + 1 {
            landed.insert(to.clone());
        }
        map.insert(s.number.clone(), StepNo(to));
    }
    for s in &thm.steps {
        let n = &s.number.0;
        if run.moves(n).is_none() && landed.contains(n) {
            return Err(format!(
                "step {} would land on step {}, which stays where it is",
                map.iter()
                    .find(|(_, to)| **to == s.number)
                    .map_or_else(String::new, |(from, _)| from.to_string()),
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

/// A number a note writes that is a step the renumber moves.
struct NoteNaming {
    /// The line the note starts on.
    line: usize,
    was: StepNo,
    now: StepNo,
}

/// Each number a note of the theorem writes that is a step `map` moves.
/// A note is prose the reader does not read, so its words are looked at as
/// words: a number in it may name a step, as "line 2 says e ≠ 0" does, or
/// may not, as "from 1 to n" does, and the renumber changes neither. It
/// says where each is, for whoever moved the steps to read.
fn notes_naming(
    thm: &Theorem,
    region: &[String],
    map: &BTreeMap<StepNo, StepNo>,
) -> Vec<NoteNaming> {
    let mut notes: Vec<(&str, usize)> = Vec::new();
    if let Some(note) = thm.fields.get("note") {
        // The theorem's fields keep no line; its note is the field line of
        // the theorem's that opens with the word.
        let line = region
            .iter()
            .position(|l| l.split_whitespace().next() == Some("note"))
            .map_or(thm.line, |at| thm.line + at);
        notes.push((note, line));
    }
    for step in &thm.steps {
        if let Some((note, line)) = &step.note {
            notes.push((note, *line));
        }
        notes.extend(
            step.part_notes
                .values()
                .map(|(note, line)| (note.as_str(), *line)),
        );
    }
    notes.sort_by_key(|(_, line)| *line);
    let mut out = Vec::new();
    for (note, line) in notes {
        let mut seen: BTreeSet<StepNo> = BTreeSet::new();
        for word in note.split_whitespace() {
            let word = word
                .trim_start_matches(['(', '"', '`'])
                .trim_end_matches([',', ';', ':', ')', '"', '`', '.']);
            if !is_number(word) {
                continue;
            }
            let was = StepNo::parse(word);
            if let Some(now) = map.get(&was) {
                if seen.insert(was.clone()) {
                    out.push(NoteNaming {
                        line,
                        was,
                        now: now.clone(),
                    });
                }
            }
        }
    }
    out
}

/// One number to put in place of another: on a line of the file, from byte
/// `from` to byte `to`, the number `new`.
struct Cut {
    from: usize,
    to: usize,
    new: String,
}

/// Every line of the theorem with its moved steps numbered as `map` says,
/// at each place the reader read a step number or a citation of one
/// (`proof::references`). Where the reader places a number that the file
/// does not write there, the reading and the file disagree: that is said,
/// and nothing is changed.
fn renumber(
    thm: &Theorem,
    lines: &mut [String],
    map: &BTreeMap<StepNo, StepNo>,
) -> Result<(), String> {
    let raw: Vec<&str> = lines.iter().map(String::as_str).collect();
    let mut edits: BTreeMap<usize, Vec<Cut>> = BTreeMap::new();
    for Reference { cite, line } in references(thm) {
        let Cited::Line(number) = &cite.cited else {
            continue;
        };
        let Some(new) = map.get(number) else {
            continue;
        };
        // What the reader read there is what the file writes there, or the
        // two disagree and nothing is cut.
        let written = number.to_string();
        let placed = physical(&raw, line, cite.at)
            .filter(|&(l, at)| raw[l].get(at..at + cite.len) == Some(written.as_str()));
        let Some((l, at)) = placed else {
            return Err(format!(
                "{}:{line}: the reader reads step {number} {} bytes into this line, and the file does not write it there",
                thm.path, cite.at
            ));
        };
        edits.entry(l).or_default().push(Cut {
            from: at,
            to: at + cite.len,
            new: new.to_string(),
        });
    }
    let claims: BTreeSet<usize> = thm.steps.iter().map(|s| s.line - 1).collect();
    for (l, mut cuts) in edits {
        // Cut from the right, so each cut leaves the places of those before
        // it where they were; one place read twice is cut once.
        cuts.sort_by_key(|c| std::cmp::Reverse(c.from));
        cuts.dedup_by(|a, b| a.from == b.from);
        let line = &mut lines[l];
        let header = claims.contains(&l);
        for Cut { from, to, new } in cuts {
            let old_len = to - from;
            line.replace_range(from..to, &new);
            // A claim keeps its column: the spaces after its number take
            // up the difference.
            if header && from == line.len() - line.trim_start().len() {
                let after = from + new.len() + 1;
                let gap = line[after..].len() - line[after..].trim_start().len();
                let wanted =
                    (gap as i64 + old_len as i64 - new.len() as i64).max(1) as usize;
                line.replace_range(after..after + gap, &" ".repeat(wanted));
            }
        }
    }
    Ok(())
}

/// Each changed line that a planted test or a design document quotes, with
/// where: those quotes no longer match. A quote is of whole lines, so
/// `restate 1` is not found in `restate 12`, and of this theorem: in the
/// planted tests, the text of an edit naming the theorem's `file`; in a
/// document, a `proof` block every line of which the theorem writes, as
/// `tests/doc_examples.rs` finds an example in the proof it quotes.
fn quoted_lines(
    root: &Path,
    file: &str,
    theorem: &[String],
    old: &[&str],
) -> Vec<(String, String)> {
    let mut places: Vec<(String, Vec<String>)> = Vec::new();
    let planted = "tests/planted_check.rs";
    if let Ok(text) = std::fs::read_to_string(root.join(planted)) {
        places.push((planted.to_string(), planted_quotes(&text, file)));
    }
    let written: BTreeSet<&str> = theorem.iter().map(|l| l.trim()).collect();
    if let Ok(dir) = std::fs::read_dir(root.join("docs")) {
        for entry in dir.flatten() {
            let path = entry.path();
            if path.extension().is_some_and(|e| e == "md") {
                if let Ok(text) = std::fs::read_to_string(&path) {
                    let shown = format!("docs/{}", entry.file_name().to_string_lossy());
                    places.push((shown, document_quotes(&text, &written)));
                }
            }
        }
    }
    let mut out = Vec::new();
    for line in old {
        for (place, quotes) in &places {
            let found = (line.to_string(), place.clone());
            if quotes.iter().any(|q| q == line) && !out.contains(&found) {
                out.push(found);
            }
        }
    }
    out
}

/// The lines the planted tests' edits of `file` write, each trimmed: every
/// line after an `edit(` whose first argument is `file`, up to the next
/// `edit(`, cut at each `\n` its string literals write, with what comes
/// before the last quotation mark of a piece left off.
fn planted_quotes(text: &str, file: &str) -> Vec<String> {
    let names_file = |rest: &str| {
        rest.trim_start()
            .strip_prefix('"')
            .and_then(|r| r.split_once('"'))
            .is_some_and(|(named, _)| named == file)
    };
    let calls: Vec<(usize, bool)> = text
        .match_indices("edit(")
        .map(|(at, call)| (at, names_file(&text[at + call.len()..])))
        .collect();
    let mut out = Vec::new();
    let mut offset = 0;
    for line in text.split_inclusive('\n') {
        let end = offset + line.len();
        offset = end;
        let governed = calls.iter().rev().find(|(at, _)| *at < end);
        if !governed.is_some_and(|(_, ours)| *ours) {
            continue;
        }
        for piece in line.split("\\n") {
            let piece = piece.rsplit_once('"').map_or(piece, |(_, after)| after);
            out.push(piece.trim().to_string());
        }
    }
    out
}

/// The lines of a document's `proof` blocks that quote the theorem whose
/// lines, trimmed, are `written`: a block every line of which it writes,
/// leaving out a line ending `...`, which stands for lines left out.
fn document_quotes(text: &str, written: &BTreeSet<&str>) -> Vec<String> {
    let mut out = Vec::new();
    let mut block: Option<Vec<&str>> = None;
    for line in text.lines() {
        let fence = line.trim();
        match block.as_mut() {
            None if fence == "```proof" => block = Some(Vec::new()),
            None => {}
            Some(lines) if fence.starts_with("```") => {
                let quoted: Vec<&str> = lines
                    .iter()
                    .copied()
                    .filter(|l| !l.is_empty() && !l.ends_with("..."))
                    .collect();
                if !quoted.is_empty() && quoted.iter().all(|l| written.contains(l)) {
                    out.extend(quoted.iter().map(|l| l.to_string()));
                }
                block = None;
            }
            Some(lines) => lines.push(fence),
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
            Some(Run {
                parent: vec![4],
                first: 2,
                last: Some(9)
            })
        );
        assert_eq!(
            Run::parse("4.2.."),
            Some(Run {
                parent: vec![4],
                first: 2,
                last: None
            })
        );
        assert_eq!(
            Run::parse("5"),
            Some(Run {
                parent: vec![],
                first: 5,
                last: Some(5)
            })
        );
        assert_eq!(Run::parse("4.2..5.1"), None);
        assert_eq!(Run::parse("4.9..4.2"), None);
        assert_eq!(shift("+2"), Some(2));
        assert_eq!(shift("-1"), Some(-1));
        assert_eq!(shift("2"), None);
    }

    #[test]
    fn a_planted_quote_is_a_whole_line_of_an_edit_of_the_file() {
        let text = concat!(
            "case(\n",
            "    vec![edit(\n",
            "        \"a.proof\",\n",
            "        Some(\"3.  x = 1\\n    restate 12\\n\".to_string()),\n",
            "    )],\n",
            "),\n",
            "case(vec![edit(\"b.proof\", Some(\"    restate 1\\n\".to_string()))]),\n",
        );
        let quotes = planted_quotes(text, "a.proof");
        assert!(quotes.iter().any(|q| q == "3.  x = 1"));
        assert!(quotes.iter().any(|q| q == "restate 12"));
        assert!(!quotes.iter().any(|q| q == "restate 1"));
        assert!(planted_quotes(text, "b.proof")
            .iter()
            .any(|q| q == "restate 1"));
    }

    #[test]
    fn a_document_quotes_a_theorem_only_in_a_block_it_writes_whole() {
        let written: BTreeSet<&str> = ["1.  n = 2k", "algebra, from H1", "restate 1"]
            .into_iter()
            .collect();
        let text = concat!(
            "```proof\n",
            "1.  n = 2k\n",
            "    algebra, from H1\n",
            "...\n",
            "```\n",
            "\n",
            "```proof\n",
            "2.  n = 3\n",
            "    restate 1\n",
            "```\n",
        );
        let quotes = document_quotes(text, &written);
        assert_eq!(quotes, vec!["1.  n = 2k", "algebra, from H1"]);
    }

    #[test]
    fn a_note_writing_a_moved_step_is_said_and_left() {
        let text = concat!(
            "theorem t\n",
            "  note        Line 2 says it again, and 10 is no step.\n",
            "  let x ∈ ℤ                                                           (H1)\n",
            "  assume x = 1                                                        (H2)\n",
            "  then x = 1\n",
            "\n",
            "1.  x = 1\n",
            "    restate H2\n",
            "\n",
            "2.  x = 1\n",
            "    restate 1\n",
        );
        let (_, theorems) = crate::corpus::parse_proof("t.proof", text, 0).unwrap();
        let thm = &theorems[0];
        let region: Vec<String> = text.lines().map(str::to_string).collect();
        let map = BTreeMap::from([
            (StepNo(vec![1]), StepNo(vec![2])),
            (StepNo(vec![2]), StepNo(vec![3])),
        ]);
        let named = notes_naming(thm, &region, &map);
        assert_eq!(named.len(), 1);
        assert_eq!(
            (named[0].line, &named[0].was, &named[0].now),
            (2, &StepNo(vec![2]), &StepNo(vec![3]))
        );
        let mut lines = region.clone();
        renumber(thm, &mut lines, &map).unwrap();
        assert_eq!(lines[1], region[1]);
        assert_eq!(lines[10], "    restate 2");
    }
}
