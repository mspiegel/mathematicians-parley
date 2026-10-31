//! `parley by`: write a theorem whose only step repeats its conclusion and
//! opens a block as the theorem proved `by` that block's method
//! (`SYNTAX.md`, a theorem proved by a method).
//!
//! The theorem is one whose proof is step 1 alone, step 1's claim is the
//! `then` line word for word, and step 1's method opens a block: `both
//! directions`, `contradiction`, `proof`, `induction` or `cases`. The step's
//! claim and method lines go; the method is written under `then` as `by
//! <method>`; the block moves four columns left, each label keeping its
//! column; every step number and every citation of one loses its leading
//! `1.` (`renumber::renumber`, at the places the reader read them); and the
//! induction hypothesis `assume step 1 is true for k` says `assume the
//! theorem is true for k`. Nothing else changes.

use std::collections::BTreeMap;
use std::path::Path;

use crate::corpus::proof::{Method, Step, StepNo};
use crate::corpus::skeleton;
use crate::corpus::{corpus, Theorem};
use crate::said::Said;
use crate::source::Disk;

/// The methods a theorem may be proved `by`: those that open a block of
/// steps, a calculation's chain being no block.
const BLOCKS: [Method; 5] = [
    Method::BothDirections,
    Method::Contradiction,
    Method::Proof,
    Method::Induction,
    Method::Cases,
];

/// The theorem's step 1, where the theorem is one this writes in the `by`
/// form; or why it is not.
fn only_step(thm: &Theorem) -> Result<&Step, &'static str> {
    if thm.steps.first().is_some_and(Step::proves_theorem) {
        return Err("it is proved `by` a method already");
    }
    let top: Vec<&Step> = thm.steps.iter().filter(|s| s.number.len() == 1).collect();
    let [step] = top.as_slice() else {
        return Err("its proof is more than one step");
    };
    if !BLOCKS.iter().any(|&m| step.just.head.is(m)) {
        return Err("its step opens no block a theorem may be proved by");
    }
    let words = |text: &str| -> String {
        text.split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
            .trim_end_matches('.')
            .to_string()
    };
    if words(step.claim.text()) != words(&thm.conclusion) {
        return Err("its step says the conclusion in other words");
    }
    Ok(step)
}

/// The column a line's text starts at.
fn indent(line: &str) -> usize {
    line.len() - line.trim_start().len()
}

/// The column the claim of the step written on `line` starts at: past its
/// number and the spaces after it.
fn claim_column(line: &str) -> usize {
    let at = indent(line);
    let rest = &line[at..];
    let number = rest.find(char::is_whitespace).unwrap_or(rest.len());
    at + number + indent(&rest[number..])
}

/// How wide a step's number and the spaces after it are, as the corpus
/// writes them: `1.  `, `10. `, `1.1.  `, `1.10. `, wide enough for the
/// number and one space, and never narrower than two columns a level and
/// two more.
fn number_width(number: &StepNo) -> usize {
    (format!("{number}.").len() + 1).max(2 * number.len() + 2)
}

/// The block of `step`, already renumbered in `lines`, laid out as a
/// theorem proved `by` its method is written: each step at the claim column
/// of the step whose block it is in, the theorem's at column 0, its number
/// as wide as `number_width` says, and every other line moved with the
/// nearest step above it whose claim column it stands at or right of. A
/// line closing on a label keeps the label in its column.
fn relaid(
    thm: &Theorem,
    step: &Step,
    old: &[String],
    lines: &mut [String],
    end: usize,
) {
    let inside: Vec<&Step> = thm.steps.iter().filter(|s| s.line > step.line).collect();
    // Each step's claim column as written, and as it will be.
    let mut was: BTreeMap<StepNo, usize> = BTreeMap::new();
    let mut now: BTreeMap<StepNo, usize> = BTreeMap::new();
    was.insert(step.number.clone(), claim_column(&old[step.line - 1]));
    now.insert(step.number.clone(), 0);
    for s in &inside {
        was.insert(s.number.clone(), claim_column(&old[s.line - 1]));
        let renumbered = StepNo(s.number.0[1..].to_vec());
        let at = now.get(&s.number.parent()).copied().unwrap_or(0);
        now.insert(s.number.clone(), at + number_width(&renumbered));
    }
    let headers: BTreeMap<usize, &Step> =
        inside.iter().map(|s| (s.line - 1, *s)).collect();
    for l in step.just.line..end {
        let line = &old[l];
        if line.trim().is_empty() {
            continue;
        }
        let at = indent(line);
        // The step this line belongs to: its own, for a step's line;
        // otherwise the nearest above whose claim column it reaches.
        let owner = std::iter::once(step)
            .chain(inside.iter().copied())
            .filter(|s| {
                s.line - 1 < l || headers.get(&l).is_some_and(|h| h.line == s.line)
            })
            .filter(|s| {
                if let Some(h) = headers.get(&l) {
                    s.number == h.number.parent()
                } else {
                    was[&s.number] <= at
                }
            })
            .max_by_key(|s| s.line);
        let Some(owner) = owner else {
            continue;
        };
        let shift = now[&owner.number] as isize - was[&owner.number] as isize;
        let moved = (at as isize + shift).max(0) as usize;
        let text = match headers.get(&l) {
            Some(h) => {
                let renumbered = StepNo(h.number.0[1..].to_vec());
                let head = format!("{renumbered}.");
                let claim = lines[l][claim_column(&lines[l])..].to_string();
                format!(
                    "{}{head:<width$}{claim}",
                    " ".repeat(moved),
                    width = number_width(&renumbered)
                )
            }
            None => format!("{}{}", " ".repeat(moved), lines[l].trim_start()),
        };
        lines[l] = kept_label(&text, line);
    }
}

/// `text` with its closing label moved back to the column `was` writes it
/// at, where `was` closes on one after two spaces or more and `text` leaves
/// room for it.
fn kept_label(text: &str, was: &str) -> String {
    let (Some(label), Some(_)) =
        (skeleton::label_at_end(text), skeleton::label_at_end(was))
    else {
        return text.to_string();
    };
    let written = format!("({label})");
    let column = was.len() - written.len();
    if !was[..column].ends_with("  ") {
        return text.to_string();
    }
    let body = text[..text.len() - written.len()].trim_end();
    if body.len() + 2 > column {
        return text.to_string();
    }
    format!("{body}{}{written}", " ".repeat(column - body.len()))
}

/// The theorems of the corpus this writes in the `by` form, by qualified
/// name, each with its method.
pub fn list(root: &Path) -> Said {
    let tree = Disk::new(root.to_path_buf());
    let found = match corpus(&tree) {
        Ok(found) => found,
        Err(p) => return refused(p.to_string()),
    };
    let mut printed = String::new();
    let mut count = 0;
    for thm in &found.theorems {
        if let Ok(step) = only_step(thm) {
            printed += &format!("{}  {}\n", thm.qualified(), step.just.head);
            count += 1;
        }
    }
    printed += &format!("{count} theorem(s)\n");
    Said {
        printed,
        complained: String::new(),
        status: 0,
    }
}

fn refused(why: String) -> Said {
    Said {
        printed: String::new(),
        complained: format!("{why}\n"),
        status: 2,
    }
}

/// Write the theorem `name` names in the `by` form, writing its file unless
/// `dry`.
pub fn run(root: &Path, name: &str, dry: bool) -> Said {
    let tree = Disk::new(root.to_path_buf());
    let found = match corpus(&tree) {
        Ok(found) => found,
        Err(p) => return refused(p.to_string()),
    };
    let Some(thm) = found.theorems.iter().find(|t| t.qualified() == name) else {
        return refused(format!("no theorem {name}"));
    };
    let step = match only_step(thm) {
        Ok(step) => step,
        Err(why) => {
            return refused(format!("{name} is not written in the `by` form: {why}"))
        }
    };
    let file = root.join(&thm.path);
    let text = match std::fs::read_to_string(&file) {
        Ok(text) => text,
        Err(e) => return refused(format!("{}: {e}", thm.path)),
    };
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let end = super::renumber::region_end(&found.theorems, thm, lines.len());
    let old = lines.clone();
    // Every step under step 1 loses the leading `1.`, where the reader read
    // its number or a citation of it.
    let map: BTreeMap<StepNo, StepNo> = thm
        .steps
        .iter()
        .filter(|s| s.number.len() > 1)
        .map(|s| (s.number.clone(), StepNo(s.number.0[1..].to_vec())))
        .collect();
    if let Err(why) = super::renumber::renumber(thm, &mut lines, &map) {
        return refused(why);
    }
    // The induction hypothesis names the theorem.
    for o in step.openers.iter().filter(|o| o.is_hypothesis) {
        let at = o.line - 1;
        let said = skeleton::induction_hypothesis(&lines[at]).and_then(|h| h.step);
        if said == Some("1") {
            lines[at] = lines[at].replacen("step 1 is true", "the theorem is true", 1);
        }
    }
    relaid(thm, step, &old, &mut lines, end);
    // Step 1's claim and method go, and the method is written under `then`.
    let method = old[step.just.line - 1].trim().to_string();
    let first = step.line - 1;
    let last = step.just.line - 1;
    lines.drain(first..=last);
    // The blank line that stood between the claim and the block goes too.
    if lines.get(first).is_some_and(|l| l.trim().is_empty())
        && lines.get(first - 1).is_some_and(|l| l.trim().is_empty())
    {
        lines.remove(first);
    }
    let then = thm.conclusion_line;
    lines.insert(then, format!("  by          {method}"));
    let mut printed = format!(
        "{}: {name} written `by {method}`, {} step(s) renumbered{}\n",
        thm.path,
        map.len(),
        if dry {
            ", nothing written (dry run)"
        } else {
            ""
        }
    );
    if dry {
        let region: Vec<&String> = lines
            .iter()
            .skip(thm.line - 1)
            .take(end - thm.line + 1)
            .collect();
        for l in region {
            printed += &format!("  {l}\n");
        }
    } else {
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
