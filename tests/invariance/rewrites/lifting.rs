//! Raising requires and defines, lifting blocks.

use super::*;
use std::cmp::Reverse;
use std::iter;

use parley::corpus::proof::{DefineLine, Step};
use parley::corpus::{define, Hypothesis};
use parley::notations::{
    FUNCTION_TYPE, IS_A_POLYNOMIAL, MEMBERSHIP, NUMBER_SYSTEMS, PLANE, POLYNOMIALS,
};
use parley::outcome;
use parley::sorts::introduction::Form;
use regex::escape;

/// The methods a requires line may name as its one citation, as a step may.
pub(super) const REQUIRES_METHODS: [Method; 4] = [
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
pub(super) fn requires_raised_in(
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
        // The new step takes the step's number; the theorem's own step has
        // none to give.
        let Some(number) = step.number.number() else {
            continue;
        };
        let changed = moved_down(thm, lines, end, number);
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
pub(super) fn moved_down(
    thm: &Theorem,
    lines: &mut [String],
    end: usize,
    number: &StepNo,
) -> usize {
    let map = run_shifted(thm, number, |n| n >= number.last(), 1);
    renumbered(thm, lines, end, &map)
}

/// The numbers of the run of the step numbered `number`, and of the steps
/// inside them, that `moves` picks by their place in the run, each moved by
/// `by`.
pub(super) fn run_shifted(
    thm: &Theorem,
    number: &StepNo,
    moves: impl Fn(u32) -> bool,
    by: i32,
) -> BTreeMap<String, String> {
    let depth = number.depth();
    let mut map: BTreeMap<String, String> = BTreeMap::new();
    for other in thm.steps.iter().filter_map(|s| s.number.number()) {
        let v = other.parts();
        if v.len() >= depth
            && v[..depth - 1] == number.parts()[..depth - 1]
            && moves(v[depth - 1])
        {
            let to = other.with(depth - 1, v[depth - 1].saturating_add_signed(by));
            map.insert(other.to_string(), to.to_string());
        }
    }
    map
}

/// Every step of `thm` numbered as `map` says, with every line citing one;
/// the number of lines changed.
pub(super) fn renumbered(
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
        for at in reasoned_lines(other) {
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
        let mut defines: Vec<&DefineLine> = thm
            .defines
            .iter()
            .filter(|d| d.line > thm.conclusion_line)
            .collect();
        // From the bottom, so each define's lines are where they were read.
        defines.sort_by_key(|d| Reverse(d.line));
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
pub(super) fn define_raised(
    thm: &Theorem,
    d: &DefineLine,
    lines: &mut Vec<String>,
) -> Option<usize> {
    // One name, read as the tools read it; sequences by recursion stay.
    let parts = define::define_parts(&d.text);
    let Built(DefineParts::One(one)) = parts else {
        return None;
    };
    let name = one.name;
    let reads = d.line;
    if !lines.get(reads)?.trim_start().starts_with("reads ") {
        return None;
    }
    let next = thm.steps.iter().find(|s| s.line > d.line)?;
    let parent = next.number.parent();
    let run: Vec<&Step> = thm
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
                re(&format!(r"\b{}\b", escape(&name))).is_match(l)
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
pub(super) enum LineEdit {
    Insert(usize, Vec<String>),
    Remove(usize),
}

/// The first step of `thm` that serves only requires lines, moved into them;
/// the number of lines it changed, or None where no step can move.
pub(super) fn dull_step_moved(
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
        // The theorem's own step has no number for one to follow.
        let Some(number) = step.number.number() else {
            continue;
        };
        let next = number
            .with(number.depth() - 1, number.last() + 1)
            .to_string();
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
            .chain(iter::once(format!("requires {claim}: {}", step.just.text)))
            .collect();
        let carried_facts: BTreeSet<&str> = step
            .requires
            .iter()
            .map(|r| r.fact.text())
            .chain(iter::once(claim.as_str()))
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
        let Some(number) = step.number.number() else {
            continue;
        };
        let last = number.last();
        let map = run_shifted(thm, number, |m| m > last, -1);
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
            for at in reasoned_lines(other) {
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
        let last = iter::once(step.just.line)
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
        edits.sort_by_key(|e| Reverse(place(e)));
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
pub(super) struct Lifted {
    pub(super) region: Vec<String>,
    pub(super) changed: usize,
}

/// One block made a lemma: the lemma's lines, the lines of the theorem the
/// step's block took up, and what the step is written as instead.
pub(super) struct Lemma {
    pub(super) lines: Vec<String>,
    pub(super) from: usize,
    pub(super) to: usize,
    pub(super) citing: Vec<String>,
}

/// One hypothesis of a lemma: its line's text after the keyword's place,
/// `let n ∈ ℕ` or `assume n² is even`, and its label.
pub(super) struct Assumed {
    pub(super) text: String,
    pub(super) label: String,
    /// The names it writes, read.
    pub(super) names: BTreeSet<String>,
}

pub(super) fn lifted(
    ctx: &Context,
    thm: &Theorem,
    lines: &[String],
    end: usize,
) -> Result<Option<Lifted>, String> {
    let tops: Vec<&Step> = thm.steps.iter().filter(|s| s.number.depth() == 1).collect();
    let has_block = |s: &Step| {
        thm.steps
            .iter()
            .any(|o| o.number.depth() > 1 && s.number.contains(&o.number))
    };
    let blocks: Vec<&Step> = tops.iter().copied().filter(|s| has_block(s)).collect();
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
pub(super) fn names_given(thm: &Theorem) -> BTreeSet<String> {
    thm.defines
        .iter()
        .filter_map(|d| match define_parts(&d.text) {
            Built(parts) => Some(parts.names()),
            outcome::Declined(_) => None,
        })
        .flatten()
        .collect()
}

/// Formula text read by the front end, each sentence a tree; a sentence
/// that does not read leaves the block where it is.
pub(super) fn read_all(
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
pub(super) fn formulas_written(
    thm: &Theorem,
    step: &Step,
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
pub(super) fn leaves_set_out(ctx: &Context, written: &Written, name: &str) -> bool {
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
pub(super) fn hypothesis_read(
    ctx: &Context,
    sorts: &Sorts,
    thm: &Theorem,
    h: &Hypothesis,
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
pub(super) fn names_in(trees: &[Node]) -> BTreeSet<String> {
    trees.iter().flat_map(|t| t.names()).collect()
}

/// Whether a citation of a lemma is asked to supply what its `let` says, as
/// `citing::library` reads a hypothesis: a sort, a set, a point, a function's
/// type and a membership in a number system it is not.
pub(super) fn let_asked(
    ctx: &Context,
    sorts: &Sorts,
    path: &str,
    body: &str,
) -> Result<bool, String> {
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
            m.notation() == MEMBERSHIP
                && m.children
                    .get(1)
                    .is_some_and(|set| set.notation() == NUMBER_SYSTEMS)
        }),
        _ => true,
    })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lemma_of(
    ctx: &Context,
    thm: &Theorem,
    lines: &[String],
    end: usize,
    step: &Step,
    tops: &[&Step],
    named: &BTreeSet<String>,
    sorts: &Sorts,
) -> Result<Lemma, String> {
    let inner: Vec<&Step> = thm
        .steps
        .iter()
        .filter(|o| step.number.contains(&o.number))
        .collect();
    // A step that ends its theorem's contradiction says so in its own
    // justification, which a lemma proving its claim could not say.
    if step.just.contradicting.is_some() {
        return Err("it ends the theorem's contradiction".into());
    }
    let start = step.line - 1;
    // The block ends at the next top step, or before at the next part of a
    // theorem proved `by` a method, whose marker and openers stay.
    let theorem_parts = thm
        .steps
        .iter()
        .filter(|s| s.number.is_theorem())
        .flat_map(|s| s.parts.iter().map(|(_, line)| line - 1));
    let next = tops
        .iter()
        .map(|t| t.line - 1)
        .chain(theorem_parts)
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
        let values =
            iter::once(&s.just.values).chain(s.requires.iter().map(|r| r.values()));
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
    // The names each step the block cites writes, all of which the lemma
    // assumes: a step above it that obtains one of them is then brought in
    // by the walk below, though it comes first.
    for t in tops.iter().filter(|t| t.line - 1 < start) {
        if !outside.contains(&t.number.to_string()) {
            continue;
        }
        for sentence in t.claim.sentences() {
            let said = sentence.read(&ctx.g, sorts).map_err(|p| {
                format!("step {} does not read: {}", t.number, p.message)
            })?;
            used.extend(said.names());
        }
    }
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
            let polynomial = said.notation() == IS_A_POLYNOMIAL
                || said
                    .children
                    .get(1)
                    .is_some_and(|set| set.notation() == POLYNOMIALS);
            let point = said.notation() == MEMBERSHIP
                && said
                    .children
                    .get(1)
                    .is_some_and(|set| set.notation() == PLANE);
            let introduced = match said.notation() {
                _ if polynomial => format!("{} be a polynomial", name.text),
                _ if point => format!("{} be a point", name.text),
                MEMBERSHIP | FUNCTION_TYPE => ctx.g.print(&said),
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
                s.notation() == MEMBERSHIP
                    && s.children.first().is_some_and(|t| !t.is_name())
                    && s.children
                        .get(1)
                        .is_some_and(|set| set.notation() == NUMBER_SYSTEMS)
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
    // An `assume` is needed where the block cites it, where it is what
    // gives a name the lemma writes its sort, as `assume H is a subgroup of
    // G` gives H, which no `let` writes, and where it may say the points of
    // an angle the block writes differ: an angle is written only where they
    // are said to, by any line in scope (`SYNTAX.md`, Formulas), as
    // `assume A, C, B form a triangle` says it for ∠ACB. And an `assume`
    // saying a letter the lemma writes exists is kept with the `let` that
    // introduces it: `let A be a set` alone says A exists, which a theorem
    // writing the two lines does not say of its A.
    let mut exists_of: Vec<Option<BTreeSet<String>>> = Vec::new();
    for h in &thm.hypotheses {
        let says = match h.kind {
            Intro::Let => None,
            _ => {
                let read = hypothesis_read(ctx, sorts, thm, h)?;
                match read.as_slice() {
                    [one] if &*one.notation_name() == "exists" => Some(one.names()),
                    _ => None,
                }
            }
        };
        exists_of.push(says);
    }
    let angles: Vec<BTreeSet<String>> = block_trees
        .iter()
        .flat_map(|n| n.walk())
        .filter(|n| &*n.notation_name() == "angle")
        .map(|n| n.names())
        .collect();
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
                        || (!writes.is_empty()
                            && angles.iter().any(|points| writes.is_subset(points)))
                        || exists_of[i]
                            .as_ref()
                            .is_some_and(|said| said.iter().all(|l| used.contains(l)))
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
    for n in inner.iter().filter_map(|s| s.number.number()) {
        map.insert(n.to_string(), vec![n.with(0, 1).to_string()]);
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
        for at in reasoned_lines(s) {
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
