//! What each step, block and requires line may rest on (`ELABORATION.md`,
//! the proof rules; `SYNTAX.md`, what a block rests on).
//!
//! A step rests on the lines its reason cites, the line it contradicts and
//! its own requires lines; a requires line on what its reason cites and the
//! requires lines above it. Each also rests on the defines its reason reads
//! what it cites with: the header defines a cited hypothesis is written in,
//! the defines a cited theorem of the file is stated over, and this proof's
//! define of a sequence by recursion a cited theorem of the file is stated
//! over. A block rests besides on its own steps and their requires lines,
//! its openers, what it assumes, the defines inside it, the lines a `join`
//! or `restate` inside it cites, and the line a step closing it on a
//! contradiction contradicts, with the defines that step cites.

use std::collections::BTreeSet;

use indexmap::IndexMap;

use super::library::Known;
use super::record::{Resting, RestsOn};
use crate::citing::Library;
use crate::corpus::proof::{self, visible, Justification};
use crate::corpus::{define_parts, DefineParts, Item, Method, Step, Theorem};
use crate::outcome::{Built, Checked};
use crate::sorts;

/// What each step, block and requires line of `thm` may rest on.
pub fn rests_on(thm: &Theorem, known: &Known, library: &Library) -> RestsOn {
    let mut out = RestsOn::default();
    for step in &thm.steps {
        let alone = step_rests_on(thm, known, library, step);
        let mut block = alone.clone();
        block.extend(block_rests_on(thm, step));
        out.steps.push(alone);
        out.blocks.push(block);
        // A requires line, and a reason of its own a chain's line or a
        // substitute's row gives, which is read as a requires line of the
        // step.
        let lines: Vec<usize> = step.requires.iter().map(|r| r.line).collect();
        let chained = proof::chain_reasons(&step.just, &thm.path);
        for req in step.requires.iter().chain(&chained) {
            let resting =
                reason_rests_on(thm, known, library, req.line, &req.by, &lines);
            out.requires.insert(req.line, resting);
        }
    }
    // The reason under a let that says a kind of number, read as the last
    // requires line of the step below the let, its own requires lines above
    // it (`Reason::under`).
    for d in &thm.defines {
        let Some(reason) = &d.reason else {
            continue;
        };
        let mut lines: Vec<usize> = reason.requires.iter().map(|r| r.line).collect();
        lines.push(reason.line);
        for req in &reason.requires {
            let resting =
                reason_rests_on(thm, known, library, req.line, &req.by, &lines);
            out.requires.insert(req.line, resting);
        }
        let resting =
            reason_rests_on(thm, known, library, reason.line, &reason.by, &lines);
        out.requires.insert(reason.line, resting);
    }
    out
}

/// What the reason `by` on page line `line`, read as a requires line, may
/// rest on: what it cites, the defines it reads with, the requires lines of
/// its step written above it, of `lines`, and itself. A reason on none of
/// `lines`, a chain's line's, is under them all.
fn reason_rests_on(
    thm: &Theorem,
    known: &Known,
    library: &Library,
    line: usize,
    by: &Checked<Justification>,
    lines: &[usize],
) -> BTreeSet<Resting> {
    let mut out = BTreeSet::new();
    if let Ok(by) = by {
        out.extend(by.refs.iter().cloned().map(Resting::Named));
        out.extend(read_with(thm, known, library, by));
    }
    out.extend(
        lines
            .iter()
            .take_while(|l| **l != line)
            .map(|l| Resting::Requires(*l)),
    );
    out.insert(Resting::Requires(line));
    out
}

/// What `step` alone may rest on: the lines its reason cites, the line it
/// contradicts, its requires lines, and the defines its reason and its
/// chain's reasons read with.
fn step_rests_on(
    thm: &Theorem,
    known: &Known,
    library: &Library,
    step: &Step,
) -> BTreeSet<Resting> {
    let mut out: BTreeSet<Resting> =
        step.just.refs.iter().cloned().map(Resting::Named).collect();
    out.extend(step.just.contradicting.iter().cloned().map(Resting::Named));
    out.extend(step.requires.iter().map(|r| Resting::Requires(r.line)));
    out.extend(read_with(thm, known, library, &step.just));
    for reason in proof::chain_reasons(&step.just, &thm.path) {
        if let Ok(by) = &reason.by {
            out.extend(read_with(thm, known, library, by));
        }
    }
    out
}

/// What the block `step` opens rests on besides what the step alone does: a
/// line inside it is one numbered under the step, or, for the theorem
/// proved `by` a method, every numbered step.
fn block_rests_on(thm: &Theorem, step: &Step) -> BTreeSet<Resting> {
    let number = step.number.to_string();
    let theorem = step.proves_theorem();
    let prefix = format!("{number}.");
    let inside = |name: &str| match theorem {
        true => name
            .split('.')
            .all(|p| !p.is_empty() && p.bytes().all(|b| b.is_ascii_digit())),
        false => name.starts_with(&prefix),
    };
    let steps_inside: Vec<&Step> = thm
        .steps
        .iter()
        .filter(|s| inside(&s.number.to_string()))
        .collect();
    let mut out: BTreeSet<Resting> = steps_inside
        .iter()
        .map(|s| Resting::Named(s.number.to_string()))
        .collect();
    out.extend(
        steps_inside
            .iter()
            .flat_map(|s| s.requires.iter().map(|r| Resting::Requires(r.line))),
    );
    out.extend(
        step.openers
            .iter()
            .filter(|o| !o.label.is_empty())
            .map(|o| Resting::Named(o.label.clone())),
    );
    out.insert(Resting::Assumes(number.clone()));
    // A define inside the block is the block's own, as its openers are: it
    // comes after the block's first line and before its last step.
    if let Some(last) = steps_inside.iter().map(|s| s.line).max() {
        out.extend(
            thm.defines
                .iter()
                .filter(|d| step.line < d.line && d.line < last)
                .map(|d| Resting::Named(d.label.clone())),
        );
    }
    // The block's own steps, one level below it: the top level for the
    // theorem.
    let depth = match theorem {
        true => 0,
        false => number.matches('.').count() + 1,
    };
    for inner in steps_inside {
        if inner.number.to_string().matches('.').count() != depth {
            continue;
        }
        if inner.just.head.is(Method::Join) || inner.just.head.is(Method::Restate) {
            out.extend(inner.just.refs.iter().cloned().map(Resting::Named));
        }
        // A block closed on a contradiction rests on the line its last step
        // contradicts, read with the defines that step cites (`SYNTAX.md`,
        // What a cited line says).
        if inner.just.contradicting.is_some() {
            out.extend(inner.just.contradicting.iter().cloned().map(Resting::Named));
            out.extend(
                inner
                    .just
                    .refs
                    .iter()
                    .filter(|r| thm.defines.iter().any(|d| &d.label == *r))
                    .cloned()
                    .map(Resting::Named),
            );
        }
    }
    out
}

/// The defines a reason reads what it cites with, and so rests on: the
/// header defines a hypothesis it cites is written in, the defines a
/// theorem of the file it cites is stated over (`sorts::stated_over`), and
/// this proof's define of each sequence by recursion such a theorem is
/// stated over.
fn read_with(
    thm: &Theorem,
    known: &Known,
    library: &Library,
    just: &Justification,
) -> BTreeSet<Resting> {
    let mut out = BTreeSet::new();
    for r in &just.refs {
        out.extend(hypothesis_defines(thm, known, r));
    }
    if let Some(cited) = just.cited_item() {
        let full = thm.names.full(&cited);
        out.extend(
            sorts::stated_over(thm, known.env.scopes, &full)
                .into_iter()
                .map(Resting::Named),
        );
        if let Some(Item::Theorem(other)) = library.item(&full) {
            out.extend(recursions_read(thm, other));
        }
    }
    out
}

/// The defines whose names the hypothesis labelled `label` writes, which
/// the statement reads it with (`sorts::statement_definitions`); none where
/// `label` is no hypothesis. A sequence by recursion is read another way
/// (`recursions_read`), and is not among them.
fn hypothesis_defines(thm: &Theorem, known: &Known, label: &str) -> Vec<Resting> {
    let Some(h) = thm
        .hypotheses
        .iter()
        .find(|h| h.label.as_deref() == Some(label))
    else {
        return Vec::new();
    };
    let written = h.body(&thm.path);
    let names: BTreeSet<String> = written
        .sentences()
        .iter()
        .filter_map(|s| known.read_as_written(s))
        .flat_map(|n| n.names())
        .map(|n| n.to_string())
        .collect();
    statement_defines(thm, known)
        .into_iter()
        .filter(|(name, _)| names.contains(name))
        .map(|(_, resting)| resting)
        .collect()
}

/// Each define the statement is read with that gives one name a rule, by
/// the name it gives: those its file writes above it and those it imports,
/// each by the label a citation names it by, and those of its header.
fn statement_defines(thm: &Theorem, known: &Known) -> IndexMap<String, Resting> {
    let one_rule =
        |text: &str| matches!(define_parts(text), Built(DefineParts::One(_)));
    let mut out = IndexMap::new();
    for v in visible(known.env.scopes, thm.scope, thm.line) {
        if !one_rule(&v.define.text) {
            continue;
        }
        let resting = match v.scope == thm.scope {
            true => Resting::Named(v.define.label.clone()),
            false => match known.env.scopes[thm.scope].import_label(&v.name) {
                Some(label) => Resting::Named(label.to_string()),
                None => Resting::Unlabelled(v.name.clone()),
            },
        };
        out.insert(v.name.clone(), resting);
    }
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        if let Built(DefineParts::One(one)) = define_parts(&d.text) {
            out.insert(one.name, Resting::Named(d.label.clone()));
        }
    }
    out
}

/// The labels of this proof's defines by recursion that give a name a
/// sequence `other`'s statement is stated over.
fn recursions_read(thm: &Theorem, other: &Theorem) -> Vec<Resting> {
    let mut out: Vec<Resting> = Vec::new();
    for (_, r) in other.stated_recursions() {
        for name in &r.names {
            let own = thm.defines.iter().find(|d| match define_parts(&d.text) {
                Built(DefineParts::Recursion(mine)) => mine.names.contains(name),
                _ => false,
            });
            if let Some(d) = own {
                let label = Resting::Named(d.label.clone());
                if !out.contains(&label) {
                    out.push(label);
                }
            }
        }
    }
    out
}
