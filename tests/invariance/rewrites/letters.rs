//! Renaming letters, reversing values and splitting claims.

use std::cmp::Reverse;
use std::iter;

use parley::corpus::RecordKind;
use parley::notations::{COMMA_CONJUNCTION, CONJUNCTION};

use super::*;

/// How a renaming rewrite picks its letters: from the theorem, the letters
/// it writes, and those it may not touch, the old letter to the new.
pub(super) type Choose = fn(
    &Context,
    &Theorem,
    &BTreeSet<String>,
    &BTreeSet<String>,
) -> Option<BTreeMap<String, String>>;

/// A rewrite that renames letters of one theorem at a time: `choose` picks
/// the renaming from the theorem, its letters, and those it may not touch.
pub(super) fn renaming(
    ctx: &Context,
    path: &str,
    text: &str,
    choose: Choose,
) -> Rewritten {
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
pub(super) fn makes_pairs_for_themselves(
    thm: &Theorem,
    map: &BTreeMap<String, String>,
) -> bool {
    let reasons = thm.steps.iter().flat_map(|s| {
        iter::once(&s.just).chain(s.requires.iter().filter_map(|r| r.by.as_ref().ok()))
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
pub(super) fn subjects_named(
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
        let Some(record) = ctx
            .corpus
            .records
            .iter()
            .find(|r| r.qualified() == full && r.kind == RecordKind::Definition)
        else {
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
pub(super) fn swap(
    ctx: &Context,
    thm: &Theorem,
    _: &BTreeSet<String>,
    held: &BTreeSet<String>,
) -> Option<BTreeMap<String, String>> {
    // A letter the theorem also binds, `for all i, j ∈ T` in a phrase's
    // meaning written out, would capture the other letter put for it.
    let binds = bound(ctx, thm);
    let free: Vec<String> = introduced(thm)
        .into_iter()
        .filter(|l| !held.contains(l) && !binds.contains(l))
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
pub(super) fn library_pool(ctx: &Context, thm: &Theorem) -> Vec<String> {
    let mut pool: Vec<String> = Vec::new();
    for reason in reasons(thm) {
        for full in cites(thm, &reason.text) {
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
pub(super) fn to_library(
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
pub(super) fn bound_to_library(
    ctx: &Context,
    thm: &Theorem,
    used: &BTreeSet<String>,
    held: &BTreeSet<String>,
) -> Option<BTreeMap<String, String>> {
    renamed_to_library(ctx, thm, bound(ctx, thm), used, held)
}

/// The letters the binders in a theorem's formulas bind, in the order the
/// theorem writes them.
pub(super) fn bound(ctx: &Context, thm: &Theorem) -> Vec<String> {
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
    for r in thm.let_requires() {
        trees.extend(said(Intro::Assume, r.fact.clone()));
    }
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
pub(super) fn renamed_to_library(
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
pub(super) fn to_i(
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
pub(super) fn replace_claim(
    lines: &mut Vec<String>,
    claim: &Claim,
    region_end: usize,
    new: &str,
) {
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
pub(super) fn claims(
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
pub(super) fn flatten(node: &Node, out: &mut Vec<String>, g: &Grammar) {
    if is_conjunction(node) {
        for child in &node.children {
            flatten(child, out, g);
        }
    } else {
        out.push(g.print(node));
    }
}

pub(super) fn is_conjunction(node: &Node) -> bool {
    matches!(node.notation(), CONJUNCTION | COMMA_CONJUNCTION)
        && node.children.len() == 2
}

/// `A and B` as `A. B`: `SYNTAX.md` writes a conjunction as sentences, and
/// several sentences mean their conjunction. The other way round is not a
/// change here, since a long "and" is a way the language says not to write.
pub(super) fn conjunction_split(ctx: &Context, read: &[Node]) -> Option<String> {
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
pub(super) fn relation_turned(sentence: &str) -> Option<String> {
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
pub(super) fn sentences_turned(text: &str) -> Option<String> {
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
        spans.sort_by_key(|r| Reverse((r.line, r.from)));
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
pub(super) fn written_out_by_rows(thm: &Theorem) -> BTreeSet<String> {
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
