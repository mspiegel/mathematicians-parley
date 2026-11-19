//! Renaming statements, naming parts and renumbering.

use std::cmp::Reverse;

use parley::corpus::Step;
use parley::sorts;

use super::*;

/// The lines a step's citation is written on, from 0: its justification and
/// the lines it goes on to, or a requires line and the lines it goes on to.
pub(super) struct Citation {
    pub(super) lines: Vec<usize>,
    /// The values it gives what it cites, as the proof parser cut them from
    /// the justification or a requires line's reason.
    pub(super) values: Values,
    /// The line of the step whose justification it is; None for a requires
    /// line's reason.
    pub(super) step: Option<usize>,
}

pub(super) fn citations_of(
    thm: &Theorem,
    lines: &[String],
    end: usize,
) -> Vec<Citation> {
    let mut out = Vec::new();
    for step in &thm.steps {
        let j = step.just.line - 1;
        let mut at = vec![j];
        at.extend(continued(lines, j, end));
        out.push(Citation {
            lines: at,
            values: step.just.values.clone(),
            step: Some(step.line),
        });
    }
    // A chain line's or a substitute row's reason of its own is read as a
    // requires line is (`chain`, `substitute_rows`), and cites as one does.
    let reasons: Vec<Requires> = thm
        .steps
        .iter()
        .flat_map(|s| {
            let links = match chain(&s.just, &thm.path) {
                Some(Ok(c)) => c.lines.into_iter().filter_map(|l| l.reason).collect(),
                _ => Vec::new(),
            };
            let rows = match substitute_rows(&s.just, &thm.path) {
                Some(Ok(r)) => r.into_iter().filter_map(|r| r.reason).collect(),
                _ => Vec::new(),
            };
            links.into_iter().chain(rows)
        })
        .collect();
    for r in thm
        .steps
        .iter()
        .flat_map(|s| &s.requires)
        .chain(thm.let_requires())
        .chain(&reasons)
    {
        let l = r.line - 1;
        let mut at = vec![l];
        at.extend(continued(lines, l, end));
        out.push(Citation {
            lines: at,
            values: r.values().clone(),
            step: None,
        });
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
                let Some(letter) = let_letter(&sorts::body_of(h.text.trim(), "let"))
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
            if makes_pairs_for_themselves(thm, &map) {
                declined.push(Declined {
                    theorem: thm.qualified(),
                    why:
                        "the renaming gives a cited letter itself, `P := A` as `P := P`"
                            .to_string(),
                });
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
    let item = re(r"\bthm:([A-Za-z0-9′-]+)");
    // A renaming that would give a cited letter itself, `A := P` as
    // `P := P`, is not made: no proof writes that pair where matching finds
    // the letter (`SYNTAX.md`, no pair says what goes without saying).
    for (path, lines) in &texts {
        for (thm, end) in theorems_of(ctx, path, lines.len()) {
            for citation in citations_of(thm, lines, end) {
                let Some(m) = item.captures(&lines[citation.lines[0]]) else {
                    continue;
                };
                let full = thm.names.full(&m[1]);
                let Some(map) = renamings.get(&full) else {
                    continue;
                };
                // The citer's letters are renamed too where it is cited
                // itself: `n := p` is `b := b` with n and p both renamed b.
                let own = renamings.get(&thm.qualified());
                let itself = citation.values.pairs().any(|(name, value)| {
                    let value = value.text().trim();
                    let value =
                        own.and_then(|o| o.get(value)).map_or(value, String::as_str);
                    map.get(name).is_some_and(|new| new == value)
                });
                if itself {
                    renamings.remove(&full);
                    declined.push(Declined {
                        theorem: full,
                        why: "a citation's pair would name a letter for itself"
                            .to_string(),
                    });
                }
            }
        }
    }
    let mut changed: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    let mut theorems: BTreeMap<String, Vec<String>> = BTreeMap::new();
    // Each citation of a renamed theorem, said again under its new names.
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
                let named: BTreeSet<String> =
                    citation.values.names().map(String::from).collect();
                for &l in &citation.lines {
                    let mut c = chars(&lines[l]);
                    let mut spans = assigned_names(&c);
                    spans.sort_by_key(|s| Reverse(s.0));
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
                // A letter the citation leaves to the matcher is given what
                // the matcher makes it there, under its new name; one the
                // matcher does not fix meant the citer's letter of its name.
                // Where that is the citer's letter of the new name, the
                // names agree again and the citation still leaves it.
                let bound = citation
                    .step
                    .and_then(|l| ctx.bound.get(&(path.clone(), l)));
                let left: Vec<String> = map
                    .iter()
                    .filter(|(old, _)| !named.contains(*old))
                    .filter_map(|(old, new)| {
                        let value = bound.and_then(|b| b.get(old)).unwrap_or(old);
                        (value != new).then(|| format!("{new} := {value}"))
                    })
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
pub(super) struct Part {
    pub(super) text: String,
    /// The step whose claim writes it first, by its index in the theorem.
    pub(super) step: usize,
    /// Whether it is a set, which the corpus names with a capital, or a
    /// number, which it names in lower case.
    pub(super) set: bool,
}

/// A part the rewrite names, and what naming it changes.
pub(super) struct Named {
    pub(super) part: String,
    pub(super) name: String,
    pub(super) label: String,
    /// The line the define goes above, from 0: the first line of the step
    /// that writes the part first.
    pub(super) at: usize,
    /// The step number that step is written as, for the `reads` line.
    pub(super) step: String,
    /// The last line of each citation that now cites the define, from 0,
    /// with whether it already says `from`.
    pub(super) cite: Vec<(usize, bool)>,
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
        inserts.sort_by_key(|c| Reverse(c.at));
        for c in inserts {
            let head = format!("let {} = {}", c.name, c.part);
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
pub(super) fn parts_of(ctx: &Context, thm: &Theorem) -> Result<Vec<Part>, String> {
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
        .filter_map(|h| let_letter(&sorts::body_of(h.text.trim(), "let")))
        .collect();
    let blocked: BTreeSet<String> = introduced(thm)
        .into_iter()
        .filter(|l| !header.contains(l))
        .collect();
    let mut out: Vec<Part> = Vec::new();
    for (index, step) in thm.steps.iter().enumerate() {
        if step.number.depth() != 1 || step.impossible {
            continue;
        }
        for sentence in sentences(&step.claim_text()) {
            let tree = read_one(&sentence, &ctx.g, &sorts)
                .map_err(|p| format!("step {} does not read: {p}", step.number))?;
            let nodes = tree.walk();
            // A part free in a letter some binder of the sentence holds may
            // stand where that binder gives the letter its meaning, which a
            // define above the step would not, so it is not named.
            let held: BTreeSet<String> = nodes
                .iter()
                .filter_map(|n| binders.get(&n.notation()).map(|b| (n, b)))
                .flat_map(|(n, b)| {
                    b.held
                        .iter()
                        .filter_map(|&h| n.children.get(h))
                        .filter(|h| h.is_name())
                        .map(|h| h.text.to_string())
                        .collect::<Vec<_>>()
                })
                .collect();
            for node in nodes.iter().skip(1) {
                let term = node.sort.is("number") || node.sort.is("set");
                // Only a part the parser read from the sentence is cut from
                // it: a node it built without reading has no text of its own
                // to name.
                let read = node.span().is_some();
                let binds = node
                    .walk()
                    .iter()
                    .any(|n| binders.contains_key(&n.notation()));
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
pub(super) fn char_places(line: &str, needle: &str) -> Vec<usize> {
    line.match_indices(needle)
        .map(|(byte, _)| line[..byte].chars().count())
        .collect()
}

/// The citations that cite the define where `part` is named from the step
/// that first writes it on, as `Named::cite` holds them; None where some
/// line would no longer follow, or the part is written where the rewrite
/// cannot tell what it is.
pub(super) fn naming_follows(
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
            &CheckedTheorem::of(thm),
            step,
            Env {
                g: &ctx.g,
                scopes: &ctx.corpus.scopes,
            },
        );
        let says_part =
            |r: &str| scope.get(r).is_some_and(|t| t.text().contains(&part.text));
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
            .any(|r| r.lines().iter().any(|c| says_part(c)))
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
                let from = !step.just.from.is_empty();
                cite.push((last, from));
            }
            Head::Define | Head::Lines | Head::Manipulation(_) => return None,
            Head::Method(m) => match m {
                Method::Proof
                | Method::Contradiction
                | Method::Induction
                | Method::BothDirections => {}
                // A link citing a line carries that line: it writes the name
                // exactly where the line does. A link with a reason of its own
                // reads the term above it as well as its own, as a step reads
                // its claim (`SYNTAX.md`, a chain line's reason is checked as
                // if the line were a step): where either writes the part, a
                // reason citing an item cites the define, as such a step
                // does, and a method is left alone, since what it makes of
                // the name is its own.
                Method::Calculation => {
                    let Some(Ok(calculation)) = chain(&step.just, &thm.path) else {
                        return None;
                    };
                    for (i, &l) in links.iter().enumerate() {
                        match chain_cited(&lines[l]) {
                            Some(r) => {
                                if writes(&l) != says_part(&r) {
                                    return None;
                                }
                            }
                            None => {
                                let above = i.checked_sub(1).map(|k| links[k]);
                                if !writes(&l) && !above.is_some_and(|a| writes(&a)) {
                                    continue;
                                }
                                let reason = calculation
                                    .lines
                                    .get(i)
                                    .and_then(|link| link.reason.as_ref())?;
                                let by = reason.by().ok()?;
                                if reason.cited_item().is_none()
                                    || by.contradicting.is_some()
                                    || reason.refs().iter().any(|r| says_part(r))
                                {
                                    return None;
                                }
                                cite.push((l, !by.from.is_empty()));
                            }
                        }
                    }
                }
                Method::Substitute
                | Method::Join
                | Method::Restate
                | Method::Instantiate
                | Method::Exhibit
                | Method::Obtain
                | Method::Cases => {
                    if writes_part != cites_part {
                        return None;
                    }
                }
                // A chain's lines meet as they are written, so naming a part
                // in some of them and not others parts what met.
                Method::Algebra
                | Method::Arithmetic
                | Method::RealArithmetic
                | Method::Inequalities
                | Method::Transitivity
                | Method::Antisymmetry
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
pub(super) fn fresh_name(
    ctx: &Context,
    set: bool,
    taken: &BTreeSet<String>,
) -> Option<String> {
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

/// A citation's text with each step number `map` names said as the new
/// number, where a citation names a line: in a `from`, `join` or `restate`
/// list, and
/// after `line`, `contradicting`, `into` or `in`, as `references` and the
/// proof reader read them. A number anywhere else belongs to a formula.
pub(super) fn renumbered_refs(text: &str, map: &BTreeMap<String, String>) -> String {
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

/// Whether line `l` goes on with a `from`, `join` or `restate` list the line above it
/// leaves open: the line above ends in a comma inside such a list, or is
/// itself nothing but more of one. The proof reader joins the two, so the
/// lines and labels on `l` are cited as surely as those before the break.
pub(super) fn goes_on_list(lines: &[String], l: usize) -> bool {
    let Some(above) = l.checked_sub(1).map(|a| lines[a].trim()) else {
        return false;
    };
    let Some(listed) = above.strip_suffix(',') else {
        return false;
    };
    let opened =
        re(r"\b(?:from|join|restate)\s+([A-Za-z0-9.′]+(?:\s*,\s*[A-Za-z0-9.′]+)*)$");
    opened.is_match(listed)
        || (listed.split(',').all(|item| is_cited_name(item.trim()))
            && goes_on_list(lines, l - 1))
}

/// Whether `item` is written as a cited line or label is: a step number, `H1`,
/// `IH`, `2′`.
pub(super) fn is_cited_name(item: &str) -> bool {
    !item.is_empty()
        && item
            .chars()
            .all(|c| c.is_alphanumeric() || c == '.' || c == '′')
}

/// Line `l` as a citation rewrite reads it: one going on with a list from
/// the line above (`goes_on_list`) is given the `from` it continues, which
/// `listed_back` takes away again.
pub(super) fn as_listed(lines: &[String], l: usize) -> (String, bool) {
    let line = &lines[l];
    if !goes_on_list(lines, l) {
        return (line.clone(), false);
    }
    let lead = line.len() - line.trim_start().len();
    (format!("{}from {}", &line[..lead], &line[lead..]), true)
}

/// A line `as_listed` gave a `from`, rewritten, with that `from` taken away.
pub(super) fn listed_back(text: String, given: bool) -> String {
    if !given {
        return text;
    }
    let lead = text.len() - text.trim_start().len();
    let rest = text[lead..].strip_prefix("from ").unwrap_or(&text[lead..]);
    format!("{}{rest}", &text[..lead])
}

/// Line `l`'s citations said as `map` says them, a line going on with a
/// list from the line above read as more of that list.
pub(super) fn renumbered_line(
    lines: &[String],
    l: usize,
    map: &BTreeMap<String, String>,
) -> String {
    let (text, given) = as_listed(lines, l);
    listed_back(renumbered_refs(&text, map), given)
}

/// A step's induction hypothesis said as `map` says it: the hypothesis
/// names the step it is the hypothesis of, `assume step 2 is true for m`.
/// The lines changed.
pub(super) fn renumbered_hypothesis(
    step: &Step,
    lines: &mut [String],
    map: &BTreeMap<String, String>,
) -> usize {
    let hypothesis = re(r"\b(assume\s+step\s+)([0-9]+(?:\.[0-9]+)*)(\s+is\s+true\b)");
    let mut changed = 0;
    for o in &step.openers {
        let l = o.line - 1;
        let new = hypothesis
            .replace(&lines[l], |c: &regex::Captures| {
                let number =
                    map.get(&c[2]).cloned().unwrap_or_else(|| c[2].to_string());
                format!("{}{number}{}", &c[1], &c[3])
            })
            .into_owned();
        if new != lines[l] {
            lines[l] = new;
            changed += 1;
        }
    }
    changed
}

/// A line ending on a reason, a chain line or a row, with what the reason
/// cites said as `map` says it: the line or label it gives, or the
/// citations of a reason of its own, `algebra, from 3, 5` or `substitute
/// line 4` (`skeleton::chain_reason`).
pub(super) fn renumbered_link(line: &str, map: &BTreeMap<String, String>) -> String {
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

/// The lines (1-based) of a step that end on a reason citing lines: each
/// chain line, each row of a bare `substitute`, and the first row of an
/// inequalities step, whose later rows name manipulations, `adding 1`.
pub(super) fn reasoned_lines(step: &Step) -> Vec<usize> {
    let rows = if step.just.head == Head::Method(Method::Substitute) {
        &step.just.rows[..]
    } else {
        &step.just.rows[..step.just.rows.len().min(1)]
    };
    step.just
        .chain
        .iter()
        .chain(rows)
        .map(|(_, at)| *at)
        .collect()
}

/// Whether `fact` says the term `claim` says is in a number system, of a
/// system holding that one: `|A| ∈ ℝ` of `|A| ∈ ℕ₀`.
pub(super) fn widened(fact: &str, claim: &str) -> bool {
    match (membership_of(fact), membership_of(claim)) {
        (Some(wide), Some(narrow)) => {
            wide.term == narrow.term && narrow.system <= wide.system
        }
        _ => false,
    }
}

/// The number systems, each inside the next.
pub(super) const SYSTEMS: [&str; 6] = ["ℕ", "ℕ₀", "ℤ", "ℚ", "ℝ", "ℂ"];

/// A membership in a number system as a line writes it: the term, and the
/// system by its place among `SYSTEMS`.
pub(super) struct Membership {
    pub(super) term: String,
    pub(super) system: usize,
}

/// `t ∈ S` read off a fact with S a number system; None for any other.
pub(super) fn membership_of(said: &str) -> Option<Membership> {
    let (term, set) = said.trim().trim_end_matches('.').split_once(" ∈ ")?;
    let system = SYSTEMS.iter().position(|s| *s == set.trim())?;
    Some(Membership {
        term: term.trim().to_string(),
        system,
    })
}

/// `from 2, 17` without 17, and `membership, from 14` without 14 as
/// `membership`; None where nothing would be left.
pub(super) fn without_ref(how: &str, gone: &str) -> Option<String> {
    let how = how.trim();
    let at = how.rfind("from ")?;
    let head = how[..at].trim_end().trim_end_matches(',').trim_end();
    let kept: Vec<&str> = how[at + "from ".len()..]
        .split(',')
        .map(str::trim)
        .filter(|r| *r != gone)
        .collect();
    match (head.is_empty(), kept.is_empty()) {
        (true, true) => None,
        (false, true) => Some(head.to_string()),
        (true, false) => Some(format!("from {}", kept.join(", "))),
        (false, false) => Some(format!("{head}, from {}", kept.join(", "))),
    }
}
