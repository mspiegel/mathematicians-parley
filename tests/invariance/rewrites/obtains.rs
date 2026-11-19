//! Relabelling, obtains, header defines and lowering defines.

use std::cmp::Reverse;

use parley::corpus::proof::{DefineLine, Justification};
use parley::corpus::{define, ScopeId, Step};
use parley::notations::{FUNCTION_TYPE, IN};
use parley::outcome;
use regex::escape;

use super::*;

/// A step's heading with its number said as `map` says it, the claim kept
/// in its column.
pub(super) fn renumbered_heading(
    line: &str,
    map: &BTreeMap<String, Vec<String>>,
) -> String {
    let lead = line.len() - line.trim_start().len();
    let rest = &line[lead..];
    let Some(dot) = rest.find(char::is_whitespace) else {
        return line.to_string();
    };
    let number = rest[..dot].trim_end_matches('.');
    match map.get(number).and_then(|v| v.first()) {
        Some(new) => {
            let said = format!("{new}.");
            let width = dot.max(said.len());
            format!("{}{:<width$}{}", &line[..lead], said, &rest[dot..])
        }
        None => line.to_string(),
    }
}

/// The one label `map` gives a reference standing where one line goes.
pub(super) fn one_label(
    map: &BTreeMap<String, Vec<String>>,
    r: &str,
) -> Result<Option<String>, String> {
    match map.get(r).map(Vec::as_slice) {
        None => Ok(None),
        Some([one]) => Ok(Some(one.clone())),
        Some(_) => Err(format!(
            "{r} is cited where one line stands, and says several"
        )),
    }
}

/// A justification, requires or opening line with each line it cites said
/// as `map` says it: in a `from` or `join` list, a reference may become
/// several; after `line`, `contradicting`, and in `step N is true`, it must
/// stay one. A step number given a label loses its `line`.
pub(super) fn relabelled_refs(
    text: &str,
    map: &BTreeMap<String, Vec<String>>,
) -> Result<String, String> {
    let lists =
        re(r"\b(from|join|restate)(\s+)([A-Za-z0-9.′]+(?:\s*,\s*[A-Za-z0-9.′]+)*)");
    let text = lists
        .replace_all(text, |c: &regex::Captures| {
            let items: Vec<String> = c[3]
                .split(',')
                .map(|item| {
                    let lead = &item[..item.len() - item.trim_start().len()];
                    match map.get(item.trim()) {
                        Some(new) => format!("{lead}{}", new.join(", ")),
                        None => item.to_string(),
                    }
                })
                .collect();
            format!("{}{}{}", &c[1], &c[2], items.join(","))
        })
        .into_owned();
    let mut fault = None;
    let numbered = |s: &str| s.chars().all(|c| c.is_ascii_digit() || c == '.');
    let line = re(r"\bline(\s+)([0-9]+(?:\.[0-9]+)*)\b");
    let text = line
        .replace_all(&text, |c: &regex::Captures| match one_label(map, &c[2]) {
            Ok(Some(new)) if numbered(&new) => format!("line{}{new}", &c[1]),
            Ok(Some(new)) => new,
            Ok(None) => c[0].to_string(),
            Err(e) => {
                fault = Some(e);
                c[0].to_string()
            }
        })
        .into_owned();
    let single = re(r"\b(contradicting|step)(\s+)([A-Za-z0-9.′]+?)(\.?)(\s|$)");
    let text = single
        .replace_all(&text, |c: &regex::Captures| {
            match one_label(map, c[3].trim_end_matches('.')) {
                Ok(Some(new)) => format!("{}{}{new}{}{}", &c[1], &c[2], &c[4], &c[5]),
                Ok(None) => c[0].to_string(),
                Err(e) => {
                    fault = Some(e);
                    c[0].to_string()
                }
            }
        })
        .into_owned();
    match fault {
        Some(e) => Err(e),
        None => Ok(text),
    }
}

/// A chain line with the line it cites at its right end said as `map` says
/// it, which must be one.
pub(super) fn relabelled_link(
    line: &str,
    map: &BTreeMap<String, Vec<String>>,
) -> Result<String, String> {
    let end = line.trim_end().len();
    let Some(reason) = chain_reason(&line[..end]) else {
        return Ok(line.to_string());
    };
    let start = end - reason.len();
    let new = if is_ref(reason) {
        one_label(map, reason)?.unwrap_or_else(|| reason.to_string())
    } else {
        relabelled_refs(reason, map)?
    };
    Ok(format!("{}{new}{}", &line[..start], &line[end..]))
}

/// Each step obtaining from an item written as two: a step claiming the
/// item's "there is", cited as a step citing it is, and an obtain from that
/// line (`SYNTAX.md`, `obtain`). The "there is" is what the item says, each
/// letter as the checker reads it at the step (`checker::obtained_there`).
/// From a definition that unfolds it is the one the obtain's claim states
/// (`ELABORATION.md`): each name runs over the set its membership sentence
/// gives, in the order the obtain names them, and the other sentences are
/// what is said of them, in the order written. The
/// corpus obtains from items far more often than it claims their "there
/// is", so this puts each such fact on the route a proof meets least.
pub fn obtains_claimed(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut text = text.to_string();
    let mut count = 0;
    let mut theorems = Vec::new();
    let mut declined = Vec::new();
    let Some(scope) = ctx
        .corpus
        .theorems
        .iter()
        .find(|t| t.path == path)
        .map(|t| t.scope)
    else {
        return Rewritten {
            text,
            lines: 0,
            theorems,
            declined,
        };
    };
    // The file read again after each obtain is rewritten. The last is
    // rewritten first, so every one above it is on the line the checker
    // read it on, and is as many obtains from the top as it was.
    let mut at = None;
    loop {
        let (_, mut thms) = parse_proof(path, &text, scope).expect("the file reads");
        thms.sort_by_key(|t| t.line);
        let lines: Vec<String> = text.lines().map(str::to_string).collect();
        let mut obtains = Vec::new();
        for (i, thm) in thms.iter().enumerate() {
            let end = thms.get(i + 1).map_or(lines.len(), |n| n.line - 1);
            for step in &thm.steps {
                if step.just.head.is(Method::Obtain) && step.just.cited_item().is_some()
                {
                    obtains.push((thm, end, step));
                }
            }
        }
        let next = match at {
            None => obtains.len(),
            Some(i) => i,
        };
        if next == 0 {
            break;
        }
        at = Some(next - 1);
        let (thm, end, step) = obtains[next - 1];
        let mut lines = lines;
        match obtain_claimed(ctx, path, thm, &mut lines, end, step) {
            Ok(changed) => {
                count += changed;
                if !theorems.contains(&thm.qualified()) {
                    theorems.push(thm.qualified());
                }
                text = joined(lines, &text);
            }
            Err(why) => declined.push(Declined {
                theorem: thm.qualified(),
                why: format!("step {}: {why}", step.number),
            }),
        }
    }
    Rewritten {
        text,
        lines: count,
        theorems,
        declined,
    }
}

/// The names an obtain introduces, as its justification lists them before
/// the item: `obtain p, q: thm:x` names p and q.
pub(super) fn obtained_names(how: &str) -> Option<Vec<String>> {
    let names = re(r"^obtain\s+([^:]+):").captures(how.trim())?;
    Some(names[1].split(',').map(|n| n.trim().to_string()).collect())
}

/// The "there is" an obtain's claim states, as a tree: each name over the
/// set its membership sentence gives, or the functions its type gives, and
/// what the other sentences say of them.
pub(super) fn existence_of(
    ctx: &Context,
    sorts: &Sorts,
    claim: &Written,
    names: &[String],
) -> Result<Node, String> {
    let read = read_all(ctx, sorts, claim)?;
    let made = |pattern: &str, children: Vec<Node>| {
        made_as(&ctx.g, pattern, children)
            .ok_or_else(|| format!("no notation is written {pattern}"))
    };
    let mut over: BTreeMap<String, (Node, Node)> = BTreeMap::new();
    let mut said = Vec::new();
    for node in read {
        let named = |n: &Node| {
            n.is_name()
                && names.iter().any(|m| *m == n.text)
                && !over.contains_key(n.text.as_str())
        };
        match (node.notation(), node.spelling(), node.children.as_slice()) {
            // "There is f : X → Y" runs over the functions from X to Y.
            (FUNCTION_TYPE, _, [f, from, to]) if named(f) => {
                let functions =
                    made("the functions from _ to _", vec![from.clone(), to.clone()])?;
                over.insert(f.text.to_string(), (f.clone(), functions));
            }
            (_, IN, [x, set]) if named(x) => {
                over.insert(x.text.to_string(), (x.clone(), set.clone()));
            }
            _ => said.push(node),
        }
    }
    let mut body =
        conjoined(&ctx.g, said).ok_or("the claim says nothing of what it obtains")?;
    for name in names.iter().rev() {
        let (x, set) = over
            .get(name)
            .ok_or_else(|| format!("the claim states no membership of {name}"))?;
        body = made("there is _ ∈ _ with _", vec![x.clone(), set.clone(), body])?;
    }
    Ok(body)
}

/// One obtain written as a step claiming its "there is" and an obtain from
/// that step's line; the number of lines changed.
pub(super) fn obtain_claimed(
    ctx: &Context,
    path: &str,
    thm: &Theorem,
    lines: &mut Vec<String>,
    end: usize,
    step: &Step,
) -> Result<usize, String> {
    let names = obtained_names(&step.just.text).ok_or("the obtain names nothing")?;
    let original = ctx
        .corpus
        .theorems
        .iter()
        .find(|t| t.qualified() == thm.qualified())
        .ok_or("the theorem is not in the corpus")?;
    let sorts = sorts_in_scope(
        original,
        Env {
            g: &ctx.g,
            scopes: &ctx.corpus.scopes,
        },
    );
    // What the item says there is, where the obtain asks it of the item; a
    // definition that unfolds gives the existence the claim states.
    let there_is = match ctx.obtained.get(&(path.to_string(), step.line)) {
        Some(Built(said)) => match said.as_slice() {
            [one] => one.clone(),
            _ => return Err("the item says more than its \"there is\"".into()),
        },
        Some(Route::Declined(why)) => return Err(why.reason()),
        None => ctx
            .g
            .print(&existence_of(ctx, &sorts, &step.claim, &names)?),
    };
    // A step reading a defined name as what it names cites the define
    // (`SYNTAX.md`), and an obtain from a line cites nothing else.
    let binders = ctx.g.binders();
    let free = |trees: Vec<Node>| -> BTreeSet<String> {
        trees.iter().flat_map(|t| free_names(t, &binders)).collect()
    };
    let claimed = free(read_all(ctx, &sorts, &step.claim)?);
    let stated = free(read_all(
        ctx,
        &sorts,
        &Written::new(there_is.clone(), path, step.line),
    )?);
    let defined: Vec<&String> = claimed
        .iter()
        .filter(|n| !stated.contains(*n) && !names.contains(n))
        .collect();
    if !defined.is_empty() {
        return Err(format!(
            "the claim writes {}, which the \"there is\" writes out, and an obtain from a line cites no define",
            defined.iter().map(|n| n.as_str()).collect::<Vec<_>>().join(", ")
        ));
    }
    let heading = step.line - 1;
    let reason = step.just.line - 1;
    let number = format!("{}.", step.number);
    let at = lines[heading]
        .find(&number)
        .ok_or("the step's number is not where it is read")?;
    let claim_at = at
        + number.len()
        + lines[heading][at + number.len()..]
            .chars()
            .take_while(|c| c.is_whitespace())
            .map(char::len_utf8)
            .sum::<usize>();
    let prefix = lines[heading][..claim_at].to_string();
    let claim_lines: Vec<String> = lines[heading..reason].to_vec();
    let mut last = continued(lines, reason, end)
        .last()
        .copied()
        .unwrap_or(reason);
    for r in &step.requires {
        let l = r.line - 1;
        last = last.max(continued(lines, l, end).last().copied().unwrap_or(l));
    }
    let reason_indent: String = lines[reason]
        .chars()
        .take_while(|c| c.is_whitespace())
        .collect();
    let from = lines[reason]
        .find("obtain ")
        .ok_or("the obtain is not where it is read")?;
    let item_at = from
        + lines[reason][from..]
            .find(':')
            .ok_or("the obtain names no item")?
        + 1;
    let cited = lines[reason][item_at..].trim_start().to_string();
    let number = step
        .number
        .number()
        .ok_or("the theorem's own step has no number to move")?;
    let mut changed = moved_down(thm, lines, end, number);
    // The obtain, under the number the run moved it to, from the new line.
    let mut obtain: Vec<String> = vec![String::new()];
    obtain.extend(claim_lines);
    obtain[1] = lines[heading].clone();
    obtain.push(format!(
        "{reason_indent}obtain {} from line {}",
        names.join(", "),
        step.number
    ));
    // The step claiming the "there is", under the obtain's own number.
    let claimed = vec![
        format!("{prefix}{there_is}"),
        format!("{}{cited}", &lines[reason][..from]),
    ];
    changed += obtain.len() + claimed.len();
    // The reason's continued lines and the requires lines stay with the
    // step that cites the item.
    let after: Vec<String> = lines.drain(last + 1..).collect();
    let kept: Vec<String> = lines.drain(reason + 1..).collect();
    lines.truncate(heading);
    lines.extend(claimed);
    lines.extend(kept);
    lines.extend(obtain);
    lines.extend(after);
    Ok(changed)
}

/// A define of one name, on one line with its `reads` line under it, and
/// the names its term writes free beside its own arguments, read by the
/// front end with the theorem's sorts. A recursion, a define over several
/// lines and one saying a kind of number, which a reason under it proves,
/// are declined.
pub(super) struct Movable {
    pub(super) name: String,
    /// The line, from 0, the define is written on; its `reads` line is the
    /// next.
    pub(super) at: usize,
    pub(super) label: String,
    pub(super) uses: BTreeSet<String>,
}

pub(super) fn movable(
    ctx: &Context,
    sorts: &Sorts,
    d: &DefineLine,
    lines: &[String],
) -> Result<Movable, String> {
    let parts = define::define_parts(&d.text);
    let Built(DefineParts::One(one)) = parts else {
        return Err(format!("{} is a recursion", d.label));
    };
    if one.kind.is_some() || d.reason.is_some() {
        return Err(format!("{} says a kind of number", d.label));
    }
    let at = d.line - 1;
    if !lines[at].trim_start().starts_with("let ")
        || !lines
            .get(at + 1)
            .is_some_and(|l| l.trim_start().starts_with("reads "))
    {
        return Err(format!("{} is written over several lines", d.label));
    }
    let binders = ctx.g.binders();
    let mut uses: BTreeSet<String> = read_all(ctx, sorts, &d.rule(&one.body))?
        .iter()
        .flat_map(|t| free_names(t, &binders))
        .collect();
    // A domain names what it is over as the rule does: `for k ∈ {1, …, N}`
    // names N.
    for p in &one.params {
        uses.extend(
            read_all(ctx, sorts, &d.domain(p))?
                .iter()
                .flat_map(|t| free_names(t, &binders)),
        );
    }
    for p in &one.params {
        uses.remove(&p.name);
    }
    Ok(Movable {
        name: one.name,
        at,
        label: d.label.clone(),
        uses,
    })
}

/// The names a theorem's header gives or writes: what its hypotheses say,
/// read, and the names its header defines give.
pub(super) fn header_names(
    ctx: &Context,
    sorts: &Sorts,
    thm: &Theorem,
) -> Result<BTreeSet<String>, String> {
    let mut out = BTreeSet::new();
    for h in &thm.hypotheses {
        out.extend(names_in(&hypothesis_read(ctx, sorts, thm, h)?));
    }
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        if let Built(parts) = define_parts(&d.text) {
            out.extend(parts.names());
        }
    }
    for r in &thm.ranges {
        out.extend(ctx.letters_of(&r.text));
    }
    Ok(out)
}

/// The names the defines above a file's first theorem give.
pub(super) fn file_names(ctx: &Context, thm: &Theorem) -> BTreeSet<String> {
    ctx.corpus.scopes[thm.scope]
        .defines
        .iter()
        .filter_map(|d| match define_parts(&d.text) {
            Built(parts) => Some(parts.names()),
            outcome::Declined(_) => None,
        })
        .flatten()
        .collect()
}

/// Whether `name` is written on any of `lines`.
pub(super) fn writes(lines: &[String], name: &str) -> bool {
    lines.iter().any(|l| {
        if name.chars().count() == 1 {
            loose_letters(l).contains(name)
        } else {
            re(&format!(r"\b{}\b", escape(name))).is_match(l)
        }
    })
}

/// Each define in a theorem's header over nothing the theorem names raised
/// above the file's first theorem, where it is the file's (`SYNTAX.md`): a
/// naming `let` written as a `define`, `:=` for `=`. The statement and the
/// steps then speak of a define from outside the theorem, which the
/// statement means written out, as it meant the header's. A define whose
/// name another theorem of the file writes stays, and one whose label the
/// file gives elsewhere takes a label the file does not give.
pub fn header_defines_raised(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let mut count = 0;
    let mut theorems = Vec::new();
    let mut declined = Vec::new();
    let mut raised: Vec<String> = Vec::new();
    let thms = theorems_of(ctx, path, lines.len());
    let Some(first) = thms.iter().map(|(t, _)| t.line).min() else {
        return Rewritten {
            text: text.to_string(),
            lines: 0,
            theorems,
            declined,
        };
    };
    // Every label the file gives, so a raised define takes a new one where
    // its own is given elsewhere.
    let label_re = re(r"\(([A-Z])(\d+)\)\s*$");
    let mut given: BTreeMap<String, usize> = BTreeMap::new();
    for l in &lines {
        if let Some(c) = label_re.captures(l) {
            *given.entry(format!("{}{}", &c[1], &c[2])).or_default() += 1;
        }
    }
    let mut next_label = given
        .keys()
        .filter_map(|l| l.strip_prefix('D').and_then(|n| n.parse::<usize>().ok()))
        .max()
        .unwrap_or(0)
        + 1;
    for (thm, end) in &thms {
        let sorts = sorts_in_scope(
            thm,
            Env {
                g: &ctx.g,
                scopes: &ctx.corpus.scopes,
            },
        );
        let header: Vec<&DefineLine> = thm
            .defines
            .iter()
            .filter(|d| d.line < thm.conclusion_line)
            .collect();
        if header.is_empty() {
            continue;
        }
        let own = match header_names(ctx, &sorts, thm) {
            Ok(n) => n,
            Err(why) => {
                declined.push(Declined {
                    theorem: thm.qualified(),
                    why,
                });
                continue;
            }
        };
        let files = file_names(ctx, thm);
        let elsewhere: Vec<String> = lines[..thm.line - 1]
            .iter()
            .chain(lines[*end..].iter())
            .cloned()
            .collect();
        let mut moved: Vec<(Movable, String)> = Vec::new();
        let mut why = Vec::new();
        for d in header {
            let m = match movable(ctx, &sorts, d, &lines) {
                Ok(m) => m,
                Err(e) => {
                    why.push(e);
                    continue;
                }
            };
            let named: Vec<&String> = m
                .uses
                .iter()
                .filter(|n| own.contains(*n) && !files.contains(*n))
                .collect();
            if !named.is_empty() {
                why.push(format!(
                    "{} names {}, which the theorem gives",
                    m.label,
                    named
                        .iter()
                        .map(|n| n.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
                continue;
            }
            if writes(&elsewhere, &m.name) {
                why.push(format!("another theorem of the file writes {}", m.name));
                continue;
            }
            let label = if given.get(&m.label).copied().unwrap_or(0) > 1 {
                let fresh = format!("D{next_label}");
                next_label += 1;
                fresh
            } else {
                m.label.clone()
            };
            moved.push((m, label));
        }
        if !why.is_empty() {
            declined.push(Declined {
                theorem: thm.qualified(),
                why: why.join("; "),
            });
        }
        if moved.is_empty() {
            continue;
        }
        // The theorem's lines without the raised defines, each cited by the
        // label it now has.
        let mut region: Vec<String> = Vec::new();
        for (i, was) in lines.iter().enumerate().take(*end).skip(thm.line - 1) {
            if moved.iter().any(|(m, _)| i == m.at || i == m.at + 1) {
                continue;
            }
            let mut line = was.clone();
            for (m, label) in &moved {
                if *label != m.label && i >= thm.conclusion_line {
                    line = re(&format!(r"\b{}\b", escape(&m.label)))
                        .replace_all(&line, label.as_str())
                        .into_owned();
                }
            }
            if line != *was {
                count += 1;
            }
            region.push(line);
        }
        for (m, label) in &moved {
            let written = lines[m.at].trim_start();
            let rest = written.strip_prefix("let ").unwrap_or(written);
            let defined = rest.replacen(" = ", " := ", 1);
            let defined = label_re
                .replace(&defined, format!("({label})").as_str())
                .into_owned();
            raised.push(format!("define {defined}"));
            raised.push(format!("       {}", lines[m.at + 1].trim_start()));
            raised.push(String::new());
            count += 2;
        }
        lines.splice(thm.line - 1..*end, region);
        theorems.push(thm.qualified());
    }
    // Above the file's first theorem, which no theorem's lines moved.
    lines.splice(first - 1..first - 1, raised);
    Rewritten {
        text: joined(lines, text),
        lines: count,
        theorems,
        declined,
    }
}

/// How many times each line of `thm` is cited: by a step's reason, its
/// requires lines, its chain, or a define's reason.
pub(super) fn citations_counted(thm: &Theorem) -> BTreeMap<String, usize> {
    let mut out: BTreeMap<String, usize> = BTreeMap::new();
    let mut add = |r: &str| *out.entry(r.to_string()).or_default() += 1;
    for step in &thm.steps {
        step.just.refs.iter().for_each(|r| add(r));
        for r in &step.requires {
            r.lines().iter().for_each(|r| add(r));
        }
        for (text, _) in &step.just.chain {
            if let Some(r) = chain_cited(text) {
                add(&r);
            }
        }
    }
    for reason in thm.defines.iter().filter_map(|d| d.reason.as_ref()) {
        reason.lines().iter().for_each(|r| add(r));
    }
    out
}

/// Whether `r` is one of the lines a `from` list ending `line` names, a
/// list of lines and labels and nothing after it.
pub(super) fn in_from_list(line: &str, r: &str) -> bool {
    line.rfind("from ").is_some_and(|at| {
        let items: Vec<&str> = line[at + "from ".len()..]
            .split(',')
            .map(str::trim)
            .collect();
        items.iter().all(|i| {
            !i.is_empty()
                && i.chars()
                    .all(|c| c.is_alphanumeric() || c == '.' || c == '′')
        }) && items.contains(&r)
    })
}

/// A file read again, as `parse_proof` reads it, with each theorem's end.
pub(super) fn reread<'t>(
    path: &str,
    text: &str,
    scope: ScopeId,
    thms: &'t mut Vec<Theorem>,
) -> Vec<(&'t Theorem, usize)> {
    let (_, read) = parse_proof(path, text, scope).expect("the file reads");
    *thms = read;
    thms.sort_by_key(|t| t.line);
    let count = text.lines().count();
    let mut out = Vec::new();
    for (i, t) in thms.iter().enumerate() {
        let end = thms.get(i + 1).map_or(count, |n| n.line - 1);
        out.push((t, end));
    }
    out
}

/// The step of `thms` whose heading is on `line`, with its theorem's end.
pub(super) fn step_on<'t>(
    thms: &[(&'t Theorem, usize)],
    line: usize,
) -> Option<(&'t Theorem, usize, &'t Step)> {
    thms.iter().find_map(|(t, end)| {
        t.steps
            .iter()
            .find(|s| s.line == line)
            .map(|s| (*t, *end, s))
    })
}

/// Each line cited once, by a step's `from` list, first restated by a step
/// of its own that `restate`s it, written just above the citing step, which
/// cites the new step instead (`SYNTAX.md`: `restate`'s claim is its one
/// cited line). A step citing several such lines restates the last.
pub fn cited_lines_restated(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut text = text.to_string();
    let mut count = 0;
    let mut theorems = Vec::new();
    let Some(scope) = ctx
        .corpus
        .theorems
        .iter()
        .find(|t| t.path == path)
        .map(|t| t.scope)
    else {
        return Rewritten {
            text,
            lines: 0,
            theorems,
            declined: Vec::new(),
        };
    };
    // Each citing step's line and the line it restates, from the file as
    // it was. Done from the bottom, so each is where it was read.
    let mut pending: Vec<(usize, String)> = Vec::new();
    let mut thms = Vec::new();
    for (thm, _) in reread(path, &text, scope, &mut thms) {
        let counted = citations_counted(thm);
        let numbers: BTreeSet<String> =
            thm.steps.iter().map(|s| s.number.to_string()).collect();
        for step in &thm.steps {
            if !step.just.chain.is_empty() {
                continue;
            }
            // A line in another block than the citing step's is read there
            // at the letters of the blocks between (`SYNTAX.md`, a "for all"
            // at a block's letter), which a restatement written inside the
            // citing step's block would not be: only a line of its own block
            // is restated.
            let block = |n: &str| n.rsplit_once('.').map(|(b, _)| b.to_string());
            let here = block(&step.number.to_string());
            let restated = step.just.refs.iter().rev().find(|r| {
                numbers.contains(*r)
                    && block(r) == here
                    && counted.get(*r) == Some(&1)
                    && in_from_list(&step.just.text, r)
                    && thm
                        .steps
                        .iter()
                        .find(|s| s.number.to_string() == **r)
                        // An obtain's memberships are said there once, and no
                        // later step writes them (`SYNTAX.md`).
                        .is_some_and(|s| {
                            !s.impossible && !s.just.head.is(Method::Obtain)
                        })
            });
            if let Some(r) = restated {
                pending.push((step.line, r.clone()));
            }
        }
    }
    pending.sort_by_key(|(line, _)| Reverse(*line));
    for (line, restated) in pending {
        let mut thms = Vec::new();
        let read = reread(path, &text, scope, &mut thms);
        let Some((thm, end, step)) = step_on(&read, line) else {
            continue;
        };
        let Some(cited) = thm.steps.iter().find(|s| s.number.to_string() == restated)
        else {
            continue;
        };
        let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
        let number = step.number.to_string();
        let heading = step.line - 1;
        let prefix: String = lines[heading]
            .chars()
            .take_while(|c| c.is_whitespace())
            .collect();
        let indent: String = lines[step.just.line - 1]
            .chars()
            .take_while(|c| c.is_whitespace())
            .collect();
        let Some(moving) = step.number.number() else {
            continue;
        };
        count += moved_down(thm, &mut lines, end, moving);
        let map = BTreeMap::from([(restated.clone(), number.clone())]);
        let mut reason = vec![step.just.line - 1];
        reason.extend(continued(&lines, step.just.line - 1, end));
        for l in reason {
            lines[l] = renumbered_line(&lines, l, &map);
        }
        let claim = cited
            .claim
            .text()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        let new_step = vec![
            format!("{prefix}{number}.  {claim}"),
            format!("{indent}restate {restated}"),
            String::new(),
        ];
        count += new_step.len() + 1;
        lines.splice(heading..heading, new_step);
        if !theorems.contains(&thm.qualified()) {
            theorems.push(thm.qualified());
        }
        text = joined(lines, &text);
    }
    Rewritten {
        text,
        lines: count,
        theorems,
        declined: Vec::new(),
    }
}

/// Each step citing an item, cited once and by a later step of its run,
/// written as a requires line of that step: its claim the line's fact and
/// its reason the line's (`SYNTAX.md`: a requires line is justified as a
/// step is). The reverse of `requires_raised`. A step of one line saying
/// one sentence is moved, under a step whose reason is one line and that
/// opens no block.
pub fn steps_as_requires(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut text = text.to_string();
    let mut count = 0;
    let mut theorems = Vec::new();
    let Some(scope) = ctx
        .corpus
        .theorems
        .iter()
        .find(|t| t.path == path)
        .map(|t| t.scope)
    else {
        return Rewritten {
            text,
            lines: 0,
            theorems,
            declined: Vec::new(),
        };
    };
    let lone = |lines: &[String], l: usize| !lines[l].trim_end().ends_with(',');
    // An item whose hypotheses its requires lines state: not a definition,
    // which unfolds the line a step cites rather than asking it.
    let asks = |just: &Justification| {
        just.cited_item().is_some_and(|cited| {
            let full = just.item(&cited);
            !ctx.corpus
                .records
                .iter()
                .any(|r| r.qualified() == full && r.kind.unfolds())
        })
    };
    let movable = |thm: &Theorem, x: &Step, lines: &[String]| {
        let opens = thm.steps.iter().any(|o| {
            o.number.depth() > x.number.depth() && x.number.contains(&o.number)
        });
        // A requires line holds for its own step only, and a statement
        // applying a define is carried to from the proof's outermost lines,
        // one of which may say an argument is in the define's domain
        // (`checker::citations::check_conclusion_domains`): such a line, a
        // membership or a part, stays a line.
        let says_domain = ctx
            .tokens(x.claim.text())
            .is_some_and(|t| t.iter().any(|t| t.text == "∈" || t.text == "⊆"));
        let carried_from =
            x.number.depth() == 1 && says_domain && applies_a_define(ctx, thm);
        // A part, X ⊆ A, is cited for what it says of its members as well,
        // "for all x ∈ X, x ∈ A" (`SYNTAX.md`, a subset as its members),
        // which no hypothesis asks in that form: it stays a line.
        let a_part = ctx
            .tokens(x.claim.text())
            .is_some_and(|t| t.iter().any(|t| t.text == "⊆"));
        !carried_from
            && !a_part
            && x.just.head.is_item()
            && asks(&x.just)
            && x.just.target.is_none()
            && x.just.contradicting.is_none()
            && x.just.chain.is_empty()
            && x.requires.is_empty()
            && x.openers.is_empty()
            && !opens
            && x.claim.sentences().len() == 1
            && x.just.line == x.line + 1
            && lone(lines, x.just.line - 1)
    };
    // The citer of `x`: the one step citing it, later in its run.
    let citer = |thm: &'_ Theorem, x: &Step, lines: &[String]| {
        let r = x.number.to_string();
        if citations_counted(thm).get(&r) != Some(&1) {
            return None;
        }
        thm.steps
            .iter()
            .find(|s| s.just.refs.contains(&r))
            .filter(|s| {
                s.number.parent() == x.number.parent()
                    && s.part == x.part
                    && s.line > x.line
                    && in_from_list(&lines[s.just.line - 1], &r)
                    && s.just.contradicting.is_none()
                    && asks(&s.just)
                    && s.just.chain.is_empty()
                    // A requires line goes after a step's rows, and a row
                    // cites a line and never a requires line.
                    && s.just.rows.is_empty()
                    && s.openers.is_empty()
                    && !s.just.head.takes_block()
                    && lone(lines, s.just.line - 1)
            })
            .cloned()
    };
    let mut pending: Vec<usize> = Vec::new();
    let mut thms = Vec::new();
    let lines: Vec<String> = text.lines().map(str::to_string).collect();
    for (thm, _) in reread(path, &text, scope, &mut thms) {
        for x in &thm.steps {
            // A membership the page says once at the citer, k! ∈ ℕ, is one
            // its requires lines may not say, since the step already has it
            // (`check_repeated`). And a requires line does work where a
            // cited step need not (`check_requires_work`), so a step the
            // citer does not need stays a step. Both read the lines as the
            // checker read them, before any step moves.
            let at = |s: &Step| (thm.path.clone(), x.line, s.line);
            let fits = |s: &Step| {
                !ctx.said_once.contains(&at(s)) && ctx.needed.contains(&at(s))
            };
            if movable(thm, x, &lines)
                && citer(thm, x, &lines).is_some_and(|s| fits(&s))
            {
                pending.push(x.line);
            }
        }
    }
    pending.sort_by_key(|line| Reverse(*line));
    for line in pending {
        let mut thms = Vec::new();
        let read = reread(path, &text, scope, &mut thms);
        let Some((thm, end, x)) = step_on(&read, line) else {
            continue;
        };
        let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
        let Some(s) = citer(thm, x, &lines) else {
            continue;
        };
        // The citer no longer cites the step, and then the steps after it
        // move up one.
        let at = s.just.line - 1;
        let indent: String = lines[at]
            .chars()
            .take_while(|c| c.is_whitespace())
            .collect();
        let Some(rest) = without_ref(&lines[at], &x.number.to_string()) else {
            continue;
        };
        lines[at] = format!("{indent}{rest}");
        let Some(moving) = x.number.number() else {
            continue;
        };
        let n = moving.last();
        let map = run_shifted(thm, moving, |m| m > n, -1);
        count += renumbered(thm, &mut lines, end, &map);
        let fact = x.claim.text().trim().trim_end_matches('.').to_string();
        lines.insert(
            at + 1,
            format!("{indent}requires {fact}: {}", x.just.text.trim()),
        );
        // The step's heading and reason, and a blank line after them.
        let mut gone = 2;
        if lines.get(x.line + 1).is_some_and(|l| l.trim().is_empty()) {
            gone += 1;
        }
        lines.drain(x.line - 1..x.line - 1 + gone);
        count += 2 + gone;
        if !theorems.contains(&thm.qualified()) {
            theorems.push(thm.qualified());
        }
        text = joined(lines, &text);
    }
    Rewritten {
        text,
        lines: count,
        theorems,
        declined: Vec::new(),
    }
}

/// Whether `thm`'s statement applies a define of its own or of its file,
/// as `G(m − 1, n)` applies G: a name a define gives, written with a
/// bracket after it, as the tokeniser cuts the statement.
pub(super) fn applies_a_define(ctx: &Context, thm: &Theorem) -> bool {
    let mut names = file_names(ctx, thm);
    for d in &thm.defines {
        if let Built(parts) = define_parts(&d.text) {
            names.extend(parts.names());
        }
    }
    let tokens = ctx.tokens(thm.stated().text()).unwrap_or_default();
    tokens
        .windows(2)
        .any(|w| names.contains(&w[0].text) && w[1].text == "(")
}

/// Each define in a proof over nothing but what the theorem's header gives
/// lowered into the header, above `then` (`SYNTAX.md`: a define may stand
/// where the proof first needs it, or in the header). A define whose name
/// the proof gives twice, as two cases might, stays.
pub fn defines_lowered(ctx: &Context, path: &str, text: &str) -> Rewritten {
    let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
    let mut count = 0;
    let mut theorems = Vec::new();
    let mut declined = Vec::new();
    for (thm, end) in theorems_of(ctx, path, lines.len()) {
        let sorts = sorts_in_scope(
            thm,
            Env {
                g: &ctx.g,
                scopes: &ctx.corpus.scopes,
            },
        );
        let proof: Vec<&DefineLine> = thm
            .defines
            .iter()
            .filter(|d| d.line > thm.conclusion_line)
            .collect();
        if proof.is_empty() {
            continue;
        }
        let own = match header_names(ctx, &sorts, thm) {
            Ok(n) => n,
            Err(why) => {
                declined.push(Declined {
                    theorem: thm.qualified(),
                    why,
                });
                continue;
            }
        };
        let files = file_names(ctx, thm);
        let given: Vec<String> = proof
            .iter()
            .filter_map(|d| match define_parts(&d.text) {
                Built(parts) => Some(parts.names()),
                outcome::Declined(_) => None,
            })
            .flatten()
            .collect();
        let mut written_above: Vec<String> = vec![thm.conclusion.clone()];
        written_above.extend(thm.hypotheses.iter().map(|h| h.text.clone()));
        let mut moved: Vec<Movable> = Vec::new();
        let mut why = Vec::new();
        for d in proof {
            let m = match movable(ctx, &sorts, d, &lines) {
                Ok(m) => m,
                Err(e) => {
                    why.push(e);
                    continue;
                }
            };
            let outside: Vec<&String> = m
                .uses
                .iter()
                .filter(|n| !own.contains(*n) && !files.contains(*n))
                .collect();
            if !outside.is_empty() {
                why.push(format!(
                    "{} names {}, which the header does not give",
                    m.label,
                    outside
                        .iter()
                        .map(|n| n.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
                continue;
            }
            if given.iter().filter(|n| **n == m.name).count() > 1 {
                why.push(format!("the proof gives {} twice", m.name));
                continue;
            }
            // The statement is in the header's scope, and a letter it binds
            // would be the define's name there.
            if writes(&written_above, &m.name) {
                why.push(format!("the header writes {}", m.name));
                continue;
            }
            moved.push(m);
        }
        if !why.is_empty() {
            declined.push(Declined {
                theorem: thm.qualified(),
                why: why.join("; "),
            });
        }
        if moved.is_empty() {
            continue;
        }
        let mut region: Vec<String> = Vec::new();
        let mut i = thm.line - 1;
        while i < end {
            if i == thm.conclusion_line - 1 {
                for m in &moved {
                    region.push(format!("  {}", lines[m.at].trim_start()));
                    region.push(format!("         {}", lines[m.at + 1].trim_start()));
                    count += 2;
                }
            }
            if let Some(m) = moved.iter().find(|m| m.at == i) {
                // The define, its reads line, and a blank line after them.
                i = m.at + 2;
                if lines.get(i).is_some_and(|l| l.trim().is_empty()) {
                    i += 1;
                }
                continue;
            }
            region.push(lines[i].clone());
            i += 1;
        }
        lines.splice(thm.line - 1..end, region);
        theorems.push(thm.qualified());
    }
    Rewritten {
        text: joined(lines, text),
        lines: count,
        theorems,
        declined,
    }
}
