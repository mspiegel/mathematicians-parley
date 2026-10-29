//! An angle is written only where its three points are said to differ
//! (`SYNTAX.md`, Formulas).
//!
//! ∠PQR needs P ≠ Q, Q ≠ R and P ≠ R said where it is written: by a line in
//! scope above it, a requires line of its own step, or earlier in its own
//! line, as the condition of an "if" or a "with" or a conjunct before it. A
//! difference is said by `≠`, written either way round; by "P, Q, R form a
//! triangle", which says all three; by "Q is between P and R", which does
//! too; or by "X and Y are on the same side of line AB", or on opposite
//! sides, which says A ≠ B and that X and Y each differ from A and B. A
//! theorem's statement says it among its hypotheses.

use super::formulas::{claim_parts, one_formula_parts, FormulaPart};
use super::library::{Known, Stated};
use super::structure::in_scope;
use super::Report;
use std::collections::BTreeSet;

use indexmap::IndexMap;

use crate::corpus::{define_parts, DefineParts, Intro, Record, Step, Theorem};
use crate::formula::Sorts;
use crate::matching::{alike_top, Context};
use crate::outcome::Built;
use crate::sorts::{unlabel, Env};
use crate::formula::notation_id::NotationId;
use crate::formula::page::Written;
use crate::formula::Node;
use crate::notations::{
    COMMA_CONJUNCTION, CONDITIONAL, CONJUNCTION, EQUALITY, IMPLICATION, LOGICAL_NOT,
};

/// Two points a line says differ, and the step whose claim says it, where a
/// numbered step does.
struct Apart {
    one: Node,
    other: Node,
    step: Option<String>,
}

/// Every angle a theorem writes has its three points said to differ where
/// it is written.
pub fn check_angle_points(report: &mut Report, thm: &Theorem, known: &Known) {
    // An angle written twice on a line is reported once.
    let mut told: Vec<(usize, Node)> = Vec::new();
    each_angle(thm, known, &mut |part, angle, said| {
        if told.iter().any(|(l, t)| *l == part.line && known.alike(t, angle)) {
            return;
        }
        let same = |a: &Node, b: &Node| known.alike(a, b);
        let missing: Vec<String> = unsaid(angle, said, &same)
            .into_iter()
            .map(|(p, q)| format!("{} ≠ {}", known.print(p), known.print(q)))
            .collect();
        if !missing.is_empty() {
            told.push((part.line, angle.clone()));
            report.say(
                &thm.path,
                part.line,
                format!(
                    "{} writes {}, and nothing where it is written says {}: an angle is written only where its three points are said to differ",
                    part.what,
                    known.print(angle),
                    missing.join(" or ")
                ),
            );
        }
    });
}

/// The numbered steps an angle rests on: a step whose claim says two of its
/// points differ, where nothing else above the angle says so. Such a step
/// is used, as a step another line cites is (`structure::check_steps_used`).
pub fn steps_relied_on(thm: &Theorem, known: &Known) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let same = |a: &Node, b: &Node| known.alike(a, b);
    each_angle(thm, known, &mut |_, angle, said| {
        for (a, b) in [(0, 1), (1, 2), (0, 2)] {
            let (p, q) = (&angle.children[a], &angle.children[b]);
            let saying: Vec<&Apart> = said.iter().filter(|x| x.says(p, q, &same)).collect();
            if saying.iter().all(|x| x.step.is_some()) {
                out.extend(saying.iter().filter_map(|x| x.step.clone()));
            }
        }
    });
    out
}

/// Call `found` at each angle a theorem writes, with the part it is written
/// in and the differences said where it stands.
fn each_angle(
    thm: &Theorem,
    known: &Known,
    found: &mut impl FnMut(&FormulaPart, &Node, &[Apart]),
) {
    let ids = Ids::new();
    let stated: Vec<Apart> = thm
        .hypotheses
        .iter()
        .filter(|h| h.kind != Intro::Let)
        .flat_map(|h| sentences(known, &h.body(&thm.path)))
        .flat_map(|n| apart(&n, &ids))
        .collect();
    let mut parts = claim_parts(thm);
    parts.extend(one_formula_parts(thm));
    parts.extend(naming_parts(thm));
    for part in parts {
        let step = governing(thm, &part);
        let mut said: Vec<Apart> = stated.iter().map(Apart::copy).collect();
        if let Some(step) = step {
            said.extend(above(thm, known, step, part.line, &ids));
        }
        let mut earlier = Vec::new();
        for node in sentences(known, &part.written) {
            walk(&node, &said, &mut earlier, &ids, &mut |angle, here| {
                found(&part, angle, here)
            });
            earlier.extend(apart(&node, &ids));
        }
    }
}

/// The pairs of an angle's points that nothing in `said` says differ.
fn unsaid<'a>(
    angle: &'a Node,
    said: &[Apart],
    same: &impl Fn(&Node, &Node) -> bool,
) -> Vec<(&'a Node, &'a Node)> {
    [(0, 1), (1, 2), (0, 2)]
        .iter()
        .map(|&(a, b)| (&angle.children[a], &angle.children[b]))
        .filter(|(p, q)| !said.iter().any(|x| x.says(p, q, same)))
        .collect()
}

/// Every angle a library item's statement writes has its three points said
/// to differ by the item's `assume` lines, or earlier in its own line.
pub fn check_record_angles(
    report: &mut Report,
    records: &[Record],
    env: Env,
    record_sorts: &IndexMap<usize, Sorts>,
    ctx: &Context,
) {
    let ids = Ids::new();
    let same = |a: &Node, b: &Node| alike_top(a, b, ctx);
    for (i, r) in records.iter().enumerate() {
        if !r.kind.is_item() {
            continue;
        }
        let sorts = &record_sorts[&i];
        // A sentence that does not read is `database::check_statements`'s to
        // report, at the same line.
        let read = |text: &str, line: usize| -> Vec<Node> {
            let mut out = Vec::new();
            for s in Written::new(unlabel(text), &r.path, line).sentences() {
                match s.read(env.g, sorts) {
                    Ok(node) => out.push(node),
                    Err(_) => continue,
                }
            }
            out
        };
        let assumed: Vec<(Vec<Node>, usize)> = r
            .hypotheses
            .iter()
            .filter(|h| h.kind == Intro::Assume)
            .map(|h| (read(&h.text, h.line), h.line))
            .collect();
        let said: Vec<Apart> = assumed
            .iter()
            .flat_map(|(nodes, _)| nodes.iter().flat_map(|n| apart(n, &ids)))
            .collect();
        let mut places = assumed;
        places.extend(r.conclusions.iter().map(|(t, n)| (read(t, *n), *n)));
        for (nodes, line) in places {
            let mut earlier = Vec::new();
            let mut told: Vec<Node> = Vec::new();
            for node in nodes {
                walk(&node, &said, &mut earlier, &ids, &mut |angle, here| {
                    if told.iter().any(|t| alike_top(t, angle, ctx)) {
                        return;
                    }
                    let missing: Vec<String> = unsaid(angle, here, &same)
                        .into_iter()
                        .map(|(p, q)| format!("{} ≠ {}", env.g.print(p), env.g.print(q)))
                        .collect();
                    if !missing.is_empty() {
                        told.push(angle.clone());
                        report.say(
                            &r.path,
                            line,
                            format!(
                                "{} {} writes {}, and its hypotheses do not say {}: an angle is written only where its three points are said to differ",
                                r.header(),
                                r.name,
                                env.g.print(angle),
                                missing.join(" or ")
                            ),
                        );
                    }
                });
                earlier.extend(apart(&node, &ids));
            }
        }
    }
}

/// The notations this check reads, by the names their records give.
struct Ids {
    angle: NotationId,
    triangle: NotationId,
    between: NotationId,
    same_side: NotationId,
    opposite_sides: NotationId,
}

impl Ids {
    fn new() -> Ids {
        Ids {
            angle: NotationId::of("angle"),
            triangle: NotationId::of("forms-a-triangle"),
            between: NotationId::of("between"),
            same_side: NotationId::of("same-side"),
            opposite_sides: NotationId::of("opposite-sides"),
        }
    }
}

impl Apart {
    fn copy(&self) -> Apart {
        Apart {
            one: self.one.clone(),
            other: self.other.clone(),
            step: self.step.clone(),
        }
    }

    /// Whether this says `p` and `q` differ, in either order, two points
    /// being one where `same` says so.
    fn says(&self, p: &Node, q: &Node, same: &impl Fn(&Node, &Node) -> bool) -> bool {
        (same(&self.one, p) && same(&self.other, q)) || (same(&self.one, q) && same(&self.other, p))
    }
}

/// The differences a formula says outright: each "and" part of it that is a
/// `≠`, a triangle or a betweenness.
fn apart(node: &Node, ids: &Ids) -> Vec<Apart> {
    let pair = |one: &Node, other: &Node| Apart {
        one: one.clone(),
        other: other.clone(),
        step: None,
    };
    let n = node.notation();
    if (n == CONJUNCTION || n == COMMA_CONJUNCTION) && !node.children.is_empty() {
        return node.children.iter().flat_map(|c| apart(c, ids)).collect();
    }
    if n == LOGICAL_NOT
        && node.children.len() == 1
        && node.children[0].notation() == EQUALITY
        && node.children[0].children.len() == 2
    {
        let eq = &node.children[0].children;
        return vec![pair(&eq[0], &eq[1])];
    }
    if (n == ids.triangle || n == ids.between) && node.children.len() == 3 {
        let c = &node.children;
        return vec![pair(&c[0], &c[1]), pair(&c[1], &c[2]), pair(&c[0], &c[2])];
    }
    // X and Y on a side of line AB are off the line, so neither is A or B,
    // and a line through two points has them apart.
    if (n == ids.same_side || n == ids.opposite_sides) && node.children.len() == 4 {
        let c = &node.children;
        return vec![
            pair(&c[2], &c[3]),
            pair(&c[0], &c[2]),
            pair(&c[0], &c[3]),
            pair(&c[1], &c[2]),
            pair(&c[1], &c[3]),
        ];
    }
    Vec::new()
}

/// Walk a formula, calling `found` at each angle with the differences said
/// where it stands: `said`, those of the line's earlier sentences, and
/// within the formula the condition of an "if" before its consequence and
/// each "and" part before the next.
fn walk(
    node: &Node,
    said: &[Apart],
    earlier: &mut Vec<Apart>,
    ids: &Ids,
    found: &mut impl FnMut(&Node, &[Apart]),
) {
    let n = node.notation();
    if n == ids.angle && node.children.len() == 3 {
        let mut here: Vec<Apart> = said.iter().map(Apart::copy).collect();
        here.extend(earlier.iter().map(Apart::copy));
        found(node, &here);
    }
    let in_order = n == CONJUNCTION
        || n == COMMA_CONJUNCTION
        || n == IMPLICATION
        || n == CONDITIONAL;
    if in_order {
        let kept = earlier.len();
        for child in &node.children {
            walk(child, said, earlier, ids, found);
            earlier.extend(apart(child, ids));
        }
        earlier.truncate(kept);
        return;
    }
    for child in &node.children {
        walk(child, said, earlier, ids, found);
    }
}

/// Each sentence of a written part, read as the page writes it; one that
/// does not read is `check_formulas`'s to report.
fn sentences(known: &Known, written: &Written) -> Vec<Node> {
    written
        .sentences()
        .iter()
        .filter_map(|s| known.read_as_written(s))
        .collect()
}

/// The step whose scope a part stands in: the last step whose claim is on
/// or above the part's line. None for the statement and what stands above
/// the first step.
fn governing<'t>(thm: &'t Theorem, part: &FormulaPart) -> Option<&'t Step> {
    if thm.hypotheses.iter().any(|h| h.line == part.line) || part.line == thm.line {
        return None;
    }
    thm.steps.iter().rev().find(|s| s.line <= part.line)
}

/// The differences said above `line` in `step`'s scope: the claims of the
/// steps it sees, the lines its labels name, and its own requires lines.
fn above(thm: &Theorem, known: &Known, step: &Step, line: usize, ids: &Ids) -> Vec<Apart> {
    let mut out = Vec::new();
    for t in &thm.steps {
        let seen = t.number == step.number || in_scope(&t.number, &step.number);
        if seen && t.line < line {
            let number = t.number.to_string();
            out.extend(
                sentences(known, &t.claim)
                    .iter()
                    .flat_map(|n| apart(n, ids))
                    .map(|a| Apart {
                        step: Some(number.clone()),
                        ..a
                    }),
            );
        }
    }
    for (key, stated) in known.scope(step).iter() {
        if key.starts_with(|c: char| c.is_ascii_digit()) {
            continue;
        }
        if stated_line(stated).is_some_and(|l| l < line) {
            out.extend(known.sentences(stated).iter().flat_map(|n| apart(n, ids)));
        }
    }
    for r in &step.requires {
        out.extend(sentences(known, &r.fact).iter().flat_map(|n| apart(n, ids)));
    }
    out
}

/// The line a statement in scope stands on.
fn stated_line(stated: &Stated) -> Option<usize> {
    match stated {
        Stated::Written(w) | Stated::Hypothesis(w) => Some(w.line()),
        Stated::Introduced(i) => Some(i.body.line()),
        Stated::InBlocks { line, .. } => Some(line.line()),
        Stated::Kind { .. } => None,
    }
}

/// A naming `let` above a step and the requires lines under its reason, as
/// parts: an angle a let names is written there.
fn naming_parts(thm: &Theorem) -> Vec<FormulaPart> {
    let mut out = Vec::new();
    for d in &thm.defines {
        let what = format!("let {}", d.label);
        if let Built(DefineParts::One(said)) = define_parts(&d.text) {
            out.push(FormulaPart::new(d.line, what.clone(), &d.rule(&said.body)));
        }
        if let Some(reason) = &d.reason {
            for r in &reason.requires {
                out.push(FormulaPart::new(r.line, what.clone(), &r.fact));
            }
        }
    }
    out
}
