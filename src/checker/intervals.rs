//! A closed interval's ends are numbers where the interval is written
//! (`SYNTAX.md`, Formulas).
//!
//! The shape of an interval says what its members are: a member of [a, b]
//! is a real number (`citing::interval_system`). That a and b are real is
//! asked once, where a line lets a letter range over the interval, by a
//! `let`, an `obtain`, a "for all" or a "there is": by the one membership
//! rule over no lines (`membership::shown`), with the letters and function
//! types in scope there, since a line introducing a letter cites nothing.
//! `let x ∈ [0, f(1)]` under `let f : ℝ → ℝ` has f(1) real by f's type.

use super::angles::{governing, sentences};
use super::formulas::{claim_parts, one_formula_parts, FormulaPart};
use super::library::{introduced, statement_scope, typed_in_scope, Known};
use super::record::IntervalEnds;
use super::Report;

use indexmap::IndexMap;

use crate::citing::{closed_interval, Introduced};
use crate::corpus::Theorem;
use crate::formula::Node;
use crate::methods::membership::{self, Shown};
use crate::notations::MEMBERSHIP;
use crate::rules::System;

/// Every closed interval a line lets a letter range over has ends the one
/// membership rule says are in the system the interval asks.
pub fn check_interval_ends(report: &mut Report, thm: &Theorem, known: &Known) {
    each_interval(thm, known, &mut |part, interval, ends, shown| {
        for (end, shown) in interval.children.iter().zip(shown) {
            if shown.is_none() {
                report.say(
                    &thm.path,
                    part.line,
                    format!(
                        "{} lets a letter range over {}, and nothing in scope says {} ∈ {}: an interval's ends are numbers",
                        part.what,
                        known.print(interval),
                        known.print(end),
                        ends.sign()
                    ),
                );
            }
        }
    });
}

/// How the ends of each closed interval a line lets a letter range over
/// are numbers, once for each interval (`CheckedTheorem::interval_ends`).
pub fn interval_ends(thm: &Theorem, known: &Known) -> Vec<IntervalEnds> {
    let mut out: Vec<IntervalEnds> = Vec::new();
    each_interval(thm, known, &mut |_, interval, _, shown| {
        let [Some(low), Some(high)] = shown else {
            return;
        };
        if out.iter().any(|e| known.alike(&e.interval, interval)) {
            return;
        }
        out.push(IntervalEnds {
            interval: interval.clone(),
            low,
            high,
        });
    });
    out
}

/// Call `found` at each closed interval a line lets a letter range over,
/// with the part it is written in, the system its ends are asked in, and
/// how each end is in it, None where the one rule does not say.
fn each_interval(
    thm: &Theorem,
    known: &Known,
    found: &mut impl FnMut(&FormulaPart, &Node, System, [Option<Shown>; 2]),
) {
    let mut parts = claim_parts(thm);
    parts.extend(one_formula_parts(thm));
    let statement = statement_scope(known);
    for part in parts {
        let (letters, typed): (Introduced, Vec<Node>) = match governing(thm, &part) {
            Some(step) => (introduced(known, step), typed_in_scope(known, step)),
            None => statement.clone(),
        };
        let given = membership::Facts {
            facts: &[],
            letters,
            ranged: IndexMap::new(),
            typed: &typed,
            in_sums: &typed,
            targets: known.targets,
            ctx: known.ctx,
        };
        for node in sentences(known, &part.written) {
            for ranging in node.walk() {
                let Some((interval, ends)) = ranged_over(&ranging, known) else {
                    continue;
                };
                let [low, high] = interval.children.as_slice() else {
                    continue;
                };
                let shown = [
                    membership::shown(low, ends, &given),
                    membership::shown(high, ends, &given),
                ];
                found(&part, interval, ends, shown);
            }
        }
    }
}

/// The closed interval `node` lets a letter range over, and the system its
/// ends are asked in: `x ∈ [a, b]`, or a binder over [a, b], "for all
/// x ∈ [a, b], …", with points taken out or not. None for any other node.
fn ranged_over<'n>(node: &'n Node, known: &Known) -> Option<(&'n Node, System)> {
    let (letter, set) = match node.children.as_slice() {
        [letter, set] if node.notation() == MEMBERSHIP => (letter, set),
        [letter, set, _] if known.ctx.binders.contains_key(&node.notation()) => {
            (letter, set)
        }
        _ => return None,
    };
    if !letter.is_name() {
        return None;
    }
    closed_interval(set)
}
