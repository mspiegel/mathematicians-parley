//! Chain claims, inequality rows, kind methods and memberships.

use super::super::record::{HeldByLines, Inspection, PlaceShown, ShownBy, StatedIn};
use super::*;
use crate::methods::inspection;
use crate::methods::inspection::{Facts, Inspected};
use std::iter;

use crate::citing;
use crate::citing::Introduced;
use crate::corpus::{proof, DefineLine};
use crate::formula::{page, ByShape};
use num_traits::{Signed, Zero};

/// What a calculation's chain gives of its ends.
pub(super) enum ChainClaim {
    /// The first term related to the last by the chain's relation.
    Ends(Node),
    /// Orders going up and going down, which give nothing.
    BothWays,
}

/// What `links` give, as `check_calculation_claims` reads it; None for no
/// chain, a link that does not read (`check_formulas`' to report), or a
/// congruence joined with an order (`check_chain_congruences`').
pub(super) fn chain_claim(links: &[Link], known: &Known) -> Option<ChainClaim> {
    let read = |w: &Written| known.read_as_written(&w.formula().ok()?);
    let first = read(&links.first()?.from)?;
    let last_line = &links.last()?.line;
    let last = read(&last_line.term)?;
    let congruence = links.iter().find(|l| l.line.relation == "≡");
    let (relation, modulus) = match congruence {
        Some(link) => {
            let ordered = links
                .iter()
                .any(|l| !["=", "≡"].contains(&l.line.relation.as_str()));
            if ordered {
                return None;
            }
            ("≡", Some(read(link.line.modulus.as_ref()?)?))
        }
        None => {
            let related: Option<Vec<Related>> = links
                .iter()
                .map(|l| l.claim(known).as_ref().and_then(Related::of))
                .collect();
            match chain_rel(&related?) {
                Some(rel) => (sign(rel), None),
                None => return Some(ChainClaim::BothWays),
            }
        }
    };
    let at = (last_line.term.path(), last_line.line);
    let (g, sorts) = (known.env.g, &known.sorts);
    related(g, sorts, relation, &first, &last, modulus.as_ref(), at)
        .ok()
        .map(ChainClaim::Ends)
}

/// An `antisymmetry` step (`METHODS.md`, antisymmetry): it cites two lines,
/// an order `a ≤ b` and its converse `b ≤ a`, and claims `a = b`, either way
/// round, every atom of the two sides real.
pub fn check_antisymmetry(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in thm
        .steps
        .iter()
        .filter(|s| s.just.head.is(Method::Antisymmetry))
    {
        let links = match cited_links(thm, step, known, "antisymmetry") {
            Ok(links) => links,
            Err(defect) => {
                report.problems.push(defect);
                continue;
            }
        };
        let number = &step.number;
        // Each read from below: `b ≥ a` is `a ≤ b`.
        let below: Vec<Related> = links
            .iter()
            .map(|l| {
                if l.rel == Rel::Ge {
                    l.turned()
                } else {
                    l.clone()
                }
            })
            .collect();
        let converse = match below.as_slice() {
            [one, other] => {
                one.rel == Rel::Le
                    && other.rel == Rel::Le
                    && known.alike(&one.left, &other.right)
                    && known.alike(&one.right, &other.left)
            }
            _ => false,
        };
        if !converse {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {number} cites by antisymmetry what is not two lines a ≤ b and b ≤ a, an order and its converse"
                ),
            );
            continue;
        }
        let Some(claim) = known.whole_as_written(&step.claim) else {
            continue; // `check_formulas` says it does not read
        };
        let equation = Related {
            left: below[0].left.clone(),
            right: below[0].right.clone(),
            rel: Rel::Eq,
            said: claim.clone(),
            written: true,
            turned: false,
        };
        if !Related::of(&claim).is_some_and(|c| c.says(&equation, known)) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {number} claims {}, and its lines give {} = {}",
                    step.claim_text(),
                    known.print(&equation.left),
                    known.print(&equation.right)
                ),
            );
            continue;
        }
        report_unreal(report, thm, step, &claim, &links, known, targets);
    }
}

/// Whether two terms are one number by the field's identities, as `algebra`
/// decides an identity (`methods::algebra`): what writing a side another way
/// keeps.
pub(super) fn one_number(a: &Node, b: &Node, known: &Known, targets: &Targets) -> bool {
    let equation = made(known.env.g, EQUALS, vec![a.clone(), b.clone()]);
    let labels = FloatLabels::new(IndexMap::new());
    matches!(
        algebra::decide(&term_of_node(&equation, targets), &[], &labels),
        algebra::Verdict::Holds { .. }
    )
}

/// A term written in a row's reason, `adding 2·A` or `multiplying by 1/2`,
/// read through the tree reader.
pub(super) fn reason_term(written: &Written, known: &Known) -> Checked<Node> {
    known.parse(&written.formula()?)
}

/// Whether `row` is `above` with the manipulation `reason` names
/// (`METHODS.md`, inequalities, Rows), each side compared as one number
/// (`one_number`). `term` is the term the reason writes, read.
pub(super) fn row_follows(
    above: &Related,
    row: &Related,
    reason: &RowReason,
    term: Option<&Node>,
    known: &Known,
    targets: &Targets,
) -> bool {
    let g = known.env.g;
    let sides = |rel: Rel, left: &Node, right: &Node| {
        row_is(row, rel, left, right, known, targets)
    };
    match (reason, term) {
        (RowReason::Adding(_), Some(t)) => {
            let plus = |side: &Node| made(g, PLUS, vec![side.clone(), t.clone()]);
            sides(above.rel, &plus(&above.left), &plus(&above.right))
        }
        (RowReason::Multiplying(_), Some(c)) => {
            let labels = FloatLabels::new(IndexMap::new());
            let Some(value) = linear::numeral(&term_of_node(c, targets), &labels)
            else {
                return false;
            };
            if Zero::is_zero(&value) {
                return false;
            }
            // A negative number turns an order round.
            let rel = if Signed::is_negative(&value) {
                above.rel.converse()
            } else {
                above.rel
            };
            let times = |side: &Node| made(g, TIMES, vec![c.clone(), side.clone()]);
            sides(rel, &times(&above.left), &times(&above.right))
        }
        // An equation's sides swapped, or an order turned round: `a > 0` to
        // `0 < a`.
        (RowReason::Restate, _) => row.says_as_written(&above.turned(), known),
        (RowReason::Weakening, _) => {
            let weaker = matches!(
                (above.rel, row.rel),
                (Rel::Lt, Rel::Le)
                    | (Rel::Gt, Rel::Ge)
                    | (Rel::Eq, Rel::Le)
                    | (Rel::Eq, Rel::Ge)
                    | (Rel::Lt, Rel::Ne)
                    | (Rel::Gt, Rel::Ne)
            );
            weaker
                && known.alike(&row.left, &above.left)
                && known.alike(&row.right, &above.right)
        }
        (RowReason::Algebra, _) => sides(above.rel, &above.left, &above.right),
        _ => false,
    }
}

/// Whether `row` relates by `rel` two sides that are `left` and `right`,
/// each as one number (`one_number`), written that way round: an
/// equation's sides swapped, or an order turned round, is a `restate` row
/// of its own.
pub(super) fn row_is(
    row: &Related,
    rel: Rel,
    left: &Node,
    right: &Node,
    known: &Known,
    targets: &Targets,
) -> bool {
    row.rel == rel
        && one_number(&row.left, left, known, targets)
        && one_number(&row.right, right, known, targets)
}

/// What a row names, said in a message: `with 2·A added to both sides`.
pub(super) fn row_said(reason: &RowReason) -> String {
    match reason {
        RowReason::Cited(r) => format!("as {r} says it"),
        RowReason::Adding(t) => format!("with {t} added to both sides"),
        RowReason::Multiplying(c) => {
            format!("with both sides multiplied by {c}, a numeral other than 0")
        }
        RowReason::Restate => "with its two sides swapped".to_string(),
        RowReason::Weakening => "with its relation weakened".to_string(),
        RowReason::Algebra => {
            "with a side written as the same number another way".to_string()
        }
    }
}

/// An `inequalities` step's rows (`METHODS.md`, inequalities, Rows): each
/// a single relation, read through the tree reader; the first the line the
/// step cites, written out; each after it the row above with the
/// manipulation its reason names, its atoms real as a step's are; and the
/// last the claim, written either way round.
pub fn check_inequality_rows(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in &thm.steps {
        let Some(cut) = rows(&step.just, &thm.path) else {
            continue;
        };
        let number = &step.number;
        let written = match cut {
            Ok(written) => written,
            Err(defect) => {
                report.problems.push(defect);
                continue;
            }
        };
        let mut read: Vec<Related> = Vec::new();
        for row in &written {
            let node = match row.formula.formula().and_then(|s| known.parse(&s)) {
                Ok(node) => node,
                Err(problem) => {
                    report.problems.push(problem);
                    break;
                }
            };
            let Some(related) = Related::of(&node) else {
                report.say(
                    &thm.path,
                    row.line,
                    format!("a row of step {number} is no single relation of =, ≠, <, ≤, > or ≥"),
                );
                break;
            };
            read.push(related);
        }
        if read.len() != written.len() {
            continue;
        }
        // The first row writes out the line it cites, the step's only one,
        // or one of the relations a line saying several says.
        let cited_lines = match &written[0].reason {
            RowReason::Cited(r) => line_relations(step, r, known),
            _ => Vec::new(),
        };
        // A relation the line says without writing it has no written
        // orientation, and the row may write it either way round
        // (`METHODS.md`, inequalities).
        if !cited_lines.iter().any(|line| {
            line.says_as_written(&read[0], known)
                || (!line.written && line.says(&read[0], known))
        }) {
            // The line turned round is a restate row after it, not the
            // first row (`METHODS.md`, inequalities, Rows).
            let turned = cited_lines.iter().any(|line| line.says(&read[0], known));
            let said = if turned {
                format!(
                    "the first row of step {number} is the line it cites turned round; write the line as it is written, and turn it with a restate row"
                )
            } else {
                format!(
                    "the first row of step {number} is not a line the step cites, written out with its label as its reason"
                )
            };
            report.say(&thm.path, written[0].line, said);
            continue;
        }
        let whole_cited: Vec<Node> = match &written[0].reason {
            RowReason::Cited(r) => cited_says(step, r, known),
            _ => Vec::new(),
        };
        let mut held = true;
        for (i, row) in written.iter().enumerate().skip(1) {
            let term = match &row.reason {
                RowReason::Adding(t) | RowReason::Multiplying(t) => {
                    match reason_term(t, known) {
                        Ok(node) => Some(node),
                        Err(problem) => {
                            report.problems.push(problem);
                            held = false;
                            break;
                        }
                    }
                }
                _ => None,
            };
            if !row_follows(
                &read[i - 1],
                &read[i],
                &row.reason,
                term.as_ref(),
                known,
                targets,
            ) {
                // The manipulation and a turn are two rows, the turn a
                // restate row of its own.
                let turned = !matches!(row.reason, RowReason::Restate)
                    && row_follows(
                        &read[i - 1],
                        &read[i].turned(),
                        &row.reason,
                        term.as_ref(),
                        known,
                        targets,
                    );
                let said = if turned {
                    format!(
                        "a row of step {number} is the row above {}, turned round; turning it round is a restate row of its own",
                        row_said(&row.reason)
                    )
                } else {
                    format!(
                        "a row of step {number} is not the row above {}",
                        row_said(&row.reason)
                    )
                };
                report.say(&thm.path, row.line, said);
                held = false;
                break;
            }
            // What the cited line says besides the relation the rows start
            // from, `x ∈ ℝ. x > 0.`, says it of every row.
            let relations = [read[i].said.clone(), read[i - 1].said.clone()];
            let mut lines = vec![relations[1].clone()];
            lines.extend(whole_cited.iter().cloned());
            let line_of = vec![0; lines.len()];
            let pair = ClosureRead::new(relations[0].clone(), lines, line_of);
            if let Some(said) = real_unsaid(
                &ClosureClaim::step(step),
                &pair,
                &relations,
                known,
                targets,
            ) {
                report.say(&thm.path, row.line, said);
                held = false;
                break;
            }
        }
        let Some(claim) = known.whole_as_written(&step.claim) else {
            continue; // `check_formulas` says it does not read
        };
        let last = read.last().expect("a step's rows");
        let claimed = Related::of(&claim);
        if held
            && !claimed
                .as_ref()
                .is_some_and(|c| c.says_as_written(last, known))
        {
            let said = if claimed.is_some_and(|c| c.says(last, known)) {
                format!(
                    "the last row of step {number} is its claim turned round; end with a restate row that writes the claim as it is written"
                )
            } else {
                format!("the last row of step {number} is not its claim")
            };
            report.say(&thm.path, written[written.len() - 1].line, said);
        }
    }
}

/// A requires line naming one manipulation, `requires q ≠ 0: weakening,
/// from 2.1` (`METHODS.md`, inequalities, Rows): its fact is the one line it
/// cites with that manipulation, as a row is of the row above, and its
/// atoms are real.
pub fn check_requires_manipulations(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in &thm.steps {
        for req in &step.requires {
            let Ok(by) = &req.by else {
                continue;
            };
            let Head::Manipulation(made) = &by.head else {
                continue;
            };
            // One that does not name its one line is `check_reason`'s.
            let [cited] = req.lines() else {
                continue;
            };
            let cited = cited.clone();
            let reason = made.as_row(&thm.path, req.line);
            let said = line_relations(step, &cited, known);
            let fact = known
                .whole_as_written(&req.fact)
                .and_then(|n| Related::of(&n));
            let term = match &reason {
                RowReason::Adding(t) | RowReason::Multiplying(t) => {
                    match reason_term(&t.clone(), known) {
                        Ok(node) => Some(node),
                        Err(problem) => {
                            report.problems.push(problem);
                            continue;
                        }
                    }
                }
                _ => None,
            };
            // The fact is the line with the one manipulation, written the way
            // round the manipulation leaves it. Of a line saying several
            // relations, it is one of them manipulated.
            let line = fact.as_ref().and_then(|fact| {
                said.iter()
                    .find(|line| {
                        row_follows(line, fact, &reason, term.as_ref(), known, targets)
                    })
                    .cloned()
            });
            if line.is_none() {
                // The manipulation and a turn are two, and a requires line
                // names one (`METHODS.md`, inequalities, Rows).
                let turned = fact.as_ref().map(Related::turned).filter(|turned| {
                    !matches!(reason, RowReason::Restate)
                        && said.iter().any(|line| {
                            row_follows(
                                line,
                                turned,
                                &reason,
                                term.as_ref(),
                                known,
                                targets,
                            )
                        })
                });
                let message = if let Some(t) = turned {
                    format!(
                        "the requires line {} of {} is {cited} {}, turned round; a requires line names one manipulation, so write it as the manipulation leaves it: {} {} {}",
                        str::trim(req.fact.text()),
                        step.called(),
                        row_said(&reason),
                        known.print(&t.left),
                        sign(t.rel),
                        known.print(&t.right)
                    )
                } else {
                    format!(
                        "the requires line {} of {} is not {cited} {}",
                        str::trim(req.fact.text()),
                        step.called(),
                        row_said(&reason)
                    )
                };
                report.say(&thm.path, req.line, message);
                continue;
            }
            let (Some(line), Some(fact)) = (line, fact) else {
                continue;
            };
            let relations = [fact.said.clone(), line.said.clone()];
            let at = ClosureClaim::requires(step, req);
            let Some(read) = at.read(known, targets, false) else {
                continue;
            };
            let Some(unsaid) = unsaid_of(&at, &read, &relations, known, targets) else {
                continue;
            };
            // A requires line takes what the lines above it state (`SYNTAX.md`),
            // so a line below that would say it is named, read as if above.
            let below = step
                .requires
                .iter()
                .skip_while(|o| o.line != req.line)
                .skip(1)
                .find(|o| {
                    let mut with = ClosureClaim::requires(step, req);
                    with.above.push(o);
                    with.read(known, targets, false).is_some_and(|read| {
                        unsaid_of(&with, &read, &relations, known, targets)
                            .is_none_or(|still| !still.same(&unsaid, known))
                    })
                });
            let said = unsaid.said(known);
            let message = match (below, &unsaid) {
                (Some(o), _) => format!(
                    "{}; the requires line {} below says it, and a requires line takes only what the lines above it state: move it above",
                    unsaid.told(known, "nothing above says"),
                    str::trim(o.fact.text())
                ),
                (None, Unsaid::Real(_)) => format!(
                    "{said}; a requires line by {} takes a membership from a requires line above it",
                    by.head
                ),
                (None, Unsaid::Nonzero(_)) => said,
            };
            report.say(&thm.path, req.line, message);
        }
    }
}

/// How the page writes a relation.
pub(super) fn sign(rel: Rel) -> &'static str {
    match rel {
        Rel::Eq => "=",
        Rel::Ne => "≠",
        Rel::Lt => "<",
        Rel::Le => "≤",
        Rel::Gt => ">",
        Rel::Ge => "≥",
    }
}

/// Reports an atom of the claim or of `links` that nothing says is real
/// (`real_unsaid`).
pub(super) fn report_unreal(
    report: &mut Report,
    thm: &Theorem,
    step: &Step,
    claim: &Node,
    links: &[Related],
    known: &Known,
    targets: &Targets,
) {
    let relations: Vec<Node> = iter::once(claim.clone())
        .chain(links.iter().map(|l| l.said.clone()))
        .collect();
    // A cited line says all it says, not only the relation the chain takes
    // from it: `δ ∈ ℝ. δ > 0.` says δ is real.
    let mut lines = relations[1..].to_vec();
    let mut line_of: Vec<usize> = (0..links.len()).collect();
    for (i, r) in step.just.refs.iter().enumerate() {
        for said in cited_says(step, r, known) {
            lines.push(said);
            line_of.push(i);
        }
    }
    let read = ClosureRead::new(claim.clone(), lines, line_of);
    // The cited lines are the orders the step links, so a membership is
    // taken from a requires line (`METHODS.md`, transitivity, antisymmetry).
    if let Some(said) =
        real_unsaid(&ClosureClaim::step(step), &read, &relations, known, targets)
    {
        report.say(
            &thm.path,
            step.just.line,
            format!(
                "{said}; {} takes a membership from a requires line",
                step.just.head
            ),
        );
    }
}

/// The two sides of an equation, an order or a disequality; none for
/// anything else.
pub(super) fn relation_sides(node: &Node) -> Vec<&Node> {
    match (node.notation(), node.children.as_slice()) {
        (EQUALITY | ORDER, [a, b]) => vec![a, b],
        (LOGICAL_NOT, [inner]) => relation_sides(inner),
        _ => Vec::new(),
    }
}

/// Whether a sentence is an equation or a disequality, what `algebra`
/// combines.
pub(super) fn algebra_relation(node: &Node) -> bool {
    match (node.notation(), node.children.as_slice()) {
        (EQUALITY, [_, _]) => true,
        (LOGICAL_NOT, [inner]) => inner.notation() == EQUALITY,
        _ => false,
    }
}

/// What a side of a relation `algebra` asks to be numbers: a pair's two
/// coordinates (`METHODS.md`, Pairs), or the side itself.
pub(super) fn coordinates_of<'n>(side: &'n Node, targets: &Targets) -> Vec<&'n Node> {
    if term_of_node(side, targets).label() == Some("cop") {
        side.children.iter().collect()
    } else {
        vec![side]
    }
}

/// The two sides of an equation or a disequality; none for anything else.
pub(super) fn sides_of(node: &Node) -> Vec<&Node> {
    match (node.notation(), node.children.as_slice()) {
        (EQUALITY, [a, b]) => vec![a, b],
        (LOGICAL_NOT, [inner]) => sides_of(inner),
        _ => Vec::new(),
    }
}

/// What `inequalities` claims holds (`METHODS.md`, inequalities): a step's
/// claim of one sentence follows by linear arithmetic from what the lines it
/// cites say and the bounds a membership among them implies
/// (`methods::inequalities::decide`), each read as `check_algebra_holds`
/// reads it; and a requires line's whose reason is `inequalities`.
pub fn check_inequalities_holds(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in &thm.steps {
        // A step with rows is its rows' (`check_inequality_rows`).
        if step.just.head.is(Method::Inequalities) && step.just.rows.is_empty() {
            let at = ClosureClaim::step(step);
            if !inequalities_hold(report, thm, &at, known, targets) {
                report.undecided(&thm.path, Method::Inequalities, step);
            }
        }
        for req in step.requires.iter().filter(|r| r.is(Method::Inequalities)) {
            let at = ClosureClaim::requires(step, req);
            if !inequalities_hold(report, thm, &at, known, targets) {
                report.undecided_requires(&thm.path, Method::Inequalities, step, req);
            }
        }
    }
}

/// A requires line of an algebra, arithmetic or inequalities step saying a
/// membership says it of a term the step combines (`SYNTAX.md`, requires):
/// one in its claim, in a line it cites, or in another of its requires
/// lines, which may ask it. A membership of a term found in none of them is
/// a line the step neither uses nor asks for.
pub fn check_requires_combined(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in &thm.steps {
        let head = &step.just.head;
        if !(head.is(Method::Algebra)
            || head.is(Method::Arithmetic)
            || head.is(Method::Inequalities))
        {
            continue;
        }
        let Some(read) = ClosureClaim::step(step).read(known, targets, true) else {
            continue;
        };
        let mut combined: Vec<Node> = vec![read.claimed];
        combined.extend(read.lines);
        combined.extend(known.whole(step, &step.claim));
        let scope = known.scope(step);
        combined.extend(
            step.just
                .refs
                .iter()
                .filter_map(|r| scope.get(r))
                .flat_map(|s| known.writes(s, &known.citing_step(step))),
        );
        let said: Vec<Option<Node>> = step
            .requires
            .iter()
            .map(|r| known.whole(step, &r.fact))
            .collect();
        for (i, req) in step.requires.iter().enumerate() {
            let Some(fact) = &said[i] else {
                continue;
            };
            let (MEMBERSHIP, [term, _]) = (fact.notation(), fact.children.as_slice())
            else {
                continue;
            };
            let others = said
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .filter_map(|(_, o)| o.as_ref());
            let found = combined
                .iter()
                .chain(others)
                .any(|tree| tree.walk().iter().any(|n| known.alike(n, term)));
            if !found {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of {} says {}, and the {} neither uses nor asks for it",
                        step.called(),
                        str::trim(req.fact.text()),
                        step.kind_word()
                    ),
                );
            }
        }
    }
}

/// How a closure method decides a claim (`algebra_holds` and the like):
/// whether it decided, reporting what it refuses.
pub(super) type Decides =
    fn(&mut Report, &Theorem, &ClosureClaim, &Known, &Targets) -> bool;

/// A `let` saying what kind of number its name is shows it by its reason,
/// as a requires line of the step after it would (`SYNTAX.md`, a let with a
/// kind; `citations::check_kinds` for a reason citing an item): where the
/// reason is a method, the method decides `gcd(s, w) ∈ ℕ`, and a reason it
/// does not decide, or that leaves a hypothesis unsaid, is reported.
pub fn check_kind_methods(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for UnderLet {
        define: d,
        step: under,
    } in reasons_under_lets(thm, known)
    {
        let Some(shown) = under.requires.last() else {
            continue;
        };
        if shown.is(Method::Arithmetic) {
            if let Some(why) = arithmetic_unshown(&shown.fact, known, targets) {
                report.say(
                    &thm.path,
                    d.line,
                    format!(
                        "the reason under let {} does not show {}: arithmetic finds it {why}",
                        d.label,
                        str::trim(shown.fact.text())
                    ),
                );
            }
            continue;
        }
        let decides: Decides = if shown.is(Method::Membership) {
            membership_holds
        } else if shown.is(Method::Algebra) {
            algebra_holds
        } else if shown.is(Method::Inequalities) {
            inequalities_hold
        } else {
            continue;
        };
        let mut scratch = Report::default();
        let at = ClosureClaim::requires(&under, shown);
        let decided = decides(&mut scratch, thm, &at, known, targets);
        let why = match scratch.problems.first() {
            Some(problem) => problem.message.clone(),
            None if !decided => "its method does not decide it".to_string(),
            None => continue,
        };
        report.say(
            &thm.path,
            d.line,
            format!(
                "the reason under let {} does not show {}: {why}",
                d.label,
                str::trim(shown.fact.text())
            ),
        );
    }
}

/// A let saying what kind of number its name is, and the step below it
/// with the let's requires lines and then its reason as its requires lines,
/// which is how the reason is read (`SYNTAX.md`, a let with a kind). The
/// reason is the last.
pub struct UnderLet<'t> {
    pub define: &'t DefineLine,
    pub step: Step,
}

/// The theorem's lets that say a kind, each with its reason read as a
/// requires line of the step after it (`UnderLet`); a let with no step
/// after it is reported by the reader.
pub fn reasons_under_lets<'t>(thm: &'t Theorem, known: &Known) -> Vec<UnderLet<'t>> {
    thm.defines
        .iter()
        .filter_map(|d| {
            let Ok(Some(kinded)) = d.kinded(&thm.path, &known.env.g.members) else {
                return None;
            };
            let after = thm.step_after(d.line)?;
            let reason = d.reason.as_ref()?;
            Some(UnderLet {
                define: d,
                step: reason.under(&d.label, after, kinded.shown.fact.clone()),
            })
        })
        .collect()
}

/// What a method step's lines are asked against: how its method decides,
/// and the defines of functions the theorem may apply.
pub(super) struct CitesAsked<'a> {
    pub(super) decides: Decides,
    pub(super) functions: &'a [super::super::citations::Defined],
    pub(super) library: &'a Library<'a>,
    pub(super) targets: &'a Targets,
}

impl CitesAsked<'_> {
    /// Whether `step` holds citing `refs` in place of its lines: its method
    /// decides it with nothing refused, and each define it applies has its
    /// argument in its domain by what it cites (`check_define_domains`).
    pub(super) fn holds_citing(
        &self,
        thm: &Theorem,
        step: &Step,
        refs: &[String],
        known: &Known,
    ) -> bool {
        let mut lighter = step.clone();
        lighter.just.refs = refs.to_vec();
        self.holds(thm, &lighter, known)
    }

    /// Whether `lighter`, a step with something of it taken away, holds:
    /// its method decides it with nothing refused, and each define it
    /// applies has its argument in its domain.
    pub(super) fn holds(&self, thm: &Theorem, lighter: &Step, known: &Known) -> bool {
        let mut scratch = Report::default();
        let decided = (self.decides)(
            &mut scratch,
            thm,
            &ClosureClaim::step(lighter),
            known,
            self.targets,
        );
        decided
            && scratch.problems.is_empty()
            && super::super::citations::domains_unsaid(
                lighter,
                self.functions,
                known,
                self.library,
            )
            .is_empty()
    }
}

/// A step resting on a closure method uses each line it cites, as a step
/// citing an item does (`check_surplus`; `DATABASE.md`, a named thing doing
/// no work is an error): with the line taken away, the method no longer
/// decides the claim, or a hypothesis of it, an atom's membership, a
/// divisor's `≠ 0` or a define's argument in its domain, is left unsaid. A
/// step that does not hold with all its lines is reported where the method
/// is checked, and asked nothing here. A step with rows cites the one line
/// its first row is.
pub fn check_method_cites_used(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let functions =
        super::super::citations::defined_functions(&proof::in_scope(thm, scopes));
    for step in &thm.steps {
        let decides: Decides = match step.just.head.method() {
            Some(Method::Algebra) => algebra_holds,
            Some(Method::Inequalities) if step.just.rows.is_empty() => {
                inequalities_hold
            }
            Some(Method::Membership) => membership_holds,
            Some(Method::Inspection) => inspection_holds,
            _ => continue,
        };
        let asked = CitesAsked {
            decides,
            functions: &functions,
            library,
            targets: &library.targets,
        };
        let refs = &step.just.refs;
        if !asked.holds(thm, step, known) {
            continue;
        }
        let mut seen = BTreeSet::new();
        for r in refs.iter().filter(|r| seen.insert(r.as_str())) {
            let without: Vec<String> =
                refs.iter().filter(|x| *x != r).cloned().collect();
            // A define the step cites may be what reads the line it
            // contradicts, `contradicting 1` where line 1 says e ≠ 0 and the
            // claim says it of what e names.
            if reads_contradicted(step, &without, library, known) {
                continue;
            }
            if asked.holds_citing(thm, step, &without, known) {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!("step {} cites {r} and uses nothing it says", step.number),
                );
            }
        }
        // A requires line other than a membership, `x ≠ 0` or an order,
        // does work in the same sense; a membership is
        // `check_requires_combined`'s. A requires line rests on those above
        // it (`SYNTAX.md`), so only the last is asked here: one above it is
        // what the elaborator judges by what the lines below rest on.
        for (i, req) in step.requires.iter().enumerate() {
            let membership = known
                .whole(step, &req.fact)
                .is_some_and(|n| n.notation() == MEMBERSHIP);
            if i + 1 != step.requires.len() || membership {
                continue;
            }
            let mut lighter = step.clone();
            lighter.requires.remove(i);
            if asked.holds(thm, &lighter, known) {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of {} says {}, and the {} neither uses nor asks for it",
                        step.called(),
                        str::trim(req.fact.text()),
                        step.kind_word()
                    ),
                );
            }
        }
    }
}

/// `check_inequalities_holds` of one claim; whether it was decided.
pub(super) fn inequalities_hold(
    report: &mut Report,
    thm: &Theorem,
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> bool {
    let Some(mut read) = at.read(known, targets, false) else {
        return false;
    };
    read.read_at_member(known);
    let labels = FloatLabels::new(IndexMap::new());
    let implied: Vec<Term> = read
        .lines
        .iter()
        .flat_map(conjuncts)
        .flat_map(|part| implied_facts(&part, known.env, &known.sorts))
        .chain(read.member_implies(known))
        .map(|n| term_of_node(&n, targets))
        .collect();
    let cited: Vec<Term> = read
        .lines
        .iter()
        .map(|n| term_of_node(n, targets))
        .collect();
    let claimed = term_of_node(&read.claimed, targets);
    match inequalities::decide(&claimed, &cited, &implied, &labels) {
        Some(true) => {
            if let Some(said) = inequalities_unsaid(at, &read, known, targets) {
                report.say(&thm.path, at.line, at.said(said));
            }
            true
        }
        Some(false) => {
            let step = at.step.called();
            let said = inequalities::refusal(
                &at.claim.to_string(),
                &step,
                &claimed,
                &cited,
                &implied,
                &labels,
            );
            report.say(&thm.path, at.line, at.said(said));
            true
        }
        None => false,
    }
}

/// What `inspection` claims holds (`METHODS.md`, inspection): a claim about
/// sets listed in full, checked element by element against what the lines
/// the step cites say (`methods::inspection`), each sentence a kernel term.
/// One the facts show false is refused; one they settle neither way is left
/// to the build, and counted.
pub fn check_inspection_holds(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in &thm.steps {
        if !step.just.head.is(Method::Inspection) {
            continue;
        }
        // A claim that does not read is `check_formulas`'s to report.
        if known.whole(step, &step.claim).is_none() {
            continue;
        }
        if !inspection_holds(report, thm, &ClosureClaim::step(step), known, targets) {
            report.undecided(&thm.path, Method::Inspection, step);
        }
    }
}

/// `check_inspection_holds` of one claim, from the lines it cites; whether
/// it was decided.
pub(super) fn inspection_holds(
    report: &mut Report,
    thm: &Theorem,
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> bool {
    let Some(claim) = known.whole(at.step, at.claim) else {
        return false;
    };
    let scope = known.scope(at.step);
    let cited: Vec<Term> = at
        .refs
        .iter()
        .filter_map(|r| scope.get(r))
        .flat_map(|stated| known.supplied(stated, &known.citing_step(at.step)))
        .map(|n| term_of_node(&n, targets))
        .collect();
    let what = format!("step {} claims {}", at.step.number, known.print(&claim));
    match Facts::of(&cited).decide(&term_of_node(&claim, targets)) {
        Inspected::Holds => true,
        Inspected::Fails => {
            report.say(
                &thm.path,
                at.line,
                format!("{what}, which inspection of what it cites shows false"),
            );
            true
        }
        Inspected::Unsettled(why) => {
            report.say(&thm.path, at.line, format!("{what}, and {why}"));
            true
        }
        Inspected::Undecided => false,
    }
}

/// What `membership` claims holds (`METHODS.md`, membership): a step's claim
/// `t ∈ S`, or `for all k ∈ X, t ∈ S` at a member of X, and a requires
/// line's whose reason is `membership`, each decided by
/// `methods::membership::holds` from what the lines it cites say, the
/// requires lines above it, what a membership among them implies, and the
/// memberships the page says once.
pub fn check_membership_holds(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in &thm.steps {
        if step.just.head.is(Method::Membership) {
            let at = ClosureClaim::step(step);
            // A claim of no shape the method decides is refused once, by
            // `check_membership_claims`, which says why.
            if !membership_holds(report, thm, &at, known, targets)
                && membership_claim_refused(step, known).is_none()
            {
                report.undecided(&thm.path, Method::Membership, step);
            }
        }
        for req in step.requires.iter().filter(|r| r.is(Method::Membership)) {
            let at = ClosureClaim::requires(step, req);
            if !membership_holds(report, thm, &at, known, targets) {
                report.undecided_requires(&thm.path, Method::Membership, step, req);
            }
        }
    }
}

/// The claims the `membership` method proves whose term is in its system
/// beside an equation a line they name says, each by the line its reason
/// is on (`CheckedTheorem::members_shown`): how the check found the term
/// there, which a backend proves the same way.
pub fn members_shown(
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) -> IndexMap<usize, super::super::record::PlaceShown> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        if step.just.head.is(Method::Membership) {
            let at = ClosureClaim::step(step);
            if let Some(shown) = member_beside(&at, known, targets) {
                out.insert(step.just.line, shown);
            }
        }
        for req in step.requires.iter().filter(|r| r.is(Method::Membership)) {
            let (at, Ok(by)) = (ClosureClaim::requires(step, req), &req.by) else {
                continue;
            };
            if let Some(shown) = member_beside(&at, known, targets) {
                out.insert(by.line, shown);
            }
        }
    }
    out
}

/// The claims `inspection` decides hold, a step's and each requires line's
/// whose reason is the method, each by the line its reason is on, with the
/// case that decided it (`CheckedTheorem::inspected`).
pub fn inspected(
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) -> IndexMap<usize, super::super::record::Inspection> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        if step.just.head.is(Method::Inspection) {
            if let Some(how) =
                inspection_case(&ClosureClaim::step(step), known, targets)
            {
                out.insert(step.just.line, how);
            }
        }
        for req in step.requires.iter().filter(|r| r.is(Method::Inspection)) {
            let (at, Ok(by)) = (ClosureClaim::requires(step, req), &req.by) else {
                continue;
            };
            if let Some(how) = inspection_case(&at, known, targets) {
                out.insert(by.line, how);
            }
        }
    }
    out
}

/// The case of `inspection` that decides one claim from the lines it
/// cites, as `inspection_holds` reads them; None where it does not hold.
pub(super) fn inspection_case(
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> Option<super::super::record::Inspection> {
    let claim = known.whole(at.step, at.claim)?;
    let scope = known.scope(at.step);
    let defined = known.citing_step(at.step);
    // Each cited sentence beside the reference it is read from.
    let mut cited: Vec<Term> = Vec::new();
    let mut from: Vec<&String> = Vec::new();
    for r in at.refs {
        let Some(stated) = scope.get(r) else {
            continue;
        };
        for n in known.supplied(stated, &defined) {
            cited.push(term_of_node(&n, targets));
            from.push(r);
        }
    }
    Some(
        match Facts::of(&cited).case(&term_of_node(&claim, targets))? {
            inspection::Case::OneOf { fact, range } => Inspection::OneOf {
                from: from.get(fact)?.to_string(),
                range,
            },
            inspection::Case::Prime => Inspection::Prime,
            inspection::Case::Empty => Inspection::Empty,
            inspection::Case::Member => Inspection::Member,
            inspection::Case::Size => Inspection::Size,
            inspection::Case::TakenSize { kept } => Inspection::TakenSize { kept },
            inspection::Case::Taken { kept } => Inspection::Taken { kept },
            inspection::Case::Other => Inspection::Other,
        },
    )
}

/// The parts each reason's lines put in a number system, by the line the
/// reason is on (`CheckedTheorem::held_by_lines`): of a step's claim and the
/// lines it names, and of each requires line and the lines its own reason
/// names, read as the `membership` method reads what a claim rests on
/// (`MembershipIn`, `methods::membership::held_otherwise`).
pub fn held_by_lines(
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) -> IndexMap<usize, Vec<super::super::record::HeldByLines>> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        let at = ClosureClaim::step(step);
        // An inequalities step with rows writes in its rows what it combines.
        let rows: Vec<Node> = match proof::rows(&step.just, &thm.path) {
            Some(Ok(rows)) => rows
                .iter()
                .filter_map(|r| r.formula.formula().ok())
                .filter_map(|s| known.parse(&s).ok())
                .collect(),
            _ => Vec::new(),
        };
        out.insert(step.just.line, held_at_with(&at, &rows, known, targets));
        for req in &step.requires {
            if let Ok(by) = &req.by {
                let at = ClosureClaim::requires(step, req);
                out.insert(by.line, held_at(&at, known, targets));
            }
        }
        // A calculation's rows and a substitution's, each by the line its
        // reason is on, read as the requires line it is.
        let substituted: Vec<Requires> =
            match proof::substitute_rows(&step.just, &thm.path) {
                Some(Ok(rows)) => rows.into_iter().filter_map(|r| r.reason).collect(),
                _ => Vec::new(),
            };
        let reasons: Vec<Requires> = chain_links(&step.just, &thm.path)
            .into_iter()
            .filter_map(|link| link.line.reason)
            .chain(substituted)
            .collect();
        for req in &reasons {
            if let Ok(by) = &req.by {
                let at = ClosureClaim::row(step, req);
                out.insert(by.line, held_at(&at, known, targets));
            }
        }
    }
    // The reason under a define that says a kind, read as the requires line
    // it is checked as, under the step after the define
    // (`citations::check_kinds`, `Reason::under`).
    for d in &thm.defines {
        let Ok(Some(kinded)) = d.kinded(&thm.path, &known.env.g.members) else {
            continue;
        };
        let (Some(after), Some(reason)) = (thm.step_after(d.line), d.reason.as_ref())
        else {
            continue;
        };
        let under = reason.under(&d.label, after, kinded.shown.fact.clone());
        let Some(req) = under.requires.last() else {
            continue;
        };
        if let Ok(by) = &req.by {
            let at = ClosureClaim::requires(&under, req);
            out.insert(by.line, held_at(&at, known, targets));
        }
    }
    out
}

/// The notations whose parts stand in no order that each reason's claim and
/// lines write in more than one order, by the line the reason is on
/// (`CheckedTheorem::commuted_by_lines`): of a step's claim and the lines it
/// names, and of each requires line and the lines its own reason names.
pub fn commuted_by_lines(
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) -> IndexMap<usize, Vec<String>> {
    let commuted = |at: &ClosureClaim| -> Vec<String> {
        let Some(read) = at.read(known, targets, true) else {
            return Vec::new();
        };
        let nodes: Vec<Node> = iter::once(read.claimed.clone())
            .chain(read.lines.iter().cloned())
            .collect();
        targets.written_in_other_orders(&nodes)
    };
    let mut out = IndexMap::new();
    for step in &thm.steps {
        out.insert(step.just.line, commuted(&ClosureClaim::step(step)));
        for req in &step.requires {
            if let Ok(by) = &req.by {
                out.insert(by.line, commuted(&ClosureClaim::requires(step, req)));
            }
        }
        // A calculation's rows and a substitution's, each by the line its
        // reason is on, the change a substitution's row makes its claim.
        let substituted: Vec<Requires> =
            match proof::substitute_rows(&step.just, &thm.path) {
                Some(Ok(rows)) => rows.into_iter().filter_map(|r| r.reason).collect(),
                _ => Vec::new(),
            };
        let rows: Vec<Requires> = chain_links(&step.just, &thm.path)
            .into_iter()
            .filter_map(|link| link.line.reason)
            .chain(substituted)
            .collect();
        for req in &rows {
            if let Ok(by) = &req.by {
                out.insert(by.line, commuted(&ClosureClaim::row(step, req)));
            }
        }
    }
    out
}

/// The number systems a part may be asked in: ℂ too, where Metamath proves
/// a term complex for each lemma of arithmetic it applies.
pub(super) const HELD_IN: [System; 6] = [
    System::N,
    System::N0,
    System::Z,
    System::Q,
    System::R,
    System::C,
];

/// `held_by_lines` of one claim: every part of its terms and of its lines'
/// that those lines put in a system, once for each system, with how.
pub(super) fn held_at(
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> Vec<super::super::record::HeldByLines> {
    held_at_with(at, &[], known, targets)
}

/// `held_at`, of the terms `more` writes as well: an inequalities step's
/// rows.
fn held_at_with(
    at: &ClosureClaim,
    more: &[Node],
    known: &Known,
    targets: &Targets,
) -> Vec<super::super::record::HeldByLines> {
    let Some(read) = at.read(known, targets, true) else {
        return Vec::new();
    };
    let mut held = MembershipIn::of(at, &read, known);
    // A claim said of every member is read at a member, as
    // `membership_holds` decides it: its letter in the set's system.
    if let (FOR_ALL, [bound, set, _]) =
        (read.claimed.notation(), read.claimed.children.as_slice())
    {
        member_of(bound, set, &mut held.letters, &mut held.ranged);
    }
    let given = held.given(targets, known);
    let mut out: Vec<HeldByLines> = Vec::new();
    let mut seen: FxIndexSet<(ByShape, System)> = FxIndexSet::default();
    // The claim and what the reason rests on as its check reads it, the
    // step's own requires lines among them (`MembershipIn::stated`).
    let stated = held.stated.clone();
    for part in iter::once(&read.claimed)
        .chain(&read.lines)
        .chain(&stated)
        .chain(more)
        .flat_map(|n| n.walk())
    {
        if part.notation() == NUMERAL {
            continue;
        }
        for system in HELD_IN {
            if !seen.insert((part.by_shape(), system)) {
                continue;
            }
            let Some(shown) = methods_membership::held_shown(&part, system, &given)
            else {
                continue;
            };
            out.push(HeldByLines {
                term: part.clone(),
                system,
                shown,
            });
        }
    }
    out
}

/// Of a claim `t ∈ S` the `membership` method proves, how t is in S where
/// an equation among what it rests on puts t beside a term in S
/// (`methods::membership::shown`, `Besides::of`); None where t is said, or the
/// claim is of another shape.
pub(super) fn member_beside(
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> Option<super::super::record::PlaceShown> {
    let read = at.read(known, targets, true)?;
    let mut held = MembershipIn::of(at, &read, known);
    // A claim said of every member is read at a member, as
    // `membership_holds` decides it.
    // The claim as the page writes it, no define written out.
    let as_page = match at.claim.sentences().as_slice() {
        [one] => known.read_as_written(one),
        _ => None,
    };
    let (claimed, written) = match (
        read.claimed.notation(),
        read.claimed.children.as_slice(),
        as_page,
    ) {
        (FOR_ALL, [bound, set, body], written) => {
            if !member_of(bound, set, &mut held.letters, &mut held.ranged) {
                return None;
            }
            let written =
                written.and_then(|w| match (w.notation(), w.children.as_slice()) {
                    (FOR_ALL, [_, _, b]) => Some(b.clone()),
                    _ => None,
                });
            (body.clone(), written)
        }
        (_, _, written) => (read.claimed.clone(), written),
    };
    let (MEMBERSHIP, [term, set]) = (claimed.notation(), claimed.children.as_slice())
    else {
        return None;
    };
    let system = (set.notation() == NUMBER_SYSTEMS)
        .then(|| System::of_sign(&set.text))
        .flatten()?;
    let given = held.given(targets, known);
    let shown = |by| {
        Some(PlaceShown {
            term: term.clone(),
            system,
            by,
        })
    };
    if let Some(b) = methods_membership::shown(term, system, &given)
        .and_then(|s| super::super::record::Besides::of(&s))
    {
        return shown(ShownBy::Beside(b));
    }
    // A term a cited define writes out, read as its value.
    let as_written =
        written.and_then(|w| match (w.notation(), w.children.as_slice()) {
            (MEMBERSHIP, [t, _]) => Some(t.clone()),
            _ => None,
        });
    if as_written.is_some_and(|w| !known.alike(&w, term)) {
        return shown(ShownBy::Define {
            value: term.clone(),
        });
    }
    // A function's value by its type.
    if let Some(map) = methods_membership::value_typed_by(term, system, &given) {
        if let [_, point] = term.children.as_slice() {
            return shown(ShownBy::Typed {
                map: map.clone(),
                at: point.clone(),
            });
        }
    }
    None
}

/// `check_membership_holds` of one claim; whether it was decided.
pub(super) fn membership_holds(
    report: &mut Report,
    thm: &Theorem,
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> bool {
    let Some(read) = at.read(known, targets, true) else {
        return false;
    };
    let mut held = MembershipIn::of(at, &read, known);
    // A claim said of every member is decided at a member.
    let mut claimed = read.claimed.clone();
    if let (FOR_ALL, [bound, set, body]) =
        (claimed.notation(), claimed.children.as_slice())
    {
        if !member_of(bound, set, &mut held.letters, &mut held.ranged) {
            return false;
        }
        claimed = body.clone();
    }
    let (MEMBERSHIP, [term, set]) = (claimed.notation(), claimed.children.as_slice())
    else {
        return false;
    };
    let Some(system) = (set.notation() == NUMBER_SYSTEMS)
        .then(|| System::of_sign(&set.text))
        .flatten()
    else {
        return false;
    };
    let given = held.given(targets, known);
    if !methods_membership::holds(term, system, &given) {
        let step = at.step.called();
        // The first part the claim is built from that nothing held says is
        // a number there, through a cited equation where one carries it, or
        // a divisor nothing says is not zero.
        let parts = methods_membership::Parts::of(term);
        let unsaid = methods_membership::unsaid_atom(term, system, &given)
            .map(|a| {
                format!(
                    ": nothing says {} ∈ {}, which it needs",
                    known.print(&a),
                    known.print(set)
                )
            })
            .or_else(|| {
                parts
                    .divisors
                    .iter()
                    .find_map(|d| methods_membership::unsaid_part(d, &given))
                    .map(|d| {
                        format!(
                            ": nothing says {} ≠ 0, which it needs to divide by it",
                            known.print(&d)
                        )
                    })
            })
            .unwrap_or_default();
        let said = format!("{} is not built from what {step} cites{unsaid}", at.claim);
        report.say(&thm.path, at.line, at.said(said));
    }
    true
}

/// What a closure claim's terms are numbers by (`methods::membership`): the
/// lines it cites, the requires lines it rests on, each part of them and
/// what a membership among them implies; the letters the page puts in a
/// number system once, the member a step said of every member speaks of,
/// and the function types in scope.
pub(super) struct MembershipIn {
    pub(super) facts: Vec<Node>,
    /// The facts the lines state, of which `facts` holds these and what
    /// they imply, `x > 0` of `x ∈ ℕ` (`implied_facts`).
    pub(super) stated: Vec<Node>,
    /// Where the page writes each of `stated`, in its order; None for a
    /// line of a read `ClosureClaim::read` did not make (`MembershipIn::of`).
    pub(super) stated_in: Vec<Option<StatedIn>>,
    pub(super) letters: Introduced,
    pub(super) ranged: IndexMap<String, methods_membership::Range>,
    pub(super) typed: Vec<Node>,
    /// The function types in scope, which a sum's terms may use.
    pub(super) in_sums: Vec<Node>,
}

impl MembershipIn {
    pub(super) fn of(
        at: &ClosureClaim,
        read: &ClosureRead,
        known: &Known,
    ) -> MembershipIn {
        let mut letters = super::super::library::introduced(known, at.step);
        // A step's requires lines are among its facts in (`METHODS.md`), a
        // requires line's are the lines above it, which `read` holds.
        let mut lines = read.lines.clone();
        // Where each line is, as `ClosureClaim::read` places it (`line_of`):
        // a cited line by its reference, then a requires line above by its
        // place among those. A read made otherwise, a chain's links by
        // their place, has no such place.
        let mut sources: Vec<Option<StatedIn>> = read
            .line_of
            .iter()
            .map(|&i| match at.refs.get(i) {
                Some(r) => Some(StatedIn::Cited { line: r.clone() }),
                None => at
                    .above
                    .get(i - at.refs.len())
                    .map(|r| StatedIn::Requires { line: r.line }),
            })
            .collect();
        if at.requires.is_none() {
            let defined = known.citing_step(at.step);
            for r in &at.step.requires {
                for said in r
                    .fact
                    .sentences()
                    .iter()
                    .filter_map(|s| known.read_citing(s, &defined))
                {
                    lines.push(said);
                    sources.push(Some(StatedIn::Requires { line: r.line }));
                }
            }
        }
        // A claim said of every member of a set is decided at a member, which
        // is in that set: x ∈ [a, b] of "for all x ∈ [a, b], …", where a
        // function typed on [a, b] gives its value.
        if let (FOR_ALL, [bound, set, _]) =
            (read.claimed.notation(), read.claimed.children.as_slice())
        {
            if let Some(member) =
                page::made_as(known.env.g, "_ ∈ _", vec![bound.clone(), set.clone()])
            {
                lines.push(member);
                sources.push(Some(StatedIn::Member));
            }
        }
        // A step said of every member in one line, and its requires lines,
        // speak of the member (`SYNTAX.md`), which the step's claim puts in
        // its set.
        let mut ranged = IndexMap::new();
        if at.step.openers.is_empty() {
            if let Some(member) = known.step_member(at.step) {
                if let (MEMBERSHIP, [bound, set]) =
                    (member.notation(), member.children.as_slice())
                {
                    member_of(bound, set, &mut letters, &mut ranged);
                }
            }
        }
        let mut stated: Vec<Node> = Vec::new();
        let mut stated_in: Vec<Option<StatedIn>> = Vec::new();
        for (line, source) in lines.iter().zip(&sources) {
            for part in conjuncts(line) {
                stated.push(part);
                stated_in.push(source.clone());
            }
        }
        let mut facts = stated.clone();
        let implied: Vec<Node> = stated
            .iter()
            .flat_map(|f| implied_facts(f, known.env, &known.sorts))
            .collect();
        facts.extend(implied);
        for f in &facts {
            if let (MEMBERSHIP, [name, set]) = (f.notation(), f.children.as_slice()) {
                if let (true, Some(system)) =
                    (name.is_name(), System::of_sign(&set.text))
                {
                    letters.entry(name.text.to_string()).or_insert(system);
                }
            }
        }
        // A function's type is cited for its values (`READERS.md`): the
        // types among what the claim rests on, and none merely in scope.
        let typed: Vec<Node> = facts
            .iter()
            .filter(|f| types_a_function(f))
            .cloned()
            .collect();
        MembershipIn {
            facts,
            stated,
            stated_in,
            letters,
            ranged,
            typed,
            in_sums: super::super::library::typed_in_scope(known, at.step),
        }
    }

    /// What the decider reads.
    pub(super) fn given<'a>(
        &'a self,
        targets: &'a Targets,
        known: &'a Known,
    ) -> methods_membership::Facts<'a> {
        methods_membership::Facts {
            facts: &self.facts,
            letters: self.letters.clone(),
            ranged: self.ranged.clone(),
            typed: &self.typed,
            in_sums: &self.in_sums,
            targets,
            ctx: known.ctx,
        }
    }
}

/// The letter a "for all" binds, put in the number system its set lies in,
/// a number system, a range or an interval, and where the set is a range,
/// as running over it. Any other set, ℝ ∖ {0}, puts the letter in no
/// system: what the member is is said by the step's requires lines
/// (`SYNTAX.md`, a step said of every member). False where the letter is
/// no name.
pub(super) fn member_of(
    bound: &Node,
    set: &Node,
    letters: &mut Introduced,
    ranged: &mut IndexMap<String, methods_membership::Range>,
) -> bool {
    if !bound.is_name() {
        return false;
    }
    let system = match set.notation() {
        NUMBER_SYSTEMS => System::of_sign(&set.text),
        INTEGER_RANGE => citing::range_system(set),
        _ => match citing::interval_system(set, letters) {
            Some(system) => Some(system),
            None => return true,
        },
    };
    let Some(system) = system else {
        return false;
    };
    letters.insert(bound.text.to_string(), system);
    if let (INTEGER_RANGE, [start, end]) = (set.notation(), set.children.as_slice()) {
        ranged.insert(
            bound.text.to_string(),
            methods_membership::Range {
                start: start.clone(),
                end: end.clone(),
            },
        );
    }
    true
}
