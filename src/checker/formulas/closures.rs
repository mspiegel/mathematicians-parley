//! Closure claims, real arithmetic, links and recursions.

use std::slice;

use super::*;
use crate::checker::library;
use crate::checker::record::{Facing, PassedCondition, TakenCase};
use crate::corpus::proof;
use crate::matching;
use crate::methods::pairs::Coordinate;
use crate::methods::surds::Verdict as Surd;
use crate::methods::{field, pairs};

/// A claim a closure method is asked of: a step's own, or a requires line's
/// read as the step it would be, with the requires lines above it among what
/// it cites (`ELABORATION.md`, R2).
pub(super) struct ClosureClaim<'s> {
    /// The step the claim is made at.
    pub(super) step: &'s Step,
    pub(super) claim: &'s Written,
    pub(super) refs: &'s [String],
    /// The requires lines above a requires line, whose facts it rests on.
    pub(super) above: Vec<&'s Requires>,
    /// Where a refusal is said.
    pub(super) line: usize,
    /// The requires line, where the claim is one.
    pub(super) requires: Option<&'s Requires>,
}

/// A closure claim and what it cites, read.
pub(super) struct ClosureRead {
    pub(super) claimed: Node,
    /// The claim's sentences, read, whose conjunction is `claimed`; the
    /// body of a claim read at a member.
    pub(super) sentences: Vec<Node>,
    pub(super) lines: Vec<Node>,
    /// The page's line each of `lines` is of: the cited line by its place
    /// among the references, and a requires line above after them, by its
    /// place among those.
    pub(super) line_of: Vec<usize>,
    /// Where the claim is read at a member (`read_at_member`), the membership
    /// its "for all" gives the member.
    pub(super) member: Option<Node>,
}

impl ClosureRead {
    /// A claim and the lines it is read from, as it stands, not at a member.
    pub(super) fn new(
        claimed: Node,
        lines: Vec<Node>,
        line_of: Vec<usize>,
    ) -> ClosureRead {
        ClosureRead {
            sentences: vec![claimed.clone()],
            claimed,
            lines,
            line_of,
            member: None,
        }
    }

    /// A claim said of every member, read at a member (`SYNTAX.md`, a step
    /// said of every member), as a citation's is (`claimed_member`): the
    /// body in the claim's place, and the membership its "for all" gives
    /// the member, kept as `member`. The claim as it stands where it says
    /// no "for all".
    pub(super) fn read_at_member(&mut self, known: &Known) {
        if let Some((member, body)) = claimed_member(&self.claimed, known.env.g) {
            self.member = Some(member);
            self.sentences = vec![body.clone()];
            self.claimed = body;
        }
    }

    /// What the member's membership implies, `i ≥ 1` of i ∈ ℕ, where the
    /// claim is read at a member.
    pub(super) fn member_implies(&self, known: &Known) -> Vec<Node> {
        self.member
            .iter()
            .flat_map(|m| implied_facts(m, known.env, &known.sorts))
            .collect()
    }
}

impl<'s> ClosureClaim<'s> {
    pub(super) fn step(step: &'s Step) -> ClosureClaim<'s> {
        ClosureClaim {
            step,
            claim: &step.claim,
            refs: &step.just.refs,
            above: Vec::new(),
            line: step.just.line,
            requires: None,
        }
    }

    /// A calculation row's reason, read as the requires line it is
    /// (`ChainLine::reason`), with every requires line of its step: the
    /// step's requires lines stand under its rows, and a row's reason is
    /// read with them (`CHECKER.md`).
    pub(super) fn row(step: &'s Step, req: &'s Requires) -> ClosureClaim<'s> {
        ClosureClaim {
            above: step.requires.iter().collect(),
            ..ClosureClaim::requires(step, req)
        }
    }

    pub(super) fn requires(step: &'s Step, req: &'s Requires) -> ClosureClaim<'s> {
        ClosureClaim {
            step,
            claim: &req.fact,
            refs: req.lines(),
            above: step.requires_above(req.line).collect(),
            line: req.line,
            requires: Some(req),
        }
    }

    /// The claim and what it cites, read with the defines it cites written
    /// out; None for a claim of more than one sentence, or one that does
    /// not read, which `check_formulas` reports. Of the requires lines
    /// above, a disequality is left out where `differing` does not keep it:
    /// two terms differing is taken only from a line the claim cites
    /// (`METHODS.md`), as the build reads it (`as_a_step`), and `membership`
    /// reads a divisor's `≠ 0` above it.
    pub(super) fn read(
        &self,
        known: &Known,
        targets: &Targets,
        differing: bool,
    ) -> Option<ClosureRead> {
        // The defines written out are those the claim cites, `refs`: the
        // step's own, or fewer where a check asks what a line does.
        let item = match self.requires {
            Some(_) => None,
            None => self.step.just.cited_item().map(|c| self.step.just.item(&c)),
        };
        // A `membership` citing a let that says its kind of number takes the
        // kind, u(x) ∈ ℝ of `let u(x) = …, a real number`, and leaves the
        // name standing (`SYNTAX.md`: a step that needs a value's
        // membership cites the label); any other method reads its rule.
        let kinded: Vec<String> = match self.membership() {
            true => {
                library::kinded_above(known.thm, known.shape(), self.step, known.env)
                    .into_iter()
                    .map(|k| k.label)
                    .collect()
            }
            false => Vec::new(),
        };
        let written_out: Vec<String> = self
            .refs
            .iter()
            .filter(|r| !kinded.contains(r))
            .cloned()
            .collect();
        let defined = known.citing_item(&written_out, item.as_deref());
        // A claim of several sentences is their conjunction (`SYNTAX.md`),
        // as `0 ≤ e. e ≤ 9.` is `0 ≤ e and e ≤ 9`.
        let sentences: Vec<Node> = self
            .claim
            .sentences()
            .iter()
            .map(|s| known.read_citing(s, &defined))
            .collect::<Option<_>>()?;
        let claimed = conjoined(known.env.g, sentences.clone())?;
        let scope = known.scope(self.step);
        let mut lines: Vec<Node> = Vec::new();
        let mut line_of: Vec<usize> = Vec::new();
        for (i, r) in self.refs.iter().enumerate() {
            let Some(written) = scope.get(r) else {
                continue;
            };
            for said in known.supplied(written, &defined) {
                lines.push(said);
                line_of.push(i);
            }
        }
        let labels = FloatLabels::new(IndexMap::new());
        for (k, o) in self.above.iter().enumerate() {
            for s in o.fact.sentences() {
                let Some(said) = known.read_citing(&s, &defined) else {
                    continue;
                };
                let apart = linear::fact(&term_of_node(&said, targets), &labels)
                    .is_some_and(|f| f.how == linear::How::Ne);
                if differing || !apart {
                    lines.push(said);
                    line_of.push(self.refs.len() + k);
                }
            }
        }
        Some(ClosureRead {
            sentences,
            ..ClosureRead::new(claimed, lines, line_of)
        })
    }

    /// Whether the claim's reason is the `membership` method: the requires
    /// line's own, or the step's.
    fn membership(&self) -> bool {
        let just = match self.requires {
            Some(req) => req.by.as_ref().ok(),
            None => Some(&self.step.just),
        };
        just.is_some_and(|j| j.head.is(Method::Membership))
    }

    /// A refusal as it is said here: of the requires line, where the claim
    /// is one.
    pub(super) fn said(&self, refusal: String) -> String {
        match self.requires {
            Some(req) => format!(
                "the requires line {} of {}, read as a step citing what it cites: {refusal}",
                req.fact,
                self.step.called()
            ),
            None => refusal,
        }
    }
}

/// A term a decider names, in the page's words: the part of what it read
/// that makes that term (`term_of_node`), printed.
pub(super) fn printed(
    term: &Term,
    read: &[&Node],
    known: &Known,
    targets: &Targets,
    labels: &FloatLabels,
) -> String {
    let want = term.rpn(labels);
    read.iter()
        .flat_map(|n| n.walk())
        .find(|part| term_of_node(part, targets).rpn(labels) == want)
        .map(|part| known.print(&part))
        .unwrap_or_else(|| want.to_string())
}

/// The coordinate each claim that two pairs differ is shown at, by the line
/// its reason is on (`CheckedTheorem::pairs_apart`): a step's and each
/// requires line's whose reason is `arithmetic`, `real arithmetic` or
/// `algebra`, as that method found it (`methods::pairs`). (1, 1) ≠ (2, 3)
/// by arithmetic is apart at the first; (a, b) ≠ (c, d) by algebra from
/// b ≠ d at the second.
pub fn pairs_apart(
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) -> IndexMap<usize, Coordinate> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        let at = ClosureClaim::step(step);
        if let Some(c) = pair_apart_at(&at, step.just.head.method(), known, targets) {
            out.insert(step.just.line, c);
        }
        for req in &step.requires {
            let Ok(by) = &req.by else {
                continue;
            };
            let at = ClosureClaim::requires(step, req);
            if let Some(c) = pair_apart_at(&at, by.head.method(), known, targets) {
                out.insert(by.line, c);
            }
        }
    }
    out
}

/// `pairs_apart` of one claim, by its reason's method; None where the
/// claim says no two pairs differ, or its method finds no coordinate.
fn pair_apart_at(
    at: &ClosureClaim,
    method: Option<Method>,
    known: &Known,
    targets: &Targets,
) -> Option<Coordinate> {
    // The claim's one fact, as the method reads it.
    let one = || {
        let facts: Vec<Node> = at
            .claim
            .sentences()
            .iter()
            .filter_map(|s| known.read_as_written(s))
            .flat_map(|n| conjuncts(&n))
            .collect();
        match facts.as_slice() {
            [one] => Some(one.clone()),
            _ => None,
        }
    };
    let apart = |term: &Term| pairs::relation(term).filter(|p| p.apart);
    match method? {
        Method::Arithmetic => {
            let term = term_of_node(&written_out(&one()?, known), targets);
            field::pairs_apart_at(&apart(&term)?)
        }
        Method::RealArithmetic => {
            let term = real_term(&one()?, known, targets);
            reals::pairs_apart_at(&apart(&term)?)
        }
        Method::Algebra => algebra_decided(at, known, targets)?.pair_apart,
        _ => None,
    }
}

/// What working out a fact `arithmetic` claims finds.
pub(in crate::checker) enum Worked {
    Holds,
    /// It is false, or cannot be worked out, and why.
    Fails(String),
    /// A sentence of it is no fact the decider works out, which the build
    /// is left to.
    Undecided,
}

/// A fact `arithmetic` claims, each sentence worked out
/// (`methods::field::decide_closed`). A sentence that does not read is
/// `check_formulas`'s to report.
pub(in crate::checker) fn arithmetic_worked(
    written: &Written,
    known: &Known,
    targets: &Targets,
) -> Worked {
    let mut out = Worked::Holds;
    // "A. B." and "A and B" are one claim (SYNTAX.md), so each sentence is
    // taken apart at its "and"s and every fact worked out alone.
    let facts = written
        .sentences()
        .iter()
        .filter_map(|s| known.read_as_written(s))
        .flat_map(|n| conjuncts(&n))
        .collect::<Vec<_>>();
    for node in facts {
        let node = written_out(&node, known);
        match decide_closed(&term_of_node(&node, targets)) {
            Built(Verdict::Holds(false)) => {
                return Worked::Fails("is false".to_string())
            }
            Built(Verdict::Unworked(why)) => return Worked::Fails(why.to_string()),
            Built(Verdict::Holds(true)) => {}
            Declined(_) => out = Worked::Undecided,
        }
    }
    out
}

/// What working out a fact `real arithmetic` claims finds.
pub(in crate::checker) enum RealWorked {
    Holds,
    /// It is false, or a part of it has no value, and why.
    Fails(String),
    /// Its sides have values, and the relation between them is not one
    /// real arithmetic decides, and why. It is not reported as false.
    Undecided(String),
    /// A sentence of it is not built from numerals, square roots, π, e and
    /// logarithms.
    Unread,
    /// It holds and takes nothing beyond what `arithmetic` works out, so it
    /// is `arithmetic`'s.
    NumeralsAlone,
}

/// A fact `real arithmetic` claims, each sentence worked out
/// (`methods::reals::decide_closed`). A sentence that does not read is
/// `check_formulas`'s to report.
pub(in crate::checker) fn real_worked(
    written: &Written,
    known: &Known,
    targets: &Targets,
) -> RealWorked {
    // Each sentence taken apart at its "and"s, as `arithmetic_worked` does.
    let nodes: Vec<Node> = written
        .sentences()
        .iter()
        .filter_map(|s| known.read_as_written(s))
        .flat_map(|n| conjuncts(&n))
        .collect();
    real_worked_of(&nodes, known, targets)
}

/// A sentence as `real arithmetic` reads it: as `term_of_node` does, with
/// each library function the theorem imports, and gives no meaning of its
/// own, built out of what it builds, as the build reads it.
pub(super) fn real_term(node: &Node, known: &Known, targets: &Targets) -> Term {
    let library = |name: &str| library_named(name, known);
    term_of_node_reading(&written_out(node, known), targets, &library)
}

/// Whether `name` is a library function in the theorem: imported, and not a
/// name its `let` lines or `obtain` steps introduce (`introduced`). The
/// settled sorts hold a library function's name with the library's sort, so
/// they do not tell the two apart; a define's name is one letter, which no
/// library function's is.
pub(super) fn library_named(name: &str, known: &Known) -> bool {
    known.sorts.imported.contains(name) && !introduced(known.thm, known).contains(name)
}

/// The pieces two terms of a link differ in, into `out`, each closed as
/// `real arithmetic` reads one: no name in it but a library function's, ln
/// in ln(2). False where a piece they differ in has a letter of the proof's
/// in it, as `cos(x)` against `cos(y)`.
pub(super) fn real_pieces(
    one: &Node,
    other: &Node,
    known: &Known,
    out: &mut Vec<Piece>,
) -> bool {
    if known.alike(one, other) {
        return true;
    }
    let closed = |n: &Node| n.names().iter().all(|name| library_named(name, known));
    if closed(one) && closed(other) {
        out.push(Piece {
            was: one.clone(),
            now: other.clone(),
        });
        return true;
    }
    one.notation() == other.notation()
        && one.text == other.text
        && one.children.len() == other.children.len()
        && one
            .children
            .iter()
            .zip(&other.children)
            .all(|(a, b)| real_pieces(a, b, known, out))
}

/// Each sentence of a fact as `real arithmetic` reads it (`real_term`),
/// taken apart at its "and"s as `arithmetic_worked` does; None where one
/// does not read.
pub(super) fn real_terms(
    written: &Written,
    known: &Known,
    targets: &Targets,
) -> Option<Vec<Term>> {
    let read: Option<Vec<Node>> = written
        .sentences()
        .iter()
        .map(|s| known.read_as_written(s))
        .collect();
    Some(
        read?
            .iter()
            .flat_map(conjuncts)
            .map(|n| real_term(&n, known, targets))
            .collect(),
    )
}

/// Whether a fact holds a square root, π, e, a logarithm or an
/// exponential, which `real arithmetic` works out and `arithmetic` does not
/// (`reals::beyond_arithmetic`).
pub(super) fn beyond_arithmetic(
    written: &Written,
    known: &Known,
    targets: &Targets,
) -> bool {
    real_terms(written, known, targets)
        .is_some_and(|terms| terms.iter().any(reals::beyond_arithmetic))
}

/// `real_worked` of sentences already read.
pub(super) fn real_worked_of(
    nodes: &[Node],
    known: &Known,
    targets: &Targets,
) -> RealWorked {
    let mut out = RealWorked::Holds;
    let mut beyond = false;
    for node in nodes {
        let term = real_term(node, known, targets);
        beyond |= reals::beyond_arithmetic(&term);
        match reals::decide_closed(&term) {
            Built(Surd::Holds(false)) => {
                return RealWorked::Fails("is false".to_string())
            }
            Built(Surd::Unworked(why)) => return RealWorked::Fails(why.to_string()),
            Built(Surd::Undecided(why)) => {
                return RealWorked::Undecided(why.to_string())
            }
            Built(Surd::Holds(true)) => {}
            Declined(_) => out = RealWorked::Unread,
        }
    }
    match out {
        RealWorked::Holds if !beyond => RealWorked::NumeralsAlone,
        out => out,
    }
}

/// Why `real arithmetic` does not show a fact, or None where it holds:
/// what is said after "which".
pub(super) fn real_unshown(worked: RealWorked) -> Option<String> {
    match worked {
        RealWorked::Holds => None,
        RealWorked::Fails(why) => Some(why),
        RealWorked::Undecided(why) => Some(format!("{why}{}", reals::NOT_DECIDED_HERE)),
        RealWorked::Unread => Some(reals::UNREAD.to_string()),
        RealWorked::NumeralsAlone => Some(
            "takes no square root, π, e, logarithm or exponential; a claim of numerals alone cites arithmetic"
                .to_string(),
        ),
    }
}

/// What `real arithmetic` claims holds when it is worked out (`METHODS.md`,
/// real arithmetic): a step's claim and a requires line's fact are decided
/// (`methods::surds::decide_closed`), and one that is false, has a part with
/// no value, states a relation the method does not decide, or takes no
/// square root, is reported.
pub fn check_real_arithmetic_holds(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    let shown = |fact: &Written| match real_worked(fact, known, targets) {
        RealWorked::Unread => Shown::Unread(reals::UNREAD.to_string()),
        worked => real_unshown(worked).map_or(Shown::Holds, Shown::Unshown),
    };
    for step in &thm.steps {
        check_shown_by(report, thm, step, Method::RealArithmetic, &shown);
        let just = &step.just;
        if let (Some(Source::RealArithmetic), Some(equation)) =
            (&just.source, &just.equation)
        {
            if let Some(why) = real_unshown(real_worked(equation, known, targets)) {
                report.say(
                    &thm.path,
                    just.line,
                    format!(
                        "step {} takes {equation} from real arithmetic, which {why}",
                        step.number
                    ),
                );
            }
        }
        // A link naming `real arithmetic` is closed, and worked out whole.
        for link in chain_links(just, &thm.path) {
            if link.line.cite != "real arithmetic" {
                continue;
            }
            // A link that does not read is the elaborator's to report.
            let Some(claim) = link.claim(known) else {
                continue;
            };
            // A library function's name, ln in ln(2), is no letter.
            let closed = claim.names().iter().all(|name| library_named(name, known));
            let why = if closed {
                real_unshown(real_worked_of(&[claim], known, targets))
            } else {
                // A link whose terms have letters changes closed pieces
                // alone, each worked out, as one naming arithmetic does.
                let mut pieces = Vec::new();
                let split = match (claim.notation(), claim.children.as_slice()) {
                    (EQUALITY, [one, other]) => {
                        real_pieces(one, other, known, &mut pieces)
                    }
                    _ => false,
                };
                if split {
                    pieces.into_iter().find_map(|Piece { was, now }| {
                        let piece = made(known.env.g, EQUALS, vec![was, now]);
                        real_unshown(real_worked_of(&[piece], known, targets))
                    })
                } else {
                    Some(
                        "changes something with a letter in it; a link may name real arithmetic where only closed pieces change, and any other cites the numbered step that states it"
                            .to_string(),
                    )
                }
            };
            if let Some(why) = why {
                report.say(
                    &thm.path,
                    link.line.line,
                    format!(
                        "a link of step {} names real arithmetic for {}, which {why}",
                        step.number,
                        link.line.quoted(&link.from)
                    ),
                );
            }
        }
    }
}

/// A closed claim `real arithmetic` decides cites it, as one `arithmetic`
/// works out cites arithmetic (`check_closed_by_arithmetic`): asked of a
/// step and each requires line giving `algebra` or `inequalities` for a
/// claim that holds a square root, π, e or a logarithm and that real
/// arithmetic finds true or false. One it does not decide, π = e, stays
/// theirs, and so does an order, which `inequalities` may prove from what
/// it cites of a root or an atom whether or not real arithmetic decides it.
pub fn check_closed_by_real_arithmetic(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    let decided = |written: &Written| {
        let terms = real_terms(written, known, targets)?;
        if !terms.iter().any(reals::beyond_arithmetic)
            || terms.iter().any(reals::is_order)
        {
            return None;
        }
        let mut holds = true;
        for t in &terms {
            let Built(Surd::Holds(this)) = reals::decide_closed(t) else {
                return None;
            };
            holds &= this;
        }
        Some(holds)
    };
    check_closed_by(report, thm, Method::RealArithmetic, &decided);
}

/// The most terms a sum or product over a range of numerals is written out
/// to; one over more is left as it is, and `arithmetic` does not decide it.
pub(super) const WRITTEN_OUT: u64 = 1000;

/// `node` with each product and sum over a range of numerals written out as
/// its terms, `∏(k ∈ {0, …, 2}) (5 − k)` as `(5 − 0)·(5 − 1)·(5 − 2)`,
/// which `arithmetic` works out as it works any product (`METHODS.md`,
/// arithmetic).
pub(super) fn written_out(node: &Node, known: &Known) -> Node {
    let children: Vec<Node> = node
        .children
        .iter()
        .map(|c| written_out(c, known))
        .collect();
    let here = node.with_children(children);
    let (index, start, end, body, joined) =
        match (here.notation(), here.children.as_slice()) {
            (PRODUCT_OVER, [index, range, body]) => match range.children.as_slice() {
                [start, end] if range.notation() == INTEGER_RANGE => {
                    (index, start, end, body, TIMES)
                }
                _ => return here,
            },
            (SUM, [index, start, end, body]) => (index, start, end, body, PLUS),
            (PRODUCT, [index, start, end, body]) => (index, start, end, body, TIMES),
            _ => return here,
        };
    let bound = |n: &Node| {
        (n.notation() == NUMERAL)
            .then(|| n.text.parse::<u64>().ok())
            .flatten()
    };
    let (Some(from), Some(to)) = (bound(start), bound(end)) else {
        return here;
    };
    if !index.is_name() || from > to || to - from >= WRITTEN_OUT {
        return here;
    }
    let g = known.env.g;
    let at = |k: u64| {
        let put = Binding::from([(index.text, numeral(&k.to_string()))]);
        matching::substitute_apart(body, &put, known.ctx)
    };
    (from + 1..=to).fold(at(from), |acc, k| made(g, joined, vec![acc, at(k)]))
}

/// `arithmetic` stands in for a line only where the fact is numerals alone.
///
/// A `substitute` may take its equation from `arithmetic`, and a chain link
/// may give `arithmetic` as its reason, because a claim with no letter in it
/// gives a reader nothing to check but working it out. One with a letter has
/// something to check, and is a numbered step of its own. A link whose terms
/// have letters but change only where they have none uses a fact of numerals
/// alone (`changed_closed`). `SYNTAX.md` has the rule.
pub fn check_closed_arithmetic(report: &mut Report, thm: &Theorem, known: &Known) {
    // A sentence that does not read is `check_formulas`'s to report.
    let closed = |written: &Written| -> bool {
        written.sentences().iter().all(|s| {
            known
                .read_as_written(s)
                .is_none_or(|n| n.names().is_empty())
        })
    };
    for step in &thm.steps {
        let just = &step.just;
        if let (Some(Source::Arithmetic), Some(equation)) =
            (&just.source, &just.equation)
        {
            if !closed(equation) {
                report.say(
                    &thm.path,
                    just.line,
                    format!(
                        "step {} takes {equation} from arithmetic, and it has a letter in it; a fact with a letter is a numbered step of its own",
                        step.number
                    ),
                );
            }
        }
        for link in chain_links(just, &thm.path) {
            if link.line.cite != "arithmetic" {
                continue;
            }
            // A link that does not read is the elaborator's to report.
            let Some(claim) = link.claim(known) else {
                continue;
            };
            // An order is worked out of numerals alone: one relating terms
            // with letters in them is inequalities', which a step of its own
            // shows and the link cites.
            if !claim.names().is_empty() && claim.notation() == ORDER {
                report.say(
                    &thm.path,
                    link.line.line,
                    format!(
                        "a link of step {} names arithmetic for {}, an order of terms with letters in them, which arithmetic does not work out; a step showing it by inequalities is cited instead",
                        step.number,
                        link.line.quoted(&link.from)
                    ),
                );
                continue;
            }
            if !claim.names().is_empty() && !changed_closed(&link, known) {
                report.say(
                    &thm.path,
                    link.line.line,
                    format!(
                        "a link of step {} names arithmetic for {}, which changes something with a letter in it; a link may name arithmetic where only pieces of numerals alone change, and any other cites the numbered step that states it",
                        step.number,
                        link.line.quoted(&link.from)
                    ),
                );
            }
        }
    }
}

/// Whether `written` holds, where `arithmetic` works out each of its
/// sentences (`methods::field::decide_closed`): built from numerals by the
/// operations it reads, and a relation it decides. √2·√2 = 2 has no letter
/// and is not one, nor is 1 + i·0 = 1, nor |{1, …, 23}| = 23. A sentence
/// that does not read is `check_formulas`'s to report, and is none.
pub(super) fn arithmetic_works_out(
    written: &Written,
    known: &Known,
    targets: &Targets,
) -> Option<bool> {
    let mut holds = true;
    for s in written.sentences().iter() {
        let n = known.read_as_written(s)?;
        let term = term_of_node(&written_out(&n, known), targets);
        let Built(Verdict::Holds(this)) = decide_closed(&term) else {
            return None;
        };
        holds &= this;
    }
    Some(holds)
}

/// A claim `arithmetic` can work out cites it, whatever relation it states:
/// `algebra` and `inequalities` combine what a step says of its letters and
/// constants, and a claim arithmetic works out gives a reader nothing to
/// check but working it out (`METHODS.md`, arithmetic). A claim with no
/// letter that it cannot work out, √2·√2 = 2, is theirs. Asked of a step
/// and of each requires line.
pub fn check_closed_by_arithmetic(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    let worked = |written: &Written| arithmetic_works_out(written, known, targets);
    check_closed_by(report, thm, Method::Arithmetic, &worked);
}

/// `membership` claims that a term is in a number system, and nothing else
/// (`METHODS.md`), or that every member of a set has a term in one.
pub fn check_membership_claims(report: &mut Report, thm: &Theorem, known: &Known) {
    for step in &thm.steps {
        if !step.just.head.is(Method::Membership) {
            continue;
        }
        if let Some(why) = membership_claim_refused(step, known) {
            report.say(&thm.path, step.just.line, why);
        }
    }
}

/// Why a `membership` step's claim is none the method makes, or None where
/// it is one, or does not read (`check_formulas` says so). One line, one
/// step: a membership step says one term is in a number system, and two,
/// as sentences or joined by "and", are two steps.
pub(super) fn membership_claim_refused(step: &Step, known: &Known) -> Option<String> {
    fn says_membership(node: &Node) -> bool {
        if node.notation() == FOR_ALL && node.children.len() == 3 {
            return says_membership(&node.children[2]);
        }
        node.notation() == MEMBERSHIP
            && node.children.len() == 2
            && node.children[1].notation() == NUMBER_SYSTEMS
    }
    let many = |count: usize| {
        format!(
            "step {} claims {count} sentences by membership, which says one term is in a number system; each is a step of its own",
            step.number
        )
    };
    let sentences = step.claim.sentences();
    if sentences.len() > 1 {
        return Some(many(sentences.len()));
    }
    for sentence in sentences {
        let Ok(node) = known.parse(&sentence) else {
            continue;
        };
        let joined = conjuncts(&node).len();
        if joined > 1 {
            return Some(many(joined));
        }
        if !says_membership(&node) {
            return Some(format!(
                "step {} names membership for {sentence}, which says no term is in a number system",
                step.number
            ));
        }
    }
    None
}

/// The labels of the defines a theorem's links may cite: its own, its
/// file's and those its file imports.
pub(super) fn define_labels(thm: &Theorem, scopes: &[FileScope]) -> BTreeSet<String> {
    proof::in_scope(thm, scopes)
        .into_iter()
        .filter_map(|d| d.label)
        .collect()
}

/// How the two sides of a link citing a define meet once the define is
/// written out (`Known::alike_how`): Some(None) where they do not; None
/// where the link does not read or is no equation.
pub(super) fn define_link_meeting(
    link: &Link,
    known: &Known,
) -> Option<Option<Meeting>> {
    let claim = link.claim(known)?;
    let cite = &link.line.cite;
    let written = known.as_cited(&claim, &known.citing(slice::from_ref(cite)));
    let (one, other) = equation_sides(&written)?;
    Some(known.alike_how(one, other))
}

/// The two sides of an equation, read under each "for all" it stands in:
/// `A` and `B` of `for all x ∈ S, A = B`. None for a statement of another
/// shape.
pub(super) fn equation_sides(statement: &Node) -> Option<(&Node, &Node)> {
    match (statement.notation(), statement.children.as_slice()) {
        (EQUALITY, [one, other]) => Some((one, other)),
        (FOR_ALL, [_, _, body]) => equation_sides(body),
        _ => None,
    }
}

/// How each link citing a define, and each step whose reason is defines it
/// names, meets the defines written out: the two sides of the equation it
/// claims, a "for all"'s at its body, or None where they do not meet; by the
/// link's line or the line of the step's reason
/// (`CheckedTheorem::define_links`).
pub fn define_link_meetings(
    thm: &Theorem,
    known: &Known,
) -> IndexMap<usize, Option<Meeting>> {
    let defines = define_labels(thm, known.env.scopes);
    let mut out: IndexMap<usize, Option<Meeting>> = thm
        .steps
        .iter()
        .flat_map(|step| chain_links(&step.just, &thm.path))
        .filter(|link| defines.contains(link.line.cite.as_str()))
        .filter_map(|link| Some((link.line.line, define_link_meeting(&link, known)?)))
        .collect();
    for step in thm.steps.iter().filter(|s| s.just.head == Head::Define) {
        let Some(claim) = known.whole(step, &step.claim) else {
            continue;
        };
        let cited: Vec<String> = step
            .just
            .refs
            .iter()
            .filter(|r| defines.contains(r.as_str()))
            .cloned()
            .collect();
        let written = known.as_cited(&claim, &known.citing(&cited));
        if let Some((one, other)) = equation_sides(&written) {
            out.insert(step.just.line, known.alike_how(one, other));
        }
    }
    out
}

/// Where in the line each calculation link cites the link stands, by the
/// link's line (`CheckedTheorem::link_places`): the sentence or part of one
/// that says it, as `check_chain_links` finds it, placed as a citation's
/// facts are (`FirstAt`), and which way the link faces it
/// (`CheckedTheorem::link_facings`). None for a link citing a define,
/// arithmetic, or a line it finds nothing in to place.
pub fn link_places(thm: &Theorem, library: &Library, known: &Known) -> LinkPlaces {
    let defines = define_labels(thm, known.env.scopes);
    let mut out = LinkPlaces::default();
    for step in &thm.steps {
        let scope = known.scope(step);
        for link in chain_links(&step.just, &thm.path) {
            let cite = &link.line.cite;
            if defines.contains(cite.as_str()) || cite == "arithmetic" {
                continue;
            }
            let Some(stated) = scope.get(cite) else {
                continue;
            };
            let Some(reading) = link_reading(&link, step, known, library) else {
                continue;
            };
            let own = known.sentence_count(stated);
            // A link read off a chain, a = c of a = b = c, stands in the
            // sentence the chain is, as the pair it reads (`placed`).
            let placed = reading.at.and_then(|k| {
                super::super::citations::placed(
                    cite,
                    &reading.says[k],
                    &reading.says,
                    own,
                )
            });
            if let Some(at) = placed {
                // How the line as written met the link, where not as written.
                if let Some(met) = known
                    .alike_how(&reading.said, &at.written)
                    .filter(|m| !m.as_written())
                {
                    out.meetings.insert(link.line.line, met);
                }
                out.places.insert(link.line.line, at);
            }
            let facing = reading.at.and_then(|k| {
                super::super::citations::facing_of(
                    &reading.says[k].cited,
                    &reading.said,
                    known,
                )
            });
            if let Some(facing) = facing {
                out.facings.insert(link.line.line, facing);
            }
        }
    }
    out
}

/// Where each calculation link citing a line stands in it, and which way it
/// faces it, by the link's line (`link_places`).
#[derive(Default)]
pub struct LinkPlaces {
    pub places: IndexMap<usize, FirstAt>,
    pub facings: IndexMap<usize, Facing>,
    /// How the line met the link, where not as written.
    pub meetings: IndexMap<usize, Meeting>,
}

/// A calculation link read against the line it cites: what the line says
/// (`Known::says`), the link as a citation of the step compares it, and
/// which of the line's facts it is, the first alike (`alike_top`); None
/// where the line is not in scope or the link does not read.
pub(super) struct LinkReading {
    pub(super) says: Vec<super::super::library::Said>,
    pub(super) said: Node,
    pub(super) at: Option<usize>,
}

/// `LinkReading` of one link of `step`: what `check_chain_links` asks of
/// it, and where `link_places` finds it.
pub(super) fn link_reading(
    link: &Link,
    step: &Step,
    known: &Known,
    library: &Library,
) -> Option<LinkReading> {
    let scope = known.scope(step);
    let stated = scope.get(&link.line.cite)?;
    let claim = link.claim(known)?;
    let defined = known.citing_step(step);
    let said = known.as_cited(&claim, &defined);
    let says = known.says(stated, &defined);
    let at = says
        .iter()
        .position(|s| alike_top(&said, &s.cited, &library.ctx));
    Some(LinkReading { says, said, at })
}

/// Each link of a calculation cites a line that says it.
///
/// `SYNTAX.md`: a link `rel t  L` cites one line whose claim is exactly the
/// previous term rel t, read either way round where it is an equation. A
/// line saying `a(0) = M` does not say `gcd(a(0), b(0)) = gcd(M, b(0))`:
/// that is a substitution, a step of its own. A line of several sentences,
/// or a conjunction, says each of them. A link naming `arithmetic` is
/// `check_closed_arithmetic`'s, and one citing a define is the define's
/// reading of the name.
pub fn check_chain_links(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let defines = define_labels(thm, scopes);
    for step in &thm.steps {
        for link in chain_links(&step.just, &thm.path) {
            let cite = &link.line.cite;
            // A link citing a define is what the define makes its name: with
            // the define written out, an equation's two sides are one.
            if defines.contains(cite.as_str()) {
                if let Some(None) = define_link_meeting(&link, known) {
                    report.say(
                        &thm.path,
                        link.line.line,
                        format!(
                            "{} is not what {cite} makes it",
                            link.line.quoted(&link.from)
                        ),
                    );
                }
                continue;
            }
            if cite == "arithmetic" || !known.scope(step).contains_key(cite) {
                continue;
            }
            // A link that does not read is the elaborator's to report.
            let Some(reading) = link_reading(&link, step, known, library) else {
                continue;
            };
            let said = reading.said;
            let lines: Vec<Node> = reading.says.into_iter().map(|s| s.cited).collect();
            if reading.at.is_none() {
                report.say(
                    &thm.path,
                    link.line.line,
                    format!(
                        "a link of step {} cites {cite}, which does not say {}; a link cites the line that states it, and a substitution is a step of its own",
                        step.number,
                        link.line.quoted(&link.from)
                    ),
                );
                continue;
            }
            // What the link drops an identity element from is a number by
            // what the step names or the page says once, the link's own
            // letters among them.
            let mut parts = Parts {
                facts: known.parts(step, library).facts.clone(),
                claims: vec![said.clone()],
                seed: Binding::new(),
                said_once: Vec::new(),
            };
            let introduced = super::super::library::introduced(known, step);
            let typed = super::super::library::typed_in_scope(known, step);
            let points = super::super::library::points_introduced(known, step);
            said_once(
                &mut parts,
                &introduced,
                &points,
                &typed,
                library,
                &known.sorts,
            );
            if let Some(left) =
                link_unsaid(&said, &lines, &parts.facts, library).first()
            {
                report.say(
                    &thm.path,
                    link.line.line,
                    format!(
                        "a link of step {} drops an identity element from {}, which nothing the step names says is a number; a requires line of the step says it",
                        step.number,
                        known.print(left)
                    ),
                );
            }
        }
    }
}

/// The name the define carrying `label` gives, or None: one this theorem
/// writes, one its file writes, or one its file imports under an alias.
pub(super) fn define_named(
    thm: &Theorem,
    label: &str,
    scopes: &[FileScope],
) -> Option<String> {
    // A recursion gives no one name.
    proof::in_scope(thm, scopes)
        .into_iter()
        .find(|d| d.label.as_deref() == Some(label))
        .and_then(|d| d.parts.name().map(|_| d.name))
}

/// The define by recursion this theorem writes under `label`, with the line
/// it is written on, or None where the label is another kind of define or
/// none.
pub(super) fn recursion_cited(
    thm: &Theorem,
    label: &str,
) -> Option<(Recursion, usize)> {
    let d = thm.defines.iter().find(|d| d.label == label)?;
    match define_parts(&d.text) {
        Built(DefineParts::Recursion(r)) => Some((r, d.line)),
        _ => None,
    }
}

/// What the define by recursion says `name` is at the argument `at`, as
/// (the rule's term there, the index it is taken at, or None at 0); or None
/// where `at` is neither 0 nor something plus one. 1 is 0 + 1 with its 0
/// dropped (`SYNTAX.md`, "An identity element goes without saying"), so
/// F(1) is the step rule at 0; 2 is not 1 + 1 by any element dropped, and
/// is a value no rule gives.
pub(super) fn recursion_value(
    said: &Recursion,
    name: &str,
    at: &Node,
    written: impl Fn(&RuleText) -> Written,
    env: Env,
    sorts: &Sorts,
) -> Checked<Option<(Node, Option<Node>)>> {
    let (rule, index) = if at.notation() == NUMERAL && at.text == "0" {
        (&said.start[name], None)
    } else if at.spelling() == PLUS
        && at.children.len() == 2
        && at.children[1].notation() == NUMERAL
        && at.children[1].text == "1"
    {
        (&said.step[name], Some(at.children[0].clone()))
    } else if at.notation() == NUMERAL && at.text == "1" {
        (&said.step[name], Some(Node::numeral("0")))
    } else {
        return Ok(None);
    };
    let mut local = sorts.clone();
    local.insert(said.index.clone(), Sort::of("number"));
    let mut term = written(rule).formula()?.read(env.g, &local)?;
    if let Some(index) = &index {
        let mut put = Binding::new();
        put.insert(Symbol::of(&said.index), index.clone());
        // Apart from a letter the rule binds, a sum's index among them.
        term = substitute_apart_by(&term, &put, &env.g.binders());
    }
    Ok(Some((term, index)))
}

/// The value a term by cases takes where the facts say which case, with the
/// conditions passed to reach it, or why no case is said. A term not by
/// cases is its own value, passing none.
pub(super) enum Case {
    Value { value: Node, passed: Vec<Passed> },
    Unsaid(&'static str),
}

/// A condition passed on the way to a case: whether it holds or fails, and
/// the fact that says so.
pub(super) struct Passed {
    pub(super) holds: bool,
    pub(super) fact: Node,
}

/// A condition is said where a fact is it, or denies it, as one formula
/// (`Known::alike`): `0 = b(k)` says the condition `b(k) = 0` holds.
pub(super) fn case_taken(
    node: &Node,
    facts: &[Node],
    wrappers: &FxIndexSet<NotationId>,
    known: &Known,
) -> Case {
    let mut node = node.clone();
    let mut passed = Vec::new();
    while node.notation() == BY_CASES && node.children.len() == 3 {
        let (value, condition, rest) = (
            node.children[0].clone(),
            node.children[1].clone(),
            node.children[2].clone(),
        );
        if let Some(f) = facts.iter().find(|f| known.alike(f, &condition)) {
            passed.push(Passed {
                holds: true,
                fact: f.clone(),
            });
            return Case::Value { value, passed };
        }
        if let Some(f) = facts.iter().find(|f| {
            wrappers.contains(&f.notation())
                && !f.children.is_empty()
                && known.alike(&f.children[0], &condition)
        }) {
            passed.push(Passed {
                holds: false,
                fact: f.clone(),
            });
            node = rest;
            continue;
        }
        return Case::Unsaid(
            "no line it cites says whether a case's condition holds or fails",
        );
    }
    Case::Value {
        value: node,
        passed,
    }
}

/// How a step's equation is a define's value: its two sides one term as
/// written, whatever case holds; one side's case, taken by the conditions
/// passed, alike the other side; or neither, with why where a condition is
/// unsaid. The check (`check_define_citation`) and the record
/// (`define_cases`) both read a step by this.
pub(super) enum Given {
    AsWritten,
    Taken {
        passed: Vec<Passed>,
        /// How the case's value meets the other side (`Known::alike_how`).
        meeting: Option<Meeting>,
    },
    Not(Option<&'static str>),
}

pub(super) fn value_given(
    left: &Node,
    right: &Node,
    facts: &[Node],
    wrappers: &FxIndexSet<NotationId>,
    known: &Known,
) -> Given {
    // Written out, the two sides one term: the claim is the define's
    // value as the define writes it, whatever case holds, as
    // `e(n) = s(D(f(n), n))` is where s is by cases.
    if known.alike(left, right) {
        return Given::AsWritten;
    }
    let mut why: Option<&'static str> = None;
    for (one, other) in [(left, right), (right, left)] {
        match case_taken(one, facts, wrappers, known) {
            Case::Unsaid(reason) => why = why.or(Some(reason)),
            Case::Value { value, passed } => {
                if known.alike(&value, other) {
                    let meeting = known.alike_how(&value, other);
                    return Given::Taken { passed, meeting };
                }
            }
        }
    }
    Given::Not(why)
}

/// What is wrong with a step's claim, read as one equation a define by
/// recursion gives; None where nothing is.
///
/// One side is a sequence at 0 or at X + 1, and the other is what the define
/// says it is there: the value at 0, or the rule at k + 1 with X for k, in
/// the case the cited lines say it is in. At X + 1 a cited line says X ∈ ℕ₀,
/// since the rule holds only at a step the index takes.
pub(super) fn recursion_equation(
    claims: &[Node],
    facts: &[Node],
    said: &Recursion,
    line: usize,
    known: &Known,
    wrappers: &FxIndexSet<NotationId>,
    equals: &FxIndexSet<NotationId>,
) -> Option<String> {
    let sorts = &known.sorts;
    if claims.len() != 1 || !equals.contains(&claims[0].notation()) {
        return Some(
            "claims no one equation; a define says what its names are equal to"
                .to_string(),
        );
    }
    let mut why: Option<String> = Some(format!(
        "its claim has none of {} applied on either side",
        said.names.join(", ")
    ));
    let kids = &claims[0].children;
    let orders = [(&kids[0], &kids[1]), (&kids[1], &kids[0])];
    for (one, other) in orders {
        if !(one.notation() == APPLICATION
            && one.children.len() == 2
            && one.children[0].is_name()
            && said.names.iter().any(|n| *n == one.children[0].text))
        {
            continue;
        }
        why = None;
        let name = &one.children[0].text;
        let rule = |text: &RuleText| text.written(&known.thm.path, line);
        let Ok(found) =
            recursion_value(said, name, &one.children[1], rule, known.env, sorts)
        else {
            continue; // `check_formulas` says it does not read
        };
        let Some((term, index)) = found else {
            why = Some(format!(
                "{name} is given at 0 and at {} + 1, and nowhere else",
                said.index
            ));
            continue;
        };
        if let Some(index) = &index {
            let said_in = facts.iter().any(|f| {
                f.notation() == MEMBERSHIP
                    && f.children.len() == 2
                    && known.alike(&f.children[0], index)
                    && f.children[1].text == said.domain
            });
            if !said_in {
                why = Some(format!(
                    "no line it cites says the index is in {}",
                    said.domain
                ));
                continue;
            }
        }
        match case_taken(&term, facts, wrappers, known) {
            Case::Unsaid(reason) => {
                why = Some(reason.to_string());
                continue;
            }
            Case::Value { value: got, .. } => {
                if known.alike(&got, other) {
                    return None;
                }
            }
        }
    }
    Some(match why {
        Some(why) if !why.is_empty() => {
            format!("claims a value it does not give: {why}")
        }
        _ => "claims a value it does not give".to_string(),
    })
}

/// A define by recursion says each value from the values before it.
///
/// A value at 0 names none of the sequences, and a rule at k + 1 names them
/// only at k: `a(k + 1) := a(k + 1) + 1` says nothing, and `a(k + 1) :=
/// a(k − 1)` reaches a value the rule has not given yet. Each rule reads,
/// since a rule that does not is a value nobody can cite.
///
/// A rule at k + 1 may name k itself, as `c(k + 1) := c(k) + k` does; a
/// value at 0 has no k to name.
pub fn check_recursions(report: &mut Report, thm: &Theorem, known: &Known) {
    for d in &thm.defines {
        let Built(DefineParts::Recursion(said)) = define_parts(&d.text) else {
            continue;
        };
        let mut local = known.sorts.clone();
        local.insert(said.index.clone(), Sort::of("number"));
        let label = &d.label;
        for (given, at) in [(&said.start, None), (&said.step, Some(&said.index))] {
            for (name, rule) in given {
                let place = match at {
                    None => format!("{name}(0)"),
                    Some(at) => format!("{name}({at} + 1)"),
                };
                let rule = d.rule(rule);
                let tree = match rule
                    .formula()
                    .and_then(|s| known.keep_read(&s, &local))
                {
                    Ok(tree) => tree,
                    Err(p) => {
                        report.say(
                            &thm.path,
                            d.line,
                            format!(
                                "define {label}: the rule for {place} does not read: {}",
                                p.message
                            ),
                        );
                        continue;
                    }
                };
                let applied = |node: &Node| {
                    node.notation() == APPLICATION
                        && node.children.len() == 2
                        && node.children[0].is_name()
                        && said.names.iter().any(|n| *n == node.children[0].text)
                };
                let nodes = walk(slice::from_ref(&tree));
                let at_k: BTreeSet<usize> = nodes
                    .iter()
                    .filter(|n| applied(n))
                    .map(|n| n.children[1].id())
                    .collect();
                if at.is_none()
                    && nodes.iter().any(|n| {
                        n.is_name() && n.text == said.index && !at_k.contains(&n.id())
                    })
                {
                    report.say(
                        &thm.path,
                        d.line,
                        format!(
                            "define {label}: the value of {place} names {}, which has no value at 0",
                            said.index
                        ),
                    );
                }
                for node in &nodes {
                    if !applied(node) {
                        continue;
                    }
                    let arg = &node.children[1];
                    if let Some(at) = at {
                        if arg.is_name() && arg.text == *at {
                            continue;
                        }
                    }
                    let message = match at {
                        Some(_) => format!(
                            "define {label}: the rule for {place} names {} at a place other than {}",
                            node.children[0].text, said.index
                        ),
                        None => format!(
                            "define {label}: the value of {place} names {}, which has no value before 0",
                            node.children[0].text
                        ),
                    };
                    report.say(&thm.path, d.line, message);
                    break;
                }
            }
        }
    }
}

/// A step citing a define claims what the define says the name is.
///
/// The claim is an equation with the name on one side, applied or not, and
/// its value on the other, in either order. Written out, the two sides are
/// one term. Where the define is by cases, the lines the step cites say
/// which case it is in, by its condition or that condition's negation, and
/// the value is the one that case gives: `h(t) = g⁻¹(t)` cites D2 from a
/// line saying t ∉ C.
pub fn check_define_citation(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let env = library.env;
    let wrappers = wrappers(env);
    for step in &thm.steps {
        let just = &step.just;
        if just.head != Head::Define {
            continue;
        }
        let label = just.defined.clone().unwrap_or_default();
        let say = format!("step {} cites {label}", step.number);
        if let Some((recursion, line)) = recursion_cited(thm, &label) {
            let parts = known.parts(step, library);
            if let Some(why) = recursion_equation(
                &parts.claims,
                &parts.facts,
                &recursion,
                line,
                known,
                &wrappers,
                &library.ctx.equations,
            ) {
                report.say(&thm.path, just.line, format!("{say} and {why}"));
            }
            continue;
        }
        let Some(name) = define_named(thm, &label, scopes) else {
            report.say(
                &thm.path,
                just.line,
                format!("{say}, which no define in scope carries"),
            );
            continue;
        };
        let parts = known.parts(step, library);
        let written: Result<Vec<Node>, _> = step
            .claim
            .sentences()
            .iter()
            .map(|s| known.parse(s))
            .collect();
        let Ok(written) = written else {
            continue;
        };
        // A define with a parameter says what its function is on, as well as
        // what its name is equal to (`ELABORATION.md`).
        if parts.claims.len() == 1
            && written.len() == 1
            && library
                .ctx
                .functions_on
                .contains(&parts.claims[0].notation())
        {
            // The subject as written: the claim's parts have the defined
            // name written out, and h is then the function it names.
            let subject = written[0].children.first();
            if !subject.is_some_and(|s| s.is_name() && s.text == name) {
                report.say(
                    &thm.path,
                    just.line,
                    format!("{say} and claims that something other than {name} is a function on a set"),
                );
            }
            continue;
        }
        if parts.claims.len() != 1
            || written.len() != 1
            || !library.ctx.equations.contains(&parts.claims[0].notation())
        {
            report.say(
                &thm.path,
                just.line,
                format!("{say} and claims no one equation; a define says what its name is equal to, and a define with a parameter what its function is on"),
            );
            continue;
        }
        let named: BTreeSet<String> = written[0]
            .walk()
            .iter()
            .filter(|n| n.is_name())
            .map(|n| n.text.to_string())
            .collect();
        if !named.contains(&name) {
            report.say(
                &thm.path,
                just.line,
                format!("{say} and its claim never names {name}"),
            );
            continue;
        }
        let (left, right) =
            (&parts.claims[0].children[0], &parts.claims[0].children[1]);
        if let Given::Not(why) =
            value_given(left, right, &parts.facts, &wrappers, known)
        {
            let tail = why.map(|w| format!(": {w}")).unwrap_or_default();
            report.say(
                &thm.path,
                just.line,
                format!("{say} and claims a value it does not give{tail}"),
            );
        }
    }
}

/// Of each step citing a define by cases whose value it claims in one case,
/// the conditions it passes to reach it, each placed in the line the step
/// cites that says it holds or fails, and how the case's value meets the
/// other side (`CheckedTheorem::define_cases`), as `check_define_citation`
/// reads the step; by the step's line.
pub fn define_cases(
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> IndexMap<usize, TakenCase> {
    let wrappers = wrappers(library.env);
    let mut out = IndexMap::new();
    for step in thm.steps.iter().filter(|s| s.just.head == Head::Define) {
        let label = step.just.defined.as_deref().unwrap_or_default();
        if recursion_cited(thm, label).is_some() {
            continue;
        }
        let parts = known.parts(step, library);
        let [claim] = parts.claims.as_slice() else {
            continue;
        };
        if !library.ctx.equations.contains(&claim.notation()) {
            continue;
        }
        let Given::Taken { passed, meeting } = value_given(
            &claim.children[0],
            &claim.children[1],
            &parts.facts,
            &wrappers,
            known,
        ) else {
            continue;
        };
        if passed.is_empty() {
            continue;
        }
        let passed = passed
            .iter()
            .map(|p| PassedCondition {
                holds: p.holds,
                said_by: fact_placed(step, &p.fact, known),
            })
            .collect();
        out.insert(step.just.line, TakenCase { passed, meeting });
    }
    out
}

/// Where in a line the step cites the fact stands, the first line that says
/// it, placed as a citation's facts are (`FirstAt`); None where no line the
/// step cites says it, a requires line's fact among them.
pub(in crate::checker) fn fact_placed(
    step: &Step,
    fact: &Node,
    known: &Known,
) -> Option<FirstAt> {
    let scope = known.scope(step);
    let defined = known.citing_step(step);
    step.just.refs.iter().find_map(|r| {
        let stated = scope.get(r)?;
        let says = known.says(stated, &defined);
        let s = says.iter().find(|s| known.alike(&s.cited, fact))?;
        super::super::citations::placed(r, s, &says, known.sentence_count(stated))
    })
}
