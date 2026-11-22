//! What an algebra step leaves unsaid, relations and orders.

use super::super::record::{NonzeroBy, NotZero};
use super::*;
use std::{iter, slice};

use crate::checker::record::PageReading;
use crate::citing::finite::FiniteSets;
use crate::citing::NonzeroHow;
use crate::citing::{finite, Implication};
use crate::formula::node::ByShape;
use crate::matching::Defined;
use crate::methods::pairs::Coordinate;
use crate::methods::{field, pairs};
use crate::{citing, matching};

/// An `algebra` claim as the method decides it: the claim and its lines
/// read, the cited lines fact by fact, and the verdict.
pub(super) struct AlgebraDecided {
    pub(super) read: ClosureRead,
    /// The cited lines' facts one by one, which the verdict's `combined`
    /// counts among.
    pub(super) facts: Vec<Node>,
    pub(super) verdict: algebra::Verdict,
    /// Of a claim that two pairs differ, the coordinate a cited difference
    /// shows them apart at (`algebra::apart_at`).
    pub(super) pair_apart: Option<Coordinate>,
}

/// The `algebra` decision of one claim; None where the claim does not read.
pub(super) fn algebra_decided(
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> Option<AlgebraDecided> {
    let mut read = at.read(known, targets, false)?;
    read.read_at_member(known);
    let labels = FloatLabels::new(IndexMap::new());
    // The cited lines fact by fact, so that a line saying several things,
    // in sentences or joined by "and", asks only of the ones combined. Each
    // is decided with its identity elements dropped, as the claim is
    // (`SYNTAX.md`, "An identity element goes without saying"): F(0 + 1) and
    // F(1) are one atom.
    let ctx = &known.ctx;
    let facts: Vec<Node> = read.lines.iter().flat_map(conjuncts).collect();
    let cited: Vec<Term> = facts
        .iter()
        .map(|n| term_of_node(&matching::bare(n, ctx), targets))
        .collect();
    let claimed = term_of_node(&matching::bare(&read.claimed, ctx), targets);
    // Sums are read as linear where some term of the step is linear in
    // something, as the build reads them (`field::says_something_linear`).
    let linear = iter::once(&claimed)
        .chain(&cited)
        .any(|t| field::says_something_linear(t, &labels));
    let verdict =
        field::reading_sums(linear, || algebra::decide(&claimed, &cited, &labels));
    let pair_apart = pairs::relation(&claimed)
        .filter(|p| p.apart)
        .and_then(|p| algebra::apart_at(&p, &cited, &labels));
    Some(AlgebraDecided {
        read,
        facts,
        verdict,
        pair_apart,
    })
}

/// The parts each `algebra` reason divides by, with why each is not zero,
/// by the line the reason is on (`CheckedTheorem::divided_by`): a step's,
/// a requires line's, and a calculation row's, read as the requires line
/// it is (`ChainLine::reason`). Of a claim that holds, the divisors of its
/// claim and of the cited lines it combines, each taken apart as `nonzero`
/// finds it not zero; a part nothing says is not zero is left out, as the
/// check reports it.
pub fn divided_by(
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) -> IndexMap<usize, Vec<super::super::record::NotZero>> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        if step.just.head.is(Method::Algebra) {
            let parts = divided_at(&ClosureClaim::step(step), known, targets);
            if !parts.is_empty() {
                out.insert(step.just.line, parts);
            }
        }
        let rows: Vec<Requires> = chain_links(&step.just, &thm.path)
            .into_iter()
            .filter_map(|link| link.line.reason)
            .collect();
        let claims = step
            .requires
            .iter()
            .map(|req| (req, ClosureClaim::requires(step, req)))
            .chain(rows.iter().map(|req| (req, ClosureClaim::row(step, req))));
        for (req, at) in claims {
            let (true, Ok(by)) = (req.is(Method::Algebra), &req.by) else {
                continue;
            };
            let parts = divided_at(&at, known, targets);
            if !parts.is_empty() {
                out.insert(by.line, parts);
            }
        }
    }
    out
}

/// `divided_by` of one claim.
pub(super) fn divided_at(
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> Vec<super::super::record::NotZero> {
    let Some(AlgebraDecided {
        read,
        facts,
        verdict: algebra::Verdict::Holds { combined },
        ..
    }) = algebra_decided(at, known, targets)
    else {
        return Vec::new();
    };
    // What says a divisor is not zero is read with the disequalities of the
    // requires lines above kept, as `membership` reads a divisor's `≠ 0`
    // (`ClosureClaim::read`).
    let Some(mut with_unequal) = at.read(known, targets, true) else {
        return Vec::new();
    };
    with_unequal.read_at_member(known);
    let held = MembershipIn::of(at, &with_unequal, known);
    let given = held.given(targets, known);
    let mut relations = vec![read.claimed.clone()];
    relations.extend(
        combined
            .iter()
            .filter_map(|&i| facts.get(i))
            .filter(|n| algebra_relation(n))
            .cloned(),
    );
    let mut out: Vec<NotZero> = Vec::new();
    for relation in &relations {
        let sides = sides_of(relation)
            .into_iter()
            .flat_map(|side| coordinates_of(side, targets));
        for side in sides {
            for d in methods_membership::Parts::of(side).divisors {
                for (term, how) in methods_membership::nonzero_how(&d, &given)
                    .into_iter()
                    .flatten()
                {
                    if out.iter().any(|o| known.alike(&o.term, &term)) {
                        continue;
                    }
                    let by = match how {
                        NonzeroHow::Stated(line) => {
                            // The line it is read from: itself where a line
                            // states it, or the fact implying it.
                            let Some(from) = held
                                .stated
                                .iter()
                                .find(|s| known.alike(s, line))
                                .or_else(|| {
                                    held.stated.iter().find(|s| {
                                        implied_facts(s, known.env, &known.sorts)
                                            .iter()
                                            .any(|i| known.alike(i, line))
                                    })
                                })
                            else {
                                continue;
                            };
                            NonzeroBy::Stated {
                                line: line.clone(),
                                from: from.clone(),
                            }
                        }
                        NonzeroHow::Numerals => NonzeroBy::Numerals,
                        NonzeroHow::Positive => NonzeroBy::Positive,
                    };
                    out.push(NotZero { term, by });
                }
            }
        }
    }
    out
}

/// What an `algebra` step that holds leaves unsaid of its hypotheses
/// (`METHODS.md`, algebra): every atom of its claim and of the cited lines
/// it combines, `combined` by their place among `facts`, the cited lines'
/// facts one by one, is a number, said once or by a line the step names,
/// and every divisor they write other than a numeral is not zero by such a
/// line. None where both are said.
pub(super) fn algebra_unsaid(
    at: &ClosureClaim,
    read: &ClosureRead,
    facts: &[Node],
    combined: &[usize],
    known: &Known,
    targets: &Targets,
) -> Option<String> {
    let held = MembershipIn::of(at, read, known);
    let given = held.given(targets, known);
    let mut relations = vec![read.claimed.clone()];
    relations.extend(
        combined
            .iter()
            .filter_map(|&i| facts.get(i))
            .filter(|n| algebra_relation(n))
            .cloned(),
    );
    for relation in &relations {
        let sides = sides_of(relation)
            .into_iter()
            .flat_map(|side| coordinates_of(side, targets));
        for side in sides {
            let parts = methods_membership::Parts::of(side);
            if let Some(atom) = parts
                .atoms
                .iter()
                .find(|a| !methods_membership::atom_held(a, System::C, &given))
            {
                return Some(unsaid_number(
                    atom,
                    at,
                    known,
                    "∈ ℝ or ∈ ℂ",
                    "nothing says",
                ));
            }
            if let Some(unsaid) = parts
                .divisors
                .iter()
                .find_map(|d| methods_membership::unsaid_part(d, &given))
            {
                return Some(format!(
                    "nothing says {} ≠ 0, which this step needs to divide by it",
                    known.print(&unsaid)
                ));
            }
        }
    }
    None
}

/// What an `inequalities` step that holds leaves unsaid of its hypotheses
/// (`METHODS.md`, inequalities): every atom of its claim and of the facts
/// the step combines (`inequalities::combined`), not of every sentence a
/// cited line says, is a real number, said once or by a line the step
/// names, and a divisor that is not a numeral is not zero by such a line.
/// None where both are said.
pub(super) fn inequalities_unsaid(
    at: &ClosureClaim,
    read: &ClosureRead,
    known: &Known,
    targets: &Targets,
) -> Option<String> {
    let labels = FloatLabels::new(IndexMap::new());
    // The cited lines fact by fact, so that a line saying several things
    // asks only of the ones combined.
    let mut facts: Vec<Node> = Vec::new();
    let mut line_of: Vec<usize> = Vec::new();
    for (said, &line) in read.lines.iter().zip(&read.line_of) {
        for part in conjuncts(said) {
            facts.push(part);
            line_of.push(line);
        }
    }
    let implied: Vec<Term> = facts
        .iter()
        .flat_map(|part| implied_facts(part, known.env, &known.sorts))
        .chain(read.member_implies(known))
        .map(|n| term_of_node(&n, targets))
        .collect();
    let terms: Vec<Term> = facts.iter().map(|n| term_of_node(n, targets)).collect();
    let claimed = term_of_node(&read.claimed, targets);
    let used = inequalities::combined(&claimed, &terms, &line_of, &implied, &labels)?;
    let relations: Vec<Node> = conjuncts(&read.claimed)
        .into_iter()
        .chain(used.cited.iter().filter_map(|&i| facts.get(i).cloned()))
        .collect();
    real_unsaid(at, read, &relations, known, targets)
}

/// What `relations` leave unsaid of an order's hypotheses (`METHODS.md`,
/// inequalities, Hypotheses): every atom of their sides a real number, and
/// every divisor that is not a numeral not zero, each said once or by a line
/// the step names. None where both are said.
pub(super) fn real_unsaid(
    at: &ClosureClaim,
    read: &ClosureRead,
    relations: &[Node],
    known: &Known,
    targets: &Targets,
) -> Option<String> {
    unsaid_of(at, read, relations, known, targets).map(|u| match &u {
        Unsaid::Real(atom) => unsaid_number(atom, at, known, "∈ ℝ", "nothing says"),
        Unsaid::Nonzero(_) => u.said(known),
    })
}

/// The message for an atom a method needs to be a number and nothing says
/// is one: a point is never one, which no line can say, so a point is told
/// that the step treats it as a number (`METHODS.md`, Rows: each row's atoms
/// are real); any other atom is told what is not said of it, `systems`
/// being "∈ ℝ" or "∈ ℝ or ∈ ℂ" and `nothing` how the message opens.
pub(super) fn unsaid_number(
    atom: &Node,
    at: &ClosureClaim,
    known: &Known,
    systems: &str,
    nothing: &str,
) -> String {
    let point = atom.is_name()
        && super::super::library::points_introduced(known, at.step)
            .contains(atom.text.as_str());
    if point {
        format!(
            "this step treats {} as a number, and it is a point",
            known.print(atom)
        )
    } else {
        format!(
            "{nothing} {} {systems}, which this step needs",
            known.print(atom)
        )
    }
}

/// What an order's relations need of a term that nothing says.
pub(super) enum Unsaid {
    /// An atom of a side, which has to be a real number.
    Real(Node),
    /// A divisor, or the part of one, which has to be other than 0.
    Nonzero(Node),
}

impl Unsaid {
    pub(super) fn said(&self, known: &Known) -> String {
        self.told(known, "nothing says")
    }

    /// The message, opening with `nothing`: "nothing says", or "nothing
    /// above says" where a line below says it.
    pub(super) fn told(&self, known: &Known, nothing: &str) -> String {
        match self {
            Unsaid::Real(atom) => {
                format!("{nothing} {} ∈ ℝ, which this step needs", known.print(atom))
            }
            Unsaid::Nonzero(part) => format!(
                "{nothing} {} ≠ 0, which this step needs to divide by it",
                known.print(part)
            ),
        }
    }

    /// Whether the two ask the same of the same term.
    pub(super) fn same(&self, other: &Unsaid, known: &Known) -> bool {
        match (self, other) {
            (Unsaid::Real(a), Unsaid::Real(b))
            | (Unsaid::Nonzero(a), Unsaid::Nonzero(b)) => known.alike(a, b),
            _ => false,
        }
    }
}

/// `real_unsaid`, naming the term and what it needs.
pub(super) fn unsaid_of(
    at: &ClosureClaim,
    read: &ClosureRead,
    relations: &[Node],
    known: &Known,
    targets: &Targets,
) -> Option<Unsaid> {
    let held = MembershipIn::of(at, read, known);
    let given = held.given(targets, known);
    for relation in relations {
        for side in relation_sides(relation) {
            let parts = methods_membership::Parts::of(side);
            if let Some(atom) = parts
                .atoms
                .iter()
                .find(|a| !methods_membership::atom_held(a, System::R, &given))
            {
                return Some(Unsaid::Real(atom.clone()));
            }
            if let Some(unsaid) = parts
                .divisors
                .iter()
                .find_map(|d| methods_membership::unsaid_part(d, &given))
            {
                return Some(Unsaid::Nonzero(unsaid));
            }
        }
    }
    None
}

/// A relation of `=`, `≠`, `<`, `≤`, `>` or `≥` as the page writes it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Rel {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Rel {
    pub(super) fn of(node: &Node) -> Option<Rel> {
        // A disequality is the negation of an equation (`Related::of`): a
        // record declares `_ ≠ _` the negation of `_ = _`.
        match node.spelling() {
            EQUALS => Some(Rel::Eq),
            LESS => Some(Rel::Lt),
            AT_MOST => Some(Rel::Le),
            GREATER => Some(Rel::Gt),
            AT_LEAST => Some(Rel::Ge),
            _ => None,
        }
    }

    pub(super) fn up(self) -> bool {
        matches!(self, Rel::Lt | Rel::Le)
    }

    pub(super) fn down(self) -> bool {
        matches!(self, Rel::Gt | Rel::Ge)
    }

    /// The same relation read from its right side: `a < b` is `b > a`.
    pub(super) fn converse(self) -> Rel {
        match self {
            Rel::Eq => Rel::Eq,
            Rel::Ne => Rel::Ne,
            Rel::Lt => Rel::Gt,
            Rel::Le => Rel::Ge,
            Rel::Gt => Rel::Lt,
            Rel::Ge => Rel::Le,
        }
    }
}

/// One relation between two terms, its sides as the page writes them, and
/// the formula it is read from.
#[derive(Clone, Debug)]
pub(super) struct Related {
    pub(super) left: Node,
    pub(super) right: Node,
    pub(super) rel: Rel,
    pub(super) said: Node,
    /// Whether the line it is taken from writes it; one the line says
    /// without writing it has no written orientation (`METHODS.md`,
    /// inequalities, the first row).
    pub(super) written: bool,
    /// Whether it is read from the right side of the formula it is taken
    /// from (`turned`).
    pub(super) turned: bool,
}

impl Related {
    /// A formula that is one relation; None for any other, a conjunction of
    /// two among them. `a ≠ b` is read as the negation of `a = b`.
    pub(super) fn of(node: &Node) -> Option<Related> {
        if let (LOGICAL_NOT, [inner]) = (node.notation(), node.children.as_slice()) {
            let equation = Related::of(inner).filter(|e| e.rel == Rel::Eq)?;
            return Some(Related {
                rel: Rel::Ne,
                said: node.clone(),
                ..equation
            });
        }
        let rel = Rel::of(node)?;
        let [left, right] = node.children.as_slice() else {
            return None;
        };
        Some(Related {
            left: left.clone(),
            right: right.clone(),
            rel,
            said: node.clone(),
            written: true,
            turned: false,
        })
    }

    /// The link read from its right side, from the same formula.
    pub(super) fn turned(&self) -> Related {
        Related {
            left: self.right.clone(),
            right: self.left.clone(),
            rel: self.rel.converse(),
            said: self.said.clone(),
            written: self.written,
            turned: !self.turned,
        }
    }

    /// Whether this says what `other` says, as written or read from its
    /// right side.
    pub(super) fn says(&self, other: &Related, known: &Known) -> bool {
        let same = |a: &Related, b: &Related| {
            a.rel == b.rel
                && known.alike(&a.left, &b.left)
                && known.alike(&a.right, &b.right)
        };
        same(self, other) || same(self, &other.turned())
    }

    /// Whether this says what `other` says, written the same way round: a
    /// row's relation as it stands (`METHODS.md`, inequalities, Rows), where
    /// turning an order round is a `restate` row of its own.
    pub(super) fn says_as_written(&self, other: &Related, known: &Known) -> bool {
        self.rel == other.rel
            && known.alike(&self.left, &other.left)
            && known.alike(&self.right, &other.right)
    }
}

/// The relation a chain of these links gives (`METHODS.md`, transitivity),
/// as a calculation's: `=` where every link is `=`, and otherwise the order
/// it goes, strict where a link is. None for a chain going both ways.
pub(super) fn chain_rel(links: &[Related]) -> Option<Rel> {
    let up = links.iter().any(|l| l.rel.up());
    let down = links.iter().any(|l| l.rel.down());
    let strict = links.iter().any(|l| matches!(l.rel, Rel::Lt | Rel::Gt));
    match (up, down) {
        (true, true) => None,
        (false, false) => Some(Rel::Eq),
        (true, false) => Some(if strict { Rel::Lt } else { Rel::Le }),
        (false, true) => Some(if strict { Rel::Gt } else { Rel::Ge }),
    }
}

/// Whether `term` starts `link`, as written or, for an equation, from its
/// right side.
pub(super) fn starts(term: &Node, link: &Related, known: &Known) -> bool {
    known.alike(term, &link.left) || known.alike(term, &link.right)
}

/// Each relation of `=`, `≠`, `<`, `≤`, `>` or `≥` the line `r` in a step's
/// scope says (`Known::says`), as written: the line's own, or of a line
/// saying several things, `0 < x and x < 1`, each of them, an equation of a
/// chain and a bound a membership or a range gives among them, each with
/// whether the line writes it.
pub(super) fn line_relations(step: &Step, r: &str, known: &Known) -> Vec<Related> {
    let Some(stated) = known.scope(step).get(r).cloned() else {
        return Vec::new();
    };
    let mut out: Vec<Related> = Vec::new();
    for said in known.says(&stated, &known.citing_step(step)) {
        let Some(mut related) = Related::of(&said.written) else {
            continue;
        };
        related.written = said.from.is_written();
        if !out.iter().any(|o| known.alike(&o.said, &related.said)) {
            out.push(related);
        }
    }
    out
}

/// A define of a theorem names something new, and names a thing.
///
/// Its name is no letter the theorem introduces, by a `let` or an `obtain`,
/// and no other define's of the theorem: a name stands for one thing, so a
/// line saying x says which x. And what it names is a number, a set or a
/// map, never a statement, as a statement is nothing for the name to equal
/// (`SYNTAX.md`, a define).
pub fn check_define_names(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    scopes: &[FileScope],
) {
    let letters = introduced(thm, known);
    let mut named: IndexMap<String, usize> = IndexMap::new();
    for d in &thm.defines {
        let Built(said) = define_parts(&d.text) else {
            continue;
        };
        for name in said.names() {
            if letters.contains(&name) {
                report.say(
                    &thm.path,
                    d.line,
                    format!(
                        "define {} names {name}, which theorem {} already introduces",
                        d.label, thm.name
                    ),
                );
            } else if let Some(at) = named.get(&name) {
                report.say(
                    &thm.path,
                    d.line,
                    format!("{name} is already defined at line {at}"),
                );
            }
            named.entry(name).or_insert(d.line);
        }
        let Some(name) = define_named(thm, &d.label, scopes) else {
            continue;
        };
        let defined = known.citing(slice::from_ref(&d.label));
        // A function's value is a thing as the name is: Q(x) = x < 1 is a
        // statement of x, and no function.
        if let Some(Defined::Rule(rule)) = defined.get(&name) {
            if rule.body.sort.is("formula") {
                report.say(
                    &thm.path,
                    d.line,
                    format!(
                        "define {} says each value of {name} is {}, a statement, and a define names a thing: a number, a set or a map",
                        d.label,
                        known.print(&rule.body)
                    ),
                );
            }
        }
        if let Some(Defined::Term(term)) = defined.get(&name) {
            if term.sort.is("formula") {
                report.say(
                    &thm.path,
                    d.line,
                    format!(
                        "define {} says {name} is {}, a statement, and a define names a thing: a number, a set or a map",
                        d.label,
                        known.print(term)
                    ),
                );
            }
        }
    }
}

/// The equation a define of a name says, `e = ⌊A + 1/2⌋ − A` of `let e =
/// ⌊A + 1/2⌋ − A`, as a link citing it reads it (`SYNTAX.md`, a step may
/// cite a define); None where `r` carries no define of a name standing for
/// a term.
pub(in crate::checker) fn define_equation(
    thm: &Theorem,
    step: &Step,
    r: &str,
    known: &Known,
) -> Option<Node> {
    let name = define_named(thm, r, known.env.scopes)?;
    let defined = known.citing(&[r.to_string()]);
    let Some(Defined::Term(term)) = defined.get(&name) else {
        return None;
    };
    let named = Written::new(&name, &thm.path, step.just.line)
        .formula()
        .ok()?;
    let named = known.read_as_written(&named)?;
    Some(made(known.env.g, EQUALS, vec![named, term.clone()]))
}

/// A define of a function cited among a chain's lines, as a calculation's
/// link citing it is read: an equation between the term the line before
/// ends at and the one the line after starts from, which the define makes
/// one. Each such equation the neighbouring lines' terms give, the claim's
/// first and last terms standing for the lines at the ends; none where `r`
/// is no define.
pub(super) fn define_applied(
    thm: &Theorem,
    step: &Step,
    r: &str,
    known: &Known,
) -> Vec<Related> {
    if !thm.defines.iter().any(|d| d.label == r) {
        return Vec::new();
    }
    let refs = &step.just.refs;
    let Some(at) = refs.iter().position(|x| x == r) else {
        return Vec::new();
    };
    let claim = known
        .whole_as_written(&step.claim)
        .as_ref()
        .and_then(Related::of);
    let terms_of = |i: Option<usize>, end: fn(&Related) -> Node| -> Vec<Node> {
        match i.and_then(|i| refs.get(i)) {
            Some(other) => line_relations(step, other, known)
                .iter()
                .flat_map(|l| [l.left.clone(), l.right.clone()])
                .collect(),
            None => claim.iter().map(end).collect(),
        }
    };
    let before = terms_of(at.checked_sub(1), |c| c.left.clone());
    let after = terms_of(Some(at + 1), |c| c.right.clone());
    let defined = known.citing(slice::from_ref(&r.to_string()));
    let mut out = Vec::new();
    for one in &before {
        for other in &after {
            let same = known.alike(
                &known.as_cited(one, &defined),
                &known.as_cited(other, &defined),
            );
            if same && !known.alike(one, other) {
                let said = made(known.env.g, EQUALS, vec![one.clone(), other.clone()]);
                out.extend(Related::of(&said));
            }
        }
    }
    out
}

/// What the line `r` in a step's scope says (`Known::says`), as written.
pub(super) fn cited_says(step: &Step, r: &str, known: &Known) -> Vec<Node> {
    let Some(stated) = known.scope(step).get(r).cloned() else {
        return Vec::new();
    };
    known
        .says(&stated, &known.citing_step(step))
        .into_iter()
        .map(|s| s.written)
        .collect()
}

/// The lines a step cites, each as one link, in the order cited
/// (`METHODS.md`, transitivity): a line's relation, or of a line saying
/// several, the one of them that meets its neighbours, which is to be one
/// only. A define of a name says its equation besides any kind of number it
/// gives. The first line with no such relation reported.
pub(super) fn cited_links(
    thm: &Theorem,
    step: &Step,
    known: &Known,
    method: &str,
) -> Checked<Vec<Related>> {
    let number = &step.number;
    let mut each: Vec<Vec<Related>> = Vec::new();
    for r in &step.just.refs {
        let mut said: Vec<Related> = line_relations(step, r, known)
            .into_iter()
            .filter(|l| l.rel != Rel::Ne)
            .collect();
        said.extend(
            define_equation(thm, step, r, known)
                .as_ref()
                .and_then(Related::of),
        );
        if said.is_empty() {
            said = define_applied(thm, step, r, known);
        }
        if said.is_empty() {
            // A membership is what a requires line takes from a line, where
            // the page does not say it once.
            let membership = cited_says(step, r, known).iter().any(|c| {
                c.notation() == MEMBERSHIP
                    && super::super::citations::membership_said_once(c, step, known)
                        .is_none()
            });
            let instead = if membership {
                ", and a membership it states is taken by a requires line"
            } else {
                ""
            };
            return Err(Problem::new(
                &thm.path,
                step.just.line,
                format!(
                    "step {number} cites {r} by {method}, and {r} states no relation of =, <, ≤, > or ≥{instead}"
                ),
            ));
        }
        each.push(said);
    }
    // Where a line says several relations, the claim decides
    // (`METHODS.md`, transitivity): the one taken from each line is the one
    // making a chain from the claim's first term to its last.
    if each.iter().any(|said| said.len() > 1) {
        let reaching = reaching_claim(thm, step, &each, known);
        match reaching.as_slice() {
            [one] => return Ok(one.clone()),
            [_, _, ..] => {
                return Err(Problem::new(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {number} cites lines by {method} that say several relations, and more than one choice of them reaches the claim"
                    ),
                ));
            }
            [] => {}
        }
    }
    let meets = |a: &Related, b: &Related| {
        starts(&a.left, b, known) || starts(&a.right, b, known)
    };
    let mut out: Vec<Related> = Vec::new();
    for (i, said) in each.iter().enumerate() {
        if let [one] = said.as_slice() {
            out.push(one.clone());
            continue;
        }
        let fits: Vec<&Related> = said
            .iter()
            .filter(|s| match out.last() {
                Some(before) => meets(before, s),
                None => each
                    .get(i + 1)
                    .is_some_and(|next| next.iter().any(|n| meets(s, n))),
            })
            .collect();
        let [one] = fits.as_slice() else {
            return Err(Problem::new(
                &thm.path,
                step.just.line,
                format!(
                    "step {number} cites {} by {method}, which says several relations, and not just one of them meets the lines it is cited with",
                    step.just.refs[i]
                ),
            ));
        };
        out.push((*one).clone());
    }
    Ok(out)
}

/// Each choice of one relation from each cited line, `each` in the order
/// cited, whose chain reaches the step's claim; none where the claim does
/// not read or no choice reaches it. Choices whose relations are the same
/// formulas are one.
pub(super) fn reaching_claim(
    thm: &Theorem,
    step: &Step,
    each: &[Vec<Related>],
    known: &Known,
) -> Vec<Vec<Related>> {
    let Some(claim) = known
        .whole_as_written(&step.claim)
        .as_ref()
        .and_then(Related::of)
    else {
        return Vec::new();
    };
    let mut choices: Vec<Vec<Related>> = vec![Vec::new()];
    for said in each {
        choices = choices
            .into_iter()
            .flat_map(|before| {
                said.iter().map(move |one| {
                    let mut next = before.clone();
                    next.push(one.clone());
                    next
                })
            })
            .collect();
    }
    let mut out: Vec<Vec<Related>> = Vec::new();
    for choice in choices {
        let Ok(chained) = chain_of(thm, step, &choice, known) else {
            continue;
        };
        if !claim.says(&chained, known) {
            continue;
        }
        let seen = out.iter().any(|o| {
            o.iter()
                .zip(&choice)
                .all(|(a, b)| known.alike(&a.said, &b.said))
        });
        if !seen {
            out.push(choice);
        }
    }
    out
}

/// The relation each line a `transitivity` step cites gives its chain, as
/// written, with where it stands in the line and whether the chain reads it
/// from its right side, by the line of each step's justification
/// (`CheckedTheorem::links`); a step whose lines make no chain has none, and
/// is among the theorem's problems.
pub fn transitivity_links(
    thm: &Theorem,
    known: &Known,
    library: &Library,
) -> IndexMap<usize, Chain> {
    thm.steps
        .iter()
        .filter(|s| s.just.head.is(Method::Transitivity))
        .filter_map(|s| {
            let links = cited_links(thm, s, known, "transitivity").ok()?;
            let chain = faced(thm, s, &links, known).ok()?;
            let each = links.iter().zip(&chain).zip(&s.just.refs);
            let linked = each
                .enumerate()
                .map(|(i, ((link, read), r))| ChainLink {
                    said: link.said.clone(),
                    at: order_line(thm, s, r, &link.said, known, library),
                    turned: read.turned,
                    joint: match i.checked_sub(1).map(|before| &chain[before]) {
                        Some(before) => known
                            .alike_how(&before.right, &read.left)
                            .unwrap_or_default(),
                        None => Meeting::default(),
                    },
                    define_facing: thm
                        .defines
                        .iter()
                        .any(|d| d.label == *r)
                        .then(|| define_named_facing(thm, s, r, &link.said, known))
                        .flatten(),
                })
                .collect();
            // The claim runs from the chain's first left side, or from its
            // last right side, written the other way round.
            let ends = chain_of(thm, s, &links, known).ok()?;
            let claim = Related::of(&known.whole_as_written(&s.claim)?)?;
            let claim_turned = !known.alike(&claim.left, &ends.left);
            let same = |a: &Node, b: &Node| known.print(a) == known.print(b);
            let (left, right) = match claim_turned {
                false => (&claim.left, &claim.right),
                true => (&claim.right, &claim.left),
            };
            let as_written = chain.windows(2).all(|w| same(&w[0].right, &w[1].left))
                && same(left, &ends.left)
                && same(right, &ends.right);
            let falls = chain.iter().any(|l| matches!(l.rel, Rel::Gt | Rel::Ge));
            let meets = |a: &Node, b: &Node| known.alike_how(a, b).unwrap_or_default();
            let ends = super::super::record::ChainEnds {
                first: meets(left, &ends.left),
                last: meets(right, &ends.right),
            };
            Some((
                s.just.line,
                Chain {
                    links: linked,
                    claim_turned,
                    as_written,
                    falls,
                    ends,
                },
            ))
        })
        .collect()
}

/// What each order step rests on (`CheckedTheorem::orders`), by the line of
/// its justification: each plain `inequalities` step and each requires line
/// whose reason is `inequalities`, the combination the checker decided it by
/// (`inequalities::combined`); each step with rows, the line its first row
/// writes out; each requires line naming one manipulation, the line it
/// manipulates. One with a fact that stands nowhere a backend can name it
/// is left out.
pub fn order_steps(
    thm: &Theorem,
    known: &Known,
    library: &Library,
) -> IndexMap<usize, OrderStep> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        if step.just.head.is(Method::Inequalities) {
            let recorded = match step.just.rows.is_empty() {
                true => combined_order(thm, &ClosureClaim::step(step), known, library),
                false => rows_order(thm, step, known, library),
            };
            if let Some(order) = recorded {
                out.insert(step.just.line, order);
            }
        }
        for req in &step.requires {
            let recorded = match req.is(Method::Inequalities) {
                true => combined_order(
                    thm,
                    &ClosureClaim::requires(step, req),
                    known,
                    library,
                ),
                false => manipulation_order(thm, step, req, known, library),
            };
            if let Some(order) = recorded {
                out.insert(req.line, order);
            }
        }
    }
    out
}

/// A fact a membership among an order step's facts implies
/// (`combined_order`), with the rule, and the fact it is implied by, by its
/// place; None for the member a claim said of every member is read at.
pub(super) struct ImpliedFact {
    pub(super) node: Node,
    pub(super) rule: Implication,
    pub(super) from: Option<usize>,
}

/// What a plain order claim rests on, read as `inequalities_hold` reads it
/// to decide it: each fact of the lines it cites, part by part, and what a
/// membership among them, or the member it is read at, implies.
pub(super) fn combined_order(
    thm: &Theorem,
    at: &ClosureClaim,
    known: &Known,
    library: &Library,
) -> Option<OrderStep> {
    let targets = &library.targets;
    let mut read = at.read(known, targets, false)?;
    read.read_at_member(known);
    let mut facts: Vec<Node> = Vec::new();
    let mut line_of: Vec<usize> = Vec::new();
    for (said, &line) in read.lines.iter().zip(&read.line_of) {
        for part in conjuncts(said) {
            facts.push(part);
            line_of.push(line);
        }
    }
    let mut implied: Vec<ImpliedFact> = Vec::new();
    for (i, part) in facts.iter().enumerate() {
        for (node, rule) in citing::implied_by(part, known.env, &known.sorts) {
            implied.push(ImpliedFact {
                node,
                rule,
                from: Some(i),
            });
        }
    }
    if let Some(member) = &read.member {
        for (node, rule) in citing::implied_by(member, known.env, &known.sorts) {
            implied.push(ImpliedFact {
                node,
                rule,
                from: None,
            });
        }
    }
    let labels = FloatLabels::new(IndexMap::new());
    let terms: Vec<Term> = facts.iter().map(|n| term_of_node(n, targets)).collect();
    let implied_terms: Vec<Term> = implied
        .iter()
        .map(|i| term_of_node(&i.node, targets))
        .collect();
    let fact_of = |source: inequalities::Source| -> Option<OrderFact> {
        match source {
            inequalities::Source::Cited(i) => {
                order_fact(thm, at, line_of[i], &facts[i], known, library)
            }
            // What a fact implies stands where the fact does, with the rule.
            inequalities::Source::Implied(j) => {
                let one = &implied[j];
                let Some(i) = one.from else {
                    return Some(OrderFact::Member {
                        implied: one.rule,
                        written: one.node.clone(),
                    });
                };
                match order_fact(thm, at, line_of[i], &facts[i], known, library)? {
                    OrderFact::Line(source) => Some(OrderFact::Line(FirstAt {
                        written: one.node.clone(),
                        implied: Some(one.rule),
                        ..source
                    })),
                    OrderFact::Requires {
                        line,
                        implied: None,
                    } => Some(OrderFact::Requires {
                        line,
                        implied: Some(one.rule),
                    }),
                    OrderFact::Define(define) => Some(OrderFact::Kind {
                        define,
                        implied: one.rule,
                        written: one.node.clone(),
                    }),
                    _ => None,
                }
            }
        }
    };
    let mut sentences = Vec::new();
    for sentence in &read.sentences {
        let claimed = term_of_node(sentence, targets);
        let combined = inequalities::combined(
            &claimed,
            &terms,
            &line_of,
            &implied_terms,
            &labels,
        )?;
        // A define the step cites is read written out, its name its value,
        // so its equation stands among what every part adds.
        let defines: Vec<OrderFact> = at
            .refs
            .iter()
            .filter(|r| thm.defines.iter().any(|d| d.label == **r))
            .map(|r| OrderFact::Define(r.clone()))
            .collect();
        let mut parts = Vec::new();
        for part in combined.parts {
            let restates = match part.restates {
                Some(r) => Some(OrderRestated {
                    by: fact_of(r.by)?,
                    turned: r.turned,
                }),
                None => None,
            };
            let mut uses: Vec<OrderFact> =
                part.uses.into_iter().map(fact_of).collect::<Option<_>>()?;
            for d in &defines {
                let named = |f: &OrderFact| matches!((f, d), (OrderFact::Define(a), OrderFact::Define(b)) if a == b);
                if !uses.iter().any(named) {
                    uses.push(d.clone());
                }
            }
            parts.push(OrderPart {
                uses,
                split: part.split.into_iter().map(fact_of).collect::<Option<_>>()?,
                restates,
                weakened: None,
            });
        }
        sentences.push(parts);
    }
    Some(OrderStep { sentences })
}

/// Where `fact`, of the line `line` among what `at` reads (`ClosureRead::
/// line_of`), stands: a sentence or part of a cited line, a cited define's
/// equation, or a requires line above. None where it stands in none of
/// those as one sentence.
pub(super) fn order_fact(
    thm: &Theorem,
    at: &ClosureClaim,
    line: usize,
    fact: &Node,
    known: &Known,
    library: &Library,
) -> Option<OrderFact> {
    let Some(r) = at.refs.get(line) else {
        let k = line - at.refs.len();
        let above = at.above.get(k)?;
        return (above.fact.sentences().len() == 1).then_some(OrderFact::Requires {
            line: k,
            implied: None,
        });
    };
    if thm.defines.iter().any(|d| d.label == *r) {
        return Some(OrderFact::Define(r.clone()));
    }
    // The line is read with every define the step cites written out, as
    // the step reads it; it is looked in first.
    let mut refs = vec![r.clone()];
    refs.extend(at.refs.iter().filter(|o| *o != r).cloned());
    super::super::citations::fact_at(at.step, &refs, None, fact, known, library)
        .filter(|found| found.line == *r)
        .map(OrderFact::Line)
}

/// What an `inequalities` step with rows rests on: the line its first row
/// writes out, and, where its last row weakens an order to a disequality,
/// which way the order runs.
pub(super) fn rows_order(
    thm: &Theorem,
    step: &Step,
    known: &Known,
    library: &Library,
) -> Option<OrderStep> {
    let written = rows(&step.just, &thm.path)?.ok()?;
    let RowReason::Cited(r) = &written.first()?.reason else {
        return None;
    };
    let read: Vec<Related> = written
        .iter()
        .map(|row| {
            let node = known.parse(&row.formula.formula().ok()?).ok()?;
            Related::of(&node)
        })
        .collect::<Option<_>>()?;
    // The relation of the line the first row writes out, as
    // `check_inequality_rows` finds it.
    let said = line_relations(step, r, known).into_iter().find(|line| {
        line.says_as_written(&read[0], known)
            || (!line.written && line.says(&read[0], known))
    })?;
    let first = order_line(thm, step, r, &said.said, known, library)?;
    let weakened = match (written.last().map(|w| &w.reason), read.as_slice()) {
        (Some(RowReason::Weakening), [.., above, last]) if last.rel == Rel::Ne => {
            Some(weakened_of(above.rel)?)
        }
        _ => None,
    };
    // Rows from a disequality turn it round and nothing more: the claim is
    // the line, turned where an odd number of rows turns it.
    if read[0].rel == Rel::Ne {
        let turns = written
            .iter()
            .filter(|w| matches!(w.reason, RowReason::Restate))
            .count();
        return Some(OrderStep {
            sentences: vec![vec![OrderPart {
                uses: Vec::new(),
                split: Vec::new(),
                restates: Some(OrderRestated {
                    by: first,
                    turned: turns % 2 == 1,
                }),
                weakened: None,
            }]],
        });
    }
    Some(OrderStep {
        sentences: vec![vec![OrderPart {
            uses: vec![first],
            split: Vec::new(),
            restates: None,
            weakened,
        }]],
    })
}

/// What a requires line naming one manipulation, `requires q ≠ 0:
/// weakening, from 2.1`, rests on: the relation of the line it cites that
/// the manipulation makes its fact of, as `check_requires_manipulations`
/// finds it. None of any other requires line.
pub(super) fn manipulation_order(
    thm: &Theorem,
    step: &Step,
    req: &Requires,
    known: &Known,
    library: &Library,
) -> Option<OrderStep> {
    let Ok(by) = &req.by else {
        return None;
    };
    let Head::Manipulation(made) = &by.head else {
        return None;
    };
    let [cited] = req.lines() else {
        return None;
    };
    let reason = made.as_row(&thm.path, req.line);
    let fact = Related::of(&known.whole_as_written(&req.fact)?)?;
    let term = match &reason {
        RowReason::Adding(t) | RowReason::Multiplying(t) => {
            Some(reason_term(&t.clone(), known).ok()?)
        }
        _ => None,
    };
    let targets = &library.targets;
    let line = line_relations(step, cited, known)
        .into_iter()
        .find(|line| {
            row_follows(line, &fact, &reason, term.as_ref(), known, targets)
        })?;
    let weakened = match (&reason, fact.rel) {
        (RowReason::Weakening, Rel::Ne) => Some(weakened_of(line.rel)?),
        _ => None,
    };
    Some(OrderStep {
        sentences: vec![vec![OrderPart {
            uses: vec![order_line(thm, step, cited, &line.said, known, library)?],
            split: Vec::new(),
            restates: None,
            weakened,
        }]],
    })
}

/// Where the relation `said` of the line `r` a step cites stands: the
/// line's sentence or part, or a define's equation.
pub(super) fn order_line(
    thm: &Theorem,
    step: &Step,
    r: &str,
    said: &Node,
    known: &Known,
    library: &Library,
) -> Option<OrderFact> {
    if thm.defines.iter().any(|d| d.label == r) {
        return Some(OrderFact::Define(r.to_string()));
    }
    // A line's facts are found as the checker reads them, in the standard
    // order.
    let r = r.to_string();
    let said = standard(said, &library.ctx);
    super::super::citations::fact_at(
        step,
        slice::from_ref(&r),
        None,
        &said,
        known,
        library,
    )
    .map(OrderFact::Line)
}

/// Which way the strict order a disequality is weakened from runs, read
/// from its left side; None of an order that is not strict.
pub(super) fn weakened_of(rel: Rel) -> Option<Weakened> {
    match rel {
        Rel::Lt => Some(Weakened::Below),
        Rel::Gt => Some(Weakened::Above),
        _ => None,
    }
}

/// How each `antisymmetry` step's two lines make its equation
/// (`CheckedTheorem::antisymmetric`), by the line of its justification: the
/// line that says the claim's left side is at most its right, and the line
/// that says the converse, as `check_antisymmetry` pairs them. One citing a
/// define is left out.
pub fn antisymmetries(
    thm: &Theorem,
    known: &Known,
    library: &Library,
) -> IndexMap<usize, Antisymmetric> {
    thm.steps
        .iter()
        .filter(|s| s.just.head.is(Method::Antisymmetry))
        .filter_map(|step| {
            let links = cited_links(thm, step, known, "antisymmetry").ok()?;
            let ([one, other], [r1, r2]) =
                (links.as_slice(), step.just.refs.as_slice())
            else {
                return None;
            };
            let claim = Related::of(&known.whole_as_written(&step.claim)?)?;
            // Each read from below: `b ≥ a` is `a ≤ b`.
            let low = |l: &Related| match l.rel {
                Rel::Ge => l.right.clone(),
                _ => l.left.clone(),
            };
            let (below, above) = match known.alike(&low(one), &claim.left) {
                true => ((one, r1), (other, r2)),
                false => ((other, r2), (one, r1)),
            };
            let at = |(link, r): (&Related, &String)| -> Option<FirstAt> {
                if thm.defines.iter().any(|d| d.label == *r) {
                    return None;
                }
                super::super::citations::fact_at(
                    step,
                    slice::from_ref(r),
                    None,
                    &standard(&link.said, &library.ctx),
                    known,
                    library,
                )
            };
            Some((
                step.just.line,
                Antisymmetric {
                    below: at(below)?,
                    above: at(above)?,
                },
            ))
        })
        .collect()
}

/// The chain a `transitivity` step's lines make, each line's right side the
/// next one's left side, written the same way. A line may be read from
/// either side, an order as its converse (`b > a` is `a < b`), and the chain
/// goes one way as its lines are read. The link from the first left side to
/// the last right side, or the defect.
pub(super) fn chain_of(
    thm: &Theorem,
    step: &Step,
    links: &[Related],
    known: &Known,
) -> Checked<Related> {
    let number = &step.number;
    let defect = |message: String| Problem::new(&thm.path, step.just.line, message);
    let chain = faced(thm, step, links, known)?;
    let Some(rel) = chain_rel(&chain) else {
        return Err(defect(format!(
            "step {number} chains orders going up and going down, which say nothing of its ends"
        )));
    };
    // The skeleton refuses a `transitivity` with no `from`.
    let (first, last) = (
        chain.first().expect("a chain's first line"),
        chain.last().expect("a chain's last line"),
    );
    Ok(Related {
        left: first.left.clone(),
        right: last.right.clone(),
        rel,
        said: last.said.clone(),
        written: true,
        turned: false,
    })
}

/// The links of a `transitivity` step's chain, each read the way the chain
/// goes (`chain_of`): its right side the next one's left side.
pub(super) fn faced(
    thm: &Theorem,
    step: &Step,
    links: &[Related],
    known: &Known,
) -> Checked<Vec<Related>> {
    let number = &step.number;
    let defect = |message: String| Problem::new(&thm.path, step.just.line, message);
    let mut chain: Vec<Related> = Vec::new();
    for (i, link) in links.iter().enumerate() {
        let link = match chain.last() {
            None => {
                // The first line faces the way the next line takes it.
                let next = links.get(i + 1);
                let turn = next.is_some_and(|n| {
                    !starts(&link.right, n, known) && starts(&link.left, n, known)
                });
                if turn {
                    link.turned()
                } else {
                    link.clone()
                }
            }
            Some(before) if known.alike(&before.right, &link.left) => link.clone(),
            Some(before) if known.alike(&before.right, &link.right) => link.turned(),
            Some(before) => {
                return Err(defect(format!(
                    "the lines step {number} chains do not meet: {} ends at {}, and {} starts from {}; a middle term is written the same way in both",
                    step.just.refs[i - 1],
                    known.print(&before.right),
                    step.just.refs[i],
                    known.print(&link.left)
                )));
            }
        };
        chain.push(link);
    }
    Ok(chain)
}

/// A `transitivity` step (`METHODS.md`, transitivity): the lines it cites
/// make a chain in the order cited, and the claim is the chain's first term
/// related to its last by the chain's relation, written either way round.
/// Where a link is an order, every atom of the chain is real.
pub fn check_transitivity(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in thm
        .steps
        .iter()
        .filter(|s| s.just.head.is(Method::Transitivity))
    {
        let checked = cited_links(thm, step, known, "transitivity")
            .and_then(|links| chain_of(thm, step, &links, known).map(|c| (links, c)));
        let (links, chained) = match checked {
            Ok(both) => both,
            Err(defect) => {
                report.problems.push(defect);
                continue;
            }
        };
        let Some(claim) = known.whole_as_written(&step.claim) else {
            continue; // `check_formulas` says it does not read
        };
        let reached = Related::of(&claim).is_some_and(|c| c.says(&chained, known));
        if !reached {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} claims {}, and the chain it cites gives {} {} {}",
                    step.number,
                    step.claim_text(),
                    known.print(&chained.left),
                    sign(chained.rel),
                    known.print(&chained.right)
                ),
            );
            continue;
        }
        if chained.rel != Rel::Eq {
            report_unreal(report, thm, step, &claim, &links, known, targets);
        }
    }
}

/// A calculation claims its chain's first term related to its last by the
/// chain's relation: `=` where every link is `=`, the way the chain goes
/// where a link is an order, strict where one is, and `≡ (mod n)` where a
/// link is a congruence (`SYNTAX.md`, calculation). A chain of `=` and `>`
/// claims `>`, not `≥`.
pub fn check_calculation_claims(report: &mut Report, thm: &Theorem, known: &Known) {
    for step in &thm.steps {
        let links = chain_links(&step.just, &thm.path);
        let Some(chained) = chain_claim(&links, known) else {
            continue;
        };
        let chained = match chained {
            ChainClaim::Ends(node) => node,
            ChainClaim::BothWays => {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} chains orders going up and going down, which say nothing of its ends",
                        step.number
                    ),
                );
                continue;
            }
        };
        let Some(claim) = known.whole_as_written(&step.claim) else {
            continue; // `check_formulas` says it does not read
        };
        if !known.alike(&claim, &chained) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} claims {}, and its chain gives {}",
                    step.number,
                    step.claim_text(),
                    known.print(&chained)
                ),
            );
        }
    }
}

/// Of each "if P then Q" the page writes, the sets P makes finite within Q
/// (`citing::finite::finite_under`).
pub fn finite_under(page: &PageReading) -> IndexMap<ByShape, FiniteSets> {
    finite::finite_under(page.entries().map(|(_, node)| node))
}

/// How each calculation's ends meet the step's claim, by the line of its
/// justification: `{a, b} = {k(m² − n²), 2kmn}` of a chain from {a, b} to
/// {2kmn, k(m² − n²)} is met with its listed members permuted.
pub fn calculation_meetings(thm: &Theorem, known: &Known) -> IndexMap<usize, Meeting> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        let links = chain_links(&step.just, &thm.path);
        let Some(ChainClaim::Ends(chained)) = chain_claim(&links, known) else {
            continue;
        };
        let Some(claim) = known.whole_as_written(&step.claim) else {
            continue;
        };
        if let Some(met) = known.alike_how(&claim, &chained) {
            out.insert(step.just.line, met);
        }
    }
    out
}

/// Where the first row of each `substitute` step with rows stands in the
/// line it cites, and how its last row meets the claim, by the line of the
/// step's justification (`CheckedTheorem::substitute_ends`), as
/// `check_substitute_rows` reads the rows. A step whose first row no line
/// says or whose last row does not meet the claim is left out; that check
/// reports it.
pub fn substitute_row_ends(
    thm: &Theorem,
    known: &Known,
) -> IndexMap<usize, super::super::record::RowEnds> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        let just = &step.just;
        if !just.head.is(Method::Substitute) || just.equation.is_some() {
            continue;
        }
        let Some(Ok(rows)) = substitute_rows(just, &thm.path) else {
            continue;
        };
        let (Some(first), Some(last)) = (rows.first(), rows.last()) else {
            continue;
        };
        let read = |w: &Written| known.read_as_written(&w.formula().ok()?);
        let (Some(start), Some(ends), Some(claim)) = (
            read(&first.formula),
            read(&last.formula),
            known.whole_as_written(&step.claim),
        ) else {
            continue;
        };
        let scope = known.scope(step);
        let first_at = scope.get(&first.cite).and_then(|stated| {
            let says = known.says(stated, &known.citing_step(step));
            let s = says.iter().find(|s| known.alike(&s.cited, &start))?;
            super::super::citations::placed(
                &first.cite,
                s,
                &says,
                known.sentence_count(stated),
            )
        });
        let other = said_otherwise(&ends, known.env, &known.sorts);
        let met = known
            .alike_how(&ends, &claim)
            .map(|m| (m, false))
            .or_else(|| {
                let other = other.as_ref()?;
                Some((known.alike_how(other, &claim)?, true))
            });
        if let Some((last, last_other_form)) = met {
            out.insert(
                just.line,
                super::super::record::RowEnds {
                    first: first_at,
                    last,
                    last_other_form,
                },
            );
        }
    }
    out
}

/// A `substitute` step's rows start from what the line the first row cites
/// says, written out, and end on the claim (`GRAMMAR.md`, substitute rows),
/// or on the claim in its other form (`rules::OTHER_FORMS`);
/// what each row after the first changes is its reason's to prove, which
/// `check_link_reasons` asks. A `substitute` writing no equation and no rows
/// says nothing.
pub fn check_substitute_rows(report: &mut Report, thm: &Theorem, known: &Known) {
    for step in &thm.steps {
        let just = &step.just;
        if !just.head.is(Method::Substitute) || just.equation.is_some() {
            continue;
        }
        if just.source.is_none() && just.rows.is_empty() {
            report.say(
                &thm.path,
                just.line,
                format!(
                    "step {} substitutes nothing: it writes its equation, `substitute e (line L)`, or its rows below it",
                    step.number
                ),
            );
            continue;
        }
        let rows = match substitute_rows(just, &thm.path) {
            None => continue,
            Some(Err(p)) => {
                report.say(&p.path, p.line, p.message);
                continue;
            }
            Some(Ok(rows)) => rows,
        };
        let read = |w: &Written| known.read_as_written(&w.formula().ok()?);
        let (Some(first), Some(last)) = (rows.first(), rows.last()) else {
            continue;
        };
        if let Some(written) = read(&first.formula) {
            let said = known.lines_say(step, &[first.cite.as_str()]);
            if !said.iter().any(|s| known.alike(s, &written)) {
                report.say(
                    &thm.path,
                    first.line,
                    format!(
                        "the first row of step {} writes {}, which {} does not say",
                        step.number, first.formula, first.cite
                    ),
                );
            }
        }
        let (Some(ends), Some(claim)) =
            (read(&last.formula), known.whole_as_written(&step.claim))
        else {
            continue; // `check_formulas` says it does not read
        };
        // The last row may write the claim in its other form, which says
        // the claim (`rules::OTHER_FORMS`).
        let other = said_otherwise(&ends, known.env, &known.sorts);
        let ends_on_claim = iter::once(&ends)
            .chain(other.as_ref())
            .any(|e| known.alike(e, &claim));
        if !ends_on_claim {
            report.say(
                &thm.path,
                last.line,
                format!(
                    "the last row of step {} writes {}, and the step claims {}",
                    step.number,
                    last.formula,
                    step.claim_text()
                ),
            );
        }
    }
}
