//! Whether a `membership` step holds (`METHODS.md`, membership): a term is
//! in a number system because its parts are. The term is walked as the
//! page says a membership once (`citing::within`: numerals, letters, and
//! what +, −, ·, unary −, a power to a numeral and / build from them), with
//! a quotient's divisor not zero by a line saying so, by being a numeral,
//! or by its parts (`nonzero`).
//! What that walk does not take apart is in a system where a fact says so,
//! where a cited equation puts it beside a term that is, or by the closure
//! table: an operation `rules::WHOLE` names by its target, and a sum over a
//! range by its term at every index.

use std::cell::RefCell;

use indexmap::IndexMap;

use super::terms::Targets;
use crate::citing::{
    index_system, nonzero_said_once, range_system, Introduced, NonzeroHow, OnceReason,
};
use crate::formula::symbol::Symbol;
use crate::formula::Node;
use crate::matching::{alike, standard, substitute_apart, Binding, Context};
use crate::notations::{
    ADDITIVE, APPLICATION, BY_CASES, DIVIDED, EQUALITY, FOR_ALL, INTEGER_RANGE,
    JUXTAPOSITION, MEMBERSHIP, MULTIPLICATIVE, NUMBER_SYSTEMS, NUMERAL, POWER, SUM,
    SUPERSCRIPT, UNARY_MINUS,
};
use crate::rules::{self, System};
use crate::{citing, matching};

/// What a membership is decided from: the facts the step cites and its
/// requires lines above it say, each part of them and what each membership
/// among them implies; the letters the page puts in a number system once;
/// the function types in scope; and the targets that say what operation a
/// term applies.
pub struct Facts<'a> {
    pub facts: &'a [Node],
    pub letters: Introduced,
    /// The letters that run over a range {a, …, b}, a sum's index among
    /// them, with the range they run over.
    pub ranged: IndexMap<String, Range>,
    /// The function types the claim rests on, `f : D → E`, which say a
    /// value of f is in E at a point of D: a type is cited for its values
    /// (`READERS.md`).
    pub typed: &'a [Node],
    /// The function types in scope, which a sum's terms may use as well:
    /// what a type says of a sum's term at each index is no value the page
    /// writes, and the build reads it from the scope there (`in_family`).
    pub in_sums: &'a [Node],
    /// The notations' and library functions' targets, which say what
    /// operation a term applies (`Targets::operation`).
    pub targets: &'a Targets,
    pub ctx: &'a Context,
}

/// The ends of a range {a, …, b} a letter runs over.
#[derive(Clone)]
pub struct Range {
    pub start: Node,
    pub end: Node,
}

/// How deep a cited equation may carry a term to another, so that two lines
/// saying t = u and u = t end.
const CARRIED: usize = 3;

/// How the page says a term is in a number system (`shown`): the one rule
/// every context asks a membership by (`READERS.md`, membership said once;
/// `SYNTAX.md`), as a derivation a backend proves the membership by.
#[derive(Clone, Debug)]
pub enum Shown {
    /// By the said-once walk (`citing::reason`): what the page says once,
    /// and what +, −, ·, /, powers and the rest build from it. Each part the
    /// walk took as it stands, a `Stated` or `Sum` leaf of `reason`, is in
    /// `taken` with how it is shown, in the order the walk took them.
    Walked {
        reason: OnceReason,
        taken: Vec<ShownPart>,
    },
    /// A cited line states it, of a system inside the one asked.
    Stated { line: Node },
    /// An operation the closure table says gives a whole number
    /// (`rules::WHOLE`, by the term's target): x mod n in ℕ₀ of x ∈ ℤ and
    /// n ∈ ℕ, its two parts in the systems the row asks.
    Whole { op: String, parts: Vec<ShownPart> },
    /// A sum over a range in ℝ or ℂ: by a cited line saying its term at
    /// every point of a set holding the range, or by its term at the index,
    /// the index in the system its range lies in.
    Summed {
        pointwise: Option<Node>,
        body: Option<Box<ShownPart>>,
    },
    /// A power a^e, a in the system and e in ℕ₀, where the walk does not
    /// take the exponent: 2^j ∈ ℤ where a cited line says j ∈ ℕ₀.
    Powered {
        base: Box<ShownPart>,
        exponent: Box<ShownPart>,
    },
    /// A function's value f(x), by the cited type `typed`, f : D → E, E in
    /// the system, and x in D.
    Valued { typed: Node, at: Box<InDomain> },
    /// A term by cases, each of its values in the system.
    Cased {
        value: Box<ShownPart>,
        otherwise: Box<ShownPart>,
    },
    /// A cited equation puts it beside `other`, which is in the system as
    /// `other_shown` says; `term_left` where the term is the left side.
    Beside {
        equation: Node,
        other: Node,
        term_left: bool,
        other_shown: Box<Shown>,
    },
}

/// A term with how the page says it is in `system`.
#[derive(Clone, Debug)]
pub struct ShownPart {
    pub term: Node,
    pub system: System,
    pub shown: Shown,
}

/// How a function's argument is in the domain its type writes
/// (`Shown::Valued`).
#[derive(Clone, Debug)]
pub enum InDomain {
    /// A domain that is a number system, the argument in it as shown.
    Within(Box<ShownPart>),
    /// The argument is a letter running over the range the domain writes:
    /// a sum's index, or a letter a range introduces.
    Ranged,
    /// A cited line says the argument is in the domain.
    Stated { line: Node },
}

/// How the page says `term` is in `system` by what `facts` give, the one
/// rule every context asks a membership by; None where it does not. The
/// term is read with its identity elements dropped (`SYNTAX.md`, an
/// identity element goes without saying), so 2^(d·1) is the power to the
/// letter d.
///
/// The said-once walk comes first, with only stated lines for the parts it
/// takes as they stand, since a line cited only for what is said once does
/// no work. Otherwise the walk takes each such part by any way the page
/// shows one (`otherwise`): a stated line, the closure, or an equation.
pub fn shown(term: &Node, system: System, facts: &Facts) -> Option<Shown> {
    let term = &matching::bare(term, facts.ctx);
    shown_at(term, system, facts, &Carry::from(CARRIED))
}

/// How far a cited equation may still carry a term on, and the terms the
/// equations so far carried it through, the first term first: a term is
/// not carried back to one of these, so x = y read the other way is not
/// taken for y.
#[derive(Clone)]
struct Carry {
    depth: usize,
    past: Vec<Node>,
}

impl Carry {
    /// At most `depth` equations, none passed through yet.
    fn from(depth: usize) -> Carry {
        Carry {
            depth,
            past: Vec::new(),
        }
    }
}

/// `shown`, as far as `carry` lets an equation carry a term on.
fn shown_at(
    term: &Node,
    system: System,
    facts: &Facts,
    carry: &Carry,
) -> Option<Shown> {
    walked(term, system, facts, carry, Leaves::Stated)
        .or_else(|| walked(term, system, facts, carry, Leaves::Any))
}

/// What the walk takes a part it does not take apart by (`walked`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Leaves {
    /// A cited line stating it.
    Stated,
    /// Any way the page shows a part (`otherwise`).
    Any,
}

/// `Shown::Walked` of `term`, each part the walk takes as it stands taken
/// as `leaves` says; None where the walk does not reach it.
fn walked(
    term: &Node,
    system: System,
    facts: &Facts,
    carry: &Carry,
    leaves: Leaves,
) -> Option<Shown> {
    let taken: RefCell<Vec<ShownPart>> = RefCell::new(Vec::new());
    let nonzero = |d: &Node| nonzero(d, facts);
    let said = |t: &Node, s: System| -> Option<OnceReason> {
        // A letter its introduction puts in the system is said once; a
        // line saying so too does no work, and the walk reads the letter.
        if t.is_name()
            && facts
                .letters
                .get(t.text.as_str())
                .is_some_and(|l| l.within(s))
        {
            return None;
        }
        let shown = match leaves {
            Leaves::Stated => {
                stated_by(t, s, facts).map(|line| Shown::Stated { line: line.clone() })
            }
            Leaves::Any => otherwise(t, s, facts, carry),
        }?;
        let reason = shown.reason();
        taken.borrow_mut().push(ShownPart {
            term: t.clone(),
            system: s,
            shown,
        });
        Some(reason)
    };
    let reason = citing::reason_within(term, system, &facts.letters, &nonzero, &said)?;
    Some(Shown::Walked {
        reason,
        taken: taken.into_inner(),
    })
}

/// How a part the walk does not take apart is in `system`: a cited line
/// states it; the closure puts it there, by an operation the closure table
/// names, a sum, a power, a function's value or a term by cases; or a cited
/// equation puts it beside a term that is. None where none does.
fn otherwise(
    term: &Node,
    system: System,
    facts: &Facts,
    carry: &Carry,
) -> Option<Shown> {
    if let Some(line) = stated_by(term, system, facts) {
        return Some(Shown::Stated { line: line.clone() });
    }
    closed(term, system, facts, carry).or_else(|| beside(term, system, facts, carry))
}

/// `term` in `system` by a row of the closure; None where none puts it
/// there.
fn closed(term: &Node, system: System, facts: &Facts, carry: &Carry) -> Option<Shown> {
    whole_shown(term, system, facts, carry)
        .or_else(|| summed_shown(term, system, facts, carry))
        .or_else(|| powered_shown(term, system, facts, carry))
        .or_else(|| valued_shown(term, system, facts, carry))
        .or_else(|| cased_shown(term, system, facts, carry))
}

/// `term` in `system` beside the other side of the first cited equation
/// whose other side is, and is no term `carry` already passed through.
fn beside(term: &Node, system: System, facts: &Facts, carry: &Carry) -> Option<Shown> {
    let mut on = Carry {
        depth: carry.depth.checked_sub(1)?,
        past: carry.past.clone(),
    };
    on.past.push(term.clone());
    besides_by(term, facts).into_iter().find_map(|b| {
        if on.past.iter().any(|t| same(t, b.other, facts.ctx)) {
            return None;
        }
        let other_shown = shown_at(b.other, system, facts, &on)?;
        Some(Shown::Beside {
            equation: b.equation.clone(),
            other: b.other.clone(),
            term_left: b.term_left,
            other_shown: Box::new(other_shown),
        })
    })
}

/// `term` in `system` as a `ShownPart`; None where it is not.
fn part_shown(
    term: &Node,
    system: System,
    facts: &Facts,
    carry: &Carry,
) -> Option<ShownPart> {
    Some(ShownPart {
        term: term.clone(),
        system,
        shown: shown_at(term, system, facts, carry)?,
    })
}

/// A term whose operation the closure table says gives a whole number
/// (`rules::WHOLE`), in a system holding ℕ₀, its parts in what the table
/// asks. The operation is read off the term's target, a notation's or a
/// library function's (`Targets::operation`).
fn whole_shown(
    term: &Node,
    system: System,
    facts: &Facts,
    carry: &Carry,
) -> Option<Shown> {
    if !System::N0.within(system) {
        return None;
    }
    let op = facts.targets.operation(term)?;
    let w = rules::WHOLE.iter().find(|w| w.op == op.label)?;
    let ([left, right], Some(left_in), Some(right_in)) = (
        op.parts.as_slice(),
        System::of_label(w.left.1),
        System::of_label(w.right.1),
    ) else {
        return None;
    };
    Some(Shown::Whole {
        op: w.op.to_string(),
        parts: vec![
            part_shown(left, left_in, facts, carry)?,
            part_shown(right, right_in, facts, carry)?,
        ],
    })
}

/// A term by cases, what a define by cases writes out to, in a system
/// where each of its values is: s(x) ∈ ℕ₀ where s is 0 or 1.
fn cased_shown(
    term: &Node,
    system: System,
    facts: &Facts,
    carry: &Carry,
) -> Option<Shown> {
    let (BY_CASES, [value, _, otherwise]) = (term.notation(), term.children.as_slice())
    else {
        return None;
    };
    Some(Shown::Cased {
        value: Box::new(part_shown(value, system, facts, carry)?),
        otherwise: Box::new(part_shown(otherwise, system, facts, carry)?),
    })
}

/// A power a^e in a system the closure table closes under powers, a in it
/// and e in ℕ₀: 2^j ∈ ℤ where j ∈ ℕ₀.
fn powered_shown(
    term: &Node,
    system: System,
    facts: &Facts,
    carry: &Carry,
) -> Option<Shown> {
    let (POWER | SUPERSCRIPT, [base, exponent]) =
        (term.notation(), term.children.as_slice())
    else {
        return None;
    };
    rules::closed("cexp", system.label())?;
    Some(Shown::Powered {
        exponent: Box::new(part_shown(exponent, System::N0, facts, carry)?),
        base: Box::new(part_shown(base, system, facts, carry)?),
    })
}

/// A function's value f(x) in a system holding E, where a cited type says
/// `f : D → E` and x is in D.
fn valued_shown(
    term: &Node,
    system: System,
    facts: &Facts,
    carry: &Carry,
) -> Option<Shown> {
    let (APPLICATION, [f, at]) = (term.notation(), term.children.as_slice()) else {
        return None;
    };
    facts.typed.iter().find_map(|t| {
        let [g, domain, codomain] = t.children.as_slice() else {
            return None;
        };
        if !same(g, f, facts.ctx)
            || !codomain_system(codomain).is_some_and(|s| s.within(system))
        {
            return None;
        }
        Some(Shown::Valued {
            typed: t.clone(),
            at: Box::new(in_domain_shown(at, domain, facts, carry)?),
        })
    })
}

/// How `x` is in the set `domain` a function is typed over: in a number
/// system as shown, by running over the range the domain writes, or by a
/// cited line saying so.
fn in_domain_shown(
    x: &Node,
    domain: &Node,
    facts: &Facts,
    carry: &Carry,
) -> Option<InDomain> {
    if domain.notation() == NUMBER_SYSTEMS {
        let s = System::of_sign(&domain.text)?;
        return Some(InDomain::Within(Box::new(part_shown(x, s, facts, carry)?)));
    }
    let runs_over = x.is_name()
        && facts.ranged.get(x.text.as_str()).is_some_and(|r| {
            matches!(domain.children.as_slice(), [a, b]
                if domain.notation() == INTEGER_RANGE
                    && same(a, &r.start, facts.ctx)
                    && same(b, &r.end, facts.ctx))
        });
    if runs_over {
        return Some(InDomain::Ranged);
    }
    facts
        .facts
        .iter()
        .find(|f| {
            f.notation() == MEMBERSHIP
                && matches!(f.children.as_slice(), [y, set]
                    if same(y, x, facts.ctx) && same(set, domain, facts.ctx))
        })
        .map(|line| InDomain::Stated { line: line.clone() })
}

/// A sum over a range in ℝ or ℂ, its term in that system at every index:
/// the index is in the system its range lies in (`rules::RANGE_WITHIN`), and
/// a term dividing by something that holds the index is one a fact says at
/// every point of a set holding the range (`SYNTAX.md`). The function types
/// in scope say what a type says of the term at each index.
fn summed_shown(
    term: &Node,
    system: System,
    facts: &Facts,
    carry: &Carry,
) -> Option<Shown> {
    let sum = Summed::of(term)?;
    if !matches!(system, System::R | System::C) {
        return None;
    }
    // A line saying the term at every index of the sum says the sum is a
    // number, whatever the term is; a term dividing by the index is so only
    // by such a line, since nothing else says its divisor is not zero.
    if let Some(line) = facts
        .facts
        .iter()
        .find(|f| said_pointwise(f, &sum, system, facts.ctx))
    {
        return Some(Shown::Summed {
            pointwise: Some(line.clone()),
            body: None,
        });
    }
    let mut letters = facts.letters.clone();
    if let Some(inside) = index_system(sum.start) {
        letters.insert(sum.index.to_string(), inside);
    }
    if divides_by(sum.body, sum.index, &letters) {
        return None;
    }
    let mut ranged = facts.ranged.clone();
    ranged.insert(
        sum.index.to_string(),
        Range {
            start: sum.start.clone(),
            end: sum.end.clone(),
        },
    );
    let typed: Vec<Node> = facts.typed.iter().chain(facts.in_sums).cloned().collect();
    let at = Facts {
        facts: facts.facts,
        letters,
        ranged,
        typed: &typed,
        in_sums: facts.in_sums,
        targets: facts.targets,
        ctx: facts.ctx,
    };
    Some(Shown::Summed {
        pointwise: None,
        body: Some(Box::new(part_shown(sum.body, system, &at, carry)?)),
    })
}

/// Whether `term` is in `system` by what `facts` give (`shown`).
pub fn holds(term: &Node, system: System, facts: &Facts) -> bool {
    shown(term, system, facts).is_some()
}

/// Whether the page says `term` is in `system`, which a method's atoms ask
/// of it: the one rule (`shown`).
pub fn said(term: &Node, system: System, facts: &Facts) -> bool {
    holds(term, system, facts)
}

/// The fact stating `term` is in a number system inside `system`; None
/// where none does.
fn stated_by<'f>(term: &Node, system: System, facts: &'f Facts) -> Option<&'f Node> {
    facts.facts.iter().find(|f| {
        f.notation() == MEMBERSHIP
            && matches!(f.children.as_slice(), [held, set]
                if set.notation() == NUMBER_SYSTEMS
                    && same(held, term, facts.ctx)
                    && System::of_sign(&set.text).is_some_and(|k| k.within(system)))
    })
}

/// The terms the equations among the facts put `term` beside: b of a = b
/// where a is `term`, and a where b is.
fn besides<'f>(term: &Node, facts: &'f Facts) -> Vec<&'f Node> {
    besides_by(term, facts)
        .into_iter()
        .map(|b| b.other)
        .collect()
}

/// A term an equation among the facts puts beside another.
struct Beside<'f> {
    /// The equation, as the facts hold it.
    equation: &'f Node,
    /// Its other side.
    other: &'f Node,
    /// Whether the term is the equation's left side: `a·f(a)` of
    /// `a·f(a) = f(a)·a`.
    term_left: bool,
}

/// `besides`, each with the equation that puts the term there.
fn besides_by<'f>(term: &Node, facts: &'f Facts) -> Vec<Beside<'f>> {
    facts
        .facts
        .iter()
        .filter_map(|f| match (f.notation(), f.children.as_slice()) {
            (EQUALITY, [a, b]) if same(a, term, facts.ctx) => Some(Beside {
                equation: f,
                other: b,
                term_left: true,
            }),
            (EQUALITY, [a, b]) if same(b, term, facts.ctx) => Some(Beside {
                equation: f,
                other: a,
                term_left: false,
            }),
            _ => None,
        })
        .collect()
}

/// Whether an atom of an `algebra` or `inequalities` step is in `system`
/// (`METHODS.md`, membership, Facts in: the test every method's side
/// conditions are asked by): the one rule (`shown`), as citing a(0) = 0
/// says a(0) is a number.
pub fn atom_held(term: &Node, system: System, facts: &Facts) -> bool {
    holds(term, system, facts)
}

impl Shown {
    /// The walk's reason for a term so shown (`citing::OnceReason`): the
    /// walk's own; a sum's; a whole number's row of the closure as its
    /// operation built from its parts, each by its own reason, as a backend
    /// reads a row (x mod n of x ∈ ℤ and n ∈ ℕ); and any other a part the
    /// walk takes as it stands.
    pub fn reason(&self) -> OnceReason {
        match self {
            Shown::Walked { reason, .. } => reason.clone(),
            Shown::Summed { .. } => OnceReason::Sum,
            Shown::Whole { parts, .. } => {
                OnceReason::Built(parts.iter().map(|p| p.shown.reason()).collect())
            }
            _ => OnceReason::Stated,
        }
    }

    /// How the term itself is held where the walk took it as it stands, its
    /// one part: a stated line, a row of the closure or a cited equation.
    /// The derivation itself where the walk took the term apart, or the
    /// derivation is no walk.
    pub fn as_held(&self) -> &Shown {
        match self {
            // The walk took the term itself where its reason is its one
            // part's own.
            Shown::Walked { reason, taken } => match taken.as_slice() {
                [part] if part.shown.reason() == *reason => &part.shown,
                _ => self,
            },
            _ => self,
        }
    }
}

/// Whether a bare `from` line reads `term ∈ system` off its facts
/// (`SYNTAX.md`): the one rule (`shown`).
pub fn read_off(term: &Node, system: System, facts: &Facts) -> bool {
    holds(term, system, facts)
}

fn member(term: &Node, system: System, facts: &Facts, depth: usize) -> bool {
    shown_at(term, system, facts, &Carry::from(depth)).is_some()
}

/// Whether two terms are one, each read in its standard spelling as
/// `Known::alike` reads them: x² is x^2, whichever way a line was read.
fn same(a: &Node, b: &Node, ctx: &Context) -> bool {
    alike(
        &standard(a, ctx),
        &standard(b, ctx),
        ctx,
        &IndexMap::new(),
        &IndexMap::new(),
    )
}

/// Whether a divisor is not zero: a numeral other than zero or a term the
/// page says once is a positive integer (`nonzero_said_once`), a fact
/// saying it, as `d ≠ 0` either way round or as a sign, `0 < d` or `d < 0`,
/// or its parts: a product, a quotient, a negation or a power to a numeral
/// is not zero when its parts are (`ELABORATION.md`, the divisor's order).
pub fn nonzero(divisor: &Node, facts: &Facts) -> bool {
    citing::nonzero_said(divisor, &facts.letters, facts.facts, facts.ctx)
}

/// Each part of a divisor `nonzero` reads as not zero, with how: each part
/// of a product, a quotient, a negation or a power to a numeral, taken
/// apart as far as each part is not zero, which is how a backend clearing
/// the division meets them, 1·N! as 1 and N!; or the divisor whole, where
/// one reason holds of it and not of each part. None where neither holds.
pub fn nonzero_how<'f>(
    divisor: &Node,
    facts: &'f Facts,
) -> Option<Vec<(Node, NonzeroHow<'f>)>> {
    let parts: Vec<&Node> = match (
        divisor.notation(),
        divisor.spelling(),
        divisor.children.as_slice(),
    ) {
        (MULTIPLICATIVE | JUXTAPOSITION, _, [a, b]) | (_, DIVIDED, [a, b]) => {
            vec![a, b]
        }
        (UNARY_MINUS, _, [a]) => vec![a],
        (POWER | SUPERSCRIPT, _, [a, e]) if e.notation() == NUMERAL => vec![a],
        _ => Vec::new(),
    };
    let apart: Option<Vec<(Node, NonzeroHow<'f>)>> = (!parts.is_empty())
        .then(|| {
            let mut out = Vec::new();
            for p in &parts {
                out.extend(nonzero_how(p, facts)?);
            }
            Some(out)
        })
        .flatten();
    apart.or_else(|| {
        said_nonzero_how(divisor, facts).map(|how| vec![(divisor.clone(), how)])
    })
}

/// How the page says a divisor is not zero once, or which fact says it;
/// None where neither does (`said_nonzero`).
fn said_nonzero_how<'f>(divisor: &Node, facts: &'f Facts) -> Option<NonzeroHow<'f>> {
    citing::nonzero_said_how(divisor, &facts.letters, facts.facts, facts.ctx)
}

/// The first part of `term` nothing in `facts` says is in `system`, as a
/// refusal names it: an atom of the term (`Parts`), or where a cited
/// equation puts that atom beside another term, the first part of that
/// term not said, which is why the equation did not carry it. None where
/// every atom holds.
pub fn unsaid_atom(term: &Node, system: System, facts: &Facts) -> Option<Node> {
    unsaid_carried(term, system, facts, CARRIED)
}

fn unsaid_carried(
    term: &Node,
    system: System,
    facts: &Facts,
    depth: usize,
) -> Option<Node> {
    let atom = Parts::of(term)
        .atoms
        .into_iter()
        .find(|a| !member(a, system, facts, depth))?;
    if depth > 0 {
        if let Some(inner) = besides(&atom, facts)
            .into_iter()
            .find_map(|other| unsaid_carried(other, system, facts, depth - 1))
        {
            return Some(inner);
        }
    }
    Some(atom)
}

/// The part of a divisor `nonzero` finds nothing saying is not zero: the
/// divisor itself, or where it is a product, a quotient, a negation or a
/// power to a numeral, the first of its parts that is not. None where it is
/// not zero.
pub fn unsaid_part(divisor: &Node, facts: &Facts) -> Option<Node> {
    if nonzero(divisor, facts) {
        return None;
    }
    let parts: Vec<&Node> = match (
        divisor.notation(),
        divisor.spelling(),
        divisor.children.as_slice(),
    ) {
        (MULTIPLICATIVE | JUXTAPOSITION, _, [a, b]) | (_, DIVIDED, [a, b]) => {
            vec![a, b]
        }
        (UNARY_MINUS, _, [a]) => vec![a],
        (POWER | SUPERSCRIPT, _, [a, e]) if e.notation() == NUMERAL => vec![a],
        _ => Vec::new(),
    };
    parts
        .iter()
        .find_map(|p| unsaid_part(p, facts))
        .or_else(|| Some(divisor.clone()))
}

/// How `facts` hold a part the walk takes as it stands in `system`, as
/// `shown` takes such a part (`otherwise`): a stated line, a row of the
/// closure, or a cited equation, each with how its own parts are shown.
/// None where none does.
pub fn held_shown(term: &Node, system: System, facts: &Facts) -> Option<Shown> {
    otherwise(term, system, facts, &Carry::from(CARRIED))
}

impl Shown {
    /// Each term and line the derivation writes, for `f` to rewrite in
    /// place: the written record writes out what the checked one reads.
    pub fn nodes_mut(&mut self, f: &mut dyn FnMut(&mut Node)) {
        match self {
            Shown::Walked { taken, .. } => {
                for part in taken {
                    part.nodes_mut(f);
                }
            }
            Shown::Stated { line } => f(line),
            Shown::Whole { parts, .. } => {
                for part in parts {
                    part.nodes_mut(f);
                }
            }
            Shown::Summed { pointwise, body } => {
                if let Some(line) = pointwise {
                    f(line);
                }
                if let Some(body) = body {
                    body.nodes_mut(f);
                }
            }
            Shown::Powered { base, exponent } => {
                base.nodes_mut(f);
                exponent.nodes_mut(f);
            }
            Shown::Valued { typed, at } => {
                f(typed);
                match at.as_mut() {
                    InDomain::Within(part) => part.nodes_mut(f),
                    InDomain::Ranged => {}
                    InDomain::Stated { line } => f(line),
                }
            }
            Shown::Cased { value, otherwise } => {
                value.nodes_mut(f);
                otherwise.nodes_mut(f);
            }
            Shown::Beside {
                equation,
                other,
                other_shown,
                ..
            } => {
                f(equation);
                f(other);
                other_shown.nodes_mut(f);
            }
        }
    }
}

impl ShownPart {
    /// `Shown::nodes_mut`, of the term too.
    pub fn nodes_mut(&mut self, f: &mut dyn FnMut(&mut Node)) {
        f(&mut self.term);
        self.shown.nodes_mut(f);
    }
}

/// The type among `facts`, `f : X → Y`, that puts `term`, a function's
/// value f(a) at a point of X, in `system`; None where none does.
pub fn value_typed_by<'f>(
    term: &Node,
    system: System,
    facts: &'f Facts,
) -> Option<&'f Node> {
    let (APPLICATION, [f, at]) = (term.notation(), term.children.as_slice()) else {
        return None;
    };
    facts.typed.iter().find(|t| {
        let [g, domain, codomain] = t.children.as_slice() else {
            return false;
        };
        same(g, f, facts.ctx)
            && codomain_system(codomain).is_some_and(|s| s.within(system))
            && in_domain_shown(at, domain, facts, &Carry::from(0)).is_some()
    })
}

/// The number system a function's codomain puts its values in: the system
/// itself, or the one a range lies in by the declared table, ℕ for
/// {1, …, b} (`range_system`).
fn codomain_system(codomain: &Node) -> Option<System> {
    match codomain.notation() {
        NUMBER_SYSTEMS => System::of_sign(&codomain.text),
        INTEGER_RANGE => range_system(codomain),
        _ => None,
    }
}

/// The atoms of a term and the divisors it writes, as `algebra` reads it
/// (`METHODS.md`): it is taken apart where it is built by +, −, ·, unary −,
/// / and a power to a numeral, and every other part, a letter included, is
/// an atom. A numeral is neither.
pub struct Parts {
    pub atoms: Vec<Node>,
    pub divisors: Vec<Node>,
}

impl Parts {
    pub fn of(term: &Node) -> Parts {
        let mut out = Parts {
            atoms: Vec::new(),
            divisors: Vec::new(),
        };
        out.take(term);
        out
    }

    fn take(&mut self, term: &Node) {
        let numeral_exponent = |e: &Node| e.notation() == NUMERAL;
        match (term.notation(), term.spelling(), term.children.as_slice()) {
            (NUMERAL, _, _) => {}
            (ADDITIVE | JUXTAPOSITION, _, [a, b]) => {
                self.take(a);
                self.take(b);
            }
            (_, DIVIDED, [a, b]) => {
                self.take(a);
                self.take(b);
                if b.notation() != NUMERAL {
                    self.divisors.push(b.clone());
                }
            }
            (MULTIPLICATIVE, _, [a, b]) => {
                self.take(a);
                self.take(b);
            }
            (UNARY_MINUS, _, [a]) => self.take(a),
            (POWER | SUPERSCRIPT, _, [a, e]) if numeral_exponent(e) => self.take(a),
            _ => self.atoms.push(term.clone()),
        }
    }
}

/// Whether `term` divides by something holding the letter `index` that the
/// page does not say once is a positive integer, `letters` holding the
/// index's own system (`citing::nonzero_said_once`). A line saying `b ≠ 0`
/// speaks of the proof's letters, not of every value of the index, so no
/// fact is asked.
pub fn divides_by(term: &Node, index: &str, letters: &Introduced) -> bool {
    term.walk().iter().any(|part| {
        part.spelling() == DIVIDED
            && part.children.get(1).is_some_and(|d| {
                d.names().contains(index) && !nonzero_said_once(d, letters)
            })
    })
}

/// A sum over a range, its parts by name.
pub struct Summed<'n> {
    pub index: &'n str,
    pub body: &'n Node,
    pub start: &'n Node,
    pub end: &'n Node,
}

impl<'n> Summed<'n> {
    /// `term` as a sum over a range, where it is one.
    pub fn of(term: &'n Node) -> Option<Summed<'n>> {
        let (SUM, [index, start, end, body]) =
            (term.notation(), term.children.as_slice())
        else {
            return None;
        };
        index.is_name().then_some(Summed {
            index: &index.text,
            body,
            start,
            end,
        })
    }
}

/// Whether `fact` says, at every point of a set holding the sum's range,
/// that its term is in a system inside `system`: `for all k ∈ ℕ, 1/k ∈ ℝ`
/// for Σ(k = 1 to n) 1/k.
pub fn said_pointwise(
    fact: &Node,
    sum: &Summed,
    system: System,
    ctx: &Context,
) -> bool {
    let (FOR_ALL, [bound, set, body]) = (fact.notation(), fact.children.as_slice())
    else {
        return false;
    };
    let (MEMBERSHIP, [value, into]) = (body.notation(), body.children.as_slice())
    else {
        return false;
    };
    let holds_range = match set.notation() {
        NUMBER_SYSTEMS => {
            System::maybe_within(index_system(sum.start), System::of_sign(&set.text))
        }
        INTEGER_RANGE => matches!(set.children.as_slice(), [a, b]
            if same(a, sum.start, ctx) && same(b, sum.end, ctx)),
        _ => false,
    };
    let lands = into.notation() == NUMBER_SYSTEMS
        && System::of_sign(&into.text).is_some_and(|s| s.within(system));
    let at = Binding::from([(Symbol::of(sum.index), bound.clone())]);
    holds_range && lands && same(&substitute_apart(sum.body, &at, ctx), value, ctx)
}
