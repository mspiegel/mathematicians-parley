//! A membership in a number system that the page says once, where a letter
//! is introduced, and no step writes again (`READERS.md`, membership said
//! once): a numeral, a letter in the set its introducing line names and the
//! number systems containing that one, a distance between two points and an
//! angle at three in ℝ and ℂ, a sine, cosine or exponential of a real
//! argument in ℝ and ℂ, and a term built from those by +, −,
//! ·, negation, a power to a numeral or to a letter in ℕ or ℕ₀, and a
//! quotient whose divisor a fact says is not zero.
//!
//! The rule is written once, in `reason`, over a view of a term both tools
//! give (`OnceAsk`): the page's sentences here, and the build's kernel
//! terms in `Elaborator::introduced_membership`, which proves what `reason`
//! answers. So the two tools agree on which memberships a step need not
//! write.

use std::collections::BTreeSet;

use indexmap::IndexMap;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{pow, One, Signed, ToPrimitive, Zero};

use crate::formula::notation_id::NotationId;
use crate::formula::page::template;
use crate::formula::symbol::Symbol;
use crate::formula::{ByShape, Node, Sort, Sorts};
use crate::matching::{alike, expand, standard, substitute_apart, Binding, FxIndexSet};
use crate::notations::{
    ABSOLUTE_VALUE, APPLICATION, APPLICATION_TO_TWO, DEGREES, DISTANCE, DIVIDED,
    EQUALITY, EULER, FACTORIAL, GREATER, IN, INTEGER_RANGE, JUXTAPOSITION, LESS,
    LOGICAL_NOT, MAP, MEMBERSHIP, MINUS, MOD, MULTIPLICATIVE, NUMBER_SYSTEMS, NUMERAL,
    PI, PLUS, POWER, SQUARE_ROOT, SUM, SUPERSCRIPT, TIMES, UNARY_MINUS, WITHOUT,
};
use crate::rules::{self, lookup, System};
use crate::sorts::types_a_function;

use super::library::Library;
use super::parts::{Parts, SaidOnceFact};
use crate::checker::record::{StatedAt, SuppliedBy};
use crate::formula::page;
use crate::matching::Context;
use crate::methods::reals::{trig_value, Trig};
use crate::methods::terms::Targets;
use crate::methods::{membership, reals, surds};

/// The number system each letter is introduced in, by the letter as the
/// page writes it.
pub type Introduced = IndexMap<String, System>;

/// The letter and number system a sentence `x ∈ ℝ` introduces; None for
/// any other sentence, a term in place of the letter included.
pub fn introduction(said: &Node) -> Option<(String, System)> {
    let [letter, set] = said.children.as_slice() else {
        return None;
    };
    if said.spelling() != IN || !letter.is_name() {
        return None;
    }
    Some((letter.text.to_string(), set_system(set)?))
}

/// The number system a member of `set` is in: a number system's own, a
/// range's (`range_system`) or an interval's (`interval_system`), and the
/// same for each with points taken out, since a member of S ∖ {c} is a
/// member of S: x ∈ ℝ ∖ {0} is in ℝ. None for a set none of these is.
pub fn set_system(set: &Node) -> Option<System> {
    if let ([from, _], true) = (set.children.as_slice(), set.spelling() == WITHOUT) {
        return set_system(from);
    }
    match set.notation() {
        NUMBER_SYSTEMS => System::of_sign(&set.text),
        INTEGER_RANGE => range_system(set),
        _ => interval_system(set),
    }
}

/// The number system the declared table puts an interval's members in, ℝ
/// for (a, b) and [a, b] (`rules::INTERVAL_WITHIN`, which the elaborator
/// reads as well), and for an interval with points taken out, (a, b) ∖
/// {c}, whose members are its members; None for a set that is no interval.
/// It is the interval's shape that says so: that a closed interval's ends
/// are numbers is checked where the interval is written
/// (`closed_interval`).
pub fn interval_system(set: &Node) -> Option<System> {
    if let ([from, _], true) = (set.children.as_slice(), set.spelling() == WITHOUT) {
        return interval_system(from);
    }
    let interval = rules::INTERVAL_WITHIN
        .iter()
        .find(|i| NotationId::of(i.notation) == set.notation())?;
    System::of_label(interval.system)
}

/// An interval whose ends the declared table asks are in a number system,
/// [a, b] in ℝ, with points taken out or not: the interval itself, its
/// points not taken out, and the system its ends are in. None for any
/// other set.
pub fn closed_interval(set: &Node) -> Option<(&Node, System)> {
    if let ([from, _], true) = (set.children.as_slice(), set.spelling() == WITHOUT) {
        return closed_interval(from);
    }
    let interval = rules::INTERVAL_WITHIN
        .iter()
        .find(|i| NotationId::of(i.notation) == set.notation())?;
    Some((set, System::of_label(interval.ends?)?))
}

/// The least number system the declared table puts a range {a, …, b} in:
/// ℕ from 1, ℕ₀ from 0, and ℤ from anywhere (`rules::RANGE_WITHIN`, which
/// the elaborator reads as well).
pub fn range_system(range: &Node) -> Option<System> {
    let start = range.children.first()?;
    let begins = (start.notation() == NUMERAL)
        .then(|| {
            start
                .text
                .parse::<u32>()
                .ok()
                .and_then(rules::numeral_label)
        })
        .flatten();
    rules::RANGE_WITHIN
        .iter()
        .find(|row| row.first.is_none() || row.first == begins)
        .and_then(|row| System::of_label(row.system))
}

/// The memberships the page says once of the terms `parts` names, in every
/// number system each is in, and in the plane for the letters `in_plane`
/// introduces as points, laid onto its facts. A letter is introduced by
/// `introduced` or by a fact of `parts` saying it is in a number system.
/// They are added after what a membership implies is read (`finished`), so
/// that `let k ∈ ℕ` gives k ∈ ℝ here and never k ≥ 1. A sum is said once
/// by its term at every index, with the function types in scope, `typed`
/// (`sum_said_once`).
///
/// What a term is said once to be is what the term it names is, so where
/// the citation keeps its defines by name (`Parts::unfolds`) the walk reads
/// the parts with each read out, and the memberships it finds are of the
/// terms read out: s with s := (a + b)/2 is a number as (a + b)/2 is.
pub fn said_once(
    parts: &mut Parts,
    introduced: &Introduced,
    in_plane: &BTreeSet<String>,
    typed: &[Node],
    library: &Library,
    sorts: &Sorts,
) {
    let Some(unfolds) = parts.unfolds.clone() else {
        return said_once_read(parts, introduced, in_plane, typed, library, sorts);
    };
    let read = |n: &Node| standard(&expand(n, &unfolds.defines), &library.ctx);
    let mut view = Parts {
        facts: parts.facts.iter().map(read).collect(),
        claims: parts.claims.iter().map(read).collect(),
        seed: parts.seed.iter().map(|(k, v)| (*k, read(v))).collect(),
        said_once: Vec::new(),
        unfolds: None,
    };
    let before = view.facts.len();
    said_once_read(&mut view, introduced, in_plane, typed, library, sorts);
    parts.facts.extend(view.facts.drain(before..));
    parts.said_once.extend(view.said_once);
}

/// `said_once` of parts whose terms are as the walk reads them.
fn said_once_read(
    parts: &mut Parts,
    introduced: &Introduced,
    in_plane: &BTreeSet<String>,
    typed: &[Node],
    library: &Library,
    sorts: &Sorts,
) {
    // The letters a fact puts in a number system are numbers too, as the
    // bound j of "for all j ∈ {1, …, m}" is, read at a member.
    let mut letters = introduced.clone();
    for f in &parts.facts {
        let [term, set] = f.children.as_slice() else {
            continue;
        };
        if f.notation() != MEMBERSHIP || set.notation() != NUMBER_SYSTEMS {
            continue;
        }
        if let (true, Some(system)) = (term.is_name(), System::of_sign(&set.text)) {
            letters.entry(term.text.to_string()).or_insert(system);
        }
    }
    // Whether and how the page says a membership is the one rule's
    // (`membership::shown`): a letter in the system its introduction names,
    // a line that narrows it, q ∈ ℕ₀ of a q a `let` put in ℤ, being a part
    // the walk takes as it stands. A function's type the parts state is
    // cited for its values; one in scope gives a sum's terms (`READERS.md`).
    let cited_types: Vec<Node> = parts
        .facts
        .iter()
        .filter(|f| types_a_function(f))
        .cloned()
        .collect();
    let ctx = &library.ctx;
    let given = membership::Facts {
        facts: &parts.facts,
        letters: introduced.clone(),
        ranged: IndexMap::new(),
        typed: &cited_types,
        in_sums: typed,
        targets: &library.targets,
        ctx,
    };
    let mut local = sorts.clone();
    local.insert("x".into(), Sort::of("number"));
    // The code's own forms, read once here and filled with each term at x
    // and the set at S. A notation database that does not declare what one
    // writes says nothing here, and its own checks report what it lacks.
    let fill =
        |made: &Node, put: Binding| standard(&substitute_apart(made, &put, ctx), ctx);
    // S is read as the number system that fills it, whatever the page's S
    // is: each system's set and the membership in it, read once.
    let systems: Vec<Option<SystemForm>> = rules::SYSTEM_OF
        .iter()
        .map(|(sign, _)| system_form(sign, &local, library))
        .collect();
    let seeded: Vec<Node> = parts.seed.values().cloned().collect();
    let mut seen: FxIndexSet<ByShape> = FxIndexSet::default();
    let mut out = Vec::new();
    let mut walked = Vec::new();
    for node in parts
        .facts
        .iter()
        .chain(&parts.claims)
        .chain(&seeded)
        .flat_map(|n| n.walk())
    {
        // A letter a fact puts in a number system is a number, as the bound
        // j of "for all j ∈ {1, …, m}" is, read at a member.
        let number = node.sort.is("number")
            || (node.is_name() && letters.contains_key(node.text.as_str()));
        if !number || !seen.insert(node.by_shape()) {
            continue;
        }
        for ((_, label), form) in rules::SYSTEM_OF.iter().zip(&systems) {
            let Some(system) = System::of_label(label) else {
                continue;
            };
            let (Some(shown), Some(SystemForm { set, member })) =
                (membership::shown(&node, system, &given), form)
            else {
                continue;
            };
            let membership::Shown::Walked { reason, taken } = &shown else {
                continue;
            };
            let fact = fill(
                member,
                Binding::from([
                    (Symbol::of("x"), node.clone()),
                    (Symbol::of("S"), set.clone()),
                ]),
            );
            out.push(fact.clone());
            // Each part the walk took as it stands, which the checker places
            // where it records the walk: one a line states, in the system the
            // line puts it in, n ∈ ℕ of an n asked in ℤ.
            let stated = taken
                .iter()
                .map(|part| StatedAt {
                    term: part.term.clone(),
                    system: line_system(&part.shown).unwrap_or(part.system),
                    by: SuppliedBy::Unstated,
                })
                .collect();
            walked.push(SaidOnceFact {
                fact,
                reason: reason.clone(),
                stated,
                shown: shown.clone(),
            });
        }
    }
    drop(given);
    out.extend(points_in_plane(parts, &seeded, in_plane, library));
    out.extend(maps_on_domains(parts, &seeded, library));
    parts.facts.extend(out);
    parts.said_once.extend(walked);
}

/// The number system the line stating a part puts it in, where the part is
/// shown by a line (`membership::Shown::Stated`); None where it is shown
/// otherwise.
fn line_system(shown: &membership::Shown) -> Option<System> {
    let membership::Shown::Stated { line } = shown else {
        return None;
    };
    let set = line.children.get(1)?;
    (set.notation() == NUMBER_SYSTEMS)
        .then(|| System::of_sign(&set.text))
        .flatten()
}

/// Each map the step's facts, claims or values write is a function on its
/// domain, which the map writes and the page so says once (`SYNTAX.md`, a
/// map): `the map sending y ∈ ℝ to y + 1` is a function on ℝ.
fn maps_on_domains(parts: &Parts, seeded: &[Node], library: &Library) -> Vec<Node> {
    let mut seen: FxIndexSet<ByShape> = FxIndexSet::default();
    let mut out = Vec::new();
    for node in parts
        .facts
        .iter()
        .chain(&parts.claims)
        .chain(seeded)
        .flat_map(|n| n.walk())
    {
        let (MAP, [_, domain, _]) = (node.notation(), node.children.as_slice()) else {
            continue;
        };
        if !seen.insert(node.by_shape()) {
            continue;
        }
        let on = vec![node.clone(), domain.clone()];
        if let Some(made) = page::made_as(library.env.g, "_ is a function on _", on) {
            out.push(made);
        }
    }
    out
}

/// A number system's set as the code writes it, `ℝ`, and the membership
/// `x ∈ S` read with S of that set's sort, to be filled with a term and the
/// set (`said_once`).
struct SystemForm {
    set: Node,
    member: Node,
}

/// The `SystemForm` of the number system `sign` writes, read with `local`;
/// None where the notation database does not declare what it writes.
/// `term ∈ S` for the set of `system`, in the standard order, as the
/// said-once walk writes a membership; None for a system with no sign.
pub fn system_member(term: &Node, system: System, library: &Library) -> Option<Node> {
    let ctx = &library.ctx;
    let (sign, _) = rules::SYSTEM_OF
        .iter()
        .find(|(_, label)| System::of_label(label) == Some(system))?;
    let mut local = Sorts::default();
    local.insert("x".into(), Sort::of("number"));
    let SystemForm { set, member } = system_form(sign, &local, library)?;
    let put = Binding::from([(Symbol::of("x"), term.clone()), (Symbol::of("S"), set)]);
    Some(standard(&substitute_apart(&member, &put, ctx), ctx))
}

fn system_form(
    sign: &'static str,
    local: &Sorts,
    library: &Library,
) -> Option<SystemForm> {
    let set = template(sign, library.env.g, local).ok()?;
    let mut sets = local.clone();
    sets.insert("S".into(), set.sort.clone());
    let member = template("x ∈ S", library.env.g, &sets).ok()?;
    Some(SystemForm { set, member })
}

/// A ∈ 𝔼² for each letter in `points` the step names: `let A be a point`
/// says it once, as a sort (`READERS.md`, a sort is stated once), and the
/// kernel builds the sort and the membership as the one A ∈ ℂ. A point built
/// from parts, (x, y), rests on what its parts are and is not given.
fn points_in_plane(
    parts: &Parts,
    seeded: &[Node],
    points: &BTreeSet<String>,
    library: &Library,
) -> Vec<Node> {
    let ctx = &library.ctx;
    let mut local = Sorts::new();
    local.insert("x".into(), Sort::of("point"));
    let Ok(made) = template("x ∈ 𝔼²", library.env.g, &local) else {
        return Vec::new();
    };
    let mut seen: FxIndexSet<ByShape> = FxIndexSet::default();
    parts
        .facts
        .iter()
        .chain(&parts.claims)
        .chain(seeded)
        .flat_map(|n| n.walk())
        .filter(|node| node.is_name() && points.contains(node.text.as_str()))
        .filter(|node| seen.insert(node.by_shape()))
        .map(|node| {
            let put = Binding::from([(Symbol::of("x"), node.clone())]);
            standard(&substitute_apart(&made, &put, ctx), ctx)
        })
        .collect()
}

/// Whether `term` is a number by the one membership rule
/// (`membership::shown`) over `facts`: its letters each one a fact puts in a
/// number system or one `bound` binds over one, as a "there is q ∈ ℤ" does
/// its q; and a part the walk takes as it stands held by a line stating it,
/// (x − a)·q(x) where a line says q(x) ∈ ℂ, by the closure, or beside an
/// equation among `facts`.
pub fn a_number(
    term: &Node,
    facts: &[Node],
    bound: &Introduced,
    library: &Library,
) -> bool {
    let mut letters = bound.clone();
    for f in facts {
        let (MEMBERSHIP, [name, set]) = (f.notation(), f.children.as_slice()) else {
            continue;
        };
        if let (true, Some(system)) = (
            name.is_name() && set.notation() == NUMBER_SYSTEMS,
            System::of_sign(&set.text),
        ) {
            letters.entry(name.text.to_string()).or_insert(system);
        }
    }
    let typed: Vec<Node> = facts
        .iter()
        .filter(|f| types_a_function(f))
        .cloned()
        .collect();
    let given = membership::Facts {
        facts,
        letters,
        ranged: IndexMap::new(),
        typed: &typed,
        in_sums: &[],
        targets: &library.targets,
        ctx: &library.ctx,
    };
    membership::holds(term, System::C, &given)
}

/// Why the page says once that a term is in a number system (`within`):
/// what the build proves the membership from.
#[derive(Clone, Debug, PartialEq)]
pub enum OnceReason {
    /// A line the step names puts the term in the system or one inside it.
    Stated,
    /// A sum whose term is in the system at every index (`sum_said_once`).
    Sum,
    /// A numeral, whose value is in the system.
    Numeral,
    /// A letter introduced in the system or one inside it.
    Letter,
    /// A square root, π, e or a logarithm `real arithmetic` works out, which
    /// is in ℝ and ℂ.
    Real,
    /// The distance |PQ| between two points introduced as points, which is
    /// in ℝ and ℂ.
    Distance,
    /// The angle ∠PQR at three letters introduced as points, which is in ℝ
    /// and ℂ: an angle is written only where its points are said to differ
    /// (`SYNTAX.md`, Formulas), and those lines say what makes it a number.
    Angle,
    /// A sine, cosine or exponential of an argument in ℝ for the reason
    /// given, which is in ℝ and ℂ.
    Applied(Box<OnceReason>),
    /// n! of an n in ℕ₀ for the reason given, which is in ℕ and every
    /// system containing it.
    Factorial(Box<OnceReason>),
    /// |x| of an x in `within` for the reason `part` gives: of one in ℤ it
    /// is in ℕ₀, and of one in ℂ in ℝ.
    Absolute {
        within: System,
        part: Box<OnceReason>,
    },
    /// The term's operation applied to parts each in the system, the
    /// reasons given in the order the term writes its parts; a power's
    /// exponent is no part, being a numeral or a letter in ℕ or ℕ₀, and a
    /// quotient's divisor is not zero by `nonzero`.
    Built(Vec<OnceReason>),
}

/// Whether `term` is in `system` by what the page says once, or by `said`,
/// which puts a term in a system as a line stating it does.
pub fn within(
    term: &Node,
    system: System,
    letters: &Introduced,
    nonzero: &dyn Fn(&Node) -> bool,
    said: &dyn Fn(&Node, System) -> bool,
) -> bool {
    let stated = |t: &Node, s: System| said(t, s).then_some(OnceReason::Stated);
    reason_within(term, system, letters, nonzero, &stated).is_some()
}

/// Why `term` is in `system` by what the page says once, or by `said`,
/// which gives the reason a part the walk does not take apart is in a
/// system (`OnceReason::Stated` or `Sum`); None where it is not.
pub fn reason_within(
    term: &Node,
    system: System,
    letters: &Introduced,
    nonzero: &dyn Fn(&Node) -> bool,
    said: &dyn Fn(&Node, System) -> Option<OnceReason>,
) -> Option<OnceReason> {
    let mut page = PageOnce {
        letters,
        nonzero,
        said,
    };
    reason(&mut page, term, system)
}

/// How a term is made, as the said-once walk takes it apart (`OnceAsk`).
pub enum Shape<'t, T> {
    /// Numerals alone, worked out to this value.
    Value(BigRational),
    /// A letter, whose number system `OnceAsk::letter` gives.
    Letter,
    Negated(&'t T),
    /// a op b, the operation by its set.mm label: `caddc`, `cmin`, `cmul`
    /// or `cdiv`.
    Operation(&'static str, &'t T, &'t T),
    /// A base to an exponent.
    Power(&'t T, &'t T),
    /// x° for this x: x·π/180, which is in ℝ or ℂ where x is. Only the
    /// page writes it; the kernel's x·π/180 is an operation of its parts.
    Degrees(&'t T),
    /// What `real arithmetic` works out and the walk takes whole: the square
    /// root of numerals whose value is a rational of at least 0, π, e, and
    /// the logarithm of numerals whose value is a positive rational.
    Real,
    /// The distance |PQ| from the first point to the second.
    Distance(&'t T, &'t T),
    /// The angle ∠PQR, its points in the order written: P, the vertex Q,
    /// and R.
    Angle(&'t T, &'t T, &'t T),
    /// The library's sine, cosine or exponential of this argument, where
    /// `real arithmetic` does not work it out whole.
    Applied(&'t T),
    /// n! of this n.
    Factorial(&'t T),
    /// The absolute value |x| of a number x.
    Absolute(&'t T),
    /// C(n, k), gcd(a, b) or lcm(a, b), by its operation's set.mm label
    /// (`cbc`, `cgcd`, `clcm`), whose row of `rules::WHOLE` says what its
    /// parts must be.
    Whole(&'static str, &'t T, &'t T),
    /// Anything the walk does not take apart.
    Other,
}

/// What the said-once walk asks of a term, written once for both tools:
/// the page's sentences (`PageOnce`) and the build's kernel terms. The
/// rule is `reason`'s; each tool says only how its terms are made and what
/// its page says of them.
pub trait OnceAsk {
    type T;
    fn shape<'t>(&self, term: &'t Self::T) -> Shape<'t, Self::T>;
    /// The number system a letter is introduced in; None for one that is
    /// not.
    fn letter(&mut self, term: &Self::T) -> Option<System>;
    /// Whether a term is a letter introduced as a point.
    fn point(&mut self, term: &Self::T) -> bool;
    /// Whether a divisor is not zero by what the page says.
    fn nonzero(&mut self, divisor: &Self::T) -> bool;
    /// Why a part the walk does not take apart is in `system`: a line
    /// stating it (`Stated`), or a sum said once (`Sum`).
    fn said(&mut self, term: &Self::T, system: System) -> Option<OnceReason>;
}

/// Why the page says once that `term` is in `system` (`READERS.md`,
/// membership said once): what a line says of it, a numeral, a letter in
/// the system its introducing line names or one inside it, a distance or
/// an angle between letters introduced as points in ℝ or ℂ, a sine, cosine
/// or exponential of a real argument in ℝ or ℂ, or +, −, ·,
/// negation, a power to a numeral or to a letter in ℕ or ℕ₀, a quotient
/// whose divisor is not zero, and x° in ℝ or ℂ, of parts that are; None
/// where it is not.
pub fn reason<A: OnceAsk>(
    ask: &mut A,
    term: &A::T,
    system: System,
) -> Option<OnceReason> {
    if let Some(said) = ask.said(term, system) {
        return Some(said);
    }
    let label = system.label();
    match ask.shape(term) {
        Shape::Value(v) => {
            let whole = v.is_integer();
            let holds = match system {
                System::N => whole && v.is_positive(),
                System::N0 => whole && !v.is_negative(),
                System::Z => whole,
                _ => true,
            };
            holds.then_some(OnceReason::Numeral)
        }
        Shape::Letter => ask
            .letter(term)
            .is_some_and(|set| set.within(system))
            .then_some(OnceReason::Letter),
        Shape::Negated(a) => {
            lookup(rules::NEGATED, label)?;
            Some(OnceReason::Built(vec![reason(ask, a, system)?]))
        }
        Shape::Operation(op, a, b) => {
            if op == "cdiv" {
                lookup(rules::DIVIDED, label)?;
                if !ask.nonzero(b) {
                    return None;
                }
            } else {
                rules::closed(op, label)?;
            }
            let first = reason(ask, a, system)?;
            Some(OnceReason::Built(vec![first, reason(ask, b, system)?]))
        }
        Shape::Power(a, e) => {
            if !whole_exponent(ask, e) {
                return None;
            }
            rules::closed("cexp", label)?;
            Some(OnceReason::Built(vec![reason(ask, a, system)?]))
        }
        Shape::Degrees(x) => {
            if !matches!(system, System::R | System::C) {
                return None;
            }
            Some(OnceReason::Built(vec![reason(ask, x, system)?]))
        }
        Shape::Real => {
            matches!(system, System::R | System::C).then_some(OnceReason::Real)
        }
        Shape::Distance(p, q) => {
            (matches!(system, System::R | System::C) && ask.point(p) && ask.point(q))
                .then_some(OnceReason::Distance)
        }
        Shape::Angle(p, q, r) => (matches!(system, System::R | System::C)
            && ask.point(p)
            && ask.point(q)
            && ask.point(r))
        .then_some(OnceReason::Angle),
        Shape::Applied(a) => {
            if !matches!(system, System::R | System::C) {
                return None;
            }
            Some(OnceReason::Applied(Box::new(reason(ask, a, System::R)?)))
        }
        Shape::Factorial(n) => {
            Some(OnceReason::Factorial(Box::new(reason(ask, n, System::N0)?)))
        }
        Shape::Absolute(x) => {
            if System::N0.within(system) {
                if let Some(part) = reason(ask, x, System::Z) {
                    return Some(OnceReason::Absolute {
                        within: System::Z,
                        part: Box::new(part),
                    });
                }
            }
            if !matches!(system, System::R | System::C) {
                return None;
            }
            let part = reason(ask, x, System::C)?;
            Some(OnceReason::Absolute {
                within: System::C,
                part: Box::new(part),
            })
        }
        Shape::Whole(op, a, b) => {
            let whole = rules::WHOLE.iter().find(|w| w.op == op)?;
            if !System::N0.within(system) {
                return None;
            }
            let (left, right) = (
                System::of_label(whole.left.1)?,
                System::of_label(whole.right.1)?,
            );
            let first = reason(ask, a, left)?;
            Some(OnceReason::Built(vec![first, reason(ask, b, right)?]))
        }
        Shape::Other => None,
    }
}

/// Whether `real arithmetic` takes the square root of a rational: one of at
/// least 0, within its limits (`methods::surds::root_of`).
pub fn root_taken(value: &BigRational) -> bool {
    surds::root_of(value).is_ok()
}

/// Whether `real arithmetic` takes the logarithm of a rational: a positive
/// one, within its limits (`methods::reals::factored`).
pub fn log_taken(value: &BigRational) -> bool {
    value.is_positive() && reals::factored(value).is_ok()
}

/// Whether `real arithmetic` takes the sine and cosine of q·π: q's
/// denominator divides 4 or 6 (`methods::reals::trig_value`).
pub fn angle_taken(multiple: &BigRational) -> bool {
    trig_value(Trig::Sine, multiple).is_ok()
}

/// The q of a closed angle written as q·π, in radians or degrees: π, a
/// numeral, and what +, −, ·, / and negation build from them where the
/// result is a multiple of π, or x° for a numeral x. None for any other.
fn pi_multiple(term: &Node) -> Option<BigRational> {
    let (rational, of_pi) = pi_parts(term)?;
    rational.is_zero().then_some(of_pi)
}

/// A closed term as a + b·π, its rational part and its multiple of π.
fn pi_parts(term: &Node) -> Option<(BigRational, BigRational)> {
    if let Some(v) = value(term) {
        return Some((v, BigRational::zero()));
    }
    let kids = term.children.as_slice();
    Some(match (term.notation(), term.spelling(), kids) {
        (PI, _, []) => (BigRational::zero(), BigRational::one()),
        (DEGREES, _, [x]) => (
            BigRational::zero(),
            value(x)? / BigRational::from_integer(180.into()),
        ),
        (UNARY_MINUS, _, [a]) => {
            let (r, p) = pi_parts(a)?;
            (-r, -p)
        }
        (_, PLUS, [a, b]) => {
            let ((r, p), (s, q)) = (pi_parts(a)?, pi_parts(b)?);
            (r + s, p + q)
        }
        (_, MINUS, [a, b]) => {
            let ((r, p), (s, q)) = (pi_parts(a)?, pi_parts(b)?);
            (r - s, p - q)
        }
        (_, TIMES, [a, b]) | (JUXTAPOSITION, _, [a, b]) => {
            let ((r, p), (s, q)) = (pi_parts(a)?, pi_parts(b)?);
            if !p.is_zero() && !q.is_zero() {
                return None;
            }
            (&r * &s, r * q + p * s)
        }
        (_, DIVIDED, [a, b]) => {
            let ((r, p), (s, q)) = (pi_parts(a)?, pi_parts(b)?);
            if !q.is_zero() || s.is_zero() {
                return None;
            }
            (r / &s, p / s)
        }
        _ => return None,
    })
}

/// Whether a power's exponent makes it a product of copies of its base: a
/// term the page says once is in ℕ₀ (`READERS.md`, membership said once).
/// 2^j and 2^(j + 1) with j ∈ ℕ₀ are then numbers wherever 2 is, and
/// 2^(−1), 0^k with k ∈ ℤ, or 2^(p − 1) are not said once this way.
fn whole_exponent<A: OnceAsk>(ask: &mut A, exponent: &A::T) -> bool {
    reason(ask, exponent, System::N0).is_some()
}

/// The page's sentences as the said-once walk reads them: letters by the
/// systems `letters` introduces them in, and what `nonzero` and `said` say.
struct PageOnce<'a> {
    letters: &'a Introduced,
    nonzero: &'a dyn Fn(&Node) -> bool,
    said: &'a dyn Fn(&Node, System) -> Option<OnceReason>,
}

impl OnceAsk for PageOnce<'_> {
    type T = Node;

    fn shape<'t>(&self, term: &'t Node) -> Shape<'t, Node> {
        if let Some(v) = value(term) {
            return Shape::Value(v);
        }
        if term.is_name() {
            return Shape::Letter;
        }
        match (term.notation(), term.spelling(), term.children.as_slice()) {
            (UNARY_MINUS, _, [a]) => Shape::Negated(a),
            (_, PLUS, [a, b]) => Shape::Operation("caddc", a, b),
            (_, MINUS, [a, b]) => Shape::Operation("cmin", a, b),
            (_, TIMES, [a, b]) | (JUXTAPOSITION, _, [a, b]) => {
                Shape::Operation("cmul", a, b)
            }
            (_, DIVIDED, [a, b]) => Shape::Operation("cdiv", a, b),
            (POWER | SUPERSCRIPT, _, [a, e]) => Shape::Power(a, e),
            (SQUARE_ROOT, _, [a]) if value(a).is_some_and(|v| root_taken(&v)) => {
                Shape::Real
            }
            (PI | EULER, _, []) => Shape::Real,
            (DEGREES, _, [x]) => Shape::Degrees(x),
            (DISTANCE, _, [p, q]) => Shape::Distance(p, q),
            // The library's ln, sin and cos: one the theorem introduces as a
            // letter of its own is not it.
            (APPLICATION, _, [head, a])
                if head.is_name()
                    && head.text == "ln"
                    && !self.letters.contains_key("ln")
                    && value(a).is_some_and(|v| log_taken(&v)) =>
            {
                Shape::Real
            }
            (APPLICATION, _, [head, a])
                if head.is_name()
                    && matches!(head.text.as_str(), "sin" | "cos")
                    && !self.letters.contains_key(head.text.as_str())
                    && pi_multiple(a).is_some_and(|q| angle_taken(&q)) =>
            {
                Shape::Real
            }
            (APPLICATION, _, [head, a])
                if head.is_name()
                    && matches!(head.text.as_str(), "sin" | "cos" | "exp")
                    && !self.letters.contains_key(head.text.as_str()) =>
            {
                Shape::Applied(a)
            }
            (n, _, [p, q, r]) if n == NotationId::of("angle") => Shape::Angle(p, q, r),
            (FACTORIAL, _, [n]) => Shape::Factorial(n),
            (ABSOLUTE_VALUE, _, [x]) => Shape::Absolute(x),
            // The library's C, gcd and lcm: one the theorem introduces as a
            // letter of its own is not it.
            (APPLICATION_TO_TWO, _, [head, a, b])
                if head.is_name() && !self.letters.contains_key(head.text.as_str()) =>
            {
                match head.text.as_str() {
                    "C" => Shape::Whole("cbc", a, b),
                    "gcd" => Shape::Whole("cgcd", a, b),
                    "lcm" => Shape::Whole("clcm", a, b),
                    _ => Shape::Other,
                }
            }
            _ => Shape::Other,
        }
    }

    fn letter(&mut self, term: &Node) -> Option<System> {
        self.letters.get(term.text.as_str()).copied()
    }

    /// A name of the point sort: `let A be a point` or an obtain gives it
    /// the sort, and a step rests on that without naming the line.
    fn point(&mut self, term: &Node) -> bool {
        term.is_name() && term.sort.is("point")
    }

    fn nonzero(&mut self, divisor: &Node) -> bool {
        (self.nonzero)(divisor)
    }

    fn said(&mut self, term: &Node, system: System) -> Option<OnceReason> {
        (self.said)(term, system)
    }
}

/// Whether a sum over a range is a number the page says once (`READERS.md`,
/// membership said once): the one rule over no lines (`membership::shown`),
/// its term one at every index by what the page says once and by the
/// function types in scope, `typed`, as `a : {1, …, n} → ℝ` says a(k) is
/// real where k runs from 1 to n. A term dividing by what may be zero at
/// some index is not, nor is a value at a point outside its function's
/// domain: a line says those.
pub fn sum_said_once(
    term: &Node,
    system: System,
    letters: &Introduced,
    typed: &[Node],
    targets: &Targets,
    ctx: &Context,
) -> bool {
    if term.notation() != SUM {
        return false;
    }
    let given = membership::Facts {
        facts: &[],
        letters: letters.clone(),
        ranged: IndexMap::new(),
        typed: &[],
        in_sums: typed,
        targets,
        ctx,
    };
    membership::holds(term, system, &given)
}

/// The number system a range from `start` puts its members in: ℕ from 1,
/// ℕ₀ from 0, ℤ from anywhere (`rules::RANGE_WITHIN`).
pub fn index_system(start: &Node) -> Option<System> {
    let begins = (start.notation() == NUMERAL)
        .then(|| {
            start
                .text
                .parse::<u32>()
                .ok()
                .and_then(rules::numeral_label)
        })
        .flatten();
    rules::RANGE_WITHIN
        .iter()
        .find(|row| row.first.is_none() || row.first == begins)
        .and_then(|row| System::of_label(row.system))
}

/// Whether a divisor is not zero by `said`, or by its parts: a product, a
/// quotient, a negation or a power to a numeral is not zero when its parts
/// are, each by this same test. The checker's one order and list of parts
/// for a divisor (`ELABORATION.md`, a divisor's ≠ 0), `said` being what a
/// check takes as a line or the page saying it.
pub fn nonzero_by_parts(divisor: &Node, said: &dyn Fn(&Node) -> bool) -> bool {
    if said(divisor) {
        return true;
    }
    match (
        divisor.notation(),
        divisor.spelling(),
        divisor.children.as_slice(),
    ) {
        (MULTIPLICATIVE | JUXTAPOSITION, _, [a, b]) | (_, DIVIDED, [a, b]) => {
            nonzero_by_parts(a, said) && nonzero_by_parts(b, said)
        }
        (UNARY_MINUS, _, [a]) => nonzero_by_parts(a, said),
        (POWER | SUPERSCRIPT, _, [a, e]) => {
            e.notation() == NUMERAL && nonzero_by_parts(a, said)
        }
        _ => false,
    }
}

/// Whether a divisor is a term of numerals alone whose value, as
/// `arithmetic` works it out, is not zero: 3, 2 − 5 and 10^0.
pub fn closed_nonzero(divisor: &Node) -> bool {
    value(divisor).is_some_and(|v| !v.is_zero())
}

/// How a divisor, or a part of one, goes without its `≠ 0` (`SYNTAX.md`),
/// so that a backend proves it the way the check found it.
pub enum NonzeroHow<'f> {
    /// A fact says so: `d ≠ 0` either way round, or a sign, `0 < d`,
    /// `d > 0`, `d < 0` or `0 > d`. The fact as the check read it.
    Stated(&'f Node),
    /// Numerals alone, whose value is not zero: 3, 2 − 5.
    Numerals,
    /// A positive integer: the one membership rule puts it in ℕ
    /// (`membership::shown`), as it does k, j·(j + 1), 2^n and (k + 1)!
    /// where k, j and n are letters in ℕ. How it does is `shown`.
    Positive(membership::Shown),
}

/// The one of `facts`, the lines the step cites and the facts read off
/// them, that says a divisor is not zero: `d ≠ 0` either way round, or a
/// sign, `0 < d`, `d > 0`, `d < 0` or `0 > d`. None where none does.
pub fn stated_nonzero<'f>(
    divisor: &Node,
    facts: &'f [Node],
    ctx: &Context,
) -> Option<&'f Node> {
    let zero = |n: &Node| n.notation() == NUMERAL && n.text == "0";
    let none = IndexMap::new();
    let is = |n: &Node| {
        alike(
            &standard(n, ctx),
            &standard(divisor, ctx),
            ctx,
            &none,
            &none,
        )
    };
    facts.iter().find(
        |f| match (f.spelling(), f.notation(), f.children.as_slice()) {
            (_, LOGICAL_NOT, [inner]) => {
                match (inner.notation(), inner.children.as_slice()) {
                    (EQUALITY, [a, b]) => (is(a) && zero(b)) || (zero(a) && is(b)),
                    _ => false,
                }
            }
            (LESS, _, [a, b]) => (zero(a) && is(b)) || (is(a) && zero(b)),
            (GREATER, _, [a, b]) => (is(a) && zero(b)) || (zero(a) && is(b)),
            _ => false,
        },
    )
}

/// The value of a term built from numerals alone, worked out exactly; None
/// where a letter stands in it, or a division by zero.
fn value(term: &Node) -> Option<BigRational> {
    let kids = term.children.as_slice();
    match (term.notation(), term.spelling(), kids) {
        (NUMERAL, _, []) => numeral(&term.text),
        (UNARY_MINUS, _, [a]) => Some(-value(a)?),
        (_, PLUS, [a, b]) => Some(value(a)? + value(b)?),
        (_, MINUS, [a, b]) => Some(value(a)? - value(b)?),
        (_, TIMES, [a, b]) | (JUXTAPOSITION, _, [a, b]) => Some(value(a)? * value(b)?),
        (_, DIVIDED, [a, b]) => {
            let d = value(b)?;
            (!d.is_zero()).then(|| value(a)).flatten().map(|n| n / d)
        }
        (POWER | SUPERSCRIPT, _, [a, e]) => {
            let e = value(e)?;
            let k = e.is_integer().then(|| e.to_integer().to_u32()).flatten()?;
            // Past a few hundred the number is not one a page writes, and
            // working it out is not the point.
            let base = value(a)?;
            (k <= 512).then(|| pow(base, k as usize))
        }
        // The operations whose records say `decided arithmetic`, worked out
        // where `arithmetic` works them out (`methods::field::closed_value`):
        // a remainder of a whole number on dividing by one of at least 1,
        // and a factorial of a whole number, as far as a page writes one.
        (MOD, _, [a, n]) => {
            let (a, n) = (value(a)?, value(n)?);
            let whole = a.is_integer() && !a.is_negative() && n.is_integer();
            (whole && n >= BigRational::one())
                .then(|| BigRational::from_integer(a.to_integer() % n.to_integer()))
        }
        (FACTORIAL, _, [n]) => {
            let n = value(n)?;
            let k = (n.is_integer() && !n.is_negative())
                .then(|| n.to_integer().to_u32())
                .flatten()?;
            (k <= 512).then(|| {
                (1..=k)
                    .map(|f| BigRational::from_integer(BigInt::from(f)))
                    .fold(BigRational::one(), |product, f| product * f)
            })
        }
        _ => None,
    }
}

/// A decimal numeral's value: digits, with a point or without one.
fn numeral(said: &str) -> Option<BigRational> {
    let (whole, part) = said.split_once('.').unwrap_or((said, ""));
    if whole.is_empty()
        || !(whole.chars().chain(part.chars())).all(|c| c.is_ascii_digit())
    {
        return None;
    }
    let digits: BigInt = format!("{whole}{part}").parse().ok()?;
    let scale = pow(BigInt::from(10), part.len());
    Some(BigRational::new(digits, scale))
}
