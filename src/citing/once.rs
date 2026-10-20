//! A membership in a number system that the page says once, where a letter
//! is introduced, and no step writes again (`READERS.md`, membership said
//! once): a numeral, a letter in the set its introducing line names and the
//! number systems containing that one, and a term built from those by +, −,
//! ·, negation, a power to a numeral or to a letter in ℕ or ℕ₀, and a
//! quotient whose divisor a fact says is not zero.
//!
//! The rule is written once, in `reason`, over a view of a term both tools
//! give (`OnceAsk`): the page's sentences here, and the build's kernel
//! terms in `Elaborator::introduced_membership`, which proves what `reason`
//! answers. So the two tools agree on which memberships a step need not
//! write.

use indexmap::IndexMap;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::formula::page::template;
use crate::formula::symbol::Symbol;
use crate::formula::{ByShape, Node, Sort, Sorts};
use crate::matching::{alike_top, standard, substitute_apart, Binding, FxIndexSet};
use crate::notations::{
    APPLICATION, DEGREES, DIVIDED, EULER, FACTORIAL, FUNCTION_TYPE, IN, INTEGER_RANGE,
    JUXTAPOSITION, MEMBERSHIP, MINUS, MOD, MULTIPLICATIVE, NUMBER_SYSTEMS, NUMERAL, PI,
    PLUS, POWER, SQUARE_ROOT, SUM, SUPERSCRIPT, TIMES, UNARY_MINUS,
};
use crate::rules::{self, lookup, System};

use super::library::Library;
use super::parts::{bound_in, function_values, Bound, Parts};

/// The number system each letter is introduced in, by the letter as the
/// page writes it.
pub type Introduced = IndexMap<String, System>;

/// The letter and number system a sentence `x ∈ ℝ` introduces; None for any
/// other sentence, a term in place of the letter included.
pub fn introduction(said: &Node) -> Option<(String, System)> {
    let [letter, set] = said.children.as_slice() else {
        return None;
    };
    if said.spelling() != IN || !letter.is_name() {
        return None;
    }
    let system = match set.notation() {
        NUMBER_SYSTEMS => System::of_sign(&set.text)?,
        INTEGER_RANGE => range_system(set)?,
        _ => return None,
    };
    Some((letter.text.to_string(), system))
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
        .find(|(_, first, _)| first.is_none() || *first == begins)
        .and_then(|(system, _, _)| System::of_label(system))
}

/// The memberships the page says once of the terms `parts` names, in every
/// number system each is in, laid onto its facts. A letter is introduced by
/// `introduced` or by a fact of `parts` saying it is in a number system.
/// They are added after what a membership implies is read (`finished`), so
/// that `let k ∈ ℕ` gives k ∈ ℝ here and never k ≥ 1. A sum is said once
/// by its term at every index, with the function types in scope, `typed`
/// (`sum_said_once`).
pub fn said_once(
    parts: &mut Parts,
    introduced: &Introduced,
    typed: &[Node],
    library: &Library,
    sorts: &Sorts,
) {
    let mut letters = introduced.clone();
    // A term other than a letter that a fact puts in a number system is a
    // number there as a letter is, and what the said-once operations build
    // from it is too: N(n) + 1 ∈ ℝ where a line says N(n) ∈ ℝ, as a
    // method's atoms are read (`methods::membership::said`).
    let mut atoms: Vec<(Node, System)> = Vec::new();
    for f in &parts.facts {
        let [term, set] = f.children.as_slice() else {
            continue;
        };
        if f.notation() != MEMBERSHIP || set.notation() != NUMBER_SYSTEMS {
            continue;
        }
        let Some(system) = System::of_sign(&set.text) else {
            continue;
        };
        if !term.is_name() {
            atoms.push((term.clone(), system));
            continue;
        }
        // Of two systems a letter is in, the narrower stands: a line saying
        // q ∈ ℕ₀ narrows a q a `let` or an `obtain` put in ℤ.
        letters
            .entry(term.text.to_string())
            .and_modify(|held| {
                if system.within(*held) {
                    *held = system;
                }
            })
            .or_insert(system);
    }
    // A function's value at a point the page puts in the function's domain
    // once, a(n) with `let a : ℕ → ℝ` cited and `let n ∈ ℕ`, is in the
    // codomain as at a point a line says (`SYNTAX.md`, a function's type
    // and a point of its domain): the type line is cited, the point said
    // once. A domain that is no number system, a range, asks its line.
    let mut points: Vec<Node> = Vec::new();
    for typed in &parts.facts {
        let (FUNCTION_TYPE, [_, domain, _]) =
            (typed.notation(), typed.children.as_slice())
        else {
            continue;
        };
        let within = (domain.notation() == NUMBER_SYSTEMS)
            .then(|| System::of_sign(&domain.text))
            .flatten();
        let Some(within) = within else {
            continue;
        };
        for (letter, system) in &letters {
            if system.within(within) {
                let point = Node::name(Sort::none(), letter);
                points.push(bound_in(Bound::Member, &point, domain, library.env.g));
            }
        }
    }
    if !points.is_empty() {
        let types: Vec<Node> = parts
            .facts
            .iter()
            .filter(|f| f.notation() == FUNCTION_TYPE)
            .cloned()
            .chain(points)
            .collect();
        for value in function_values(&types, library.env, sorts) {
            if parts
                .facts
                .iter()
                .any(|f| alike_top(f, &value, &library.ctx))
            {
                continue;
            }
            if let (Some(system), [term, _]) = (
                value.children.get(1).and_then(|s| System::of_sign(&s.text)),
                value.children.as_slice(),
            ) {
                atoms.push((term.clone(), system));
            }
            parts.facts.push(value);
        }
    }
    let ctx = &library.ctx;
    let mut local = sorts.clone();
    local.insert("x".into(), Sort::of("number"));
    // The code's own forms read, each filled with the term at x and the set
    // at S. A notation database that does not declare what one writes says
    // nothing here, and its own checks report what it lacks.
    let form = |said: &'static str, term: &Node| -> Option<Node> {
        let made = template(said, library.env.g, &local).ok()?;
        let put = Binding::from([(Symbol::of("x"), term.clone())]);
        Some(standard(&substitute_apart(&made, &put, ctx), ctx))
    };
    // S is read as the number system that fills it, whatever the page's S
    // is.
    let member = |sign: &'static str, term: &Node| -> Option<Node> {
        let set = template(sign, library.env.g, &local).ok()?;
        let mut sets = local.clone();
        sets.insert("S".into(), set.sort.clone());
        let made = template("x ∈ S", library.env.g, &sets).ok()?;
        let put =
            Binding::from([(Symbol::of("x"), term.clone()), (Symbol::of("S"), set)]);
        Some(standard(&substitute_apart(&made, &put, ctx), ctx))
    };
    // A divisor is not zero where the page says once it is a positive
    // integer, where a fact says so, as `≠ 0` or as a sign, or by its parts
    // (`nonzero_by_parts`).
    let said_nonzero = |d: &Node| -> bool {
        if nonzero_said_once(d, &letters) {
            return true;
        }
        ["x ≠ 0", "x > 0", "x < 0"].iter().any(|said| {
            form(said, d).is_some_and(|want| {
                parts.facts.iter().any(|f| alike_top(f, &want, ctx))
            })
        })
    };
    let nonzero = |d: &Node| nonzero_by_parts(d, &said_nonzero);
    let seeded: Vec<Node> = parts.seed.values().cloned().collect();
    let mut seen: FxIndexSet<ByShape> = FxIndexSet::default();
    let mut out = Vec::new();
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
        for (sign, label) in rules::SYSTEM_OF {
            let Some(system) = System::of_label(label) else {
                continue;
            };
            let given = Given {
                atoms: &atoms,
                letters: &letters,
                typed,
                ctx,
            };
            let said = |t: &Node, s: System| given.says(t, s);
            if reason_within(&node, system, &letters, &nonzero, &said).is_some() {
                out.extend(member(sign, &node));
            }
        }
    }
    parts.facts.extend(out);
}

/// What the said-once walk takes as it stands, where it does not take a
/// term apart: a term a fact puts in a number system, and a sum said once
/// by its terms (`sum_said_once`).
struct Given<'a> {
    atoms: &'a [(Node, System)],
    letters: &'a Introduced,
    typed: &'a [Node],
    ctx: &'a crate::matching::Context,
}

impl Given<'_> {
    fn says(&self, term: &Node, system: System) -> Option<OnceReason> {
        let none = IndexMap::new();
        let stated = self.atoms.iter().any(|(a, s)| {
            s.within(system) && crate::matching::alike(a, term, self.ctx, &none, &none)
        });
        if stated {
            return Some(OnceReason::Stated);
        }
        sum_said_once(term, system, self.letters, self.typed, self.ctx)
            .then_some(OnceReason::Sum)
    }
}

/// Whether `term` is a number by what the page says once of the letters in
/// it: each letter one a fact puts in a number system or one `bound` binds
/// over one, as a "there is q ∈ ℤ" does its q; a divisor not zero only
/// where it is a numeral.
pub fn a_number_said_once(
    term: &Node,
    facts: &[Node],
    bound: &Introduced,
    ctx: &crate::matching::Context,
) -> bool {
    let mut letters = bound.clone();
    // A term a fact puts in a number system is a number there as a letter
    // is, and what +, − and · build from it is too: (x − a)·q(x) where a
    // line says q(x) ∈ ℂ.
    let mut atoms: Vec<(&Node, System)> = Vec::new();
    for f in facts {
        let [name, set] = f.children.as_slice() else {
            continue;
        };
        if f.notation() != MEMBERSHIP || set.notation() != NUMBER_SYSTEMS {
            continue;
        }
        let Some(system) = System::of_sign(&set.text) else {
            continue;
        };
        if name.is_name() {
            letters.entry(name.text.to_string()).or_insert(system);
        } else {
            atoms.push((name, system));
        }
    }
    let positive = letters.clone();
    let nonzero = |d: &Node| nonzero_said_once(d, &positive);
    let said = |t: &Node, system: System| {
        atoms.iter().any(|(a, s)| {
            crate::matching::alike(a, t, ctx, &IndexMap::new(), &IndexMap::new())
                && s.within(system)
        })
    };
    within(term, System::C, &letters, &nonzero, &said)
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
    /// What `real arithmetic` works out and the walk takes whole: the square
    /// root of numerals whose value is a rational of at least 0, π, e, and
    /// the logarithm of numerals whose value is a positive rational.
    Real,
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
    /// Whether a divisor is not zero by what the page says.
    fn nonzero(&mut self, divisor: &Self::T) -> bool;
    /// Why a part the walk does not take apart is in `system`: a line
    /// stating it (`Stated`), or a sum said once (`Sum`).
    fn said(&mut self, term: &Self::T, system: System) -> Option<OnceReason>;
}

/// Why the page says once that `term` is in `system` (`READERS.md`,
/// membership said once): what a line says of it, a numeral, a letter in
/// the system its introducing line names or one inside it, or +, −, ·,
/// negation, a power to a numeral or to a letter in ℕ or ℕ₀, and a quotient
/// whose divisor is not zero, of parts that are; None where it is not.
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
        Shape::Real => {
            matches!(system, System::R | System::C).then_some(OnceReason::Real)
        }
        Shape::Other => None,
    }
}

/// Whether `real arithmetic` takes the square root of a rational: one of at
/// least 0, within its limits (`methods::surds::root_of`).
pub fn root_taken(value: &BigRational) -> bool {
    crate::methods::surds::root_of(value).is_ok()
}

/// Whether `real arithmetic` takes the logarithm of a rational: a positive
/// one, within its limits (`methods::reals::factored`).
pub fn log_taken(value: &BigRational) -> bool {
    value.is_positive() && crate::methods::reals::factored(value).is_ok()
}

/// Whether `real arithmetic` takes the sine and cosine of q·π: q's
/// denominator divides 4 or 6 (`methods::reals::trig_value`).
pub fn angle_taken(multiple: &BigRational) -> bool {
    use crate::methods::reals::{trig_value, Trig};
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

/// Whether a power's exponent makes it a product of copies of its base:
/// a numeral in ℕ₀, or a letter introduced in ℕ or ℕ₀ (`READERS.md`,
/// membership said once). 2^j with j ∈ ℕ₀ is then a number wherever 2 is,
/// and 2^(−1), 0^k with k ∈ ℤ, or 2^(j + 1) are not said once this way.
fn whole_exponent<A: OnceAsk>(ask: &mut A, exponent: &A::T) -> bool {
    match ask.shape(exponent) {
        Shape::Value(v) => v.is_integer() && !v.is_negative(),
        Shape::Letter => ask
            .letter(exponent)
            .is_some_and(|set| set.within(System::N0)),
        _ => false,
    }
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
            _ => Shape::Other,
        }
    }

    fn letter(&mut self, term: &Node) -> Option<System> {
        self.letters.get(term.text.as_str()).copied()
    }

    fn nonzero(&mut self, divisor: &Node) -> bool {
        (self.nonzero)(divisor)
    }

    fn said(&mut self, term: &Node, system: System) -> Option<OnceReason> {
        (self.said)(term, system)
    }
}

/// Whether a sum over a range is a number the page says once (`READERS.md`,
/// membership said once): its term is one at every index, by what the page
/// says once and by the function types in scope, `typed`, as `a : {1, …,
/// n} → ℝ` says a(k) is real where k runs from 1 to n. A term dividing by
/// something other than a numeral is not, for the divisor may be zero at
/// some index, nor is a value at a point outside its function's domain: a
/// line says those.
pub fn sum_said_once(
    term: &Node,
    system: System,
    letters: &Introduced,
    typed: &[Node],
    ctx: &crate::matching::Context,
) -> bool {
    let (SUM, [index, start, end, body]) = (term.notation(), term.children.as_slice())
    else {
        return false;
    };
    if !matches!(system, System::R | System::C) || !index.is_name() {
        return false;
    }
    let mut letters = letters.clone();
    if let Some(inside) = index_system(start) {
        letters.insert(index.text.to_string(), inside);
    }
    let at = SumIndex {
        index: &index.text,
        start,
        end,
        letters: &letters,
        typed,
        ctx,
    };
    within(
        body,
        system,
        &letters,
        &|d| nonzero_said_once(d, &letters),
        &|t, s| at.says(t, s),
    )
}

/// What a sum's term is read with at each index: the index and its range,
/// the letters said once there, and the function types in scope.
struct SumIndex<'a> {
    index: &'a str,
    start: &'a Node,
    end: &'a Node,
    letters: &'a Introduced,
    typed: &'a [Node],
    ctx: &'a crate::matching::Context,
}

impl SumIndex<'_> {
    /// Whether a part the walk does not take apart is in `system` at every
    /// index: a sum inside the term by the same rule, or a function's value
    /// at a point of its domain, by a type whose codomain is in `system`.
    fn says(&self, term: &Node, system: System) -> bool {
        if sum_said_once(term, system, self.letters, self.typed, self.ctx) {
            return true;
        }
        let (APPLICATION, [f, x]) = (term.notation(), term.children.as_slice()) else {
            return false;
        };
        self.typed.iter().any(|t| {
            let [g, domain, codomain] = t.children.as_slice() else {
                return false;
            };
            g.is_name()
                && f.is_name()
                && g.text == f.text
                && codomain.notation() == NUMBER_SYSTEMS
                && System::of_sign(&codomain.text).is_some_and(|s| s.within(system))
                && self.in_domain(x, domain)
        })
    }

    /// Whether the point `x` is in a function's `domain` at every index:
    /// the index where the domain is the sum's own range, or a letter said
    /// once in a number system the domain holds.
    fn in_domain(&self, x: &Node, domain: &Node) -> bool {
        let same = |a: &Node, b: &Node| {
            crate::matching::alike(a, b, self.ctx, &IndexMap::new(), &IndexMap::new())
        };
        if domain.notation() == INTEGER_RANGE {
            return x.is_name()
                && x.text == self.index
                && matches!(domain.children.as_slice(), [a, b]
                    if same(a, self.start) && same(b, self.end));
        }
        domain.notation() == NUMBER_SYSTEMS
            && x.is_name()
            && System::of_sign(&domain.text).is_some_and(|d| {
                self.letters
                    .get(x.text.as_str())
                    .is_some_and(|s| s.within(d))
            })
    }
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
        .find(|(_, first, _)| first.is_none() || *first == begins)
        .and_then(|(system, _, _)| System::of_label(system))
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

/// Whether a divisor goes without its `≠ 0` (`SYNTAX.md`): a term of
/// numerals alone whose value is not zero, or a term the page says once is
/// in ℕ by `letters`, a positive integer, as k, j·(j + 1), 2^n and (k + 1)!
/// are where k, j and n are letters in ℕ.
pub fn nonzero_said_once(divisor: &Node, letters: &Introduced) -> bool {
    closed_nonzero(divisor)
        || within(divisor, System::N, letters, &closed_nonzero, &|_, _| false)
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
            (k <= 512).then(|| num_traits::pow(base, k as usize))
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
    let scale = num_traits::pow(BigInt::from(10), part.len());
    Some(BigRational::new(digits, scale))
}
