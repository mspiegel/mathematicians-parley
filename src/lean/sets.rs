//! Sets in Lean: a set of the things a theorem's sets hold is `Set α`, and
//! the page's operations on sets are Mathlib's on `Set`.
//!
//! The members of every set a theorem leaves open are one type `α`, as
//! set.mm's sets all hold sets; 𝒫A's members are `Set α`. A function from
//! one such set to another is a function `α → α` with the fact that it
//! maps the one into the other beside it (`statement`).

use super::doc::bridges::BridgeModule;
use super::doc::{CountForm, LeanType, Source, TermKind};
use super::expr::{
    letter_type, listed_set, relation_of, set_type, system_of, witnessed, LetterType,
    Members, Printed, System, Writer,
};
use super::templates::Num;
use crate::citing::bounds;
use crate::citing::finite::{is_finite, SaidFinite};
use crate::formula::Node;
use crate::notations::NUMBER_SYSTEMS;
use crate::outcome::Route;

/// The inverse of a map on its domain, in the bridges: Mathlib's asks a
/// nonempty type, which a statement over sets does not carry.
pub const INVERSE: &str = "LeanBridges.Functions.inverse";

/// The polynomial functions with complex coefficients, set.mm's `Poly ℂ`,
/// in the bridges: a page's polynomial is a function from ℂ to ℂ it holds.
const POLYNOMIALS: &str = "LeanBridges.Polynomials.polynomials";

/// `{x : T | body}`: the members of type `ty` the body holds of, `letter`
/// standing for each.
fn set_of(letter: &str, ty: LeanType, body: Printed) -> Printed {
    Printed::of(
        TermKind::Bound {
            form: super::doc::BoundForm::SetOf,
            letter: letter.to_string(),
            letter_ty: ty.clone(),
            body: Box::new(body),
        },
        LeanType::Set(Box::new(ty)),
    )
}

/// A count of a set in this form: a natural number, or in ℕ∞.
fn count_of(set: Printed, form: CountForm) -> Printed {
    let ty = match form {
        CountForm::Natural => LeanType::Num(Num::Nat),
        CountForm::Extended => LeanType::ENat,
    };
    Printed::of(
        TermKind::Count {
            set: Box::new(set),
            form,
        },
        ty,
    )
}

/// Whether a term counts, somewhere, a set not among `finite`: a count the
/// writer takes in ℕ∞.
pub fn counts_in_extended(
    grammar: &crate::formula::Grammar,
    finite: &crate::citing::finite::FiniteSets,
    node: &Node,
) -> bool {
    node.walk().iter().any(|n| {
        &*n.notation_name() == "cardinality"
            && n.children
                .first()
                .is_none_or(|set| !is_finite(grammar, finite, set))
    })
}

/// The parts `Writer::map_claim` writes for a line of this notation about
/// a map f from A to B, each with `_f`, `_A` and `_B` for those; None for
/// any other notation.
pub fn map_claim_parts(notation: &str) -> Option<&'static [&'static str]> {
    match notation {
        "function-type" => Some(&["Set.MapsTo _f _A _B"]),
        "one-to-one" => Some(&["Set.MapsTo _f _A _B", "Set.InjOn _f _A"]),
        "onto" => Some(&["Set.MapsTo _f _A _B", "Set.SurjOn _f _A _B"]),
        "one-to-one-onto" => Some(&[
            "Set.MapsTo _f _A _B",
            "Set.InjOn _f _A",
            "Set.SurjOn _f _A _B",
        ]),
        _ => None,
    }
}

/// The Lean type of a letter of this sort where it is a set, a member of
/// one or a map between sets; None for any other sort.
pub fn set_letter_type(sort: &crate::formula::Sort) -> Option<LetterType> {
    use crate::formula::Whole;
    match sort.full()? {
        Whole::Set(_) => Members::of_set(sort.full()?).map(LetterType::Set),
        Whole::Open => Some(LetterType::Member(Members::Things(0))),
        Whole::Property(inner) => Members::of(inner).map(LetterType::Property),
        Whole::Function(from, to) => Some(LetterType::Map {
            from: Members::of(from)?,
            to: Members::of(to)?,
        }),
        _ => None,
    }
}

impl Writer<'_> {
    /// What the members of a set term are; None for a term that is no set
    /// this writer has a type for.
    pub fn members_of(&self, node: &Node) -> Option<Members> {
        if node.is_name() {
            return match self.letters.get(node.text.as_str()) {
                Some(LetterType::Set(m)) => Some(m.clone()),
                // A member of a set of sets, the t of t ∈ 𝒫A, is a set.
                Some(LetterType::Member(Members::Sets(m))) => Some((**m).clone()),
                // A group, or a subgroup of it, holds the group's elements.
                Some(LetterType::Group) => {
                    Some(Members::Elements(node.text.to_string()))
                }
                Some(LetterType::Subgroup(g)) => Some(Members::Elements(g.clone())),
                _ => None,
            };
        }
        match &*node.notation_name() {
            // gH holds elements of g's group.
            "coset" => self.member_kind(node.children.first()?),
            "set-operations" | "set-builder" => {
                let first = match &*node.notation_name() {
                    "set-builder" => node.children.get(1)?,
                    _ => node.children.first()?,
                };
                self.set_members(first)
                    .or_else(|| node.children.get(1).and_then(|c| self.set_members(c)))
            }
            "powerset" => self
                .set_members(node.children.first()?)
                .map(|m| Members::Sets(Box::new(m))),
            "singleton" | "listed-two" | "listed-three" | "listed-four" => node
                .children
                .iter()
                .find_map(|c| self.member_kind(c))
                .or_else(|| self.numbers_held(&node.children))
                .or_else(|| self.sets_of_nothing(&node.children)),
            // {E(s) : s ∈ Y} holds what E(s) is.
            "set-image" => {
                let inner = self.set_image_inner(node)?;
                let term = node.children.first()?;
                inner
                    .member_kind(term)
                    .or_else(|| inner.numbers_held(std::slice::from_ref(term)))
            }
            // [a, b] and (a, b) hold real numbers.
            "closed-interval" | "open-interval" => Some(Members::Numbers(Num::Real)),
            // ⋃(x ∈ S) T holds what each T does, x a member of S.
            "indexed-union" => {
                let [x, s, t] = node.children.as_slice() else {
                    return None;
                };
                let mut inner = self.with_letters(self.letters.clone());
                inner
                    .letters
                    .insert(x.text.to_string(), self.set_members(s)?.letter());
                inner.set_members(t)
            }
            // A preimage holds what the map takes, an image what it gives.
            "image" => match self.preimage_of(node) {
                Some(f) => match self.letters.get(f.text.as_str()) {
                    Some(LetterType::Map { from, .. }) => Some(from.clone()),
                    Some(LetterType::Function { from, .. }) => {
                        Some(Members::Numbers(*from))
                    }
                    _ => None,
                },
                None => match self.letters.get(node.children.first()?.text.as_str()) {
                    Some(LetterType::Map { to, .. }) => Some(to.clone()),
                    Some(LetterType::Function { to, .. }) => {
                        Some(Members::Numbers(*to))
                    }
                    _ => None,
                },
            },
            // A map into sets applied, f(x) of f : A → 𝒫A, holds what each
            // of the sets it gives does.
            "application" => {
                match self.letters.get(node.children.first()?.text.as_str()) {
                    Some(LetterType::Map {
                        to: Members::Sets(m),
                        ..
                    }) => Some((**m).clone()),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// What a set term holds, as `members_of` says, or for a number system
    /// standing as a set, ℤ of ℝ ∖ ℤ, its numbers. A number system alone is
    /// left out of `members_of`, where `x ∈ ℤ` is read as a letter's type.
    pub fn set_members(&self, node: &Node) -> Option<Members> {
        // A range, {a, …, b}, holds integers.
        if node.notation() == crate::notations::INTEGER_RANGE {
            return Some(Members::Numbers(Num::Int));
        }
        self.members_of(node).or_else(|| {
            (node.notation() == NUMBER_SYSTEMS)
                .then(|| system_of(node))
                .flatten()
                .map(|s| Members::Numbers(set_type(s)))
        })
    }

    /// Numbers of the least type that holds all these terms, where every
    /// one is a number; None otherwise.
    fn numbers_held(&self, terms: &[Node]) -> Option<Members> {
        let mut at = Num::Int;
        for t in terms {
            if !self.is_number(t) {
                return None;
            }
            at = at.max(self.carrier(t).built()?);
        }
        Some(Members::Numbers(at))
    }

    /// A set of numbers written as a set of numbers of type `at`: a listed
    /// one with each member at that type, and any other as `set_term`
    /// writes it, where its members are already of that type.
    pub fn numbers_at(&self, set: &Node, at: Num) -> Route<Printed> {
        let listed = matches!(
            &*set.notation_name(),
            "singleton" | "listed-two" | "listed-three" | "listed-four"
        );
        // A narrower number system among wider numbers, ℚ among the reals:
        // the numbers its membership says are in it, as `in_system` writes
        // x ∈ ℚ of a real, `{x : ℝ | ∃ m : ℚ, (m : ℝ) = x}`.
        if let Some(system) = (set.notation() == NUMBER_SYSTEMS)
            .then(|| system_of(set))
            .flatten()
            .filter(|s| set_type(*s) < at)
        {
            let wide = self.num_type(at);
            let (narrow, positive) = match system {
                System::Type(n) => (self.num_type(n), false),
                System::Positive => (LeanType::Num(Num::Nat), true),
                System::NonNegative => (LeanType::Num(Num::Nat), false),
            };
            let m = Printed::letter("m", narrow.clone());
            let x = Printed::letter("x", wide.clone());
            let said = relation_of("=", Printed::cast(m.clone(), wide.clone()), x);
            let guard = positive
                .then(|| relation_of("<", Printed::numeral("0", narrow.clone()), m));
            let says = match (said, guard) {
                (Route::Built(s), None) => witnessed("m".to_string(), narrow, None, s),
                (Route::Built(s), Some(Route::Built(g))) => {
                    witnessed("m".to_string(), narrow, Some(g), s)
                }
                (Route::Declined(d), _) | (_, Some(Route::Declined(d))) => {
                    return Route::Declined(d)
                }
            };
            return Route::Built(set_of("x", wide, says));
        }
        if !listed {
            return match self.set_members(set) {
                Some(Members::Numbers(n)) if n == at => self.set_term(set),
                _ => Route::no(format!("a set of other than {} numbers", at.lean())),
            };
        }
        let mut members = Vec::new();
        for c in &set.children {
            match self.number_fixed(c, at) {
                Route::Built(p) => members.push(p),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        let of = LeanType::Set(Box::new(self.num_type(at)));
        Route::Built(Printed::cast(listed_set(members, of.clone()), of))
    }

    /// A member of a set of these, as Lean writes it: a number at the
    /// set's type, or a term as `set_term` writes it.
    pub fn element_term(&self, node: &Node, members: &Members) -> Route<Printed> {
        match members {
            Members::Numbers(n) => self.number_fixed(node, *n),
            _ => self.set_term(node),
        }
    }

    /// What kind of member a term is: a letter of a set's members, or a set
    /// itself, a member of a set of sets.
    pub fn member_kind(&self, node: &Node) -> Option<Members> {
        if node.is_name() {
            match self.letters.get(node.text.as_str()) {
                Some(LetterType::Member(m)) => return Some(m.clone()),
                Some(LetterType::Identity(g)) => {
                    return Some(Members::Elements(g.clone()))
                }
                _ => {}
            }
        }
        // A value by cases is a member of what its first value is.
        if &*node.notation_name() == "by-cases" {
            return self.member_kind(node.children.first()?);
        }
        // a·b and a⁻¹ in a group are elements of it.
        if matches!(&*node.notation_name(), "group-operation" | "group-inverse") {
            return node.children.iter().find_map(|c| self.member_kind(c));
        }
        if let Some(LetterType::Map { to, .. }) = node
            .children
            .first()
            .and_then(|f| self.letters.get(f.text.as_str()))
        {
            if &*node.notation_name() == "application" {
                return Some(to.clone());
            }
        }
        // g⁻¹(y) is a member of the set g maps from.
        let inverse = node.children.first().and_then(|f| self.inverted(f));
        if let Some(LetterType::Map { from, .. }) =
            inverse.and_then(|g| self.letters.get(g.text.as_str()))
        {
            if &*node.notation_name() == "application" {
                return Some(from.clone());
            }
        }
        self.members_of(node).map(|m| Members::Sets(Box::new(m)))
    }

    /// A set, a member of one, or a map, as Lean writes it.
    pub fn set_term(&self, node: &Node) -> Route<Printed> {
        if node.is_name() {
            let name = super::names::letter(&node.text);
            return match self.letters.get(node.text.as_str()) {
                Some(
                    ty @ (LetterType::Set(_)
                    | LetterType::Member(_)
                    | LetterType::Map { .. }
                    | LetterType::Function { .. }),
                ) => Route::Built(Printed::letter(name, ty.lean_type())),
                // A group standing as a set is all of its elements; its
                // identity is Lean's 1 of it; a subgroup as a set is its
                // elements.
                Some(LetterType::Group) => {
                    let of = LeanType::Set(Box::new(LeanType::Elements(
                        node.text.to_string(),
                    )));
                    Route::Built(Printed::cast(
                        Printed::head("Set.univ", Source::Mathlib),
                        of,
                    ))
                }
                Some(LetterType::Identity(g)) => Route::Built(Printed::cast(
                    Printed::numeral("1", LeanType::Elements(g.clone())),
                    LeanType::Elements(g.clone()),
                )),
                Some(LetterType::Subgroup(g)) => Route::Built(Printed::cast(
                    Printed::letter(name, LeanType::Subgroup(g.clone())),
                    LeanType::Set(Box::new(LeanType::Elements(g.clone()))),
                )),
                _ => Route::no(format!("{} is no set, member or map", node.text)),
            };
        }
        // a·b, a⁻¹ and gH of a group: Mathlib's `*`, `⁻¹`, and the left
        // coset.
        match &*node.notation_name() {
            "group-operation" => {
                let p = match self.set_parts(node, 2) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let ty = p[0].ty.clone();
                return Route::Built(Printed {
                    kind: TermKind::Infix {
                        op: super::doc::Op::TIMES,
                        lhs: Box::new(p[0].clone()),
                        rhs: Box::new(p[1].clone()),
                    },
                    ty,
                });
            }
            "group-inverse" => {
                let p = match self.set_parts(node, 1) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let ty = p[0].ty.clone();
                return Route::Built(Printed {
                    kind: TermKind::Postfix {
                        mark: super::doc::PostfixMark::Inverse,
                        inner: Box::new(p[0].clone()),
                    },
                    ty,
                });
            }
            // gH is the image of H under h ↦ g·h, as Mathlib's left coset
            // g • H is defined, written so that no scope need be opened.
            "coset" => {
                let p = match self.set_parts(node, 2) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let ty = p[1].ty.clone();
                let section = Printed {
                    kind: TermKind::Section {
                        op: super::doc::Op::TIMES,
                        left: Box::new(p[0].clone()),
                    },
                    ty: None,
                };
                return relation_of(
                    "''",
                    section,
                    super::expr::as_argument(p[1].clone()),
                )
                .map(|whole| Printed { ty, ..whole });
            }
            // F(x) if x ∈ A, G(x) otherwise, of things: as the notation's
            // template writes it of numbers, the condition decided
            // classically.
            "by-cases" => {
                let [first, condition, otherwise] = node.children.as_slice() else {
                    return Route::no("a define by cases of other than three parts");
                };
                let (a, b) = match (self.set_term(first), self.set_term(otherwise)) {
                    (Route::Built(a), Route::Built(b)) => (a, b),
                    (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                        return Route::Declined(d)
                    }
                };
                let c = match self.formula(condition) {
                    Route::Built(c) => c,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let decided = Printed::applied(
                    "Classical.propDecidable",
                    Source::Mathlib,
                    vec![c.clone()],
                    LeanType::Prop,
                );
                let ty = a.ty.clone();
                let args = [
                    Printed::of(TermKind::Elided, LeanType::Universe),
                    c,
                    decided,
                    a,
                    b,
                ];
                return Route::Built(Printed {
                    kind: TermKind::App {
                        head: Box::new(Printed::head("ite", Source::Core)),
                        args: args.into_iter().map(super::doc::Arg::Explicit).collect(),
                        explicit: true,
                    },
                    ty,
                });
            }
            _ => {}
        }
        // A number system standing as a set: all of its type, or for the
        // page's ℕ and ℕ₀ the integers above and from 0, so that a map from
        // them into ℤ, or a set of them an integer is said to be in, has
        // one type in and out.
        if let Some(system) = (node.notation() == NUMBER_SYSTEMS)
            .then(|| system_of(node))
            .flatten()
        {
            let int = LeanType::Num(Num::Int);
            let order = match system {
                super::expr::System::Positive => "<",
                super::expr::System::NonNegative => "≤",
                super::expr::System::Type(_) => {
                    let of =
                        LeanType::Set(Box::new(LeanType::Num(letter_type(system))));
                    return Route::Built(Printed::cast(
                        Printed::head("Set.univ", Source::Mathlib),
                        of,
                    ));
                }
            };
            let n = Printed::letter("n", int.clone());
            return relation_of(order, Printed::numeral("0", int.clone()), n)
                .map(|bound| set_of("n", int, bound));
        }
        let parts = |want: usize| self.set_parts(node, want);
        match &*node.notation_name() {
            "set-operations" => {
                // Of sets of numbers, both at the wider of their types: ℝ ∖
                // {2} is `Set.univ \ ({2} : Set ℝ)`.
                let numbers: Option<Num> = node
                    .children
                    .iter()
                    .map(|c| match self.set_members(c) {
                        Some(Members::Numbers(n)) => Some(n),
                        _ => None,
                    })
                    .collect::<Option<Vec<Num>>>()
                    .and_then(|ns| ns.into_iter().max());
                let p = match numbers {
                    Some(at) => {
                        let mut out = Vec::new();
                        for c in &node.children {
                            match self.numbers_at(c, at) {
                                Route::Built(x) => out.push(x),
                                Route::Declined(d) => return Route::Declined(d),
                            }
                        }
                        out
                    }
                    None => match parts(2) {
                        Route::Built(p) => p,
                        Route::Declined(d) => return Route::Declined(d),
                    },
                };
                // Lean's ∪ binds at 65 and ∩ and \ at 70, and reads no ∩
                // beside a \ unbracketed, so an operation inside another is
                // bracketed whatever it is.
                let op = match &*node.spelling().text() {
                    "∪" => "∪",
                    "∩" => "∩",
                    "∖" => "\\",
                    other => return Route::no(format!("the set operation {other}")),
                };
                let Some(op) = super::doc::Op::of(op) else {
                    return Route::no(format!("the set operation {op}"));
                };
                let inside = |p: &Printed| match p.prec() <= op.prec {
                    true => super::tactics::bracket(p.clone()),
                    false => p.clone(),
                };
                Route::Built(Printed {
                    kind: TermKind::Infix {
                        op,
                        lhs: Box::new(inside(&p[0])),
                        rhs: Box::new(inside(&p[1])),
                    },
                    ty: p[0].ty.clone(),
                })
            }
            // [a, b] and (a, b), the reals from a to b, ends in or out.
            interval @ ("closed-interval" | "open-interval") => {
                let [from, to] = node.children.as_slice() else {
                    return Route::no("an interval of other than two ends");
                };
                let lean = match interval {
                    "closed-interval" => "Set.Icc",
                    _ => "Set.Ioo",
                };
                match (
                    self.number_fixed(from, Num::Real),
                    self.number_fixed(to, Num::Real),
                ) {
                    (Route::Built(a), Route::Built(b)) => {
                        let of = LeanType::Set(Box::new(LeanType::Num(Num::Real)));
                        Route::Built(Printed::cast(
                            Printed::applied(
                                lean,
                                Source::Mathlib,
                                vec![a, b],
                                of.clone(),
                            ),
                            of,
                        ))
                    }
                    (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                        Route::Declined(d)
                    }
                }
            }
            // {a, …, b}, the integers from a to b.
            "integer-range" => {
                let [from, to] = node.children.as_slice() else {
                    return Route::no("a range of other than two ends");
                };
                match (
                    self.number_fixed(from, Num::Int),
                    self.number_fixed(to, Num::Int),
                ) {
                    (Route::Built(a), Route::Built(b)) => {
                        let of = LeanType::Set(Box::new(LeanType::Num(Num::Int)));
                        Route::Built(Printed::cast(
                            Printed::applied(
                                "Set.Icc",
                                Source::Mathlib,
                                vec![a, b],
                                of.clone(),
                            ),
                            of,
                        ))
                    }
                    (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                        Route::Declined(d)
                    }
                }
            }
            "powerset" => match parts(1) {
                Route::Built(p) => {
                    let ty = p[0].ty.clone().map(|t| LeanType::Set(Box::new(t)));
                    Route::Built(Printed {
                        kind: TermKind::Prefix {
                            mark: super::doc::PrefixMark::Powerset,
                            inner: Box::new(p[0].clone()),
                        },
                        ty,
                    })
                }
                Route::Declined(d) => Route::Declined(d),
            },
            "empty-set" => Route::Built(Printed::head("∅", Source::Core)),
            "singleton" | "listed-two" | "listed-three" | "listed-four" => {
                // Ascribed its type, which Lean cannot take from a member
                // alone: `{u, w}` of things of α is `({u, w} : Set α)`.
                let Some(members) = self.members_of(node) else {
                    return Route::no("a listed set of members with no Lean type");
                };
                self.listed(node, &members)
            }
            "image" if self.preimage_of(node).is_some() => self.preimage(node),
            // f[{1, 2}] of a function on numbers: the set at the type the
            // function takes, which may be wider than its own members'.
            "image"
                if matches!(
                    node.children
                        .first()
                        .and_then(|f| self.letters.get(f.text.as_str())),
                    Some(LetterType::Function { .. })
                ) =>
            {
                let [f, set] = node.children.as_slice() else {
                    return Route::no("an image of other than a map and a set");
                };
                let Some(LetterType::Function { from, .. }) =
                    self.letters.get(f.text.as_str())
                else {
                    return Route::no("an image under no function");
                };
                match self.numbers_at(set, *from) {
                    Route::Built(s) => self.image_within(f, &s),
                    Route::Declined(d) => Route::Declined(d),
                }
            }
            "image" => match (node.children.as_slice(), parts(2)) {
                ([f, _], Route::Built(p)) => self.image_within(f, &p[1]),
                (_, Route::Built(_)) => {
                    Route::no("an image of other than a map and a set")
                }
                (_, Route::Declined(d)) => Route::Declined(d),
            },
            "set-builder" => self.set_builder(node),
            // ⋃(x ∈ S) T, the union of T as x runs over S: `⋃ x ∈ S, T`.
            "indexed-union" => {
                let [x, s, t] = node.children.as_slice() else {
                    return Route::no("a union of other than three parts");
                };
                let Some(over) = self.set_members(s) else {
                    return Route::no("a union over a set with no Lean type");
                };
                let mut inner = self.with_letters(self.letters.clone());
                inner.letters.insert(x.text.to_string(), over.letter());
                match (self.set_term(s), inner.set_term(t)) {
                    (Route::Built(a), Route::Built(b)) => {
                        let ty = b.ty.clone();
                        Route::Built(Printed {
                            kind: TermKind::Bound {
                                form: super::doc::BoundForm::Union { set: Box::new(a) },
                                letter: super::names::letter(&x.text),
                                letter_ty: over.letter().lean_type(),
                                body: Box::new(b),
                            },
                            ty,
                        })
                    }
                    (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                        Route::Declined(d)
                    }
                }
            }
            "set-image" => self.set_image(node),
            "application" => self.map_applied(node),
            other => Route::no(format!("{other} as a set")),
        }
    }

    /// The map letter whose inverse an image is taken under, the f of
    /// f⁻¹[Z]; None for any other image.
    fn preimage_of<'n>(&self, node: &'n Node) -> Option<&'n Node> {
        self.inverted(node.children.first()?)
    }

    /// The map letter a term is the inverse of, the g of g⁻¹; None for any
    /// other term.
    fn inverted<'n>(&self, node: &'n Node) -> Option<&'n Node> {
        let [g] = node.children.as_slice() else {
            return None;
        };
        let inverse = &*node.notation_name() == "inverse"
            && matches!(
                self.letters.get(g.text.as_str()),
                Some(LetterType::Map { .. } | LetterType::Function { .. })
            );
        inverse.then_some(g)
    }

    /// f[Y], what f sends the members of Y in its domain D to, as set.mm
    /// takes it: `f '' (D ∩ Y)`. Lean's f is total, and its image of all of
    /// Y would hold values the page's f does not have.
    fn image_within(&self, f: &Node, set: &Printed) -> Route<Printed> {
        let Some(domain) = self.domain_of(&f.text) else {
            return Route::no(format!(
                "an image under {}, whose domain no line gives",
                f.text
            ));
        };
        // The function is a term of the notation, not text, so that a
        // value put for its letter, the citing page's F for an item's f,
        // stands in its place.
        let function = Printed {
            kind: TermKind::Letter(super::names::letter(&f.text)),
            ty: None,
        };
        let within =
            match relation_of("∩", super::expr::as_argument(domain), set.clone()) {
                Route::Built(w) => w,
                Route::Declined(d) => return Route::Declined(d),
            };
        relation_of("''", function, super::tactics::bracket(within)).map(|whole| {
            Printed {
                ty: set.ty.clone(),
                ..whole
            }
        })
    }

    /// The set a map or function is defined on, as Lean writes it: the one
    /// a line gives it, or for a function given between number systems,
    /// all of its type; None for any other letter.
    pub fn domain_of(&self, f: &str) -> Option<Printed> {
        if let Some(d) = self.domains.get(f) {
            return Some(d.clone());
        }
        match self.letters.get(f) {
            Some(LetterType::Function { from, .. }) if *from != Num::Nat => {
                let of = LeanType::Set(Box::new(LeanType::Num(*from)));
                Some(Printed::cast(
                    Printed::head("Set.univ", Source::Mathlib),
                    of,
                ))
            }
            _ => None,
        }
    }

    /// f⁻¹[Z], what f sends into Z, taken within f's domain A as set.mm
    /// takes it: `A ∩ f ⁻¹' Z`.
    fn preimage(&self, node: &Node) -> Route<Printed> {
        let (Some(f), Some(z)) = (self.preimage_of(node), node.children.get(1)) else {
            return Route::no("a preimage of other than a map and a set");
        };
        let Some(domain) = self.domain_of(&f.text) else {
            return Route::no(format!(
                "a preimage under {}, whose domain no line gives",
                f.text
            ));
        };
        match self.set_term(z) {
            Route::Built(z) => {
                let ty = domain.ty.clone();
                let function = Printed {
                    kind: TermKind::Letter(super::names::letter(&f.text)),
                    ty: None,
                };
                let sent =
                    match relation_of("⁻¹'", function, super::expr::as_argument(z)) {
                        Route::Built(s) => s,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                relation_of("∩", super::expr::as_argument(domain), sent)
                    .map(|whole| Printed { ty, ..whole })
            }
            Route::Declined(d) => Route::Declined(d),
        }
    }

    /// Each part of a set term, written as a set's, where it has `want`.
    fn set_parts(&self, node: &Node, want: usize) -> Route<Vec<Printed>> {
        if node.children.len() != want {
            return Route::no(format!(
                "{} of {} parts",
                node.notation_name(),
                node.children.len()
            ));
        }
        let mut out = Vec::new();
        for c in &node.children {
            match self.set_term(c) {
                Route::Built(p) => out.push(p),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        Route::Built(out)
    }

    /// {t ∈ X : P(t)}, `{t ∈ X | P t}`: the letter a member of X's, and
    /// the condition read with it.
    fn set_builder(&self, node: &Node) -> Route<Printed> {
        let [letter, set, body] = node.children.as_slice() else {
            return Route::no("a set-builder of other than three parts");
        };
        let Some(members) = self.set_members(set) else {
            return Route::no("a set-builder over a set with no Lean type");
        };
        let mut inner = self.with_letters(self.letters.clone());
        inner
            .letters
            .insert(letter.text.to_string(), members.letter());
        inner.wholes.shift_remove(&*letter.text);
        // A member of ℕ, ℕ₀ or a range from 0 or 1 is in that system, as a
        // letter a line puts there is.
        let system = match super::expr::system_of(set) {
            Some(s) => Some(s),
            None if set.notation() == crate::notations::INTEGER_RANGE => {
                Some(super::expr::range_letter_system(set))
            }
            None => None,
        };
        if let Some(
            s @ (super::expr::System::Positive | super::expr::System::NonNegative),
        ) = system
        {
            inner.introduce(&letter.text, s);
        }
        let condition = match inner.formula(body) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let name = super::names::letter(&letter.text);
        // Over a number system, the numbers of its type: {n ∈ ℤ : P(n)} is
        // `{n : ℤ | P n}`, and the page's ℕ and ℕ₀, integers here as
        // `set_term` writes them, add that n is above or from 0.
        if let Some(system) = (set.notation() == NUMBER_SYSTEMS)
            .then(|| system_of(set))
            .flatten()
        {
            let ty = LeanType::Num(set_type(system));
            let order = match system {
                super::expr::System::Positive => Some("<"),
                super::expr::System::NonNegative => Some("≤"),
                super::expr::System::Type(_) => None,
            };
            let body = match order {
                Some(order) => {
                    let bound = match relation_of(
                        order,
                        Printed::numeral("0", ty.clone()),
                        Printed::letter(name.clone(), ty.clone()),
                    ) {
                        Route::Built(b) => b,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    match relation_of("∧", bound, condition) {
                        Route::Built(b) => b,
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                None => condition,
            };
            return Route::Built(set_of(&name, ty, body));
        }
        let domain = match self.set_term(set) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let ty = domain.ty.clone();
        let Some(LeanType::Set(member)) = ty.clone() else {
            return Route::no("a set-builder over a set with no type of members");
        };
        Route::Built(Printed {
            kind: TermKind::Bound {
                form: super::doc::BoundForm::SetOfMember {
                    set: Box::new(domain),
                },
                letter: name,
                letter_ty: *member,
                body: Box::new(condition),
            },
            ty,
        })
    }

    /// The writer a set-image's term is read with, {E(s) : s ∈ Y}: its
    /// letter a member of Y's kind. None where Y is no set this writer has
    /// a type for.
    fn set_image_inner(&self, node: &Node) -> Option<Writer<'_>> {
        let [_, letter, set] = node.children.as_slice() else {
            return None;
        };
        let members = self.set_members(set)?;
        let mut inner = self.with_letters(self.letters.clone());
        inner
            .letters
            .insert(letter.text.to_string(), members.letter());
        Some(inner)
    }

    /// {E(s) : s ∈ Y}, what E(s) is as s runs over Y: Mathlib's image of the
    /// function s ↦ E(s), `(fun s => E s) '' Y`.
    fn set_image(&self, node: &Node) -> Route<Printed> {
        let [term, letter, set] = node.children.as_slice() else {
            return Route::no("a set-image of other than three parts");
        };
        let (Some(inner), Some(members)) =
            (self.set_image_inner(node), self.members_of(node))
        else {
            return Route::no("a set-image over a set with no Lean type");
        };
        // The letter is told the type of the set it runs over, which its
        // body alone may not fix: n of {p·n : n ∈ ℕ} is a natural number.
        let Some(over) = self.set_members(set) else {
            return Route::no("a set-image over a set with no Lean type");
        };
        match (inner.element_term(term, &members), self.set_term(set)) {
            (Route::Built(t), Route::Built(y)) => {
                let rule = Printed::of(
                    TermKind::Quantified {
                        quant: super::doc::Quant::Fun,
                        letter: super::names::letter(&letter.text),
                        letter_ty: over.letter().lean_type(),
                        guard: None,
                        body: Box::new(t),
                        bounded: false,
                    },
                    LeanType::Fun {
                        from: Box::new(over.letter().lean_type()),
                        to: Box::new(members.member_type()),
                    },
                );
                relation_of("''", rule, super::expr::as_argument(y)).map(|whole| {
                    Printed {
                        ty: Some(LeanType::Set(Box::new(members.member_type()))),
                        ..whole
                    }
                })
            }
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        }
    }

    /// f(x) of a map: its value, a member of the set it maps into.
    fn map_applied(&self, node: &Node) -> Route<Printed> {
        let [f, x] = node.children.as_slice() else {
            return Route::no("a map applied to other than one argument");
        };
        // g⁻¹(y): the thing in g's domain that g sends to y.
        if let Some(g) = self.inverted(f) {
            let Some(domain) = self.domains.get(g.text.as_str()) else {
                return Route::no(format!("{}⁻¹, whose domain no line gives", g.text));
            };
            let from = self.letters.get(g.text.as_str()).map(LetterType::lean_type);
            let letter = Printed {
                kind: TermKind::Letter(super::names::letter(&g.text)),
                ty: from,
            };
            let domain = domain.clone();
            return self.set_term(x).map(|p| {
                let ty = domain.ty.clone();
                Printed {
                    kind: TermKind::App {
                        head: Box::new(Printed::head(
                            INVERSE,
                            Source::Bridge(BridgeModule::Functions),
                        )),
                        args: [letter, domain, p]
                            .into_iter()
                            .map(super::doc::Arg::Explicit)
                            .collect(),
                        explicit: false,
                    },
                    ty,
                }
            });
        }
        let Some(map) = self.map_term(f) else {
            return Route::no(format!("{} applied, which is no map", f.text));
        };
        let (from, to) = match self.letters.get(f.text.as_str()) {
            Some(LetterType::Map { from, to }) => (Some(from), Some(to.member_type())),
            _ => (None, None),
        };
        // A map from numbers, v : ℕ₀ → V, takes a number, v(0).
        let argument = match from {
            Some(Members::Numbers(n)) => self.number_fixed(x, *n),
            _ => self.set_term(x),
        };
        argument.map(|p| Printed {
            kind: TermKind::App {
                head: Box::new(map),
                args: vec![super::doc::Arg::Explicit(p)],
                explicit: false,
            },
            ty: to,
        })
    }

    /// A map as Lean writes it applied: a map letter, or g ∘ f of maps,
    /// `(g ∘ f)`; None for anything else.
    fn map_term(&self, f: &Node) -> Option<Printed> {
        if f.is_name() {
            return match self.letters.get(f.text.as_str()) {
                Some(ty @ LetterType::Map { .. }) => Some(Printed::letter(
                    super::names::letter(&f.text),
                    ty.lean_type(),
                )),
                _ => None,
            };
        }
        match (&*f.notation_name(), f.children.as_slice()) {
            ("composition", [g, inner]) => {
                let (outer, inner) = (self.map_term(g)?, self.map_term(inner)?);
                let ty = outer.ty.clone();
                let composed = Printed {
                    kind: TermKind::Infix {
                        op: super::doc::Op::COMPOSE,
                        lhs: Box::new(outer),
                        rhs: Box::new(inner),
                    },
                    ty: ty.clone(),
                };
                Some(Printed {
                    kind: TermKind::Paren(Box::new(composed)),
                    ty,
                })
            }
            _ => None,
        }
    }

    /// What a map between sets is: `f : A → B` is `Set.MapsTo f A B`, and
    /// one-to-one and onto add `Set.InjOn f A` and `Set.SurjOn f A B`, each
    /// a part of a conjunction a hypothesis is taken apart by. None where
    /// the node says none of these of a map letter.
    pub fn map_claim(&self, node: &Node) -> Option<Route<Printed>> {
        let parts = map_claim_parts(&node.notation_name())?;
        let [f, from, to] = node.children.as_slice() else {
            return None;
        };
        // A map between sets, or a function between number systems, whose
        // sets are all of its types.
        if !matches!(
            self.letters.get(f.text.as_str()),
            Some(LetterType::Map { .. } | LetterType::Function { .. })
        ) {
            return None;
        }
        // f : ℤ → ℤ alone is said by f's Lean type, as `formula` writes it.
        let function = matches!(
            self.letters.get(f.text.as_str()),
            Some(LetterType::Function { .. })
        );
        if function && parts.len() == 1 {
            return None;
        }
        let (a, b) = match (self.set_term(from), self.set_term(to)) {
            (Route::Built(a), Route::Built(b)) => (a, b),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Some(Route::Declined(d))
            }
        };
        let map = Printed {
            kind: TermKind::Letter(super::names::letter(&f.text)),
            ty: self.letters.get(f.text.as_str()).map(LetterType::lean_type),
        };
        let mut claims: Vec<Printed> = Vec::new();
        for part in parts {
            let mut words = part.split_whitespace();
            let Some(head) = words.next() else {
                continue;
            };
            let args: Vec<Printed> = words
                .map(|w| match w {
                    "_f" => map.clone(),
                    "_A" => a.clone(),
                    _ => b.clone(),
                })
                .collect();
            claims.push(Printed::applied(
                head,
                Source::Mathlib,
                args,
                LeanType::Prop,
            ));
        }
        if let [one] = claims.as_slice() {
            return Some(Route::Built(one.clone()));
        }
        super::expr::joined(super::doc::Op::AND, claims, 36).map(Route::Built)
    }

    /// Whether a term counts, somewhere, a set no line says is finite, |A|
    /// or |A| + 1: a count in ℕ∞.
    pub fn counts(&self, node: &Node) -> bool {
        counts_in_extended(self.grammar, &self.finite, node)
    }

    /// Whether a relation that counts a set is one ℕ∞ says as the page
    /// does (`citing::finite::said_in_extended`), its letters in ℕ or ℕ₀
    /// those the page puts there (written `↑m.toNat` there, `count_term`).
    pub fn said_in_extended(&self, node: &Node) -> bool {
        crate::citing::finite::said_in_extended(node, &|l| {
            bounds::BoundsAsk::natural_letter(self, l)
        })
    }

    /// The sets the checker records finite are the ones this writer counts
    /// as natural numbers.
    pub fn finite_from(&mut self, said: &SaidFinite) {
        self.finite = said.sets.clone();
        self.finite_only_by = said.only_by.clone();
    }

    /// The writer a hypothesis is written with: one counting as finite only
    /// what the other hypotheses make finite, where the line may not vouch
    /// for itself. `|X| = m` written with `X.ncard` would hold of every
    /// infinite X too where m is 0; `X.encard = m` says X has m elements.
    /// None where the line vouches for every set it makes finite.
    pub fn without_line(&self, line: &Node) -> Option<Writer<'_>> {
        let only = self.finite_only_by.get(&self.grammar.print(line))?;
        let mut out = self.with_letters(self.letters.clone());
        out.finite.retain(|s, _| !only.contains(s));
        Some(out)
    }

    /// |A| of a set a line says is finite: the natural number `A.ncard`.
    /// None for any other term.
    pub fn finite_count(&self, node: &Node) -> Option<Route<Printed>> {
        let [set] = node.children.as_slice() else {
            return None;
        };
        let finite = &*node.notation_name() == "cardinality"
            && is_finite(self.grammar, &self.finite, set);
        // ∅ counted is told it is a set of things, which nothing else in
        // |∅| = 0 gives Lean.
        if finite && &*set.notation_name() == "empty-set" {
            return Some(Route::Built(count_of(
                self.empty_told(),
                CountForm::Natural,
            )));
        }
        finite.then(|| self.set_term(set).map(|s| count_of(s, CountForm::Natural)))
    }

    /// ∅ told what it holds, `(∅ : Set α)`: what `empty_of` says, or the
    /// things of the first type variable.
    fn empty_told(&self) -> Printed {
        let of = match &self.empty_of {
            Some(m) => Members::Sets(Box::new(m.clone())).member_type(),
            None => LeanType::Set(Box::new(LeanType::Things(0))),
        };
        super::expr::empty_of_type(of)
    }

    /// A count as Lean's `Set.encard` gives it, in ℕ∞, where an infinite
    /// set counts as ∞ as set.mm's ♯ counts it +∞: |A| is `A.encard`; a
    /// numeral, a letter of ℕ or ℕ₀, or a count of a finite set,
    /// `A.ncard`, is cast up; and + and · are ℕ∞'s. Subtraction declines:
    /// ℕ∞'s stops at 0, where the page's does not.
    pub fn count_term(&self, node: &Node) -> Route<Printed> {
        // A number of ℕ, the type ℕ∞ holds, cast up.
        if !self.counts(node) {
            return match self.number_fixed(node, Num::Nat) {
                Route::Built(p) => Route::Built(Printed::cast(
                    Printed::cast(p, LeanType::Num(Num::Nat)),
                    LeanType::ENat,
                )),
                Route::Declined(d) => Route::Declined(d),
            };
        }
        if &*node.notation_name() == "cardinality" {
            let [set] = node.children.as_slice() else {
                return Route::no("a count of other than one set");
            };
            // ∅ counted is told it is a set of things, which nothing else
            // in |∅| = 0 gives Lean.
            if &*set.notation_name() == "empty-set" {
                return Route::Built(count_of(self.empty_told(), CountForm::Extended));
            }
            return self.set_term(set).map(|s| count_of(s, CountForm::Extended));
        }
        let op = match (&*node.notation_name(), &*node.spelling().text()) {
            ("additive", "+") => "+",
            ("multiplicative", "·") => "*",
            (_, other) => {
                return Route::left_out(format!(
                    "{other} of a count, which ℕ∞ does not compute as the page does"
                ))
            }
        };
        let [a, b] = node.children.as_slice() else {
            return Route::no("an operation on a count of other than two parts");
        };
        let Some(op) = super::doc::Op::of(op) else {
            return Route::no(format!("the operation {op} on counts"));
        };
        match (self.count_term(a), self.count_term(b)) {
            (Route::Built(a), Route::Built(b)) => {
                Route::Built(Printed::infix(op, a, b, LeanType::ENat))
            }
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        }
    }

    /// An equation or order between counts, |A| = 2 or 1 ≤ |A|, both sides
    /// in ℕ∞; None where neither side counts a set.
    pub fn count_relation(&self, node: &Node) -> Option<Route<Printed>> {
        let [a, b] = node.children.as_slice() else {
            return None;
        };
        if !self.counts(a) && !self.counts(b) {
            return None;
        }
        if let Some(said) = self.count_equals_number(node) {
            return Some(said);
        }
        let op = node.spelling().text().to_string();
        Some(match (self.count_term(a), self.count_term(b)) {
            (Route::Built(a), Route::Built(b)) => relation_of(&op, a, b),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        })
    }

    /// |S| = j of a set S not known finite and a number j no natural number
    /// of ℕ∞'s: the count is a natural number that is j, `∃ m : ℕ, S.encard
    /// = m ∧ (m : ℤ) = j`, as set.mm's (♯‘S) = j is false of an infinite S
    /// and of a j no count is. None for any other relation; an order is not
    /// said so, since j ≤ |S| holds of an infinite S, ♯ being +∞ there.
    fn count_equals_number(&self, node: &Node) -> Option<Route<Printed>> {
        let [a, b] = node.children.as_slice() else {
            return None;
        };
        let bare = |n: &Node| &*n.notation_name() == "cardinality" && self.counts(n);
        let (count, number, count_first) = match (bare(a), bare(b)) {
            (true, false) if !self.counts(b) => (a, b, true),
            (false, true) if !self.counts(a) => (b, a, false),
            _ => return None,
        };
        if node.notation() != crate::notations::EQUALITY
            || crate::citing::finite::natural_beside_count(number, &|l| {
                bounds::BoundsAsk::natural_letter(self, l)
            })
        {
            return None;
        }
        let at = match self.carrier(number) {
            Route::Built(n) => n,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let (count, number) =
            match (self.count_term(count), self.number_fixed(number, at)) {
                (Route::Built(c), Route::Built(n)) => (c, n),
                (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                    return Some(Route::Declined(d))
                }
            };
        let m = super::expr::witness_letter(node);
        let nat = LeanType::Num(Num::Nat);
        let letter = Printed::letter(m.clone(), nat.clone());
        let cast = Printed::cast(letter.clone(), self.num_type(at));
        let equation = match count_first {
            true => relation_of("=", cast, number),
            false => relation_of("=", number, cast),
        };
        let counted = relation_of("=", count, Printed::cast(letter, LeanType::ENat));
        Some(match (counted, equation) {
            (Route::Built(c), Route::Built(e)) => {
                Route::Built(witnessed(m, nat, Some(c), e))
            }
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        })
    }

    /// A count in ℕ or ℕ₀, |A| ∈ ℕ: some natural number is the count, and
    /// for the page's ℕ, which starts at 1, one above 0. None where the term
    /// counts no set.
    pub fn count_in_system(&self, x: &Node, set: &Node) -> Option<Route<Printed>> {
        if !self.counts(x) {
            return None;
        }
        let count = match self.count_term(x) {
            Route::Built(p) => p,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let m = super::expr::witness_letter(x);
        let nat = LeanType::Num(Num::Nat);
        let letter = Printed::letter(m.clone(), nat.clone());
        let above = match system_of(set) {
            Some(super::expr::System::Positive) => Some(relation_of(
                "<",
                Printed::numeral("0", nat.clone()),
                letter.clone(),
            )),
            Some(super::expr::System::NonNegative) => None,
            _ => return Some(Route::no("a count in other than ℕ or ℕ₀")),
        };
        let said = relation_of("=", Printed::cast(letter, LeanType::ENat), count);
        Some(match (above, said) {
            (None, Route::Built(s)) => Route::Built(witnessed(m, nat, None, s)),
            (Some(Route::Built(a)), Route::Built(s)) => {
                Route::Built(witnessed(m, nat, Some(a), s))
            }
            (Some(Route::Declined(d)), _) | (_, Route::Declined(d)) => {
                Route::Declined(d)
            }
        })
    }

    /// H is a subgroup of G, of a letter Lean types `Subgroup G`: its type
    /// says it, so the claim is `True`. None for any other claim.
    pub fn subgroup_claim(&self, node: &Node) -> Option<Route<Printed>> {
        if &*node.notation_name() != "subgroup" {
            return None;
        }
        let [h, g] = node.children.as_slice() else {
            return None;
        };
        let typed = matches!(self.letters.get(h.text.as_str()),
            Some(LetterType::Subgroup(of)) if *of == *g.text);
        Some(match typed {
            true => Route::Built(Printed::truth()),
            false => {
                Route::no(format!("{} as a subgroup, which no line types", h.text))
            }
        })
    }

    /// p is a polynomial, or x ∈ the polynomials: a function from ℂ to ℂ in
    /// set.mm's polynomials, which the bridges define (`POLYNOMIALS`). None
    /// for any other claim.
    pub fn polynomial_claim(&self, node: &Node) -> Option<Route<Printed>> {
        let p = match (&*node.notation_name(), node.children.as_slice()) {
            ("is-a-polynomial", [p]) => p,
            ("membership", [p, set]) if &*set.notation_name() == "polynomials" => p,
            _ => return None,
        };
        Some(match self.set_term(p) {
            Route::Built(f) => relation_of(
                "∈",
                f,
                Printed::head(POLYNOMIALS, Source::Bridge(BridgeModule::Polynomials)),
            ),
            Route::Declined(d) => Route::Declined(d),
        })
    }

    /// For all, or there is, a polynomial q: a function from ℂ to ℂ, and
    /// that it is one; None where the set is not the polynomials.
    pub fn quantified_over_polynomials(
        &self,
        letter: &Node,
        set: &Node,
        body: &Node,
        exists: bool,
    ) -> Option<Route<Printed>> {
        if &*set.notation_name() != "polynomials" {
            return None;
        }
        let mut inner = self.with_letters(self.letters.clone());
        inner.letters.insert(
            letter.text.to_string(),
            LetterType::Function {
                from: Num::Complex,
                to: Num::Complex,
            },
        );
        let body = match inner.formula(body) {
            Route::Built(p) => p,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let q = super::names::letter(&letter.text);
        let complex = LeanType::Num(Num::Complex);
        let ty = LeanType::Fun {
            from: Box::new(complex.clone()),
            to: Box::new(complex),
        };
        let polynomial = match relation_of(
            "∈",
            Printed::letter(q.clone(), ty.clone()),
            Printed::head(POLYNOMIALS, Source::Bridge(BridgeModule::Polynomials)),
        ) {
            Route::Built(p) => p,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        Some(Route::Built(Printed::of(
            TermKind::Quantified {
                quant: match exists {
                    true => super::doc::Quant::Exists,
                    false => super::doc::Quant::ForAll,
                },
                letter: q,
                letter_ty: ty,
                guard: Some(Box::new(polynomial)),
                body: Box::new(body),
                bounded: false,
            },
            LeanType::Prop,
        )))
    }

    /// X is finite: `X.Finite`.
    pub fn finite(&self, node: &Node) -> Option<Route<Printed>> {
        if &*node.notation_name() != "finite" {
            return None;
        }
        let [set] = node.children.as_slice() else {
            return None;
        };
        Some(match self.set_term(set) {
            Route::Built(s) => Route::Built(Printed::of(
                TermKind::Field {
                    inner: Box::new(s),
                    field: "Finite".to_string(),
                },
                LeanType::Prop,
            )),
            Route::Declined(d) => Route::Declined(d),
        })
    }

    /// A listed set, {u, w}, of members of the type given, ascribed it, which
    /// Lean cannot take from a member alone: `({u, w} : Set α)`.
    fn listed(&self, node: &Node, members: &Members) -> Route<Printed> {
        let mut listed = Vec::new();
        for c in &node.children {
            match self.element_term(c, members) {
                Route::Built(p) => listed.push(p),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        let of = LeanType::Set(Box::new(self.members_type(members)));
        Route::Built(Printed::cast(listed_set(listed, of.clone()), of))
    }

    /// The type of such members here: numbers of the type an item is
    /// general in are of K.
    fn members_type(&self, members: &Members) -> LeanType {
        match members {
            Members::Numbers(n) => self.num_type(*n),
            other => other.member_type(),
        }
    }

    /// What a listed set of ∅ alone holds, {∅}, which its members do not
    /// say: in a theorem whose sets hold things, of one type α, sets of
    /// those. None where a member is anything but ∅, or no letter holds
    /// things.
    pub fn sets_of_nothing(&self, members: &[Node]) -> Option<Members> {
        let empties = members.iter().all(|m| &*m.notation_name() == "empty-set");
        let things = self.letters.values().any(|t| t.things_vars().contains(&0));
        (empties && things).then(|| Members::Sets(Box::new(Members::Things(0))))
    }

    /// A set where what it holds is known from elsewhere: a listed set at
    /// those members, {∅} as `({∅} : Set (Set ℤ))`; any other as the writer
    /// writes it.
    pub fn listed_as(&self, node: &Node, members: &Members) -> Route<Printed> {
        match &*node.notation_name() {
            "singleton" | "listed-two" | "listed-three" | "listed-four" => {
                self.listed(node, members)
            }
            _ => self.set_term(node),
        }
    }

    /// x ∈ S of a set S this writer has a type for: `x ∈ S`.
    pub fn set_membership(&self, x: &Node, set: &Node) -> Option<Route<Printed>> {
        // A set whose members say no type, ∅ or {∅}, holds what x is, so
        // x ∈ ∅ is of x's type.
        let empty = &*set.notation_name() == "empty-set";
        let listed = matches!(
            &*set.notation_name(),
            "empty-set" | "singleton" | "listed-two" | "listed-three" | "listed-four"
        );
        let members = self.members_of(set).or_else(|| {
            listed
                .then(|| {
                    self.member_kind(x)
                        .or_else(|| self.numbers_held(std::slice::from_ref(x)))
                })
                .flatten()
        })?;
        // ∅ is told its type, which nothing else in `t ∈ ∅` gives Lean, and
        // so is a listed set whose members give none, {∅}.
        let set_term = match (empty, listed) {
            (true, _) => Route::Built(super::expr::empty_of_type(LeanType::Set(
                Box::new(members.member_type()),
            ))),
            (false, true) => self.listed(set, &members),
            (false, false) => self.set_term(set),
        };
        Some(match (self.element_term(x, &members), set_term) {
            (Route::Built(a), Route::Built(b)) => relation_of("∈", a, b),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        })
    }

    /// A relation between two sets, A = B or A ⊆ B, or two members of one,
    /// x = u; None where neither side is a set or a member this writer has a
    /// type for.
    pub fn set_relation(&self, node: &Node, op: &str) -> Option<Route<Printed>> {
        let [a, b] = node.children.as_slice() else {
            return None;
        };
        // A number system compared as a set, ℤ ⊆ ℤ, is one here.
        self.set_members(a)
            .or_else(|| self.set_members(b))
            .or_else(|| self.member_kind(a))
            .or_else(|| self.member_kind(b))?;
        // Two sets of numbers are compared at the wider of their types,
        // {1, 2} ⊆ ℝ in ℝ.
        if let (Some(Members::Numbers(m)), Some(Members::Numbers(n))) =
            (self.set_members(a), self.set_members(b))
        {
            let at = m.max(n);
            return Some(match (self.numbers_at(a, at), self.numbers_at(b, at)) {
                (Route::Built(a), Route::Built(b)) => relation_of(op, a, b),
                (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
            });
        }
        Some(match (self.side_term(a, b), self.side_term(b, a)) {
            (Route::Built(a), Route::Built(b)) => relation_of(op, a, b),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        })
    }

    /// One side of a relation between sets: a listed set whose members give
    /// no type, {∅}, holds what the other side does, as Lean's `F ⊆ {∅}`
    /// reads it; any other set as the writer writes it.
    fn side_term(&self, side: &Node, other: &Node) -> Route<Printed> {
        let listed = matches!(
            &*side.notation_name(),
            "singleton" | "listed-two" | "listed-three" | "listed-four"
        );
        match (
            listed && self.members_of(side).is_none(),
            self.set_members(other),
        ) {
            (true, Some(m)) => self.listed(side, &m),
            _ => self.set_term(side),
        }
    }

    /// For all t ∈ S, or there is t ∈ S, of a set S: `∀ t ∈ S, …`, the letter
    /// a member of S's; None where S is no set this writer has a type for.
    pub fn quantified_over_set(
        &self,
        letter: &Node,
        set: &Node,
        body: &Node,
        exists: bool,
    ) -> Option<Route<Printed>> {
        // ∅, which holds no one type, holds what the body puts the letter
        // in: x of "for all x ∈ ∅, x ∈ A" is one of A's members.
        let empty = &*set.notation_name() == "empty-set";
        if empty && self.empty_of.is_none() {
            let held = body.walk().into_iter().find_map(|n| {
                match (n.notation(), n.children.as_slice()) {
                    (crate::notations::MEMBERSHIP, [x, s])
                        if x.is_name() && x.text == letter.text =>
                    {
                        self.members_of(s)
                    }
                    _ => None,
                }
            })?;
            let mut w = self.with_letters(self.letters.clone());
            w.empty_of = Some(held);
            return w.quantified_over_set(letter, set, body, exists);
        }
        let members = match self.members_of(set) {
            Some(m) => m,
            None if empty => self.empty_of.clone()?,
            None => return None,
        };
        // ∅ told what it holds, `(∅ : Set α)`, which nothing else in the
        // quantifier gives Lean.
        let domain = match self.set_term(set) {
            Route::Built(_) if empty => super::expr::empty_of_type(LeanType::Set(
                Box::new(members.letter().lean_type()),
            )),
            Route::Built(p) => p,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let mut inner = self.with_letters(self.letters.clone());
        inner
            .letters
            .insert(letter.text.to_string(), members.letter());
        // The letter bound here is a set of its own, whatever a set of its
        // name outside is: finite where its binder makes it so
        // (`citing::finite::bound_over`), and not otherwise.
        let name = self.grammar.print(letter);
        inner.finite.remove(&name);
        if let Some(why) =
            crate::citing::finite::bound_over(self.grammar, &self.finite, set)
        {
            inner.finite.insert(name, why);
        }
        let body = match inner.formula(body) {
            Route::Built(p) => p,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        // A quantifier whose guard is the membership, written `∀ t ∈ S, …`:
        // a binder the writer's comparisons and instances read as one.
        let name = super::names::letter(&letter.text);
        let letter_ty = members.letter().lean_type();
        let member = Printed::letter(name.clone(), letter_ty.clone());
        let guard = match super::expr::relation_of("∈", member, domain) {
            Route::Built(g) => g,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        Some(Route::Built(Printed::of(
            super::doc::TermKind::Quantified {
                quant: match exists {
                    true => super::doc::Quant::Exists,
                    false => super::doc::Quant::ForAll,
                },
                letter: name,
                letter_ty,
                guard: Some(Box::new(guard)),
                body: Box::new(body),
                bounded: true,
            },
            LeanType::Prop,
        )))
    }
}
