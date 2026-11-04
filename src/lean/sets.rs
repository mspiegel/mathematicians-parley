//! Sets in Lean: a set of the things a theorem's sets hold is `Set α`, and
//! the page's operations on sets are Mathlib's on `Set`.
//!
//! The members of every set a theorem leaves open are one type `α`, as
//! set.mm's sets all hold sets; 𝒫A's members are `Set α`. A function from
//! one such set to another is a function `α → α` with the fact that it
//! maps the one into the other beside it (`statement`).

use super::expr::{
    letter_type, set_type, system_of, LetterType, Members, Printed, System, Writer,
    APP, MAX,
};
use super::templates::Num;
use crate::formula::Node;
use crate::notations::NUMBER_SYSTEMS;
use crate::outcome::Route;

/// The inverse of a map on its domain, in the bridges: Mathlib's asks a
/// nonempty type, which a statement over sets does not carry.
pub const INVERSE: &str = "LeanBridges.Functions.inverse";

/// The polynomial functions with complex coefficients, set.mm's `Poly ℂ`,
/// in the bridges: a page's polynomial is a function from ℂ to ℂ it holds.
const POLYNOMIALS: &str = "LeanBridges.Polynomials.polynomials";

/// The Lean type of a letter of this sort where it is a set, a member of
/// one or a map between sets; None for any other sort.
pub fn set_letter_type(sort: &crate::formula::Sort) -> Option<LetterType> {
    use crate::formula::Whole;
    match sort.full()? {
        Whole::Set(_) => Members::of_set(sort.full()?).map(LetterType::Set),
        Whole::Open => Some(LetterType::Member(Members::Things)),
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
                .members_of(node.children.first()?)
                .map(|m| Members::Sets(Box::new(m))),
            "singleton" | "listed-two" | "listed-three" | "listed-four" => node
                .children
                .iter()
                .find_map(|c| self.member_kind(c))
                .or_else(|| self.numbers_held(&node.children)),
            // {E(s) : s ∈ Y} holds what E(s) is.
            "set-image" => {
                let inner = self.set_image_inner(node)?;
                let term = node.children.first()?;
                inner
                    .member_kind(term)
                    .or_else(|| inner.numbers_held(std::slice::from_ref(term)))
            }
            // [a, b] holds real numbers.
            "closed-interval" => Some(Members::Numbers(Num::Real)),
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
            let wide = self.type_name(at);
            let says = match system {
                System::Type(n) => {
                    format!("∃ m : {}, (m : {wide}) = x", self.type_name(n))
                }
                System::Positive => format!("∃ m : ℕ, 0 < m ∧ (m : {wide}) = x"),
                System::NonNegative => format!("∃ m : ℕ, (m : {wide}) = x"),
            };
            return Route::Built(Printed::atom(format!("{{x : {wide} | {says}}}")));
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
                Route::Built(p) => members.push(p.text),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        Route::Built(Printed::atom(format!(
            "({{{}}} : Set {})",
            members.join(", "),
            at.lean()
        )))
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
            return match self.letters.get(node.text.as_str()) {
                Some(
                    LetterType::Set(_)
                    | LetterType::Member(_)
                    | LetterType::Map { .. }
                    | LetterType::Function { .. },
                ) => Route::Built(Printed::atom(super::names::letter(&node.text))),
                // A group standing as a set is all of its elements; its
                // identity is Lean's 1 of it; a subgroup as a set is its
                // elements.
                Some(LetterType::Group) => Route::Built(Printed::atom(format!(
                    "(Set.univ : Set {})",
                    super::names::letter(&node.text)
                ))),
                Some(LetterType::Identity(g)) => Route::Built(Printed::atom(format!(
                    "(1 : {})",
                    super::names::letter(g)
                ))),
                Some(LetterType::Subgroup(g)) => Route::Built(Printed::atom(format!(
                    "({} : Set {})",
                    super::names::letter(&node.text),
                    super::names::letter(g)
                ))),
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
                return Route::Built(Printed {
                    text: format!("{} * {}", p[0].at(70), p[1].at(71)),
                    prec: 70,
                });
            }
            "group-inverse" => {
                let p = match self.set_parts(node, 1) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                return Route::Built(Printed {
                    text: format!("{}⁻¹", p[0].at(MAX)),
                    prec: MAX,
                });
            }
            // gH is the image of H under h ↦ g·h, as Mathlib's left coset
            // g • H is defined, written so that no scope need be opened.
            "coset" => {
                let p = match self.set_parts(node, 2) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                return Route::Built(Printed {
                    text: format!("({} * ·) '' {}", p[0].at(70), p[1].at(MAX)),
                    prec: 80,
                });
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
                    Route::Built(c) => c.at(MAX),
                    Route::Declined(d) => return Route::Declined(d),
                };
                return Route::Built(Printed {
                    text: format!(
                        "@ite _ {c} (Classical.propDecidable {c}) {} {}",
                        a.at(MAX),
                        b.at(MAX)
                    ),
                    prec: APP,
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
            return Route::Built(Printed::atom(match system {
                super::expr::System::Positive => "{n : ℤ | 0 < n}".to_string(),
                super::expr::System::NonNegative => "{n : ℤ | 0 ≤ n}".to_string(),
                _ => format!("(Set.univ : Set {})", letter_type(system).lean()),
            }));
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
                let (op, prec) = match &*node.spelling().text() {
                    "∪" => ("∪", 65),
                    "∩" => ("∩", 70),
                    "∖" => ("\\", 70),
                    other => return Route::no(format!("the set operation {other}")),
                };
                Route::Built(Printed {
                    text: format!("{} {op} {}", p[0].at(prec + 1), p[1].at(prec + 1)),
                    prec,
                })
            }
            // [a, b], the reals from a to b.
            "closed-interval" => {
                let [from, to] = node.children.as_slice() else {
                    return Route::no("an interval of other than two ends");
                };
                match (
                    self.number_fixed(from, Num::Real),
                    self.number_fixed(to, Num::Real),
                ) {
                    (Route::Built(a), Route::Built(b)) => Route::Built(Printed::atom(
                        format!("(Set.Icc {} {} : Set ℝ)", a.at(MAX), b.at(MAX)),
                    )),
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
                    (Route::Built(a), Route::Built(b)) => Route::Built(Printed::atom(
                        format!("(Set.Icc {} {} : Set ℤ)", a.at(MAX), b.at(MAX)),
                    )),
                    (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                        Route::Declined(d)
                    }
                }
            }
            "powerset" => match parts(1) {
                Route::Built(p) => Route::Built(Printed {
                    text: format!("𝒫 {}", p[0].at(MAX)),
                    prec: 100,
                }),
                Route::Declined(d) => Route::Declined(d),
            },
            "empty-set" => Route::Built(Printed::atom("∅")),
            "singleton" | "listed-two" | "listed-three" | "listed-four" => {
                // Ascribed its type, which Lean cannot take from a member
                // alone: `{u, w}` of things of α is `({u, w} : Set α)`.
                let Some(members) = self.members_of(node) else {
                    return Route::no("a listed set of members with no Lean type");
                };
                let mut listed = Vec::new();
                for c in &node.children {
                    match self.element_term(c, &members) {
                        Route::Built(p) => listed.push(p.text),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                Route::Built(Printed::atom(format!(
                    "({{{}}} : Set {})",
                    listed.join(", "),
                    super::expr::bracketed(&members.lean())
                )))
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
        Route::Built(Printed {
            text: format!(
                "{} '' ({domain} ∩ {})",
                super::names::letter(&f.text),
                set.at(71)
            ),
            prec: 80,
        })
    }

    /// The set a map or function is defined on, as Lean writes it: the one
    /// a line gives it, or for a function given between number systems,
    /// all of its type; None for one from ℕ, whose type Lean's ℕ begins at
    /// 0 where the page's begins at 1, and for any other letter.
    pub fn domain_of(&self, f: &str) -> Option<String> {
        if let Some(d) = self.domains.get(f) {
            return Some(d.clone());
        }
        match self.letters.get(f) {
            Some(LetterType::Function { from, .. }) if *from != Num::Nat => {
                Some(format!("(Set.univ : Set {})", from.lean()))
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
            Route::Built(z) => Route::Built(Printed {
                text: format!(
                    "{domain} ∩ {} ⁻¹' {}",
                    super::names::letter(&f.text),
                    z.at(MAX)
                ),
                prec: 70,
            }),
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
            let ty = set_type(system).lean();
            let condition = match system {
                super::expr::System::Positive => {
                    format!("0 < {name} ∧ {}", condition.at(36))
                }
                super::expr::System::NonNegative => {
                    format!("0 ≤ {name} ∧ {}", condition.at(36))
                }
                _ => condition.text,
            };
            return Route::Built(Printed::atom(format!(
                "{{{name} : {ty} | {condition}}}"
            )));
        }
        let domain = match self.set_term(set) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        Route::Built(Printed::atom(format!(
            "{{{name} ∈ {} | {}}}",
            domain.text, condition.text
        )))
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
            (Route::Built(t), Route::Built(y)) => Route::Built(Printed {
                text: format!(
                    "(fun {} : {} => {}) '' {}",
                    super::names::letter(&letter.text),
                    over.lean(),
                    t.text,
                    y.at(MAX)
                ),
                prec: 80,
            }),
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
            return match self.set_term(x) {
                Route::Built(p) => Route::Built(Printed {
                    text: format!(
                        "{INVERSE} {} {domain} {}",
                        super::names::letter(&g.text),
                        p.at(MAX)
                    ),
                    prec: 1023,
                }),
                Route::Declined(d) => Route::Declined(d),
            };
        }
        let Some(map) = self.map_text(f) else {
            return Route::no(format!("{} applied, which is no map", f.text));
        };
        match self.set_term(x) {
            Route::Built(p) => Route::Built(Printed {
                text: format!("{map} {}", p.at(MAX)),
                prec: 1023,
            }),
            Route::Declined(d) => Route::Declined(d),
        }
    }

    /// A map as Lean writes it applied: a map letter, or g ∘ f of maps,
    /// `(g ∘ f)`; None for anything else.
    fn map_text(&self, f: &Node) -> Option<String> {
        if f.is_name() {
            return matches!(
                self.letters.get(f.text.as_str()),
                Some(LetterType::Map { .. })
            )
            .then(|| super::names::letter(&f.text));
        }
        match (&*f.notation_name(), f.children.as_slice()) {
            ("composition", [g, inner]) => Some(format!(
                "({} ∘ {})",
                self.map_text(g)?,
                self.map_text(inner)?
            )),
            _ => None,
        }
    }

    /// What a map between sets is: `f : A → B` is `Set.MapsTo f A B`, and
    /// one-to-one and onto add `Set.InjOn f A` and `Set.SurjOn f A B`, each
    /// a part of a conjunction a hypothesis is taken apart by. None where
    /// the node says none of these of a map letter.
    pub fn map_claim(&self, node: &Node) -> Option<Route<Printed>> {
        let extra: &[&str] = match &*node.notation_name() {
            "function-type" => &[],
            "one-to-one" => &["Set.InjOn _f _A"],
            "onto" => &["Set.SurjOn _f _A _B"],
            "one-to-one-onto" => &["Set.InjOn _f _A", "Set.SurjOn _f _A _B"],
            _ => return None,
        };
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
        if function && extra.is_empty() {
            return None;
        }
        let (a, b) = match (self.set_term(from), self.set_term(to)) {
            (Route::Built(a), Route::Built(b)) => (a.at(MAX), b.at(MAX)),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Some(Route::Declined(d))
            }
        };
        let name = super::names::letter(&f.text);
        let parts: Vec<String> = std::iter::once("Set.MapsTo _f _A _B")
            .chain(extra.iter().copied())
            .map(|p| p.replace("_f", &name).replace("_A", &a).replace("_B", &b))
            .collect();
        let prec = if parts.len() == 1 {
            super::expr::APP
        } else {
            35
        };
        Some(Route::Built(Printed {
            text: parts.join(" ∧ "),
            prec,
        }))
    }

    /// Whether a term counts a set somewhere, |A| or |A| + 1.
    pub fn counts(node: &Node) -> bool {
        node.walk()
            .iter()
            .any(|n| &*n.notation_name() == "cardinality")
    }

    /// A count as Lean's `Set.encard` gives it, in ℕ∞, where an infinite
    /// set counts as ∞ as set.mm's ♯ counts it +∞: |A| is `A.encard`, a
    /// numeral or a letter of ℕ or ℕ₀ is cast up, and + and · are ℕ∞'s.
    /// Subtraction declines: ℕ∞'s stops at 0, where the page's does not.
    pub fn count_term(&self, node: &Node) -> Route<Printed> {
        if &*node.notation_name() == "cardinality" {
            let [set] = node.children.as_slice() else {
                return Route::no("a count of other than one set");
            };
            // ∅ counted is told it is a set of things, which nothing else
            // in |∅| = 0 gives Lean.
            if &*set.notation_name() == "empty-set" {
                return Route::Built(Printed {
                    text: format!("(∅ : Set {}).encard", super::expr::THINGS),
                    prec: MAX,
                });
            }
            return match self.set_term(set) {
                Route::Built(s) => Route::Built(Printed {
                    text: format!("{}.encard", s.at(MAX)),
                    prec: MAX,
                }),
                Route::Declined(d) => Route::Declined(d),
            };
        }
        // A number of ℕ, the type ℕ∞ holds: a numeral, or a letter of ℕ
        // or ℕ₀, cast up.
        if !Writer::counts(node) {
            return match self.number_fixed(node, Num::Nat) {
                Route::Built(p) => {
                    Route::Built(Printed::atom(format!("(({} : ℕ) : ℕ∞)", p.text)))
                }
                Route::Declined(d) => Route::Declined(d),
            };
        }
        let op = match (&*node.notation_name(), &*node.spelling().text()) {
            ("additive", "+") => "+",
            ("multiplicative", "·") => "*",
            (_, other) => {
                return Route::no(format!(
                    "{other} of a count, which ℕ∞ does not compute as the page does"
                ))
            }
        };
        let [a, b] = node.children.as_slice() else {
            return Route::no("an operation on a count of other than two parts");
        };
        let prec = if op == "+" { 65 } else { 70 };
        match (self.count_term(a), self.count_term(b)) {
            (Route::Built(a), Route::Built(b)) => Route::Built(Printed {
                text: format!("{} {op} {}", a.at(prec), b.at(prec + 1)),
                prec,
            }),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        }
    }

    /// An equation or order between counts, |A| = 2 or 1 ≤ |A|, both sides
    /// in ℕ∞; None where neither side counts a set.
    pub fn count_relation(&self, node: &Node) -> Option<Route<Printed>> {
        let [a, b] = node.children.as_slice() else {
            return None;
        };
        if !Writer::counts(a) && !Writer::counts(b) {
            return None;
        }
        let op = node.spelling().text().to_string();
        Some(match (self.count_term(a), self.count_term(b)) {
            (Route::Built(a), Route::Built(b)) => Route::Built(Printed {
                text: format!("{} {op} {}", a.at(51), b.at(51)),
                prec: 50,
            }),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        })
    }

    /// A count in ℕ or ℕ₀, |A| ∈ ℕ: some natural number is the count, and
    /// for the page's ℕ, which starts at 1, one above 0. None where the term
    /// counts no set.
    pub fn count_in_system(&self, x: &Node, set: &Node) -> Option<Route<Printed>> {
        if !Writer::counts(x) {
            return None;
        }
        let count = match self.count_term(x) {
            Route::Built(p) => p,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let above = match system_of(set) {
            Some(super::expr::System::Positive) => "0 < m ∧ ",
            Some(super::expr::System::NonNegative) => "",
            _ => return Some(Route::no("a count in other than ℕ or ℕ₀")),
        };
        Some(Route::Built(Printed {
            text: format!("∃ m : ℕ, {above}(m : ℕ∞) = {}", count.text),
            prec: 0,
        }))
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
            true => Route::Built(Printed::atom("True")),
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
            Route::Built(f) => Route::Built(Printed {
                text: format!("{} ∈ {POLYNOMIALS}", f.at(51)),
                prec: 50,
            }),
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
        let text = match exists {
            true => format!("∃ {q} : ℂ → ℂ, {q} ∈ {POLYNOMIALS} ∧ {}", body.at(35)),
            false => format!("∀ {q} : ℂ → ℂ, {q} ∈ {POLYNOMIALS} → {}", body.at(25)),
        };
        Some(Route::Built(Printed { text, prec: 0 }))
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
            Route::Built(s) => Route::Built(Printed {
                text: format!("{}.Finite", s.at(MAX)),
                prec: MAX,
            }),
            Route::Declined(d) => Route::Declined(d),
        })
    }

    /// x ∈ S of a set S this writer has a type for: `x ∈ S`.
    pub fn set_membership(&self, x: &Node, set: &Node) -> Option<Route<Printed>> {
        // ∅ holds nothing of any type, so x ∈ ∅ is of x's.
        let empty = &*set.notation_name() == "empty-set";
        let members = self.members_of(set).or_else(|| {
            empty
                .then(|| {
                    self.member_kind(x)
                        .or_else(|| self.numbers_held(std::slice::from_ref(x)))
                })
                .flatten()
        })?;
        // ∅ is told its type, which nothing else in `t ∈ ∅` gives Lean.
        let set_text = match empty {
            true => Route::Built(Printed::atom(format!(
                "(∅ : Set {})",
                super::expr::bracketed(&members.lean())
            ))),
            false => self.set_term(set),
        };
        Some(match (self.element_term(x, &members), set_text) {
            (Route::Built(a), Route::Built(b)) => Route::Built(Printed {
                text: format!("{} ∈ {}", a.at(51), b.at(51)),
                prec: 50,
            }),
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
                (Route::Built(a), Route::Built(b)) => Route::Built(Printed {
                    text: format!("{} {op} {}", a.at(51), b.at(51)),
                    prec: 50,
                }),
                (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
            });
        }
        Some(match (self.set_term(a), self.set_term(b)) {
            (Route::Built(a), Route::Built(b)) => Route::Built(Printed {
                text: format!("{} {op} {}", a.at(51), b.at(51)),
                prec: 50,
            }),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        })
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
        let members = self.members_of(set)?;
        let domain = match self.set_term(set) {
            Route::Built(p) => p,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let mut inner = self.with_letters(self.letters.clone());
        inner
            .letters
            .insert(letter.text.to_string(), members.letter());
        let body = match inner.formula(body) {
            Route::Built(p) => p,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let quantifier = if exists { "∃" } else { "∀" };
        Some(Route::Built(Printed {
            text: format!(
                "{quantifier} {} ∈ {}, {}",
                super::names::letter(&letter.text),
                domain.at(51),
                body.text
            ),
            prec: 0,
        }))
    }
}
