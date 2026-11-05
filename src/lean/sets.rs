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

/// The sets these lines make finite, as the page prints them: one a line
/// says is, `A is finite`, and one a line puts inside such a set, B of
/// `B ⊆ A` (`is_finite`). A line counts where it is the whole line or one
/// part of an "and"; under an "if" or a "not" it says nothing of the set.
pub fn finite_sets<'n>(
    grammar: &crate::formula::Grammar,
    lines: impl IntoIterator<Item = &'n Node>,
) -> std::collections::BTreeSet<String> {
    let mut said = SaidOfSets::default();
    for line in lines {
        said.read(line);
    }
    let mut out: std::collections::BTreeSet<String> =
        said.finite.iter().map(|s| grammar.print(s)).collect();
    // A part of a part of a finite set is finite too: until no more are.
    loop {
        let more: Vec<String> = said
            .subsets
            .iter()
            .filter(|s| is_finite(grammar, &out, s.whole))
            .map(|s| grammar.print(s.part))
            .filter(|p| !out.contains(p))
            .collect();
        if more.is_empty() {
            return out;
        }
        out.extend(more);
    }
}

/// What lines say of sets that makes one finite.
#[derive(Default)]
struct SaidOfSets<'n> {
    /// A of `A is finite`.
    finite: Vec<&'n Node>,
    /// `B ⊆ A`, each.
    subsets: Vec<Subset<'n>>,
}

/// A line `part ⊆ whole`.
struct Subset<'n> {
    part: &'n Node,
    whole: &'n Node,
}

impl<'n> SaidOfSets<'n> {
    fn read(&mut self, node: &'n Node) {
        use crate::notations::{COMMA_CONJUNCTION, CONJUNCTION};
        match (
            &*node.notation_name(),
            node.notation(),
            node.children.as_slice(),
        ) {
            ("finite", _, [set]) => self.finite.push(set),
            ("subset", _, [part, whole]) => self.subsets.push(Subset { part, whole }),
            // |X| = e, a count given as a number, says X is finite.
            (_, crate::notations::EQUALITY, [a, b]) => {
                for (count, value) in [(a, b), (b, a)] {
                    let counted = &*count.notation_name() == "cardinality";
                    let a_number = !value
                        .walk()
                        .iter()
                        .any(|n| &*n.notation_name() == "cardinality");
                    if let ([set], true, true) =
                        (count.children.as_slice(), counted, a_number)
                    {
                        self.finite.push(set);
                    }
                }
            }
            (_, CONJUNCTION | COMMA_CONJUNCTION, parts) => {
                for p in parts {
                    self.read(p);
                }
            }
            _ => {}
        }
    }
}

/// Whether a set is finite by what lines say (`finite_sets`) and how it
/// is made: ∅, a listed set {a, b} and a range {a, …, b}; A ∖ B where A
/// is, A ∩ B where either is, A ∪ B where both are; 𝒫A, {x ∈ A : …} and
/// {E(s) : s ∈ A} where A is.
pub fn is_finite(
    grammar: &crate::formula::Grammar,
    finite: &std::collections::BTreeSet<String>,
    set: &Node,
) -> bool {
    if finite.contains(&grammar.print(set)) {
        return true;
    }
    let of = |s: &Node| is_finite(grammar, finite, s);
    match (
        &*set.notation_name(),
        &*set.spelling().text(),
        set.children.as_slice(),
    ) {
        (
            "empty-set" | "singleton" | "listed-two" | "listed-three" | "listed-four"
            | "integer-range",
            _,
            _,
        ) => true,
        ("set-operations", "∖", [a, _]) => of(a),
        ("set-operations", "∩", [a, b]) => of(a) || of(b),
        ("set-operations", "∪", [a, b]) => of(a) && of(b),
        ("powerset", _, [a]) => of(a),
        ("set-builder", _, [_, a, _]) => of(a),
        ("set-image", _, [_, _, a]) => of(a),
        _ => false,
    }
}

/// Whether every member of a set is a finite set: 𝒫A where A is finite,
/// and what is made from such a set by {x ∈ _ : …}, ∖, ∩ and ∪, or named
/// for one (`members`).
pub fn holds_finite(
    grammar: &crate::formula::Grammar,
    finite: &std::collections::BTreeSet<String>,
    members: &std::collections::BTreeSet<String>,
    set: &Node,
) -> bool {
    if members.contains(&grammar.print(set)) {
        return true;
    }
    let of = |s: &Node| holds_finite(grammar, finite, members, s);
    match (
        &*set.notation_name(),
        &*set.spelling().text(),
        set.children.as_slice(),
    ) {
        ("powerset", _, [a]) => is_finite(grammar, finite, a),
        ("set-builder", _, [_, a, _]) => of(a),
        ("set-operations", "∖", [a, _]) => of(a),
        ("set-operations", "∩", [a, b]) => of(a) || of(b),
        ("set-operations", "∪", [a, b]) => of(a) && of(b),
        _ => false,
    }
}

/// A define of a proof: the name, and the term it names.
pub struct Named<'n> {
    pub name: String,
    pub value: &'n Node,
}

/// What a theorem's defines and bound letters add to the finite sets its
/// hypotheses give: a name for a finite set, F = {S ⊆ X : |S| = j} of a
/// finite X, is one; and a letter bound over sets that hold only finite
/// sets, the S of {S ∈ 𝒫X : |S| = j}, is one where every place the
/// theorem binds it is such a set, so that a property given for it, "|S|
/// = j", counts it as the set-builder does.
pub fn finite_names(
    grammar: &crate::formula::Grammar,
    finite: &mut std::collections::BTreeSet<String>,
    defines: &[Named],
    lines: &[&Node],
) {
    let mut members = std::collections::BTreeSet::new();
    for d in defines {
        if is_finite(grammar, finite, d.value) {
            finite.insert(d.name.clone());
        }
        if holds_finite(grammar, finite, &members, d.value) {
            members.insert(d.name.clone());
        }
    }
    let mut bound: std::collections::BTreeMap<String, bool> =
        std::collections::BTreeMap::new();
    for n in lines.iter().flat_map(|l| l.walk()) {
        let over = match (n.notation(), &*n.notation_name(), n.children.as_slice()) {
            (_, "set-builder", [x, set, _]) => Some((x, set)),
            (_, "set-image", [_, x, set]) => Some((x, set)),
            (
                crate::notations::FOR_ALL | crate::notations::THERE_IS,
                _,
                [x, set, _],
            ) => Some((x, set)),
            _ => None,
        };
        if let Some((x, set)) = over.filter(|(x, _)| x.is_name()) {
            let holds = holds_finite(grammar, finite, &members, set);
            let all = bound.entry(x.text.to_string()).or_insert(true);
            *all = *all && holds;
        }
    }
    finite.extend(bound.into_iter().filter(|(_, all)| *all).map(|(x, _)| x));
}

/// Whether a term counts, somewhere, a set not among `finite`: a count the
/// writer takes in ℕ∞.
pub fn counts_in_extended(
    grammar: &crate::formula::Grammar,
    finite: &std::collections::BTreeSet<String>,
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
                    (Route::Built(a), Route::Built(b)) => Route::Built(Printed::atom(
                        format!("({lean} {} {} : Set ℝ)", a.at(MAX), b.at(MAX)),
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
                    (Route::Built(a), Route::Built(b)) => Route::Built(Printed {
                        text: format!(
                            "⋃ {} ∈ {}, {}",
                            super::names::letter(&x.text),
                            a.at(MAX),
                            b.at(67)
                        ),
                        prec: 10,
                    }),
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
            (Route::Built(a), Route::Built(b)) => (a.at(MAX), b.at(MAX)),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Some(Route::Declined(d))
            }
        };
        let name = super::names::letter(&f.text);
        let parts: Vec<String> = parts
            .iter()
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

    /// Whether a term counts, somewhere, a set no line says is finite, |A|
    /// or |A| + 1: a count in ℕ∞.
    pub fn counts(&self, node: &Node) -> bool {
        counts_in_extended(self.grammar, &self.finite, node)
    }

    /// The sets these hypotheses make finite are the ones this writer
    /// counts as natural numbers.
    pub fn finite_from(&mut self, lines: Vec<Node>) {
        self.finite = finite_sets(self.grammar, &lines);
        self.finite_lines = lines;
    }

    /// The writer a hypothesis is written with: one counting as finite only
    /// what the other hypotheses make finite, since a line cannot vouch for
    /// itself. `|X| = 0` written with `X.ncard` would hold of every
    /// infinite X too, and say less than the page; `X.encard = 0` says X is
    /// finite. None where the line makes no set finite.
    pub fn without_line(&self, line: &Node) -> Option<Writer<'_>> {
        if finite_sets(self.grammar, std::iter::once(line)).is_empty() {
            return None;
        }
        let printed = self.grammar.print(line);
        let others: Vec<&Node> = self
            .finite_lines
            .iter()
            .filter(|l| self.grammar.print(l) != printed)
            .collect();
        let by_others = finite_sets(self.grammar, others);
        let by_all = finite_sets(self.grammar, &self.finite_lines);
        let mut out = self.with_letters(self.letters.clone());
        out.finite
            .retain(|s| by_others.contains(s) || !by_all.contains(s));
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
            let of = match &self.empty_of {
                Some(m) => Members::Sets(Box::new(m.clone())).lean(),
                None => format!("Set {}", super::expr::THINGS),
            };
            return Some(Route::Built(Printed::atom(format!("(∅ : {of}).ncard"))));
        }
        finite.then(|| {
            self.set_term(set)
                .map(|s| Printed::atom(format!("{}.ncard", s.at(MAX))))
        })
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
                Route::Built(p) => {
                    Route::Built(Printed::atom(format!("(({} : ℕ) : ℕ∞)", p.text)))
                }
                Route::Declined(d) => Route::Declined(d),
            };
        }
        if &*node.notation_name() == "cardinality" {
            let [set] = node.children.as_slice() else {
                return Route::no("a count of other than one set");
            };
            return match self.set_term(set) {
                Route::Built(s) => Route::Built(Printed {
                    text: format!("{}.encard", s.at(MAX)),
                    prec: MAX,
                }),
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
        if !self.counts(a) && !self.counts(b) {
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
        if !self.counts(x) {
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

    /// A listed set, {u, w}, of members of the type given, ascribed it, which
    /// Lean cannot take from a member alone: `({u, w} : Set α)`.
    fn listed(&self, node: &Node, members: &Members) -> Route<Printed> {
        let mut listed = Vec::new();
        for c in &node.children {
            match self.element_term(c, members) {
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

    /// What a listed set of ∅ alone holds, {∅}, which its members do not
    /// say: in a theorem whose sets hold things, of one type α, sets of
    /// those. None where a member is anything but ∅, or no letter holds
    /// things.
    fn sets_of_nothing(&self, members: &[Node]) -> Option<Members> {
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
        let set_text = match (empty, listed) {
            (true, _) => Route::Built(Printed::atom(format!(
                "(∅ : Set {})",
                super::expr::bracketed(&members.lean())
            ))),
            (false, true) => self.listed(set, &members),
            (false, false) => self.set_term(set),
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
        Some(match (self.side_term(a, b), self.side_term(b, a)) {
            (Route::Built(a), Route::Built(b)) => Route::Built(Printed {
                text: format!("{} {op} {}", a.at(51), b.at(51)),
                prec: 50,
            }),
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
