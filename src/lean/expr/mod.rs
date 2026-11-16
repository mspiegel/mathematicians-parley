//! A tree the checker read, written as a Lean term.
//!
//! Each letter keeps its own type. Each number is computed in the least of
//! ℤ, ℚ, ℝ and ℂ that holds every letter and operation of the formula it is
//! part of, never in ℕ, whose subtraction stops at 0; the two sides of a
//! relation are computed in one type, and a narrower letter is cast up. A
//! hole a notation always reads at one type, the integers `divides` takes,
//! is computed there, and a term that does not fit it is declined rather
//! than cast down (`LEAN.md`, "Number types").

use indexmap::IndexMap;

use super::doc::LeanType;
use super::templates::{Num, Slot, Template, Templates};
use crate::citing::bounds::{self, SaidBounds};
use crate::formula::{Grammar, Node};
use crate::notations::{
    EQUALITY, EQUALS, FOR_ALL, INTEGER_RANGE, LOGICAL_NOT, MEMBERSHIP, NAME, NATURALS,
    NATURALS0, NUMBER_SYSTEMS, NUMERAL, ORDER, THERE_IS,
};
use crate::outcome::Route;

mod arguments;
mod formulas;
mod operators;

pub use formulas::{pair_coordinates, pair_type};

/// What a letter is in Lean.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LetterType {
    /// A number of this type.
    Number(Num),
    /// A function from numbers of one type to numbers of another.
    Function { from: Num, to: Num },
    /// A statement, the P of "if P then Q" in a rule of reasoning.
    Statement,
    /// A set whose members are these, `A : Set α`.
    Set(Members),
    /// A member of a set whose members are these, `t : α`.
    Member(Members),
    /// A function from members of one kind to members of another, `f : α
    /// → α`; where it maps one set into another is a fact beside it.
    Map { from: Members, to: Members },
    /// A group, `{G : Type*} [Group G]`: its elements are a type, and as a
    /// set it is all of them.
    Group,
    /// The identity of the group named, `(1 : G)`.
    Identity(String),
    /// A subgroup of the group named, `H : Subgroup G`.
    Subgroup(String),
    /// A property of members of these, `P : α → Prop`; P(t) is `P t`.
    Property(Members),
}

/// What the members of a set are in Lean: things of a type variable, as
/// set.mm's sets all hold sets; sets of those, 𝒫A's members; or numbers of
/// one type, {2n : n ∈ ℤ}'s.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Members {
    /// Things of the type variable numbered: a theorem's sets all hold
    /// things of one, `α`; an item's map takes things of one to things of
    /// another where nothing it says makes them one (`items::thing_types`),
    /// so that a citation may give it numbers of two types.
    Things(usize),
    Sets(Box<Members>),
    Numbers(Num),
    /// The elements of the group of this page name, of Lean type G.
    Elements(String),
    /// Functions on the set `on` itself, `↥X → β`, the members of the
    /// functions from X to Y: a page's function has values on X alone, and
    /// a Lean function on X's whole type has others besides. `from` is
    /// what X holds, `to` what Y does.
    Maps {
        on: Box<super::doc::Term>,
        from: Box<Members>,
        to: Box<Members>,
    },
}

/// The type variable a theorem's sets of things are sets of.
pub const THINGS: &str = "α";

/// That a thing is one of ZF's sets, what "X exists" says
/// (`corpus/lean-bridges/ZF.lean`).
pub const IS_SET: &str = "LeanBridges.ZF.IsSet";

/// The class a type of things takes where a statement says a collection of
/// them exists: which of them are ZF's sets.
pub const ZF_SETS: &str = "LeanBridges.ZF.Sets";

/// The name of the type variable numbered: α, then β, γ, δ.
pub fn things_name(var: usize) -> String {
    match ["α", "β", "γ", "δ"].get(var) {
        Some(name) => name.to_string(),
        None => format!("α{var}"),
    }
}

impl Members {
    /// The members a set of this sort has; None for a sort no Lean type is
    /// written for yet, numbers among them.
    pub fn of_set(sort: &crate::formula::node::Whole) -> Option<Members> {
        match sort {
            crate::formula::node::Whole::Set(inner) => Members::of(inner),
            _ => None,
        }
    }

    /// Members of this sort, things of the first type variable.
    pub fn of(sort: &crate::formula::node::Whole) -> Option<Members> {
        match sort {
            crate::formula::node::Whole::Open => Some(Members::Things(0)),
            crate::formula::node::Whole::Set(inner) => {
                Members::of(inner).map(|m| Members::Sets(Box::new(m)))
            }
            _ => None,
        }
    }

    /// A member's type in the document model.
    pub fn member_type(&self) -> super::doc::LeanType {
        use super::doc::LeanType;
        match self {
            Members::Things(var) => LeanType::Things(*var),
            Members::Sets(m) => LeanType::Set(Box::new(m.member_type())),
            Members::Numbers(n) => LeanType::Num(*n),
            Members::Elements(g) => LeanType::Elements(g.clone()),
            Members::Maps { on, to, .. } => LeanType::Fun {
                from: Box::new(LeanType::Within(on.clone())),
                to: Box::new(to.member_type()),
            },
        }
    }

    /// How Lean writes a member's type.
    pub fn lean(&self) -> String {
        self.member_type().text()
    }

    /// The type a letter that runs over such members has: a number of the
    /// type, or a member.
    pub fn letter(&self) -> LetterType {
        match self {
            Members::Numbers(n) => LetterType::Number(*n),
            other => LetterType::Member(other.clone()),
        }
    }

    /// The type variable of the things they are, or are sets of, so that
    /// a statement takes `{α : Type*}`; None for numbers or a group's.
    fn things_var(&self) -> Option<usize> {
        match self {
            Members::Things(var) => Some(*var),
            Members::Sets(m) => m.things_var(),
            Members::Maps { from, to, .. } => {
                from.things_var().or_else(|| to.things_var())
            }
            Members::Numbers(_) | Members::Elements(_) => None,
        }
    }

    /// The same members, things of the type variable given.
    pub fn with_things(&self, var: usize) -> Members {
        match self {
            Members::Things(_) => Members::Things(var),
            Members::Sets(m) => Members::Sets(Box::new(m.with_things(var))),
            other => other.clone(),
        }
    }
}

/// A type written with a space in it, bracketed to stand as an argument.
pub fn bracketed(ty: &str) -> String {
    if ty.contains(' ') {
        format!("({ty})")
    } else {
        ty.to_string()
    }
}

impl LetterType {
    /// How Lean writes the type.
    pub fn lean(&self) -> String {
        self.lean_type().text()
    }

    /// The type in the document model.
    pub fn lean_type(&self) -> super::doc::LeanType {
        use super::doc::LeanType;
        let fun = |from: LeanType, to: LeanType| LeanType::Fun {
            from: Box::new(from),
            to: Box::new(to),
        };
        match self {
            LetterType::Statement => LeanType::Prop,
            LetterType::Number(n) => LeanType::Num(*n),
            LetterType::Function { from, to } => {
                fun(LeanType::Num(*from), LeanType::Num(*to))
            }
            LetterType::Set(m) => LeanType::Set(Box::new(m.member_type())),
            LetterType::Member(m) => m.member_type(),
            LetterType::Map { from, to } => fun(from.member_type(), to.member_type()),
            LetterType::Group => LeanType::Universe,
            LetterType::Identity(g) => LeanType::Elements(g.clone()),
            LetterType::Subgroup(g) => LeanType::Subgroup(g.clone()),
            LetterType::Property(m) => fun(m.member_type(), LeanType::Prop),
        }
    }

    /// The type variables of the things the type holds, so that its
    /// statement takes `{α β : Type*}`.
    pub fn things_vars(&self) -> Vec<usize> {
        match self {
            LetterType::Set(m) | LetterType::Member(m) | LetterType::Property(m) => {
                m.things_var().into_iter().collect()
            }
            LetterType::Map { from, to } => from
                .things_var()
                .into_iter()
                .chain(to.things_var())
                .collect(),
            _ => Vec::new(),
        }
    }
}

/// The type of each letter in scope, by its name.
pub type Letters = IndexMap<String, LetterType>;

/// A Lean term as the writer builds it (`doc::Term`).
pub type Printed = super::doc::Term;

/// The precedence of a term no operator can split: a letter, a numeral, a
/// bracketed term.
pub const MAX: u32 = 1024;
/// The precedence of a function applied to its arguments.
pub const APP: u32 = 1023;

/// Writes trees as Lean, with the letters in scope.
pub struct Writer<'a> {
    pub grammar: &'a Grammar,
    pub templates: &'a Templates,
    /// The notations the reading takes as "and", `A and B` and `A, and B`
    /// (`matching::Context::conjunctions`), which every question of whether
    /// a tree is an "and" asks (`is_and`).
    pub ands: &'a crate::matching::FxIndexSet<crate::formula::notation_id::NotationId>,
    pub letters: Letters,
    /// The letters the page puts in ℕ or ℕ₀, each a Lean integer with its
    /// fact 0 < n or 0 ≤ n beside it, as set.mm's n ∈ ℕ is a fact about a
    /// number (`Writer::introduce`): what the said-once rule reads of them.
    pub wholes: IndexMap<String, System>,
    /// For an item's statement, the number type that stands for any ring
    /// of a kind, written `K` (`items`); None elsewhere.
    pub general: Option<Num>,
    /// Terms of a wider type that a hypothesis already stated says are
    /// integers, f(a) of `f(a) ∈ ℤ` with f into ℝ: each is the integer that
    /// hypothesis gives, where the page computes with it in ℤ.
    pub integers: Vec<SaidInteger>,
    /// The set each map letter is a map from, by the letter: the A of `f :
    /// A → B`, within which a preimage is taken and an inverse is found.
    pub domains: IndexMap<String, Printed>,
    /// Terms the theorem puts in a hole of type ℝ, A/B of ⌊A/B⌋, as the
    /// page prints them: each is computed in ℝ wherever it is written.
    pub reals: Vec<String>,
    /// The sets the checker records finite, as the page prints them
    /// (`CheckedTheorem::said_finite`): a count of one, or of a set made
    /// from them as `citing::finite::is_finite` says, is a natural number,
    /// `A.ncard`, and of any other set in ℕ∞ (`sets::count_term`). Each
    /// with why it is finite (`citing::finite::FiniteBy`).
    pub finite: crate::citing::finite::FiniteSets,
    /// For each hypothesis that makes a set finite and may not vouch for
    /// itself, as printed, the sets only it does (`Writer::without_line`).
    pub finite_only_by: IndexMap<
        crate::formula::node::ByShape,
        indexmap::IndexSet<crate::formula::node::ByShape>,
    >,
    /// Of each "if P then Q", the sets P makes finite within Q, by the
    /// sentence as a tree, as the checker records them
    /// (`CheckedTheorem::finite_under`): Q is written with them finite.
    pub finite_under: std::rc::Rc<
        IndexMap<crate::formula::node::ByShape, crate::citing::finite::FiniteSets>,
    >,
    /// What ∅ holds where nothing in it says, as a count compared with the
    /// count of a set of those, |S| = |∅| (`relation_from`); None where it
    /// is a set of the theorem's things.
    pub empty_of: Option<Members>,
    /// What the lines in scope say terms are at least: a real power or
    /// square root of a term at least 0 is Mathlib's real one
    /// (`Writer::principal_is_real`).
    pub bounds: SaidBounds,
    /// What the theorem's hypotheses say terms are at least
    /// (`CheckedTheorem::statement_bounds`), which hold in every step: what
    /// says an exponent is a whole number (`said_whole`), so that a term is
    /// spelt one way throughout the theorem. A fact a later line proves is
    /// bridged at the step that uses it, and changes no spelling.
    pub whole_bounds: SaidBounds,
    /// Each real power or square root written so far in a theorem, by the
    /// page's print of it, with the forms it was written in: Mathlib's real
    /// one, the principal one in ℂ, or both, which the theorem's writer
    /// reports (`Writer::roots_written_both_ways`). Shared by every writer
    /// made from this one.
    pub root_forms: std::rc::Rc<std::cell::RefCell<IndexMap<String, (bool, bool)>>>,
}

/// The writer's view for the shared rule of what terms are at least
/// (`citing::bounds`): the lines in its scope, its letters' types, and how
/// it reads a sum.
impl bounds::BoundsAsk for Writer<'_> {
    fn bounds(&self) -> &SaidBounds {
        &self.bounds
    }

    fn same(&self, a: &Node, b: &Node) -> bool {
        self.grammar.print(a) == self.grammar.print(b)
    }

    fn natural_letter(&self, letter: &str) -> bool {
        match self.letters.get(letter) {
            Some(LetterType::Number(Num::Nat)) => true,
            Some(LetterType::Number(Num::Int)) => self.wholes.contains_key(letter),
            _ => false,
        }
    }

    fn summed_nonnegative(&self, node: &Node) -> bool {
        match self.summed(node) {
            Route::Built(s) => bounds::nonnegative(&s.inner, s.term),
            Route::Declined(_) => false,
        }
    }

    fn exponential(&self, node: &Node) -> bool {
        self.library_function(node).is_some()
            && node.children.first().is_some_and(|f| &*f.text == "exp")
    }
}

/// A sum read for writing: the writer its term is read with, where its index
/// is an integer, and its parts.
struct Summed<'a, 'n> {
    inner: Writer<'a>,
    index: &'n Node,
    over: Over<'n>,
    term: &'n Node,
}

/// What a function applied takes and gives.
struct Applied {
    /// What its argument is a member of.
    takes: Members,
    /// The number type of its value.
    gives: Num,
}

/// What a sum or product runs over.
enum Over<'n> {
    /// The integers from one end to the other.
    Range { from: &'n Node, to: &'n Node },
    /// The members of a set, Σ(x ∈ S) t.
    Set(&'n Node),
}

/// How Lean writes a term where a natural number is wanted, a power's
/// exponent or a library function's argument (`Writer::natural_form`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NaturalForm {
    /// A natural number Lean computes in ℕ, written as it stands: a count,
    /// a numeral.
    AsItIs,
    /// An integer the page says is at least 0, written as its `toNat`.
    ToNat,
    /// An integer the page does not say is at least 0: a power to it is
    /// Lean's integer power, in a field.
    Integer,
}

/// A term a line says is an integer or a rational: the term as the page
/// prints it, the line's Lean name, `∃ m : ℤ, (m : ℝ) = f a`, and the type
/// it says the term is in.
#[derive(Clone, Debug)]
pub struct SaidInteger {
    pub term: String,
    pub proof: Printed,
    pub ty: Num,
    /// The whole number written out, where a step names it so, 2 ^ ((p :
    /// ℤ) − 1).toNat of 2^(p − 1) from the line p − 1 ∈ ℕ₀, `proof` then
    /// naming its equation with the term; None where the number is the
    /// line's witness, `Classical.choose proof`.
    pub value: Option<Printed>,
    /// Whether the number stands for the term only where a whole number is
    /// asked, as a step names one (`theorem::name_wholes`): elsewhere the
    /// term keeps its own form. A line saying the term is an integer gives
    /// one that stands for it everywhere after.
    pub slot_only: bool,
    /// Of a number named as an integer's `toNat` by a line saying the
    /// integer is at least 0, the proof that it cast back is the integer,
    /// `Int.toNat_of_nonneg h : ((t.toNat : ℕ) : ℤ) = t`; None otherwise.
    pub back: Option<Printed>,
}

/// Whether the node is a sum or a product over a range, Σ(k = a to b) t or
/// ∏(k = a to b) t, which the writer reads alike; or one over a set that is
/// a range, ∏(k ∈ {1, …, n}) t, which is the same product.
fn is_big_operator(node: &Node) -> bool {
    matches!(
        node.notation(),
        crate::notations::SUM | crate::notations::PRODUCT
    ) || matches!(&*node.notation_name(), "sum-over" | "product-over")
}

/// A sum or product over a set that is a range, Σ(k ∈ {a, …, b}) t: its
/// index, the range's ends, and its term.
fn over_range(node: &Node) -> Option<[&Node; 4]> {
    if !matches!(&*node.notation_name(), "sum-over" | "product-over") {
        return None;
    }
    let [index, set, term] = node.children.as_slice() else {
        return None;
    };
    let [from, to] = set.children.as_slice() else {
        return None;
    };
    (set.notation() == INTEGER_RANGE).then_some([index, from, to, term])
}

/// The big operators over a set that is a range a formula has, which Lean
/// writes over `Finset.Icc` (`over_range`), where an item over a set of
/// numbers writes `∏ᶠ x ∈ X` of the set.
pub struct RangedOperators {
    pub sum: bool,
    pub product: bool,
}

impl RangedOperators {
    pub fn of(formula: &Node) -> RangedOperators {
        let mut out = RangedOperators {
            sum: false,
            product: false,
        };
        for node in formula.walk() {
            if over_range(&node).is_some() {
                match &*node.notation_name() {
                    "product-over" => out.product = true,
                    _ => out.sum = true,
                }
            }
        }
        out
    }
}

/// The node with each part of the shape of `from` put as `to`.
pub(super) fn put_for(node: &Node, from: &Node, to: &Node) -> Node {
    if node.spelt_alike(from) {
        return to.clone();
    }
    node.with_children(node.children.iter().map(|c| put_for(c, from, to)).collect())
}

/// Whether a big operator is a product, ∏(k = a to b) or ∏(k ∈ {a, …, b}).
fn is_product(node: &Node) -> bool {
    node.notation() == crate::notations::PRODUCT
        || &*node.notation_name() == "product-over"
}

/// The type variable an item's general letters range over.
pub const GENERAL: &str = "K";

impl<'a> Writer<'a> {
    /// A number type as this writer writes it: `K` for the general one.
    pub fn type_name(&self, n: Num) -> String {
        if self.general == Some(n) {
            GENERAL.to_string()
        } else {
            n.lean().to_string()
        }
    }

    /// A number type in the document model as this writer writes it: the
    /// general one for an item's general type.
    pub fn num_type(&self, n: Num) -> super::doc::LeanType {
        if self.general == Some(n) {
            super::doc::LeanType::General
        } else {
            super::doc::LeanType::Num(n)
        }
    }

    /// A term cast to a number type.
    fn cast(&self, term: &Printed, to: Num) -> Printed {
        Printed::cast(term.clone(), self.num_type(to))
    }

    /// Whether `node` is an "and" of two sides, in any notation the reading
    /// takes as one (`ands`).
    pub fn is_and(&self, node: &Node) -> bool {
        self.ands.contains(&node.notation()) && node.children.len() == 2
    }

    /// The two sides of `node` where it is an "and" (`is_and`); None of
    /// anything else.
    pub fn and_sides<'n>(&self, node: &'n Node) -> Option<(&'n Node, &'n Node)> {
        match (self.is_and(node), node.children.as_slice()) {
            (true, [l, r]) => Some((l, r)),
            _ => None,
        }
    }

    /// A writer with the same grammar and notations, and these letters.
    /// A writer with no letters yet.
    pub fn new(
        grammar: &'a Grammar,
        templates: &'a Templates,
        ands: &'a crate::matching::FxIndexSet<crate::formula::notation_id::NotationId>,
    ) -> Writer<'a> {
        Writer {
            grammar,
            templates,
            ands,
            letters: IndexMap::new(),
            wholes: IndexMap::new(),
            general: None,
            integers: Vec::new(),
            domains: IndexMap::new(),
            reals: Vec::new(),
            finite: crate::citing::finite::FiniteSets::new(),
            finite_only_by: IndexMap::new(),
            finite_under: std::rc::Rc::default(),
            empty_of: None,
            bounds: SaidBounds::default(),
            whole_bounds: SaidBounds::default(),
            root_forms: Default::default(),
        }
    }

    pub fn with_letters(&self, letters: Letters) -> Writer<'a> {
        Writer {
            grammar: self.grammar,
            templates: self.templates,
            ands: self.ands,
            letters,
            wholes: self.wholes.clone(),
            general: self.general,
            integers: self.integers.clone(),
            domains: self.domains.clone(),
            reals: self.reals.clone(),
            finite: self.finite.clone(),
            finite_only_by: self.finite_only_by.clone(),
            finite_under: self.finite_under.clone(),
            empty_of: self.empty_of.clone(),
            bounds: self.bounds.clone(),
            whole_bounds: self.whole_bounds.clone(),
            root_forms: self.root_forms.clone(),
        }
    }

    /// Give a letter the type its number system makes it: the page's ℕ and
    /// ℕ₀ are integers, kept in `wholes`, and any other system its own type.
    pub fn introduce(&mut self, letter: &str, system: System) {
        self.letters
            .insert(letter.to_string(), LetterType::Number(letter_type(system)));
        match system {
            System::Positive | System::NonNegative => {
                self.wholes.insert(letter.to_string(), system);
            }
            System::Type(_) => {
                self.wholes.shift_remove(letter);
            }
        }
    }

    /// The number system each number letter in scope is in, as the
    /// said-once rule reads them: a letter of `wholes` in ℕ or ℕ₀, any
    /// other in its type's.
    pub fn page_systems(&self) -> crate::citing::Introduced {
        use crate::rules::System as S;
        self.letters
            .iter()
            .filter_map(|(name, ty)| {
                let LetterType::Number(n) = ty else {
                    return None;
                };
                let system = match (self.wholes.get(name), n) {
                    (Some(System::Positive), Num::Int) => S::N,
                    (Some(System::NonNegative), Num::Int) | (_, Num::Nat) => S::N0,
                    (_, Num::Int) => S::Z,
                    (_, Num::Rat) => S::Q,
                    (_, Num::Real) => S::R,
                    (_, Num::Complex) => S::C,
                };
                Some((name.clone(), system))
            })
            .collect()
    }

    /// Whether the page says once that a term is in ℕ₀ (`citing::within`):
    /// n, k + 1 and 2k + 1 of letters in ℕ, as Metamath proves it from
    /// their introducing lines. Such a term goes where Lean wants a natural
    /// number as `(t).toNat`, and a power to it is a natural power.
    pub fn said_whole(&self, node: &Node) -> bool {
        use crate::rules::System;
        let letters = self.page_systems();
        let nonzero = |d: &Node| crate::citing::nonzero_said_once(d, &letters);
        // An integer by its letters and its build that a hypothesis of the
        // theorem says is at least 0, `p − 1` beside `p ≥ 1`, as the check
        // read the hypotheses (`whole_bounds`), is a whole number as surely
        // as one its build makes so, in every step alike.
        let integer = |t: &Node| {
            crate::citing::within(t, System::Z, &letters, &nonzero, &|_, _| false)
        };
        let bounded = |t: &Node, s: System| {
            let least = match s {
                System::N0 => 0,
                System::N => 1,
                _ => return false,
            };
            integer(t)
                && self.whole_bounds.terms.iter().any(|b| {
                    b.least >= least && bounds::BoundsAsk::same(self, &b.term, t)
                })
        };
        crate::citing::within(node, System::N0, &letters, &nonzero, &bounded)
    }

    /// What the set `a` counts holds, where `b` counts ∅: |S| beside |∅|.
    pub fn counted_beside_empty(&self, a: &Node, b: &Node) -> Option<Members> {
        let ([s], [e]) = (a.children.as_slice(), b.children.as_slice()) else {
            return None;
        };
        let counts = |n: &Node| &*n.notation_name() == "cardinality";
        if !counts(a) || !counts(b) || &*e.notation_name() != "empty-set" {
            return None;
        }
        self.set_members(s)
    }

    /// The line that says this term is an integer or a rational; None
    /// where none does.
    /// Whether a step names the term as a whole number, its `toNat` by a
    /// line saying it is at least 0 (`SaidInteger::back`), p − 1 from the
    /// requires line p − 1 ∈ ℕ₀.
    pub fn named_whole(&self, node: &Node) -> bool {
        self.whole_back(node).is_some()
    }

    /// Of a term a step names as a whole number by its `toNat`, the proof
    /// that its cast back is the term, `Int.toNat_of_nonneg h :
    /// ((t.toNat : ℕ) : ℤ) = t` (`SaidInteger::back`); None otherwise.
    pub fn whole_back(&self, node: &Node) -> Option<Printed> {
        self.said_integer(node).and_then(|s| s.back.clone())
    }

    fn said_integer(&self, node: &Node) -> Option<&SaidInteger> {
        if node.notation() == NUMERAL {
            return None;
        }
        let printed = self.grammar.print(node);
        self.integers.iter().find(|s| s.term == printed)
    }

    /// This writer where these lines hold as well: what they bound added to
    /// its own.
    /// The writer inside a quantifier over a number system, "for all x ∈
    /// ℝ" or "there is x ∈ ℕ": its letter introduced and bounded by the
    /// set, as `quantified` writes the body. None for a quantifier over
    /// anything else.
    pub fn inside_number_quantifier(
        &self,
        letter: &Node,
        set: &Node,
    ) -> Option<Writer<'a>> {
        if set.notation() != NUMBER_SYSTEMS || !letter.is_name() {
            return None;
        }
        let system = system_of(set)?;
        let mut inner = self.with_letters(self.letters.clone());
        inner.introduce(&letter.text, system);
        inner.bounds = bounds::inside_quantifier(self, letter, set);
        Some(inner)
    }

    pub fn knowing(&self, lines: &[Node]) -> Writer<'a> {
        let mut said = self.bounds.clone();
        let all: Vec<&Node> = lines.iter().collect();
        bounds::from_lines(self, &all, &mut said);
        let mut w = self.with_letters(self.letters.clone());
        w.bounds = said;
        w
    }

    /// The greatest whole number the term is shown to be at least: by a
    /// line in scope, or by its form, a whole numeral, a natural number
    /// letter at 0, n! at 1, a sum of bounded terms at the sum of their
    /// bounds, a − c at a's bound less the numeral c, a product of terms at
    /// least 0 at the product, a power of a base at least 1 at 1. None where
    /// nothing bounds it.
    pub fn least(&self, node: &Node) -> Option<i64> {
        bounds::least(self, node)
    }

    /// Whether the term is at least 0 by the lines in scope or its form
    /// (`citing::bounds::nonnegative`).
    pub fn nonnegative(&self, node: &Node) -> bool {
        bounds::nonnegative(self, node)
    }

    /// Whether a real power or square root is Mathlib's real one: its base
    /// is at least 0, where Mathlib's `x ^ y` and `Real.sqrt x` are set.mm's
    /// principal value. Of any other base the principal value is complex,
    /// (−4)^(1/2) = 2i where Mathlib's real power gives 0, and the node is
    /// written in ℂ. True of every other node.
    pub fn principal_is_real(&self, node: &Node) -> bool {
        bounds::principal_is_real(self, node)
    }

    /// Note the form a real power or square root is written in, where it is
    /// written (`Writer::number`), for `roots_written_both_ways`: not where
    /// a type is only asked of it, before the lines its step stands on are
    /// in scope.
    fn note_root_form(&self, node: &Node) {
        if !matches!(
            node.notation(),
            crate::notations::REAL_POWER | crate::notations::SQUARE_ROOT
        ) {
            return;
        }
        let real = self.principal_is_real(node);
        let mut forms = self.root_forms.borrow_mut();
        let seen = forms
            .entry(self.grammar.print(node))
            .or_insert((false, false));
        match real {
            true => seen.0 = true,
            false => seen.1 = true,
        }
    }

    /// A real power or square root this writer and those made from it wrote
    /// both as Mathlib's real one and as the principal one in ℂ, √(y − 3)
    /// before and after the line y − 3 ≥ 0: one term in two forms, which a
    /// step joining them would have to convert between. None where none
    /// was.
    pub fn roots_written_both_ways(&self) -> Option<String> {
        self.root_forms
            .borrow()
            .iter()
            .find(|(_, (real, complex))| *real && *complex)
            .map(|(term, _)| term.clone())
    }
}

/// The term bracketed as an argument is, unless it binds as tightly:
/// `(Set.Icc a b)`, `A`.
pub fn as_argument(term: Printed) -> Printed {
    match term.prec() < MAX {
        true => super::tactics::bracket(term),
        false => term,
    }
}

/// The integers from a to b as a finite set: `Finset.Icc a b`.
pub fn icc(from: Printed, to: Printed) -> Printed {
    Printed::applied(
        "Finset.Icc",
        super::doc::Source::Mathlib,
        vec![from, to],
        LeanType::Set(Box::new(LeanType::Num(Num::Int))),
    )
}

/// ∅ told its type, `(∅ : Set α)`, which nothing else gives Lean.
pub fn empty_of_type(ty: LeanType) -> Printed {
    let empty = Printed::constant("∅", super::doc::Source::Core, ty.clone());
    Printed::cast(empty, ty)
}

/// A term in brackets that no precedence asks for, as Lean is given a
/// function value: `(g ∘ f)`.
fn paren(term: Printed) -> Printed {
    let ty = term.ty.clone();
    Printed {
        kind: super::doc::TermKind::Paren(Box::new(term)),
        ty,
    }
}

/// `∃ m : T, g ∧ said`: a witness of a type, with a condition on it where
/// there is one.
pub fn witnessed(
    m: String,
    ty: LeanType,
    guard: Option<Printed>,
    said: Printed,
) -> Printed {
    Printed::of(
        super::doc::TermKind::Quantified {
            quant: super::doc::Quant::Exists,
            letter: m,
            letter_ty: ty,
            guard: guard.map(Box::new),
            body: Box::new(said),
            bounded: false,
        },
        LeanType::Prop,
    )
}

/// An anonymous constructor, `⟨a, b⟩`: an "and" of proofs, or a witness and
/// its proof.
pub fn anonymous(parts: Vec<Printed>) -> Printed {
    Printed::of(
        super::doc::TermKind::Listed {
            brackets: super::doc::Brackets::Angle,
            items: parts,
        },
        LeanType::Prop,
    )
}

/// A set listed by its members, `{a, b}`.
pub fn listed_set(members: Vec<Printed>, ty: LeanType) -> Printed {
    Printed::of(
        super::doc::TermKind::Listed {
            brackets: super::doc::Brackets::Brace,
            items: members,
        },
        ty,
    )
}

/// The parts joined by `op`, which groups to the right, `a ∧ b ∧ c`: each
/// bracketed where it binds more loosely than `need`. None of no parts.
pub fn joined(op: super::doc::Op, parts: Vec<Printed>, need: u32) -> Option<Printed> {
    let wrap = |p: Printed| match p.prec() < need {
        true => super::tactics::bracket(p),
        false => p,
    };
    let mut parts = parts.into_iter().rev();
    let last = wrap(parts.next()?);
    Some(parts.fold(last, |rest, p| {
        Printed::infix(op, wrap(p), rest, LeanType::Prop)
    }))
}

/// Two propositions joined by "and".
pub fn conjunction(a: Printed, b: Printed) -> Route<Printed> {
    relation_of("∧", a, b)
}

/// A relation between two terms, `l op r`; declined for a symbol that is
/// no Lean relation.
pub fn relation_of(op: &str, l: Printed, r: Printed) -> Route<Printed> {
    match super::doc::Op::of(op) {
        Some(op) => Route::Built(Printed::infix(op, l, r, super::doc::LeanType::Prop)),
        None => Route::no(format!("the relation {op}")),
    }
}

/// A template's tree with each hole filled by the term for it; declined
/// where a hole has no argument.
fn fill(template: &Template, children: &[Printed]) -> Route<Printed> {
    match template.skeleton.instantiate(children) {
        Some(tree) => Route::Built(tree),
        None => Route::no("a template with a hole no argument fills"),
    }
}

/// The functions from one set to another, as Lean takes them
/// (`Writer::functions_from`).
struct FunctionsFrom {
    /// The type of such a function.
    ty: LetterType,
    /// The set it maps from, as Lean writes it.
    from: Printed,
    /// The set it maps into, as Lean writes it.
    to: Printed,
}

/// `Set.MapsTo f from to`: f takes each member of `from` into `to`.
fn maps_to(f: Printed, from: Printed, to: Printed) -> Printed {
    Printed::applied(
        "Set.MapsTo",
        super::doc::Source::Mathlib,
        vec![f, from, to],
        super::doc::LeanType::Prop,
    )
}

/// The letter a membership in a number system names its witness by, `∃ m :
/// ℕ, (m : ℚ) = x`: m, or where x has a letter m, as m/p does, the first of
/// m₀, m₁, … it has none of.
pub fn witness_letter(x: &Node) -> String {
    let used: Vec<String> = x
        .walk()
        .iter()
        .filter(|n| n.is_name())
        .map(|n| super::names::letter(&n.text))
        .collect();
    let subscripts = ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉'];
    std::iter::once("m".to_string())
        .chain(subscripts.iter().map(|s| format!("m{s}")))
        .chain((10..).map(|i| format!("m_{i}")))
        .find(|l| !used.contains(l))
        .expect("the letters m_10, m_11, … do not run out")
}

/// What a number system is to a letter in Lean.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum System {
    /// The page's ℕ, from 1: a natural number above 0.
    Positive,
    /// ℕ₀: a natural number.
    NonNegative,
    /// ℤ, ℚ, ℝ or ℂ: the type itself.
    Type(Num),
}

/// The number system a `number-systems` node names.
pub fn system_of(set: &Node) -> Option<System> {
    if set.spelling() == NATURALS {
        return Some(System::Positive);
    }
    if set.spelling() == NATURALS0 {
        return Some(System::NonNegative);
    }
    match &*set.text {
        "ℤ" => Some(System::Type(Num::Int)),
        "ℚ" => Some(System::Type(Num::Rat)),
        "ℝ" => Some(System::Type(Num::Real)),
        "ℂ" => Some(System::Type(Num::Complex)),
        _ => None,
    }
}

/// The Lean types of a function from one number system to another, `A → B`
/// of `f : A → B`. A function into ℕ, whose values are above 0, is not one
/// Lean's ℕ says, so it has none here; one from ℕ, ℕ₀ or a range is a
/// function on all of ℤ, of which the page's facts say only what they say
/// of the part it names.
pub fn function_systems(from: &Node, to: &Node) -> Option<(Num, Num)> {
    // A function on a range of integers, a sum's term t : {a, …, b} → ℝ, or
    // on ℕ or ℕ₀, is a function on all of ℤ, of which what is said uses the
    // part the page names: a sum's index is an integer, and a natural
    // argument is cast up.
    let takes = if from.notation() == INTEGER_RANGE {
        Num::Int
    } else {
        match system_of(from)? {
            System::Positive | System::NonNegative => Num::Int,
            System::Type(n) => n,
        }
    };
    let gives = system_of(to)?;
    if gives == System::Positive {
        return None;
    }
    Some((takes, letter_type(gives)))
}

/// The system the index of a sum, product or series in `node` is in, where one runs
/// over the letter `letter`: ℕ from 1, ℕ₀ from 0 (`citing::index_system`),
/// ℤ from any other start. None where no sum in it has that index.
pub fn index_letter_system(node: &Node, letter: &str) -> Option<System> {
    node.walk().iter().find_map(|n| {
        let series = &*n.notation_name() == "series";
        if !is_big_operator(n) && !series {
            return None;
        }
        let (index, from) = match (over_range(n), n.children.as_slice()) {
            (Some([index, from, _, _]), _) => (index.clone(), from.clone()),
            (None, [index, from, _, _]) => (index.clone(), from.clone()),
            // Σ(k = a to ∞) t: its index and start.
            (None, [index, from, _]) if series => (index.clone(), from.clone()),
            _ => return None,
        };
        if !index.is_name() || &*index.text != letter {
            return None;
        }
        Some(match crate::citing::index_system(&from) {
            Some(crate::rules::System::N) => System::Positive,
            Some(crate::rules::System::N0) => System::NonNegative,
            _ => System::Type(Num::Int),
        })
    })
}

/// The system a letter running over a range is in, said once by the range
/// (`citing::range_system`): ℕ from 1, ℕ₀ from 0, ℤ from any other start.
pub fn range_letter_system(range: &Node) -> System {
    match crate::citing::range_system(range) {
        Some(crate::rules::System::N) => System::Positive,
        Some(crate::rules::System::N0) => System::NonNegative,
        _ => System::Type(Num::Int),
    }
}

/// The Lean type of the members of a set of numbers in a system the checker
/// records (`CheckedTheorem::set_systems`): integers for ℕ, ℕ₀ and ℤ, as
/// `set_type` gives them.
pub fn recorded_set_type(system: crate::rules::System) -> Num {
    match system {
        crate::rules::System::N
        | crate::rules::System::N0
        | crate::rules::System::Z => Num::Int,
        crate::rules::System::Q => Num::Rat,
        crate::rules::System::R => Num::Real,
        crate::rules::System::C => Num::Complex,
    }
}

/// The Lean type a letter introduced in a number system takes: the page's ℕ
/// and ℕ₀ are integers, as set.mm's are complex numbers with a fact.
pub fn letter_type(system: System) -> Num {
    match system {
        System::Positive | System::NonNegative => Num::Int,
        System::Type(n) => n,
    }
}

/// The type of what a number system holds where it stands as a set: the
/// page's ℕ and ℕ₀ are sets of integers (`sets::set_term`), any other
/// system a set of its own type.
pub fn set_type(system: System) -> Num {
    match system {
        System::Positive | System::NonNegative => Num::Int,
        System::Type(n) => n,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `a + b` of two letters, integers.
    fn sum_of_letters(a: &str, b: &str) -> Printed {
        let int = LeanType::Num(Num::Int);
        Printed::infix(
            super::super::doc::Op::PLUS,
            Printed::letter(a, int.clone()),
            Printed::letter(b, int.clone()),
            int,
        )
    }

    #[test]
    fn an_infix_template_brackets_by_lean_precedence() {
        let minus = Template::read("α, α → α: _1 - _2").expect("it reads");
        let sum = sum_of_letters("a", "b");
        // a + b − (a + b): the right side of a left-chaining operator is
        // bracketed at its own level, the left is not.
        let Route::Built(out) = fill(&minus, &[sum.clone(), sum]) else {
            panic!("the template fills");
        };
        assert_eq!(out.text(), "a + b - (a + b)");
    }

    #[test]
    fn an_argument_is_bracketed_unless_a_bracket_encloses_it() {
        let factorial = Template::read("ℕ → ℕ: Nat.factorial _1").expect("it reads");
        let n1 = Printed::infix(
            super::super::doc::Op::PLUS,
            Printed::letter("n", LeanType::Num(Num::Nat)),
            Printed::numeral("1", LeanType::Num(Num::Nat)),
            LeanType::Num(Num::Nat),
        );
        let Route::Built(applied) = fill(&factorial, std::slice::from_ref(&n1)) else {
            panic!("the template fills");
        };
        assert_eq!(applied.text(), "Nat.factorial (n + 1)");
        let floor = Template::read("ℝ → ℤ: ⌊_1⌋").expect("it reads");
        let Route::Built(enclosed) = fill(&floor, &[n1]) else {
            panic!("the template fills");
        };
        assert_eq!(enclosed.text(), "⌊n + 1⌋");
    }
}
