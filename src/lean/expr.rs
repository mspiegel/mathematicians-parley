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

use super::templates::{Num, Slot, Template, Templates};
use crate::citing::bounds::{self, SaidBounds};
use crate::formula::{Grammar, Node};
use crate::notations::{
    EQUALITY, EQUALS, FOR_ALL, IN, INTEGER_RANGE, LOGICAL_NOT, MEMBERSHIP, NAME,
    NATURALS, NATURALS0, NUMBER_SYSTEMS, NUMERAL, ORDER, THERE_IS,
};
use crate::outcome::Route;

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
}

/// The type variable a theorem's sets of things are sets of.
pub const THINGS: &str = "α";

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
        }
    }

    /// How Lean writes a member's type.
    pub fn lean(&self) -> String {
        match self {
            Members::Things(var) => things_name(*var),
            Members::Sets(m) => format!("Set {}", bracketed(&m.lean())),
            Members::Numbers(n) => n.lean().to_string(),
            Members::Elements(g) => super::names::letter(g),
        }
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
        match self {
            LetterType::Statement => "Prop".to_string(),
            LetterType::Number(n) => n.lean().to_string(),
            LetterType::Function { from, to } => {
                format!("{} → {}", from.lean(), to.lean())
            }
            LetterType::Set(m) => format!("Set {}", bracketed(&m.lean())),
            LetterType::Member(m) => m.lean(),
            LetterType::Map { from, to } => format!("{} → {}", from.lean(), to.lean()),
            LetterType::Group => "Type*".to_string(),
            LetterType::Identity(g) => super::names::letter(g),
            LetterType::Subgroup(g) => format!("Subgroup {}", super::names::letter(g)),
            LetterType::Property(m) => format!("{} → Prop", m.lean()),
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
    /// The set each map letter is a map from, as Lean writes it, by the
    /// letter: the A of `f : A → B`, within which a preimage is taken and
    /// an inverse is found.
    pub domains: IndexMap<String, String>,
    /// Terms the theorem puts in a hole of type ℝ, A/B of ⌊A/B⌋, as the
    /// page prints them: each is computed in ℝ wherever it is written.
    pub reals: Vec<String>,
    /// The sets the checker records finite, as the page prints them
    /// (`CheckedTheorem::said_finite`): a count of one, or of a set made
    /// from them as `citing::finite::is_finite` says, is a natural number,
    /// `A.ncard`, and of any other set in ℕ∞ (`sets::count_term`).
    pub finite: std::collections::BTreeSet<String>,
    /// For each hypothesis that makes a set finite, as printed, the sets
    /// only it does (`Writer::without_line`).
    pub finite_only_by:
        std::collections::BTreeMap<String, std::collections::BTreeSet<String>>,
    /// What ∅ holds where nothing in it says, as a count compared with the
    /// count of a set of those, |S| = |∅| (`relation_from`); None where it
    /// is a set of the theorem's things.
    pub empty_of: Option<Members>,
    /// Whether every count is written in ℕ∞, `A.encard`, finite or not:
    /// inside a relation ℕ∞ says as the page does (`formula`).
    pub in_extended: bool,
    /// What the lines in scope say terms are at least: a real power or
    /// square root of a term at least 0 is Mathlib's real one
    /// (`Writer::principal_is_real`).
    pub bounds: SaidBounds,
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

/// A term a line says is an integer or a rational: the term as the page
/// prints it, the line's Lean name, `∃ m : ℤ, (m : ℝ) = f a`, and the type
/// it says the term is in.
#[derive(Clone, Debug)]
pub struct SaidInteger {
    pub term: String,
    pub proof: String,
    pub ty: Num,
    /// The whole number written out, where a step names it so, 2 ^ ((p :
    /// ℤ) − 1).toNat of 2^(p − 1) from the line p − 1 ∈ ℕ₀, `proof` then
    /// naming its equation with the term; None where the number is the
    /// line's witness, `Classical.choose proof`.
    pub value: Option<String>,
    /// Whether the number stands for the term only where a whole number is
    /// asked, as a step names one (`theorem::named_atoms`): elsewhere the
    /// term keeps its own form. A line saying the term is an integer gives
    /// one that stands for it everywhere after.
    pub slot_only: bool,
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

/// The node with each part of the shape of `from` put as `to`.
pub(super) fn put_for(node: &Node, from: &Node, to: &Node) -> Node {
    if node.same_shape(from) {
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

    /// A writer with the same grammar and notations, and these letters.
    /// A writer with no letters yet.
    pub fn new(grammar: &'a Grammar, templates: &'a Templates) -> Writer<'a> {
        Writer {
            grammar,
            templates,
            letters: IndexMap::new(),
            wholes: IndexMap::new(),
            general: None,
            integers: Vec::new(),
            domains: IndexMap::new(),
            reals: Vec::new(),
            finite: std::collections::BTreeSet::new(),
            finite_only_by: std::collections::BTreeMap::new(),
            empty_of: None,
            in_extended: false,
            bounds: SaidBounds::default(),
            root_forms: Default::default(),
        }
    }

    pub fn with_letters(&self, letters: Letters) -> Writer<'a> {
        Writer {
            grammar: self.grammar,
            templates: self.templates,
            letters,
            wholes: self.wholes.clone(),
            general: self.general,
            integers: self.integers.clone(),
            domains: self.domains.clone(),
            reals: self.reals.clone(),
            finite: self.finite.clone(),
            finite_only_by: self.finite_only_by.clone(),
            empty_of: self.empty_of.clone(),
            in_extended: self.in_extended,
            bounds: self.bounds.clone(),
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
        let letters = self.page_systems();
        crate::citing::within(
            node,
            crate::rules::System::N0,
            &letters,
            &|d| crate::citing::nonzero_said_once(d, &letters),
            &|_, _| false,
        )
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
    fn said_integer(&self, node: &Node) -> Option<&SaidInteger> {
        if node.notation() == NUMERAL {
            return None;
        }
        let printed = self.grammar.print(node);
        self.integers.iter().find(|s| s.term == printed)
    }

    /// What these lines bound below is what this writer knows of its terms'
    /// least values.
    pub fn bounds_from<'n>(&mut self, lines: impl IntoIterator<Item = &'n Node>) {
        let lines: Vec<&Node> = lines.into_iter().collect();
        let mut out = SaidBounds::default();
        bounds::from_lines(self, &lines, &mut out);
        self.bounds = out;
    }

    /// This writer where these lines hold as well: what they bound added to
    /// its own.
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

/// A relation between two terms, `l op r`; declined for a symbol that is
/// no Lean relation.
fn relation_of(op: &str, l: Printed, r: Printed) -> Route<Printed> {
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

impl Writer<'_> {
    /// The node's arguments that every Lean form of its notation reads at ℝ,
    /// the A/B of ⌊A/B⌋, whatever their own types.
    pub fn always_real_args<'n>(&self, node: &'n Node) -> Vec<&'n Node> {
        let Some(pattern) = self.grammar.written_by(node.spelling()) else {
            return Vec::new();
        };
        let real = self
            .templates
            .always_real(&node.notation_name(), &pattern.pattern);
        self.args(node)
            .iter()
            .zip(real)
            .filter(|(_, r)| *r)
            .map(|(a, _)| a)
            .collect()
    }

    /// The template the node's notation and pattern have in Lean, or a
    /// decline naming the notation.
    pub fn template(&self, node: &Node) -> Route<&Template> {
        if let Some(t) = self.library_function(node) {
            return Route::Built(t);
        }
        let name = node.notation_name();
        let Some(pattern) = self.grammar.written_by(node.spelling()) else {
            return Route::no(format!("{name} is written by no plain pattern"));
        };
        // A real power or square root of a base not shown at least 0 is the
        // principal value, which is complex: its form in ℂ.
        if !self.principal_is_real(node) {
            let args = vec![Num::Complex; node.children.len()];
            return match self.templates.get(&name, &pattern.pattern, &args) {
                Some(t) if t.yields == Slot::Fixed(Num::Complex) => Route::Built(t),
                _ => Route::no(format!("notation {name} has no lean-builds form in ℂ")),
            };
        }
        // Of forms by type, the one for its terms' own types: a letter of
        // ℕ is a natural number, though it is computed in ℤ at least.
        let args: Vec<Num> = node
            .children
            .iter()
            .filter(|c| self.is_number(c))
            .filter_map(|c| match self.letters.get(c.text.as_str()) {
                Some(LetterType::Number(Num::Nat)) if c.is_name() => Some(Num::Nat),
                _ => self.carrier(c).built(),
            })
            .collect();
        match self.templates.get(&name, &pattern.pattern, &args) {
            Some(t) => Route::Built(t),
            None => Route::no(format!("notation {name} has no lean-builds field")),
        }
    }

    /// The 0 a term is compared with in `at`: told its type where nothing
    /// in the term fixes one, as 2^n − 1 of a natural n, which Lean would
    /// otherwise read in ℕ, where its subtraction stops at 0.
    fn zero_at(&self, x: &Node, at: Num) -> String {
        if at == Num::Nat || self.pinned(x) {
            "0".to_string()
        } else {
            format!("(0 : {})", self.type_name(at))
        }
    }

    /// The Lean form of the library function a node applies, `gcd(a, b)`;
    /// None for any other node, a letter of the page applied included.
    pub fn library_function(&self, node: &Node) -> Option<&Template> {
        if !matches!(
            node.notation(),
            crate::notations::APPLICATION | crate::notations::APPLICATION_TO_TWO
        ) {
            return None;
        }
        let f = node.children.first()?;
        if !f.is_name() || self.letters.contains_key(f.text.as_str()) {
            return None;
        }
        // Of a function Lean has at several types, the form its arguments'
        // types take: cos of a complex number is Complex.cos, and σ of a
        // natural number `ArithmeticFunction.sigma 1 n`, of an integer its
        // `toNat`'s.
        let args: Vec<Num> = node.children[1..]
            .iter()
            .filter_map(|a| self.argument_type(a))
            .collect();
        self.templates.function_at(&f.text, &args)
    }

    /// The type a library function reads an argument at: ℕ for a natural
    /// number, n of σ(n) with n ∈ ℕ, written `n.toNat` where n is an
    /// integer (`number`), and otherwise the least that holds it.
    fn argument_type(&self, a: &Node) -> Option<Num> {
        match self.natural(a) || self.said_whole(a) {
            true => Some(Num::Nat),
            false => self.carrier(a).built(),
        }
    }

    /// What a node's template fills its holes with: its children, or for a
    /// library function applied, what it is applied to.
    pub fn args<'n>(&self, node: &'n Node) -> &'n [Node] {
        if self.library_function(node).is_some() {
            &node.children[1..]
        } else {
            &node.children
        }
    }

    /// Whether the node is a number: by its sort, or a letter this writer
    /// gives a number type, the ε a "for all ε ∈ ℝ" binds, whose sort a
    /// record's reading may leave unknown.
    pub fn is_number(&self, node: &Node) -> bool {
        // A count of a set is a number of ℕ∞, which the writer's number
        // types do not hold (`sets::count_term`).
        if self.counts(node) {
            return false;
        }
        node.sort.is("number")
            || (node.is_name()
                && matches!(
                    self.letters.get(node.text.as_str()),
                    Some(LetterType::Number(_))
                ))
            // g⁻¹(y) and (g ∘ f)(x) of functions of numbers, whose sort the
            // checker leaves open, and f(i) of a function letter into
            // numbers a quantifier binds.
            || (node.notation() == crate::notations::APPLICATION
                && node.children.first().is_some_and(|f| {
                    self.inverse_of_function(f).is_some()
                        || (matches!(&*f.notation_name(), "composition" | "derivative")
                            && self.function_type(f).built().is_some())
                        || (f.is_name()
                            && self.library_function(node).is_none()
                            && self.applied(node).built().is_some())
                }))
    }

    /// The least number type that holds the node, ℤ at least: the type a
    /// formula made of it alone is computed in.
    pub fn carrier(&self, node: &Node) -> Route<Num> {
        // A term the theorem takes the floor of is a real at least.
        let own = self.own_carrier(node);
        match own {
            Route::Built(n)
                if !self.reals.is_empty()
                    && self.reals.contains(&self.grammar.print(node)) =>
            {
                Route::Built(n.max(Num::Real))
            }
            other => other,
        }
    }

    /// The least number type that holds the node by its own parts.
    fn own_carrier(&self, node: &Node) -> Route<Num> {
        // A term a line says is an integer is the integer it gives.
        if let Some(s) = self.said_integer(node) {
            return Route::Built(s.ty);
        }
        // A count of a finite set is a natural number, computed in ℤ.
        if let Some(count) = self.finite_count(node) {
            return count.map(|_| Num::Int);
        }
        // A power to an exponent that is no natural number is taken in a
        // field, where Lean's integer power is what the page means.
        if let Some([base, _]) = self.integer_power(node) {
            return match self.carrier(base) {
                Route::Built(n) => Route::Built(n.max(Num::Rat)),
                declined => declined,
            };
        }
        // A sum or a product is computed in its terms' type, its index an
        // integer.
        if is_big_operator(node) {
            return match self.summed(node) {
                Route::Built(s) => s.inner.carrier(s.term),
                Route::Declined(d) => Route::Declined(d),
            };
        }
        // A series is a limit, of real numbers as the series-sum item
        // states it.
        if matches!(&*node.notation_name(), "series" | "integral") {
            return Route::Built(Num::Real);
        }
        match node.notation() {
            NAME => match self.letters.get(node.text.as_str()) {
                Some(LetterType::Number(n)) => Route::Built((*n).max(Num::Int)),
                Some(LetterType::Function { .. }) => {
                    Route::no(format!("{} is a function, not a number", node.text))
                }
                Some(LetterType::Statement) => {
                    Route::no(format!("{} is a statement, not a number", node.text))
                }
                Some(
                    LetterType::Set(_)
                    | LetterType::Member(_)
                    | LetterType::Map { .. }
                    | LetterType::Group
                    | LetterType::Identity(_)
                    | LetterType::Subgroup(_)
                    | LetterType::Property(_),
                ) => Route::no(format!("{} is no number", node.text)),
                None => Route::no(format!("{} has no Lean type", node.text)),
            },
            NUMERAL => Route::Built(if node.text.contains('.') {
                Num::Rat
            } else {
                Num::Int
            }),
            crate::notations::APPLICATION if self.library_function(node).is_none() => {
                match self.applied(node) {
                    Route::Built(a) => Route::Built(a.gives.max(Num::Int)),
                    Route::Declined(d) => Route::Declined(d),
                }
            }
            _ => {
                let template = match self.template(node) {
                    Route::Built(t) => t,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match template.yields {
                    Slot::Fixed(n) => Route::Built(n.max(Num::Int)),
                    Slot::Prop => Route::no(format!(
                        "{} is a formula, not a number",
                        node.notation_name()
                    )),
                    Slot::Alpha(floor) => {
                        let mut out = floor;
                        for (child, slot) in self.args(node).iter().zip(&template.holes)
                        {
                            if let Slot::Alpha(_) = slot {
                                match self.carrier(child) {
                                    Route::Built(n) => out = out.max(n),
                                    Route::Declined(d) => return Route::Declined(d),
                                }
                            }
                        }
                        Route::Built(out)
                    }
                }
            }
        }
    }

    /// Where the claim is that a power to an integer exponent is an integer,
    /// 2^(n − 1) ∈ ℤ, the witness: the base's integer to the exponent's
    /// `toNat`, which is the power where a line in scope shows the exponent
    /// not negative. None for any other claim.
    pub fn integer_power_witness(&self, claim: &Node) -> Option<String> {
        let [t, set] = claim.children.as_slice() else {
            return None;
        };
        if claim.spelling() != IN
            || set.notation() != NUMBER_SYSTEMS
            || &*set.text != "ℤ"
        {
            return None;
        }
        let [base, exponent] = self.integer_power(t)?;
        let base = self.number_fixed(base, Num::Int).built()?;
        let exponent = self.number_fixed(exponent, Num::Int).built()?;
        let e = exponent.at(MAX);
        Some(format!(
            "⟨{} ^ {e}.toNat, by push_cast; rw [← zpow_natCast, Int.toNat_of_nonneg (show (0 : ℤ) ≤ {e} by parley_side)]⟩",
            base.at(76)
        ))
    }

    /// The base and exponent of a power whose exponent is no natural number
    /// as Lean computes one and is not said once in ℕ₀: a negative, an
    /// integer letter, or n − 1 of n ∈ ℕ. None for any other node.
    fn integer_power<'n>(&self, node: &'n Node) -> Option<&'n [Node; 2]> {
        if node.notation() != crate::notations::POWER {
            return None;
        }
        let parts: &[Node; 2] = node.children.as_slice().try_into().ok()?;
        (!self.natural(&parts[1]) && !self.said_whole(&parts[1])).then_some(parts)
    }

    /// What the function an application applies takes and gives: a
    /// function of numbers, or a map from a set of things into numbers,
    /// t : X → ℝ, whose value is a number.
    fn applied(&self, node: &Node) -> Route<Applied> {
        let Some(f) = node.children.first() else {
            return Route::no("an application of nothing");
        };
        if let Some(LetterType::Map {
            from,
            to: Members::Numbers(gives),
        }) = self.letters.get(f.text.as_str())
        {
            return Route::Built(Applied {
                takes: from.clone(),
                gives: *gives,
            });
        }
        match self.function_type(f) {
            Route::Built((from, to)) => Route::Built(Applied {
                takes: Members::Numbers(from),
                gives: to,
            }),
            Route::Declined(d) => Route::Declined(d),
        }
    }

    /// The types a function takes and gives: a function letter's, or a
    /// composite's, g ∘ f taking what f takes and giving what g gives.
    pub fn function_type(&self, f: &Node) -> Route<(Num, Num)> {
        if f.is_name() {
            return match self.letters.get(f.text.as_str()) {
                Some(LetterType::Function { from, to }) => Route::Built((*from, *to)),
                _ => Route::no(format!("{} has no Lean function type", f.text)),
            };
        }
        // g⁻¹ takes what g gives and gives what g takes; the bridge's
        // inverse is of a function of one type.
        if let Some((g, _)) = self.inverse_of_function(f) {
            return match self.letters.get(g.text.as_str()) {
                Some(LetterType::Function { from, to }) if from == to => {
                    Route::Built((*to, *from))
                }
                _ => Route::no(format!("{}⁻¹ of a function between two types", g.text)),
            };
        }
        // f′ of a function of reals into ℝ, Mathlib's `deriv f`, is one too.
        if let ("derivative", [g]) = (&*f.notation_name(), f.children.as_slice()) {
            return match self.function_type(g) {
                Route::Built((Num::Real, Num::Real)) => {
                    Route::Built((Num::Real, Num::Real))
                }
                Route::Built(_) => {
                    Route::no("a derivative of a function not from ℝ to ℝ")
                }
                Route::Declined(d) => Route::Declined(d),
            };
        }
        let [g, inner] = f.children.as_slice() else {
            return Route::no("a function that is no letter or composite");
        };
        if &*f.notation_name() != "composition" {
            return Route::no("a function that is no letter or composite");
        }
        let (from, middle) = match self.function_type(inner) {
            Route::Built(t) => t,
            Route::Declined(d) => return Route::Declined(d),
        };
        let (takes, to) = match self.function_type(g) {
            Route::Built(t) => t,
            Route::Declined(d) => return Route::Declined(d),
        };
        if takes != middle {
            return Route::no("a composite of functions whose types do not meet");
        }
        Route::Built((from, to))
    }

    /// The function letter a term is the inverse of, g of g⁻¹, with the
    /// domain a line gives it; None for any other term.
    fn inverse_of_function<'n>(&self, f: &'n Node) -> Option<(&'n Node, String)> {
        let [g] = f.children.as_slice() else {
            return None;
        };
        if &*f.notation_name() != "inverse"
            || !matches!(
                self.letters.get(g.text.as_str()),
                Some(LetterType::Function { .. })
            )
        {
            return None;
        }
        Some((g, self.domains.get(g.text.as_str())?.clone()))
    }

    /// A function as a printed term, a citation's value.
    pub fn function_printed(&self, f: &Node) -> Printed {
        Printed::atom(self.function_text(f))
    }

    /// A function as Lean writes it: a letter, or `(g ∘ f)`.
    fn function_text(&self, f: &Node) -> String {
        if let Some((g, domain)) = self.inverse_of_function(f) {
            return format!(
                "({} {} {domain})",
                super::sets::INVERSE,
                super::names::letter(&g.text)
            );
        }
        if let ("derivative", [g]) = (&*f.notation_name(), f.children.as_slice()) {
            return format!("(deriv {})", self.function_text(g));
        }
        match f.children.as_slice() {
            [g, inner] => format!(
                "({} ∘ {})",
                self.function_text(g),
                self.function_text(inner)
            ),
            _ => super::names::letter(&f.text),
        }
    }

    /// Whether some part of the node fixes the type Lean computes it in: a
    /// letter, a function's value, or an operation of a fixed type. A
    /// formula of numerals alone is computed in ℕ unless told otherwise.
    pub fn pinned(&self, node: &Node) -> bool {
        match node.notation() {
            NAME => true,
            NUMERAL => false,
            _ if is_big_operator(node)
                || matches!(&*node.notation_name(), "series" | "integral") =>
            {
                true
            }
            crate::notations::APPLICATION if self.library_function(node).is_none() => {
                true
            }
            _ => match self.template(node) {
                Route::Built(t) => match t.yields {
                    Slot::Alpha(_) => self
                        .args(node)
                        .iter()
                        .zip(&t.holes)
                        .any(|(c, s)| matches!(s, Slot::Alpha(_)) && self.pinned(c)),
                    _ => true,
                },
                Route::Declined(_) => true,
            },
        }
    }

    /// Whether a term may be computed in ℕ as Lean computes it there:
    /// built by `+`, `·` and powers from ℕ letters, numerals and values in
    /// ℕ. Subtraction and division are not.
    pub fn natural(&self, node: &Node) -> bool {
        if self.finite_count(node).is_some() {
            return true;
        }
        // A term a step names as a natural number is the one it names.
        if let Some(s) = self.said_integer(node) {
            return s.ty == Num::Nat;
        }
        // A power to an exponent that is no natural number is Lean's
        // integer power, in ℚ at least, whatever its base.
        if self.integer_power(node).is_some() {
            return false;
        }
        match node.notation() {
            NAME => matches!(
                self.letters.get(node.text.as_str()),
                Some(LetterType::Number(Num::Nat))
            ),
            NUMERAL => !node.text.contains('.'),
            crate::notations::APPLICATION if self.library_function(node).is_none() => {
                matches!(
                    self.applied(node),
                    Route::Built(Applied {
                        gives: Num::Nat,
                        ..
                    })
                )
            }
            _ => {
                let Route::Built(t) = self.template(node) else {
                    return false;
                };
                match t.yields {
                    Slot::Fixed(Num::Nat) => true,
                    Slot::Alpha(Num::Int) => {
                        let literal = node.spelling().text();
                        !matches!(&*literal, "−" | "/")
                            && !matches!(&*node.notation_name(), "unary-minus")
                            && self.args(node).iter().zip(&t.holes).all(|(c, s)| {
                                !matches!(s, Slot::Alpha(_)) || self.natural(c)
                            })
                    }
                    _ => false,
                }
            }
        }
    }

    /// A sum's parts: the writer its term is read with, its index letter an
    /// integer there, and its index, ends and term.
    fn summed<'n>(&self, node: &'n Node) -> Route<Summed<'_, 'n>> {
        let (index, over, term) = match (over_range(node), node.children.as_slice()) {
            (Some([index, from, to, term]), _) => {
                (index, Over::Range { from, to }, term)
            }
            (None, [index, set, term])
                if matches!(&*node.notation_name(), "sum-over" | "product-over") =>
            {
                (index, Over::Set(set), term)
            }
            (None, [index, from, to, term]) => (index, Over::Range { from, to }, term),
            (None, _) => return Route::no("a sum of other than four parts"),
        };
        if !index.is_name() {
            return Route::no("a sum whose index is no letter");
        }
        // Over a range the index is an integer; over a set, a member of it;
        // over ∅, which holds members of no one type, what the function
        // the term applies to the index takes, k of Σ(k ∈ ∅) t(k).
        let ty = match &over {
            Over::Range { .. } => LetterType::Number(Num::Int),
            Over::Set(set) => match self
                .set_members(set)
                .or_else(|| self.index_taken(index, term))
            {
                Some(m) => m.letter(),
                None => return Route::no("a sum over a set with no Lean type"),
            },
        };
        let mut inner = self.with_letters(self.letters.clone());
        inner.letters.insert(index.text.to_string(), ty);
        inner.wholes.shift_remove(&*index.text);
        // An index from 0 or 1 is said once in ℕ₀ or ℕ by where it starts
        // (`citing::index_system`), so x^k of Σ(k = 0 to n) x^k is a
        // natural power.
        if let Over::Range { from, .. } = &over {
            match crate::citing::index_system(from) {
                Some(crate::rules::System::N) => {
                    inner.introduce(&index.text, System::Positive)
                }
                Some(crate::rules::System::N0) => {
                    inner.introduce(&index.text, System::NonNegative)
                }
                _ => {}
            }
        }
        let range = match &over {
            Over::Range { from, to } => Some((*from, *to)),
            Over::Set(_) => None,
        };
        inner.bounds = bounds::inside_sum(self, index, range);
        Route::Built(Summed {
            inner,
            index,
            over,
            term,
        })
    }

    /// What a function the term applies to the index letter takes, the
    /// members k is among in t(k); None where the term applies none to it.
    fn index_taken(&self, index: &Node, term: &Node) -> Option<Members> {
        term.walk().iter().find_map(|n| {
            let applies = n.notation() == crate::notations::APPLICATION
                && self.library_function(n).is_none()
                && matches!(n.children.as_slice(), [_, x] if x.is_name() && x.text == index.text);
            match applies.then(|| self.applied(n)) {
                Some(Route::Built(a)) => Some(a.takes),
                _ => None,
            }
        })
    }

    /// Σ(k = a to b) t, `∑ k ∈ Finset.Icc a b, t`, and ∏ alike, its index ranging over
    /// the integers from a to b, and t computed in `at`. It is bracketed
    /// wherever it stands in more, since its body reaches as far right as
    /// it can.
    fn sum(&self, node: &Node, at: Num) -> Route<Printed> {
        let s = match self.summed(node) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        // Over a range, the integers between its ends, `∑ k ∈ Finset.Icc a
        // b`; over a set, Mathlib's sum over the members of a finite set,
        // `∑ᶠ x ∈ S`, which is the page's where the set is finite.
        let symbol = if is_product(node) { "∏" } else { "∑" };
        let over = match s.over {
            Over::Range { from, to } => {
                match (
                    self.number_fixed(from, Num::Int),
                    self.number_fixed(to, Num::Int),
                ) {
                    (Route::Built(f), Route::Built(t)) => format!(
                        "{symbol} {} ∈ Finset.Icc {} {}",
                        super::names::letter(&s.index.text),
                        f.at(MAX),
                        t.at(MAX)
                    ),
                    (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                        return Route::Declined(d)
                    }
                }
            }
            // ∅ takes the index's type, which Lean cannot read from it.
            Over::Set(set) if &*set.notation_name() == "empty-set" => {
                match s.inner.letters.get(s.index.text.as_str()) {
                    Some(ty) => format!(
                        "{symbol}ᶠ {} ∈ (∅ : Set {})",
                        super::names::letter(&s.index.text),
                        bracketed(&ty.lean())
                    ),
                    None => return Route::no("a sum over ∅ whose index has no type"),
                }
            }
            Over::Set(set) => match self.set_term(set) {
                Route::Built(p) => format!(
                    "{symbol}ᶠ {} ∈ {}",
                    super::names::letter(&s.index.text),
                    p.at(MAX)
                ),
                Route::Declined(d) => return Route::Declined(d),
            },
        };
        let term = match s.inner.number(s.term, at) {
            Route::Built(t) => t,
            Route::Declined(d) => return Route::Declined(d),
        };
        // The term is given its type: one built of numerals and naturals,
        // Σ(k = 1 to 3) 5 or 1/2^(j + 1), gives Lean nothing else to read
        // its type from, and Lean would take it in ℕ.
        let term = Printed::atom(format!("({} : {})", term.text(), self.type_name(at)));
        // Mathlib reads the body at 67, so `∑ k ∈ s, k + 1` would be the
        // sum of k, plus 1; a body below that is bracketed.
        Route::Built(Printed::raw(format!("{over}, {}", term.at(67)), 10))
    }

    /// Σ(k = a to ∞) t, the value of a series: the limit of its partial
    /// sums, `Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc a n, t)`,
    /// as set.mm and the series-sum item take it. Mathlib's `∑'` is 0 for a
    /// series that converges only conditionally, 1 − 1/3 + 1/5 − …, so it is
    /// not used. The partial sums run over a letter the series does not use.
    fn series(&self, node: &Node, at: Num) -> Route<Printed> {
        let [index, from, term] = node.children.as_slice() else {
            return Route::no("a series of other than three parts");
        };
        if !index.is_name() {
            return Route::no("a series whose index is no letter");
        }
        if at != Num::Real {
            return Route::no("a series computed in other than ℝ");
        }
        let used: Vec<String> =
            node.walk().iter().map(|n| n.text.to_string()).collect();
        let Some(upper) = ["n", "m", "N", "M", "j"]
            .into_iter()
            .find(|l| !used.iter().any(|u| u == l))
        else {
            return Route::no(
                "a series using every letter its partial sums could run over",
            );
        };
        let mut inner = self.with_letters(self.letters.clone());
        let system = match crate::citing::index_system(from) {
            Some(crate::rules::System::N) => System::Positive,
            Some(crate::rules::System::N0) => System::NonNegative,
            _ => System::Type(Num::Int),
        };
        inner.introduce(&index.text, system);
        let (start, body) =
            match (self.number_fixed(from, Num::Int), inner.number(term, at)) {
                (Route::Built(s), Route::Built(b)) => (s, b),
                (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                    return Route::Declined(d)
                }
            };
        let body = Printed::atom(format!("({} : {})", body.text(), self.type_name(at)));
        Route::Built(Printed::raw(format!(
                "Filter.limUnder Filter.atTop (fun {upper} : ℤ => ∑ {} ∈ Finset.Icc {} {upper}, {})",
                super::names::letter(&index.text),
                start.at(MAX),
                body.at(67)
            ), APP))
    }

    /// ∫(a to b) t dx, the integral from a to b, `∫ x in a..b, t`: Mathlib's
    /// interval integral, which runs from its first end to its second and is
    /// negated backwards, as set.mm's directed integral is. The letter is a
    /// real there, and the term is computed in ℝ.
    fn integral(&self, node: &Node, at: Num) -> Route<Printed> {
        let [from, to, term, letter] = node.children.as_slice() else {
            return Route::no("an integral of other than four parts");
        };
        if !letter.is_name() {
            return Route::no("an integral whose letter is no letter");
        }
        if at != Num::Real {
            return Route::no("an integral computed in other than ℝ");
        }
        let mut inner = self.with_letters(self.letters.clone());
        inner
            .letters
            .insert(letter.text.to_string(), LetterType::Number(Num::Real));
        let (a, b, body) = match (
            self.number(from, Num::Real),
            self.number(to, Num::Real),
            inner.number(term, Num::Real),
        ) {
            (Route::Built(a), Route::Built(b), Route::Built(t)) => (a, b, t),
            (Route::Declined(d), _, _)
            | (_, Route::Declined(d), _)
            | (_, _, Route::Declined(d)) => return Route::Declined(d),
        };
        let body = Printed::atom(format!("({} : ℝ)", body.text()));
        Route::Built(Printed::raw(
            format!(
                "∫ {} in {}..{}, {}",
                super::names::letter(&letter.text),
                a.at(MAX),
                b.at(MAX),
                body.at(67)
            ),
            10,
        ))
    }

    /// x(n) → L as n → ∞: `Filter.Tendsto (fun n : ℤ => x n) Filter.atTop
    /// (nhds L)`, the letter an integer in ℕ as any page letter in ℕ is, and
    /// the term and its limit computed in the type that holds both. Where
    /// the integers start, no limit sees.
    fn tends_to(&self, node: &Node) -> Route<Printed> {
        let [term, limit, letter] = node.children.as_slice() else {
            return Route::no("a limit of other than three parts");
        };
        if !letter.is_name() {
            return Route::no("a limit whose index is no letter");
        }
        let mut inner = self.with_letters(self.letters.clone());
        inner.introduce(&letter.text, System::Positive);
        // A limit is of real numbers, as the tends-to item states it: the
        // sequence and its limit are in ℝ at least, 1/n among them.
        let at = match (inner.carrier(term), self.carrier(limit)) {
            (Route::Built(a), Route::Built(b)) => a.max(b).max(Num::Real),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        let (body, l) = match (inner.number(term, at), self.number(limit, at)) {
            (Route::Built(b), Route::Built(l)) => (b, l),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        Route::Built(Printed::raw(
            format!(
                "Filter.Tendsto (fun {} : ℤ => ({} : {})) Filter.atTop (nhds {})",
                super::names::letter(&letter.text),
                body.text(),
                self.type_name(at),
                l.at(MAX)
            ),
            1000,
        ))
    }

    /// f tends to L at c: `Filter.Tendsto f (nhdsWithin c (D \ {c})) (nhds
    /// L)`, the limit of f at c taken over its domain D with c left out, as
    /// the limit-at definition reads it (`domain_of`).
    fn function_limit(&self, node: &Node) -> Route<Printed> {
        let [f, limit, at] = node.children.as_slice() else {
            return Route::no("a function limit of other than three parts");
        };
        if !f.is_name() {
            return Route::no("a limit of a function that has no name");
        }
        if !matches!(
            self.letters.get(f.text.as_str()),
            Some(LetterType::Function { to: Num::Real, .. })
        ) {
            return Route::no(format!("{} is no function into ℝ", f.text));
        }
        let Some(domain) = self.domain_of(&f.text) else {
            return Route::no(format!(
                "a limit of {}, whose domain no line gives",
                f.text
            ));
        };
        let (l, c) = match (self.number(limit, Num::Real), self.number(at, Num::Real)) {
            (Route::Built(l), Route::Built(c)) => (l, c),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        let point = c.at(MAX);
        Route::Built(Printed::raw(format!(
                "Filter.Tendsto {} (nhdsWithin {point} ({domain} \\ {{{point}}})) (nhds {})",
                super::names::letter(&f.text),
                l.at(MAX)
            ), 1000))
    }

    /// There is a bijection from A to B: `∃ g : α → β, Set.BijOn g A B`,
    /// α and β the types of A's and B's members. The map's letter is one
    /// neither set uses.
    fn bijection(&self, a: &Node, b: &Node) -> Route<Printed> {
        let (Some(from), Some(to)) = (self.set_members(a), self.set_members(b)) else {
            return Route::no("a bijection between sets with no Lean type");
        };
        let used: Vec<String> = [a, b]
            .iter()
            .flat_map(|s| s.walk())
            .map(|n| n.text.to_string())
            .collect();
        let Some(g) = ["g", "h", "φ", "ψ"]
            .iter()
            .find(|g| !used.iter().any(|u| u == *g))
        else {
            return Route::no("a bijection whose sets use every map letter");
        };
        match (self.set_term(a), self.set_term(b)) {
            (Route::Built(x), Route::Built(y)) => Route::Built(Printed::raw(
                format!(
                    "∃ {g} : {} → {}, Set.BijOn {g} {} {}",
                    from.lean(),
                    to.lean(),
                    x.at(MAX),
                    y.at(MAX)
                ),
                0,
            )),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        }
    }

    /// f is differentiable on U: each point of U is inside f's domain D, D
    /// about it, and f has a derivative there, `∀ x ∈ U, D ∈ nhds x ∧
    /// DifferentiableAt ℝ f x`. set.mm takes a derivative only at a point
    /// inside the domain, where it is Lean's `deriv f`; of f between number
    /// systems, D is all of ℝ and only the derivative is said.
    fn differentiable(&self, node: &Node) -> Route<Printed> {
        let [f, set] = node.children.as_slice() else {
            return Route::no("a differentiability of other than a function and a set");
        };
        if !f.is_name()
            || !matches!(
                self.letters.get(f.text.as_str()),
                Some(LetterType::Function {
                    from: Num::Real,
                    to: Num::Real
                })
            )
        {
            return Route::no(format!("{} is no function from ℝ to ℝ", f.text));
        }
        let Some(domain) = self.domain_of(&f.text) else {
            return Route::no(format!(
                "a derivative of {}, whose domain no line gives",
                f.text
            ));
        };
        let u = match self.numbers_at(set, Num::Real) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        let Some(x) = ["x", "y", "z", "t", "w", "v"]
            .into_iter()
            .find(|l| !self.letters.contains_key(*l) && *l != &*f.text)
        else {
            return Route::no("a differentiability using every letter it could bind");
        };
        let given = self.domains.contains_key(f.text.as_str());
        let f = super::names::letter(&f.text);
        let at = format!("DifferentiableAt ℝ {f} {x}");
        let said = match given {
            true => format!("{domain} ∈ nhds {x} ∧ {at}"),
            false => at,
        };
        Route::Built(Printed::raw(format!("∀ {x} ∈ {}, {said}", u.at(MAX)), 0))
    }

    /// f is continuous on D, `ContinuousOn f D`, of a function into ℝ and a
    /// set of reals: `predicate` is what goes before f.
    fn continuous(&self, node: &Node, predicate: &str) -> Route<Printed> {
        let [f, set] = node.children.as_slice() else {
            return Route::no("a continuity of other than a function and a set");
        };
        if !f.is_name()
            || !matches!(
                self.letters.get(f.text.as_str()),
                Some(LetterType::Function { to: Num::Real, .. })
            )
        {
            return Route::no(format!("{} is no function into ℝ", f.text));
        }
        match self.numbers_at(set, Num::Real) {
            Route::Built(s) => Route::Built(Printed::raw(
                format!(
                    "{predicate} {} {}",
                    super::names::letter(&f.text),
                    s.at(MAX)
                ),
                1000,
            )),
            Route::Declined(d) => Route::Declined(d),
        }
    }

    /// The node, a number, written as a Lean term of type `at`.
    pub fn number(&self, node: &Node, at: Num) -> Route<Printed> {
        self.note_root_form(node);
        let named = self
            .said_integer(node)
            .filter(|s| !s.slot_only || at <= Num::Int);
        if let Some(s) = named {
            let value = match &s.value {
                Some(v) => Printed::atom(format!("({v})")),
                None => Printed::atom(format!(
                    "(Classical.choose {} : {})",
                    s.proof,
                    s.ty.lean()
                )),
            };
            return self.raise(value, s.ty, at);
        }
        if let Some(count) = self.finite_count(node) {
            return match count {
                Route::Built(c) => self.raise(c, Num::Nat, at),
                Route::Declined(d) => Route::Declined(d),
            };
        }
        // A term the page says once is in ℕ₀, n or 2k + 1 of letters in
        // ℕ, where Lean wants a natural number: the integer it is, taken to
        // ℕ, which its fact 0 ≤ t brings back.
        if at == Num::Nat && !self.natural(node) && self.said_whole(node) {
            return match self.number(node, Num::Int) {
                Route::Built(t) => Route::Built(Printed::of(
                    super::doc::TermKind::ToNat(Box::new(t)),
                    super::doc::LeanType::Num(Num::Nat),
                )),
                Route::Declined(d) => Route::Declined(d),
            };
        }
        if at == Num::Nat && !self.natural(node) {
            return Route::no(format!(
                "{} would be computed in ℕ, where subtraction stops at 0",
                self.grammar.print(node)
            ));
        }
        if let Some([base, exponent]) = self.integer_power(node) {
            if at < Num::Rat {
                return Route::no(format!(
                    "{} is a power to an integer, taken in {}",
                    self.grammar.print(node),
                    at.lean()
                ));
            }
            let base = match self.number(base, at) {
                Route::Built(b) => b,
                declined => return declined,
            };
            let exponent = match self.number_fixed(exponent, Num::Int) {
                Route::Built(e) => e,
                declined => return declined,
            };
            // Lean reads no negation after `^`, so `a ^ -m` is written
            // `a ^ (-m)`.
            return Route::Built(Printed::raw(
                format!("{} ^ {}", base.at(76), exponent.at(76)),
                75,
            ));
        }
        if is_big_operator(node) {
            return self.sum(node, at);
        }
        if &*node.notation_name() == "series" {
            return self.series(node, at);
        }
        if &*node.notation_name() == "integral" {
            return self.integral(node, at);
        }
        match node.notation() {
            NAME => match self.letters.get(node.text.as_str()) {
                Some(LetterType::Number(n)) if *n == at => {
                    Route::Built(Printed::letter(
                        super::names::letter(&node.text),
                        self.num_type(*n),
                    ))
                }
                Some(LetterType::Number(n)) if *n < at => Route::Built(self.cast(
                    &Printed::letter(
                        super::names::letter(&node.text),
                        self.num_type(*n),
                    ),
                    at,
                )),
                Some(LetterType::Number(n)) => Route::no(format!(
                    "{} is in {}, which Lean would cast down to {}",
                    node.text,
                    n.lean(),
                    at.lean()
                )),
                _ => Route::no(format!("{} has no Lean number type", node.text)),
            },
            NUMERAL => Route::Built(Printed::numeral(&*node.text, self.num_type(at))),
            crate::notations::APPLICATION if self.library_function(node).is_none() => {
                let applied = match self.applied(node) {
                    Route::Built(t) => t,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let Some(arg) = node.children.get(1) else {
                    return Route::no("an application with no argument");
                };
                let arg = match &applied.takes {
                    Members::Numbers(from) => self.number(arg, *from),
                    _ => self.set_term(arg),
                };
                let arg = match arg {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let to = applied.gives;
                let value = Printed::raw(
                    format!(
                        "{} {}",
                        self.function_text(&node.children[0]),
                        arg.at(MAX)
                    ),
                    APP,
                );
                self.raise(value, to, at)
            }
            _ => {
                // A library function takes the form for its arguments' own
                // types, cos(0) `Real.cos 0` even in a line of complex
                // numbers, and its value is cast up there as any value is.
                let template = match self.template(node) {
                    Route::Built(t) => t,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let here = match template.yields {
                    Slot::Alpha(floor) => {
                        if at < floor && at != Num::Nat {
                            return Route::no(format!(
                                "{} is computed in {} at least, where Lean is asked for {}",
                                self.grammar.print(node),
                                floor.lean(),
                                at.lean()
                            ));
                        }
                        at
                    }
                    Slot::Fixed(n) => n,
                    Slot::Prop => {
                        return Route::no(format!(
                            "{} is a formula, not a number",
                            node.notation_name()
                        ))
                    }
                };
                // A value of a fixed type, ⌊x⌋ in ℤ, computes what it takes
                // in that part's own least type, not the type around it.
                let alpha = match template.yields {
                    Slot::Fixed(_) => match self.alpha_of(node, template) {
                        Route::Built(a) => a,
                        Route::Declined(d) => return Route::Declined(d),
                    },
                    _ => here,
                };
                let children = match self.holes(node, template, alpha) {
                    Route::Built(c) => c,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // A value of a fixed type an operation makes, ⌊x⌋ mod 10 in ℤ,
                // is cast up whole at its own type first: Lean puts a cast
                // around such a term at its leaves, `(a % (10 : ℤ) : ℝ)`
                // taking the remainder in ℝ.
                let value = match fill(template, &children) {
                    Route::Built(v) => v,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let value = match template.yields {
                    Slot::Fixed(_) if here < at && value.prec() < APP => {
                        self.cast(&value, here)
                    }
                    _ => value,
                };
                self.raise(value, here, at)
            }
        }
    }

    /// A value of type `own` as a term of type `at`: itself, or cast up.
    fn raise(&self, value: Printed, own: Num, at: Num) -> Route<Printed> {
        if own == at {
            Route::Built(value)
        } else if own == Num::Real && at == Num::Complex && value.prec() == 75 {
            // Lean takes `(x ^ a : ℂ)` as x cast up to the power a, and has
            // no power of a complex number to a real exponent, so a power is
            // cast whole, at its own type first.
            let own_typed = self.cast(&value, own);
            Route::Built(self.cast(&own_typed, at))
        } else if own < at {
            Route::Built(self.cast(&value, at))
        } else {
            Route::no(format!(
                "a value in {} where Lean is asked for {}",
                own.lean(),
                at.lean()
            ))
        }
    }

    /// Each child of a node in its template's hole: a number in the type
    /// the hole takes, `alpha` for a hole of the formula's type, or a
    /// formula.
    fn holes(
        &self,
        node: &Node,
        template: &Template,
        alpha: Num,
    ) -> Route<Vec<Printed>> {
        let args = self.args(node);
        if args.len() != template.holes.len() {
            return Route::no(format!(
                "{} has {} parts and its lean template {} holes",
                node.notation_name(),
                args.len(),
                template.holes.len()
            ));
        }
        // A value of a fixed type, ⌊7/2⌋ in ℤ, takes no type from around
        // it, so where nothing in what it takes fixes that type the type is
        // written: ⌊(7 : ℝ) / 2⌋.
        let told = matches!(template.yields, Slot::Fixed(_))
            && !args
                .iter()
                .zip(&template.holes)
                .any(|(c, s)| matches!(s, Slot::Alpha(_)) && self.pinned(c));
        // The later part of "P and Q" or "if P then Q" is read where P holds,
        // √x of "x > 0 and x² < √x" the square root of a number at least 0.
        let guarded = matches!(
            node.notation(),
            crate::notations::CONJUNCTION
                | crate::notations::IMPLICATION
                | crate::notations::CONDITIONAL
        );
        let mut out = Vec::new();
        for (i, (child, slot)) in args.iter().zip(&template.holes).enumerate() {
            let printed = match slot {
                Slot::Alpha(_) if told => {
                    self.number(child, alpha).map(|p| self.cast(&p, alpha))
                }
                Slot::Alpha(_) => self.number(child, alpha),
                Slot::Fixed(n) => self.number_fixed(child, *n),
                Slot::Prop if guarded && i > 0 => {
                    self.knowing(&args[..i]).formula(child)
                }
                Slot::Prop => self.formula(child),
            };
            match printed {
                Route::Built(p) => out.push(p),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        Route::Built(out)
    }

    /// A number in a hole that always takes type `n`: computed there, a
    /// term too wide for it declined. A formula of numerals alone is
    /// written with its type.
    pub fn number_fixed(&self, child: &Node, n: Num) -> Route<Printed> {
        if n != Num::Nat {
            match self.carrier(child) {
                Route::Built(c) if c > n => {
                    return Route::no(format!(
                        "{} is in {}, where Lean needs {}",
                        self.grammar.print(child),
                        c.lean(),
                        n.lean()
                    ))
                }
                Route::Built(_) => {}
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        let printed = match self.number(child, n) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        if self.pinned(child) || n == Num::Nat {
            Route::Built(printed)
        } else {
            Route::Built(self.cast(&printed, n))
        }
    }

    /// The node, a formula, written as a Lean proposition.
    pub fn formula(&self, node: &Node) -> Route<Printed> {
        // A letter that stands for a statement.
        if node.is_name()
            && self.letters.get(node.text.as_str()) == Some(&LetterType::Statement)
        {
            return Route::Built(Printed::letter(
                super::names::letter(&node.text),
                super::doc::LeanType::Prop,
            ));
        }
        // A relation of counts ℕ∞ says as the page does, k ≤ |W|, counts
        // in ℕ∞ even of a set this theorem knows is finite, as set.mm's ♯
        // counts: one sentence is then one Lean sentence in every theorem
        // that says or cites it (`Writer::said_in_extended`).
        let relation = match (node.notation(), node.children.as_slice()) {
            (LOGICAL_NOT, [inner]) => inner,
            _ => node,
        };
        if matches!(relation.notation(), EQUALITY | ORDER)
            && !self.in_extended
            && self.said_in_extended(relation)
        {
            let mut w = self.with_letters(self.letters.clone());
            w.in_extended = true;
            return w.formula(node);
        }
        // not (a = b) between numbers is written a ≠ b, as Mathlib writes it.
        if let ([inner], LOGICAL_NOT) = (node.children.as_slice(), node.notation()) {
            if inner.notation() == EQUALITY
                && inner.children.iter().all(|c| self.is_number(c))
                && self.wide_in_slot(inner).is_none()
            {
                return self.relation(inner, true);
            }
        }
        if let Some(said) = self.slot_witness(node) {
            return said;
        }
        if &*node.notation_name() == "tends-to" {
            return self.tends_to(node);
        }
        if &*node.notation_name() == "function-limit" {
            return self.function_limit(node);
        }
        if &*node.notation_name() == "continuous" {
            return self.continuous(node, "ContinuousOn");
        }
        if &*node.notation_name() == "differentiable" {
            return self.differentiable(node);
        }
        // D is open: `IsOpen D`, of a set of reals.
        if let ("open", [set]) = (&*node.notation_name(), node.children.as_slice()) {
            return self
                .numbers_at(set, Num::Real)
                .map(|s| Printed::raw(format!("IsOpen {}", s.at(MAX)), 1000));
        }
        // There is a bijection from A to B: some map of the one's members to
        // the other's that is one-to-one from A onto B, `Set.BijOn g A B`.
        if let ("bijection", [a, b]) =
            (&*node.notation_name(), node.children.as_slice())
        {
            return self.bijection(a, b);
        }
        // f is a function on a set: a Lean function is one on every set of
        // the type it takes, its values off the set none of the page's. Of
        // numbers, a set of numbers it takes; of things, a set of things.
        if let ("function-on", [f, set]) =
            (&*node.notation_name(), node.children.as_slice())
        {
            let takes = match (self.letters.get(f.text.as_str()), self.set_members(set))
            {
                (
                    Some(LetterType::Function { from, .. }),
                    Some(Members::Numbers(n)),
                ) => n <= *from,
                (Some(LetterType::Map { from, .. }), Some(m)) => *from == m,
                _ => false,
            };
            return match takes {
                true => Route::Built(Printed::truth()),
                false => Route::no(format!(
                    "{} is a function on a set of no type it takes",
                    f.text
                )),
            };
        }
        // P(t), the property P of t: `P t`.
        if let ("holds-of", [p, t]) = (&*node.notation_name(), node.children.as_slice())
        {
            let Some(LetterType::Property(members)) = self.letters.get(p.text.as_str())
            else {
                return Route::no(format!(
                    "{} holds of a term, and is no property",
                    p.text
                ));
            };
            return self.element_term(t, members).map(|t| {
                Printed::raw(
                    format!("{} {}", super::names::letter(&p.text), t.at(MAX)),
                    1023,
                )
            });
        }
        // there is a ∈ X, with nothing said of a: set.mm's "there is" over a
        // true body, `∃ a ∈ X, True`.
        if let ("there-is-some", [letter, set]) =
            (&*node.notation_name(), node.children.as_slice())
        {
            if self.set_members(set).is_none() {
                return Route::no("there is some member of a set with no Lean type");
            }
            return self.set_term(set).map(|s| {
                Printed::raw(
                    format!(
                        "∃ {} ∈ {}, True",
                        super::names::letter(&letter.text),
                        s.at(51)
                    ),
                    0,
                )
            });
        }
        // A relation between sets, A ⊆ B or A = B.
        if &*node.notation_name() == "subset" {
            if let Some(r) = self.set_relation(node, "⊆") {
                return r;
            }
        }
        if node.notation() == EQUALITY {
            if let Some(r) = self.set_relation(node, "=") {
                return r;
            }
        }
        // What a map between sets is, f : A → B or f : A → B is one-to-one.
        if let Some(r) = self.map_claim(node) {
            return r;
        }
        // A count of a set, |A| = 2 or 1 ≤ |A|, in ℕ∞; and A is finite.
        if matches!(node.notation(), EQUALITY | ORDER) {
            if let Some(r) = self.count_relation(node) {
                return r;
            }
        }
        if let Some(r) = self.finite(node) {
            return r;
        }
        if let Some(r) = self.subgroup_claim(node) {
            return r;
        }
        if let Some(r) = self.polynomial_claim(node) {
            return r;
        }
        match node.notation() {
            EQUALITY | ORDER if node.children.len() == 2 => self.relation(node, false),
            MEMBERSHIP => self.membership(node),
            // f : A → B, which Lean's types give where f takes and gives
            // those.
            crate::notations::FUNCTION_TYPE => {
                let [f, from, to] = node.children.as_slice() else {
                    return Route::no("a function type of other than three parts");
                };
                // Between sets of numbers, g : D → ℝ: that g maps the one
                // into the other, at the function's own types.
                let Some((takes, gives)) = function_systems(from, to) else {
                    let Route::Built((own_from, own_to)) = self.function_type(f) else {
                        return Route::no(
                            "a function type between sets that are no number system",
                        );
                    };
                    return match (
                        self.numbers_at(from, own_from),
                        self.numbers_at(to, own_to),
                    ) {
                        (Route::Built(a), Route::Built(b)) => {
                            Route::Built(Printed::raw(
                                format!(
                                    "Set.MapsTo {} {} {}",
                                    self.function_text(f),
                                    a.at(MAX),
                                    b.at(MAX)
                                ),
                                APP,
                            ))
                        }
                        (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                            Route::Declined(d)
                        }
                    };
                };
                // Between number systems, by f's type, where it takes all
                // the domain's numbers and gives numbers of the codomain:
                // F : ℕ₀ → ℝ of F from ℤ into ℤ.
                match self.function_type(f) {
                    Route::Built((own_from, own_to))
                        if takes <= own_from && own_to <= gives =>
                    {
                        Route::Built(Printed::truth())
                    }
                    Route::Built(_) => {
                        Route::no("a function type other than the function's own")
                    }
                    Route::Declined(d) => Route::Declined(d),
                }
            }
            THERE_IS | FOR_ALL => self.quantified(node),
            crate::notations::COMMA_CONJUNCTION => {
                let mut parts = Vec::new();
                for (i, c) in node.children.iter().enumerate() {
                    match self.knowing(&node.children[..i]).formula(c) {
                        Route::Built(p) => parts.push(p.at(36)),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                Route::Built(Printed::raw(parts.join(" ∧ "), 35))
            }
            _ => {
                let template = match self.template(node) {
                    Route::Built(t) => t,
                    Route::Declined(d) => return Route::Declined(d),
                };
                if template.yields != Slot::Prop {
                    return Route::no(format!(
                        "{} is a number, not a formula",
                        node.notation_name()
                    ));
                }
                let alpha = match self.alpha_of(node, template) {
                    Route::Built(a) => a,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match self.holes(node, template, alpha) {
                    Route::Built(children) => fill(template, &children),
                    Route::Declined(d) => Route::Declined(d),
                }
            }
        }
    }

    /// A formula that puts a term Lean does not compute as a whole number
    /// in a slot for one: "2^p − 1 divides 2^(p − 1)" of a power that is a
    /// rational in Lean, "2^(p − 1)·(2^p − 1) is perfect", gcd(2^(p − 1), b)
    /// = 1. The term is some whole number m, and the formula is said of m:
    /// `∃ m : ℤ, (m : ℚ) = 2 ^ (p − 1) ∧ 2 ^ p − 1 ∣ m`. set.mm writes the
    /// term as it stands, and its divides, σ and gcd hold of whole numbers
    /// only, so its formula holds exactly where this one does; the term
    /// keeps its one form (`GOALS.md` decision 20). None where no such slot
    /// holds such a term, or none whose letters are all the formula's own.
    fn slot_witness(&self, node: &Node) -> Option<Route<Printed>> {
        let (term, whole) = self.wide_in_slot(node)?;
        let at = match self.carrier(&term) {
            Route::Built(n) => n,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let value = match self.number_fixed(&term, at) {
            Route::Built(v) => v,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let m = witness_letter(node);
        let mut inner = self.with_letters(self.letters.clone());
        inner.letters.insert(m.clone(), LetterType::Number(whole));
        let named = Node::name(crate::formula::Sort::of("number"), &m);
        let body = match inner.formula(&put_for(node, &term, &named)) {
            Route::Built(b) => b,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        Some(Route::Built(Printed::raw(
            format!(
                "∃ {m} : {}, ({m} : {}) = {} ∧ {}",
                whole.lean(),
                self.type_name(at),
                value.at(51),
                body.at(36)
            ),
            0,
        )))
    }

    /// The first term the formula puts in a slot for a whole number that
    /// Lean does not compute as one, with the slot's type, ℤ or ℕ: an
    /// argument of divides, gcd or σ of a type wider than ℤ, or one of ℕ
    /// that is no natural number. Only a term whose letters are all free
    /// in the formula, so that the witness may stand outside it; and none
    /// inside a connective or a quantifier, whose own parts are formulas
    /// said apart. None where there is none.
    pub(super) fn wide_in_slot(&self, node: &Node) -> Option<(Node, Num)> {
        use crate::notations::{
            BICONDITIONAL, COMMA_CONJUNCTION, CONDITIONAL, CONJUNCTION, DISJUNCTION,
            IMPLICATION,
        };
        let joins = matches!(
            node.notation(),
            CONJUNCTION
                | COMMA_CONJUNCTION
                | DISJUNCTION
                | IMPLICATION
                | CONDITIONAL
                | BICONDITIONAL
                | LOGICAL_NOT
                | FOR_ALL
                | THERE_IS
        );
        if joins {
            return None;
        }
        node.walk().into_iter().find_map(|n| self.wide_arg(&n))
    }

    /// `wide_in_slot` of one node's own arguments. A power's exponent is no
    /// such slot: one that is no natural number makes the power Lean's
    /// integer power (`Writer::integer_power`).
    fn wide_arg(&self, n: &Node) -> Option<(Node, Num)> {
        if n.notation() == crate::notations::POWER {
            return None;
        }
        let template = self.template(n).built()?;
        let args = self.args(n);
        template.holes.iter().zip(args).find_map(|(slot, arg)| {
            let whole = match slot {
                Slot::Fixed(w @ (Num::Nat | Num::Int)) => *w,
                _ => return None,
            };
            let free = arg
                .names()
                .iter()
                .all(|name| self.letters.contains_key(name.as_str()));
            // A term said once in ℕ₀ is written `t.toNat` there (`number`).
            let wide = match whole {
                Num::Nat => !self.natural(arg) && !self.said_whole(arg),
                _ => self.carrier(arg).built().is_some_and(|c| c > Num::Int),
            };
            (self.is_number(arg) && free && wide).then(|| (arg.clone(), whole))
        })
    }

    /// The type a formula's `α` holes are computed in: the least that holds
    /// each of them.
    fn alpha_of(&self, node: &Node, template: &Template) -> Route<Num> {
        let mut out = Num::Int;
        for (child, slot) in self.args(node).iter().zip(&template.holes) {
            if let Slot::Alpha(floor) = slot {
                out = out.max(*floor);
                match self.carrier(child) {
                    Route::Built(n) => out = out.max(n),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        }
        Route::Built(out)
    }

    /// `a = b`, `a < b` and the rest between two numbers, both sides in the
    /// least type that holds them; a side of numerals alone is told its
    /// type where the other does not fix it. `negated` writes an equation
    /// as `≠`.
    fn relation(&self, node: &Node, negated: bool) -> Route<Printed> {
        self.relation_from(node, negated, Num::Int)
    }

    /// A relation of numerals alone, `5 = 0`, written in the type `floor`
    /// at least: the type of the lines it is reached from.
    pub fn closed_formula(&self, node: &Node, floor: Num) -> Route<Printed> {
        // A count, |∅| = 0, is in ℕ∞ whatever the lines around it; sets,
        // {1, …, 0} = ∅, are of the types their members are.
        if self.counts(node)
            || (matches!(node.notation(), EQUALITY | ORDER)
                && self.said_in_extended(node))
        {
            return self.formula(node);
        }
        if let [left, right] = node.children.as_slice() {
            let of_sets = matches!(node.notation(), EQUALITY | ORDER)
                && (self.set_members(left).is_some()
                    || self.set_members(right).is_some());
            if of_sets {
                return self.formula(node);
            }
        }
        if let ([inner], LOGICAL_NOT) = (node.children.as_slice(), node.notation()) {
            if inner.notation() == EQUALITY {
                return self.relation_from(inner, true, floor);
            }
        }
        match node.notation() {
            EQUALITY | ORDER => self.relation_from(node, false, floor),
            _ => self.formula(node),
        }
    }

    fn relation_from(&self, node: &Node, negated: bool, floor: Num) -> Route<Printed> {
        let [left, right] = node.children.as_slice() else {
            return Route::no("a relation of other than two sides");
        };
        // |S| = |∅|: ∅ is a set of what S holds.
        if self.empty_of.is_none() {
            if let Some(m) = self
                .counted_beside_empty(left, right)
                .or_else(|| self.counted_beside_empty(right, left))
            {
                let mut w = self.with_letters(self.letters.clone());
                w.empty_of = Some(m);
                return w.relation_from(node, negated, floor);
            }
        }
        if !self.is_number(left) || !self.is_number(right) {
            return Route::no(format!(
                "{} between terms that are not numbers",
                node.notation_name()
            ));
        }
        let at = match (self.carrier(left), self.carrier(right)) {
            (Route::Built(a), Route::Built(b)) => a.max(b).max(floor),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        // ℂ has no order: x < √y of a y not shown at least 0, whose square
        // root is the principal one in ℂ, is not written.
        if node.notation() == ORDER && at == Num::Complex {
            return Route::no("an order between complex numbers");
        }
        let mut l = match self.number(left, at) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let r = match self.number(right, at) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        if !self.pinned(left) && !self.pinned(right) {
            l = self.cast(&l, at);
        }
        let op = match &*node.spelling().text() {
            "=" if node.spelling() == EQUALS && negated => "≠",
            "=" if node.spelling() == EQUALS => "=",
            "<" => "<",
            ">" => ">",
            "≤" => "≤",
            "≥" => "≥",
            other => return Route::no(format!("the relation {other}")),
        };
        relation_of(op, l, r)
    }

    /// `x ∈ S`. In a number system, the membership is what it says of x in
    /// Lean: nothing more than x's type where that already holds it,
    /// `0 < n` for the page's ℕ, which starts at 1, and otherwise that some
    /// member of the system is x. In a range, x lies between its ends.
    fn membership(&self, node: &Node) -> Route<Printed> {
        let [x, set] = node.children.as_slice() else {
            return Route::no("a membership of other than two sides");
        };
        // D ∈ 𝒫ℝ of a set of numbers is D ⊆ ℝ.
        if let ("powerset", [whole]) = (&*set.notation_name(), set.children.as_slice())
        {
            if let Some(Members::Numbers(_)) = self.set_members(whole) {
                let subset = node.with_children(vec![x.clone(), whole.clone()]);
                if let Some(r) = self.set_relation(&subset, "⊆") {
                    return r;
                }
            }
        }
        if set.notation() == NUMBER_SYSTEMS {
            if let Some(r) = self.count_in_system(x, set) {
                return r;
            }
            return self.in_system(x, set);
        }
        // x ∈ {a, b, c} of numbers: a membership of Lean's sets, in the
        // least type that holds x and every member, so that x is written
        // once, as the page writes it. Ahead of other sets, whose type is
        // their members' alone.
        if matches!(
            &*set.notation_name(),
            "singleton" | "listed-two" | "listed-three" | "listed-four"
        ) && self.is_number(x)
        {
            let mut at = Num::Int;
            for n in std::iter::once(x).chain(&set.children) {
                match self.carrier(n) {
                    Route::Built(c) => at = at.max(c),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            let mut members = Vec::new();
            for member in &set.children {
                match self.number_fixed(member, at) {
                    Route::Built(p) => members.push(p.text()),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            let x = match self.number_fixed(x, at) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            return Route::Built(Printed::raw(
                format!(
                    "{} ∈ ({{{}}} : Set {})",
                    x.at(51),
                    members.join(", "),
                    self.type_name(at)
                ),
                50,
            ));
        }
        if let Some(m) = self.set_membership(x, set) {
            return m;
        }
        if set.notation() == INTEGER_RANGE {
            let [from, to] = set.children.as_slice() else {
                return Route::no("a range of other than two ends");
            };
            // A range whose ends are no integers as Lean computes them, 6/3,
            // is said by the order of its integer member between them, in
            // the type that holds all three. A member that may be no integer
            // would lose that it is one.
            if matches!(self.carrier(x), Route::Built(c) if c > Num::Int) {
                return Route::no(format!(
                    "{} is a member of a range and may be no integer",
                    self.grammar.print(x)
                ));
            }
            let wide = [x, from, to]
                .iter()
                .any(|n| matches!(self.carrier(n), Route::Built(c) if c > Num::Int));
            if wide {
                let mut at = Num::Int;
                for n in [x, from, to] {
                    match self.carrier(n) {
                        Route::Built(c) => at = at.max(c),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                let mut out = Vec::new();
                for n in [from, x, to] {
                    match self.number(n, at) {
                        Route::Built(p) => out.push(p),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                if !self.pinned(x) && !self.pinned(from) {
                    out[0] = self.cast(&out[0], at);
                }
                return Route::Built(Printed::raw(
                    format!(
                        "{} ≤ {} ∧ {} ≤ {}",
                        out[0].at(51),
                        out[1].at(51),
                        out[1].at(51),
                        out[2].at(51)
                    ),
                    35,
                ));
            }
            // Each written as an integer, a numeral too, so that a range of
            // numerals alone is not read in ℕ.
            let parts = [
                self.number_fixed(x, Num::Int),
                self.number_fixed(from, Num::Int),
                self.number_fixed(to, Num::Int),
            ];
            let mut out = Vec::new();
            for p in parts {
                match p {
                    Route::Built(p) => out.push(p),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            return Route::Built(Printed::raw(
                format!(
                    "{} ∈ Finset.Icc {} {}",
                    out[0].at(51),
                    out[1].at(MAX),
                    out[2].at(MAX)
                ),
                50,
            ));
        }
        Route::no(format!("a membership of {}", set.notation_name()))
    }

    /// `x ∈ ℤ` and the like.
    fn in_system(&self, x: &Node, set: &Node) -> Route<Printed> {
        let system = match system_of(set) {
            Some(s) => s,
            None => return Route::no(format!("the number system {}", set.text)),
        };
        let own = match self.carrier(x) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        };
        let natural_letter = x.is_name()
            && matches!(
                self.letters.get(x.text.as_str()),
                Some(LetterType::Number(Num::Nat))
            );
        let held = if natural_letter { Num::Nat } else { own };
        match system {
            System::Positive if held <= Num::Int => {
                let at = if natural_letter { Num::Nat } else { Num::Int };
                let zero = self.zero_at(x, at);
                let x = match self.number(x, at) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                relation_of("<", Printed::atom(zero), x)
            }
            System::NonNegative if held <= Num::Int => {
                if natural_letter {
                    return Route::Built(Printed::truth());
                }
                let zero = self.zero_at(x, Num::Int);
                let x = match self.number(x, Num::Int) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                relation_of("≤", Printed::atom(zero), x)
            }
            System::Type(n) if held <= n => Route::Built(Printed::truth()),
            System::Type(n) => {
                let m = witness_letter(x);
                let x = match self.number(x, own) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                Route::Built(Printed::raw(
                    format!(
                        "∃ {m} : {}, ({m} : {}) = {}",
                        self.type_name(n),
                        self.type_name(own),
                        x.at(51)
                    ),
                    0,
                ))
            }
            System::Positive | System::NonNegative => {
                let m = witness_letter(x);
                let x = match self.number(x, own) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let order = if system == System::Positive {
                    "<"
                } else {
                    "≤"
                };
                Route::Built(Printed::raw(
                    format!(
                        "∃ {m} : ℤ, 0 {order} {m} ∧ ({m} : {}) = {}",
                        self.type_name(own),
                        x.at(51)
                    ),
                    0,
                ))
            }
        }
    }

    /// `there is k ∈ S with P` and `for all k ∈ S, P`, the letter typed by
    /// the set it ranges over.
    fn quantified(&self, node: &Node) -> Route<Printed> {
        let [letter, set, body] = node.children.as_slice() else {
            return Route::no("a quantifier of other than three parts");
        };
        if !letter.is_name() {
            return Route::no("a quantifier over a term that is no letter");
        }
        let exists = node.notation() == THERE_IS;
        if let Some(q) = self.quantified_over_set(letter, set, body, exists) {
            return q;
        }
        if let Some(q) = self.quantified_over_polynomials(letter, set, body, exists) {
            return q;
        }
        if &*set.notation_name() == "functions-from" {
            return self.quantified_over_functions(letter, set, body, exists);
        }
        let name = super::names::letter(&letter.text);
        let (system, guard) = if set.notation() == NUMBER_SYSTEMS {
            match system_of(set) {
                Some(System::Type(n)) => (System::Type(n), None),
                Some(System::Positive) => {
                    (System::Positive, Some(format!("0 < {name}")))
                }
                Some(System::NonNegative) => {
                    (System::NonNegative, Some(format!("0 ≤ {name}")))
                }
                None => return Route::no(format!("the number system {}", set.text)),
            }
        } else if set.notation() == INTEGER_RANGE {
            let [from, to] = set.children.as_slice() else {
                return Route::no("a range of other than two ends");
            };
            let ends = (self.number(from, Num::Int), self.number(to, Num::Int));
            let (Route::Built(from), Route::Built(to)) = ends else {
                return Route::no("a range whose ends are not integers");
            };
            (
                range_letter_system(set),
                Some(format!(
                    "{name} ∈ Finset.Icc {} {}",
                    from.at(MAX),
                    to.at(MAX)
                )),
            )
        } else {
            return Route::no(format!("a quantifier over {}", set.notation_name()));
        };
        let ty = letter_type(system);
        let mut inner = self.with_letters(self.letters.clone());
        inner.introduce(&letter.text, system);
        // The letter is bounded by the set it runs over, x ≥ 0 of "for all
        // x ∈ ℕ₀", as a letter the header lets is, for a square root of it.
        inner.bounds = bounds::inside_quantifier(self, letter, set);
        let body = match inner.formula(body) {
            Route::Built(b) => b,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A body the letter's type already makes true says nothing.
        if body.text() == "True" {
            return Route::Built(Printed::truth());
        }
        let ty = self.type_name(ty);
        let text = match (exists, guard) {
            (true, None) => format!("∃ {name} : {ty}, {}", body.text()),
            (true, Some(g)) => format!("∃ {name} : {ty}, {g} ∧ {}", body.at(36)),
            (false, None) => format!("∀ {name} : {ty}, {}", body.text()),
            (false, Some(g)) => format!("∀ {name} : {ty}, {g} → {}", body.at(25)),
        };
        Route::Built(Printed::raw(text, 0))
    }

    /// The type of a function from one set to another: between sets of
    /// numbers, a function of the numbers' types, g : {1, …, j} → ℕ a
    /// function from ℤ to ℤ; otherwise a map between what the sets hold.
    /// None where either set has no Lean type.
    pub fn function_between(&self, from: &Node, to: &Node) -> Option<LetterType> {
        match (self.set_members(from)?, self.set_members(to)?) {
            (Members::Numbers(m), Members::Numbers(n)) => {
                Some(LetterType::Function { from: m, to: n })
            }
            (a, b) => Some(LetterType::Map { from: a, to: b }),
        }
    }

    /// "there is f : A → B with …" and "for all f : A → B, …": f a Lean
    /// function of the types the sets' members are, and that it maps A
    /// into B a fact beside it, `∃ f : ℤ → ℤ, Set.MapsTo f A B ∧ …`.
    fn quantified_over_functions(
        &self,
        letter: &Node,
        set: &Node,
        body: &Node,
        exists: bool,
    ) -> Route<Printed> {
        let [from, to] = set.children.as_slice() else {
            return Route::no("the functions between other than two sets");
        };
        let Some(ty) = self.function_between(from, to) else {
            return Route::no("the functions between sets with no Lean type");
        };
        let sides = match &ty {
            LetterType::Function { from: m, to: n } => {
                (self.numbers_at(from, *m), self.numbers_at(to, *n))
            }
            _ => (self.set_term(from), self.set_term(to)),
        };
        let (from_text, to_text) = match sides {
            (Route::Built(f), Route::Built(t)) => (f, t),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        let name = super::names::letter(&letter.text);
        let lean_type = ty.lean();
        let mut inner = self.with_letters(self.letters.clone());
        inner.letters.insert(letter.text.to_string(), ty);
        let body = match inner.formula(body) {
            Route::Built(b) => b,
            Route::Declined(d) => return Route::Declined(d),
        };
        let maps = format!(
            "Set.MapsTo {name} {} {}",
            from_text.at(MAX),
            to_text.at(MAX)
        );
        let text = match exists {
            true => format!("∃ {name} : {lean_type}, {maps} ∧ {}", body.at(36)),
            false => format!("∀ {name} : {lean_type}, {maps} → {}", body.at(25)),
        };
        Route::Built(Printed::raw(text, 0))
    }
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

    #[test]
    fn an_infix_template_brackets_by_lean_precedence() {
        let minus = Template::read("α, α → α: _1 - _2").expect("it reads");
        let sum = Printed::raw("a + b".to_string(), 65);
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
        let n1 = Printed::raw("n + 1".to_string(), 65);
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
