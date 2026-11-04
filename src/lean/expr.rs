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

/// What the members of a set are in Lean: the one type of things a
/// theorem's sets hold, `α`, as set.mm's sets all hold sets; sets of
/// those, 𝒫A's members; or numbers of one type, {2n : n ∈ ℤ}'s.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Members {
    Things,
    Sets(Box<Members>),
    Numbers(Num),
    /// The elements of the group of this page name, of Lean type G.
    Elements(String),
}

/// The type variable a theorem's sets of things are sets of.
pub const THINGS: &str = "α";

impl Members {
    /// The members a set of this sort has; None for a sort no Lean type is
    /// written for yet, numbers among them.
    pub fn of_set(sort: &crate::formula::node::Whole) -> Option<Members> {
        match sort {
            crate::formula::node::Whole::Set(inner) => Members::of(inner),
            _ => None,
        }
    }

    /// Members of this sort.
    pub fn of(sort: &crate::formula::node::Whole) -> Option<Members> {
        match sort {
            crate::formula::node::Whole::Open => Some(Members::Things),
            crate::formula::node::Whole::Set(inner) => {
                Members::of(inner).map(|m| Members::Sets(Box::new(m)))
            }
            _ => None,
        }
    }

    /// How Lean writes a member's type.
    pub fn lean(&self) -> String {
        match self {
            Members::Things => THINGS.to_string(),
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

    /// Whether they are the things a theorem's sets hold, or sets of them,
    /// so that its statement takes `{α : Type*}`.
    fn uses_things(&self) -> bool {
        match self {
            Members::Things => true,
            Members::Sets(m) => m.uses_things(),
            Members::Numbers(_) | Members::Elements(_) => false,
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

    /// Whether the type holds the things a theorem's sets are of, so that
    /// its statement takes `{α : Type*}`.
    pub fn uses_things(&self) -> bool {
        match self {
            LetterType::Set(m) | LetterType::Member(m) | LetterType::Property(m) => {
                m.uses_things()
            }
            LetterType::Map { from, to } => from.uses_things() || to.uses_things(),
            _ => false,
        }
    }
}

/// The type of each letter in scope, by its name.
pub type Letters = IndexMap<String, LetterType>;

/// Lean text, with the precedence of its outermost operator, so that a
/// term put in a hole is bracketed only where Lean would read it otherwise.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Printed {
    pub text: String,
    pub prec: u32,
}

/// The precedence of a term no operator can split: a letter, a numeral, a
/// bracketed term.
pub const MAX: u32 = 1024;
/// The precedence of a function applied to its arguments.
pub const APP: u32 = 1023;

impl Printed {
    pub fn atom(text: impl Into<String>) -> Printed {
        Printed {
            text: text.into(),
            prec: MAX,
        }
    }

    /// The text, bracketed unless it binds at least as tightly as `need`.
    pub fn at(&self, need: u32) -> String {
        if self.prec >= need {
            self.text.clone()
        } else {
            format!("({})", self.text)
        }
    }
}

/// Writes trees as Lean, with the letters in scope.
pub struct Writer<'a> {
    pub grammar: &'a Grammar,
    pub templates: &'a Templates,
    pub letters: Letters,
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
    /// The least type a relation between numbers is written in: ℤ, or ℝ
    /// inside a block that lets a real number, the ε of a limit, where a
    /// claim about natural numbers meets lines in ℝ (`Proof::open_lines`).
    pub floor: Num,
    /// Terms the theorem puts in a hole of type ℝ, A/B of ⌊A/B⌋, as the
    /// page prints them: each is computed in ℝ wherever it is written.
    pub reals: Vec<String>,
}

/// A sum read for writing: the writer its term is read with, where its index
/// is an integer, and its parts.
struct Summed<'a, 'n> {
    inner: Writer<'a>,
    index: &'n Node,
    from: &'n Node,
    to: &'n Node,
    term: &'n Node,
}

/// A term a line says is an integer or a rational: the term as the page
/// prints it, the line's Lean name, `∃ m : ℤ, (m : ℝ) = f a`, and the type
/// it says the term is in.
#[derive(Clone, Debug)]
pub struct SaidInteger {
    pub term: String,
    pub proof: String,
    pub ty: Num,
}

/// Whether the node is a sum or a product over a range, Σ(k = a to b) t or
/// ∏(k = a to b) t, which the writer reads alike; or one over a set that is
/// a range, ∏(k ∈ {1, …, n}) t, which is the same product.
fn is_big_operator(node: &Node) -> bool {
    matches!(
        node.notation(),
        crate::notations::SUM | crate::notations::PRODUCT
    ) || over_range(node).is_some()
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

    /// A term cast to a number type.
    fn cast(&self, text: &Printed, to: Num) -> Printed {
        Printed::atom(format!("({} : {})", text.text, self.type_name(to)))
    }

    /// A writer with the same grammar and notations, and these letters.
    /// A writer with no letters yet.
    pub fn new(grammar: &'a Grammar, templates: &'a Templates) -> Writer<'a> {
        Writer {
            grammar,
            templates,
            letters: IndexMap::new(),
            general: None,
            integers: Vec::new(),
            domains: IndexMap::new(),
            floor: Num::Int,
            reals: Vec::new(),
        }
    }

    pub fn with_letters(&self, letters: Letters) -> Writer<'a> {
        Writer {
            grammar: self.grammar,
            templates: self.templates,
            letters,
            general: self.general,
            integers: self.integers.clone(),
            domains: self.domains.clone(),
            floor: self.floor,
            reals: self.reals.clone(),
        }
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
}

/// How a template's text takes its holes: the precedence of the whole and
/// the least each hole needs.
struct Shape {
    prec: u32,
    needs: Vec<u32>,
}

/// Lean's infix operators: precedence and which side chains.
fn infix(op: &str) -> Option<(u32, Assoc)> {
    Some(match op {
        "↔" => (20, Assoc::Neither),
        "→" => (25, Assoc::Right),
        "∨" => (30, Assoc::Right),
        "∧" => (35, Assoc::Right),
        "=" | "≠" | "<" | ">" | "≤" | "≥" | "∣" | "∈" | "∉" | "⊆" | "⊂" | "≡" => {
            (50, Assoc::Neither)
        }
        "+" | "-" | "∪" => (65, Assoc::Left),
        "*" | "/" | "%" | "∩" | "\\" => (70, Assoc::Left),
        "^" => (75, Assoc::Right),
        "∘" => (90, Assoc::Right),
        _ => return None,
    })
}

#[derive(Clone, Copy)]
enum Assoc {
    Left,
    Right,
    Neither,
}

/// The shape of a template's text: an infix operator between two holes, a
/// prefix operator before one, or anything else, whose holes are each an
/// argument unless a bracket encloses it.
fn shape_of(text: &str, holes: usize) -> Shape {
    let words: Vec<&str> = text.split_whitespace().collect();
    if let ["_1", op, "_2"] = words.as_slice() {
        if let Some((p, assoc)) = infix(op) {
            let (left, right) = match assoc {
                Assoc::Left => (p, p + 1),
                Assoc::Right => (p + 1, p),
                Assoc::Neither => (p + 1, p + 1),
            };
            return Shape {
                prec: p,
                needs: vec![left, right],
            };
        }
    }
    if let ["¬", "_1"] = words.as_slice() {
        return Shape {
            prec: MAX,
            needs: vec![40],
        };
    }
    // A negation's argument is bracketed unless it is an atom, so that
    // −(−3) is never `--3`, which Lean reads as a comment.
    if let ["-_1"] | ["-", "_1"] = words.as_slice() {
        return Shape {
            prec: 75,
            needs: vec![76],
        };
    }
    let starts_binder = text.starts_with('∃') || text.starts_with('∀');
    let enclosed = |i: usize| {
        let mark = format!("_{}", i + 1);
        let Some(at) = text.find(&mark) else {
            return true;
        };
        let before = text[..at].chars().last();
        let after = text[at + mark.len()..].chars().next();
        matches!(before, Some('(' | '|' | '⌊' | '⌈' | '⟨' | '[' | '{' | ','))
            || matches!(after, Some(')' | '|' | '⌋' | '⌉' | '⟩' | ']' | '}' | ','))
            || (starts_binder && after.is_none())
    };
    let needs = (0..holes)
        .map(|i| if enclosed(i) { 0 } else { MAX })
        .collect();
    let prec = if starts_binder {
        0
    } else if words.len() == 1 {
        MAX
    } else {
        APP
    };
    Shape { prec, needs }
}

/// A template's text with each hole filled, bracketed as its shape needs.
fn fill(template: &Template, children: &[Printed]) -> Printed {
    let shape = shape_of(&template.text, children.len());
    let mut text = template.text.clone();
    // Highest hole first, so `_1` does not take the front of `_12`.
    for (i, child) in children.iter().enumerate().rev() {
        let mark = format!("_{}", i + 1);
        text = text.replace(&mark, &child.at(shape.needs[i]));
    }
    Printed {
        text,
        prec: shape.prec,
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

    /// `template`, where the node is computed in `at`: a library function
    /// takes the form for arguments of that type, so that cos(0) in a
    /// calculation in ℂ is `Complex.cos 0`, as cos(A) beside it is.
    fn template_at(&self, node: &Node, at: Num) -> Route<&Template> {
        let applied = matches!(
            node.notation(),
            crate::notations::APPLICATION | crate::notations::APPLICATION_TO_TWO
        ) && self.library_function(node).is_some();
        if !applied {
            return self.template(node);
        }
        let Some(f) = node.children.first() else {
            return self.template(node);
        };
        let args: Vec<Num> = node.children[1..]
            .iter()
            .filter_map(|a| self.carrier(a).built())
            .map(|c| c.max(at))
            .collect();
        match self.templates.function_at(&f.text, &args) {
            Some(t) => Route::Built(t),
            None => self.template(node),
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
        // types take: cos of a complex number is Complex.cos.
        let args: Vec<Num> = node.children[1..]
            .iter()
            .filter_map(|a| self.carrier(a).built())
            .collect();
        self.templates.function_at(&f.text, &args)
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
        if Writer::counts(node) {
            return false;
        }
        node.sort.is("number")
            || (node.is_name()
                && matches!(
                    self.letters.get(node.text.as_str()),
                    Some(LetterType::Number(_))
                ))
            // g⁻¹(y) and (g ∘ f)(x) of functions of numbers, whose sort the
            // checker leaves open.
            || (node.notation() == crate::notations::APPLICATION
                && node.children.first().is_some_and(|f| {
                    self.inverse_of_function(f).is_some()
                        || (&*f.notation_name() == "composition"
                            && self.function_type(f).built().is_some())
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
        if &*node.notation_name() == "series" {
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
                    Route::Built((_, to)) => Route::Built(to.max(Num::Int)),
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
    /// as Lean computes one: a negative or an integer letter. None for any
    /// other node.
    fn integer_power<'n>(&self, node: &'n Node) -> Option<&'n [Node; 2]> {
        if node.notation() != crate::notations::POWER {
            return None;
        }
        let parts: &[Node; 2] = node.children.as_slice().try_into().ok()?;
        (!self.natural(&parts[1])).then_some(parts)
    }

    /// The function letter an application applies, with the types it takes
    /// and gives.
    fn applied(&self, node: &Node) -> Route<(Num, Num)> {
        let Some(f) = node.children.first() else {
            return Route::no("an application of nothing");
        };
        self.function_type(f)
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
            _ if is_big_operator(node) || &*node.notation_name() == "series" => true,
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
        match node.notation() {
            NAME => matches!(
                self.letters.get(node.text.as_str()),
                Some(LetterType::Number(Num::Nat))
            ),
            NUMERAL => !node.text.contains('.'),
            crate::notations::APPLICATION if self.library_function(node).is_none() => {
                matches!(self.applied(node), Route::Built((_, Num::Nat)))
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
        let [index, from, to, term] = match (over_range(node), node.children.as_slice())
        {
            (Some(parts), _) => parts,
            (None, [index, from, to, term]) => [index, from, to, term],
            (None, _) => return Route::no("a sum of other than four parts"),
        };
        if !index.is_name() {
            return Route::no("a sum whose index is no letter");
        }
        let mut inner = self.with_letters(self.letters.clone());
        inner
            .letters
            .insert(index.text.to_string(), LetterType::Number(Num::Int));
        Route::Built(Summed {
            inner,
            index,
            from,
            to,
            term,
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
        let ends = (
            self.number_fixed(s.from, Num::Int),
            self.number_fixed(s.to, Num::Int),
        );
        let (from, to) = match ends {
            (Route::Built(f), Route::Built(t)) => (f, t),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        let term = match s.inner.number(s.term, at) {
            Route::Built(t) => t,
            Route::Declined(d) => return Route::Declined(d),
        };
        // The term is given its type: one built of numerals and naturals,
        // Σ(k = 1 to 3) 5 or 1/2^(j + 1), gives Lean nothing else to read
        // its type from, and Lean would take it in ℕ.
        let term = Printed::atom(format!("({} : {})", term.text, self.type_name(at)));
        // Mathlib reads the body at 67, so `∑ k ∈ s, k + 1` would be the
        // sum of k, plus 1; a body below that is bracketed.
        let symbol = if is_product(node) { "∏" } else { "∑" };
        Route::Built(Printed {
            text: format!(
                "{symbol} {} ∈ Finset.Icc {} {}, {}",
                super::names::letter(&s.index.text),
                from.at(MAX),
                to.at(MAX),
                term.at(67)
            ),
            prec: 10,
        })
    }

    /// Σ(k = a to ∞) t, the value of a series: the limit of its partial
    /// sums, `Filter.limUnder Filter.atTop (fun n : ℕ => ∑ k ∈ Finset.Icc a n, t)`,
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
        inner
            .letters
            .insert(index.text.to_string(), LetterType::Number(Num::Int));
        let (start, body) =
            match (self.number_fixed(from, Num::Int), inner.number(term, at)) {
                (Route::Built(s), Route::Built(b)) => (s, b),
                (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                    return Route::Declined(d)
                }
            };
        let body = Printed::atom(format!("({} : {})", body.text, self.type_name(at)));
        Route::Built(Printed {
            text: format!(
                "Filter.limUnder Filter.atTop (fun {upper} : ℕ => ∑ {} ∈ Finset.Icc {} ({upper} : ℤ), {})",
                super::names::letter(&index.text),
                start.at(MAX),
                body.at(67)
            ),
            prec: APP,
        })
    }

    /// x(n) → L as n → ∞: `Filter.Tendsto (fun n : ℕ => x n) Filter.atTop
    /// (nhds L)`, the letter running over the naturals and the term and its
    /// limit computed in the type that holds both. The page's ℕ starts at 1
    /// and Lean's at 0, which no limit sees.
    fn tends_to(&self, node: &Node) -> Route<Printed> {
        let [term, limit, letter] = node.children.as_slice() else {
            return Route::no("a limit of other than three parts");
        };
        if !letter.is_name() {
            return Route::no("a limit whose index is no letter");
        }
        let mut inner = self.with_letters(self.letters.clone());
        inner
            .letters
            .insert(letter.text.to_string(), LetterType::Number(Num::Nat));
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
        Route::Built(Printed {
            text: format!(
                "Filter.Tendsto (fun {} : ℕ => ({} : {})) Filter.atTop (nhds {})",
                super::names::letter(&letter.text),
                body.text,
                self.type_name(at),
                l.at(MAX)
            ),
            prec: 1000,
        })
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
        Route::Built(Printed {
            text: format!(
                "Filter.Tendsto {} (nhdsWithin {point} ({domain} \\ {{{point}}})) (nhds {})",
                super::names::letter(&f.text),
                l.at(MAX)
            ),
            prec: 1000,
        })
    }

    /// f is continuous on D: `ContinuousOn f D`, of a function into ℝ and a
    /// set of reals.
    fn continuous(&self, node: &Node) -> Route<Printed> {
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
            Route::Built(s) => Route::Built(Printed {
                text: format!(
                    "ContinuousOn {} {}",
                    super::names::letter(&f.text),
                    s.at(MAX)
                ),
                prec: 1000,
            }),
            Route::Declined(d) => Route::Declined(d),
        }
    }

    /// The node, a number, written as a Lean term of type `at`.
    pub fn number(&self, node: &Node, at: Num) -> Route<Printed> {
        if let Some(s) = self.said_integer(node) {
            let value = Printed::atom(format!("(Classical.choose {})", s.proof));
            return self.raise(value, s.ty, at);
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
            return Route::Built(Printed {
                text: format!("{} ^ {}", base.at(76), exponent.at(76)),
                prec: 75,
            });
        }
        if is_big_operator(node) {
            return self.sum(node, at);
        }
        if &*node.notation_name() == "series" {
            return self.series(node, at);
        }
        match node.notation() {
            NAME => match self.letters.get(node.text.as_str()) {
                Some(LetterType::Number(n)) if *n == at => {
                    Route::Built(Printed::atom(super::names::letter(&node.text)))
                }
                Some(LetterType::Number(n)) if *n < at => Route::Built(
                    self.cast(&Printed::atom(super::names::letter(&node.text)), at),
                ),
                Some(LetterType::Number(n)) => Route::no(format!(
                    "{} is in {}, which Lean would cast down to {}",
                    node.text,
                    n.lean(),
                    at.lean()
                )),
                _ => Route::no(format!("{} has no Lean number type", node.text)),
            },
            NUMERAL => Route::Built(Printed::atom(&*node.text)),
            crate::notations::APPLICATION if self.library_function(node).is_none() => {
                let (from, to) = match self.applied(node) {
                    Route::Built(t) => t,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let Some(arg) = node.children.get(1) else {
                    return Route::no("an application with no argument");
                };
                let arg = match self.number(arg, from) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let value = Printed {
                    text: format!(
                        "{} {}",
                        self.function_text(&node.children[0]),
                        arg.at(MAX)
                    ),
                    prec: APP,
                };
                self.raise(value, to, at)
            }
            _ => {
                let template = match self.template_at(node, at) {
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
                self.raise(fill(template, &children), here, at)
            }
        }
    }

    /// A value of type `own` as a term of type `at`: itself, or cast up.
    fn raise(&self, value: Printed, own: Num, at: Num) -> Route<Printed> {
        if own == at {
            Route::Built(value)
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
        let mut out = Vec::new();
        for (child, slot) in args.iter().zip(&template.holes) {
            let printed = match slot {
                Slot::Alpha(_) if told => {
                    self.number(child, alpha).map(|p| self.cast(&p, alpha))
                }
                Slot::Alpha(_) => self.number(child, alpha),
                Slot::Fixed(n) => self.number_fixed(child, *n),
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
            return Route::Built(Printed::atom(super::names::letter(&node.text)));
        }
        // not (a = b) between numbers is written a ≠ b, as Mathlib writes it.
        if let ([inner], LOGICAL_NOT) = (node.children.as_slice(), node.notation()) {
            if inner.notation() == EQUALITY
                && inner.children.iter().all(|c| self.is_number(c))
            {
                return self.relation(inner, true);
            }
        }
        if &*node.notation_name() == "tends-to" {
            return self.tends_to(node);
        }
        if &*node.notation_name() == "function-limit" {
            return self.function_limit(node);
        }
        if &*node.notation_name() == "continuous" {
            return self.continuous(node);
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
                true => Route::Built(Printed::atom("True")),
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
            return self.element_term(t, members).map(|t| Printed {
                text: format!("{} {}", super::names::letter(&p.text), t.at(MAX)),
                prec: 1023,
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
            return self.set_term(set).map(|s| Printed {
                text: format!(
                    "∃ {} ∈ {}, True",
                    super::names::letter(&letter.text),
                    s.at(51)
                ),
                prec: 0,
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
                        (Route::Built(a), Route::Built(b)) => Route::Built(Printed {
                            text: format!(
                                "Set.MapsTo {} {} {}",
                                self.function_text(f),
                                a.at(MAX),
                                b.at(MAX)
                            ),
                            prec: APP,
                        }),
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
                        Route::Built(Printed::atom("True"))
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
                for c in &node.children {
                    match self.formula(c) {
                        Route::Built(p) => parts.push(p.at(36)),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                Route::Built(Printed {
                    text: parts.join(" ∧ "),
                    prec: 35,
                })
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
                    Route::Built(children) => Route::Built(fill(template, &children)),
                    Route::Declined(d) => Route::Declined(d),
                }
            }
        }
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
        self.relation_from(node, negated, self.floor)
    }

    /// A relation of numerals alone, `5 = 0`, written in the type `floor`
    /// at least: the type of the lines it is reached from.
    pub fn closed_formula(&self, node: &Node, floor: Num) -> Route<Printed> {
        // A count, |∅| = 0, is in ℕ∞ whatever the lines around it.
        if Writer::counts(node) {
            return self.formula(node);
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
        Route::Built(Printed {
            text: format!("{} {op} {}", l.at(51), r.at(51)),
            prec: 50,
        })
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
                    Route::Built(p) => members.push(p.text),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            let x = match self.number_fixed(x, at) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            return Route::Built(Printed {
                text: format!(
                    "{} ∈ ({{{}}} : Set {})",
                    x.at(51),
                    members.join(", "),
                    self.type_name(at)
                ),
                prec: 50,
            });
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
                return Route::Built(Printed {
                    text: format!(
                        "{} ≤ {} ∧ {} ≤ {}",
                        out[0].at(51),
                        out[1].at(51),
                        out[1].at(51),
                        out[2].at(51)
                    ),
                    prec: 35,
                });
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
            return Route::Built(Printed {
                text: format!(
                    "{} ∈ Finset.Icc {} {}",
                    out[0].at(51),
                    out[1].at(MAX),
                    out[2].at(MAX)
                ),
                prec: 50,
            });
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
                Route::Built(Printed {
                    text: format!("{zero} < {}", x.at(51)),
                    prec: 50,
                })
            }
            System::NonNegative if held <= Num::Int => {
                if natural_letter {
                    return Route::Built(Printed::atom("True"));
                }
                let zero = self.zero_at(x, Num::Int);
                let x = match self.number(x, Num::Int) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                Route::Built(Printed {
                    text: format!("{zero} ≤ {}", x.at(51)),
                    prec: 50,
                })
            }
            System::Type(n) if held <= n => Route::Built(Printed::atom("True")),
            System::Type(n) => {
                let x = match self.number(x, own) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                Route::Built(Printed {
                    text: format!(
                        "∃ m : {}, (m : {}) = {}",
                        self.type_name(n),
                        self.type_name(own),
                        x.at(51)
                    ),
                    prec: 0,
                })
            }
            System::Positive | System::NonNegative => {
                let x = match self.number(x, own) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let positive = if system == System::Positive {
                    "0 < m ∧ "
                } else {
                    ""
                };
                Route::Built(Printed {
                    text: format!(
                        "∃ m : ℕ, {positive}(m : {}) = {}",
                        self.type_name(own),
                        x.at(51)
                    ),
                    prec: 0,
                })
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
        let name = super::names::letter(&letter.text);
        let (ty, guard) = if set.notation() == NUMBER_SYSTEMS {
            match system_of(set) {
                Some(System::Type(n)) => (n, None),
                Some(System::Positive) => (Num::Nat, Some(format!("0 < {name}"))),
                Some(System::NonNegative) => (Num::Nat, None),
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
                Num::Int,
                Some(format!(
                    "{name} ∈ Finset.Icc {} {}",
                    from.at(MAX),
                    to.at(MAX)
                )),
            )
        } else {
            return Route::no(format!("a quantifier over {}", set.notation_name()));
        };
        let mut inner = self.with_letters(self.letters.clone());
        inner
            .letters
            .insert(letter.text.to_string(), LetterType::Number(ty));
        let body = match inner.formula(body) {
            Route::Built(b) => b,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A body the letter's type already makes true says nothing.
        if body.text == "True" {
            return Route::Built(Printed::atom("True"));
        }
        let ty = self.type_name(ty);
        let text = match (exists, guard) {
            (true, None) => format!("∃ {name} : {ty}, {}", body.text),
            (true, Some(g)) => format!("∃ {name} : {ty}, {g} ∧ {}", body.at(36)),
            (false, None) => format!("∀ {name} : {ty}, {}", body.text),
            (false, Some(g)) => format!("∀ {name} : {ty}, {g} → {}", body.at(25)),
        };
        Route::Built(Printed { text, prec: 0 })
    }
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

/// The Lean type a letter introduced in a number system takes.
pub fn letter_type(system: System) -> Num {
    match system {
        System::Positive | System::NonNegative => Num::Nat,
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
        let minus = Template {
            holes: vec![Slot::Alpha(Num::Int), Slot::Alpha(Num::Int)],
            yields: Slot::Alpha(Num::Int),
            text: "_1 - _2".to_string(),
        };
        let sum = Printed {
            text: "a + b".to_string(),
            prec: 65,
        };
        // a + b − (a + b): the right side of a left-chaining operator is
        // bracketed at its own level, the left is not.
        let out = fill(&minus, &[sum.clone(), sum]);
        assert_eq!(out.text, "a + b - (a + b)");
    }

    #[test]
    fn an_argument_is_bracketed_unless_a_bracket_encloses_it() {
        let factorial = Template {
            holes: vec![Slot::Fixed(Num::Nat)],
            yields: Slot::Fixed(Num::Nat),
            text: "Nat.factorial _1".to_string(),
        };
        let n1 = Printed {
            text: "n + 1".to_string(),
            prec: 65,
        };
        assert_eq!(
            fill(&factorial, std::slice::from_ref(&n1)).text,
            "Nat.factorial (n + 1)"
        );
        let abs = Template {
            holes: vec![Slot::Alpha(Num::Int)],
            yields: Slot::Alpha(Num::Int),
            text: "|_1|".to_string(),
        };
        assert_eq!(fill(&abs, &[n1]).text, "|n + 1|");
    }
}
