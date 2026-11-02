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
    EQUALITY, EQUALS, FOR_ALL, INTEGER_RANGE, LOGICAL_NOT, MEMBERSHIP, NAME, NATURALS,
    NATURALS0, NUMBER_SYSTEMS, NUMERAL, ORDER, THERE_IS,
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
const APP: u32 = 1023;

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

/// A term a hypothesis says is an integer: the term as the page prints it,
/// and the hypothesis's Lean name, `∃ m : ℤ, (m : ℝ) = f a`.
#[derive(Clone, Debug)]
pub struct SaidInteger {
    pub term: String,
    pub proof: String,
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
    pub fn with_letters(&self, letters: Letters) -> Writer<'a> {
        Writer {
            grammar: self.grammar,
            templates: self.templates,
            letters,
            general: self.general,
            integers: self.integers.clone(),
        }
    }

    /// The hypothesis that says this term is an integer; None where none
    /// does.
    fn said_integer(&self, node: &Node) -> Option<&str> {
        if node.is_name() || node.notation() == NUMERAL {
            return None;
        }
        let printed = self.grammar.print(node);
        self.integers
            .iter()
            .find(|s| s.term == printed)
            .map(|s| s.proof.as_str())
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
        match self.templates.get(&name, &pattern.pattern) {
            Some(t) => Route::Built(t),
            None => Route::no(format!("notation {name} has no lean-builds field")),
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
        self.templates.function(&f.text)
    }

    /// What a node's template fills its holes with: its children, or for a
    /// library function applied, what it is applied to.
    fn args<'n>(&self, node: &'n Node) -> &'n [Node] {
        if self.library_function(node).is_some() {
            &node.children[1..]
        } else {
            &node.children
        }
    }

    /// Whether the node is a number.
    pub fn is_number(&self, node: &Node) -> bool {
        node.sort.is("number")
    }

    /// The least number type that holds the node, ℤ at least: the type a
    /// formula made of it alone is computed in.
    pub fn carrier(&self, node: &Node) -> Route<Num> {
        // A term a hypothesis says is an integer is the integer it gives.
        if self.said_integer(node).is_some() {
            return Route::Built(Num::Int);
        }
        // A power to an exponent that is no natural number is taken in a
        // field, where Lean's integer power is what the page means.
        if let Some([base, _]) = self.integer_power(node) {
            return match self.carrier(base) {
                Route::Built(n) => Route::Built(n.max(Num::Rat)),
                declined => declined,
            };
        }
        // A sum is computed in its terms' type, its index an integer.
        if node.notation() == crate::notations::SUM {
            return match self.summed(node) {
                Route::Built(s) => s.inner.carrier(s.term),
                Route::Declined(d) => Route::Declined(d),
            };
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

    /// A function as a printed term, a citation's value.
    pub fn function_printed(&self, f: &Node) -> Printed {
        Printed::atom(self.function_text(f))
    }

    /// A function as Lean writes it: a letter, or `(g ∘ f)`.
    fn function_text(&self, f: &Node) -> String {
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
            crate::notations::SUM => true,
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
    fn natural(&self, node: &Node) -> bool {
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
        let [index, from, to, term] = node.children.as_slice() else {
            return Route::no("a sum of other than four parts");
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

    /// Σ(k = a to b) t, `∑ k ∈ Finset.Icc a b, t`, its index ranging over
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
        // Mathlib reads the body at 67, so `∑ k ∈ s, k + 1` would be the
        // sum of k, plus 1; a body below that is bracketed.
        Route::Built(Printed {
            text: format!(
                "∑ {} ∈ Finset.Icc {} {}, {}",
                super::names::letter(&s.index.text),
                from.at(MAX),
                to.at(MAX),
                term.at(67)
            ),
            prec: 10,
        })
    }

    /// The node, a number, written as a Lean term of type `at`.
    pub fn number(&self, node: &Node, at: Num) -> Route<Printed> {
        if let Some(proof) = self.said_integer(node) {
            let value = Printed::atom(format!("(Classical.choose {proof})"));
            return self.raise(value, Num::Int, at);
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
            return Route::Built(Printed {
                text: format!("{} ^ {}", base.at(76), exponent.at(75)),
                prec: 75,
            });
        }
        if node.notation() == crate::notations::SUM {
            return self.sum(node, at);
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
        match node.notation() {
            EQUALITY | ORDER if node.children.len() == 2 => self.relation(node, false),
            MEMBERSHIP => self.membership(node),
            // f : A → B, which Lean's types give where f takes and gives
            // those.
            crate::notations::FUNCTION_TYPE => {
                let [f, from, to] = node.children.as_slice() else {
                    return Route::no("a function type of other than three parts");
                };
                let Some((takes, gives)) = function_systems(from, to) else {
                    return Route::no(
                        "a function type between sets that are no number system",
                    );
                };
                match self.function_type(f) {
                    Route::Built(t) if t == (takes, gives) => {
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
        self.relation_from(node, negated, Num::Int)
    }

    /// A relation of numerals alone, `5 = 0`, written in the type `floor`
    /// at least: the type of the lines it is reached from.
    pub fn closed_formula(&self, node: &Node, floor: Num) -> Route<Printed> {
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
        if set.notation() == NUMBER_SYSTEMS {
            return self.in_system(x, set);
        }
        if set.notation() == INTEGER_RANGE {
            let [from, to] = set.children.as_slice() else {
                return Route::no("a range of other than two ends");
            };
            // A range whose ends are no integers as Lean computes them, 6/3,
            // is said by the order of its member between them, in the type
            // that holds all three.
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
                let x = match self.number(x, at) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                Route::Built(Printed {
                    text: format!("0 < {}", x.at(51)),
                    prec: 50,
                })
            }
            System::NonNegative if held <= Num::Int => {
                if natural_letter {
                    return Route::Built(Printed::atom("True"));
                }
                let x = match self.number(x, Num::Int) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                Route::Built(Printed {
                    text: format!("0 ≤ {}", x.at(51)),
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
