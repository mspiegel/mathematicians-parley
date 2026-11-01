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
}

impl LetterType {
    /// How Lean writes the type.
    pub fn lean(&self) -> String {
        match self {
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

/// A Lean number type written as a cast target.
fn cast(text: &Printed, to: Num) -> Printed {
    Printed::atom(format!("({} : {})", text.text, to.lean()))
}

impl Writer<'_> {
    /// The template the node's notation and pattern have in Lean, or a
    /// decline naming the notation.
    pub fn template(&self, node: &Node) -> Route<&Template> {
        let name = node.notation_name();
        let Some(pattern) = self.grammar.written_by(node.spelling()) else {
            return Route::no(format!("{name} is written by no plain pattern"));
        };
        match self.templates.get(&name, &pattern.pattern) {
            Some(t) => Route::Built(t),
            None => Route::no(format!("notation {name} has no lean field")),
        }
    }

    /// Whether the node is a number.
    pub fn is_number(&self, node: &Node) -> bool {
        node.sort.is("number")
    }

    /// The least number type that holds the node, ℤ at least: the type a
    /// formula made of it alone is computed in.
    pub fn carrier(&self, node: &Node) -> Route<Num> {
        match node.notation() {
            NAME => match self.letters.get(node.text.as_str()) {
                Some(LetterType::Number(n)) => Route::Built((*n).max(Num::Int)),
                Some(LetterType::Function { .. }) => {
                    Route::no(format!("{} is a function, not a number", node.text))
                }
                None => Route::no(format!("{} has no Lean type", node.text)),
            },
            NUMERAL => Route::Built(if node.text.contains('.') {
                Num::Rat
            } else {
                Num::Int
            }),
            crate::notations::APPLICATION => match self.applied(node) {
                Route::Built((_, to)) => Route::Built(to.max(Num::Int)),
                Route::Declined(d) => Route::Declined(d),
            },
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
                        for (child, slot) in node.children.iter().zip(&template.holes) {
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

    /// The function letter an application applies, with the types it takes
    /// and gives.
    fn applied(&self, node: &Node) -> Route<(Num, Num)> {
        let Some(f) = node.children.first().filter(|f| f.is_name()) else {
            return Route::no("a function that is no letter is applied");
        };
        match self.letters.get(f.text.as_str()) {
            Some(LetterType::Function { from, to }) => Route::Built((*from, *to)),
            _ => Route::no(format!("{} has no Lean function type", f.text)),
        }
    }

    /// Whether some part of the node fixes the type Lean computes it in: a
    /// letter, a function's value, or an operation of a fixed type. A
    /// formula of numerals alone is computed in ℕ unless told otherwise.
    fn pinned(&self, node: &Node) -> bool {
        match node.notation() {
            NAME => true,
            NUMERAL => false,
            crate::notations::APPLICATION => true,
            _ => match self.template(node) {
                Route::Built(t) => match t.yields {
                    Slot::Alpha(_) => node
                        .children
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
            crate::notations::APPLICATION => {
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
                            && node.children.iter().zip(&t.holes).all(|(c, s)| {
                                !matches!(s, Slot::Alpha(_)) || self.natural(c)
                            })
                    }
                    _ => false,
                }
            }
        }
    }

    /// The node, a number, written as a Lean term of type `at`.
    pub fn number(&self, node: &Node, at: Num) -> Route<Printed> {
        if at == Num::Nat && !self.natural(node) {
            return Route::no(format!(
                "{} would be computed in ℕ, where subtraction stops at 0",
                self.grammar.print(node)
            ));
        }
        match node.notation() {
            NAME => match self.letters.get(node.text.as_str()) {
                Some(LetterType::Number(n)) if *n == at => {
                    Route::Built(Printed::atom(super::names::letter(&node.text)))
                }
                Some(LetterType::Number(n)) if *n < at => Route::Built(cast(
                    &Printed::atom(super::names::letter(&node.text)),
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
            NUMERAL => Route::Built(Printed::atom(&*node.text)),
            crate::notations::APPLICATION => {
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
                        super::names::letter(&node.children[0].text),
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
            Route::Built(cast(&value, at))
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
        if node.children.len() != template.holes.len() {
            return Route::no(format!(
                "{} has {} parts and its lean template {} holes",
                node.notation_name(),
                node.children.len(),
                template.holes.len()
            ));
        }
        let mut out = Vec::new();
        for (child, slot) in node.children.iter().zip(&template.holes) {
            let printed = match slot {
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
            Route::Built(cast(&printed, n))
        }
    }

    /// The node, a formula, written as a Lean proposition.
    pub fn formula(&self, node: &Node) -> Route<Printed> {
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
        for (child, slot) in node.children.iter().zip(&template.holes) {
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
            (Route::Built(a), Route::Built(b)) => a.max(b),
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
            l = cast(&l, at);
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
            let parts = [
                self.number(x, Num::Int),
                self.number(from, Num::Int),
                self.number(to, Num::Int),
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
                        n.lean(),
                        own.lean(),
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
                        own.lean(),
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
        let mut inner = Writer {
            grammar: self.grammar,
            templates: self.templates,
            letters: self.letters.clone(),
        };
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
        let ty = ty.lean();
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
