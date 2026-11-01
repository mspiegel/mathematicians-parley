//! What a theorem or an item asks for, as Lean binders.
//!
//! A `let` that puts a letter in a number system makes the letter a binder
//! of that type; the page's ℕ, which starts at 1, adds the hypothesis that
//! the letter is above 0. Every other fact asked for is a hypothesis. The
//! same reading serves a theorem's own statement and a citation of it, so
//! the two agree on the order of what is asked.

use super::expr::{letter_type, system_of, LetterType, Printed, System, Writer};
use crate::formula::Node;
use crate::notations::{IN, NUMBER_SYSTEMS};
use crate::outcome::Route;

/// One binder of a statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Binder {
    /// A letter of a type: its Lean name, and the letter as the page
    /// writes it, which a citation's values are given by.
    Letter {
        name: String,
        page: String,
        ty: LetterType,
        /// Whether its type is an item's general one, `K`, which a
        /// citation fills with the citing claim's type.
        general: bool,
    },
    /// A hypothesis, by its name, and what it says.
    Fact { name: String, says: String },
}

impl Binder {
    pub fn lean(&self) -> String {
        match self {
            Binder::Letter {
                name,
                general: true,
                ..
            } => format!("({name} : {})", super::expr::GENERAL),
            Binder::Letter { name, ty, .. } => format!("({name} : {})", ty.lean()),
            Binder::Fact { name, says } => format!("({name} : {says})"),
        }
    }
}

/// A fact a statement asks for, with the name its proof calls it by.
pub struct Asked<'n> {
    pub node: &'n Node,
    pub name: String,
}

/// The letter and system a fact `x ∈ S` introduces, S a number system;
/// None for any other fact.
pub fn introduces(node: &Node) -> Option<(String, System)> {
    let [x, set] = node.children.as_slice() else {
        return None;
    };
    if node.spelling() != IN || !x.is_name() || set.notation() != NUMBER_SYSTEMS {
        return None;
    }
    Some((x.text.to_string(), system_of(set)?))
}

/// The letter a fact `f : A → B` introduces, a function between number
/// systems, with its Lean type; None for any other fact.
pub fn introduces_function(node: &Node) -> Option<(String, LetterType)> {
    let [f, from, to] = node.children.as_slice() else {
        return None;
    };
    if node.notation() != crate::notations::FUNCTION_TYPE || !f.is_name() {
        return None;
    }
    let (from, to) = super::expr::function_systems(from, to)?;
    Some((f.text.to_string(), LetterType::Function { from, to }))
}

/// The letter a fact `k ∈ {a, …, b}` introduces, an integer between the
/// range's ends; None for any other fact.
pub fn range_letter(node: &Node) -> Option<String> {
    let [x, set] = node.children.as_slice() else {
        return None;
    };
    let fits = node.spelling() == IN
        && x.is_name()
        && set.notation() == crate::notations::INTEGER_RANGE;
    fits.then(|| x.text.to_string())
}

/// The binders of the facts asked, in order, each letter added to the
/// writer's letters as it is introduced, so a later fact reads it.
pub fn binders(writer: &mut Writer, asked: &[Asked]) -> Route<Vec<Binder>> {
    let mut out = Vec::new();
    for a in asked {
        // A letter of a range is an integer, and the range a fact about it.
        if let Some(letter) = range_letter(a.node) {
            let ty = LetterType::Number(super::templates::Num::Int);
            writer.letters.insert(letter.clone(), ty.clone());
            out.push(Binder::Letter {
                name: super::names::letter(&letter),
                page: letter,
                general: false,
                ty,
            });
        }
        if let Some((letter, ty)) = introduces_function(a.node) {
            writer.letters.insert(letter.clone(), ty.clone());
            out.push(Binder::Letter {
                name: super::names::letter(&letter),
                page: letter,
                general: false,
                ty,
            });
            continue;
        }
        if let Some((letter, system)) = introduces(a.node) {
            let ty = LetterType::Number(letter_type(system));
            writer.letters.insert(letter.clone(), ty.clone());
            let name = super::names::letter(&letter);
            out.push(Binder::Letter {
                name: name.clone(),
                page: letter.clone(),
                general: writer.general == Some(letter_type(system)),
                ty,
            });
            if system == System::Positive {
                out.push(Binder::Fact {
                    name: a.name.clone(),
                    says: format!("0 < {name}"),
                });
            }
            continue;
        }
        let says: Printed = match writer.formula(a.node) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        out.push(Binder::Fact {
            name: a.name.clone(),
            says: says.text,
        });
        // A term of a wider type said to be an integer is, in what is
        // asked after, the integer this hypothesis gives.
        if let [term, set] = a.node.children.as_slice() {
            let integer = a.node.notation() == crate::notations::MEMBERSHIP
                && system_of(set) == Some(System::Type(super::templates::Num::Int))
                && writer
                    .carrier(term)
                    .built()
                    .is_some_and(|c| c > super::templates::Num::Int);
            if integer {
                writer.integers.push(super::expr::SaidInteger {
                    term: writer.grammar.print(term),
                    proof: a.name.clone(),
                });
            }
        }
    }
    Route::Built(out)
}
