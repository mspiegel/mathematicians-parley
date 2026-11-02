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
    /// Its Lean name.
    pub fn name(&self) -> &str {
        match self {
            Binder::Letter { name, .. } | Binder::Fact { name, .. } => name,
        }
    }

    pub fn lean(&self) -> String {
        match self {
            Binder::Letter {
                name,
                ty: LetterType::Function { from, .. },
                general: true,
                ..
            } => format!("({name} : {} → {})", from.lean(), super::expr::GENERAL),
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

/// A letter a line introduces in or under a set, or as a map between sets.
struct InSet {
    letter: String,
    ty: LetterType,
    /// The fact a map's line says, `Set.MapsTo f A B`; None where the line
    /// itself is the fact.
    fact: Option<String>,
    /// A map's domain as Lean writes it, the A of `f : A → B`.
    domain: Option<String>,
}

/// The letter a line introduces in or under a set the writer has a type
/// for, or as a map between such sets. None for any other line, and for a
/// letter already typed.
fn introduces_in_set(writer: &Writer, node: &Node) -> Option<InSet> {
    let [letter, rest @ ..] = node.children.as_slice() else {
        return None;
    };
    if !letter.is_name() || writer.letters.contains_key(letter.text.as_str()) {
        return None;
    }
    match (node.notation_name().as_ref(), rest) {
        // x ∈ {1, 2} of numbers: a number of the type that holds them all.
        ("membership", [set])
            if matches!(
                set.notation_name().as_ref(),
                "singleton" | "listed-two" | "listed-three" | "listed-four"
            ) && set.children.iter().all(|c| writer.is_number(c)) =>
        {
            let mut at = super::templates::Num::Int;
            for c in &set.children {
                at = at.max(writer.carrier(c).built()?);
            }
            Some(InSet {
                letter: letter.text.to_string(),
                ty: LetterType::Number(at),
                fact: None,
                domain: None,
            })
        }
        ("membership", [set]) => Some(InSet {
            letter: letter.text.to_string(),
            ty: writer.members_of(set)?.letter(),
            fact: None,
            domain: None,
        }),
        ("subset", [set]) => Some(InSet {
            letter: letter.text.to_string(),
            ty: LetterType::Set(writer.set_members(set)?),
            fact: None,
            domain: None,
        }),
        // f : A → B, alone or one-to-one, onto, or both: a map, and the
        // fact of it, which is the line itself where it says more than the
        // type.
        (
            kind @ ("function-type" | "one-to-one" | "onto" | "one-to-one-onto"),
            [from, to],
        ) => {
            let (a, b) = (writer.members_of(from)?, writer.members_of(to)?);
            let (from_text, to_text) =
                (writer.set_term(from).built()?, writer.set_term(to).built()?);
            let lean = super::names::letter(&letter.text);
            let domain = from_text.at(super::expr::MAX);
            Some(InSet {
                letter: letter.text.to_string(),
                ty: LetterType::Map { from: a, to: b },
                fact: (kind == "function-type").then(|| {
                    format!(
                        "Set.MapsTo {lean} {domain} {}",
                        to_text.at(super::expr::MAX)
                    )
                }),
                domain: Some(domain),
            })
        }
        _ => None,
    }
}

/// `{α : Type*}`, where a binder is a set of things, a member of one or a
/// map between sets; None where none is.
pub fn things_binder(binders: &[Binder]) -> Option<String> {
    binders
        .iter()
        .any(|b| matches!(b, Binder::Letter { ty, .. } if ty.uses_things()))
        .then(|| format!("{{{} : Type*}}", super::expr::THINGS))
}

/// Where a line says what sets a map letter maps between, `f : A → B` or
/// `f : A → B is one-to-one`, the A it maps from is its domain, though the
/// letter's type came first, from its sort.
fn record_domain(writer: &mut Writer, node: &Node) {
    let kinds = ["function-type", "one-to-one", "onto", "one-to-one-onto"];
    let [f, from, _] = node.children.as_slice() else {
        return;
    };
    let map = matches!(
        writer.letters.get(f.text.as_str()),
        Some(LetterType::Map { .. })
    );
    if !map || !kinds.contains(&&*node.notation_name()) {
        return;
    }
    if let Route::Built(d) = writer.set_term(from) {
        writer
            .domains
            .insert(f.text.to_string(), d.at(super::expr::MAX));
    }
}

pub fn binders(writer: &mut Writer, asked: &[Asked]) -> Route<Vec<Binder>> {
    let mut out = Vec::new();
    for a in asked {
        record_domain(writer, a.node);
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
        // A letter a line puts in a set or under one, `x ∈ A` or `X ⊆ A`,
        // or a map between sets, `f : A → B`: the letter, of its type, and
        // the line a fact about it, the map's `Set.MapsTo f A B`.
        if let Some(InSet {
            letter,
            ty,
            fact,
            domain,
        }) = introduces_in_set(writer, a.node)
        {
            writer.letters.insert(letter.clone(), ty.clone());
            if let Some(d) = domain {
                writer.domains.insert(letter.clone(), d);
            }
            out.push(Binder::Letter {
                name: super::names::letter(&letter),
                page: letter,
                general: false,
                ty,
            });
            let says = match fact {
                Some(f) => f,
                None => match writer.formula(a.node) {
                    Route::Built(p) => p.text,
                    Route::Declined(d) => return Route::Declined(d),
                },
            };
            out.push(Binder::Fact {
                name: a.name.clone(),
                says,
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
