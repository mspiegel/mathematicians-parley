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
#[derive(Clone, Debug)]
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
    Fact {
        name: String,
        says: Printed,
        /// The line it is as the checker read it, where one is: what a
        /// citation compares the lines it cites with, to name the one that
        /// says it (`Proof::instance`).
        line: Option<Node>,
    },
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
            // A map of things into the general type's numbers, `α → K`.
            Binder::Letter {
                name,
                ty: LetterType::Map { from, .. },
                general: true,
                ..
            } => format!(
                "({name} : {} → {})",
                super::expr::bracketed(&from.lean()),
                super::expr::GENERAL
            ),
            // A set of the general type's numbers, `Set K`.
            Binder::Letter {
                name,
                ty: LetterType::Set(super::expr::Members::Numbers(_)),
                general: true,
                ..
            } => format!("({name} : Set {})", super::expr::GENERAL),
            Binder::Letter {
                name,
                general: true,
                ..
            } => format!("({name} : {})", super::expr::GENERAL),
            // A group is the type of its elements, with Mathlib's group on
            // it: the page's operation is `*`, its identity `1`.
            Binder::Letter {
                name,
                ty: LetterType::Group,
                ..
            } => format!("{{{name} : Type*}} [Group {name}]"),
            Binder::Letter { name, ty, .. } => format!("({name} : {})", ty.lean()),
            Binder::Fact { name, says, .. } => format!("({name} : {})", says.text()),
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

/// The letter a fact `p is a polynomial` introduces, a function from ℂ to
/// ℂ; None for any other fact. The page's words are read as the membership
/// p ∈ (the polynomials), or as the notation itself.
pub fn introduces_polynomial(node: &Node) -> Option<String> {
    match (&*node.notation_name(), node.children.as_slice()) {
        ("is-a-polynomial", [p]) if p.is_name() => Some(p.text.to_string()),
        ("membership", [p, set])
            if p.is_name() && &*set.notation_name() == "polynomials" =>
        {
            Some(p.text.to_string())
        }
        _ => None,
    }
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
    fact: Fact,
    /// A map's domain, the A of `f : A → B`.
    domain: Option<super::expr::Printed>,
}

/// What a line that introduces a letter says of it beside its type.
enum Fact {
    /// The line itself, `x ∈ A`.
    Line,
    /// This, which Lean's type does not give: a map's `Set.MapsTo f A B`.
    Said(Printed),
}

/// The letter a line introduces in or under a set the writer has a type
/// for, or as a map between such sets. None for any other line, and for a
/// letter already typed.
fn introduces_in_set(writer: &Writer, node: &Node) -> Option<InSet> {
    // v ∉ W, read as not (v ∈ W): v is a member of what W holds, and the
    // line, `¬ v ∈ W`, a fact about it.
    if let ([inner], crate::notations::LOGICAL_NOT) =
        (node.children.as_slice(), node.notation())
    {
        if let ([v, set], crate::notations::MEMBERSHIP) =
            (inner.children.as_slice(), inner.notation())
        {
            if v.is_name() && !writer.letters.contains_key(v.text.as_str()) {
                return Some(InSet {
                    letter: v.text.to_string(),
                    ty: writer.members_of(set)?.letter(),
                    fact: Fact::Line,
                    domain: None,
                });
            }
        }
    }
    let [letter, rest @ ..] = node.children.as_slice() else {
        return None;
    };
    if !letter.is_name() || writer.letters.contains_key(letter.text.as_str()) {
        return None;
    }
    // p is a polynomial: a function from ℂ to ℂ, and the line that it is
    // one of set.mm's polynomials (`sets::polynomial_claim`). Ahead of the
    // memberships below, as the page's words read as p ∈ (the polynomials).
    if introduces_polynomial(node).is_some() {
        return Some(InSet {
            letter: letter.text.to_string(),
            ty: LetterType::Function {
                from: super::templates::Num::Complex,
                to: super::templates::Num::Complex,
            },
            fact: Fact::Line,
            domain: None,
        });
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
                fact: Fact::Line,
                domain: None,
            })
        }
        // D ∈ 𝒫ℝ, the page's `let D ⊆ ℝ`, is a set as of `D ⊆ ℝ`.
        ("membership", [set]) if &*set.notation_name() == "powerset" => Some(InSet {
            letter: letter.text.to_string(),
            ty: LetterType::Set(writer.set_members(set.children.first()?)?),
            fact: Fact::Line,
            domain: None,
        }),
        ("membership", [set]) => Some(InSet {
            letter: letter.text.to_string(),
            ty: writer.members_of(set)?.letter(),
            fact: Fact::Line,
            domain: None,
        }),
        ("subset", [set]) => Some(InSet {
            letter: letter.text.to_string(),
            ty: LetterType::Set(writer.set_members(set)?),
            fact: Fact::Line,
            domain: None,
        }),
        // H is a subgroup of G: Lean's `Subgroup G`, whose type says it, so
        // that the line's own hypothesis is `True` (`sets::subgroup_claim`).
        ("subgroup", [group])
            if matches!(
                writer.letters.get(group.text.as_str()),
                Some(LetterType::Group)
            ) =>
        {
            Some(InSet {
                letter: letter.text.to_string(),
                ty: LetterType::Subgroup(group.text.to_string()),
                fact: Fact::Line,
                domain: None,
            })
        }
        // f : A → B, alone or one-to-one, onto, or both: a map, and the
        // fact of it, which is the line itself where it says more than the
        // type.
        (
            kind @ ("function-type" | "one-to-one" | "onto" | "one-to-one-onto"),
            [from, to],
        ) => {
            // ∅ holds nothing of any type, so a map into it gives the
            // domain's.
            let a = writer.set_members(from)?;
            let b = match &*to.notation_name() {
                "empty-set" => a.clone(),
                _ => writer.set_members(to)?,
            };
            let (from_text, to_text) =
                (writer.set_term(from).built()?, writer.set_term(to).built()?);
            let lean = super::names::letter(&letter.text);
            // Between sets of numbers, f : ℝ ∖ {2} → ℝ, a function of the
            // numbers' types, so that f(x) is a number; between sets of
            // things, a map α → α.
            let ty = match (&a, &b) {
                (
                    super::expr::Members::Numbers(from),
                    super::expr::Members::Numbers(to),
                ) => LetterType::Function {
                    from: *from,
                    to: *to,
                },
                _ => LetterType::Map { from: a, to: b },
            };
            let map_type = ty.lean_type();
            Some(InSet {
                letter: letter.text.to_string(),
                ty,
                fact: match kind == "function-type" {
                    true => Fact::Said(Printed::applied(
                        "Set.MapsTo",
                        super::doc::Source::Mathlib,
                        vec![
                            Printed::letter(lean, map_type),
                            from_text.clone(),
                            to_text,
                        ],
                        super::doc::LeanType::Prop,
                    )),
                    false => Fact::Line,
                },
                domain: Some(from_text),
            })
        }
        _ => None,
    }
}

/// `{α β : Type*}`, a type variable for each of the things a binder holds,
/// a set of them, a member of one or a map between sets, or the statement
/// writes a set of though no letter is one, `(∅ : Set α).encard = 0`; None
/// where none is.
pub fn things_binder(binders: &[Binder], statement: &str) -> Option<String> {
    let mut vars: std::collections::BTreeSet<usize> = binders
        .iter()
        .flat_map(|b| match b {
            Binder::Letter { ty, .. } => ty.things_vars(),
            _ => Vec::new(),
        })
        .collect();
    if statement.contains(&format!("Set {}", super::expr::THINGS)) {
        vars.insert(0);
    }
    let names: Vec<String> = vars.into_iter().map(super::expr::things_name).collect();
    (!names.is_empty()).then(|| format!("{{{} : Type*}}", names.join(" ")))
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
        writer.domains.insert(f.text.to_string(), d);
    }
}

/// The binders of what is asked, in order. `maps` are the maps an item has
/// whose lines are not among what it asks, `f : [a, b] → ℝ`, by the letter
/// and the set it maps from: each takes its domain once that set's letters
/// have their types, for the lines that take a limit or a derivative
/// within it.
pub fn binders(
    writer: &mut Writer,
    asked: &[Asked],
    maps: &[(&Node, &Node)],
) -> Route<Vec<Binder>> {
    let mut out = Vec::new();
    for a in asked {
        for (f, from) in maps {
            if writer.domains.contains_key(f.text.as_str()) {
                continue;
            }
            if let Route::Built(d) = writer.set_term(from) {
                writer.domains.insert(f.text.to_string(), d);
            }
        }
        record_domain(writer, a.node);
        // A letter of a range is an integer, in ℕ or ℕ₀ where the range
        // starts at 1 or 0, and the range a fact about it.
        if let Some(letter) = range_letter(a.node) {
            let ty = LetterType::Number(super::templates::Num::Int);
            let system = match a.node.children.get(1) {
                Some(range) => super::expr::range_letter_system(range),
                None => System::Type(super::templates::Num::Int),
            };
            writer.introduce(&letter, system);
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
            let (says, line) = match fact {
                Fact::Said(f) => (f, None),
                Fact::Line => match writer.formula(a.node) {
                    Route::Built(p) => (p, Some(a.node.clone())),
                    Route::Declined(d) => return Route::Declined(d),
                },
            };
            out.push(Binder::Fact {
                name: a.name.clone(),
                says,
                line,
            });
            continue;
        }
        // A membership of a letter already given its type, `assume x ∈ ℤ`
        // after `let x ∈ ℝ`, is a fact about that letter, as set.mm's is,
        // and no second letter.
        let introduced = introduces(a.node)
            .filter(|(letter, _)| !writer.letters.contains_key(letter.as_str()));
        if let Some((letter, system)) = introduced {
            let ty = LetterType::Number(letter_type(system));
            writer.introduce(&letter, system);
            let name = super::names::letter(&letter);
            out.push(Binder::Letter {
                name: name.clone(),
                page: letter.clone(),
                general: writer.general == Some(letter_type(system)),
                ty,
            });
            // n ∈ ℕ and n ∈ ℕ₀ are facts of the integer n, as set.mm's are
            // of a number.
            let int = super::doc::LeanType::Num(super::templates::Num::Int);
            let order = match system {
                System::Positive => Some("<"),
                System::NonNegative => Some("≤"),
                System::Type(_) => None,
            };
            let fact = order.map(|o| {
                super::expr::relation_of(
                    o,
                    Printed::numeral("0", int.clone()),
                    Printed::letter(name.clone(), int.clone()),
                )
            });
            if let Some(says) = fact {
                let says = match says {
                    Route::Built(s) => s,
                    Route::Declined(d) => return Route::Declined(d),
                };
                out.push(Binder::Fact {
                    name: a.name.clone(),
                    says,
                    line: None,
                });
            }
            continue;
        }
        let written = match writer.without_line(a.node) {
            Some(w) => w.formula(a.node),
            None => writer.formula(a.node),
        };
        let says: Printed = match written {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        out.push(Binder::Fact {
            name: a.name.clone(),
            says,
            line: Some(a.node.clone()),
        });
        // A term of a wider type said to be an integer is, in what is
        // asked after, the integer this hypothesis gives. A letter is not:
        // A ∈ ℤ of a real A says a fact of A, which stays the letter.
        if let [term, set] = a.node.children.as_slice() {
            let integer = a.node.notation() == crate::notations::MEMBERSHIP
                && !term.is_name()
                && system_of(set) == Some(System::Type(super::templates::Num::Int))
                && writer
                    .carrier(term)
                    .built()
                    .is_some_and(|c| c > super::templates::Num::Int);
            if integer {
                writer.integers.push(super::expr::SaidInteger {
                    term: writer.grammar.print(term),
                    proof: a.name.clone(),
                    ty: super::templates::Num::Int,
                    value: None,
                    slot_only: false,
                });
            }
        }
    }
    Route::Built(out)
}
