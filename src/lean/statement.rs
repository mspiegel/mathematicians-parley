//! What a theorem or an item asks for, as Lean binders.
//!
//! A `let` that puts a letter in a number system makes the letter a binder
//! of that type; the page's ℕ, which starts at 1, adds the hypothesis that
//! the letter is above 0. Every other fact asked for is a hypothesis. The
//! same reading serves a theorem's own statement and a citation of it, so
//! the two agree on the order of what is asked.

use super::expr::{letter_type, system_of, LetterType, Printed, System, Writer};
use crate::citing::HypothesisAt;
use crate::formula::Node;
use crate::notations::{
    EMPTY_SET, FUNCTION_TYPE, IN, IS_AN_INTEGER_POLYNOMIAL, IS_A_POLYNOMIAL,
    LISTED_FOUR, LISTED_THREE, LISTED_TWO, MEMBERSHIP, NUMBER_SYSTEMS, ONE_TO_ONE,
    ONE_TO_ONE_ONTO, ONTO, POLYNOMIALS, POWERSET, SINGLETON, SUBGROUP, SUBSET,
};
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
        /// Where the statement writes it, where it says a fact the page
        /// writes, by which a citation finds what supplies it. For a
        /// letter's number system, `n ∈ ℕ`, the membership's place, whose
        /// `says` is the bound `0 < n`. None for a fact only Lean states.
        at: Option<StatedAt>,
    },
}

/// Where a statement writes a hypothesis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatedAt {
    /// A sentence of a hypothesis line, or the type a `let` line gives a
    /// map, whose supplier a citation's record gives by this place
    /// (`Supplied::at`).
    Hypothesis(HypothesisAt),
    /// A define by recursion in the header, by its label, which a citation
    /// meets with the citing proof's define of the same recursion
    /// (`Cited::recursions`).
    Recursion(String),
    /// That the letter of this page name, which a `let` line introduces,
    /// is one of ZF's sets: what set.mm's reading of the line adds, and the
    /// page never writes (`with_sethoods`). A citation meets it with the
    /// citing statement's own fact of the letter it gives.
    Sethood(String),
}

impl Binder {
    /// Its Lean name.
    pub fn name(&self) -> &str {
        match self {
            Binder::Letter { name, .. } | Binder::Fact { name, .. } => name,
        }
    }

    /// The binder in the document model.
    pub fn doc(&self) -> super::doc::file::Binder {
        use super::doc::file::Binder as Doc;
        match self {
            Binder::Fact { name, says, .. } => Doc::Fact {
                name: name.clone(),
                says: says.clone(),
            },
            Binder::Letter { ty, .. } => Doc::Typed {
                text: self.lean(),
                ty: Some(ty.lean_type()),
            },
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
    /// Where the statement writes it (`citing::HypothesisAt`).
    pub at: HypothesisAt,
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
/// systems, with its Lean type; None for any other fact. The systems are
/// the checker's (`CheckedTheorem::function_systems`); what is Lean's own is
/// which sets its types cover: a number system or a range of integers, as
/// the domain, a function from ℕ, ℕ₀ or a range being one on all of ℤ; and
/// no codomain ℕ, whose values are above 0. A function between other sets
/// is a map with its domain beside it (`introduces_in_set`).
pub fn introduces_function(
    writer: &Writer,
    node: &Node,
) -> Option<(String, LetterType)> {
    let [f, from, to] = node.children.as_slice() else {
        return None;
    };
    if node.notation() != crate::notations::FUNCTION_TYPE || !f.is_name() {
        return None;
    }
    let whole = |set: &Node| {
        set.notation() == crate::notations::INTEGER_RANGE || system_of(set).is_some()
    };
    if !whole(from) || !whole(to) || to.notation() == crate::notations::INTEGER_RANGE {
        return None;
    }
    let between = writer.function_systems.get(f.text.as_str())?;
    if between.to == crate::rules::System::N {
        return None;
    }
    let ty = LetterType::Function {
        from: super::expr::recorded_set_type(between.from),
        to: super::expr::recorded_set_type(between.to),
    };
    Some((f.text.to_string(), ty))
}

/// The letter a fact `p is a polynomial` introduces, a function from ℂ to
/// ℂ; None for any other fact. The page's words are read as the membership
/// p ∈ (the polynomials), or as the notation itself.
pub fn introduces_polynomial(node: &Node) -> Option<String> {
    match (node.notation(), node.children.as_slice()) {
        (IS_A_POLYNOMIAL | IS_AN_INTEGER_POLYNOMIAL, [p]) if p.is_name() => {
            Some(p.text.to_string())
        }
        (MEMBERSHIP, [p, set]) if p.is_name() && set.notation() == POLYNOMIALS => {
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
    match (node.notation(), rest) {
        // x ∈ {1, 2} of numbers: a number of the type that holds them all.
        (MEMBERSHIP, [set])
            if matches!(
                set.notation(),
                SINGLETON | LISTED_TWO | LISTED_THREE | LISTED_FOUR
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
        (MEMBERSHIP, [set]) if set.notation() == POWERSET => Some(InSet {
            letter: letter.text.to_string(),
            ty: LetterType::Set(writer.set_members(set.children.first()?)?),
            fact: Fact::Line,
            domain: None,
        }),
        (MEMBERSHIP, [set]) => Some(InSet {
            letter: letter.text.to_string(),
            ty: writer.members_of(set)?.letter(),
            fact: Fact::Line,
            domain: None,
        }),
        (SUBSET, [set]) => Some(InSet {
            letter: letter.text.to_string(),
            ty: LetterType::Set(writer.set_members(set)?),
            fact: Fact::Line,
            domain: None,
        }),
        // H is a subgroup of G: Lean's `Subgroup G`, whose type says it, so
        // that the line's own hypothesis is `True` (`sets::subgroup_claim`).
        (SUBGROUP, [group])
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
        (kind @ (FUNCTION_TYPE | ONE_TO_ONE | ONTO | ONE_TO_ONE_ONTO), [from, to]) => {
            // ∅ holds nothing of any type, so a map into it gives the
            // domain's.
            let a = writer.set_members(from)?;
            let b = match to.notation() {
                EMPTY_SET => a.clone(),
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
                fact: match kind == FUNCTION_TYPE {
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
pub fn things_binder(
    binders: &[Binder],
    statement: &[&Printed],
) -> Option<super::doc::file::Binder> {
    use super::doc::LeanType;
    let mut vars: std::collections::BTreeSet<usize> = binders
        .iter()
        .flat_map(|b| match b {
            Binder::Letter { ty, .. } => ty.things_vars(),
            _ => Vec::new(),
        })
        .collect();
    let sets_of_things = LeanType::Set(Box::new(LeanType::Things(0)));
    if statement.iter().any(|s| s.writes_type(&sets_of_things)) {
        vars.insert(0);
    }
    let names: Vec<String> = vars.into_iter().map(super::expr::things_name).collect();
    if names.is_empty() {
        return None;
    }
    // Each type stands for set.mm's universe of sets, which is never empty:
    // ∅ is in it. So a function between two of them exists, and an inverse
    // has a value where it takes nothing back.
    let mut text = format!("{{{} : Type*}}", names.join(" "));
    for n in &names {
        text.push_str(&format!(" [Nonempty {n}]"));
    }
    // Where the statement says a collection exists, its things are of a
    // type whose ZF sets `Sets` says, as `ZFSet` and sets of it are.
    if says_exists(binders, statement) {
        for n in &names {
            text.push_str(&format!(" [{} {n}]", super::expr::ZF_SETS));
        }
    }
    Some(super::doc::file::Binder::Typed { text, ty: None })
}

/// That a thing is one of ZF's sets, `LeanBridges.ZF.IsSet X`.
pub fn is_set(of: Printed) -> Printed {
    Printed::applied(
        super::expr::IS_SET,
        super::doc::Source::Bridge(super::doc::bridges::BridgeModule::ZF),
        vec![of],
        super::doc::LeanType::Prop,
    )
}

/// The name of the fact that a letter is one of ZF's sets, `hX_set`.
pub fn sethood_name(letter: &str) -> String {
    format!("h{}_set", super::names::letter(letter))
}

/// The letters a statement's `let` lines introduce as sets or members of
/// them, A of `let A be a set`, x of `let x be an element`, a of `let a ∉
/// X`: those set.mm reads as sets of ZF.
pub fn let_letters(
    hypotheses: &[crate::corpus::proof::Hypothesis],
    path: &str,
) -> Vec<String> {
    use crate::sorts::introduction::{Form, Introduction};
    hypotheses
        .iter()
        .filter(|h| h.kind == crate::corpus::Intro::Let)
        .filter_map(|h| match Introduction::read(h.body(path)).form {
            Form::Set(name) | Form::Element(name) | Form::NotIn(name) => Some(name),
            _ => None,
        })
        .collect()
}

/// The binders with, after each letter of `lets` a statement that says some
/// collection exists introduces, the fact that the letter is one of ZF's
/// sets: set.mm reads `let X be a set`, `let x be an element` and `let a ∉
/// X` so (`elab::reading::hypothesis_node`), and the page never writes it.
/// A letter of numbers is none of ZF's things, and a letter a hypothesis
/// says exists has its fact already. `statement` is what it concludes.
pub fn with_sethoods(
    binders: Vec<Binder>,
    lets: &[String],
    statement: &[&Printed],
) -> Vec<Binder> {
    if !says_exists(&binders, statement) {
        return binders;
    }
    let said: Vec<Printed> = binders
        .iter()
        .filter_map(|b| match b {
            Binder::Fact { says, .. } => Some(says.clone()),
            Binder::Letter { .. } => None,
        })
        .collect();
    let mut out = Vec::new();
    for b in binders {
        let fact = match &b {
            Binder::Letter { name, page, ty, .. }
                if lets.contains(page) && of_things(ty) =>
            {
                let says = is_set(Printed::letter(name.clone(), ty.lean_type()));
                (!said.contains(&says)).then(|| Binder::Fact {
                    name: sethood_name(page),
                    says,
                    at: Some(StatedAt::Sethood(page.clone())),
                })
            }
            _ => None,
        };
        out.push(b);
        out.extend(fact);
    }
    out
}

/// Whether a letter of this type is a thing ZF's sets are, a set of things
/// or a member of one, and not a number or a set of numbers.
fn of_things(ty: &LetterType) -> bool {
    use super::expr::Members;
    fn things(m: &Members) -> bool {
        match m {
            Members::Things(_) => true,
            Members::Sets(m) => things(m),
            _ => false,
        }
    }
    match ty {
        LetterType::Set(m) | LetterType::Member(m) => things(m),
        _ => false,
    }
}

/// Whether a statement says some collection exists, in what it asks or
/// what it concludes.
pub fn says_exists(binders: &[Binder], statement: &[&Printed]) -> bool {
    let names =
        |p: &Printed| p.constants().iter().any(|c| c.name == super::expr::IS_SET);
    statement.iter().any(|s| names(s))
        || binders.iter().any(|b| match b {
            Binder::Fact { says, .. } => names(says),
            Binder::Letter { .. } => false,
        })
}

/// Where a line says what sets a map or function letter maps between, `f :
/// A → B` or `f : A → B is one-to-one`, the A it maps from is its domain,
/// though the letter's type came first. A function from ℕ, whose Lean type
/// is from ℤ, has ℕ for its domain, not all of ℤ.
pub(super) fn record_domain(writer: &mut Writer, node: &Node) {
    let kinds = [FUNCTION_TYPE, ONE_TO_ONE, ONTO, ONE_TO_ONE_ONTO];
    let [f, from, _] = node.children.as_slice() else {
        return;
    };
    let map = matches!(
        writer.letters.get(f.text.as_str()),
        Some(LetterType::Map { .. } | LetterType::Function { .. })
    );
    if !map || !kinds.contains(&node.notation()) {
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
        // A letter a range introduces is an integer, in ℕ or ℕ₀ where the
        // range starts at 1 or 0, and the range a fact about it. A range
        // holding a letter let above, k ∈ ℝ, is a fact about that letter,
        // as `assume k ∈ ℤ` is.
        let ranged = range_letter(a.node)
            .filter(|letter| !writer.letters.contains_key(letter.as_str()));
        if let Some(letter) = ranged {
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
        if let Some((letter, ty)) = introduces_function(writer, a.node) {
            writer.letters.insert(letter.clone(), ty.clone());
            record_domain(writer, a.node);
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
                Fact::Said(f) => f,
                Fact::Line => match writer.formula(a.node) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                },
            };
            // What the letter's type says, `H : Subgroup G` of "H is a
            // subgroup of G", is no hypothesis in Lean.
            if says.text() == "True" {
                continue;
            }
            out.push(Binder::Fact {
                name: a.name.clone(),
                says,
                at: Some(StatedAt::Hypothesis(a.at)),
            });
            continue;
        }
        // A membership of a letter already given its type, `assume x ∈ ℤ`
        // after `let x ∈ ℝ`, is a fact about that letter, as set.mm's is,
        // and no second letter: the page puts x in ℤ only in the steps that
        // name the line (`docs/SYNTAX.md`), as the checker's `introduced`
        // does.
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
                // Its line is the membership, as the checker records where
                // a citation's value is in the system (`Cited::supplied`).
                out.push(Binder::Fact {
                    name: a.name.clone(),
                    says,
                    at: Some(StatedAt::Hypothesis(a.at)),
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
        // A fact Lean's types make true, `H is a subgroup of G` of an `H :
        // Subgroup G`, is no hypothesis in Lean, and a citation passes
        // nothing for it.
        if says.text() == "True" {
            continue;
        }
        out.push(Binder::Fact {
            name: a.name.clone(),
            says,
            at: Some(StatedAt::Hypothesis(a.at)),
        });
        // A term of a wider type said to be an integer is, in what is
        // asked after, the integer this hypothesis gives. A letter is not:
        // A ∈ ℤ of a real A says a fact of A, which stays the letter. The
        // steps write the term so too: a later hypothesis Lean can state
        // only of an integer, f(a)·a ≡ b (mod n), is stated of this one,
        // and a term has one Lean form in a theorem (`GOALS.md` decision
        // 20).
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
                    proof: super::tactics::hyp(&a.name),
                    ty: super::templates::Num::Int,
                    value: None,
                    slot_only: false,
                    back: None,
                });
            }
        }
    }
    Route::Built(out)
}
