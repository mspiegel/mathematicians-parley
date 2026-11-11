//! The library's items in Lean: each sentence an item concludes is a
//! theorem whose statement is printed from the record, as the checker read
//! it, and whose proof is the record's `lean` entry for that sentence.
//!
//! A citation then applies a theorem that says exactly what the page reads,
//! and `lake build` checks each mapped record against Mathlib, as a
//! citation's test checks it against set.mm in the Metamath build.

use indexmap::IndexMap;

use super::expr::{LetterType, Writer, GENERAL};
use super::names::{module_of, snake};
use super::statement::{binders, Asked, Binder};
use super::templates::Num;
use crate::checker::CheckedCorpus;
use crate::corpus::{Record, RecordKind};
use crate::formula::Node;
use crate::outcome::Route;

/// One sentence an item concludes, as Lean has it.
#[derive(Clone, Debug)]
pub struct Sentence {
    /// The theorem's full Lean name.
    pub decl: String,
    pub binders: Vec<Binder>,
    /// The sentence, as the checker read it.
    pub says: Node,
    /// The sentence in Lean.
    pub prop: super::expr::Printed,
    /// Where the item is a corpus theorem whose statement holds several
    /// sentences joined, the fields that take this one, `["2", "1"]` for
    /// `.2.1`.
    pub part: Vec<&'static str>,
    /// The arithmetic the page writes in the whole of the declaration's
    /// statement, what it asks included, which the gate's read-back
    /// compares with what Lean elaborated (`readback`).
    pub arithmetic: std::collections::BTreeMap<String, usize>,
    /// What its general letters range over; None where it has none.
    pub general: Option<General>,
    /// The domain each of its maps is on, by the map's letter: the X of `f
    /// : X → W`, which a citation that gives f a value and X none takes
    /// from that value's domain.
    pub domains: IndexMap<String, super::expr::Printed>,
}

/// An item of the library in Lean: its sentences, counted across its
/// groups in order, as a citation counts them.
#[derive(Clone, Debug)]
pub struct Item {
    pub module: String,
    pub sentences: Vec<Sentence>,
    /// The record's `lean` entry for each sentence; empty for a corpus
    /// theorem, which its own file proves.
    pub proofs: Vec<String>,
}

/// What an item's general letters range over: the number type the record
/// puts them in, and the kind of ring a statement of that type needs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct General {
    /// ℂ or ℝ, as the record says.
    pub num: Num,
    /// Whether the statement divides, so that it holds in a field.
    pub field: bool,
    /// Whether it orders, so that it holds in an ordered ring.
    pub ordered: bool,
    /// Whether it takes a floor, so that it holds in a ring with one.
    pub floor: bool,
    /// Whether it casts a number system into the type, so that it holds in
    /// a ring of characteristic 0.
    pub cast: bool,
}

impl General {
    /// The Lean binders of the type and its class.
    pub fn binders(&self) -> String {
        // A domain, so that a statement that cancels a factor, or says a
        // product is 0 only where a factor is, holds; ℤ, ℚ, ℝ and ℂ are
        // all domains, and a field is one already.
        let ring = if self.field {
            format!("[Field {GENERAL}]")
        } else {
            format!("[CommRing {GENERAL}] [IsDomain {GENERAL}]")
        };
        let order = if self.ordered {
            format!(" [LinearOrder {GENERAL}] [IsStrictOrderedRing {GENERAL}]")
        } else {
            String::new()
        };
        let floor = if self.floor {
            format!(" [FloorRing {GENERAL}]")
        } else {
            String::new()
        };
        let cast = if self.cast {
            format!(" [CharZero {GENERAL}]")
        } else {
            String::new()
        };
        format!("{{{GENERAL} : Type*}} {ring}{order}{floor}{cast}")
    }
}

/// The notations a statement may use and hold in any ring of a kind: its
/// arithmetic, order, floor and connectives. A statement using any other, √
/// or π, is about ℝ or ℂ themselves.
const ALGEBRAIC: &[&str] = &[
    "name",
    "numeral",
    "additive",
    "multiplicative",
    "power",
    "superscript",
    "unary-minus",
    "equality",
    "order",
    "absolute-value",
    "floor",
    "conjunction",
    "comma-conjunction",
    "disjunction",
    "logical-not",
    "biconditional",
    "conditional",
    "implication",
    "membership",
    "number-systems",
    "sum",
    "product",
    // Sums and products over a set, and what is said of the set, of things
    // or of numbers: these ask nothing of the ring the values are in.
    "sum-over",
    "product-over",
    "finite",
    "cardinality",
    "subset",
    "set-operations",
    "empty-set",
    "singleton",
    "listed-two",
    "listed-three",
    "listed-four",
    "powerset",
    "function-type",
    "one-to-one",
    "onto",
    "one-to-one-onto",
    "for-all",
    "there-is",
    "there-are",
    "there-are-two",
    "integer-range",
];

/// Whether an item's sentence holds of any ring of a kind, and which: where
/// the record puts a letter in ℂ or ℝ and the sentence uses only arithmetic,
/// order and connectives, it is said of any commutative ring, a field where
/// it divides, ordered where it orders, as Mathlib states such facts. A
/// citation then applies it in the citing claim's own type.
fn general_kind(
    group: &crate::citing::Group,
    says: &Node,
    functions: &[Node],
    free: &[FreeLetter],
) -> Option<General> {
    // A letter a notation reads at ℝ itself holds the item to ℝ.
    if free.iter().any(|f| f.fixed) {
        return None;
    }
    let nodes: Vec<&Node> = group
        .wants
        .iter()
        .map(|(_, n)| n)
        .chain(std::iter::once(says))
        .collect();
    // What the letters are numbers of, and what its functions give: a sum's
    // term t : {a, …, b} → ℝ is a function into any ring of the kind.
    let given = functions
        .iter()
        .filter_map(function_gives)
        .map(|(_, to)| to);
    let systems: Vec<Num> = nodes
        .iter()
        .filter_map(|n| super::statement::introduces(n))
        .map(|(_, s)| super::expr::letter_type(s))
        .chain(given)
        .chain(free.iter().map(|f| f.num))
        .collect();
    let num = if systems.contains(&Num::Complex) {
        Num::Complex
    } else if systems.contains(&Num::Real) {
        Num::Real
    } else {
        return None;
    };
    // The item's own function letters may be applied; a library function,
    // cos, is about ℝ itself.
    // Its maps between sets of things, g of `g : Y → Z be one-to-one`, are
    // its own as well.
    let maps = nodes
        .iter()
        .copied()
        .chain(functions.iter())
        .filter_map(|n| {
            let mapping = matches!(
                &*n.notation_name(),
                "function-type" | "one-to-one" | "onto" | "one-to-one-onto"
            );
            match n.children.first() {
                Some(f) if mapping && f.is_name() => Some(f.text.to_string()),
                _ => None,
            }
        });
    let own: Vec<String> = functions
        .iter()
        .filter_map(function_gives)
        .map(|(f, _)| f)
        .chain(maps)
        .collect();
    let applies_own = |p: &Node| {
        &*p.notation_name() == "application"
            && p.children
                .first()
                .is_some_and(|f| own.iter().any(|o| *o == *f.text))
    };
    let parts: Vec<Node> = nodes.iter().flat_map(|n| n.walk()).collect();
    if !parts
        .iter()
        .all(|p| ALGEBRAIC.contains(&&*p.notation_name()) || applies_own(p))
    {
        return None;
    }
    // A quotient asks a field, and so does a power to an integer letter or
    // a negative exponent, which Lean takes only where there are inverses.
    let integers: Vec<String> = nodes
        .iter()
        .filter_map(|n| super::statement::introduces(n))
        .filter(|(_, s)| *s == super::expr::System::Type(Num::Int))
        .map(|(letter, _)| letter)
        .collect();
    let integer_power = |p: &Node| {
        p.notation() == crate::notations::POWER
            && p.children.get(1).is_some_and(|e| {
                e.walk().iter().any(|n| {
                    integers.iter().any(|i| n.is_name() && *i == *n.text)
                        || n.notation() == crate::notations::UNARY_MINUS
                })
            })
    };
    // A number system named, x ∈ ℚ, is a cast into the type, which asks it
    // to have characteristic 0; a cast from ℚ asks a field.
    let systems_named: Vec<&Node> = parts
        .iter()
        .filter(|p| p.notation() == crate::notations::NUMBER_SYSTEMS)
        .collect();
    let cast = !systems_named.is_empty();
    let field = parts
        .iter()
        .any(|p| p.spelling() == crate::notations::DIVIDED || integer_power(p))
        || systems_named.iter().any(|s| &*s.text == "ℚ");
    let floor = parts.iter().any(|p| &*p.notation_name() == "floor");
    // An order between integers, b + 1 ≥ a of a range's ends, is an order
    // of ℤ and asks nothing of the ring.
    let ordered = floor
        || parts.iter().any(|p| {
            p.notation() == crate::notations::ABSOLUTE_VALUE
                || (p.notation() == crate::notations::ORDER
                    && !order_of_integers(p, &integers))
        });
    if num == Num::Complex && ordered {
        return None;
    }
    // A "there is" beside an order may say what holds of ℝ itself and not
    // of every ordered field: a natural number above any x, which a field
    // that is not Archimedean lacks.
    let exists = parts.iter().any(|p| {
        matches!(
            &*p.notation_name(),
            "there-is" | "there-are" | "there-are-two"
        )
    });
    if exists && ordered {
        return None;
    }
    Some(General {
        num,
        field,
        ordered,
        floor,
        cast,
    })
}

/// The function letter of a function line into a number system and the
/// type of its values: t : {a, …, b} → ℝ between number systems, or t : X
/// → ℝ from a set of things. None for any other line.
fn function_gives(node: &Node) -> Option<(String, Num)> {
    if let Some((f, LetterType::Function { to, .. })) =
        super::statement::introduces_function(node)
    {
        return Some((f, to));
    }
    let [f, _, to] = node.children.as_slice() else {
        return None;
    };
    match super::expr::system_of(to) {
        Some(super::expr::System::Type(n))
            if node.notation() == crate::notations::FUNCTION_TYPE && f.is_name() =>
        {
            Some((f.text.to_string(), n))
        }
        _ => None,
    }
}

/// Whether an order is between integers only: every letter in it one of
/// the integer letters given, and at least one letter.
fn order_of_integers(order: &Node, integers: &[String]) -> bool {
    let walked = order.walk();
    walked.iter().any(|n| n.is_name())
        && walked
            .iter()
            .all(|n| !n.is_name() || integers.iter().any(|i| *i == *n.text))
}

/// A letter of an item no line introduces, the x of "x ∈ ℚ ↔ …".
pub struct FreeLetter {
    pub name: String,
    /// What it is a number of: ℂ, set.mm's widest; ℝ where the statement
    /// orders it, since ℂ has no order; or ℤ where it puts it in a range.
    pub num: Num,
    /// Whether a notation reads it at ℝ itself, "x is irrational", which
    /// holds it there.
    pub fixed: bool,
}

/// The group's letters no fact it asks and no function type of the item's
/// introduces, and what each is a number of.
fn free_letters(
    group: &crate::citing::Group,
    says: &Node,
    functions: &[Node],
    w: &Writer,
    binders: &IndexMap<
        crate::formula::notation_id::NotationId,
        crate::formula::Binds,
        rustc_hash::FxBuildHasher,
    >,
) -> Vec<FreeLetter> {
    let stated: Vec<Node> = group
        .wants
        .iter()
        .map(|(_, n)| n.clone())
        .chain(std::iter::once(says.clone()))
        .collect();
    let statements = statement_letters(&stated);
    let ordered: std::collections::BTreeSet<String> = stated
        .iter()
        .flat_map(|n| n.walk())
        .filter(|n| n.notation() == crate::notations::ORDER)
        .flat_map(|n| n.names())
        .collect();
    // A range's member is an integer, and so is a letter that stands as a
    // range's end, the k of {1, …, k}: set.mm's ranges are of integers.
    // A letter a count is compared with, n of "n ≤ |W|", is a natural
    // number: a count is one, or ∞ (`sets::count_term`), and Lean compares
    // the two in ℕ∞, which holds the naturals.
    let beside_count: std::collections::BTreeSet<String> = stated
        .iter()
        .flat_map(|n| n.walk())
        .filter(|n| {
            matches!(
                n.notation(),
                crate::notations::EQUALITY | crate::notations::ORDER
            )
        })
        .flat_map(|n| match n.children.as_slice() {
            [a, b] if w.counts(b) && a.is_name() => vec![a.text.to_string()],
            [a, b] if w.counts(a) && b.is_name() => vec![b.text.to_string()],
            _ => Vec::new(),
        })
        .collect();
    let in_range: std::collections::BTreeSet<String> = stated
        .iter()
        .flat_map(|n| n.walk())
        .flat_map(|n| {
            let ends: Vec<String> = match n.notation() {
                crate::notations::INTEGER_RANGE => n
                    .children
                    .iter()
                    .filter(|c| c.is_name())
                    .map(|c| c.text.to_string())
                    .collect(),
                _ => Vec::new(),
            };
            super::statement::range_letter(&n).into_iter().chain(ends)
        })
        .collect();
    let mut fixed = std::collections::BTreeSet::new();
    for n in stated.iter().flat_map(|n| n.walk()) {
        let Route::Built(t) = w.template(&n) else {
            continue;
        };
        for (slot, child) in t.holes.iter().zip(&n.children) {
            if matches!(slot, super::templates::Slot::Fixed(Num::Real))
                && child.is_name()
            {
                fixed.insert(child.text.to_string());
            }
        }
    }
    let introduced: Vec<String> = group
        .wants
        .iter()
        .map(|(_, n)| n)
        .chain(functions)
        .filter_map(|n| {
            super::statement::range_letter(n)
                .or_else(|| function_gives(n).map(|(l, _)| l))
                .or_else(|| super::statement::introduces(n).map(|(l, _)| l))
                .or_else(|| super::statement::introduces_polynomial(n))
        })
        .collect();
    group
        .free_names(binders)
        .into_iter()
        .filter(|name| {
            !group.functions.contains(name)
                && !group.identities.contains(name)
                && !statements.contains(name)
                && !introduced.contains(name)
        })
        .map(|name| {
            let real = ordered.contains(&name) || fixed.contains(&name);
            // A member of a range the item names, the k of "k ∈ {1, …, n}
            // ↔ k ∈ ℕ and k ≤ n", is an integer, as a range letter is in a
            // theorem: of any other k both sides are false.
            let num = if beside_count.contains(&name) {
                Num::Nat
            } else if in_range.contains(&name) {
                Num::Int
            } else if real {
                Num::Real
            } else {
                Num::Complex
            };
            FreeLetter {
                num,
                fixed: fixed.contains(&name),
                name,
            }
        })
        .collect()
}

/// The function letter of a function into numbers and its type, alone or
/// one-to-one or onto: of `f : D → ℝ` between sets of numbers that are
/// not both number systems, a
/// function of the numbers' types; of `t : X → ℝ` from a set of things, a
/// map from those into the numbers. None for any other node.
fn function_into_numbers(
    w: &super::expr::Writer,
    node: &Node,
) -> Option<(String, LetterType)> {
    let [f, from, to] = node.children.as_slice() else {
        return None;
    };
    let typed = matches!(
        &*node.notation_name(),
        "function-type" | "one-to-one" | "onto" | "one-to-one-onto"
    );
    if !typed || !f.is_name() {
        return None;
    }
    match (w.set_members(from)?, w.set_members(to)?) {
        (super::expr::Members::Numbers(a), super::expr::Members::Numbers(b)) => {
            Some((f.text.to_string(), LetterType::Function { from: a, to: b }))
        }
        (from, to @ super::expr::Members::Numbers(_)) => {
            Some((f.text.to_string(), LetterType::Map { from, to }))
        }
        _ => None,
    }
}

/// The Lean type the sorts give a letter that is a set, a member of one or
/// a map between sets, its things of the type variable `things` gives it;
/// None for any other letter.
fn set_type_in(
    sorts: Option<&crate::formula::Sorts>,
    things: &ThingTypes,
    name: &str,
) -> Option<LetterType> {
    let ty = sorts
        .and_then(|s| s.get(name))
        .and_then(super::sets::set_letter_type)?;
    Some(match ty {
        LetterType::Map { from, to } => LetterType::Map {
            from: from.with_things(things.var(&ThingKey::From(name.to_string()))),
            to: to.with_things(things.var(&ThingKey::To(name.to_string()))),
        },
        LetterType::Set(m) => LetterType::Set(m.with_things(things.of_letter(name))),
        LetterType::Member(m) => {
            LetterType::Member(m.with_things(things.of_letter(name)))
        }
        LetterType::Property(m) => {
            LetterType::Property(m.with_things(things.of_letter(name)))
        }
        other => other,
    })
}

/// A set letter named in a function's type that has no type yet, given the
/// one its sort makes and a binder for it.
fn type_named_set(
    w: &mut Writer,
    statements: &mut Vec<Binder>,
    sorts: Option<&crate::formula::Sorts>,
    things: &ThingTypes,
    set: &Node,
) {
    let unbound = set.is_name() && !w.letters.contains_key(set.text.as_str());
    if let Some(ty) = unbound
        .then(|| set_type_in(sorts, things, &set.text))
        .flatten()
    {
        w.letters.insert(set.text.to_string(), ty.clone());
        statements.push(Binder::Letter {
            name: super::names::letter(&set.text),
            page: set.text.to_string(),
            ty,
            general: false,
        });
    }
}

/// Whether the node is a letter the sorts make a map.
fn map_letter(node: &Node, sorts: Option<&crate::formula::Sorts>) -> bool {
    node.is_name()
        && matches!(
            sorts
                .and_then(|s| s.get(node.text.as_str()))
                .and_then(|s| s.full()),
            Some(crate::formula::Whole::Function(..))
        )
}

/// What an item's things are of: a letter's own, or what a map letter
/// takes or gives.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ThingKey {
    /// The things a set, element or property letter is or holds or is of.
    Letter(String),
    /// What a map letter takes.
    From(String),
    /// What a map letter gives.
    To(String),
}

/// The type variable an item's things take, by what they are of: things
/// two of its terms compare, join or are members of are of one type, and a
/// map takes the things of its domain to those of the set it maps into,
/// which are of another where nothing the item says makes them one. Of
/// `E : Y → Z` and `u ∈ {E(s) : s ∈ Y} ↔ there is s ∈ Y with u = E(s)`, Y
/// and s are α, Z and u are β; of `f : X → X`, all are α. Variables are
/// numbered in the order the item first names their things.
#[derive(Default)]
struct ThingTypes {
    parent: std::collections::BTreeMap<ThingKey, ThingKey>,
    /// Each key, in the order first met.
    met: Vec<ThingKey>,
    vars: std::collections::BTreeMap<ThingKey, usize>,
    /// The letters a "there is f : X → Y" binds, maps as a map letter of
    /// the item's sorts is.
    bound_maps: std::collections::BTreeSet<String>,
}

impl ThingTypes {
    /// Read from the item's map lines, then its lines.
    fn read(lines: &[&Node], sorts: Option<&crate::formula::Sorts>) -> ThingTypes {
        let mut out = ThingTypes::default();
        for line in lines {
            out.class(line, sorts);
        }
        let mut roots: Vec<ThingKey> = Vec::new();
        for key in out.met.clone() {
            let root = out.root(&key);
            let var = match roots.iter().position(|r| *r == root) {
                Some(i) => i,
                None => {
                    roots.push(root);
                    roots.len() - 1
                }
            };
            out.vars.insert(key, var);
        }
        out
    }

    /// The type variable of these things; the first for any the item
    /// does not name.
    fn var(&self, key: &ThingKey) -> usize {
        self.vars.get(key).copied().unwrap_or(0)
    }

    fn of_letter(&self, name: &str) -> usize {
        self.var(&ThingKey::Letter(name.to_string()))
    }

    fn root(&self, key: &ThingKey) -> ThingKey {
        let mut at = key.clone();
        while let Some(up) = self.parent.get(&at) {
            at = up.clone();
        }
        at
    }

    fn meet(&mut self, key: &ThingKey) {
        if !self.met.contains(key) {
            self.met.push(key.clone());
        }
    }

    /// The things of the two are of one type.
    fn join(&mut self, a: Option<ThingKey>, b: Option<ThingKey>) {
        let (Some(a), Some(b)) = (a, b) else {
            return;
        };
        self.meet(&a);
        self.meet(&b);
        let (ra, rb) = (self.root(&a), self.root(&b));
        if ra != rb {
            self.parent.insert(rb, ra);
        }
    }

    /// The key of the things a term is, holds or is made of, joining what
    /// the term says are of one type; None for a statement, a number or a
    /// map.
    fn class(
        &mut self,
        node: &Node,
        sorts: Option<&crate::formula::Sorts>,
    ) -> Option<ThingKey> {
        let bound = self.bound_maps.clone();
        let is_map = |n: &Node| {
            map_letter(n, sorts) || (n.is_name() && bound.contains(&*n.text))
        };
        let name = node.notation_name();
        let kids = node.children.as_slice();
        match (&*name, kids) {
            // There is f : X → Y with …: f a map from X's things to Y's,
            // what the body says of it read as of a map letter.
            ("there-is" | "for-all", [f, set, body])
                if f.is_name() && &*set.notation_name() == "functions-from" =>
            {
                self.bound_maps.insert(f.text.to_string());
                if let [from, to] = set.children.as_slice() {
                    let (a, b) = (self.class(from, sorts), self.class(to, sorts));
                    self.join(Some(ThingKey::From(f.text.to_string())), a);
                    self.join(Some(ThingKey::To(f.text.to_string())), b);
                }
                self.class(body, sorts);
                None
            }
            _ if node.is_name() => {
                if is_map(node) || node.sort.is("number") || node.sort.is("formula") {
                    return None;
                }
                let key = ThingKey::Letter(node.text.to_string());
                self.meet(&key);
                Some(key)
            }
            // f : Y → Z, with or without a property: f takes Y's things
            // to Z's.
            (
                "function-type" | "one-to-one" | "onto" | "one-to-one-onto",
                [f, from, to],
            ) if is_map(f) => {
                let (a, b) = (self.class(from, sorts), self.class(to, sorts));
                self.join(Some(ThingKey::From(f.text.to_string())), a);
                self.join(Some(ThingKey::To(f.text.to_string())), b);
                None
            }
            // f(x), and f[X] the image: x and X are of what f takes, the
            // value of what it gives; under g⁻¹ the other way round.
            ("application" | "image", [f, x]) => {
                // g⁻¹(y) is the bridges' inverse, which gives y itself where
                // g sends nothing to it, so g's two sides are one type.
                if let ("application", ("inverse", [g])) =
                    (&*name, (&*f.notation_name(), f.children.as_slice()))
                {
                    if let Some((takes, gives)) = self.sides(g, sorts) {
                        self.join(Some(takes), Some(gives));
                    }
                }
                let arg = self.class(x, sorts);
                match self.sides(f, sorts) {
                    Some((takes, gives)) => {
                        self.join(Some(takes), arg);
                        Some(gives)
                    }
                    // P(t) of a property: t is of what P is of.
                    None if f.is_name() && !node.sort.is("number") => {
                        let p = self.class(f, sorts);
                        self.join(p, arg);
                        None
                    }
                    None => None,
                }
            }
            // A bijection from X to Y, or the maps from X to Y a "there is
            // f : X → Y" ranges over: X's things and Y's may be of two
            // types, as a map's sides are.
            ("bijection" | "functions-from", [from, to]) => {
                self.class(from, sorts);
                self.class(to, sorts);
                None
            }
            // {E(s) : s ∈ Y}: s is of Y's things, and the set holds E(s)'s.
            ("set-image", [term, letter, set]) => {
                let (s, y) = (self.class(letter, sorts), self.class(set, sorts));
                self.join(s, y);
                self.class(term, sorts)
            }
            // A statement joins its terms, u = E(s), x ∈ X, ∀ x ∈ X; a
            // number is made of numbers; a term of sets, X ∪ Y, joins them.
            _ => {
                let classes: Vec<ThingKey> =
                    kids.iter().filter_map(|k| self.class(k, sorts)).collect();
                for pair in classes.windows(2) {
                    self.join(Some(pair[0].clone()), Some(pair[1].clone()));
                }
                let term = !node.sort.is("number") && !node.sort.is("formula");
                term.then(|| classes.into_iter().next()).flatten()
            }
        }
    }

    /// What a map term takes and gives: f's, g ∘ f's, or g⁻¹'s; None for
    /// a term no map letter makes.
    fn sides(
        &mut self,
        f: &Node,
        sorts: Option<&crate::formula::Sorts>,
    ) -> Option<(ThingKey, ThingKey)> {
        if map_letter(f, sorts) || (f.is_name() && self.bound_maps.contains(&*f.text)) {
            let (from, to) = (
                ThingKey::From(f.text.to_string()),
                ThingKey::To(f.text.to_string()),
            );
            self.meet(&from);
            self.meet(&to);
            return Some((from, to));
        }
        match (&*f.notation_name(), f.children.as_slice()) {
            ("inverse", [g]) => self.sides(g, sorts).map(|(a, b)| (b, a)),
            ("composition", [g, inner]) => {
                let (takes, mid) = self.sides(inner, sorts)?;
                let (mid2, gives) = self.sides(g, sorts)?;
                self.join(Some(mid), Some(mid2));
                Some((takes, gives))
            }
            _ => None,
        }
    }
}

/// The letters that stand where a statement stands: a whole sentence, or a
/// part an "and", "or", "not", "if" or "↔" joins, the P and Q of a rule of
/// reasoning.
fn statement_letters(sentences: &[Node]) -> std::collections::BTreeSet<String> {
    use crate::notations::{
        BICONDITIONAL, COMMA_CONJUNCTION, CONDITIONAL, CONJUNCTION, DISJUNCTION,
        IMPLICATION, LOGICAL_NOT,
    };
    let mut out = std::collections::BTreeSet::new();
    for s in sentences {
        if s.is_name() {
            out.insert(s.text.to_string());
        }
        for n in s.walk() {
            let joins = matches!(
                n.notation(),
                BICONDITIONAL
                    | COMMA_CONJUNCTION
                    | CONDITIONAL
                    | CONJUNCTION
                    | DISJUNCTION
                    | IMPLICATION
                    | LOGICAL_NOT
            );
            if joins {
                out.extend(
                    n.children
                        .iter()
                        .filter(|c| c.is_name())
                        .map(|c| c.text.to_string()),
                );
            }
        }
    }
    out
}

/// The prefix a citation writes before an item of this kind.
pub fn prefix(record: &Record) -> &'static str {
    match record.kind {
        RecordKind::Definition => "def",
        RecordKind::Axiom => "axi",
        _ if record.mundane => "mun",
        _ => "thm",
    }
}

/// The module that holds a record's items: `Parley.Items.Stdlib.Divisibility`
/// for the records of `corpus/stdlib/divisibility.records`.
pub fn items_module(record: &Record) -> String {
    module_of(&format!("items/{}", record.module()))
}

/// The record of an item, by its full name.
pub fn record_of<'c>(checked: &'c CheckedCorpus, full: &str) -> Option<&'c Record> {
    checked
        .corpus
        .records
        .iter()
        .find(|r| format!("{}/{}", r.module(), r.name) == full)
}

/// The item a record states, in Lean; declined where a sentence of it does
/// not print. The record's `lean-proof` field holds one proof for each sentence,
/// set apart by ` ; `.
/// A record's line letting a group, `let G be a group with operation · and
/// identity e`: the group's name, its identity's, and the line's text, by
/// which its reading is told among what the item asks.
struct GroupLine {
    group: String,
    identity: String,
    text: String,
}

/// Each line of the record that lets a group.
fn group_lines(record: &Record) -> Vec<GroupLine> {
    use crate::sorts::introduction::{Form, Introduction};
    record
        .hypotheses
        .iter()
        .filter_map(|h| {
            let body = h.body(&record.path);
            match Introduction::read(body.clone()).form {
                Form::Group {
                    group, identity, ..
                } => Some(GroupLine {
                    group,
                    identity,
                    text: body.text().to_string(),
                }),
                _ => None,
            }
        })
        .collect()
}

pub fn item(writer: &Writer, checked: &CheckedCorpus, record: &Record) -> Route<Item> {
    let full = format!("{}/{}", record.module(), record.name);
    let Some(Some(groups)) = checked.library.groups.get(&full) else {
        return Route::no(format!("{full} has no reading as an item"));
    };
    let module = items_module(record);
    let base = format!("{}_{}", prefix(record), snake(&record.name));
    let total: usize = groups.iter().map(|g| g.gives.len()).sum();
    let mut sentences = Vec::new();
    let groups_let = group_lines(record);
    // A phrase a define gives is written out as its meaning, as a theorem's
    // page is (`checker::written`).
    let phrases = crate::checker::written::library_phrases(
        &checked.corpus.records,
        &checked.library.groups,
    );
    let facts = checked.library.item_facts.get(&full);
    let groups: Vec<crate::citing::Group> = groups
        .iter()
        .map(|g| crate::checker::written::group_written(g, &phrases, writer.grammar))
        .collect();
    for (gi, group) in groups.iter().enumerate() {
        // What the checker read the group's lines to say of its terms
        // (`LibraryReading::item_facts`).
        let Some(read) = facts.and_then(|f| f.get(gi)) else {
            return Route::no("an item group the checker read no facts of");
        };
        for (si, says) in group.gives.iter().enumerate() {
            let mut w = Writer::new(writer.grammar, writer.templates);
            for g in &groups_let {
                w.letters.insert(g.group.clone(), LetterType::Group);
                w.letters
                    .insert(g.identity.clone(), LetterType::Identity(g.group.clone()));
            }
            w.bounds = read.bounds.clone();
            let functions: &[Node] = checked
                .library
                .function_types
                .get(&full)
                .map_or(&[], Vec::as_slice);
            let free =
                free_letters(group, says, functions, &w, &writer.grammar.binders());
            // A letter the record's sorts make a set, a member of one or a
            // map between sets, `let Y be a set`: of Lean's `Set α`, and no
            // number the item's general type is chosen for.
            let sorts = checked
                .corpus
                .records
                .iter()
                .position(|r| std::ptr::eq(r, record))
                .and_then(|i| checked.library.record_sorts.get(&i));
            let lines: Vec<&Node> = functions
                .iter()
                .chain(group.wants.iter().map(|(_, n)| n))
                .chain(std::iter::once(says))
                .collect();
            let things = ThingTypes::read(&lines, sorts);
            // A set the item's hypotheses say is finite is counted as a
            // natural number; one only its conclusion says is, X of "if
            // |X| = m then X is finite", is not, as the count comes first.
            w.finite_from(&read.finite);
            let mut sets: Vec<(String, LetterType)> = free
                .iter()
                .filter_map(|f| {
                    set_type_in(sorts, &things, &f.name).map(|ty| (f.name.clone(), ty))
                })
                .collect();
            for (name, ty) in &sets {
                w.letters.insert(name.clone(), ty.clone());
            }
            // A letter the sorts leave out that stands as a member of a set,
            // the u of "u ∈ Y ∖ Z", is a member of that set's kind.
            let said: Vec<&Node> = group
                .wants
                .iter()
                .map(|(_, n)| n)
                .chain(std::iter::once(says))
                .collect();
            // A set of numbers, which its sort does not say the type of, is
            // of the numbers the item puts it among: D of D ⊆ ℝ, D ∈ 𝒫ℝ.
            // Or of the numbers of a set it is joined with or taken from:
            // c of {1, …, i} ∖ c is a set of integers.
            let systems = read.set_systems.get(si).cloned().unwrap_or_default();
            for (name, system) in systems {
                let ty = LetterType::Set(super::expr::Members::Numbers(
                    super::expr::recorded_set_type(system),
                ));
                let free_letter = free.iter().any(|f| f.name == name);
                if free_letter && !w.letters.contains_key(&name) {
                    w.letters.insert(name.clone(), ty.clone());
                    sets.push((name, ty));
                }
            }
            // A function a line the item asks says is one-to-one or onto,
            // `f : X → X be one-to-one` of X ⊆ ℤ, takes its type from the
            // sets that line names, once those have theirs.
            for node in &said {
                if let Some((name, ty)) = function_into_numbers(&w, node) {
                    let free_letter = free.iter().any(|f| f.name == name);
                    if free_letter && !w.letters.contains_key(&name) {
                        w.letters.insert(name.clone(), ty.clone());
                        sets.push((name, ty));
                    }
                }
            }
            // Any other set of numbers is of reals where the item compares
            // numbers by order or integrates over reals, and of complex
            // numbers where it does neither, as its number letters are
            // (`free_letters`).
            let ordered = said.iter().flat_map(|n| n.walk()).any(|n| {
                n.notation() == crate::notations::ORDER
                    || &*n.notation_name() == "integral"
            });
            let of_numbers = |s: &crate::formula::Sort| {
                matches!(s.full(), Some(crate::formula::Whole::Set(m))
                    if matches!(**m, crate::formula::Whole::Number))
            };
            // A set named only in a function's type, the X of `f : X → ℝ`,
            // is one of them too.
            let in_types = functions
                .iter()
                .flat_map(|n| n.children.iter().skip(1))
                .filter(|s| s.is_name())
                .map(|s| s.text.to_string());
            let names: Vec<String> = free
                .iter()
                .map(|f| f.name.clone())
                .chain(in_types)
                .collect();
            for name in names {
                let sorted = sorts.and_then(|s| s.get(name.as_str()));
                if w.letters.contains_key(&name) || !sorted.is_some_and(of_numbers) {
                    continue;
                }
                // The set a function maps from, where the item applies the
                // function only at members of a range, t(k) of k ∈ {a, …,
                // b}, is a set of integers.
                let at_integers = crate::citing::number_sets::domain_at_integers(
                    &name, functions, &said,
                );
                let num = match (at_integers, ordered) {
                    (true, _) => Num::Int,
                    (false, true) => Num::Real,
                    (false, false) => Num::Complex,
                };
                let ty = LetterType::Set(super::expr::Members::Numbers(num));
                w.letters.insert(name.clone(), ty.clone());
                sets.push((name, ty));
            }
            let listed = |n: &Node| {
                matches!(
                    &*n.notation_name(),
                    "singleton" | "listed-two" | "listed-three" | "listed-four"
                )
            };
            let of_no_number = |n: &Node| {
                n.is_name()
                    && free.iter().any(|f| *f.name == *n.text)
                    && !n.sort.is("number")
            };
            // {u, w} where no letter of it has a number's sort, a pair of
            // elements of any sort, wherever it stands: each is a thing, and
            // the statement holds of numbers as of any other type. Ahead of
            // the memberships below, so that x of x ∈ {u, w} is one too.
            for n in said.iter().flat_map(|n| n.walk()) {
                if listed(&n) && n.children.iter().all(of_no_number) {
                    for t in &n.children {
                        if !sets.iter().any(|(s, _)| *s == *t.text) {
                            let ty = LetterType::Member(super::expr::Members::Things(
                                things.of_letter(&t.text),
                            ));
                            w.letters.insert(t.text.to_string(), ty.clone());
                            sets.push((t.text.to_string(), ty));
                        }
                    }
                }
            }
            for n in said.iter().flat_map(|n| n.walk()) {
                let [x, set] = n.children.as_slice() else {
                    continue;
                };
                let member = n.notation() == crate::notations::MEMBERSHIP
                    && x.is_name()
                    && free.iter().any(|f| *f.name == *x.text)
                    && !sets.iter().any(|(s, _)| *s == *x.text);
                // Typed as it is met, so that a later set made of it, the gH
                // of u ∈ gH after g ∈ G, has a type too.
                if let Some(m) = member.then(|| w.members_of(set)).flatten() {
                    w.letters.insert(x.text.to_string(), m.letter());
                    sets.push((x.text.to_string(), m.letter()));
                }
            }
            // The letters left are numbers. A group's own, its name and its
            // identity, are typed by its line; its subgroups and elements by
            // the lines that let them, `H is a subgroup of G`, `a ∈ G`.
            let of_group = |name: &str| {
                let sort = sorts.and_then(|s| s.get(name)).and_then(|s| s.full());
                matches!(sort, Some(crate::formula::Whole::GroupElement))
                    || matches!(sort, Some(crate::formula::Whole::Set(m))
                        if matches!(**m, crate::formula::Whole::GroupElement))
            };
            let free: Vec<FreeLetter> = free
                .into_iter()
                .filter(|f| !sets.iter().any(|(s, _)| *s == f.name))
                .filter(|f| !w.letters.contains_key(&f.name) && !of_group(&f.name))
                .collect();
            let kind = general_kind(group, says, functions, &free);
            w.general = kind.map(|k| k.num);
            // A group line is the group's binder, not a fact asked
            // (`group_lines`).
            let asked: Vec<Asked> = group
                .wants
                .iter()
                .enumerate()
                .filter(|(_, (text, _))| !groups_let.iter().any(|g| g.text == *text))
                .map(|(i, (_, node))| Asked {
                    node,
                    name: format!("h{}", i + 1),
                })
                .collect();
            // A letter of the item that stands for a statement, the P of
            // "P or Q", is a proposition it is stated for.
            let mut statements: Vec<Binder> = groups_let
                .iter()
                .map(|g| Binder::Letter {
                    name: super::names::letter(&g.group),
                    page: g.group.clone(),
                    general: false,
                    ty: LetterType::Group,
                })
                .collect();
            let stated: Vec<Node> = group
                .wants
                .iter()
                .map(|(_, n)| n.clone())
                .chain(std::iter::once(says.clone()))
                .collect();
            let said = statement_letters(&stated);
            for name in group.free_names(&writer.grammar.binders()) {
                if said.contains(&name) {
                    w.letters.insert(name.clone(), LetterType::Statement);
                    statements.push(Binder::Letter {
                        name: super::names::letter(&name),
                        page: name,
                        ty: LetterType::Statement,
                        general: false,
                    });
                }
            }
            // A function the item has, `t : {a, …, b} → ℝ`, which its
            // groups leave out because a citation supplies nothing for it.
            for node in checked
                .library
                .function_types
                .get(&full)
                .into_iter()
                .flatten()
            {
                // The X of `t : X → ℝ`, named only in the type, has its
                // own first, so that t takes its members.
                if let [_, from, _] = node.children.as_slice() {
                    type_named_set(&mut w, &mut statements, sorts, &things, from);
                }
                if let Some((letter, ty)) = super::statement::introduces_function(node)
                    .or_else(|| function_into_numbers(&w, node))
                {
                    // A function into the item's general type gives K, and
                    // so does a map of things into it.
                    let general = match &ty {
                        LetterType::Function { to, .. } => w.general == Some(*to),
                        LetterType::Map {
                            to: super::expr::Members::Numbers(to),
                            ..
                        } => w.general == Some(*to),
                        _ => false,
                    };
                    w.letters.insert(letter.clone(), ty.clone());
                    statements.push(Binder::Letter {
                        name: super::names::letter(&letter),
                        page: letter,
                        ty,
                        general,
                    });
                }
            }
            for (name, ty) in &sets {
                w.letters.insert(name.clone(), ty.clone());
                // A set of the item's general type's numbers is a `Set K`.
                let general = matches!(ty, LetterType::Set(super::expr::Members::Numbers(n))
                    if w.general == Some(*n));
                statements.push(Binder::Letter {
                    name: super::names::letter(name),
                    page: name.clone(),
                    ty: ty.clone(),
                    general,
                });
            }
            // A map the item has, `f : D → E`, maps the one set into the
            // other, which its groups leave out as they leave out its type.
            // The fact is written once every letter has its type, after the
            // binders, since D may be made of letters a line lets, [a, b].
            let mut maps: Vec<(&Node, &Node, &Node)> = Vec::new();
            for node in checked
                .library
                .function_types
                .get(&full)
                .into_iter()
                .flatten()
            {
                let [f, from, to] = node.children.as_slice() else {
                    continue;
                };
                // A map of things, or a function of numbers whose domain is
                // a set and not a number system, f : D → ℝ.
                let of_numbers = function_into_numbers(&w, node).is_some()
                    && super::expr::function_systems(from, to).is_none();
                if !of_numbers
                    && !matches!(
                        w.letters.get(f.text.as_str()),
                        Some(LetterType::Map { .. })
                    )
                {
                    continue;
                }
                // A set named only in the map's type, the W of `f : X → W`,
                // is a letter of the item all the same.
                for set in [from, to] {
                    type_named_set(&mut w, &mut statements, sorts, &things, set);
                }
                maps.push((f, from, to));
            }
            for letter in &free {
                if w.letters.contains_key(&letter.name) {
                    continue;
                }
                let ty = LetterType::Number(letter.num);
                w.letters.insert(letter.name.clone(), ty.clone());
                statements.push(Binder::Letter {
                    name: super::names::letter(&letter.name),
                    page: letter.name.clone(),
                    ty,
                    general: !letter.fixed && w.general == Some(letter.num),
                });
            }
            let domains: Vec<(&Node, &Node)> =
                maps.iter().map(|(f, from, _)| (*f, *from)).collect();
            let mut binders: Vec<Binder> = match binders(&mut w, &asked, &domains) {
                Route::Built(b) => statements.into_iter().chain(b).collect(),
                Route::Declined(d) => return Route::Declined(d),
            };
            for (f, from, to) in maps {
                let name = super::names::letter(&f.text);
                // Into all of a number type, t : X → ℝ, its Lean type says
                // where it maps, and K's where the item is general.
                if matches!(
                    super::expr::system_of(to),
                    Some(super::expr::System::Type(_))
                ) {
                    let Route::Built(a) = w.set_term(from) else {
                        return Route::no(format!(
                            "{} maps from a set with no Lean form",
                            f.text
                        ));
                    };
                    w.domains.insert(f.text.to_string(), a);
                    continue;
                }
                let (Route::Built(a), Route::Built(b)) =
                    (w.set_term(from), w.set_term(to))
                else {
                    return Route::no(format!(
                        "{} maps between sets with no Lean form",
                        f.text
                    ));
                };
                let map = super::expr::Printed {
                    kind: super::doc::TermKind::Letter(name.clone()),
                    ty: w.letters.get(f.text.as_str()).map(LetterType::lean_type),
                };
                binders.push(Binder::Fact {
                    name: format!("h{name}"),
                    says: super::expr::Printed::applied(
                        "Set.MapsTo",
                        super::doc::Source::Mathlib,
                        vec![map, a.clone(), b],
                        super::doc::LeanType::Prop,
                    ),
                    line: None,
                });
                w.domains.insert(f.text.to_string(), a);
            }
            let prop = match w.formula(says) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            let name = if total == 1 {
                base.clone()
            } else {
                format!("{base}_{}", sentences.len() + 1)
            };
            let mut stated: Vec<Node> =
                group.wants.iter().map(|(_, n)| n.clone()).collect();
            stated.push(says.clone());
            let arithmetic = super::readback::page_arithmetic(&w, &stated);
            sentences.push(Sentence {
                decl: format!("{module}.{name}"),
                binders,
                says: says.clone(),
                prop,
                part: Vec::new(),
                arithmetic,
                general: kind,
                domains: w.domains.clone(),
            });
        }
    }
    let entries: Vec<&str> = record
        .lean_target()
        .map(|f| f.split(" ; ").map(str::trim).collect())
        .unwrap_or_default();
    if entries.len() != sentences.len() {
        return Route::no(format!(
            "{full} concludes {} sentences and its lean-proof field gives {} proofs",
            sentences.len(),
            entries.len()
        ));
    }
    let mut proofs = Vec::new();
    for (entry, sentence) in entries.iter().zip(&sentences) {
        match proof_of(entry, sentence) {
            Route::Built(proof) => proofs.push(proof),
            Route::Declined(d) => return Route::Declined(d),
        }
    }
    Route::Built(Item {
        module,
        sentences,
        proofs,
    })
}

/// One `lean-proof` entry as Lean text. A bridge, named in full,
/// `lean-bridges/counting/pascal`, states the item as the build writes it,
/// so it is applied to the item's letters and hypotheses in order; any
/// other entry is Mathlib's proof, written in Lean already.
fn proof_of(entry: &str, sentence: &Sentence) -> Route<String> {
    if !entry.starts_with(super::names::LEAN_BRIDGES) {
        return Route::Built(entry.to_string());
    }
    let bridge = match super::names::bridge_of(entry) {
        Route::Built(bridge) => bridge,
        Route::Declined(d) => return Route::Declined(d),
    };
    // A group binds its type implicitly, `{G : Type*} [Group G]`, which Lean
    // fills from the arguments after it.
    let mut applied = vec![bridge];
    applied.extend(
        sentence
            .binders
            .iter()
            .filter(|b| {
                !matches!(
                    b,
                    Binder::Letter {
                        ty: LetterType::Group,
                        ..
                    }
                )
            })
            .map(|b| b.name().to_string()),
    );
    Route::Built(applied.join(" "))
}

/// A Lean theorem's declaration, its name taken from its full name.
pub fn declaration(
    sentence: &Sentence,
    proof: &str,
    modules: std::collections::BTreeSet<String>,
) -> super::doc::file::Declaration {
    use super::doc::file::{Binder as Doc, DeclProof, Declaration};
    let short = sentence.decl.rsplit('.').next().unwrap_or(&sentence.decl);
    let mut binders: Vec<Doc> = sentence
        .general
        .iter()
        .map(|g| Doc::Typed {
            text: g.binders(),
            ty: None,
        })
        .collect();
    binders.extend(super::statement::things_binder(
        &sentence.binders,
        &[&sentence.prop],
    ));
    binders.extend(sentence.binders.iter().map(Binder::doc));
    Declaration {
        name: short.to_string(),
        binders,
        says: sentence.prop.clone(),
        proof: DeclProof::Verbatim {
            text: proof.to_string(),
            modules,
        },
    }
}
