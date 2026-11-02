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
    pub prop: String,
    /// Where the item is a corpus theorem whose statement holds several
    /// sentences joined, the projection that takes this one, `.2.1`.
    pub part: String,
    /// The arithmetic the page writes in the whole of the declaration's
    /// statement, what it asks included, which the gate's read-back
    /// compares with what Lean elaborated (`readback`).
    pub arithmetic: std::collections::BTreeMap<String, usize>,
    /// What its general letters range over; None where it has none.
    pub general: Option<General>,
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
        .filter_map(super::statement::introduces_function)
        .filter_map(|(_, ty)| match ty {
            super::expr::LetterType::Function { to, .. } => Some(to),
            _ => None,
        });
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
    let own: Vec<String> = functions
        .iter()
        .filter_map(super::statement::introduces_function)
        .map(|(f, _)| f)
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
        .filter(|(_, s)| super::expr::letter_type(*s) == Num::Int)
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
    let ordered = floor
        || parts.iter().any(|p| {
            matches!(
                p.notation(),
                crate::notations::ORDER | crate::notations::ABSOLUTE_VALUE
            )
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

/// A letter of an item no line introduces, the x of "x ∈ ℚ ↔ …".
pub struct FreeLetter {
    pub name: String,
    /// What it is a number of: ℂ, set.mm's widest, or ℝ where the
    /// statement orders it, since ℂ has no order.
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
                .or_else(|| super::statement::introduces_function(n).map(|(l, _)| l))
                .or_else(|| super::statement::introduces(n).map(|(l, _)| l))
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
            FreeLetter {
                num: if real { Num::Real } else { Num::Complex },
                fixed: fixed.contains(&name),
                name,
            }
        })
        .collect()
}

/// The Lean type the sorts give a letter that is a set, a member of one or
/// a map between sets; None for any other letter.
fn set_type_in(
    sorts: Option<&crate::formula::Sorts>,
    name: &str,
) -> Option<LetterType> {
    sorts
        .and_then(|s| s.get(name))
        .and_then(super::sets::set_letter_type)
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
pub fn item(writer: &Writer, checked: &CheckedCorpus, record: &Record) -> Route<Item> {
    let full = format!("{}/{}", record.module(), record.name);
    let Some(Some(groups)) = checked.library.groups.get(&full) else {
        return Route::no(format!("{full} has no reading as an item"));
    };
    let module = items_module(record);
    let base = format!("{}_{}", prefix(record), snake(&record.name));
    let total: usize = groups.iter().map(|g| g.gives.len()).sum();
    let mut sentences = Vec::new();
    for group in groups.iter() {
        for says in &group.gives {
            let mut w = Writer::new(writer.grammar, writer.templates);
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
            let mut sets: Vec<(String, LetterType)> = free
                .iter()
                .filter_map(|f| {
                    set_type_in(sorts, &f.name).map(|ty| (f.name.clone(), ty))
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
            for n in said.iter().flat_map(|n| n.walk()) {
                let [x, set] = n.children.as_slice() else {
                    continue;
                };
                let member = n.notation() == crate::notations::MEMBERSHIP
                    && x.is_name()
                    && free.iter().any(|f| *f.name == *x.text)
                    && !sets.iter().any(|(s, _)| *s == *x.text);
                if let Some(m) = member.then(|| w.members_of(set)).flatten() {
                    sets.push((x.text.to_string(), LetterType::Member(m)));
                    continue;
                }
                // x ∈ {u, w} where no letter of it has a number's sort, the
                // pair of elements of any sort: each is a thing, and the
                // statement holds of numbers as of any other type.
                let listed = matches!(
                    &*set.notation_name(),
                    "singleton" | "listed-two" | "listed-three" | "listed-four"
                );
                let things: Vec<&Node> =
                    std::iter::once(x).chain(&set.children).collect();
                let of_no_number = |n: &&Node| {
                    n.is_name()
                        && free.iter().any(|f| *f.name == *n.text)
                        && !n.sort.is("number")
                };
                if n.notation() == crate::notations::MEMBERSHIP
                    && listed
                    && things.iter().all(of_no_number)
                {
                    for t in things {
                        if !sets.iter().any(|(s, _)| *s == *t.text) {
                            let ty = LetterType::Member(super::expr::Members::Things);
                            w.letters.insert(t.text.to_string(), ty.clone());
                            sets.push((t.text.to_string(), ty));
                        }
                    }
                }
            }
            let free: Vec<FreeLetter> = free
                .into_iter()
                .filter(|f| !sets.iter().any(|(s, _)| *s == f.name))
                .collect();
            let kind = general_kind(group, says, functions, &free);
            w.general = kind.map(|k| k.num);
            let asked: Vec<Asked> = group
                .wants
                .iter()
                .enumerate()
                .map(|(i, (_, node))| Asked {
                    node,
                    name: format!("h{}", i + 1),
                })
                .collect();
            // A letter of the item that stands for a statement, the P of
            // "P or Q", is a proposition it is stated for.
            let mut statements = Vec::new();
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
                if let Some((letter, ty)) = super::statement::introduces_function(node)
                {
                    // A function into the item's general type gives K.
                    let general = matches!(ty, LetterType::Function { to, .. }
                        if w.general == Some(to));
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
                statements.push(Binder::Letter {
                    name: super::names::letter(name),
                    page: name.clone(),
                    ty: ty.clone(),
                    general: false,
                });
            }
            // A map the item has, `f : D → E`, maps the one set into the
            // other, which its groups leave out as they leave out its type.
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
                if !matches!(
                    w.letters.get(f.text.as_str()),
                    Some(LetterType::Map { .. })
                ) {
                    continue;
                }
                // A set named only in the map's type, the W of `f : X → W`,
                // is a letter of the item all the same.
                for set in [from, to] {
                    let unbound =
                        set.is_name() && !w.letters.contains_key(set.text.as_str());
                    if let Some(ty) =
                        unbound.then(|| set_type_in(sorts, &set.text)).flatten()
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
                let (Route::Built(a), Route::Built(b)) =
                    (w.set_term(from), w.set_term(to))
                else {
                    return Route::no(format!(
                        "{} maps between sets with no Lean form",
                        f.text
                    ));
                };
                let name = super::names::letter(&f.text);
                let domain = a.at(super::expr::MAX);
                statements.push(Binder::Fact {
                    name: format!("h{name}"),
                    says: format!(
                        "Set.MapsTo {name} {domain} {}",
                        b.at(super::expr::MAX)
                    ),
                });
                w.domains.insert(f.text.to_string(), domain);
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
            let binders = match binders(&mut w, &asked) {
                Route::Built(b) => statements.into_iter().chain(b).collect(),
                Route::Declined(d) => return Route::Declined(d),
            };
            let prop = match w.formula(says) {
                Route::Built(p) => p.text,
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
                part: String::new(),
                arithmetic,
                general: kind,
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
    let mut applied = vec![bridge];
    applied.extend(sentence.binders.iter().map(|b| b.name().to_string()));
    Route::Built(applied.join(" "))
}

/// A Lean theorem's declaration, its name taken from its full name.
pub fn declaration(sentence: &Sentence, proof: &str) -> String {
    let short = sentence.decl.rsplit('.').next().unwrap_or(&sentence.decl);
    let mut binders: Vec<String> =
        sentence.general.iter().map(General::binders).collect();
    binders.extend(super::statement::things_binder(&sentence.binders));
    binders.extend(sentence.binders.iter().map(Binder::lean));
    let space = if binders.is_empty() { "" } else { " " };
    format!(
        "theorem {short}{space}{} :\n    {} :=\n  {proof}",
        binders.join(" "),
        sentence.prop
    )
}
