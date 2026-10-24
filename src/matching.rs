//! Matching an item's hypothesis against the fact a step supplies for it.
//!
//! The match is one-way: the item is a pattern whose names stand for
//! anything, and the fact is ground. `mun:stdlib/sets/subset-transitive`
//! assumes X ⊆ Y and Y ⊆ Z, and a step citing it from two lines claiming
//! S ⊆ [a, b] and [a, b] ⊆ ℝ supplies them with X, Y, Z standing for S,
//! [a, b] and ℝ. A name that appears twice must stand for the same thing
//! both times, which is what makes the middle Y load-bearing.
//!
//! A citation may write its instantiation, and the written pairs seed the
//! binding, so they are checked rather than trusted; a citation that writes
//! none is read the same way.

use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use crate::corpus::{Record, RecordKind};
use crate::formula::notation_id::{NotationId, Spelling};
use crate::formula::symbol::Symbol;
use crate::formula::{Binds, ByShape, Node, NodeId, Notation};
use crate::notations::{APPLICATION, APPLICATION_TO_TWO, NUMERAL, PROPERTY_OF};
use crate::regex;

/// Split on the commas outside brackets.
pub fn split_commas(text: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth: i64 = 0;
    let mut start = 0;
    for (i, ch) in text.char_indices() {
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                out.push(&text[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(&text[start..]);
    out.into_iter()
        .filter(|p| !str::trim(p).is_empty())
        .collect()
}

/// What the names of a pattern have been matched to.
pub type Binding = IndexMap<Symbol, Node>;

/// What a match needs to know of the notations: which bind a variable,
/// which apply a property or a function, and which are equations.
#[derive(Clone, Debug, Default)]
pub struct Context {
    pub binders: FxIndexMap<NotationId, Binds>,
    /// For each application, whether it applies a `property` or a
    /// `function`.
    pub props: FxIndexMap<NotationId, String>,
    pub equations: FxIndexSet<NotationId>,
    /// The notations saying a function is a function on a set (`wfn`).
    pub functions_on: FxIndexSet<NotationId>,
    /// The notations writing a sum (`csu`).
    pub sums: FxIndexSet<NotationId>,
    /// The notations saying there is something (`wrex`).
    pub existences: FxIndexSet<NotationId>,
    /// The notations saying something of everything, over a set or not
    /// (`wral`, `wal`).
    pub universals: FxIndexSet<NotationId>,
    /// Each spelling that is another of its notation's with the holes in
    /// another order: `x > 0` is `0 < x` (`turned`).
    pub turned: FxIndexMap<Spelling, Turned>,
    /// Each spelling that, holding another in one hole, is a third: a
    /// product over the set {a, …, b} is the product from a to b (`filled`).
    pub filled: FxIndexMap<Spelling, Vec<Filled>>,
    /// The notations whose holes stand in any order, `commutes any order`:
    /// "A, B, C form a triangle" is "C, A, B form a triangle", and {v, w} is
    /// {w, v}.
    pub unordered: FxIndexSet<NotationId>,
    /// Each operation's identity element, by its spelling, from the
    /// records' `identity` field. It goes without saying wherever it
    /// stands, so every match and comparison reads x + 0 as x (`SYNTAX.md`).
    pub identities: FxIndexMap<Spelling, IdentityElement>,
}

/// The maps every match and comparison looks a notation up in, at each
/// node: hashed by `FxHash`, for short keys the program makes itself and no
/// one chooses to collide, where the default hasher guards against that.
pub type FxIndexMap<K, V> = IndexMap<K, V, rustc_hash::FxBuildHasher>;
pub type FxIndexSet<K> = IndexSet<K, rustc_hash::FxBuildHasher>;

/// The notations of these names, as ids.
fn ids_of(names: IndexSet<String>) -> FxIndexSet<NotationId> {
    names.iter().map(|n| NotationId::of(n)).collect()
}

/// An operation's identity element, and the holes, counted from 0, it may
/// stand in: 0 in either of x + y's, 0 in the second of x − y's.
#[derive(Clone, Debug)]
pub struct IdentityElement {
    pub element: String,
    pub holes: Vec<usize>,
}

impl IdentityElement {
    /// Whether the node is this element, a numeral written as it.
    fn is(&self, node: &Node) -> bool {
        node.children.is_empty()
            && node.notation() == NUMERAL
            && node.text == self.element
    }
}

/// Each operation's identity element, from the `identity` field.
fn identities(
    notations: &[Notation],
    records: &[Record],
) -> FxIndexMap<Spelling, IdentityElement> {
    let mut out = FxIndexMap::default();
    for r in records.iter().filter(|r| r.kind == RecordKind::Notation) {
        let Some(says) = r.field("identity") else {
            continue;
        };
        let patterns: Vec<&Notation> =
            notations.iter().filter(|n| n.name == r.name).collect();
        let says = crate::targets::split_entries(says);
        if says.len() != patterns.len() {
            continue;
        }
        for (pattern, said) in patterns.iter().zip(says) {
            let Some((element, holes)) = crate::targets::identity_said(said) else {
                continue;
            };
            out.insert(
                Spelling::new(pattern.key_id, pattern.literal_id),
                IdentityElement {
                    element: element.to_string(),
                    holes,
                },
            );
        }
    }
    out
}

/// The notations whose record says `commutes any order`. A notation whose
/// two holes may only be exchanged, as `·`'s, is not one: k · 2 and 2k are
/// one number to the elaborator, and the page writes the one it cites.
fn unordered(records: &[Record]) -> IndexSet<String> {
    records
        .iter()
        .filter(|r| r.kind == RecordKind::Notation)
        .filter(|r| {
            crate::targets::commutes_said(r)
                .contains(&Some(crate::targets::Commutes::AnyOrder))
        })
        .map(|r| r.name.clone())
        .collect()
}

/// What a spelling is in its notation's standard order: the literal it is
/// written with there, and which of its own holes, counted from 1, fills
/// each hole of that one.
#[derive(Clone, Debug)]
pub struct Turned {
    pub spelling: Spelling,
    pub places: Vec<usize>,
}

impl Context {
    pub fn new(notations: &[Notation], records: &[Record]) -> Context {
        let (binders, props) = binding_context(notations);
        let filled = filled(notations, records, &binders);
        Context {
            binders,
            props,
            equations: ids_of(equations(records)),
            functions_on: ids_of(functions_on(records)),
            sums: ids_of(sums(records)),
            existences: ids_of(existences(records)),
            universals: ids_of(universals(records)),
            turned: turned(notations, records),
            filled,
            unordered: ids_of(unordered(records)),
            identities: identities(notations, records),
        }
    }

    /// The places of a binder that hold the letters it binds, and those of
    /// the body they are bound in; neither for a notation that binds none.
    pub fn held_body(&self, notation: NotationId) -> (Vec<usize>, Vec<usize>) {
        match self.binders.get(&notation) {
            Some(b) => (b.held.clone(), b.body.clone()),
            None => (Vec::new(), Vec::new()),
        }
    }
}

/// Which notations bind a variable, and which apply a property or a
/// function.
///
/// Both are read from the declarations: a binder is a notation with a
/// `binds` line, and an application is one whose first hole takes a property
/// or a function and whose second takes what that applies to. The second map
/// says which of the two each applies, because a function is read as a
/// family only where a binder applies it to what it binds. Nothing here is
/// known by name.
pub fn binding_context(
    notations: &[Notation],
) -> (
    FxIndexMap<NotationId, Binds>,
    FxIndexMap<NotationId, String>,
) {
    let mut binders = FxIndexMap::default();
    let mut props = FxIndexMap::default();
    for n in notations {
        if let Some(first) = n.holes.first() {
            if (first == "property" || first == "function") && applies_first(n) {
                props.insert(n.key_id, first.clone());
            }
        }
        if let Some(b) = n.node_binds() {
            binders.insert(n.key_id, b);
        }
    }
    (binders, props)
}

/// The names free in `node`: those no binder in it holds, `binders` being
/// the binding notations as `binding_context` reads them.
pub fn free_names(
    node: &Node,
    binders: &FxIndexMap<NotationId, Binds>,
) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    free_names_under(node, binders, &mut Vec::new(), &mut out);
    out
}

/// `free_names` of a part, `bound` holding the letters the binders around
/// it hold.
fn free_names_under(
    node: &Node,
    binders: &FxIndexMap<NotationId, Binds>,
    bound: &mut Vec<Symbol>,
    out: &mut BTreeSet<String>,
) {
    if node.is_name() {
        if !bound.contains(&node.text) {
            out.insert(node.text.to_string());
        }
        return;
    }
    let binds = binders.get(&node.notation());
    for (at, child) in node.children.iter().enumerate() {
        let Some(binds) = binds else {
            free_names_under(child, binders, bound, out);
            continue;
        };
        if binds.held.contains(&at) {
            continue;
        }
        if binds.body.contains(&at) {
            let held: Vec<Symbol> = binds
                .held
                .iter()
                .filter_map(|&h| node.children.get(h))
                .filter(|h| h.is_name())
                .map(|h| h.text)
                .collect();
            let depth = bound.len();
            bound.extend(held);
            free_names_under(child, binders, bound, out);
            bound.truncate(depth);
            continue;
        }
        free_names_under(child, binders, bound, out);
    }
}

/// The notation's second hole takes what its first applies to: `f(x)` puts
/// an α where f is a function from α, and `P(x)` where P is a property of
/// α. `f is a function on X` and `f : X → Y` take a set of α there, and say
/// something of f rather than apply it.
fn applies_first(n: &Notation) -> bool {
    let Some(sort) = &n.sort else {
        return false;
    };
    let Some((holes, _)) = sort.rsplit_once(" → ") else {
        return false;
    };
    let holes: Vec<&str> = holes.split(", ").map(str::trim).collect();
    let domain = holes[0]
        .strip_prefix("function from ")
        .and_then(|rest| rest.split_once(" to "))
        .map(|(from, _)| from)
        .or_else(|| holes[0].strip_prefix("property of "));
    domain.is_some() && holes.get(1).copied() == domain
}

/// The occurrences of a property that may decide what it stands for.
///
/// Only one may: the occurrence inside the braces, applied to the very
/// variable the braces bind. There the answer is forced, because a property
/// is introduced before the braces open and so cannot mention what they
/// bind, and every occurrence of that variable in the condition must
/// therefore be the hole. An occurrence outside is applied to an ordinary
/// name the property is allowed to mention, where several readings would
/// fit, so it is checked against what the inside one decided and never
/// allowed to decide.
pub fn binding_sites(
    pattern: &Node,
    ctx: &Context,
    bound: &[Symbol],
    out: &mut IndexSet<NodeId>,
) {
    if ctx.props.contains_key(&pattern.notation())
        && pattern.children.len() == 2
        && pattern.children[1].is_name()
        && bound.contains(&pattern.children[1].text)
    {
        out.insert(pattern.id());
    }
    let (held, body) = ctx.held_body(pattern.notation());
    let own: Vec<Symbol> = held
        .iter()
        .filter(|&&at| pattern.children[at].is_name())
        .map(|&at| pattern.children[at].text)
        .collect();
    for (i, child) in pattern.children.iter().enumerate() {
        if body.contains(&i) {
            let mut inner = bound.to_vec();
            inner.extend(own.iter().cloned());
            binding_sites(child, ctx, &inner, out);
        } else {
            binding_sites(child, ctx, bound, out);
        }
    }
}

regex!(WCEQ, r"^wceq\b");

/// The notations that are equations, taken from what they target in the
/// kernel, `wceq`, rather than named here. An equation's two sides say the
/// same read either way round (`SYNTAX.md`).
pub fn equations(records: &[Record]) -> IndexSet<String> {
    records
        .iter()
        .filter(|r| {
            r.kind == RecordKind::Notation
                && WCEQ.is_match(str::trim(r.field_or_empty("metamath")))
        })
        .map(|r| r.name.clone())
        .collect()
}

/// A target with its holes blanked, and the hole each blank held:
/// `_2 _1 clt wbr` is `_ _ clt wbr` with holes 2 and 1.
fn blanked(target: &str) -> (String, Vec<usize>) {
    let mut holes = Vec::new();
    let shape: Vec<&str> = target
        .split_whitespace()
        .map(|t| match t.strip_prefix('_').and_then(|n| n.parse().ok()) {
            Some(n) => {
                holes.push(n);
                "_"
            }
            None => t,
        })
        .collect();
    (shape.join(" "), holes)
}

/// Whether a target's holes stand in order, `_1 _2 …`.
fn in_order(holes: &[usize]) -> bool {
    holes.iter().enumerate().all(|(at, &h)| h == at + 1)
}

/// Each pattern whose target is another pattern's with the holes in another
/// order, or in the same order, and how its holes stand in that one. Two
/// such patterns are one term in the kernel, and so one term to compare.
///
/// Within a record: `_ > _` targets `_2 _1 clt wbr`, which is `_ < _`'s
/// `_1 _2 clt wbr` with the two holes exchanged, so x > 0 and 0 < x are one.
/// The pattern whose holes stand in order is the standard one.
///
/// Across records: `x²` (superscript) and `x^2` (power) both target
/// `_1 _2 cexp co`, and `if A then B` and `A → B` both `_1 _2 wi`, so a
/// record stating xⁿ is cited at x², and one stating A → B at a conditional.
/// The record first in the database is the standard one.
///
/// Which is standard is taken from what the database targets rather than
/// named here.
fn turned(notations: &[Notation], records: &[Record]) -> FxIndexMap<Spelling, Turned> {
    let mut out = FxIndexMap::default();
    // The first in-order pattern of each target shape, across records.
    let mut first_of: FxIndexMap<String, Spelling> = FxIndexMap::default();
    for r in records.iter().filter(|r| r.kind == RecordKind::Notation) {
        let targets: Vec<&str> = r
            .field_or_empty("target")
            .split(", ")
            .map(str::trim)
            .collect();
        let patterns: Vec<&Notation> =
            notations.iter().filter(|n| n.name == r.name).collect();
        if targets.len() != patterns.len() {
            continue;
        }
        let read: Vec<(String, Vec<usize>)> =
            targets.iter().map(|t| blanked(t)).collect();
        for (i, (shape, holes)) in read.iter().enumerate() {
            if holes.is_empty() || !in_order(holes) {
                continue;
            }
            match first_of.get(shape) {
                Some(standard)
                    if standard.notation != patterns[i].spelling().notation =>
                {
                    out.insert(
                        patterns[i].spelling(),
                        Turned {
                            spelling: *standard,
                            places: holes.clone(),
                        },
                    );
                }
                Some(_) => {}
                None => {
                    first_of.insert(shape.clone(), patterns[i].spelling());
                }
            }
        }
        for (i, (shape, holes)) in read.iter().enumerate() {
            if holes.is_empty() || in_order(holes) {
                continue;
            }
            let standard = read.iter().enumerate().find(|(j, (other, theirs))| {
                *j != i && other == shape && in_order(theirs)
            });
            if let Some((j, _)) = standard {
                out.insert(
                    patterns[i].spelling(),
                    Turned {
                        spelling: patterns[j].spelling(),
                        places: holes.clone(),
                    },
                );
            }
        }
    }
    // A pattern turned to its record's standard, where that standard is
    // itself another record's pattern, goes to the other's standard at once.
    let across: FxIndexMap<Spelling, Spelling> = out
        .iter()
        .filter(|(_, t)| in_order(&t.places))
        .map(|(from, t)| (*from, t.spelling))
        .collect();
    for t in out.values_mut() {
        if let Some(standard) = across.get(&t.spelling) {
            t.spelling = *standard;
        }
    }
    out
}

/// Where a part of the standard pattern comes from, in a tree of a pattern
/// that holds another in one hole (`Filled`): a part of the outer pattern
/// or of the inner one, by its hole counted from 1.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Source {
    Outer(usize),
    Inner(usize),
}

/// A pattern that, holding a second one in one hole, is a third pattern's
/// term: `∏(k ∈ {a, …, b}) t`, product-over holding a range, is
/// `∏(k = a to b) t`.
#[derive(Clone, Debug)]
pub struct Filled {
    /// The outer pattern's hole, counted from 1, that the inner one fills.
    pub hole: usize,
    /// The inner pattern.
    pub inner: Spelling,
    /// The pattern the two are, which is the one they are compared in.
    pub standard: Spelling,
    /// The part each hole of the standard pattern takes, in its order.
    pub places: Vec<Source>,
}

/// One token of a target: a word of set.mm's, or a hole by its number.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Token<'t> {
    Word(&'t str),
    Hole(usize),
}

/// A pattern with its target read as tokens, where each hole stands once.
struct Targeted<'t> {
    spelling: Spelling,
    tokens: Vec<Token<'t>>,
    holes: usize,
}

/// The target's tokens, where it writes each of its holes once.
fn tokens_of(target: &str) -> Option<(Vec<Token<'_>>, usize)> {
    let tokens: Vec<Token> = target
        .split_whitespace()
        .map(|t| match t.strip_prefix('_').and_then(|n| n.parse().ok()) {
            Some(n) => Token::Hole(n),
            None => Token::Word(t),
        })
        .collect();
    let mut holes: Vec<usize> = tokens
        .iter()
        .filter_map(|t| match t {
            Token::Hole(n) => Some(*n),
            Token::Word(_) => None,
        })
        .collect();
    let count = holes.len();
    holes.sort_unstable();
    holes.dedup();
    (holes.len() == count && holes.iter().enumerate().all(|(at, &h)| h == at + 1))
        .then_some((tokens, count))
}

/// The words of a target with every hole blanked, as `blanked` writes them.
fn shape_of<'t>(tokens: impl Iterator<Item = Token<'t>>) -> String {
    tokens
        .map(|t| match t {
            Token::Word(w) => w,
            Token::Hole(_) => "_",
        })
        .collect::<Vec<&str>>()
        .join(" ")
}

/// Each pattern that, with another pattern in one of its holes, is a third
/// pattern's target, the holes read in that one's order. The two trees are
/// one term in the kernel, and so one term to compare, in the third
/// pattern: product-over targets `_2 _3 _1 cprod`, a range `_1 _2 cfz co`,
/// and the range in the set's hole is `_2 _3 cfz co _4 _1 cprod`, which is
/// product's target, so `∏(k ∈ {a, …, b}) t` is `∏(k = a to b) t`.
///
/// Which is standard is taken from what the database targets rather than
/// named here: the pattern whose target is the whole, since the outer one
/// may hold any set and is the whole only where it holds the inner.
///
/// Only a whole that binds a letter is read so: a sum or a product written
/// over a set and over a range, two ways a reader writes where its letter
/// runs. A divisibility of a difference is a congruence in the kernel too,
/// and |P − Q| a distance, but the page says each as its own claim, and
/// they are compared as written.
fn filled(
    notations: &[Notation],
    records: &[Record],
    binders: &FxIndexMap<NotationId, Binds>,
) -> FxIndexMap<Spelling, Vec<Filled>> {
    let mut all: Vec<Targeted> = Vec::new();
    for r in records.iter().filter(|r| r.kind == RecordKind::Notation) {
        let targets: Vec<&str> = r
            .field_or_empty("target")
            .split(", ")
            .map(str::trim)
            .collect();
        let patterns: Vec<&Notation> =
            notations.iter().filter(|n| n.name == r.name).collect();
        if targets.len() != patterns.len() {
            continue;
        }
        for (target, pattern) in targets.iter().zip(patterns) {
            if let Some((tokens, holes)) = tokens_of(target) {
                if holes > 0 {
                    all.push(Targeted {
                        spelling: pattern.spelling(),
                        tokens,
                        holes,
                    });
                }
            }
        }
    }
    let mut by_shape: FxIndexMap<String, Vec<usize>> = FxIndexMap::default();
    for (at, t) in all.iter().enumerate() {
        by_shape
            .entry(shape_of(t.tokens.iter().copied()))
            .or_default()
            .push(at);
    }
    let mut out: FxIndexMap<Spelling, Vec<Filled>> = FxIndexMap::default();
    for outer in &all {
        for hole in 1..=outer.holes {
            for inner in &all {
                if inner.spelling.notation == outer.spelling.notation {
                    continue;
                }
                // The tokens with the inner target in the hole, each hole
                // with the part it is.
                let mut spliced: Vec<(Token, Option<Source>)> = Vec::new();
                for &t in &outer.tokens {
                    match t {
                        Token::Hole(n) if n == hole => {
                            spliced.extend(inner.tokens.iter().map(|&i| match i {
                                Token::Hole(m) => (i, Some(Source::Inner(m))),
                                Token::Word(_) => (i, None),
                            }))
                        }
                        Token::Hole(n) => spliced.push((t, Some(Source::Outer(n)))),
                        Token::Word(_) => spliced.push((t, None)),
                    }
                }
                let shape = shape_of(spliced.iter().map(|(t, _)| *t));
                for &at in by_shape.get(&shape).into_iter().flatten() {
                    let standard = &all[at];
                    if standard.spelling.notation == outer.spelling.notation
                        || standard.spelling.notation == inner.spelling.notation
                        || !binders.contains_key(&standard.spelling.notation)
                    {
                        continue;
                    }
                    let mut places = vec![Source::Outer(0); standard.holes];
                    let pairs = standard.tokens.iter().zip(&spliced).filter_map(
                        |(t, (_, from))| match (t, from) {
                            (Token::Hole(n), Some(from)) => Some((*n, *from)),
                            _ => None,
                        },
                    );
                    for (n, from) in pairs {
                        places[n - 1] = from;
                    }
                    out.entry(outer.spelling).or_default().push(Filled {
                        hole,
                        inner: inner.spelling,
                        standard: standard.spelling,
                        places,
                    });
                }
            }
        }
    }
    out
}

/// The tree with each spelling put in its standard one (`Context::turned`,
/// `Context::filled`), as two trees are compared: `x > 0` read as `0 < x`,
/// x² as x^2, `∏(k ∈ {1, …, n}) k` as `∏(k = 1 to n) k`. A message that
/// prints a tree read so prints the standard spelling.
pub fn standard(node: &Node, ctx: &Context) -> Node {
    if ctx.turned.is_empty() && ctx.filled.is_empty() {
        return node.clone();
    }
    turned_to_standard(node, ctx).unwrap_or_else(|| node.clone())
}

/// What a node is in its standard spelling, where it is another's.
enum Standard<'c> {
    Turned(&'c Turned),
    Filled(&'c Filled),
}

/// `standard` of a tree that has a spelling to turn somewhere in it; None
/// for one that has none, which is kept as it is, with what it was read from.
fn turned_to_standard(node: &Node, ctx: &Context) -> Option<Node> {
    let turned: Vec<Option<Node>> = node
        .children
        .iter()
        .map(|c| turned_to_standard(c, ctx))
        .collect();
    let filled = ctx.filled.get(&node.spelling()).and_then(|all| {
        all.iter().find(|f| {
            node.children
                .get(f.hole - 1)
                .is_some_and(|c| c.spelling() == f.inner)
        })
    });
    let here = match filled {
        Some(f) => Some(Standard::Filled(f)),
        None => ctx
            .turned
            .get(&node.spelling())
            .filter(|t| t.places.len() == node.children.len())
            .map(Standard::Turned),
    };
    if here.is_none() && turned.iter().all(Option::is_none) {
        return None;
    }
    let children: Vec<Node> = turned
        .into_iter()
        .zip(&node.children)
        .map(|(t, c)| t.unwrap_or_else(|| c.clone()))
        .collect();
    Some(match here {
        Some(Standard::Turned(t)) => {
            let placed = t.places.iter().map(|&p| children[p - 1].clone()).collect();
            Node::of(t.spelling, node.sort.clone(), placed)
        }
        Some(Standard::Filled(f)) => {
            let inner = &children[f.hole - 1];
            let placed = f
                .places
                .iter()
                .map(|p| match *p {
                    Source::Outer(n) => children[n - 1].clone(),
                    Source::Inner(n) => inner.children[n - 1].clone(),
                })
                .collect();
            Node::of(f.standard, node.sort.clone(), placed)
        }
        None => node.with_children(children),
    })
}

/// The notations whose `metamath` is set.mm's `Fn`: what a define with a
/// parameter says of its function.
pub fn functions_on(records: &[Record]) -> IndexSet<String> {
    records
        .iter()
        .filter(|r| {
            r.kind == RecordKind::Notation
                && str::trim(r.field_or_empty("metamath")) == "wfn"
        })
        .map(|r| r.name.clone())
        .collect()
}

/// The notations whose `metamath` is set.mm's `csu`, a sum over some range.
pub fn sums(records: &[Record]) -> IndexSet<String> {
    records
        .iter()
        .filter(|r| {
            r.kind == RecordKind::Notation
                && str::trim(r.field_or_empty("metamath")).starts_with("csu ")
        })
        .map(|r| r.name.clone())
        .collect()
}

/// The notations saying there is something: their `metamath` is `wrex`,
/// once or nested, over whatever set.
pub fn existences(records: &[Record]) -> IndexSet<String> {
    records
        .iter()
        .filter(|r| {
            r.kind == RecordKind::Notation
                && str::trim(r.field_or_empty("metamath")).starts_with("wrex")
        })
        .map(|r| r.name.clone())
        .collect()
}

/// The notations saying something of everything: their `metamath` is
/// `wral`, once or nested, over whatever set, or `wal`, over no set.
pub fn universals(records: &[Record]) -> IndexSet<String> {
    records
        .iter()
        .filter(|r| {
            let metamath = str::trim(r.field_or_empty("metamath"));
            r.kind == RecordKind::Notation
                && (metamath.starts_with("wral") || metamath.starts_with("wal"))
        })
        .map(|r| r.name.clone())
        .collect()
}

/// A claim whose notation says its parts stand in no order (`commutes any
/// order`), read in each order of its parts; any other claim as it stands.
/// The ways b's parts may stand against a's: as written, and turned round
/// where a is an equation. Where a's notation is unordered its parts are
/// paired in any order instead (`fit_in_any_order`, `parts_related`).
fn orders(a: &Node, b: &Node, ctx: &Context) -> Vec<Vec<Node>> {
    if ctx.equations.contains(&a.notation()) && b.children.len() == 2 {
        let mut turned = b.children.clone();
        turned.reverse();
        return vec![b.children.clone(), turned];
    }
    vec![b.children.clone()]
}

/// Bind the pattern's variables so that it becomes the ground tree.
///
/// Returns the binding, or None where the pattern does not fit. Two trees
/// are compared up to the letters they bind and the order of an equation's
/// sides (`alike`), and a binder of the pattern's may take the ground's
/// letter (`bound_as`).
pub fn match_tree(
    pattern: &Node,
    ground: &Node,
    binding: &Binding,
    variables: &BTreeSet<String>,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
) -> Option<Binding> {
    // Most matches are refused at the root, by a notation that differs, and
    // the binding is copied only for one that is not.
    if refused_at_root(pattern, ground, binding, variables, ctx) {
        return None;
    }
    let mut out = binding.clone();
    fit(pattern, ground, &mut out, variables, sites, ctx).then_some(out)
}

/// The pattern is one of the variables being bound.
fn is_variable(pattern: &Node, variables: &BTreeSet<String>) -> bool {
    pattern.is_name() && variables.contains(pattern.text.as_str())
}

/// The pattern applies a property or function that is one of the variables.
fn applies_variable(
    pattern: &Node,
    variables: &BTreeSet<String>,
    ctx: &Context,
) -> bool {
    ctx.props.contains_key(&pattern.notation())
        && pattern.children.len() == 2
        && pattern.children[0].is_name()
        && variables.contains(pattern.children[0].text.as_str())
}

/// The two nodes differ in what they are, so no binding makes one the other.
fn differs(pattern: &Node, ground: &Node) -> bool {
    pattern.notation() != ground.notation()
        || pattern.text != ground.text
        || pattern.children.len() != ground.children.len()
}

/// `fit` would give back false at the root without copying the binding.
fn refused_at_root(
    pattern: &Node,
    ground: &Node,
    binding: &Binding,
    variables: &BTreeSet<String>,
    ctx: &Context,
) -> bool {
    !is_variable(pattern, variables)
        && !applies_variable(pattern, variables, ctx)
        && differs(pattern, ground)
        && !holds_identity(pattern, binding, variables, ctx)
        && identity_kept(ground, ctx).is_none()
}

/// Whether a pattern's operation holds its identity element in a hole:
/// written there, or a variable there the binding holds as it.
fn holds_identity(
    pattern: &Node,
    binding: &Binding,
    variables: &BTreeSet<String>,
    ctx: &Context,
) -> bool {
    identity_of(pattern, ctx).is_some_and(|law| {
        law.holes.iter().any(|&hole| {
            let unit = &pattern.children[hole];
            law.is(unit)
                || (is_variable(unit, variables)
                    && binding.get(&unit.text).is_some_and(|b| law.is(b)))
        })
    })
}

/// The identity element of the operation a node applies, where it has one
/// and two holes.
fn identity_of<'c>(node: &Node, ctx: &'c Context) -> Option<&'c IdentityElement> {
    if node.children.len() != 2 {
        return None;
    }
    ctx.identities.get(&node.spelling())
}

/// Every binding under which the pattern fits the ground, each once: what
/// `match_tree` gives back, and the others it would have found had it gone
/// on. A listing whose elements stand in any order, or an equation, inside
/// a claim may fit more than one way, and which way is the citation is
/// decided by the rest of the claim and by the cited lines: `{a, b} ⊆ S`
/// against `{v, w} ⊆ S` with a := v and with a := w.
pub fn match_every_way(
    pattern: &Node,
    ground: &Node,
    binding: &Binding,
    variables: &BTreeSet<String>,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
) -> Vec<Binding> {
    let mut found: Vec<Binding> = Vec::new();
    if refused_at_root(pattern, ground, binding, variables, ctx) {
        return found;
    }
    let mut keys: Vec<Vec<(Symbol, ByShape)>> = Vec::new();
    let mut out = binding.clone();
    let mut keep = |b: &mut Binding| {
        let key: Vec<(Symbol, ByShape)> =
            b.iter().map(|(k, v)| (*k, v.by_shape())).collect();
        if !keys.contains(&key) {
            keys.push(key);
            found.push(b.clone());
        }
        false
    };
    fit_each(pattern, ground, &mut out, variables, sites, ctx, &mut keep);
    found
}

/// What is done with a binding under which a pattern fits: true ends the
/// search with it, false asks for the next way the pattern fits.
type Then<'t> = dyn FnMut(&mut Binding) -> bool + 't;

/// `match_tree` into one binding, growing it in place: the first way the
/// pattern fits.
fn fit(
    pattern: &Node,
    ground: &Node,
    binding: &mut Binding,
    variables: &BTreeSet<String>,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
) -> bool {
    fit_each(pattern, ground, binding, variables, sites, ctx, &mut |_| {
        true
    })
}

/// Each way the pattern fits the ground, handed to `then` in turn until it
/// gives back true.
///
/// Matching only ever adds a variable the binding does not have, and adds it
/// at the end, so an attempt that fails is undone by cutting the binding
/// back to the length it had before. Copying the binding at every node of
/// every attempt instead measured at a quarter of a check. When this gives
/// back false, the binding is as it was.
fn fit_each(
    pattern: &Node,
    ground: &Node,
    binding: &mut Binding,
    variables: &BTreeSet<String>,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
    then: &mut Then,
) -> bool {
    let before = binding.len();
    if is_variable(pattern, variables) {
        if let Some(seen) = binding.get(&pattern.text) {
            return alike(seen, ground, ctx, &IndexMap::new(), &IndexMap::new())
                && then(binding);
        }
        binding.insert(pattern.text, ground.clone());
        return then_kept(true, before, binding, then);
    }
    if applies_variable(pattern, variables, ctx) {
        if ctx.props.get(&pattern.notation()).map(String::as_str) != Some("function") {
            let fits = property(pattern, ground, binding, sites, ctx);
            return then_kept(fits, before, binding, then);
        }
        if let Some(fits) = family(pattern, ground, binding, variables, sites, ctx) {
            return then_kept(fits, before, binding, then);
        }
        if let Some(rule) = applied_as_rule(pattern, ground, binding, sites, ctx) {
            // t is first the function the ground applies, and then the rule
            // that applies it: f stands for t only where the item's other
            // mentions of t say f's domain, and a product over a part of
            // that domain takes the rule x ↦ f(x) over the part.
            if fit_structure(pattern, ground, binding, variables, sites, ctx, then) {
                return true;
            }
            binding.insert(pattern.children[0].text, rule);
            return then_kept(true, before, binding, then);
        }
    }
    fit_structure(pattern, ground, binding, variables, sites, ctx, then)
}

/// The rule `x ↦ g(x)` a function letter t of the pattern may stand for at
/// `t(x)` under a binder of x, where the ground applies a function of the
/// page, g, to the same x: the other way `family` leaves to the written
/// match, which makes t g itself. None where t is bound already, x is not
/// a letter a binder binds there, or the ground is no such application.
fn applied_as_rule(
    pattern: &Node,
    ground: &Node,
    binding: &Binding,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
) -> Option<Node> {
    let name = &pattern.children[0].text;
    let arg = read_at(&pattern.children[1], binding, ctx);
    let plain = ground.notation() == pattern.notation()
        && ground.children.len() == 2
        && ground.children[1].same_shape(&arg);
    (plain
        && !binding.contains_key(name)
        && sites.contains(&pattern.id())
        && arg.is_name())
    .then(|| Node::property(&arg.text, ground.clone()))
}

/// The ground written in the pattern's spelling, where the ground is the
/// standard form of that spelling holding another in one hole and the
/// pattern holds something else there: `∏(k = 2 to n) k` read as
/// `∏(k ∈ {2, …, n}) k` for a pattern `∏(x ∈ X) x`, so that X is bound to
/// the range. None where the pattern's spelling is the ground's, or the
/// ground is no such standard form.
fn unfilled(pattern: &Node, ground: &Node, ctx: &Context) -> Option<Node> {
    if pattern.spelling() == ground.spelling() {
        return None;
    }
    let f = ctx.filled.get(&pattern.spelling())?.iter().find(|f| {
        f.standard == ground.spelling() && f.places.len() == ground.children.len()
    })?;
    let held = pattern.children.get(f.hole - 1)?;
    if held.spelling() == f.inner {
        return None;
    }
    let from = |wanted: Source| {
        f.places
            .iter()
            .position(|&p| p == wanted)
            .map(|at| ground.children[at].clone())
    };
    let inner_holes = f
        .places
        .iter()
        .filter_map(|p| match p {
            Source::Inner(n) => Some(*n),
            Source::Outer(_) => None,
        })
        .max()?;
    let inner_children: Vec<Node> = (1..=inner_holes)
        .map(|n| from(Source::Inner(n)))
        .collect::<Option<Vec<Node>>>()?;
    let inner = Node::of(f.inner, held.sort.clone(), inner_children);
    let mut children = Vec::new();
    for n in 1..=pattern.children.len() {
        if n == f.hole {
            children.push(inner.clone());
        } else {
            children.push(from(Source::Outer(n))?);
        }
    }
    Some(Node::of(pattern.spelling(), ground.sort.clone(), children))
}

/// Each way the pattern fits the ground part by part, as `fit_each` does
/// once a variable at the root has had its turn, handed to `then` in turn.
fn fit_structure(
    pattern: &Node,
    ground: &Node,
    binding: &mut Binding,
    variables: &BTreeSet<String>,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
    then: &mut Then,
) -> bool {
    // A product over a set whose set is still to be bound meets a product
    // from a to b as the product over {a, …, b}, the form it is the
    // standard of (`Context::filled`).
    if let Some(open) = unfilled(pattern, ground, ctx) {
        return fit_structure(pattern, &open, binding, variables, sites, ctx, then);
    }
    // Whether the pattern fitted as written, its parts against the ground's,
    // in some way. An identity element is read away only where it did not.
    let mut written = false;
    if !differs(pattern, ground) {
        let pattern = bound_as(pattern, ground, variables, ctx);
        // The letters a binder binds are paired before what it binds them
        // over, wherever the notation writes them: ∫(a to x) f(t) dt names
        // its letter last, and f(t) read before t is paired would make f
        // a function of a letter it does not mention.
        let (held, _) = ctx.held_body(pattern.notation());
        let mut first: Vec<usize> = held.clone();
        // A part holding an occurrence that decides what a function letter
        // stands for is paired before the parts that only check it:
        // t(k + 1) − t(k) reads t off t(k), wherever t(k) is written.
        let rest: Vec<usize> = (0..pattern.children.len())
            .filter(|i| !held.contains(i))
            .collect();
        let (deciding, checking): (Vec<usize>, Vec<usize>) = rest
            .into_iter()
            .partition(|&i| holds_site(&pattern.children[i], sites));
        first.extend(deciding);
        first.extend(checking);
        let mut marked = |b: &mut Binding| {
            written = true;
            then(b)
        };
        if ctx.unordered.contains(&pattern.notation()) {
            let mut pairing = Pairing {
                pattern: &pattern.children,
                ground: &ground.children,
                order: &first,
                taken: vec![false; ground.children.len()],
            };
            if fit_in_any_order(
                &mut pairing,
                0,
                binding,
                variables,
                sites,
                ctx,
                &mut marked,
            ) {
                return true;
            }
        } else {
            for children in orders(&pattern, ground, ctx) {
                let parts = Parts {
                    pattern: &pattern.children,
                    ground: &children,
                    order: &first,
                };
                if fit_parts(&parts, 0, binding, variables, sites, ctx, &mut marked) {
                    return true;
                }
            }
        }
    }
    if written {
        return false;
    }
    // x + 0 is x wherever it stands (`Context::identities`): in the pattern,
    // or in the ground.
    if without_identity(pattern, ground, binding, variables, sites, ctx, then) {
        return true;
    }
    match identity_kept(ground, ctx) {
        Some(kept) => fit_each(pattern, &kept, binding, variables, sites, ctx, then),
        None => false,
    }
}

/// `then` of a binding a fit that takes one way only left, where it fitted;
/// the binding cut back to `before` where it did not, or `then` asked on.
fn then_kept(
    fitted: bool,
    before: usize,
    binding: &mut Binding,
    then: &mut Then,
) -> bool {
    if fitted && then(binding) {
        return true;
    }
    binding.truncate(before);
    false
}

/// A pattern's parts each against the ground's part in the same place, in
/// the order they are paired (`fit_each`'s).
struct Parts<'n> {
    pattern: &'n [Node],
    ground: &'n [Node],
    /// The parts by place, in the order they are paired.
    order: &'n [usize],
}

/// `fit_each` of the parts from `at` on in `parts.order`, every way each
/// fits handed on to the parts after it, and `then` asked of each way they
/// all fit. When this gives back false, the binding is as it was.
fn fit_parts(
    parts: &Parts,
    at: usize,
    binding: &mut Binding,
    variables: &BTreeSet<String>,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
    then: &mut Then,
) -> bool {
    let Some(&i) = parts.order.get(at) else {
        return then(binding);
    };
    fit_each(
        &parts.pattern[i],
        &parts.ground[i],
        binding,
        variables,
        sites,
        ctx,
        &mut |b| fit_parts(parts, at + 1, b, variables, sites, ctx, then),
    )
}

/// A pattern's parts being paired with the ground's where the notation
/// says they stand in any order: the pattern's parts in the order they are
/// paired (`fit`'s), and which of the ground's parts are taken.
struct Pairing<'n> {
    pattern: &'n [Node],
    ground: &'n [Node],
    /// The pattern's parts by place, in the order they are paired.
    order: &'n [usize],
    /// Whether the ground's part at each place is paired already.
    taken: Vec<bool>,
}

/// `fit_each` of the pattern's parts from `at` on in `pairing.order`, each
/// with one of the ground's parts not yet taken, and `then` asked of each
/// pairing that fits whole. A part is tried against each ground part in
/// turn and the rest paired after it, so the orders tried are only those
/// whose first parts fit, and a list of any length is not written out in
/// every order. When this gives back false, the binding is as it was.
fn fit_in_any_order(
    pairing: &mut Pairing,
    at: usize,
    binding: &mut Binding,
    variables: &BTreeSet<String>,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
    then: &mut Then,
) -> bool {
    let Some(&part) = pairing.order.get(at) else {
        return then(binding);
    };
    let (pattern, ground) = (pairing.pattern, pairing.ground);
    for (place, against) in ground.iter().enumerate() {
        if pairing.taken[place] {
            continue;
        }
        pairing.taken[place] = true;
        let done = fit_each(
            &pattern[part],
            against,
            binding,
            variables,
            sites,
            ctx,
            &mut |b| fit_in_any_order(pairing, at + 1, b, variables, sites, ctx, then),
        );
        if done {
            return true;
        }
        pairing.taken[place] = false;
    }
    false
}

/// Whether each of `a`'s parts is paired with one of `b`'s, every one of
/// `b`'s used once, where `related` says which two may pair: a matching
/// found by augmenting paths, so that a listing of any length is compared
/// in every order without each order written out.
fn paired_in_some_order(
    a: &[Node],
    b: &[Node],
    related: &dyn Fn(&Node, &Node) -> bool,
) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let pairs: Vec<Vec<bool>> = a
        .iter()
        .map(|x| b.iter().map(|y| related(x, y)).collect())
        .collect();
    let mut partner: Vec<Option<usize>> = vec![None; b.len()];
    (0..a.len()).all(|i| augmented(i, &pairs, &mut partner, &mut vec![false; b.len()]))
}

/// Whether `a`'s part `i` is given a partner, taking a free one of `b`'s
/// it may pair with or moving the part that holds one to another
/// (`paired_in_some_order`).
fn augmented(
    i: usize,
    pairs: &[Vec<bool>],
    partner: &mut [Option<usize>],
    seen: &mut [bool],
) -> bool {
    for j in 0..pairs[i].len() {
        if !pairs[i][j] || seen[j] {
            continue;
        }
        seen[j] = true;
        if partner[j].is_none_or(|k| augmented(k, pairs, partner, seen)) {
            partner[j] = Some(i);
            return true;
        }
    }
    false
}

/// Whether each of a's parts is `related` to the part of b's that stands
/// against it (`orders`), or, where a's notation says its parts stand in
/// any order, to one of b's parts each.
fn parts_related(
    a: &Node,
    b: &Node,
    ctx: &Context,
    related: &dyn Fn(&Node, &Node) -> bool,
) -> bool {
    if ctx.unordered.contains(&a.notation()) {
        return paired_in_some_order(&a.children, &b.children, related);
    }
    orders(a, b, ctx).iter().any(|kids| {
        a.children
            .iter()
            .zip(kids.iter())
            .all(|(x, y)| related(x, y))
    })
}

/// Whether one of `sites`, the occurrences that may decide a property or
/// function (`binding_sites`), stands in `node`.
fn holds_site(node: &Node, sites: &IndexSet<NodeId>) -> bool {
    !sites.is_empty()
        && (sites.contains(&node.id())
            || node.children.iter().any(|c| holds_site(c, sites)))
}

/// A pattern's operation read with its identity element in one hole, the
/// other hole matched against the ground: a + c against 1 with a := 0.
fn without_identity(
    pattern: &Node,
    ground: &Node,
    binding: &mut Binding,
    variables: &BTreeSet<String>,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
    then: &mut Then,
) -> bool {
    let Some(law) = identity_of(pattern, ctx) else {
        return false;
    };
    for &hole in &law.holes {
        let (unit, kept) = (&pattern.children[hole], &pattern.children[1 - hole]);
        // The element is one the instance has, written or a variable already
        // fixed as it: none is made up to read x as 0 + x.
        let written = law.is(unit)
            || (is_variable(unit, variables)
                && binding.get(&unit.text).is_some_and(|b| law.is(b)));
        if written && fit_each(kept, ground, binding, variables, sites, ctx, then) {
            return true;
        }
    }
    false
}

/// The pattern with the letter it binds spelt as the ground spells it,
/// where the letter is no variable of the pattern's and the ground's letter
/// is free nowhere in it; the pattern as it is otherwise.
///
/// A definition's formula read at a term binds a letter of its own, and a
/// line saying the same thing may bind another: `there is b ∈ G with gH =
/// bH` answers K's `there is g ∈ G with X = gH` at X := gH.
fn bound_as(
    pattern: &Node,
    ground: &Node,
    variables: &BTreeSet<String>,
    ctx: &Context,
) -> Node {
    let (held, body) = ctx.held_body(pattern.notation());
    let mut pattern = pattern.clone();
    for at in held {
        let ours = pattern.children[at].clone();
        let theirs = ground.children[at].clone();
        if !ours.is_name()
            || !theirs.is_name()
            || ours.text == theirs.text
            || variables.contains(ours.text.as_str())
            || pattern.names().contains(theirs.text.as_str())
        {
            continue;
        }
        let mut swap = Binding::new();
        swap.insert(ours.text, theirs.clone());
        let children = pattern
            .children
            .iter()
            .enumerate()
            .map(|(i, c)| {
                if i == at {
                    theirs.clone()
                } else if body.contains(&i) {
                    // Apart from a binder inside that binds the new letter.
                    substitute_apart(c, &swap, ctx)
                } else {
                    c.clone()
                }
            })
            .collect();
        pattern = pattern.with_children(children);
    }
    pattern
}

/// Whether two trees are one formula, spelt alike but for the letters they
/// bind: `there is a ∈ G with Z = aH` and `there is b ∈ G with Z = bH` are
/// one claim, and neither says anything of a or of b.
///
/// A letter one of them binds is paired with the letter the other binds in
/// the same place, and a free letter must be the same letter on both sides,
/// never one the other side binds. An equation is alike either way round
/// (`orders`).
pub fn alike(
    a: &Node,
    b: &Node,
    ctx: &Context,
    ours: &IndexMap<Symbol, Symbol>,
    theirs: &IndexMap<Symbol, Symbol>,
) -> bool {
    if alike_as_written(a, b, ctx, ours, theirs) {
        return true;
    }
    // x + 0 is x wherever it stands (`Context::identities`).
    identity_kept(a, ctx).is_some_and(|k| alike(&k, b, ctx, ours, theirs))
        || identity_kept(b, ctx).is_some_and(|k| alike(a, &k, ctx, ours, theirs))
}

/// The operand an identity element leaves, where `node` is an operation
/// with its identity in a hole the record allows it: x for x + 0. None
/// otherwise. The identity may itself be written with one left out, so
/// a^(0 + 1) leaves a.
fn identity_kept(node: &Node, ctx: &Context) -> Option<Node> {
    let law = identity_of(node, ctx)?;
    law.holes
        .iter()
        .find(|&&hole| {
            let at = &node.children[hole];
            law.is(at) || identity_kept(at, ctx).is_some_and(|k| law.is(&k))
        })
        .map(|&hole| node.children[1 - hole].clone())
}

/// What each identity element dropped between `instance` and `ground`
/// leaves, where the two are one once the elements are dropped (`fit`), each
/// with its own elements dropped first: comparing A − 1·⌊A/1⌋ with A − ⌊A⌋
/// drops 1· from ⌊A/1⌋ and /1 from A, and gives ⌊A⌋ and A. An identity law
/// holds of a number, so each is one a citation must say is a number
/// (`SYNTAX.md`, "An identity element goes without saying").
pub fn identities_dropped(instance: &Node, ground: &Node, ctx: &Context) -> Vec<Node> {
    let mut out = Vec::new();
    dropped_into(instance, ground, ctx, &mut out);
    out
}

fn dropped_into(instance: &Node, ground: &Node, ctx: &Context, out: &mut Vec<Node>) {
    if instance.same_shape(ground) {
        return;
    }
    if !differs(instance, ground) {
        // The parts are paired as the match paired them: an equation's
        // sides either way round, whichever way they are one once their
        // identity elements are dropped.
        let none = IndexMap::new();
        let one =
            |a: &Node, b: &Node| alike(&bare(a, ctx), &bare(b, ctx), ctx, &none, &none);
        let kids = &instance.children;
        let swapped = ctx.equations.contains(&instance.notation())
            && kids.len() == 2
            && !(one(&kids[0], &ground.children[0])
                && one(&kids[1], &ground.children[1]))
            && one(&kids[1], &ground.children[0])
            && one(&kids[0], &ground.children[1]);
        let mut pairs: Vec<(&Node, &Node)> =
            kids.iter().zip(&ground.children).collect();
        if swapped {
            pairs = vec![
                (&kids[1], &ground.children[0]),
                (&kids[0], &ground.children[1]),
            ];
        }
        for (a, b) in pairs {
            dropped_into(a, b, ctx, out);
        }
        return;
    }
    if let Some(kept) = identity_kept(instance, ctx) {
        out.push(bare(&kept, ctx));
        dropped_into(&kept, ground, ctx, out);
    } else if let Some(kept) = identity_kept(ground, ctx) {
        out.push(bare(&kept, ctx));
        dropped_into(instance, &kept, ctx, out);
    }
}

/// A term with every identity element dropped, its parts first.
pub fn bare(node: &Node, ctx: &Context) -> Node {
    if node.children.is_empty() {
        return node.clone();
    }
    let kids: Vec<Node> = node.children.iter().map(|c| bare(c, ctx)).collect();
    let mut out = node.with_children(kids);
    while let Some(kept) = identity_kept(&out, ctx) {
        out = kept;
    }
    out
}

/// `alike`, the two read as written at the head.
fn alike_as_written(
    a: &Node,
    b: &Node,
    ctx: &Context,
    ours: &IndexMap<Symbol, Symbol>,
    theirs: &IndexMap<Symbol, Symbol>,
) -> bool {
    if a.is_name() && b.is_name() {
        if ours.contains_key(&a.text) || theirs.contains_key(&b.text) {
            return ours.get(&a.text) == Some(&b.text)
                && theirs.get(&b.text) == Some(&a.text);
        }
        return a.text == b.text;
    }
    if a.notation() != b.notation()
        || a.text != b.text
        || a.children.len() != b.children.len()
    {
        return false;
    }
    let Some(shape) = ctx.binders.get(&a.notation()) else {
        return parts_related(a, b, ctx, &|x, y| alike(x, y, ctx, ours, theirs));
    };
    let pairs: Vec<(&Node, &Node)> = shape
        .held
        .iter()
        .map(|&at| (&a.children[at], &b.children[at]))
        .collect();
    if pairs.iter().any(|(x, y)| !x.is_name() || !y.is_name()) {
        return a.same_shape(b);
    }
    let mut inner_ours = ours.clone();
    let mut inner_theirs = theirs.clone();
    for (x, y) in &pairs {
        inner_ours.insert(x.text, y.text);
    }
    for (x, y) in &pairs {
        inner_theirs.insert(y.text, x.text);
    }
    a.children
        .iter()
        .zip(b.children.iter())
        .enumerate()
        .all(|(i, (p, q))| {
            if shape.held.contains(&i) {
                return true;
            }
            if shape.body.contains(&i) {
                alike(p, q, ctx, &inner_ours, &inner_theirs)
            } else {
                alike(p, q, ctx, ours, theirs)
            }
        })
}

/// Whether two trees are one formula, compared from the top.
pub fn alike_top(a: &Node, b: &Node, ctx: &Context) -> bool {
    alike(a, b, ctx, &IndexMap::new(), &IndexMap::new())
}

/// Whether `aim` is `start` with one side of the equation `left = right`
/// put for the other at some of the places it stands, every place or fewer,
/// as a `substitute` makes it (`SYNTAX.md`). Either side may be the one
/// `start` holds, and an identity element the putting makes may be left
/// out, as anywhere (`alike`): put in at every place, p(a) = 0 makes
/// p(x) = (x − a)·q(x) + p(a) into p(x) = (x − a)·q(x).
pub fn substituted_in(
    start: &Node,
    aim: &Node,
    left: &Node,
    right: &Node,
    ctx: &Context,
) -> bool {
    put_at_some(start, aim, left, right, ctx)
        || [(left, right), (right, left)].iter().any(|(was, now)| {
            alike_top(&put_everywhere(start, was, now, ctx), aim, ctx)
        })
}

/// `start` with `now` put at every place `was` stands.
pub fn put_everywhere(start: &Node, was: &Node, now: &Node, ctx: &Context) -> Node {
    put_places(start, was, now, ctx).unwrap_or_else(|| start.clone())
}

/// `put_everywhere`, or None where `was` stands nowhere in `start`. A part
/// is a place before the whole is: `0 + 1` holds 1 as its second part, and
/// is 1 itself only with its 0 dropped, which a part standing there needs
/// no one to say.
pub(crate) fn put_places(
    start: &Node,
    was: &Node,
    now: &Node,
    ctx: &Context,
) -> Option<Node> {
    let mut any = false;
    let kids: Vec<Node> = start
        .children
        .iter()
        .map(|c| match put_places(c, was, now, ctx) {
            Some(put) => {
                any = true;
                put
            }
            None => c.clone(),
        })
        .collect();
    if any {
        return Some(start.with_children(kids));
    }
    alike_top(start, was, ctx).then(|| now.clone())
}

/// `substituted_in` put at some of the places, each part compared with its
/// own.
pub fn put_at_some(
    start: &Node,
    aim: &Node,
    left: &Node,
    right: &Node,
    ctx: &Context,
) -> bool {
    if alike_top(start, aim, ctx)
        || alike_top(start, left, ctx) && alike_top(aim, right, ctx)
        || alike_top(start, right, ctx) && alike_top(aim, left, ctx)
    {
        return true;
    }
    if start.notation() == aim.notation()
        && start.text == aim.text
        && !start.children.is_empty()
        && start.children.len() == aim.children.len()
        && parts_related(start, aim, ctx, &|a, b| {
            substituted_in(a, b, left, right, ctx)
        })
    {
        return true;
    }
    identity_kept(start, ctx).is_some_and(|k| substituted_in(&k, aim, left, right, ctx))
        || identity_kept(aim, ctx)
            .is_some_and(|k| substituted_in(start, &k, left, right, ctx))
}

/// P applied to something, where P is one of the pattern's variables.
fn property(
    pattern: &Node,
    ground: &Node,
    binding: &mut Binding,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
) -> bool {
    let name = &pattern.children[0].text;
    let arg = read_at(&pattern.children[1], binding, ctx);
    let Some(stands) = binding.get(name) else {
        if !sites.contains(&pattern.id()) || !arg.is_name() {
            return false; // only the inside occurrence decides
        }
        binding.insert(*name, Node::property(&arg.text, ground.clone()));
        return true;
    };
    if stands.notation() != PROPERTY_OF {
        return false;
    }
    let mut at = Binding::new();
    at.insert(stands.text, arg);
    let filled = substitute_apart(&stands.children[0], &at, ctx);
    alike_top(&filled, ground, ctx)
}

/// What a pattern applying a property says, where the property is one of
/// the variables and the binding already holds it: its body with the
/// pattern's argument in its hole, the argument still a pattern. None for
/// any other pattern.
///
/// A conclusion `P(u)` is offered whole, since what P stands for is not
/// known until the requirement holding the braces decides it; this is what
/// it says once that is decided, so that a claim may take a conjunct of it
/// as it takes a conjunct of any conclusion.
pub fn property_said(
    pattern: &Node,
    binding: &Binding,
    variables: &BTreeSet<String>,
    ctx: &Context,
) -> Option<Node> {
    if !applies_variable(pattern, variables, ctx)
        || ctx.props.get(&pattern.notation()).map(String::as_str) != Some("property")
    {
        return None;
    }
    let stands = binding.get(&pattern.children[0].text)?;
    if stands.notation() != PROPERTY_OF {
        return None;
    }
    let mut at = Binding::new();
    at.insert(stands.text, pattern.children[1].clone());
    Some(substitute_apart(&stands.children[0], &at, ctx))
}

/// What a property or a function is applied to, in the ground's terms.
///
/// Every name in it the match has bound is what it was bound to: an item's
/// `t(n + 1)` asks of the step's summand at m + 1 where n is m, and its
/// `t(k − c)` at k − 1 where c is 1. What is bound to a property is not a
/// term, and is left alone.
fn read_at(arg: &Node, binding: &Binding, ctx: &Context) -> Node {
    let terms: Binding = binding
        .iter()
        .filter(|(_, t)| t.notation() != PROPERTY_OF)
        .map(|(v, t)| (*v, t.clone()))
        .collect();
    substitute_apart(arg, &terms, ctx)
}

/// t applied to something, where t is a function the pattern names.
///
/// Under a binder that applies it to what it binds, t is whatever is summed
/// or said there, read as a term with that variable as its hole: an item
/// summing t(k) over k is about d(k)·10^k − d(k) when that is the step's
/// summand. It is read so only where the term is not itself a function
/// applied to the variable, since there t is simply that function, and the
/// item's other mentions of t, which are not applications, still name it.
///
/// Gives back whether the match fits, where this decides it, growing the
/// binding where it fits; None where it does not decide, and the
/// application is matched as it stands.
fn family(
    pattern: &Node,
    ground: &Node,
    binding: &mut Binding,
    variables: &BTreeSet<String>,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
) -> Option<bool> {
    let name = &pattern.children[0].text;
    let arg = read_at(&pattern.children[1], binding, ctx);
    let stands = binding.get(name).cloned();
    if let Some(stands) = &stands {
        if stands.notation() == PROPERTY_OF {
            let mut at = Binding::new();
            at.insert(stands.text, arg.clone());
            let filled = substitute_apart(&stands.children[0], &at, ctx);
            // At a letter still to be bound, a "there is"'s own in u =
            // E(s), the rule there is matched, which binds it: E(s) with E
            // the map n ↦ 2n meets 2m at s := m.
            if is_variable(&arg, variables) && !binding.contains_key(&arg.text) {
                return Some(fit(&filled, ground, binding, variables, sites, ctx));
            }
            return Some(alike_top(&filled, ground, ctx));
        }
    }
    let plain = ground.notation() == pattern.notation()
        && ground.children.len() == 2
        && ground.children[1].same_shape(&arg);
    if stands.is_none() && sites.contains(&pattern.id()) && arg.is_name() && !plain {
        binding.insert(*name, Node::property(&arg.text, ground.clone()));
        return Some(true);
    }
    None
}

/// What a define with arguments stands for: `define S(m) := …` is a
/// function, and S(t) is its body with t for m; `define G(a, n) := …` is a
/// function of two, and G(s, t) is its body with s for a and t for n.
#[derive(Clone, Debug)]
pub struct Rule {
    /// The arguments, in the order the name takes them, each with its
    /// domain.
    pub params: Vec<crate::corpus::Param>,
    /// The same arguments read where the define is written: each name with
    /// the sort its domain gives it, and the domain.
    pub read: Vec<ParamRead>,
    pub body: Node,
    /// What binds, from the grammar the body was read with
    /// (`Grammar::binders`).
    pub binders: Rc<FxIndexMap<NotationId, Binds>>,
}

/// One argument of a define, read: its name and its domain.
#[derive(Clone, Debug)]
pub struct ParamRead {
    pub name: Node,
    pub domain: Node,
}

impl Rule {
    /// The rule with `values` put for its arguments, in order; None where
    /// the count differs. A letter the body binds is kept apart from the
    /// values: `f(x) := Σ(k = 1 to x) 1/k` at k sums over another letter.
    pub fn at(&self, values: &[Node]) -> Option<Node> {
        if values.len() != self.params.len() {
            return None;
        }
        let mut put = Binding::new();
        for (p, v) in self.params.iter().zip(values) {
            put.insert(Symbol::of(&p.name), v.clone());
        }
        Some(substitute_apart_by(&self.body, &put, &self.binders))
    }
}

/// What a defined name stands for: a term, or a function's rule.
#[derive(Clone, Debug)]
pub enum Defined {
    Term(Node),
    Rule(Rule),
}

pub type Definitions = IndexMap<String, Defined>;

/// The tree with every defined name replaced by the term it names.
///
/// A define abbreviates and asserts nothing, so the two are one formula when
/// two formulas are compared: a step claiming `𝒫X = U ∪ T` and a theorem
/// concluding the same thing with the sets written out say the same thing. A
/// define may be written in terms of an earlier one, so this repeats, and
/// the depth is bounded because nothing stops a file naming something after
/// itself.
///
/// A defined function is read where it is applied: S(k + 1) is the rule with
/// k + 1 for its parameter. Standing alone it is the rule itself, a property
/// with the parameter as its hole, which is what an item's function letter
/// is bound to where the item applies it under a binder. So `f : S → S` and
/// every f(r) lying in S are about one thing, however each is written.
pub fn expand(node: &Node, definitions: &Definitions) -> Node {
    expand_to(node, definitions, 8)
}

fn expand_to(node: &Node, definitions: &Definitions, depth: i32) -> Node {
    if definitions.is_empty() || depth <= 0 {
        return node.clone();
    }
    if node.is_name() {
        match definitions.get(node.text.as_str()) {
            // A function of one argument standing alone is its rule, a
            // property with the argument as its hole. One of two has no such
            // reading, and its name stands as written.
            Some(Defined::Rule(rule)) if rule.params.len() == 1 => {
                return Node::property(
                    &rule.params[0].name,
                    expand_to(&rule.body, definitions, depth - 1),
                );
            }
            Some(Defined::Term(t)) => return expand_to(t, definitions, depth - 1),
            _ => {}
        }
    }
    if matches!(node.notation(), APPLICATION | APPLICATION_TO_TWO)
        && node.children.len() >= 2
        && node.children[0].is_name()
    {
        if let Some(Defined::Rule(rule)) =
            definitions.get(node.children[0].text.as_str())
        {
            let values: Vec<Node> = node.children[1..]
                .iter()
                .map(|c| expand_to(c, definitions, depth))
                .collect();
            if let Some(at) = rule.at(&values) {
                return expand_to(&at, definitions, depth - 1);
            }
        }
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| expand_to(c, definitions, depth))
            .collect(),
    )
}

/// Letters a binder is renamed to, where a value put under it would be
/// caught.
pub fn fresh_letters() -> Vec<String> {
    let mut out: Vec<String> = ('a'..='z').map(|c| c.to_string()).collect();
    out.extend(('a'..='z').map(|c| format!("{c}'")));
    out
}

/// The tree with each bound name replaced by what it stands for, keeping
/// what a binder binds apart from what is put under it, which is the one
/// way a value is put into a tree: K's `there is g ∈ G with X = gH` at
/// X := gH is `there is a ∈ G with
/// gH = aH`, and never `there is g ∈ G with gH = gH`, which catches the g of
/// gH and says something else. A binder whose letter a value mentions is
/// spelt with a letter nothing there uses; one naming a letter the binding
/// replaces keeps it, as the letter is its own inside.
pub fn substitute_apart(node: &Node, binding: &Binding, ctx: &Context) -> Node {
    substitute_apart_by(node, binding, &ctx.binders)
}

/// The tree with each letter a binder in it holds that is one of `clash`
/// spelt with a letter neither `clash` nor `used` has, in the binder and
/// in its body: an item's `for all n ∈ ℕ, f(n) > 0` beside its free n is
/// `for all a ∈ ℕ, f(a) > 0`, so that what a citation puts for the free n
/// is never caught by the binder.
pub fn bound_apart(
    node: &Node,
    clash: &BTreeSet<String>,
    used: &BTreeSet<String>,
    binders: &FxIndexMap<NotationId, Binds>,
) -> Node {
    let held = binders
        .get(&node.notation())
        .map(|b| (b.held.clone(), b.body.clone()));
    let mut renamed = Binding::new();
    let mut spelt: IndexMap<usize, Node> = IndexMap::new();
    if let Some((held, _)) = &held {
        let mut taken: BTreeSet<String> = used.union(clash).cloned().collect();
        taken.extend(node.names().iter().map(|n| n.to_string()));
        for &at in held {
            let var = &node.children[at];
            if !var.is_name() || !clash.contains(var.text.as_str()) {
                continue;
            }
            let letter = fresh_letters()
                .into_iter()
                .find(|c| !taken.contains(c))
                .unwrap_or_default();
            taken.insert(letter.clone());
            let fresh = Node::name(var.sort.clone(), &letter);
            spelt.insert(at, fresh.clone());
            renamed.insert(var.text, fresh);
        }
    }
    let body = held.map(|(_, body)| body).unwrap_or_default();
    let children: Vec<Node> = node
        .children
        .iter()
        .enumerate()
        .map(|(i, c)| {
            if let Some(fresh) = spelt.get(&i) {
                return fresh.clone();
            }
            let c = if body.contains(&i) && !renamed.is_empty() {
                substitute_apart_by(c, &renamed, binders)
            } else {
                c.clone()
            };
            bound_apart(&c, clash, used, binders)
        })
        .collect();
    // A tree no binder in it renames is the tree itself, whose nodes keep
    // their identity (`Node::same`).
    if children.iter().zip(&node.children).all(|(a, b)| a.same(b)) {
        return node.clone();
    }
    node.with_children(children)
}

/// `substitute_apart` with only the table of what binds, which the grammar
/// keeps (`Grammar::binders`), for a place that has no matching context.
pub fn substitute_apart_by(
    node: &Node,
    binding: &Binding,
    binders: &FxIndexMap<NotationId, Binds>,
) -> Node {
    if node.notation() == crate::notations::NAME || node.notation() == NUMERAL {
        return binding
            .get(&node.text)
            .cloned()
            .unwrap_or_else(|| node.clone());
    }
    let (held, body) = match binders.get(&node.notation()) {
        Some(b) => (b.held.clone(), b.body.clone()),
        None => (Vec::new(), Vec::new()),
    };
    if held.is_empty() || held.iter().any(|&at| !node.children[at].is_name()) {
        return node.with_children(
            node.children
                .iter()
                .map(|c| substitute_apart_by(c, binding, binders))
                .collect(),
        );
    }
    let own: BTreeSet<Symbol> = held.iter().map(|&at| node.children[at].text).collect();
    let inner: Binding = binding
        .iter()
        .filter(|(k, _)| !own.contains(*k))
        .map(|(k, v)| (*k, v.clone()))
        .collect();
    let mut used = node.names();
    for v in binding.values() {
        used.extend(v.names());
    }
    let mut spelt: IndexMap<usize, Node> = IndexMap::new();
    let mut renamed = inner.clone();
    for &at in &held {
        let var = &node.children[at];
        if inner
            .values()
            .any(|v| v.names().contains(var.text.as_str()))
        {
            let letter = fresh_letters()
                .into_iter()
                .find(|c| !used.contains(c))
                .unwrap_or_default();
            let fresh = Node::name(var.sort.clone(), &letter);
            used.insert(letter);
            spelt.insert(at, fresh.clone());
            renamed.insert(var.text, fresh);
        }
    }
    let children = node
        .children
        .iter()
        .enumerate()
        .map(|(i, c)| {
            if held.contains(&i) {
                spelt.get(&i).cloned().unwrap_or_else(|| c.clone())
            } else if body.contains(&i) {
                substitute_apart_by(c, &renamed, binders)
            } else {
                substitute_apart_by(c, binding, binders)
            }
        })
        .collect();
    node.with_children(children)
}
