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
use std::ops::Deref;
use std::slice;
use std::sync::Arc;

use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxBuildHasher;

use crate::corpus::{Param, Record, RecordKind};
use crate::formula::notation_id::{NotationId, Spelling};
use crate::formula::symbol::Symbol;
use crate::formula::{Binds, ByShape, Node, NodeId, Notation};
use crate::notations::{
    APPLICATION, APPLICATION_TO_TWO, MAP, MAP_OF_TWO, NAME, NUMERAL, PROPERTY_OF,
};
use crate::targets::Commutes;
use crate::{regex, targets};

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
    /// The notations joining two claims by "and" (`wa`).
    pub conjunctions: FxIndexSet<NotationId>,
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
    /// The notations two of whose holes stand in no order, by those two
    /// places counted from 0, `commutes any order of holes 1 and 2`: a ≡ b
    /// (mod n) is b ≡ a (mod n).
    pub unordered_pairs: FxIndexMap<NotationId, (usize, usize)>,
    /// Each operation's identity element, by its spelling, from the
    /// records' `identity` field. It goes without saying wherever it
    /// stands, so every match and comparison reads x + 0 as x (`SYNTAX.md`).
    pub identities: FxIndexMap<Spelling, IdentityElement>,
}

/// The defines a comparison may read out where two trees differ, by the
/// name each defines (`Reading`): what a citation cites, which the page
/// writes by name and a comparison reads as what it names only where the
/// other tree asks for that.
#[derive(Clone, Debug, Default)]
pub struct Unfolds {
    pub defines: Definitions,
}

/// What a match or a comparison reads its trees with: the notations
/// (`Context`), and the defines it may read out where the two differ
/// (`Unfolds`), none deeper than `budget` on any one path. With no defines
/// the trees are compared as they are written.
#[derive(Clone, Copy)]
pub struct Reading<'a> {
    pub ctx: &'a Context,
    pub unfolds: Option<&'a Unfolds>,
    pub budget: u8,
}

impl<'a> Reading<'a> {
    /// A reading with no defines to read out.
    pub fn plain(ctx: &'a Context) -> Reading<'a> {
        Reading {
            ctx,
            unfolds: None,
            budget: 0,
        }
    }

    /// A reading that may read out the defines `unfolds` holds, as deep
    /// as `expand` reads them.
    pub fn with(ctx: &'a Context, unfolds: &'a Unfolds) -> Reading<'a> {
        Reading {
            ctx,
            unfolds: Some(unfolds),
            budget: 8,
        }
    }

    /// The reading one define deeper along a path, where it may read one
    /// more; None where it has no defines or has read as deep as it may.
    fn deeper(self) -> Option<Reading<'a>> {
        let unfolds = self.unfolds?;
        (self.budget > 0 && !unfolds.defines.is_empty()).then(|| Reading {
            budget: self.budget - 1,
            ..self
        })
    }

    /// The define `node` names at its head, where this reading may read
    /// it out: a name a term or a function of one argument defines, or a
    /// defined function applied to as many values as it takes.
    fn define_at(&self, node: &Node) -> Option<(&'a str, &'a Defined)> {
        let unfolds = self.unfolds?;
        if self.budget == 0 {
            return None;
        }
        let head = match node.is_name() {
            true => node,
            false
                if matches!(node.notation(), APPLICATION | APPLICATION_TO_TWO)
                    && node.children.len() >= 2
                    && node.children[0].is_name() =>
            {
                &node.children[0]
            }
            false => return None,
        };
        let (name, defined) = unfolds.defines.get_key_value(head.text.as_str())?;
        Some((name.as_str(), defined))
    }
}

/// The define at the head of `node` read out one step and put in standard
/// form, with the name it defines: a term for its name; a function of one
/// argument standing alone as its rule, a property with the argument as
/// its hole; a defined function applied, its rule at the values; a defined
/// map applied, the map's rule at the values. None where the head is no
/// define this reading may read out, a function of several arguments
/// stands alone, or a name that is no map is applied.
fn unfold_head(node: &Node, ctx: Reading<'_>) -> Option<(Node, String)> {
    let (name, defined) = ctx.define_at(node)?;
    let read = match (defined, node.is_name()) {
        (Defined::Term(term), true) => term.clone(),
        (Defined::Rule(rule), true) => {
            let [param] = rule.params.as_slice() else {
                return None;
            };
            Node::property(&param.name, rule.body.clone())
        }
        (Defined::Rule(rule), false) => rule.at(&node.children[1..])?,
        // A name a map defines, applied, is the map applied, which reads as
        // its rule at the values (`map_applied`): p(t) with p := (s ∈ A ↦
        // f(s)) is f(t).
        (Defined::Term(term), false) => {
            let mut applied = vec![term.clone()];
            applied.extend(node.children[1..].iter().cloned());
            map_applied(&node.with_children(applied), ctx.ctx)?
        }
    };
    Some((standard(&read, ctx.ctx), name.to_string()))
}

/// `node` with each of its parts whose head is a define read out, put in
/// standard form again, where reading a part out changes how the node
/// itself is spelt: `∏(k ∈ R) k` with R := {1, …, n} is the product from 1
/// to n, and `x + Z` with Z := 0 holds its identity. With each part read
/// out, by its place in `tree`. None where no part's head is a define this
/// reading may read out.
fn parts_unfolded(
    node: &Node,
    tree: Tree,
    ctx: Reading<'_>,
) -> Option<(Node, Vec<Unfold>)> {
    let mut read = Vec::new();
    let mut kids = Vec::with_capacity(node.children.len());
    for (i, child) in node.children.iter().enumerate() {
        match unfold_head(child, ctx) {
            Some((part, name)) => {
                read.push(Unfold {
                    name,
                    tree,
                    at: vec![i],
                    read: part.clone(),
                });
                kids.push(part);
            }
            None => kids.push(child.clone()),
        }
    }
    if read.is_empty() {
        return None;
    }
    Some((standard(&node.with_children(kids), ctx.ctx), read))
}

/// Whether `node` or one of its parts has a define at its head that this
/// reading may read out: what a match does not refuse at its root, since
/// reading it out may make the ground what the pattern asks.
fn unfoldable(node: &Node, ctx: Reading<'_>) -> bool {
    ctx.define_at(node).is_some()
        || node.children.iter().any(|c| ctx.define_at(c).is_some())
}

/// `node`, a value the match bound a pattern's function letter to, read as
/// what it names where it is a define: a function's name as its rule, a
/// map's as the map, which is what a letter applied in the pattern asks.
fn value_read(node: &Node, ctx: Reading<'_>) -> Node {
    match node.is_name() {
        true => unfold_head(node, ctx).map_or_else(|| node.clone(), |(read, _)| read),
        false => node.clone(),
    }
}

impl<'a> From<&'a Context> for Reading<'a> {
    fn from(ctx: &'a Context) -> Reading<'a> {
        Reading::plain(ctx)
    }
}

impl Deref for Reading<'_> {
    type Target = Context;

    fn deref(&self) -> &Context {
        self.ctx
    }
}

/// The maps every match and comparison looks a notation up in, at each
/// node: hashed by `FxHash`, for short keys the program makes itself and no
/// one chooses to collide, where the default hasher guards against that.
pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;
pub type FxIndexSet<K> = IndexSet<K, FxBuildHasher>;

/// The notations of these names, as ids.
/// The notations whose holes stand in no order (`commutes any order`), by
/// id: a triangle's three points, a listed set's elements, a distance's two
/// points.
pub fn unordered_notations(records: &[Record]) -> FxIndexSet<NotationId> {
    ids_of(unordered(records))
}

fn ids_of(names: IndexSet<String>) -> FxIndexSet<NotationId> {
    names.iter().map(|n| NotationId::of(n)).collect()
}

/// An operation's identity element, and the holes, counted from 0, it may
/// stand in: 0 in either of x + y's, 0 in the second of x − y's.
#[derive(Clone, Debug)]
pub struct IdentityElement {
    pub element: String,
    pub holes: Vec<usize>,
    /// The law's pattern among its notation's (`targets::IdentityLaw`).
    pub pattern: usize,
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
    for law in targets::identity_laws(records) {
        let Some(pattern) = notations
            .iter()
            .filter(|n| n.name == law.notation)
            .nth(law.pattern)
        else {
            continue;
        };
        out.insert(
            Spelling::new(pattern.key_id, pattern.literal_id),
            IdentityElement {
                element: law.element.to_string(),
                holes: law.holes,
                pattern: law.pattern,
            },
        );
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
        .filter(|r| targets::commutes_said(r).contains(&Some(Commutes::AnyOrder)))
        .map(|r| r.name.clone())
        .collect()
}

/// The notations whose record names two holes that stand in no order,
/// `commutes any order of holes 1 and 2`, with those two places. A record's
/// patterns build one notation, so the first such entry stands for it.
fn unordered_pairs(records: &[Record]) -> FxIndexMap<NotationId, (usize, usize)> {
    let mut out = FxIndexMap::default();
    for r in records.iter().filter(|r| r.kind == RecordKind::Notation) {
        let pair = targets::commutes_said(r).into_iter().find_map(|c| match c {
            Some(Commutes::AnyOrderOf(i, j)) => Some((i, j)),
            _ => None,
        });
        if let Some(pair) = pair {
            out.insert(NotationId::of(&r.name), pair);
        }
    }
    out
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
            conjunctions: ids_of(conjunctions(records)),
            universals: ids_of(universals(records)),
            turned: turned(notations, records),
            filled,
            unordered: ids_of(unordered(records)),
            unordered_pairs: unordered_pairs(records),
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
            r.kind == RecordKind::Notation && WCEQ.is_match(str::trim(r.syntax()))
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
            .metamath_target_or_empty()
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
            .metamath_target_or_empty()
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
    standard_how(node, ctx).0
}

/// `standard`, with whether it respelt anything: true where the tree had a
/// spelling to turn, a hole to fill or a map applied to read as its rule.
pub fn standard_how(node: &Node, ctx: &Context) -> (Node, bool) {
    if ctx.turned.is_empty() && ctx.filled.is_empty() {
        return (node.clone(), false);
    }
    match turned_to_standard(node, ctx) {
        Some(respelt) => (respelt, true),
        None => (node.clone(), false),
    }
}

/// What a node is in its standard spelling, where it is another's.
enum Standard<'c> {
    Turned(&'c Turned),
    Filled(&'c Filled),
}

/// `standard` of a tree that has a spelling to turn somewhere in it; None
/// for one that has none, which is kept as it is, with what it was read from.
fn turned_to_standard(node: &Node, ctx: &Context) -> Option<Node> {
    // A map applied to a value is its rule at the value, as the build reads
    // it (`applied_body`): the map sending y ∈ D to u(y), applied to x, is
    // u(x). That x is in D is the step's to say (`SYNTAX.md`, a map).
    if let Some(read) = map_applied(node, ctx) {
        return Some(turned_to_standard(&read, ctx).unwrap_or(read));
    }
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

/// A map applied to a value, read as the map's rule with the value for the
/// letter it binds, and a map of two applied to two values the same way with
/// each for its letter; None for anything else.
pub fn map_applied(node: &Node, ctx: &Context) -> Option<Node> {
    let (letters, rule, values) = match (node.notation(), node.children.as_slice()) {
        (APPLICATION, [map, at]) => match (map.notation(), map.children.as_slice()) {
            (MAP, [letter, _, rule]) => (vec![letter], rule, vec![at]),
            _ => return None,
        },
        (APPLICATION_TO_TWO, [map, a, b]) => {
            match (map.notation(), map.children.as_slice()) {
                (MAP_OF_TWO, [x, _, y, _, rule]) => (vec![x, y], rule, vec![a, b]),
                _ => return None,
            }
        }
        _ => return None,
    };
    if !letters.iter().all(|l| l.is_name()) {
        return None;
    }
    let binding: Binding = letters
        .iter()
        .zip(values)
        .map(|(l, v)| (l.text, v.clone()))
        .collect();
    Some(substitute_apart(rule, &binding, ctx))
}

/// Each value a map applied in `node` is read at, with the domain the map
/// gives that value: one for a map, two for a map of two. Empty for
/// anything else.
pub fn map_arguments(node: &Node) -> Vec<(Node, Node)> {
    match (node.notation(), node.children.as_slice()) {
        (APPLICATION, [map, at]) => match (map.notation(), map.children.as_slice()) {
            (MAP, [_, domain, _]) => vec![(at.clone(), domain.clone())],
            _ => Vec::new(),
        },
        (APPLICATION_TO_TWO, [map, a, b]) => {
            match (map.notation(), map.children.as_slice()) {
                (MAP_OF_TWO, [_, first, _, second, _]) => {
                    vec![(a.clone(), first.clone()), (b.clone(), second.clone())]
                }
                _ => Vec::new(),
            }
        }
        _ => Vec::new(),
    }
}

/// The notations whose `metamath-syntax` is set.mm's `Fn`: what a define with a
/// parameter says of its function.
pub fn functions_on(records: &[Record]) -> IndexSet<String> {
    records
        .iter()
        .filter(|r| r.kind == RecordKind::Notation && str::trim(r.syntax()) == "wfn")
        .map(|r| r.name.clone())
        .collect()
}

/// The notations whose `metamath-syntax` is set.mm's `csu`, a sum over some range.
pub fn sums(records: &[Record]) -> IndexSet<String> {
    records
        .iter()
        .filter(|r| {
            r.kind == RecordKind::Notation && str::trim(r.syntax()).starts_with("csu ")
        })
        .map(|r| r.name.clone())
        .collect()
}

/// The notations saying there is something: their `metamath-syntax` is `wrex`,
/// once or nested, over whatever set.
pub fn existences(records: &[Record]) -> IndexSet<String> {
    records
        .iter()
        .filter(|r| {
            r.kind == RecordKind::Notation && str::trim(r.syntax()).starts_with("wrex")
        })
        .map(|r| r.name.clone())
        .collect()
}

/// The notations joining two claims by "and": the first word of their
/// `metamath-syntax` is `wa`, as "wa, …" may say more after the label.
pub fn conjunctions(records: &[Record]) -> IndexSet<String> {
    let first_word = |r: &Record| -> String {
        str::trim(r.syntax())
            .chars()
            .take_while(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || *c == '-')
            .collect()
    };
    records
        .iter()
        .filter(|r| r.kind == RecordKind::Notation && first_word(r) == "wa")
        .map(|r| r.name.clone())
        .collect()
}

/// The notations saying something of everything: their `metamath-syntax` is
/// `wral`, once or nested, over whatever set, or `wal`, over no set.
pub fn universals(records: &[Record]) -> IndexSet<String> {
    records
        .iter()
        .filter(|r| {
            let metamath = str::trim(r.syntax());
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
    order_places(a, b, ctx)
        .iter()
        .map(|places| places.iter().map(|&k| b.children[k].clone()).collect())
        .collect()
}

/// `orders` as places: for each way, the place in b of the part against
/// each of a's, in a's order.
fn order_places(a: &Node, b: &Node, ctx: &Context) -> Vec<Vec<usize>> {
    let written: Vec<usize> = (0..b.children.len()).collect();
    if ctx.equations.contains(&a.notation()) && b.children.len() == 2 {
        return vec![written, vec![1, 0]];
    }
    if let Some(&(i, j)) = ctx.unordered_pairs.get(&a.notation()) {
        if i.max(j) < b.children.len() {
            let mut turned = written.clone();
            turned.swap(i, j);
            return vec![written, turned];
        }
    }
    vec![written]
}

/// Bind the pattern's variables so that it becomes the ground tree.
///
/// Returns the binding, or None where the pattern does not fit. Two trees
/// are compared up to the letters they bind and the order of an equation's
/// sides (`alike`), and a binder of the pattern's may take the ground's
/// letter (`bound_as`). Where `ctx` is a `Reading` with defines, a define
/// is read out where the pattern asks for what it names.
pub fn match_tree<'c>(
    pattern: &Node,
    ground: &Node,
    binding: &Binding,
    variables: &BTreeSet<String>,
    sites: &IndexSet<NodeId>,
    ctx: impl Into<Reading<'c>>,
) -> Option<Binding> {
    let ctx = ctx.into();
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
    ctx: Reading<'_>,
) -> bool {
    !is_variable(pattern, variables)
        && !applies_variable(pattern, variables, &ctx)
        && differs(pattern, ground)
        && !holds_identity(pattern, binding, variables, &ctx)
        && identity_kept(ground, ctx).is_none()
        && !unfoldable(ground, ctx)
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
pub fn match_every_way<'c>(
    pattern: &Node,
    ground: &Node,
    binding: &Binding,
    variables: &BTreeSet<String>,
    sites: &IndexSet<NodeId>,
    ctx: impl Into<Reading<'c>>,
) -> Vec<Binding> {
    let ctx = ctx.into();
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
    ctx: Reading<'_>,
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
    ctx: Reading<'_>,
    then: &mut Then,
) -> bool {
    let before = binding.len();
    if is_variable(pattern, variables) {
        if let Some(seen) = binding.get(&pattern.text) {
            return alike_how(seen, ground, ctx, &IndexMap::new(), &IndexMap::new())
                .is_some()
                && then(binding);
        }
        binding.insert(pattern.text, ground.clone());
        return then_kept(true, before, binding, then);
    }
    if applies_variable(pattern, variables, &ctx) {
        if ctx.props.get(&pattern.notation()).map(String::as_str) != Some("function") {
            let fits = property(pattern, ground, binding, sites, ctx);
            return then_kept(fits, before, binding, then);
        }
        // A rule or a map filled in is matched in the pattern's place, but
        // not one that names the page's letter of the pattern's
        // (`names_its_letter`).
        let own = names_its_letter(pattern, binding, &ctx);
        if let Some(filled) =
            rule_at_open_argument(pattern, binding, variables, ctx).filter(|_| !own)
        {
            return fit_each(&filled, ground, binding, variables, sites, ctx, then);
        }
        if let Some(filled) = map_at_argument(pattern, binding, ctx).filter(|_| !own) {
            return fit_each(&filled, ground, binding, variables, sites, ctx, then);
        }
        if let Some(fits) = family(pattern, ground, binding, variables, sites, ctx) {
            return then_kept(fits, before, binding, then);
        }
        if let Some(rule) = applied_as_rule(pattern, ground, binding, sites, &ctx) {
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

/// t(u) where t is bound already to a rule and u holds a letter of the item
/// still to be bound: the rule with u, as the pattern writes it, in its
/// hole. Matching that binds u's letters, as they would be bound with t
/// written out: `product-reindex` at ∏(x ∈ L) f(x), with t the rule z ↦ z,
/// meets t(g(y)) as g(y), whose g is then the rule x ↦ f(x). The pattern's
/// own u is put in, not a copy read through the binding, so that what is
/// under a binder there is still known to be. None where t is bound to no
/// rule or u has no such letter.
fn rule_at_open_argument(
    pattern: &Node,
    binding: &Binding,
    variables: &BTreeSet<String>,
    ctx: Reading<'_>,
) -> Option<Node> {
    let stands = &value_read(binding.get(&pattern.children[0].text)?, ctx);
    let [arg] = &pattern.children[1..] else {
        return None;
    };
    let open = free_names(arg, &ctx.binders)
        .into_iter()
        .any(|n| variables.contains(&n) && !binding.contains_key(&Symbol::of(&n)));
    if stands.notation() != PROPERTY_OF || !open {
        return None;
    }
    let mut put = Binding::new();
    put.insert(stands.text, arg.clone());
    Some(substitute_apart(&stands.children[0], &put, &ctx))
}

/// t(u) where t is bound already to a map: the map's rule with u, as the
/// pattern writes it, for the letter it binds (`map_applied`): L'Hôpital's
/// f(x)/g(x), with f the map sending y ∈ D to u(y), is u(x)/g(x). None
/// where t is bound to no map.
fn map_at_argument(
    pattern: &Node,
    binding: &Binding,
    ctx: Reading<'_>,
) -> Option<Node> {
    let stands = value_read(binding.get(&pattern.children[0].text)?, ctx);
    let mut children = vec![stands];
    children.extend(pattern.children[1..].iter().cloned());
    map_applied(
        &Node::of(pattern.spelling(), pattern.sort.clone(), children),
        &ctx,
    )
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
        && ground.children[1].spelt_alike(&arg);
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
    ctx: Reading<'_>,
    then: &mut Then,
) -> bool {
    // A product over a set whose set is still to be bound meets a product
    // from a to b as the product over {a, …, b}, the form it is the
    // standard of (`Context::filled`).
    if let Some(open) = unfilled(pattern, ground, &ctx) {
        return fit_structure(pattern, &open, binding, variables, sites, ctx, then);
    }
    // Whether the pattern fitted as written, its parts against the ground's,
    // in some way. An identity element is read away only where it did not.
    let mut written = false;
    if !differs(pattern, ground) {
        let pattern = bound_as(pattern, ground, binding, variables, &ctx);
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
            for children in orders(&pattern, ground, &ctx) {
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
        // A function letter applied meets a define applied both as written,
        // F := f, and read out, where the item's other mentions of F ask for
        // what f is: f(x) with f(x) := F(x) is F(x), whose F is the page's.
        // The way as written is offered first.
        if let (true, Some(deeper), Some((read, _))) = (
            applies_variable(pattern, variables, &ctx),
            ctx.deeper(),
            unfold_head(ground, ctx),
        ) {
            return fit_each(pattern, &read, binding, variables, sites, deeper, then);
        }
        return false;
    }
    // x + 0 is x wherever it stands (`Context::identities`): in the pattern,
    // or in the ground.
    if without_identity(pattern, ground, binding, variables, sites, ctx, then) {
        return true;
    }
    if let Some(kept) = identity_kept(ground, ctx) {
        if fit_each(pattern, &kept, binding, variables, sites, ctx, then) {
            return true;
        }
    }
    // A define the pattern asks for what it names is read out there, and
    // only there: the ground's head, else a part whose reading respells
    // the ground (`Reading`). A variable of the pattern binds the ground as
    // written, so what no structure asks for keeps the page's spelling.
    let Some(deeper) = ctx.deeper() else {
        return false;
    };
    if let Some((read, _)) = unfold_head(ground, ctx) {
        return fit_each(pattern, &read, binding, variables, sites, deeper, then);
    }
    match parts_unfolded(ground, Tree::Second, ctx) {
        Some((read, _)) => {
            fit_each(pattern, &read, binding, variables, sites, deeper, then)
        }
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
    ctx: Reading<'_>,
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
    ctx: Reading<'_>,
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
    whole: &Node,
    a: &[Node],
    b: &[Node],
    related: &dyn Fn(&Node, &Node) -> Option<Meeting>,
) -> Option<Meeting> {
    if a.len() != b.len() {
        return None;
    }
    let met: Vec<Vec<Option<Meeting>>> = a
        .iter()
        .map(|x| b.iter().map(|y| related(x, y)).collect())
        .collect();
    // Each part in its own place where that pairs them: {2, 3, 2} meets
    // itself as written, not with its two 2s crossed.
    let in_place: Option<Vec<Meeting>> =
        (0..a.len()).map(|i| met[i][i].clone()).collect();
    if let Some(in_place) = in_place {
        return Some(
            in_place
                .into_iter()
                .enumerate()
                .map(|(i, m)| m.under(i, i))
                .fold(Meeting::default(), Meeting::with),
        );
    }
    let pairs: Vec<Vec<bool>> = met
        .iter()
        .map(|row| row.iter().map(Option::is_some).collect())
        .collect();
    let mut partner: Vec<Option<usize>> = vec![None; b.len()];
    if !(0..a.len())
        .all(|i| augmented(i, &pairs, &mut partner, &mut vec![false; b.len()]))
    {
        return None;
    }
    let mut out = Meeting::default();
    let mut order = Vec::new();
    for (j, i) in partner.iter().enumerate() {
        let i = (*i)?;
        out.permuted |= i != j;
        order.push(i);
        out = out.with(met[i][j].clone()?.under(i, j));
    }
    if out.permuted {
        out.flips.push(Flip {
            notation: whole.notation_name().to_string(),
            at: Vec::new(),
            order,
            term: whole.clone(),
        });
    }
    Some(out)
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
    parts_related_how(a, b, ctx, &|x, y| related(x, y).then(Meeting::default)).is_some()
}

/// `parts_related`, with how the parts met: each pair's meeting, the parts
/// taken the other way round where the second of `orders` paired them, and
/// paired out of order where an unordered notation's matching did.
fn parts_related_how(
    a: &Node,
    b: &Node,
    ctx: &Context,
    related: &dyn Fn(&Node, &Node) -> Option<Meeting>,
) -> Option<Meeting> {
    if ctx.unordered.contains(&a.notation()) {
        return paired_in_some_order(a, &a.children, &b.children, related);
    }
    order_places(a, b, ctx)
        .iter()
        .enumerate()
        .find_map(|(way, places)| {
            let mut out = Meeting {
                turned: way > 0,
                ..Meeting::default()
            };
            for (k, (x, &at)) in a.children.iter().zip(places.iter()).enumerate() {
                out = out.with(related(x, &b.children[at])?.under(k, at));
            }
            // Two holes of a notation that stands in no order in those two
            // only, taken the other way round.
            if let (true, Some(&(i, j))) =
                (way > 0, ctx.unordered_pairs.get(&a.notation()))
            {
                let mut order: Vec<usize> = (0..a.children.len()).collect();
                order.swap(i, j);
                out.flips.push(Flip {
                    notation: a.notation_name().to_string(),
                    at: Vec::new(),
                    order,
                    term: a.clone(),
                });
            }
            Some(out)
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
    ctx: Reading<'_>,
    then: &mut Then,
) -> bool {
    let Some(law) = identity_of(pattern, ctx.ctx) else {
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
/// where the letter is no variable of the pattern's, or is one the match
/// has bound already to another letter, and the ground's letter is free
/// nowhere in it; the pattern as it is otherwise.
///
/// A definition's formula read at a term binds a letter of its own, and a
/// line saying the same thing may bind another: `there is b ∈ G with gH =
/// bH` answers K's `there is g ∈ G with X = gH` at X := gH. An item's
/// hypotheses that each bind n, `x(n) → L as n → ∞` and `x(n) ≤ B for all
/// n ≥ N`, meet lines that bind n in one and i in the other: the first
/// pairs n with n, and the second is read as binding i.
fn bound_as(
    pattern: &Node,
    ground: &Node,
    binding: &Binding,
    variables: &BTreeSet<String>,
    ctx: &Context,
) -> Node {
    let (held, body) = ctx.held_body(pattern.notation());
    let mut pattern = pattern.clone();
    for at in held {
        let ours = pattern.children[at].clone();
        let theirs = ground.children[at].clone();
        let paired_elsewhere = binding
            .get(&ours.text)
            .is_some_and(|stood| stood.is_name() && stood.text != theirs.text);
        if !ours.is_name()
            || !theirs.is_name()
            || ours.text == theirs.text
            || (variables.contains(ours.text.as_str()) && !paired_elsewhere)
            || variables.contains(theirs.text.as_str())
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
pub fn alike<'c>(
    a: &Node,
    b: &Node,
    ctx: impl Into<Reading<'c>>,
    ours: &IndexMap<Symbol, Symbol>,
    theirs: &IndexMap<Symbol, Symbol>,
) -> bool {
    alike_how(a, b, ctx, ours, theirs).is_some()
}

/// How two formulas `alike` finds one are one: what pairing them took.
/// Each backend carries out the same differences by its own lemmas, and
/// reads them here instead of comparing the two again.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Meeting {
    /// An equation, or two holes that stand in no order, taken the other
    /// way round somewhere.
    pub turned: bool,
    /// The parts of a notation whose parts stand in any order paired other
    /// than in their places.
    pub permuted: bool,
    /// A letter one binds paired with a different letter the other binds.
    pub renamed: bool,
    /// One side read in another spelling of the same notation, `x > 0` as
    /// `0 < x` or x² as x^2, or a map applied read as its rule
    /// (`standard`).
    pub respelled: bool,
    /// The line's defined names read as what they name, as the citation
    /// reads a define it cites: `i ∈ S` met as `i ∈ {i ∈ … : …}`, S the
    /// define (`Known::read_citing`).
    pub defines_read: bool,
    /// Each identity element dropped, x + 0 read as x.
    pub identities: Vec<Dropped>,
    /// Each notation whose parts stand in no order that met with its parts
    /// paired other than in their places, where it stands.
    pub flips: Vec<Flip>,
    /// Each define read out where the two differed and the other asked for
    /// what it names (`Reading`), the outermost first.
    pub unfolded: Vec<Unfold>,
}

/// A define read out where a comparison needed what it names: `S` of `i ∈
/// S` read as `{i ∈ … : …}` where the other tree writes that. The name, the
/// tree it stood in, its place there, counted in that tree with the
/// unfoldings before it made, and what it was read as there, which a
/// backend reaches from the name by the define's equation. A meeting's
/// identities and flips are placed in the trees with every unfolding made.
#[derive(Clone, Debug)]
pub struct Unfold {
    pub name: String,
    pub tree: Tree,
    pub at: Vec<usize>,
    pub read: Node,
}

impl PartialEq for Unfold {
    fn eq(&self, other: &Unfold) -> bool {
        self.name == other.name
            && self.tree == other.tree
            && self.at == other.at
            && self.read.shape() == other.read.shape()
    }
}

impl Eq for Unfold {}

/// A notation whose parts stand in no order (`commutes`), met with its
/// parts in another order than the other tree writes them: |AB| against
/// |BA|, or `P is between A and B` against `P is between B and A`. A
/// backend turns it by its own lemma for the notation.
#[derive(Clone, Debug)]
pub struct Flip {
    /// The notation's name.
    pub notation: String,
    /// Where it stands in the first tree: the place of each child to go
    /// down by from its root, counted from 0.
    pub at: Vec<usize>,
    /// Which of the first tree's parts is paired with each of the second's:
    /// `order[k]` is the place in the first of the part against the
    /// second's k-th.
    pub order: Vec<usize>,
    /// The notation's term as the first tree writes it, |AB|; the second
    /// writes it with its parts in `order`, |BA|.
    pub term: Node,
}

/// Two flips are one where they are of one notation at one place in one
/// order, their terms one tree by shape, as the checker compares trees.
impl PartialEq for Flip {
    fn eq(&self, other: &Flip) -> bool {
        self.notation == other.notation
            && self.at == other.at
            && self.order == other.order
            && self.term.shape() == other.term.shape()
    }
}

impl Eq for Flip {}

impl Flip {
    /// The term as the second tree writes it: the first's parts in `order`.
    pub fn turned(&self) -> Node {
        let parts: Vec<Node> = self
            .order
            .iter()
            .filter_map(|&k| self.term.children.get(k).cloned())
            .collect();
        self.term.with_children(parts)
    }
}

impl Meeting {
    /// The same meeting of two parts that stand as the `first`-th child of
    /// the first tree and the `second`-th of the second: each place gains
    /// its tree's step.
    fn under(self, first: usize, second: usize) -> Meeting {
        self.within(Tree::First, first).within(Tree::Second, second)
    }

    /// The same meeting, with one of its trees the `index`-th child of a
    /// larger one: each place in that tree gains the step. A flip's place is
    /// in the first tree.
    fn within(mut self, tree: Tree, index: usize) -> Meeting {
        if tree == Tree::First {
            for flip in &mut self.flips {
                flip.at.insert(0, index);
            }
        }
        for dropped in self.identities.iter_mut().filter(|d| d.tree == tree) {
            dropped.at.insert(0, index);
        }
        for unfold in self.unfolded.iter_mut().filter(|u| u.tree == tree) {
            unfold.at.insert(0, index);
        }
        self
    }

    /// Whether the two are written alike: nothing was taken to pair them.
    pub fn as_written(&self) -> bool {
        *self == Meeting::default()
    }

    /// Whether the two are one term up to the letters they bind: nothing
    /// was taken to pair them but a bound letter renamed. A flip comes with
    /// `turned` or `permuted`, so none is left.
    pub fn renamed_only(&self) -> bool {
        !self.turned
            && !self.permuted
            && !self.respelled
            && !self.defines_read
            && self.identities.is_empty()
            && self.unfolded.is_empty()
    }

    /// Whether the parts of a notation that stand in any order were paired
    /// out of their places, and nothing else was taken but a bound letter
    /// renamed: no side turned, respelled or without an identity.
    pub fn permuted_only(&self) -> bool {
        self.permuted
            && !self.turned
            && !self.respelled
            && !self.defines_read
            && self.identities.is_empty()
            && self.unfolded.is_empty()
    }

    /// Both meetings at once: what either took.
    fn with(mut self, other: Meeting) -> Meeting {
        self.turned |= other.turned;
        self.permuted |= other.permuted;
        self.renamed |= other.renamed;
        self.respelled |= other.respelled;
        self.defines_read |= other.defines_read;
        self.identities.extend(other.identities);
        self.flips.extend(other.flips);
        self.unfolded.extend(other.unfolded);
        self
    }

    /// `tree`, the one of the two trees the meeting is of that `which`
    /// names, with each identity element dropped from it taken out at its
    /// place, deepest first: what the elements leave, which a backend
    /// reaches from the tree by its own identity laws. None where a place
    /// is no operation of the tree, so `tree` is not the one met.
    pub fn with_identities_dropped(&self, tree: &Node, which: Tree) -> Option<Node> {
        let mut out = tree.clone();
        for dropped in self.identities.iter().filter(|d| d.tree == which) {
            let operation = node_at(&out, &dropped.at)?;
            let kept = operation.children.get(1 - dropped.hole)?.clone();
            out = put_at_places(&out, slice::from_ref(&dropped.at), &kept);
        }
        Some(out)
    }

    /// `tree`, the one of the two trees the meeting is of that `which`
    /// names, with each define the meeting read out in it put as what it
    /// was read as, at its place, the outermost first. None where a place
    /// is no part of the tree, so `tree` is not the one met. What a
    /// meeting's identities are dropped from (`with_identities_dropped`).
    pub fn with_unfolded(&self, tree: &Node, which: Tree) -> Option<Node> {
        let mut out = tree.clone();
        for unfold in self.unfolded.iter().filter(|u| u.tree == which) {
            node_at(&out, &unfold.at)?;
            out = put_at_places(&out, slice::from_ref(&unfold.at), &unfold.read);
        }
        Some(out)
    }

    /// The same meeting, with a side read in another spelling where
    /// `respelled`.
    pub fn respelt(mut self, respelled: bool) -> Meeting {
        self.respelled |= respelled;
        self
    }
}

/// An identity element dropped: the operation by its notation's name and
/// the literal it is written with, the hole the element stood in, and the
/// element, `additive` written `+` with 0 in hole 1 for x + 0.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dropped {
    pub operation: String,
    pub literal: String,
    pub hole: usize,
    pub element: String,
    /// The law, by its pattern among the operation's
    /// (`targets::IdentityLaw`).
    pub pattern: usize,
    /// The tree the element stands in, of the two `alike_how` compared.
    pub tree: Tree,
    /// Where the operation stands in that tree: the place of each child to
    /// go down by from its root, counted from 0, as `Flip::at`. The
    /// elements are listed deepest first, so each place is one in the tree
    /// with the elements before it dropped.
    pub at: Vec<usize>,
}

/// Which of the two trees `alike_how` compared a place is in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tree {
    First,
    Second,
}

/// `alike`, with how the two met; None where they are not alike. Where
/// `ctx` is a `Reading` with defines, a define is read out where the two
/// trees differ, and the meeting records where.
pub fn alike_how<'c>(
    a: &Node,
    b: &Node,
    ctx: impl Into<Reading<'c>>,
    ours: &IndexMap<Symbol, Symbol>,
    theirs: &IndexMap<Symbol, Symbol>,
) -> Option<Meeting> {
    let ctx = ctx.into();
    if let Some(met) = alike_as_written(a, b, ctx, ours, theirs) {
        return Some(met);
    }
    // x + 0 is x wherever it stands (`Context::identities`). What the kept
    // operand meets is at its place under the operation, and the element is
    // dropped after it, deepest first.
    if let Some(kept) = identity_kept_how(a, Tree::First, ctx) {
        if let Some(met) = alike_how(&kept.node, b, ctx, ours, theirs) {
            return Some(met.within(Tree::First, kept.place).with(kept.met));
        }
    }
    if let Some(kept) = identity_kept_how(b, Tree::Second, ctx) {
        if let Some(met) = alike_how(a, &kept.node, ctx, ours, theirs) {
            return Some(met.within(Tree::Second, kept.place).with(kept.met));
        }
    }
    alike_unfolded(a, b, ctx, ours, theirs)
}

/// `alike_how` of two trees that meet neither as written nor with an
/// identity element dropped, once a define is read out where one differs
/// from the other (`Reading`): the define at the head of the first, else
/// at the second's, else at the head of a part whose reading respells the
/// node. The read-outs are recorded where they were made, the outermost
/// first. None where the reading has no defines to read out.
fn alike_unfolded(
    a: &Node,
    b: &Node,
    ctx: Reading<'_>,
    ours: &IndexMap<Symbol, Symbol>,
    theirs: &IndexMap<Symbol, Symbol>,
) -> Option<Meeting> {
    let deeper = ctx.deeper()?;
    for tree in [Tree::First, Tree::Second] {
        let node = if tree == Tree::First { a } else { b };
        let Some((read, name)) = unfold_head(node, ctx) else {
            continue;
        };
        let met = match tree {
            Tree::First => alike_how(&read, b, deeper, ours, theirs),
            Tree::Second => alike_how(a, &read, deeper, ours, theirs),
        };
        if let Some(met) = met {
            let here = Meeting {
                unfolded: vec![Unfold {
                    name,
                    tree,
                    at: Vec::new(),
                    read,
                }],
                ..Meeting::default()
            };
            return Some(here.with(met));
        }
    }
    for tree in [Tree::First, Tree::Second] {
        let node = if tree == Tree::First { a } else { b };
        let Some((read, parts)) = parts_unfolded(node, tree, ctx) else {
            continue;
        };
        let met = match tree {
            Tree::First => alike_how(&read, b, deeper, ours, theirs),
            Tree::Second => alike_how(a, &read, deeper, ours, theirs),
        };
        if let Some(met) = met {
            let here = Meeting {
                unfolded: parts,
                respelled: true,
                ..Meeting::default()
            };
            return Some(here.with(met));
        }
    }
    None
}

/// The operand an identity element leaves (`identity_kept_how`): the
/// operand, its place among the operation's parts, and the elements
/// dropped to leave it.
struct Kept {
    node: Node,
    place: usize,
    met: Meeting,
}

/// The operand an identity element leaves, where `node` is an operation
/// with its identity in a hole the record allows it: x for x + 0. None
/// otherwise. The identity may itself be written with one left out, so
/// a^(0 + 1) leaves a.
fn identity_kept<'c>(node: &Node, ctx: impl Into<Reading<'c>>) -> Option<Node> {
    identity_kept_how(node, Tree::First, ctx.into()).map(|kept| kept.node)
}

/// `identity_kept`, with the elements dropped, `node` standing at the root
/// of `tree`: one its identity was itself written with, then the
/// operation's.
fn identity_kept_how(node: &Node, tree: Tree, ctx: Reading<'_>) -> Option<Kept> {
    let law = identity_of(node, ctx.ctx)?;
    law.holes.iter().find_map(|&hole| {
        let at = &node.children[hole];
        let mut met = Meeting::default();
        if !law.is(at) {
            let inner = identity_kept_how(at, tree, ctx)?;
            if !law.is(&inner.node) {
                return None;
            }
            met = inner.met.within(tree, hole);
        }
        met.identities.push(Dropped {
            operation: node.notation_name().to_string(),
            literal: node.spelling().text().to_string(),
            hole,
            element: law.element.clone(),
            pattern: law.pattern,
            tree,
            at: Vec::new(),
        });
        Some(Kept {
            node: node.children[1 - hole].clone(),
            place: 1 - hole,
            met,
        })
    })
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
    if instance.spelt_alike(ground) {
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

/// `alike_how`, the two read as written at the head.
fn alike_as_written(
    a: &Node,
    b: &Node,
    ctx: Reading<'_>,
    ours: &IndexMap<Symbol, Symbol>,
    theirs: &IndexMap<Symbol, Symbol>,
) -> Option<Meeting> {
    if a.is_name() && b.is_name() {
        if ours.contains_key(&a.text) || theirs.contains_key(&b.text) {
            let paired = ours.get(&a.text) == Some(&b.text)
                && theirs.get(&b.text) == Some(&a.text);
            return paired.then(|| Meeting {
                renamed: a.text != b.text,
                ..Meeting::default()
            });
        }
        return (a.text == b.text).then(Meeting::default);
    }
    if a.notation() != b.notation()
        || a.text != b.text
        || a.children.len() != b.children.len()
    {
        return None;
    }
    let Some(shape) = ctx.binders.get(&a.notation()) else {
        return parts_related_how(a, b, &ctx, &|x, y| {
            alike_how(x, y, ctx, ours, theirs)
        });
    };
    let pairs: Vec<(&Node, &Node)> = shape
        .held
        .iter()
        .map(|&at| (&a.children[at], &b.children[at]))
        .collect();
    if pairs.iter().any(|(x, y)| !x.is_name() || !y.is_name()) {
        return a.spelt_alike(b).then(Meeting::default);
    }
    let mut inner_ours = ours.clone();
    let mut inner_theirs = theirs.clone();
    for (x, y) in &pairs {
        inner_ours.insert(x.text, y.text);
    }
    for (x, y) in &pairs {
        inner_theirs.insert(y.text, x.text);
    }
    let mut out = Meeting {
        renamed: pairs.iter().any(|(x, y)| x.text != y.text),
        ..Meeting::default()
    };
    for (i, (p, q)) in a.children.iter().zip(b.children.iter()).enumerate() {
        if shape.held.contains(&i) {
            continue;
        }
        let met = match shape.body.contains(&i) {
            true => alike_how(p, q, ctx, &inner_ours, &inner_theirs),
            false => alike_how(p, q, ctx, ours, theirs),
        };
        out = out.with(met?.under(i, i));
    }
    Some(out)
}

/// Whether two trees are one formula, compared from the top.
pub fn alike_top<'c>(a: &Node, b: &Node, ctx: impl Into<Reading<'c>>) -> bool {
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
/// no one to say. A whole written as `was` is written is the place itself,
/// though a part of it is `was` with an identity element dropped:
/// (1/(m + 1))·1 is put for as a whole, not its 1/(m + 1).
pub(crate) fn put_places(
    start: &Node,
    was: &Node,
    now: &Node,
    ctx: &Context,
) -> Option<Node> {
    if start.spelt_alike(was) {
        return Some(now.clone());
    }
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

/// Where a substitution puts its equation: of `aim` as `start` with one
/// side of `left = right` put for the other, which way round, and the
/// places in `start` it is put at, each by its path of children from the
/// top. Each part is compared as the same tree, as the page writes it: no
/// standard order, no identity element dropped, no bound letter renamed,
/// so that putting the one side for the other at the places makes `aim`
/// exactly. One side is put for the other at every place: the equation's
/// left side for its right where `turned`. None where no one way makes
/// `aim` so.
pub fn substitution_places(
    start: &Node,
    aim: &Node,
    left: &Node,
    right: &Node,
) -> Option<SubstitutionPlaces> {
    [(left, right, false), (right, left, true)]
        .into_iter()
        .find_map(|(was, now, turned)| {
            let mut places = Vec::new();
            let made = places_put(start, aim, was, now, &mut Vec::new(), &mut places);
            (made && !places.is_empty())
                .then_some(SubstitutionPlaces { turned, places })
        })
}

/// Every place `was` stands in `term`, compared as the same tree as the
/// page writes it, each by its path of children from the top; none inside
/// another.
pub fn places_of(term: &Node, was: &Node) -> Vec<Vec<usize>> {
    fn walk(term: &Node, was: &Node, at: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if term.spelt_alike(was) {
            out.push(at.clone());
            return;
        }
        for (k, child) in term.children.iter().enumerate() {
            at.push(k);
            walk(child, was, at, out);
            at.pop();
        }
    }
    let mut out = Vec::new();
    walk(term, was, &mut Vec::new(), &mut out);
    out
}

/// Every place a term `alike` to `was` stands in `term`, |BA| of |AB|, each
/// by its path of children from the top; none inside another. Where the
/// page writes `was` as it stands, `places_of` finds the same places.
pub fn places_alike(term: &Node, was: &Node, ctx: &Context) -> Vec<Vec<usize>> {
    fn walk(
        term: &Node,
        was: &Node,
        ctx: &Context,
        at: &mut Vec<usize>,
        out: &mut Vec<Vec<usize>>,
    ) {
        if alike_top(term, was, ctx) {
            out.push(at.clone());
            return;
        }
        for (k, child) in term.children.iter().enumerate() {
            at.push(k);
            walk(child, was, ctx, at, out);
            at.pop();
        }
    }
    let mut out = Vec::new();
    walk(term, was, ctx, &mut Vec::new(), &mut out);
    out
}

/// The node at `path`, a path of children from the top of `tree`; None
/// where the tree has no such place.
pub fn node_at<'n>(tree: &'n Node, path: &[usize]) -> Option<&'n Node> {
    path.iter().try_fold(tree, |node, &k| node.children.get(k))
}

/// The term with `now` put at each of `places`, paths of children from the
/// top.
pub fn put_at_places(term: &Node, places: &[Vec<usize>], now: &Node) -> Node {
    if places.iter().any(|p| p.is_empty()) {
        return now.clone();
    }
    let children = term
        .children
        .iter()
        .enumerate()
        .map(|(k, child)| {
            let below: Vec<Vec<usize>> = places
                .iter()
                .filter(|p| p[0] == k)
                .map(|p| p[1..].to_vec())
                .collect();
            match below.is_empty() {
                true => child.clone(),
                false => put_at_places(child, &below, now),
            }
        })
        .collect();
    term.with_children(children)
}

/// What `substitution_places` finds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SubstitutionPlaces {
    /// Whether the equation's left side is put for its right; its right
    /// side is put for its left where not.
    pub turned: bool,
    /// Each place put at, by its path of children from the top of what the
    /// equation is put into.
    pub places: Vec<Vec<usize>>,
}

/// Whether `aim` is `start` with `now` put for `was` at some places, each
/// place put at pushed onto `places` by its path from the top, `at` being
/// the path to `start`.
fn places_put(
    start: &Node,
    aim: &Node,
    was: &Node,
    now: &Node,
    at: &mut Vec<usize>,
    places: &mut Vec<Vec<usize>>,
) -> bool {
    if start.spelt_alike(aim) {
        return true;
    }
    if start.spelt_alike(was) && aim.spelt_alike(now) {
        places.push(at.clone());
        return true;
    }
    let shaped = start.notation() == aim.notation()
        && start.text == aim.text
        && !start.children.is_empty()
        && start.children.len() == aim.children.len();
    shaped
        && start
            .children
            .iter()
            .zip(&aim.children)
            .enumerate()
            .all(|(k, (s, a))| {
                at.push(k);
                let put = places_put(s, a, was, now, at, places);
                at.pop();
                put
            })
}

/// P applied to something, where P is one of the pattern's variables.
fn property(
    pattern: &Node,
    ground: &Node,
    binding: &mut Binding,
    sites: &IndexSet<NodeId>,
    ctx: Reading<'_>,
) -> bool {
    let name = &pattern.children[0].text;
    let arg = read_at(&pattern.children[1], binding, &ctx);
    let Some(stands) = binding.get(name).map(|s| value_read(s, ctx)) else {
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
    let filled = substitute_apart(&stands.children[0], &at, &ctx);
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

/// Whether the rule or map bound to the pattern's function letter names a
/// letter of the page with that letter's name: t bound to the page's
/// y ↦ t(g(y)), where a citation gives t no value. Filled in at t(z), it
/// gives t(g(z)), whose t is the page's; matched again, that t is read as
/// the item's letter and filled in again, t(g(g(z))), without end, and E
/// bound to s ↦ E(s) gives back E(s) itself each time. What such a rule
/// gives is the page's own term, which is compared as written.
fn names_its_letter(pattern: &Node, binding: &Binding, ctx: &Context) -> bool {
    let letter = &pattern.children[0].text;
    binding
        .get(letter)
        .is_some_and(|rule| free_names(rule, &ctx.binders).contains(letter.as_str()))
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
    ctx: Reading<'_>,
) -> Option<bool> {
    let name = &pattern.children[0].text;
    let arg = read_at(&pattern.children[1], binding, &ctx);
    let stands = binding.get(name).map(|s| value_read(s, ctx));
    if let Some(stands) = &stands {
        if stands.notation() == PROPERTY_OF {
            let mut at = Binding::new();
            at.insert(stands.text, arg.clone());
            let filled = substitute_apart(&stands.children[0], &at, &ctx);
            // At a letter still to be bound, a "there is"'s own in u =
            // E(s), the rule there is matched, which binds it: E(s) with E
            // the map n ↦ 2n meets 2m at s := m. A rule naming the page's
            // letter of the pattern's is compared as written
            // (`names_its_letter`).
            if !names_its_letter(pattern, binding, &ctx)
                && is_variable(&arg, variables)
                && !binding.contains_key(&arg.text)
            {
                return Some(fit(&filled, ground, binding, variables, sites, ctx));
            }
            return Some(alike_top(&filled, ground, ctx));
        }
    }
    let plain = ground.notation() == pattern.notation()
        && ground.children.len() == 2
        && ground.children[1].spelt_alike(&arg);
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
    pub params: Vec<Param>,
    /// The same arguments read where the define is written: each name with
    /// the sort its domain gives it, and the domain.
    pub read: Vec<ParamRead>,
    pub body: Node,
    /// What binds, from the grammar the body was read with
    /// (`Grammar::binders`).
    pub binders: Arc<FxIndexMap<NotationId, Binds>>,
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
    if node.notation() == NAME || node.notation() == NUMERAL {
        return binding
            .get(&node.text)
            .cloned()
            .unwrap_or_else(|| node.clone());
    }
    // A leaf that is no name holds nothing to put in, and a literal keeps the
    // term it stands for, which a rebuilt node would not.
    if node.children.is_empty() {
        return node.clone();
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::corpus::Within;
    use crate::formula::notation_id::NO_LITERAL;
    use crate::formula::Sort;
    use crate::notations::{EQUALS, IN, MAP, PLUS, WITHOUT};

    fn name(letter: &str) -> Node {
        Node::name(Sort::of("set"), letter)
    }

    fn made(spelling: Spelling, children: Vec<Node>) -> Node {
        Node::of(spelling, Sort::of("set"), children)
    }

    fn member(a: Node, set: Node) -> Node {
        made(IN, vec![a, set])
    }

    fn without(a: Node, b: Node) -> Node {
        made(WITHOUT, vec![a, b])
    }

    fn plus(a: Node, b: Node) -> Node {
        made(PLUS, vec![a, b])
    }

    fn equal(a: Node, b: Node) -> Node {
        made(EQUALS, vec![a, b])
    }

    fn variables(names: &[&str]) -> BTreeSet<String> {
        names.iter().map(|n| n.to_string()).collect()
    }

    /// S defined as A ∖ B.
    fn s_is_a_without_b() -> Unfolds {
        let mut defines = Definitions::new();
        defines.insert(
            "S".to_string(),
            Defined::Term(without(name("A"), name("B"))),
        );
        Unfolds { defines }
    }

    fn fitted(
        pattern: &Node,
        ground: &Node,
        letters: &[&str],
        ctx: Reading<'_>,
    ) -> Option<Binding> {
        let sites = IndexSet::new();
        match_tree(
            pattern,
            ground,
            &Binding::new(),
            &variables(letters),
            &sites,
            ctx,
        )
    }

    fn bound(binding: &Binding, letter: &str) -> String {
        binding[&Symbol::of(letter)].shape().to_string()
    }

    #[test]
    fn a_name_is_read_out_where_the_pattern_asks_for_what_it_names() {
        let ctx = Context::default();
        let unfolds = s_is_a_without_b();
        let pattern = member(name("u"), without(name("X"), name("Y")));
        let ground = member(name("i"), name("S"));
        let read = Reading::with(&ctx, &unfolds);
        let binding = fitted(&pattern, &ground, &["u", "X", "Y"], read)
            .expect("S read as A ∖ B fits X ∖ Y");
        assert_eq!(bound(&binding, "u"), name("i").shape());
        assert_eq!(bound(&binding, "X"), name("A").shape());
        assert_eq!(bound(&binding, "Y"), name("B").shape());
        // As written, without the define, nothing fits.
        let plain = Reading::plain(&ctx);
        assert!(fitted(&pattern, &ground, &["u", "X", "Y"], plain).is_none());
    }

    #[test]
    fn a_variable_binds_the_page_s_term_as_written() {
        let ctx = Context::default();
        let unfolds = s_is_a_without_b();
        let pattern = member(name("u"), name("X"));
        let ground = member(name("i"), name("S"));
        let read = Reading::with(&ctx, &unfolds);
        let binding = fitted(&pattern, &ground, &["u", "X"], read).expect("it fits");
        assert_eq!(bound(&binding, "X"), name("S").shape());
    }

    #[test]
    fn a_defined_function_applied_is_read_as_its_rule_at_the_values() {
        let ctx = Context::default();
        // g(x) := x + 1
        let rule = Rule {
            params: vec![Param {
                name: "x".to_string(),
                domain: "ℕ".to_string(),
                within: Within::Members,
                said: "x ∈ ℕ".to_string(),
            }],
            read: Vec::new(),
            body: plus(name("x"), Node::numeral("1")),
            binders: Arc::new(FxIndexMap::default()),
        };
        let mut defines = Definitions::new();
        defines.insert("g".to_string(), Defined::Rule(rule));
        let unfolds = Unfolds { defines };
        let applied = made(
            Spelling::new(APPLICATION, NO_LITERAL),
            vec![name("g"), Node::numeral("3")],
        );
        let pattern = plus(name("a"), name("b"));
        let read = Reading::with(&ctx, &unfolds);
        let binding = fitted(&pattern, &applied, &["a", "b"], read)
            .expect("g(3) read as 3 + 1 fits a + b");
        assert_eq!(bound(&binding, "a"), Node::numeral("3").shape());
        assert_eq!(bound(&binding, "b"), Node::numeral("1").shape());
    }

    #[test]
    fn an_identity_element_spelt_as_a_define_is_dropped() {
        let mut ctx = Context::default();
        ctx.identities.insert(
            PLUS,
            IdentityElement {
                element: "0".to_string(),
                holes: vec![1],
                pattern: 0,
            },
        );
        let mut defines = Definitions::new();
        defines.insert("Z".to_string(), Defined::Term(Node::numeral("0")));
        let unfolds = Unfolds { defines };
        let none = IndexMap::new();
        let met = alike_how(
            &plus(name("x"), name("Z")),
            &name("x"),
            Reading::with(&ctx, &unfolds),
            &none,
            &none,
        )
        .expect("x + Z, Z := 0, meets x");
        assert_eq!(met.unfolded.len(), 1);
        assert_eq!(met.unfolded[0].name, "Z");
        assert_eq!(met.unfolded[0].at, vec![1]);
        assert_eq!(met.identities.len(), 1);
    }

    #[test]
    fn a_letter_bound_by_name_meets_the_term_the_name_reads_as() {
        let ctx = Context::default();
        let unfolds = s_is_a_without_b();
        let pattern = equal(name("X"), name("X"));
        let ground = equal(name("S"), without(name("A"), name("B")));
        let read = Reading::with(&ctx, &unfolds);
        let binding = fitted(&pattern, &ground, &["X"], read)
            .expect("X is S, and S read out is A ∖ B");
        assert_eq!(bound(&binding, "X"), name("S").shape());
        let plain = Reading::plain(&ctx);
        assert!(fitted(&pattern, &ground, &["X"], plain).is_none());
    }

    #[test]
    fn a_meeting_records_where_a_define_was_read_out() {
        let ctx = Context::default();
        let unfolds = s_is_a_without_b();
        let none = IndexMap::new();
        let read_out = without(name("A"), name("B"));
        let met = alike_how(
            &member(name("i"), name("S")),
            &member(name("i"), read_out.clone()),
            Reading::with(&ctx, &unfolds),
            &none,
            &none,
        )
        .expect("i ∈ S meets i ∈ A ∖ B");
        assert_eq!(
            met.unfolded,
            vec![Unfold {
                name: "S".to_string(),
                tree: Tree::First,
                at: vec![1],
                read: read_out.clone(),
            }]
        );
        // The first tree with the read-out made is the second.
        let made = met
            .with_unfolded(&member(name("i"), name("S")), Tree::First)
            .expect("the place is in the tree");
        assert_eq!(made.shape(), member(name("i"), read_out).shape());
    }

    #[test]
    fn a_part_is_read_out_where_that_respells_the_node() {
        // A product over a set holding a range is the product from one end
        // to the other: over(R, t) with R := range(1, n) is from-to(1, n, t).
        let spelt =
            |notation: &str| Spelling::new(NotationId::of(notation), NO_LITERAL);
        let (over, range, from_to) = (
            spelt("test-over"),
            spelt("test-range"),
            spelt("test-from-to"),
        );
        let mut ctx = Context::default();
        ctx.filled.insert(
            over,
            vec![Filled {
                hole: 1,
                inner: range,
                standard: from_to,
                places: vec![Source::Inner(1), Source::Inner(2), Source::Outer(2)],
            }],
        );
        let set = made(range, vec![Node::numeral("1"), name("n")]);
        let mut defines = Definitions::new();
        defines.insert("R".to_string(), Defined::Term(set.clone()));
        let unfolds = Unfolds { defines };
        let none = IndexMap::new();
        let written = made(over, vec![name("R"), name("t")]);
        let standard = made(from_to, vec![Node::numeral("1"), name("n"), name("t")]);
        let met = alike_how(
            &written,
            &standard,
            Reading::with(&ctx, &unfolds),
            &none,
            &none,
        )
        .expect("over(R, t), R := range(1, n), meets from-to(1, n, t)");
        assert!(met.respelled);
        assert_eq!(
            met.unfolded,
            vec![Unfold {
                name: "R".to_string(),
                tree: Tree::First,
                at: vec![0],
                read: set,
            }]
        );
        assert!(alike_how(&written, &standard, &ctx, &none, &none).is_none());
    }

    fn applied(f: &str, arg: Node) -> Node {
        made(Spelling::new(APPLICATION, NO_LITERAL), vec![name(f), arg])
    }

    #[test]
    fn a_defined_map_applied_is_read_as_its_rule_at_the_value() {
        let ctx = Context::default();
        // p := (s ∈ A ↦ s + 1)
        let map = made(
            Spelling::new(MAP, NO_LITERAL),
            vec![name("s"), name("A"), plus(name("s"), Node::numeral("1"))],
        );
        let mut defines = Definitions::new();
        defines.insert("p".to_string(), Defined::Term(map));
        let unfolds = Unfolds { defines };
        let pattern = plus(name("a"), name("b"));
        let read = Reading::with(&ctx, &unfolds);
        let binding = fitted(&pattern, &applied("p", name("t")), &["a", "b"], read)
            .expect("p(t) read as t + 1 fits a + b");
        assert_eq!(bound(&binding, "a"), name("t").shape());
        assert_eq!(bound(&binding, "b"), Node::numeral("1").shape());
    }

    #[test]
    fn a_function_letter_meets_a_defined_function_both_ways() {
        let mut ctx = Context::default();
        ctx.props.insert(APPLICATION, "function".to_string());
        // f(x) := F(x)
        let rule = Rule {
            params: vec![Param {
                name: "x".to_string(),
                domain: "ℝ".to_string(),
                within: Within::Members,
                said: "x ∈ ℝ".to_string(),
            }],
            read: Vec::new(),
            body: applied("F", name("x")),
            binders: Arc::new(FxIndexMap::default()),
        };
        let mut defines = Definitions::new();
        defines.insert("f".to_string(), Defined::Rule(rule));
        let unfolds = Unfolds { defines };
        let ways = match_every_way(
            &applied("G", name("u")),
            &applied("f", name("y")),
            &Binding::new(),
            &variables(&["G", "u"]),
            &IndexSet::new(),
            Reading::with(&ctx, &unfolds),
        );
        let gs: Vec<String> = ways.iter().map(|b| bound(b, "G")).collect();
        assert_eq!(
            gs,
            vec![name("f").shape().to_string(), name("F").shape().to_string()]
        );
    }

    #[test]
    fn nothing_is_read_out_without_defines() {
        let ctx = Context::default();
        let none = IndexMap::new();
        let met = alike_how(
            &member(name("i"), name("S")),
            &member(name("i"), without(name("A"), name("B"))),
            &ctx,
            &none,
            &none,
        );
        assert!(met.is_none());
    }
}
