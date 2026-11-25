//! Each theorem's record as the page reads with what the theorem's file
//! defines outside it written out, and each phrase written as its meaning
//! (`CheckedTheorem::written`): T(k + 1) of `define T(k) := k(k + 1)/2` as
//! (k + 1)(k + 2)/2, as the Metamath build reads it (`elab::reading`). A
//! backend with no name for such a function, as Lean has none, reads this
//! record; the facts read from the page are read again of the page as
//! written, a letter a define written out binds being one the page as read
//! does not.

use std::sync::Arc;
use std::{iter, slice};

use indexmap::IndexMap;

use super::record::{
    AlgebraMade, CheckedTheorem, OrderFact, ShownBy, SuppliedBy, Unfolded,
};
use super::CheckedCorpus;
use crate::citing::finite::{FiniteBy, Making};
use crate::citing::{finite, number_sets, Group, Introduced, Want};
use crate::corpus::proof::{Hypothesis, Intro};
use crate::corpus::{Record, RecordKind, Theorem};
use crate::formula::node::ByShape;
use crate::formula::notation_id::NotationId;
use crate::formula::symbol::Symbol;
use crate::formula::{Grammar, Node};
use crate::matching::{Binding, Context, Defined, Definitions, SubstitutionPlaces};
use crate::notations::{BICONDITIONAL, EQUALS};
use crate::sorts::introduction::{Form, Introduction};
use crate::{citing, matching};

/// A phrase a define gives, `c is a counting ahead through k`: its slots
/// and what it means, from the definition record the define stands for,
/// whose statement is the phrase, `↔`, and the meaning. A definition of a
/// graph's notion, deg(x) or "v and e form a walk of n edges", is one too,
/// its statement the notion, `=` or `↔`, and what it is: a graph is no
/// structure a backend can name its notions on (`docs/LEAN.md`, "Graphs").
pub struct Phrase {
    slots: Vec<Symbol>,
    meaning: Node,
    /// The graph the definition's `let` line names, whose letters in the
    /// meaning, the E of deg(x) = |{a ∈ E : x is incident with a}|, are the
    /// page's own graph's where it is written out.
    graph: Option<GraphLetters>,
}

/// The letters a `let` line names a graph and its parts by: `let G be an
/// undirected multigraph with vertices V and edges E`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphLetters {
    pub graph: String,
    pub vertices: String,
    pub edges: String,
}

/// The graph a theorem's or a record's `let` lines name; None where none
/// does.
pub fn graph_letters(hypotheses: &[Hypothesis], path: &str) -> Option<GraphLetters> {
    hypotheses
        .iter()
        .filter(|h| h.kind == Intro::Let)
        .find_map(|h| match Introduction::read(h.body(path)).form {
            Form::Graph(line) | Form::GraphListed(line) => Some(GraphLetters {
                graph: line.graph,
                vertices: line.vertices,
                edges: line.edges,
            }),
            _ => None,
        })
}

/// Whether a record's statement is written out where it is used: a phrase
/// a define gives, or a definition of a graph's notion.
fn written_where_used(r: &Record) -> bool {
    r.kind == RecordKind::Definition
        && (r.phrase.is_some() || graph_letters(&r.hypotheses, &r.path).is_some())
}

/// The graph letters of each record that names a graph, by its full name.
pub fn record_graphs(records: &[Record]) -> IndexMap<String, GraphLetters> {
    records
        .iter()
        .filter_map(|r| {
            graph_letters(&r.hypotheses, &r.path)
                .map(|g| (format!("{}/{}", r.module(), r.name), g))
        })
        .collect()
}

/// Where a fact is supplied, with `out` applied to what each line it names
/// writes there, those inside what lines give together among them.
fn supplied_written(by: &mut super::record::SuppliedBy, out: &impl Fn(&Node) -> Node) {
    match by {
        SuppliedBy::Line(at) | SuppliedBy::SaidOnce(at) => {
            at.written = out(&at.written)
        }
        SuppliedBy::Through { carrier, member } => {
            supplied_written(carrier, out);
            supplied_written(member, out);
        }
        SuppliedBy::Parts(parts) => {
            for p in parts {
                supplied_written(p, out);
            }
        }
        // The walk's own fact is as the walk read it; where each part it
        // took from a line stands is a line's like any other.
        SuppliedBy::Walked(walked) => {
            for part in &mut walked.stated {
                supplied_written(&mut part.by, out);
            }
        }
        SuppliedBy::Requires { .. }
        | SuppliedBy::Bound { .. }
        | SuppliedBy::Identity(_)
        | SuppliedBy::Unstated => {}
    }
}

/// The parts of a definition's right side (`Cited::unfolded`) with `out`
/// applied to each fact, witness and place.
fn unfolded_written(
    parts: &mut [super::record::Unfolded],
    out: &impl Fn(&Node) -> Node,
) {
    for part in parts {
        match part {
            Unfolded::Fact { fact, by, .. } => {
                *fact = out(fact);
                supplied_written(by, out);
            }
            Unfolded::Witness {
                value,
                member,
                body,
            } => {
                *value = out(value);
                unfolded_written(slice::from_mut(member.as_mut()), out);
                unfolded_written(body, out);
            }
        }
    }
}

/// The record with the theorem's outside defines and phrases written out;
/// None where it has none of either, and the record stands as read.
pub fn written_out(
    checked: &CheckedCorpus,
    ctx: &Context,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Option<CheckedTheorem> {
    // The file's functions, and the header's of more than one argument,
    // c(j, y), which a backend has no letter of one type for: each written
    // out where it is applied.
    let several = |d: &Defined| matches!(d, Defined::Rule(r) if r.params.len() > 1);
    let rules: Definitions = rec
        .outside
        .iter()
        .filter(|(_, d)| matches!(d, Defined::Rule(_)))
        .chain(
            rec.statement_definitions
                .iter()
                .filter(|(n, d)| several(d) && !rec.outside.contains_key(*n)),
        )
        .map(|(n, d)| (n.clone(), d.clone()))
        .collect();
    let phrases = phrase_meanings(checked, rec);
    let written_page = rec
        .page
        .entries()
        .flat_map(|(_, n)| n.walk())
        .any(|n| phrases.contains_key(&n.notation()));
    if rules.is_empty() && !written_page {
        return None;
    }
    let graph = graph_letters(&thm.hypotheses, &thm.path);
    let out = |n: &Node| {
        let n = matching::expand(n, &rules);
        phrases_written(&n, &phrases, &checked.grammar, graph.as_ref(), 8)
    };
    let binding =
        |b: &Binding| -> Binding { b.iter().map(|(k, v)| (*k, out(v))).collect() };
    let mut written = rec.clone();
    // A define written out here is written out in every line the build is
    // handed, so no reason is left to read it written out.
    for names in written.defines_read.values_mut() {
        names.retain(|name| !rules.contains_key(name));
    }
    written.defines_read.retain(|_, names| !names.is_empty());
    written.page = super::record::PageReading::new(
        rec.page
            .entries()
            .map(|(k, n)| (k.clone(), out(n)))
            .collect(),
    );
    written.asserted = rec
        .asserted
        .iter()
        .map(|line| line.iter().map(out).collect())
        .collect();
    // The statement's defines, E = {c ∈ O : c is a counting ahead through
    // m + n}, with the phrases in their terms written as their meanings,
    // as the page's lines are.
    for d in written.statement_definitions.values_mut() {
        if let Defined::Term(t) = d {
            *t = out(t);
        }
    }
    for c in written
        .cited
        .iter_mut()
        .flatten()
        .chain(written.cited_requires.values_mut())
    {
        c.binding = binding(&c.binding);
        for f in c.firsts.iter_mut().flatten() {
            f.asked = out(&f.asked);
            supplied_written(&mut f.by, &out);
        }
        for s in &mut c.supplied {
            supplied_written(&mut s.by, &out);
            for w in &mut s.witnesses {
                w.value = out(&w.value);
                w.said = out(&w.said);
                supplied_written(&mut w.member, &out);
            }
        }
        for parts in c.unfolded.iter_mut().flatten() {
            unfolded_written(parts, &out);
        }
    }
    for all in written.exhibited.values_mut() {
        for e in all.iter_mut().flatten() {
            e.values = binding(&e.values);
            for s in &mut e.shown {
                supplied_written(&mut s.by, &out);
            }
        }
    }
    for read in written.read_at.iter_mut().flatten() {
        read.said = out(&read.said);
        read.opened_by.written = out(&read.opened_by.written);
    }
    for said in written
        .bounds
        .iter_mut()
        .chain([&mut written.statement_bounds])
    {
        for b in &mut said.terms {
            b.term = out(&b.term);
        }
        for line in &mut said.over_ranges {
            *line = out(line);
        }
    }
    for owed in written.blocks.iter_mut().flat_map(|b| &mut b.owes) {
        owed.written = owed.written.iter().map(out).collect();
    }
    for s in written.supposed.values_mut() {
        s.against = out(&s.against);
    }
    let chained = written
        .links
        .values_mut()
        .flat_map(|chain| chain.links.iter_mut())
        .filter_map(|link| match link.at.as_mut() {
            Some(super::record::OrderFact::Line(at)) => Some(at),
            _ => None,
        });
    let order_facts = written
        .orders
        .values_mut()
        .flat_map(|o| o.sentences.iter_mut().flatten())
        .flat_map(|p| {
            p.uses
                .iter_mut()
                .chain(p.split.iter_mut())
                .chain(p.restates.as_mut().map(|r| &mut r.by))
        });
    let mut made_facts = Vec::new();
    for made in written.combinations.values_mut() {
        for m in made_parts(made, &mut made_facts) {
            *m = out(m);
        }
    }
    let mut ordered = Vec::new();
    for fact in order_facts.chain(made_facts) {
        match fact {
            super::record::OrderFact::Line(at) => ordered.push(at),
            super::record::OrderFact::Kind { written, .. }
            | super::record::OrderFact::Member { written, .. } => {
                *written = out(written)
            }
            _ => {}
        }
    }
    let antisymmetric = written
        .antisymmetric
        .values_mut()
        .flat_map(|a| [&mut a.below, &mut a.above]);
    let joined = written
        .joined
        .values_mut()
        .flatten()
        .flatten()
        .map(|p| &mut p.at);
    let joined_wholes = written
        .joined_wholes
        .values_mut()
        .flatten()
        .map(|w| &mut w.at);
    for at in written
        .link_places
        .values_mut()
        .chain(written.restated.values_mut().filter_map(|r| r.at_mut()))
        .chain(chained)
        .chain(ordered)
        .chain(antisymmetric)
        .chain(joined)
        .chain(joined_wholes)
    {
        at.written = out(&at.written);
    }
    for part in written.joined_claim.values_mut().flatten() {
        *part = out(part);
    }
    for r in written.restated.values_mut() {
        if let super::record::Restated::Lines(by) = r {
            supplied_written(by, &out);
        }
    }
    for i in written.instantiated.values_mut() {
        i.at.written = out(&i.at.written);
        for g in &mut i.guards {
            g.written = out(&g.written);
        }
        for c in &mut i.conditions {
            c.read = out(&c.read);
        }
        let bys = i
            .guards
            .iter_mut()
            .map(|g| &mut g.by)
            .chain(i.conditions.iter_mut().map(|c| &mut c.by));
        for by in bys {
            supplied_written(by, &out);
        }
    }
    for c in written.contradicted.values_mut() {
        c.at.written = out(&c.at.written);
    }
    for c in written.cases_from.values_mut() {
        c.at.written = out(&c.at.written);
    }
    for at in written
        .introduced_at
        .iter_mut()
        .flat_map(|m| m.values_mut())
    {
        at.written = out(&at.written);
    }
    for p in written.obtained_parts.values_mut().flatten() {
        p.owed_written = out(&p.owed_written);
    }
    for at in written.obtained_from.values_mut() {
        at.written = out(&at.written);
    }
    // A substitution's places are paths into what it is put into, which
    // writing a define out moves, s(n + (j + 1)) becoming a sum over its
    // range: they are found again between the start written out and what
    // the putting makes of the page's start, written out. Where writing the
    // defines out makes the start what the putting makes, s(t) < 10 of
    // `s(t) = (t + 1) mod 10` put into (t + 1) mod 10 < 10, the line is the
    // claim as written out, and there is no place to put at. One whose
    // places are not found so is left out, as one never recorded.
    let substitution_written = |s: &mut super::record::Substituted| -> bool {
        let [left, right] = s.equation.children.as_slice() else {
            return false;
        };
        let now = match s.put.turned {
            false => right,
            true => left,
        };
        let made = matching::put_at_places(&s.start, &s.put.places, now);
        let (start, made) = (out(&s.start), out(&made));
        let (left, right) = (out(left), out(right));
        let put = match matching::substitution_places(&start, &made, &left, &right) {
            Some(put) => put,
            None if matching::alike_top(&start, &made, ctx) => SubstitutionPlaces {
                turned: s.put.turned,
                places: Vec::new(),
            },
            None => return false,
        };
        s.equation = out(&s.equation);
        s.start = start;
        s.put = put;
        if let Some(from) = &mut s.from {
            from.written = out(&from.written);
        }
        if let super::record::SubstitutedInto::Line(at) = &mut s.into {
            at.written = out(&at.written);
        }
        true
    };
    written.substituted.retain(|_, s| substitution_written(s));
    written
        .substituted_rows
        .retain(|_, s| substitution_written(s));
    written
        .substituted_sentences
        .retain(|_, s| substitution_written(s));
    let beside_written = |b: &mut super::record::Besides| {
        let mut at = Some(b);
        while let Some(b) = at {
            b.equation = out(&b.equation);
            b.other = out(&b.other);
            b.other_stated = b.other_stated.as_ref().map(out);
            if let Some(row) = &mut b.other_row {
                row.left = out(&row.left);
                row.right = out(&row.right);
            }
            at = b.other_beside.as_deref_mut();
        }
    };
    for shown in written
        .places_shown
        .iter_mut()
        .flatten()
        .chain(written.members_shown.values_mut())
    {
        shown.term = out(&shown.term);
        match &mut shown.by {
            ShownBy::Beside(b) => beside_written(b),
            ShownBy::Typed { map, at } => {
                *map = out(map);
                *at = out(at);
            }
            ShownBy::Define { value } => *value = out(value),
            ShownBy::Said => {}
        }
    }
    for part in written.divided_by.values_mut().flatten() {
        part.term = out(&part.term);
        if let super::record::NonzeroBy::Stated { line, from, .. } = &mut part.by {
            *line = out(line);
            *from = out(from);
        }
    }
    for member in written.at_member.values_mut() {
        member.set = out(&member.set);
    }
    for held in written.held_by_lines.values_mut().flatten() {
        held.term = out(&held.term);
        held.shown.nodes_mut(&mut |n| *n = out(n));
    }
    // The sets the page makes finite, read of the page as written here: a
    // letter bound in a define written out, the c of {c ∈ 𝒫{1, …, k} : …},
    // is one the page as read does not bind.
    written.said_finite = super::finite_of(ctx, thm, &written);
    // What the lines in scope at each step make finite, the same facts with
    // the sets and the lines they are read from written out, as the page
    // here writes them: deg(x) as the count it stands for.
    written.finite_at = rec
        .finite_at
        .iter()
        .map(|sets| {
            sets.iter()
                .map(|(set, why)| {
                    (written_key(set, &out), finite_by_written(why, &out))
                })
                .collect()
        })
        .collect();
    written.finite_under = super::formulas::finite_under(&written.page);
    written.set_systems = super::set_systems_of(&written);
    written.element_systems = super::element_systems_of(&written);
    written.function_systems = super::function_systems_of(&written);
    Some(written)
}

/// A tree keyed by its shape, written out.
/// The multipliers an `algebra` making writes, each to be written out;
/// the facts it takes are put in `facts`.
fn made_parts<'m>(
    made: &'m mut AlgebraMade,
    facts: &mut Vec<&'m mut OrderFact>,
) -> Vec<&'m mut Node> {
    match made {
        AlgebraMade::Sum(sum) => sum
            .terms
            .iter_mut()
            .map(|t| {
                facts.push(&mut t.fact);
                &mut t.multiplier
            })
            .collect(),
        AlgebraMade::Rescaled(r) => {
            facts.push(&mut r.fact);
            vec![&mut r.by, &mut r.back.multiplier]
        }
        AlgebraMade::Pairs(each) => each
            .iter_mut()
            .flat_map(|(_, one)| made_parts(one, facts))
            .collect(),
    }
}

fn written_key(key: &ByShape, out: &impl Fn(&Node) -> Node) -> ByShape {
    ByShape(out(&key.0))
}

/// Why a set is finite, each line and set it names written out.
fn finite_by_written(why: &FiniteBy, out: &impl Fn(&Node) -> Node) -> FiniteBy {
    let boxed = |w: &FiniteBy| Box::new(finite_by_written(w, out));
    match why {
        FiniteBy::Said(line) => FiniteBy::Said(written_key(line, out)),
        FiniteBy::Counted { line, at_least_one } => FiniteBy::Counted {
            line: written_key(line, out),
            at_least_one: *at_least_one,
        },
        FiniteBy::Covered { line, over } => FiniteBy::Covered {
            line: written_key(line, out),
            over: boxed(over),
        },
        FiniteBy::Part { line, whole } => FiniteBy::Part {
            line: written_key(line, out),
            whole: boxed(whole),
        },
        FiniteBy::Define(name) => FiniteBy::Define(name.clone()),
        FiniteBy::Bound(name) => FiniteBy::Bound(name.clone()),
        FiniteBy::MemberOf(w) => FiniteBy::MemberOf(boxed(w)),
        FiniteBy::Made(made) => FiniteBy::Made(match made {
            Making::Empty => Making::Empty,
            Making::Listed => Making::Listed,
            Making::Range => Making::Range,
            Making::Minus(w) => Making::Minus(boxed(w)),
            Making::Inter(w) => Making::Inter(boxed(w)),
            Making::Union(a, b) => Making::Union(boxed(a), boxed(b)),
            Making::Powerset(w) => Making::Powerset(boxed(w)),
            Making::Builder(w) => Making::Builder(boxed(w)),
            Making::Image(w) => Making::Image(boxed(w)),
            Making::Coset(w) => Making::Coset(boxed(w)),
            Making::Applied(name) => Making::Applied(name.clone()),
            Making::Functions(a, b) => Making::Functions(boxed(a), boxed(b)),
            Making::Product(a, b) => Making::Product(boxed(a), boxed(b)),
        }),
    }
}

/// Each item's groups, by its full name (`LibraryReading::groups`).
pub type Groups = IndexMap<String, Option<Arc<Vec<Group>>>>;

/// Each phrase the library's phrase defines give, by its notation, read
/// from the definition records' own groups, for the items that state one.
pub fn library_phrases(
    records: &[Record],
    groups: &Groups,
) -> IndexMap<NotationId, Phrase> {
    let mut out = IndexMap::new();
    for r in records.iter().filter(|r| written_where_used(r)) {
        let full = format!("{}/{}", r.module(), r.name);
        let Some(Some(groups)) = groups.get(&full) else {
            continue;
        };
        let graph = graph_letters(&r.hypotheses, &r.path);
        for read in groups.iter().flat_map(|g| &g.gives) {
            if let Some((notation, phrase)) = phrase_of(read, graph.clone()) {
                out.insert(notation, phrase);
            }
        }
    }
    out
}

/// An item's group with each phrase in it written out as its meaning, as a
/// theorem's page is (`written_out`); `graph` is the graph the item's own
/// `let` line names.
pub fn group_written(
    group: &Group,
    phrases: &IndexMap<NotationId, Phrase>,
    grammar: &Grammar,
    graph: Option<&GraphLetters>,
) -> Group {
    let out = |n: &Node| phrases_written(n, phrases, grammar, graph, 8);
    Group {
        wants: group
            .wants
            .iter()
            .map(|w| Want {
                tree: out(&w.tree),
                ..w.clone()
            })
            .collect(),
        gives: group.gives.iter().map(out).collect(),
        functions: group.functions.clone(),
        identities: group.identities.clone(),
    }
}

/// What each group of each item says of its terms, its phrases written out
/// (`group_written`), by the item's full name and the group's place
/// (`LibraryReading::item_facts`).
pub fn item_facts(
    groups: &Groups,
    phrases: &IndexMap<NotationId, Phrase>,
    grammar: &Grammar,
    ctx: &Context,
    function_types: &IndexMap<String, Vec<Want>>,
    graphs: &IndexMap<String, GraphLetters>,
) -> IndexMap<String, Vec<super::record::GroupFacts>> {
    let mut out = IndexMap::new();
    for (full, read) in groups {
        let Some(read) = read else {
            continue;
        };
        let graph = graphs.get(full);
        let typed: Vec<Node> = function_types
            .get(full)
            .into_iter()
            .flatten()
            .map(|t| t.tree.clone())
            .collect();
        let facts = read
            .iter()
            .map(|g| {
                group_facts(&group_written(g, phrases, grammar, graph), &typed, ctx)
            })
            .collect();
        out.insert(full.clone(), facts);
    }
    out
}

/// `item_facts` of one group, read as the shared rules read a theorem's
/// lines: what its hypotheses bound below and make finite, a set only its
/// conclusion says is finite being counted after it; and for each sentence
/// it concludes, the number system each set letter of numbers holds by the
/// hypotheses and that sentence; and the systems of the function letters
/// its function-type lines, `typed`, and hypotheses give a type.
fn group_facts(
    group: &Group,
    typed: &[Node],
    ctx: &Context,
) -> super::record::GroupFacts {
    let wants: Vec<Node> = group.asked().cloned().collect();
    let none = Introduced::new();
    let set_systems = group
        .gives
        .iter()
        .map(|says| {
            let said: Vec<&Node> = wants.iter().chain(iter::once(says)).collect();
            number_sets::set_letter_systems(&said)
        })
        .collect();
    // A count is at least 1 by the number systems the item's own hypotheses
    // put its letters in, k + 1 of a k ∈ ℕ₀ (`citing::introduction`), and
    // what they bound.
    let mut letters = Introduced::new();
    for want in &wants {
        if let Some((letter, system)) = citing::introduction(want) {
            letters.insert(letter, system);
        }
    }
    let bounds = super::bounds::said_by(&wants, &none, ctx);
    let positive = super::bounds::positive_by(&letters, &bounds, ctx);
    let finite = finite::said_finite(&wants, &[], &[], &positive);
    let lines: Vec<&Node> = typed.iter().chain(&wants).collect();
    let function_systems = number_sets::function_systems(&lines, &IndexMap::new());
    super::record::GroupFacts {
        bounds,
        finite,
        set_systems,
        function_systems,
    }
}

/// Each phrase a theorem can read, by its notation, as the Metamath build
/// reads it (`Elaborator::phrase_meanings`).
fn phrase_meanings(
    checked: &CheckedCorpus,
    rec: &CheckedTheorem,
) -> IndexMap<NotationId, Phrase> {
    let mut out = IndexMap::new();
    for r in checked
        .corpus
        .records
        .iter()
        .filter(|r| written_where_used(r))
    {
        let graph = graph_letters(&r.hypotheses, &r.path);
        for written in r.stated() {
            let Ok(sentence) = written.formula() else {
                continue;
            };
            let Some(Ok(read)) = rec.items.get(&sentence) else {
                continue;
            };
            if let Some((notation, phrase)) = phrase_of(read, graph.clone()) {
                out.insert(notation, phrase);
            }
        }
    }
    out
}

/// The phrase a definition's statement gives, `P(c, k) ↔ meaning` of a
/// phrase whose slots are letters, or `deg(x) = term` of a graph's notion,
/// by its notation; None for any other statement. `graph` is the graph the
/// definition's `let` line names.
fn phrase_of(read: &Node, graph: Option<GraphLetters>) -> Option<(NotationId, Phrase)> {
    let [phrase, meaning] = read.children.as_slice() else {
        return None;
    };
    let defines = read.notation() == BICONDITIONAL
        || (graph.is_some() && read.spelling() == EQUALS);
    if !defines || phrase.is_name() || !phrase.children.iter().all(Node::is_name) {
        return None;
    }
    Some((
        phrase.notation(),
        Phrase {
            slots: phrase.children.iter().map(|c| c.text).collect(),
            meaning: meaning.clone(),
            graph,
        },
    ))
}

/// The tree with each phrase written out as its meaning at what fills its
/// slots, the meaning's own letters kept apart from what is put in. A
/// graph's notion is written out only where `graph`, the page's own, is
/// there for the letters of the definition's graph to be.
fn phrases_written(
    node: &Node,
    phrases: &IndexMap<NotationId, Phrase>,
    grammar: &Grammar,
    graph: Option<&GraphLetters>,
    depth: usize,
) -> Node {
    if depth == 0 {
        return node.clone();
    }
    if let Some(p) = phrases.get(&node.notation()) {
        let put = match (&p.graph, graph) {
            (None, _) => Some(Binding::new()),
            (Some(theirs), Some(ours)) => Some(graph_put(&p.meaning, theirs, ours)),
            (Some(_), None) => None,
        };
        if let Some(mut put) = put.filter(|_| p.slots.len() == node.children.len()) {
            for (slot, value) in
                p.slots.iter().copied().zip(node.children.iter().cloned())
            {
                put.insert(slot, value);
            }
            let at =
                matching::substitute_apart_by(&p.meaning, &put, &grammar.binders());
            return phrases_written(&at, phrases, grammar, graph, depth - 1);
        }
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| phrases_written(c, phrases, grammar, graph, depth))
            .collect(),
    )
}

/// The definition's graph letters the meaning uses, each put as the page's
/// own graph letter of the same part.
fn graph_put(meaning: &Node, theirs: &GraphLetters, ours: &GraphLetters) -> Binding {
    let pairs = [
        (&theirs.graph, &ours.graph),
        (&theirs.vertices, &ours.vertices),
        (&theirs.edges, &ours.edges),
    ];
    let walked = meaning.walk();
    let mut put = Binding::new();
    for (from, to) in pairs {
        if let Some(n) = walked.iter().find(|n| n.is_name() && *n.text == **from) {
            put.insert(n.text, Node::name(n.sort.clone(), to));
        }
    }
    put
}
