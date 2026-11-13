//! Each theorem's record as the page reads with what the theorem's file
//! defines outside it written out, and each phrase written as its meaning
//! (`CheckedTheorem::written`): T(k + 1) of `define T(k) := k(k + 1)/2` as
//! (k + 1)(k + 2)/2, as the Metamath build reads it (`elab::reading`). A
//! backend with no name for such a function, as Lean has none, reads this
//! record; the facts read from the page are read again of the page as
//! written, a letter a define written out binds being one the page as read
//! does not.

use indexmap::IndexMap;

use super::record::CheckedTheorem;
use super::CheckedCorpus;
use crate::corpus::Theorem;
use crate::formula::notation_id::NotationId;
use crate::formula::{Grammar, Node};

/// A phrase a define gives, `c is a counting ahead through k`: its slots
/// and what it means, from the definition record the define stands for,
/// whose statement is the phrase, `↔`, and the meaning.
pub struct Phrase {
    slots: Vec<crate::formula::symbol::Symbol>,
    meaning: Node,
}

/// Where a fact is supplied, with `out` applied to what each line it names
/// writes there, those inside what lines give together among them.
fn supplied_written(by: &mut super::record::SuppliedBy, out: &impl Fn(&Node) -> Node) {
    use super::record::SuppliedBy;
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
        SuppliedBy::Requires { .. }
        | SuppliedBy::Walked(_)
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
    use super::record::Unfolded;
    for part in parts {
        match part {
            Unfolded::Fact { fact, by } => {
                *fact = out(fact);
                supplied_written(by, out);
            }
            Unfolded::Witness {
                value,
                member,
                body,
            } => {
                *value = out(value);
                unfolded_written(std::slice::from_mut(member.as_mut()), out);
                unfolded_written(body, out);
            }
        }
    }
}

/// The record with the theorem's outside defines and phrases written out;
/// None where it has none of either, and the record stands as read.
pub fn written_out(
    checked: &CheckedCorpus,
    ctx: &crate::matching::Context,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Option<CheckedTheorem> {
    let rules: crate::matching::Definitions = rec
        .outside
        .iter()
        .filter(|(_, d)| matches!(d, crate::matching::Defined::Rule(_)))
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
    let out = |n: &Node| {
        let n = crate::matching::expand(n, &rules);
        phrases_written(&n, &phrases, &checked.grammar, 8)
    };
    let binding = |b: &crate::matching::Binding| -> crate::matching::Binding {
        b.iter().map(|(k, v)| (*k, out(v))).collect()
    };
    let mut written = rec.clone();
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
    for c in written
        .cited
        .iter_mut()
        .flatten()
        .chain(written.cited_requires.values_mut())
    {
        c.binding = binding(&c.binding);
        for f in &mut c.firsts {
            supplied_written(f, &out);
        }
        for s in &mut c.supplied {
            supplied_written(&mut s.by, &out);
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
    let mut ordered = Vec::new();
    for fact in order_facts {
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
    let joined = written.joined.values_mut().flatten().flatten();
    for at in written
        .link_places
        .values_mut()
        .chain(written.restated.values_mut())
        .chain(chained)
        .chain(ordered)
        .chain(antisymmetric)
        .chain(joined)
    {
        at.written = out(&at.written);
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
        let made = crate::matching::put_at_places(&s.start, &s.put.places, now);
        let (start, made) = (out(&s.start), out(&made));
        let (left, right) = (out(left), out(right));
        let put =
            match crate::matching::substitution_places(&start, &made, &left, &right) {
                Some(put) => put,
                None if crate::matching::alike_top(&start, &made, ctx) => {
                    crate::matching::SubstitutionPlaces {
                        turned: s.put.turned,
                        places: Vec::new(),
                    }
                }
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
        b.equation = out(&b.equation);
        b.other = out(&b.other);
        b.other_stated = b.other_stated.as_ref().map(out);
    };
    for shown in written
        .places_shown
        .iter_mut()
        .flatten()
        .chain(written.members_shown.values_mut())
    {
        shown.term = out(&shown.term);
        if let super::record::ShownBy::Beside(b) = &mut shown.by {
            beside_written(b);
        }
    }
    for held in written.held_by_lines.values_mut().flatten() {
        use super::record::LinesHold;
        held.term = out(&held.term);
        match &mut held.by {
            LinesHold::Stated { line } => *line = out(line),
            LinesHold::Beside(b) => beside_written(b),
            LinesHold::Closed => {}
        }
    }
    // The sets the page makes finite, read of the page as written here: a
    // letter bound in a define written out, the c of {c ∈ 𝒫{1, …, k} : …},
    // is one the page as read does not bind.
    written.said_finite = super::finite_of(&checked.grammar, ctx, thm, &written);
    written.set_systems = super::set_systems_of(&written);
    written.element_systems = super::element_systems_of(&written);
    written.function_systems = super::function_systems_of(&written);
    Some(written)
}

/// Each item's groups, by its full name (`LibraryReading::groups`).
pub type Groups = IndexMap<String, Option<std::sync::Arc<Vec<crate::citing::Group>>>>;

/// Each phrase the library's phrase defines give, by its notation, read
/// from the definition records' own groups, for the items that state one.
pub fn library_phrases(
    records: &[crate::corpus::Record],
    groups: &Groups,
) -> IndexMap<NotationId, Phrase> {
    let mut out = IndexMap::new();
    let made = records.iter().filter(|r| {
        r.phrase.is_some() && r.kind == crate::corpus::RecordKind::Definition
    });
    for r in made {
        let full = format!("{}/{}", r.module(), r.name);
        let Some(Some(groups)) = groups.get(&full) else {
            continue;
        };
        for read in groups.iter().flat_map(|g| &g.gives) {
            if let Some((notation, phrase)) = phrase_of(read) {
                out.insert(notation, phrase);
            }
        }
    }
    out
}

/// An item's group with each phrase in it written out as its meaning, as a
/// theorem's page is (`written_out`).
pub fn group_written(
    group: &crate::citing::Group,
    phrases: &IndexMap<NotationId, Phrase>,
    grammar: &Grammar,
) -> crate::citing::Group {
    let out = |n: &Node| phrases_written(n, phrases, grammar, 8);
    crate::citing::Group {
        wants: group
            .wants
            .iter()
            .map(|w| crate::citing::Want {
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
    ctx: &crate::matching::Context,
) -> IndexMap<String, Vec<super::record::GroupFacts>> {
    let mut out = IndexMap::new();
    for (full, read) in groups {
        let Some(read) = read else {
            continue;
        };
        let facts = read
            .iter()
            .map(|g| group_facts(&group_written(g, phrases, grammar), grammar, ctx))
            .collect();
        out.insert(full.clone(), facts);
    }
    out
}

/// `item_facts` of one group, read as the shared rules read a theorem's
/// lines: what its hypotheses bound below and make finite, a set only its
/// conclusion says is finite being counted after it; and for each sentence
/// it concludes, the number system each set letter of numbers holds by the
/// hypotheses and that sentence.
fn group_facts(
    group: &crate::citing::Group,
    grammar: &Grammar,
    ctx: &crate::matching::Context,
) -> super::record::GroupFacts {
    let wants: Vec<Node> = group.asked().cloned().collect();
    let none = crate::citing::Introduced::new();
    let set_systems = group
        .gives
        .iter()
        .map(|says| {
            let said: Vec<&Node> = wants.iter().chain(std::iter::once(says)).collect();
            crate::citing::number_sets::set_letter_systems(&said, &none)
        })
        .collect();
    // A count is at least 1 by the number systems the item's own hypotheses
    // put its letters in, k + 1 of a k ∈ ℕ₀ (`citing::introduction`), and
    // what they bound.
    let mut letters = crate::citing::Introduced::new();
    for want in &wants {
        if let Some((letter, system)) = crate::citing::introduction(want, &letters) {
            letters.insert(letter, system);
        }
    }
    let bounds = super::bounds::said_by(&wants, &none, ctx);
    let positive = super::bounds::positive_by(&letters, &bounds, ctx);
    let finite =
        crate::citing::finite::said_finite(grammar, &wants, &[], &[], &positive);
    super::record::GroupFacts {
        bounds,
        finite,
        set_systems,
    }
}

/// Each phrase a theorem can read, by its notation, as the Metamath build
/// reads it (`Elaborator::phrase_meanings`).
fn phrase_meanings(
    checked: &CheckedCorpus,
    rec: &CheckedTheorem,
) -> IndexMap<NotationId, Phrase> {
    let mut out = IndexMap::new();
    let made = checked.corpus.records.iter().filter(|r| {
        r.phrase.is_some() && r.kind == crate::corpus::RecordKind::Definition
    });
    for r in made {
        for written in r.stated() {
            let Ok(sentence) = written.formula() else {
                continue;
            };
            let Some(Ok(read)) = rec.items.get(&sentence) else {
                continue;
            };
            if let Some((notation, phrase)) = phrase_of(read) {
                out.insert(notation, phrase);
            }
        }
    }
    out
}

/// The phrase a definition's statement gives, `P(c, k) ↔ meaning` of a
/// phrase whose slots are letters, by its notation; None for any other
/// statement.
fn phrase_of(read: &Node) -> Option<(NotationId, Phrase)> {
    let [phrase, meaning] = read.children.as_slice() else {
        return None;
    };
    if read.notation() != crate::notations::BICONDITIONAL
        || !phrase.children.iter().all(Node::is_name)
    {
        return None;
    }
    Some((
        phrase.notation(),
        Phrase {
            slots: phrase.children.iter().map(|c| c.text).collect(),
            meaning: meaning.clone(),
        },
    ))
}

/// The tree with each phrase written out as its meaning at what fills its
/// slots, the meaning's own letters kept apart from what is put in.
fn phrases_written(
    node: &Node,
    phrases: &IndexMap<NotationId, Phrase>,
    grammar: &Grammar,
    depth: usize,
) -> Node {
    if depth == 0 {
        return node.clone();
    }
    if let Some(p) = phrases.get(&node.notation()) {
        if p.slots.len() == node.children.len() {
            let put: crate::matching::Binding = p
                .slots
                .iter()
                .copied()
                .zip(node.children.iter().cloned())
                .collect();
            let at = crate::matching::substitute_apart_by(
                &p.meaning,
                &put,
                &grammar.binders(),
            );
            return phrases_written(&at, phrases, grammar, depth - 1);
        }
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| phrases_written(c, phrases, grammar, depth))
            .collect(),
    )
}
