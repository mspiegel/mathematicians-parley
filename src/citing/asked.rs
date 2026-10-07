//! What an item a citation names asks for there.

use std::collections::BTreeSet;

use indexmap::IndexMap;

use crate::formula::Node;
use crate::matching::{fresh_letters, substitute_apart, Binding, Context, PROPERTY};
use crate::outcome::{Built, Declined, Route};

use super::conclude::{taken, Taken};
use super::library::Library;
use super::parts::Parts;

/// What an item asks of one citation: the group the citation takes and the
/// binding it takes it under, and the item's hypotheses said at the citation.
pub struct Asked {
    pub taken: Taken,
    /// Each hypothesis of the group taken, and what each function-type `let`
    /// line of the item says (`Library::function_types`), with the item's
    /// letters replaced by what they stand for. One with a letter the
    /// citation leaves unfixed is left out: `let t : {a, …, b} → ℝ`, where t
    /// stands for a summand, asks nothing a line could write.
    pub hypotheses: Vec<Node>,
}

/// What the item of that full name asks of a citation with these parts;
/// declined where no group of the item concludes what the citation claims.
pub fn asked(name: &str, parts: &Parts, library: &Library) -> Route<Asked> {
    let Some(groups) = library.groups(name) else {
        return Route::no("no item has that name");
    };
    let taken = match taken(&groups, &parts.claims, &parts.facts, &parts.seed, library)
    {
        Built(t) => t,
        Declined(d) => return Declined(d),
    };
    let wants = groups[taken.group].wants.iter().map(|(_, t)| t.clone());
    let typed = library.function_types(name);
    let mut hypotheses = Vec::new();
    for asks in wants.chain(typed) {
        let unfixed = asks.names().iter().any(|n| {
            let fixed = taken.binding.get(n).is_some_and(|b| b.notation != PROPERTY);
            !fixed && !library.env.g.functions.contains_key(n)
        });
        if !unfixed {
            hypotheses.push(filled(&asks, &taken.binding, &library.ctx));
        }
    }
    Built(Asked { taken, hypotheses })
}

/// `node` with each name `bound` fixes replaced by what it stands for, and a
/// letter bound to a rule applied where the node applies it.
pub fn filled(node: &Node, bound: &Binding, ctx: &Context) -> Node {
    if node.is_name() {
        return match bound.get(&node.text) {
            Some(stands) if stands.notation != PROPERTY => stands.clone(),
            _ => node.clone(),
        };
    }
    if ctx.props.contains_key(&node.notation)
        && node.children.len() == 2
        && node.children[0].is_name()
    {
        if let Some(rule) = bound.get(&node.children[0].text) {
            if rule.notation == PROPERTY {
                let mut at = Binding::new();
                at.insert(rule.text.clone(), filled(&node.children[1], bound, ctx));
                return substitute_apart(&rule.children[0], &at, ctx);
            }
        }
    }
    if node.children.is_empty() {
        return node.clone();
    }
    // Under a binder its own letters are its own, and a value that mentions
    // one is kept apart from it, as `substitute_apart` keeps it: prime-factor's
    // `there is p ∈ ℕ with … p divides m` at m := p! + 1 binds another letter,
    // and never the p of p!.
    let (held, body) = ctx.held_body(&node.notation);
    if !held.is_empty() && held.iter().all(|&at| node.children[at].is_name()) {
        let own: BTreeSet<String> = held
            .iter()
            .map(|&at| node.children[at].text.clone())
            .collect();
        let mut inner: Binding = bound
            .iter()
            .filter(|(k, _)| !own.contains(*k))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let mut used = node.names();
        for v in bound.values() {
            used.extend(v.names());
        }
        let mut spelt: IndexMap<usize, Node> = IndexMap::new();
        for &at in &held {
            let var = &node.children[at];
            if bound
                .iter()
                .any(|(k, v)| !own.contains(k) && v.names().contains(&var.text))
            {
                let letter = fresh_letters()
                    .into_iter()
                    .find(|c| !used.contains(c))
                    .unwrap_or_default();
                let fresh = Node::leaf("name", var.sort.clone(), &letter);
                used.insert(letter);
                spelt.insert(at, fresh.clone());
                inner.insert(var.text.clone(), fresh);
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
                    filled(c, &inner, ctx)
                } else {
                    filled(c, bound, ctx)
                }
            })
            .collect();
        return Node::new(&node.notation, node.sort.clone(), children, &node.text);
    }
    Node::new(
        &node.notation,
        node.sort.clone(),
        node.children
            .iter()
            .map(|c| filled(c, bound, ctx))
            .collect(),
        &node.text,
    )
}
