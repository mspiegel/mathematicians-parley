//! Whether a citation's facts supply the patterns an item asks for.

use std::borrow::Cow;
use std::collections::BTreeSet;

use indexmap::IndexSet;

use crate::formula::{Node, NodeId};
use crate::matching::{match_tree, substitute_apart, Binding, Context, PROPERTY};
use crate::rules;

use super::library::{either_way, Library};

/// The places in a pattern where a binder applies a property or a function to
/// what it binds, which decide what the property or function stands for
/// (`matching::binding_sites`).
pub type Sites = IndexSet<NodeId>;

/// Every name the trees use.
pub fn names_of(trees: &[Node]) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for t in trees {
        out.extend(t.names());
    }
    out
}

/// Every hypothesis is stated by one of the facts.
///
/// A hypothesis that is a "there is" may instead be stated by a fact giving
/// its body with some value in place of the bound variable, which is the
/// move `SYNTAX.md` describes for exhibit: the cited line determines the
/// value and the text never writes it. `there is s ∈ S`, which says only
/// that S has a member, is stated by any fact putting something in S.
pub fn supply(
    patterns: &[Node],
    facts: &[Node],
    binding: &Binding,
    variables: &BTreeSet<String>,
    library: &Library,
    sites: &Sites,
    reuse: bool,
) -> Option<Binding> {
    let mut used = vec![false; facts.len()];
    search(
        patterns, facts, &mut used, binding, variables, library, sites, reuse, None,
    )
}

/// A search asked for every way the facts supply the hypotheses, rather
/// than the first: the facts the attempt in hand has taken, by index, and
/// what to do with each way once it is complete, given the facts it took
/// and the binding it supplied them under.
pub struct Ways<'v> {
    pub path: Vec<usize>,
    pub found: &'v mut dyn FnMut(&[usize], &Binding),
}

/// `supply` over one list of facts, leaving out those `used` marks.
///
/// A fact taken by one hypothesis is marked for the hypotheses after it and
/// unmarked when the search backs out, so the facts are never copied: the
/// search is most of what a check costs, and copying the list at every step
/// of it was a large part of the search.
///
/// Given `ways`, it does not stop at the first way that works: each is
/// handed to `ways.found` with the facts it took, and the search goes on, so
/// it gives back None having tried everything.
#[allow(clippy::too_many_arguments)]
pub fn search(
    patterns: &[Node],
    facts: &[Node],
    used: &mut Vec<bool>,
    binding: &Binding,
    variables: &BTreeSet<String>,
    library: &Library,
    sites: &Sites,
    reuse: bool,
    mut ways: Option<&mut Ways>,
) -> Option<Binding> {
    let Some((first, rest)) = patterns.split_first() else {
        if let Some(ways) = ways {
            (ways.found)(&ways.path, binding);
            return None;
        }
        return Some(binding.clone());
    };
    let ctx = &library.ctx;
    let mut first = first.clone();
    // A property already bound stands for a formula, so what it asks of the
    // facts is that formula rather than the application. Filling it in first
    // is what lets the rules below see it: `P(a)` may turn out to be a
    // "there is", and then a fact giving an instance of it supplies it.
    let mut open_names: Cow<BTreeSet<String>> = Cow::Borrowed(variables);
    if ctx.props.contains_key(&first.notation)
        && first.children.len() == 2
        && first.children[0].is_name()
    {
        if let Some(stands) = binding.get(&first.children[0].text) {
            if stands.notation == PROPERTY {
                // The argument is read through the binding whole: P(k + 1)
                // with k bound to o asks the property of o + 1.
                let terms: Binding = binding
                    .iter()
                    .filter(|(_, t)| t.notation != PROPERTY)
                    .map(|(v, t)| (v.clone(), t.clone()))
                    .collect();
                let arg = substitute_apart(&first.children[1], &terms, ctx);
                let mut at = Binding::new();
                at.insert(stands.text.clone(), arg.clone());
                first = substitute_apart(&stands.children[0], &at, ctx);
                // The formula a property stands for is the step's own, so a
                // name in it is the step's, even spelt as one of the item's.
                // Only a letter of the argument still to be matched is the
                // item's to fill.
                let unbound: BTreeSet<String> = arg
                    .names()
                    .iter()
                    .map(|n| n.to_string())
                    .filter(|n| variables.contains(n) && !binding.contains_key(n))
                    .collect();
                open_names = Cow::Owned(unbound);
            }
        }
    }
    // An equation, or the denial of one, is searched for each way round
    // (`either_way`): which way the hypothesis is read is decided by the
    // hypotheses after it as much as by the fact it is matched with.
    for first in either_way(&first, library) {
        let mut body_form: Option<(Node, BTreeSet<String>)> = None;
        if library.exists.contains(&first.notation) && first.children.len() > 2 {
            // A "there is" pattern holds its body last and names its variables
            // before it, one name and one domain at a time, so the two-variable
            // form is read the same way as the one-variable form.
            let body = first.children[first.children.len() - 1].clone();
            let mut seen = open_names.as_ref().clone();
            for c in &first.children[..first.children.len() - 1] {
                if c.is_name() {
                    seen.insert(c.text.clone());
                }
            }
            body_form = Some((body, seen));
        }
        let forms = std::iter::once((&first, open_names.as_ref()))
            .chain(body_form.iter().map(|(n, s)| (n, s)));
        // Whether every variable of the hypothesis is already bound, which is
        // the same for every fact tried here, so asked at most once.
        let mut pinned: Option<bool> = None;
        for i in 0..facts.len() {
            if used[i] {
                continue;
            }
            let fact = &facts[i];
            for (which, (form, seen)) in forms.clone().enumerate() {
                let is_first = which == 0;
                let mut found = match_tree(form, fact, binding, seen, sites, ctx);
                if found.is_none()
                    && is_first
                    && library.exists.contains(&first.notation)
                    && first.children.len() == 2
                    && library.members.contains(&fact.notation)
                    && fact.children.len() == 2
                {
                    found = match_tree(
                        &first.children[1],
                        &fact.children[1],
                        binding,
                        variables,
                        sites,
                        ctx,
                    );
                }
                // A "for all" said of a set is said of every set inside it
                // (`SYNTAX.md`).
                if found.is_none() && is_first {
                    if let Some(smaller) = narrowed(&first, fact, binding, ctx) {
                        found = match_tree(form, &smaller, binding, seen, sites, ctx);
                    }
                }
                let Some(found) = found else { continue };
                // A "there is" given by an instance is given only where the
                // instance is in the domain: the step's requires lines are where
                // `SYNTAX.md` has a witness named. Matching the body alone took
                // any value at all.
                if !is_first {
                    let remaining: Vec<Node> = facts
                        .iter()
                        .zip(used.iter())
                        .filter(|(_, u)| !**u)
                        .map(|(f, _)| f.clone())
                        .collect();
                    if !witnessed_in(&first, &found, &remaining, seen, library, sites) {
                        continue;
                    }
                }
                // A fact is used once when nothing has pinned the binding yet, or
                // a variable free in two hypotheses binds to whatever made the
                // first of them match and the second is then satisfied by the
                // same line. Where the claim has already pinned it, one line may
                // legitimately answer two requirements. A hypothesis whose every
                // variable the binding already fixed is a closed claim, and what
                // goes wrong above cannot: nothing is left for the line to bind.
                let pinned = *pinned
                    .get_or_insert_with(|| all_bound(&first, variables, binding));
                let takes = !(reuse || pinned);
                if takes {
                    used[i] = true;
                }
                // A fact that supplies a hypothesis is one the way uses, taken
                // for the hypotheses after it or not.
                if let Some(ways) = ways.as_deref_mut() {
                    ways.path.push(i);
                }
                let done = search(
                    rest,
                    facts,
                    used,
                    &found,
                    variables,
                    library,
                    sites,
                    reuse,
                    ways.as_deref_mut(),
                );
                if let Some(ways) = ways.as_deref_mut() {
                    ways.path.pop();
                }
                if takes {
                    used[i] = false;
                }
                if done.is_some() {
                    return done;
                }
            }
        }
    }
    None
}

/// Every one of the variables the tree names is bound already.
fn all_bound(tree: &Node, variables: &BTreeSet<String>, binding: &Binding) -> bool {
    if tree.is_name()
        && variables.contains(&tree.text)
        && !binding.contains_key(&tree.text)
    {
        return false;
    }
    tree.children
        .iter()
        .all(|c| all_bound(c, variables, binding))
}

/// Whether the declared table puts the set `inner` inside `outer`.
///
/// Both are parsed sets: a number system, or a range {a, …, b}.
/// `rules::WITHIN` and `rules::RANGE_WITHIN` are the table, which the
/// elaborator reads as well.
fn set_within(inner: &Node, outer: &Node) -> bool {
    if outer.notation != "number-systems" {
        return false;
    }
    let big = rules::system_of(&outer.text);
    if inner.notation == "number-systems" {
        return rules::within_path(rules::system_of(&inner.text), big).is_some();
    }
    if inner.notation == "integer-range" && inner.children.len() == 2 {
        let start = &inner.children[0];
        let begins = if start.notation == "numeral" {
            start
                .text
                .parse::<u32>()
                .ok()
                .and_then(rules::numeral_label)
        } else {
            None
        };
        return rules::RANGE_WITHIN.iter().any(|(system, first, _)| {
            (first.is_none() || *first == begins)
                && rules::within_path(Some(system), big).is_some()
        });
    }
    false
}

/// A "for all" fact read over the smaller domain a pattern asks for, or
/// None where the table does not put that domain inside the fact's.
fn narrowed(
    pattern: &Node,
    fact: &Node,
    binding: &Binding,
    ctx: &Context,
) -> Option<Node> {
    if pattern.notation != "for-all"
        || fact.notation != "for-all"
        || pattern.children.len() != 3
        || fact.children.len() != 3
    {
        return None;
    }
    // The domain is read only once the match has fixed every letter in it:
    // {a, …, b} says nothing until a is known to be 1.
    if pattern.children[1]
        .names()
        .iter()
        .any(|n| !binding.contains_key(n))
    {
        return None;
    }
    let terms: Binding = binding
        .iter()
        .filter(|(_, t)| t.notation != PROPERTY)
        .map(|(v, t)| (v.clone(), t.clone()))
        .collect();
    let asked = substitute_apart(&pattern.children[1], &terms, ctx);
    if !set_within(&asked, &fact.children[1]) {
        return None;
    }
    Some(Node::new(
        &fact.notation,
        fact.sort.clone(),
        vec![fact.children[0].clone(), asked, fact.children[2].clone()],
        &fact.text,
    ))
}

/// Whether one of the facts puts each value a "there is" was given in the
/// domain it ranges over.
///
/// The pattern names its variables before its body, one name and one domain
/// at a time.
fn witnessed_in(
    exists: &Node,
    binding: &Binding,
    facts: &[Node],
    variables: &BTreeSet<String>,
    library: &Library,
    sites: &Sites,
) -> bool {
    let pairs = &exists.children[..exists.children.len() - 1];
    for pair in pairs.chunks(2) {
        let [name, domain] = pair else { continue };
        if !name.is_name() {
            continue;
        }
        let Some(value) = binding.get(&name.text) else {
            return false;
        };
        let witnessed = facts.iter().any(|f| {
            library.members.contains(&f.notation)
                && f.children.len() == 2
                && f.children[0].shape() == value.shape()
                && match_tree(
                    domain,
                    &f.children[1],
                    binding,
                    variables,
                    sites,
                    &library.ctx,
                )
                .is_some()
        });
        if !witnessed {
            return false;
        }
    }
    true
}
