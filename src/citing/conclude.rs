//! Whether a citation's claim is what the item it cites concludes.

use std::collections::BTreeSet;

use crate::formula::{walk, Node};
use indexmap::IndexMap;

use crate::matching::{
    alike, binding_sites, free_names, match_tree, substitute_apart, Binding, PROPERTY,
};
use crate::outcome::{Built, Route};

use super::library::{conjuncts, either_way, readings, Group, Library};
use super::supply::{names_of, supply, Sites};

/// Every sentence of the claim takes a reading of the conclusion, and what
/// those readings ask for is then supplied by the facts: the binding they
/// were supplied under, or None where no reading is.
///
/// It backtracks, because a sentence can fit a reading whose requirement
/// the step does not meet while another reading's it does.
#[allow(clippy::too_many_arguments)]
fn take(
    claims: &[Node],
    candidates: &[(Node, Vec<Node>)],
    binding: &Binding,
    used: &[Node],
    need: &[Node],
    given: &[Node],
    variables: &BTreeSet<String>,
    library: &Library,
    sites: &Sites,
) -> Option<Binding> {
    let Some((claim, later)) = claims.split_first() else {
        let mut all = need.to_vec();
        all.extend(used.iter().cloned());
        return supply(&all, given, binding, variables, library, sites, true);
    };
    for (cand, first) in candidates {
        // What a property stands for is decided inside the braces, so a
        // requirement holding them is matched before the claim that uses it.
        let mut start = binding.clone();
        if walk(first).iter().any(|x| sites.contains(&x.id())) {
            match supply(first, given, binding, variables, library, sites, false) {
                Some(s) => start = s,
                None => continue,
            }
        }
        let Some(found) =
            match_tree(cand, claim, &start, variables, sites, &library.ctx)
        else {
            continue;
        };
        let seen: BTreeSet<&str> = used.iter().map(|u| u.shape()).collect();
        let mut more = used.to_vec();
        more.extend(first.iter().filter(|f| !seen.contains(f.shape())).cloned());
        let done = take(
            later, candidates, &found, &more, need, given, variables, library, sites,
        );
        if done.is_some() {
            return done;
        }
    }
    None
}

/// The group of an item a citation takes, by its place among the item's
/// groups, and what the item's letters stand for there.
pub struct Taken {
    pub group: usize,
    /// Only the letters free in the group's statement. The search also binds
    /// a letter a "there is" or a "for all" of the item binds itself, to the
    /// value that gave it, and that letter stands for nothing at the
    /// citation: the s of `there is s ∈ S` is still the conclusion's own s.
    pub binding: Binding,
}

impl Taken {
    fn of(group: usize, mut binding: Binding, of: &Group, library: &Library) -> Taken {
        let mut free = BTreeSet::new();
        for t in of.gives.iter().chain(of.wants.iter().map(|(_, t)| t)) {
            free.extend(free_names(t, &library.ctx.binders));
        }
        binding.retain(|name, _| free.contains(name));
        Taken { group, binding }
    }
}

/// Whether one group of an item's conclusions covers what is claimed.
pub fn concludes(
    groups: &[Group],
    claims: &[Node],
    facts: &[Node],
    seed: &Binding,
    library: &Library,
) -> bool {
    !taken(groups, claims, facts, seed, library).is_declined()
}

/// The first group of an item's conclusions that covers what is claimed,
/// with the binding the claim and the facts fix; declined where no group
/// does.
pub fn taken(
    groups: &[Group],
    claims: &[Node],
    facts: &[Node],
    seed: &Binding,
    library: &Library,
) -> Route<Taken> {
    // A conclusion is offered conjunct by conjunct, so a claim is asked for
    // the same way: `u ∈ Y and u ∈ Z` is the two facts a reading gives.
    let claims: Vec<Node> = claims.iter().flat_map(|c| conjuncts(c, library)).collect();
    for (group, Group { wants: want, gives }) in groups.iter().enumerate() {
        let mut candidates: Vec<(Node, Vec<Node>)> = Vec::new();
        let mut sites = Sites::new();
        for concl in gives {
            binding_sites(concl, &library.ctx, &[], &mut sites);
            for (target, extra) in readings(concl, library) {
                let first: Vec<Node> =
                    extra.iter().flat_map(|e| conjuncts(e, library)).collect();
                for c in conjuncts(&target, library) {
                    for way in either_way(&c, library) {
                        candidates.push((way, first.clone()));
                    }
                }
            }
        }
        let need: Vec<Node> = want
            .iter()
            .flat_map(|(_, t)| conjuncts(t, library))
            .collect();
        for (_, t) in want {
            binding_sites(t, &library.ctx, &[], &mut sites);
        }
        let mut trees = gives.clone();
        trees.extend(want.iter().map(|(_, t)| t.clone()));
        let variables = names_of(&trees);
        if let Some(binding) = take(
            &claims,
            &candidates,
            seed,
            &[],
            &need,
            facts,
            &variables,
            library,
            &sites,
        ) {
            return Built(Taken::of(group, binding, &groups[group], library));
        }
    }
    Route::no("no group of the item concludes the claim from the facts named")
}

/// Whether the item gives a "there is" from what the step names.
///
/// An obtain claims the body of what the item says there is, which
/// `concludes` does not read. What it does read is the way to the
/// existential: an item that gives one only from a line saying n is odd
/// needs that line as surely as it needs any other.
pub fn obtains(
    groups: &[Group],
    facts: &[Node],
    seed: &Binding,
    library: &Library,
) -> bool {
    !obtained(groups, facts, seed, library).is_declined()
}

/// The first group of an item that gives a "there is" from the facts, with
/// the binding the facts fix; declined where none does.
///
/// The facts supply the group's hypotheses as well as what the reading asks
/// first, so that every letter the item says the "there is" of is bound: the
/// x of `x(n) → L as n → ∞` is fixed by that hypothesis alone.
pub fn obtained(
    groups: &[Group],
    facts: &[Node],
    seed: &Binding,
    library: &Library,
) -> Route<Taken> {
    for (group, Group { wants, gives }) in groups.iter().enumerate() {
        let asked: Vec<Node> = wants
            .iter()
            .flat_map(|(_, t)| conjuncts(t, library))
            .collect();
        for concl in gives {
            let mut sites = Sites::new();
            binding_sites(concl, &library.ctx, &[], &mut sites);
            for t in &asked {
                binding_sites(t, &library.ctx, &[], &mut sites);
            }
            for (target, extra) in readings(concl, library) {
                // The "there is" is the reading's target or a part of it, and
                // may be a property the definition applies, which the line
                // the step cites decides.
                let mut need: Vec<Node> =
                    extra.iter().flat_map(|e| conjuncts(e, library)).collect();
                need.extend(asked.iter().cloned());
                let variables = names_of(&need);
                let found =
                    supply(&need, facts, seed, &variables, library, &sites, false);
                if let Some(binding) = found {
                    if conjuncts(&target, library)
                        .iter()
                        .any(|part| existential(part, &binding, library))
                    {
                        let taken = Taken::of(group, binding, &groups[group], library);
                        return Built(taken);
                    }
                }
            }
        }
    }
    Route::no("no group of the item gives a \"there is\" from the facts named")
}

/// Whether one part of what a definition says is a "there is", with a
/// property it applies read as what the binding says the property is.
fn existential(part: &Node, binding: &Binding, library: &Library) -> bool {
    let mut part = part.clone();
    if library.ctx.props.contains_key(&part.notation)
        && part.children.len() == 2
        && part.children[0].is_name()
    {
        let Some(stands) = binding.get(&part.children[0].text) else {
            return false;
        };
        if stands.notation != PROPERTY {
            return false;
        }
        let terms: Binding = binding
            .iter()
            .filter(|(_, v)| v.notation != PROPERTY)
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let arg = substitute_apart(&part.children[1], &terms, &library.ctx);
        let mut at = Binding::new();
        at.insert(stands.text.clone(), arg);
        part = substitute_apart(&stands.children[0], &at, &library.ctx);
    }
    library.exists.contains(&part.notation)
}

/// The fact follows from the cited item applied as often as it takes.
///
/// A closure line names a principle, not one use of it: `2k² + 2k ∈ ℤ`
/// cites the closure of the integers once where the kernel applies it three
/// times, and a reader wants the one line. So the item's own conclusions are
/// matched against the claim and against whatever they then ask for, and
/// nothing else is allowed in.
pub fn derives(
    claim: &Node,
    groups: &[Group],
    facts: &[Node],
    library: &Library,
    depth: i32,
) -> bool {
    if depth <= 0 {
        return false;
    }
    // A fact that is the claim, however either writes an equation or names
    // what it binds (`matching::alike`).
    let none = IndexMap::new();
    if facts
        .iter()
        .any(|f| alike(f, claim, &library.ctx, &none, &none))
    {
        return true;
    }
    for Group { wants: want, gives } in groups {
        let mut trees = gives.clone();
        trees.extend(want.iter().map(|(_, t)| t.clone()));
        let variables = names_of(&trees);
        for concl in gives {
            let Some(binding) = match_tree(
                concl,
                claim,
                &Binding::new(),
                &variables,
                &Sites::new(),
                &library.ctx,
            ) else {
                continue;
            };
            if want.iter().all(|(_, t)| {
                derives(
                    &substitute_apart(t, &binding, &library.ctx),
                    groups,
                    facts,
                    library,
                    depth - 1,
                )
            }) {
                return true;
            }
        }
    }
    false
}
