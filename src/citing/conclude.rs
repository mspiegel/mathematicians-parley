//! Whether a citation's claim is what the item it cites concludes.

use std::collections::BTreeSet;

use crate::formula::{walk, Node};
use indexmap::IndexMap;

use crate::matching::{
    alike, binding_sites, free_names, match_tree, substitute_apart, Binding, PROPERTY,
};
use crate::outcome::{Built, Route};

use super::library::{conjuncts, either_way, readings, Group, Library};
use super::supply::{names_of, search, supply, Sites, Ways};

/// Every sentence of the claim takes a reading of the conclusion, and what
/// those readings ask for is then supplied by the facts: the binding they
/// were supplied under, or None where no reading is.
///
/// It backtracks, because a sentence can fit a reading whose requirement
/// the step does not meet while another reading's it does.
///
/// Given `ways`, it does not stop at the first way that works: every way of
/// supplying what a reading asks first is followed, as well as the first,
/// and each complete way is handed to `ways.found` with the facts it took,
/// those taken first included; it gives back None having tried everything.
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
    mut ways: Option<&mut Ways>,
) -> Option<Binding> {
    let Some((claim, later)) = claims.split_first() else {
        let mut all = need.to_vec();
        all.extend(used.iter().cloned());
        let mut marks = vec![false; given.len()];
        return search(
            &all, given, &mut marks, binding, variables, library, sites, true, ways,
        );
    };
    for (cand, first) in candidates {
        // What a property stands for is decided inside the braces, so a
        // requirement holding them is matched before the claim that uses it.
        let starts: Vec<Start> = if walk(first).iter().any(|x| sites.contains(&x.id()))
        {
            supplied_first(first, given, binding, variables, library, sites, &ways)
        } else {
            vec![Start {
                path: Vec::new(),
                binding: binding.clone(),
            }]
        };
        for start in starts {
            let Some(found) =
                match_tree(cand, claim, &start.binding, variables, sites, &library.ctx)
            else {
                continue;
            };
            let seen: BTreeSet<&str> = used.iter().map(|u| u.shape()).collect();
            let mut more = used.to_vec();
            more.extend(first.iter().filter(|f| !seen.contains(f.shape())).cloned());
            let at = ways.as_deref().map_or(0, |w| w.path.len());
            if let Some(w) = ways.as_deref_mut() {
                w.path.extend(&start.path);
            }
            let done = take(
                later,
                candidates,
                &found,
                &more,
                need,
                given,
                variables,
                library,
                sites,
                ways.as_deref_mut(),
            );
            if let Some(w) = ways.as_deref_mut() {
                w.path.truncate(at);
            }
            if done.is_some() {
                return done;
            }
        }
    }
    None
}

/// A binding to match a claim under: one way of supplying what a reading
/// asks first, and the facts that way took.
struct Start {
    path: Vec<usize>,
    binding: Binding,
}

/// The ways the facts supply what a reading asks first: the first way
/// alone, or, where `ways` asks for every way, each of them.
#[allow(clippy::too_many_arguments)]
fn supplied_first(
    first: &[Node],
    given: &[Node],
    binding: &Binding,
    variables: &BTreeSet<String>,
    library: &Library,
    sites: &Sites,
    ways: &Option<&mut Ways>,
) -> Vec<Start> {
    if ways.is_none() {
        return supply(first, given, binding, variables, library, sites, false)
            .map(|binding| Start {
                path: Vec::new(),
                binding,
            })
            .into_iter()
            .collect();
    }
    let mut starts: Vec<Start> = Vec::new();
    let mut record = |path: &[usize], binding: &Binding| {
        starts.push(Start {
            path: path.to_vec(),
            binding: binding.clone(),
        });
    };
    let mut every = Ways {
        path: Vec::new(),
        found: &mut record,
    };
    let mut marks = vec![false; given.len()];
    let _ = search(
        first,
        given,
        &mut marks,
        binding,
        variables,
        library,
        sites,
        false,
        Some(&mut every),
    );
    starts
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
    for (group, of) in groups.iter().enumerate() {
        let offer = Offer::of(of, library);
        if let Some(binding) = take(
            &claims,
            &offer.candidates,
            seed,
            &[],
            &offer.need,
            facts,
            &offer.variables,
            library,
            &offer.sites,
            None,
        ) {
            return Built(Taken::of(group, binding, &groups[group], library));
        }
    }
    Route::no("no group of the item concludes the claim from the facts named")
}

/// Every way the facts let a group of the item conclude the claim, as the
/// facts each way takes, by index, handed to `found`.
///
/// This is `taken` searched to the end rather than to the first way, over
/// every group: each reading the claim may take, each way the facts supply
/// what that reading asks first, and each way they supply the rest.
pub fn taken_ways(
    groups: &[Group],
    claims: &[Node],
    facts: &[Node],
    seed: &Binding,
    library: &Library,
    found: &mut dyn FnMut(&[usize]),
) {
    let claims: Vec<Node> = claims.iter().flat_map(|c| conjuncts(c, library)).collect();
    let mut record = |path: &[usize], _: &Binding| found(path);
    for of in groups {
        let offer = Offer::of(of, library);
        let mut ways = Ways {
            path: Vec::new(),
            found: &mut record,
        };
        let _ = take(
            &claims,
            &offer.candidates,
            seed,
            &[],
            &offer.need,
            facts,
            &offer.variables,
            library,
            &offer.sites,
            Some(&mut ways),
        );
    }
}

/// What one group of an item offers a claim, read once for every way of
/// taking it.
struct Offer {
    /// Each conjunct of each reading of a conclusion, either way round, with
    /// what that reading asks first.
    candidates: Vec<(Node, Vec<Node>)>,
    /// The group's hypotheses, conjunct by conjunct.
    need: Vec<Node>,
    /// The item's letters, which the claim and the facts bind.
    variables: BTreeSet<String>,
    /// Where a property or function the item binds is applied.
    sites: Sites,
}

impl Offer {
    fn of(group: &Group, library: &Library) -> Offer {
        let Group { wants: want, gives } = group;
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
        Offer {
            candidates,
            need,
            variables,
            sites,
        }
    }
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
