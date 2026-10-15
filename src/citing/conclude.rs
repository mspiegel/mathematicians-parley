//! Whether a citation's claim is what the item it cites concludes.

use std::collections::BTreeSet;

use crate::formula::page::conjoined;
use crate::formula::{walk, Node};
use indexmap::IndexMap;

use crate::matching::{
    alike, binding_sites, free_names, identities_dropped, match_tree, put_everywhere,
    substitute_apart, Binding, PROPERTY,
};
use crate::outcome::{Built, Route};

use super::asked::filled;
use super::library::{conjuncts, either_way, readings, Group, Library, Way};
use super::once::{a_number_said_once, Introduced};
use super::supply::{names_of, search, supplier, supply, Sites, Ways};
use crate::rules;

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
///
/// `chosen` holds, sentence by sentence, the candidate each sentence of the
/// claim took, for the way it gives back.
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
    chosen: &mut Vec<usize>,
) -> Option<Binding> {
    let Some((claim, later)) = claims.split_first() else {
        let mut all = need.to_vec();
        all.extend(used.iter().cloned());
        let mut marks = vec![false; given.len()];
        return search(
            &all, given, &mut marks, binding, variables, library, sites, true, ways,
        );
    };
    for (taking, (cand, first)) in candidates.iter().enumerate() {
        // What a property stands for is decided inside the braces, so a
        // requirement holding them is matched before the claim that uses it.
        let starts: Vec<Start> = if walk(first).iter().any(|x| sites.contains(&x.id()))
        {
            supplied_first(first, given, binding, variables, library, sites)
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
            if !identities_on_numbers(cand, claim, &found, given, library) {
                continue;
            }
            let seen: BTreeSet<&str> = used.iter().map(|u| u.shape()).collect();
            let mut more = used.to_vec();
            more.extend(first.iter().filter(|f| !seen.contains(f.shape())).cloned());
            let at = ways.as_deref().map_or(0, |w| w.path.len());
            if let Some(w) = ways.as_deref_mut() {
                w.path.extend(&start.path);
            }
            chosen.push(taking);
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
                chosen,
            );
            if let Some(w) = ways.as_deref_mut() {
                w.path.truncate(at);
            }
            if done.is_some() {
                return done;
            }
            chosen.pop();
        }
    }
    None
}

/// Whether every identity element the match of `cand` against `claim`
/// dropped leaves a number by what the facts say, a membership the page
/// says once among them (`said_once`): an identity law holds of a number,
/// and that is a `requires` line where the page does not say it once
/// (`SYNTAX.md`, "An identity element goes without saying").
fn identities_on_numbers(
    cand: &Node,
    claim: &Node,
    binding: &Binding,
    given: &[Node],
    library: &Library,
) -> bool {
    unnumbered(cand, claim, binding, given, library).is_empty()
}

/// What an identity element the match of `cand` against `claim` dropped
/// leaves, where the facts do not say it is a number.
fn unnumbered(
    cand: &Node,
    claim: &Node,
    binding: &Binding,
    given: &[Node],
    library: &Library,
) -> Vec<Node> {
    let ctx = &library.ctx;
    let instance = filled(cand, binding, ctx);
    let dropped = identities_dropped(&instance, claim, ctx);
    if dropped.is_empty() {
        return dropped;
    }
    // A letter the claim or the instance binds over a number system is said
    // to be in it by its binder, as a `let` says it; what is left is spelt
    // in the instance's letters where the two bind different ones.
    let mut bound = Introduced::new();
    for node in claim.walk().into_iter().chain(instance.walk()) {
        if let [name, set, _] = node.children.as_slice() {
            if library.exists.contains(&node.notation)
                && name.is_name()
                && set.notation == "number-systems"
            {
                if let Some(system) = rules::system_of(&set.text) {
                    bound.insert(name.text.clone(), system);
                }
            }
        }
    }
    dropped
        .into_iter()
        .filter(|left| {
            !a_number_said_once(left, given, &bound, ctx)
                && !given.iter().any(|f| {
                    library.members.contains(&f.notation)
                        && matches!(f.children.as_slice(), [term, set]
                            if set.notation == "number-systems"
                                && alike(term, left, ctx, &IndexMap::new(), &IndexMap::new()))
                })
        })
        .collect()
}

/// What a `substitute` leaves unsaid to be a number: where `aim` is reached
/// from one of `starts` only by putting the equation `left = right` in at
/// every place and dropping an identity element that makes (`matching::
/// substituted_in`), what each dropped element leaves and `facts` do not
/// say is a number (`SYNTAX.md`, "An identity element goes without saying":
/// a substitute and the line it makes). Empty where the claim is reached
/// with nothing dropped, or not reached at all, which the step's own check
/// reports.
pub fn substitution_unsaid(
    starts: &[Node],
    aim: &Node,
    left: &Node,
    right: &Node,
    facts: &[Node],
    library: &Library,
) -> Vec<Node> {
    let ctx = &library.ctx;
    // What dropping an element leaves is asked first, wherever in the term
    // the element stands: C(m, k)·1·1^k is C(m, k)·1^k only where C(m, k)
    // is a number, and a fit at some places would pass over that.
    for start in starts {
        for (was, now) in [(left, right), (right, left)] {
            let made = put_everywhere(start, was, now, ctx);
            if alike(&made, aim, ctx, &IndexMap::new(), &IndexMap::new()) {
                let left_over = unnumbered(&made, aim, &Binding::new(), facts, library);
                if !left_over.is_empty() {
                    return left_over;
                }
            }
        }
    }
    Vec::new()
}

/// What a calculation link leaves unsaid to be a number, where it is what
/// one of `says`, the sentences of the line it cites, says only once an
/// identity element is dropped: each dropped element's leftover that
/// `facts` do not say is a number. A link has no requires line, so a drop
/// from what the page does not say once is a step of its own (`SYNTAX.md`,
/// "An identity element goes without saying"). Empty where a sentence is
/// the link as written, or none is the link at all.
pub fn link_unsaid(
    link: &Node,
    says: &[Node],
    facts: &[Node],
    library: &Library,
) -> Vec<Node> {
    let ctx = &library.ctx;
    let none = IndexMap::new();
    if says.iter().any(|s| {
        identities_dropped(s, link, ctx).is_empty() && alike(s, link, ctx, &none, &none)
    }) {
        return Vec::new();
    }
    for said in says {
        if alike(said, link, ctx, &none, &none) {
            return unnumbered(said, link, &Binding::new(), facts, library);
        }
    }
    Vec::new()
}

/// What a claim the item concludes once its identity elements are dropped
/// leaves unsaid to be a number, where that is why no group takes it: each
/// claim matched against each conclusion the groups offer under the seed,
/// and what the first match that drops an element leaves and the facts do
/// not say is a number. Empty where no match drops one.
pub fn identities_unsaid(
    groups: &[Group],
    claims: &[Node],
    facts: &[Node],
    seed: &Binding,
    library: &Library,
) -> Vec<Node> {
    let (whole, split) = (whole_claim(claims, library), split_claims(claims, library));
    for of in groups {
        let offer = Offer::of(of, library);
        for claim in offer.claims_read(&whole, &split) {
            for (cand, _) in &offer.candidates {
                let Some(found) = match_tree(
                    cand,
                    claim,
                    seed,
                    &offer.variables,
                    &offer.sites,
                    &library.ctx,
                ) else {
                    continue;
                };
                let left = unnumbered(cand, claim, &found, facts, library);
                if !left.is_empty() {
                    return left;
                }
            }
        }
    }
    Vec::new()
}

/// A binding to match a claim under: one way of supplying what a reading
/// asks first, and the facts that way took.
struct Start {
    path: Vec<usize>,
    binding: Binding,
}

/// Every way the facts supply what a reading asks first.
fn supplied_first(
    first: &[Node],
    given: &[Node],
    binding: &Binding,
    variables: &BTreeSet<String>,
    library: &Library,
    sites: &Sites,
) -> Vec<Start> {
    // Every way, not the first: a line of two sentences supplies the
    // braces from either, and the claim decides which (`set-image` from
    // t ∈ {2n : n ∈ ℤ}. t ∈ {3n : n ∈ ℤ}. claiming t = 3n).
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
    /// The conclusion of the group each sentence of the claim takes, in the
    /// claim's order; none for an obtain, which takes the group's "there
    /// is" whole.
    pub concluded: Vec<Concluded>,
    /// What the readings taken ask a fact to state first, in the item's
    /// letters (`readings`); the facts that state it are `first_facts`.
    pub asks_first: Vec<Node>,
}

/// One conclusion of an item a sentence of a claim takes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Concluded {
    /// The conclusion, by its place among its group's sentences.
    pub sentence: usize,
    /// Which way it is read (`readings`).
    pub way: Way,
}

impl Taken {
    fn of(
        group: usize,
        mut binding: Binding,
        concluded: Vec<Concluded>,
        of: &Group,
        library: &Library,
    ) -> Taken {
        let mut free = BTreeSet::new();
        for t in of.gives.iter().chain(of.wants.iter().map(|(_, t)| t)) {
            free.extend(free_names(t, &library.ctx.binders));
        }
        binding.retain(|name, _| free.contains(name));
        Taken {
            group,
            binding,
            concluded,
            asks_first: Vec::new(),
        }
    }

    /// The facts that state what the readings taken ask first, as `facts`
    /// read them (`supplier`): the side a definition is unfolded from.
    /// Looked up only when asked, since a search takes far more readings
    /// than a record keeps.
    pub fn first_facts(
        &self,
        groups: &[Group],
        facts: &[Node],
        library: &Library,
    ) -> Vec<Node> {
        let Some(group) = groups.get(self.group) else {
            return Vec::new();
        };
        let mut trees = group.gives.clone();
        trees.extend(group.wants.iter().map(|(_, t)| t.clone()));
        let variables = names_of(&trees);
        let mut sites = Sites::new();
        for t in &trees {
            binding_sites(t, &library.ctx, &[], &mut sites);
        }
        first_facts(
            &self.asks_first,
            facts,
            &self.binding,
            &variables,
            library,
            &sites,
        )
    }
}

/// The fact that states each of `firsts` under the binding the search
/// found, where one does (`supplier`).
fn first_facts(
    firsts: &[Node],
    facts: &[Node],
    binding: &Binding,
    variables: &BTreeSet<String>,
    library: &Library,
    sites: &Sites,
) -> Vec<Node> {
    let none = IndexMap::new();
    let mut out: Vec<Node> = Vec::new();
    for first in firsts {
        if let Some(fact) = supplier(first, facts, binding, variables, library, sites) {
            if !out
                .iter()
                .any(|f| alike(f, fact, &library.ctx, &none, &none))
            {
                out.push(fact.clone());
            }
        }
    }
    out
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
    let (whole, split) = (whole_claim(claims, library), split_claims(claims, library));
    for (group, of) in groups.iter().enumerate() {
        let offer = Offer::of(of, library);
        let mut chosen = Vec::new();
        if let Some(binding) = take(
            offer.claims_read(&whole, &split),
            &offer.candidates,
            seed,
            &[],
            &offer.need,
            facts,
            &offer.variables,
            library,
            &offer.sites,
            None,
            &mut chosen,
        ) {
            let concluded = chosen
                .iter()
                .map(|&c| Concluded {
                    sentence: offer.from[c],
                    way: offer.ways[c],
                })
                .collect();
            let mut taken =
                Taken::of(group, binding, concluded, &groups[group], library);
            taken.asks_first = chosen
                .iter()
                .flat_map(|&c| offer.candidates[c].1.iter().cloned())
                .collect();
            return Built(taken);
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
    let (whole, split) = (whole_claim(claims, library), split_claims(claims, library));
    let mut record = |path: &[usize], _: &Binding| found(path);
    for of in groups {
        let offer = Offer::of(of, library);
        let mut ways = Ways {
            path: Vec::new(),
            found: &mut record,
        };
        let _ = take(
            offer.claims_read(&whole, &split),
            &offer.candidates,
            seed,
            &[],
            &offer.need,
            facts,
            &offer.variables,
            library,
            &offer.sites,
            Some(&mut ways),
            &mut Vec::new(),
        );
    }
}

/// A claim conjunct by conjunct, as a conclusion is offered: `u ∈ Y and
/// u ∈ Z` is the two facts a reading gives.
fn split_claims(claims: &[Node], library: &Library) -> Vec<Node> {
    claims.iter().flat_map(|c| conjuncts(c, library)).collect()
}

/// A claim of several sentences as the one formula they make, their
/// conjunction (`SYNTAX.md`): what a statement letter stands for.
fn whole_claim(claims: &[Node], library: &Library) -> Vec<Node> {
    match claims {
        [_, _, ..] => conjoined(library.env.g, claims.to_vec())
            .into_iter()
            .collect(),
        _ => claims.to_vec(),
    }
}

impl Offer {
    /// The claims as this group reads them: conjunct by conjunct, as its
    /// conclusion is offered, except where the group concludes one statement
    /// letter, which stands for the claim whole however many conjuncts it
    /// has: iff-from-left's Q at Q := 0 ≤ x and x < 1.
    fn claims_read<'c>(&self, whole: &'c [Node], split: &'c [Node]) -> &'c [Node] {
        if self.letter {
            whole
        } else {
            split
        }
    }
}

/// What one group of an item offers a claim, read once for every way of
/// taking it.
struct Offer {
    /// Whether the group concludes one statement letter and nothing else.
    letter: bool,
    /// Each conjunct of each reading of a conclusion, either way round, with
    /// what that reading asks first.
    candidates: Vec<(Node, Vec<Node>)>,
    /// The conclusion each candidate is read from, by its place among the
    /// group's sentences.
    from: Vec<usize>,
    /// Which way that conclusion is read for each candidate.
    ways: Vec<Way>,
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
        let mut from = Vec::new();
        let mut ways = Vec::new();
        let mut sites = Sites::new();
        for (sentence, concl) in gives.iter().enumerate() {
            binding_sites(concl, &library.ctx, &[], &mut sites);
            for reading in readings(concl, library) {
                let first: Vec<Node> = reading
                    .first
                    .iter()
                    .flat_map(|e| conjuncts(e, library))
                    .collect();
                for c in conjuncts(&reading.claimed, library) {
                    for turned in either_way(&c, library) {
                        candidates.push((turned, first.clone()));
                        from.push(sentence);
                        ways.push(reading.way);
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
        // A conclusion is a sentence, so one that is a bare letter of the
        // item's is a statement letter.
        let letter = matches!(gives.as_slice(), [one]
            if one.is_name() && variables.contains(&one.text));
        Offer {
            letter,
            candidates,
            from,
            ways,
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
            for reading in readings(concl, library) {
                let target = reading.claimed;
                // The "there is" is the reading's target or a part of it, and
                // may be a property the definition applies, which the line
                // the step cites decides.
                let first: Vec<Node> = reading
                    .first
                    .iter()
                    .flat_map(|e| conjuncts(e, library))
                    .collect();
                let mut need = first.clone();
                need.extend(asked.iter().cloned());
                let variables = names_of(&need);
                let found =
                    supply(&need, facts, seed, &variables, library, &sites, false);
                if let Some(binding) = found {
                    if conjuncts(&target, library)
                        .iter()
                        .any(|part| existential(part, &binding, library))
                    {
                        let mut taken = Taken::of(
                            group,
                            binding,
                            Vec::new(),
                            &groups[group],
                            library,
                        );
                        taken.asks_first = first;
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
