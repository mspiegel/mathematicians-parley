//! Whether a citation's claim is what the item it cites concludes.

use std::collections::BTreeSet;

use crate::formula::page::conjoined;
use crate::formula::{walk, ByShape, Node};
use indexmap::IndexMap;

use crate::matching::{
    alike, alike_top, binding_sites, identities_dropped, match_every_way, match_tree,
    property_said, put_everywhere, substitute_apart, Binding, Context, FxIndexSet,
};
use crate::notations::{PROPERTY_OF, THERE_IS};
use crate::outcome::{Built, Route};

use super::asked::filled;
use super::library::{conjuncts, either_way, readings, Group, Library, Way};
use super::once::{a_number_said_once, Introduced};
use super::parts::{bound_in, Bound};
use super::supply::{
    body_reading, search, supplier, supply, unwitnessed, Sites, Unwitnessed, Ways,
};
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
    free: &BTreeSet<String>,
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
        // requirement holding them is matched before the claim that uses it;
        // where the claim holds them itself, `t ∈ {2n : n ∈ ℤ}` for set-image,
        // the claim decides it, and the requirement is supplied after, a
        // "there is" from a line saying its body at a value as any is.
        let holds = |x: &[Node]| walk(x).iter().any(|y| sites.contains(&y.id()));
        let starts: Vec<Start> = if holds(first) && !holds(std::slice::from_ref(cand)) {
            supplied_first(first, given, binding, variables, library, sites)
        } else {
            vec![Start {
                path: Vec::new(),
                binding: binding.clone(),
            }]
        };
        // The claim is fitted every way it fits, so that the facts decide
        // which way it is the conclusion (`claim_matched`).
        let tries: Vec<(&Start, Binding)> = starts
            .iter()
            .flat_map(|s| {
                claim_matched(cand, claim, &s.binding, variables, sites, library)
                    .into_iter()
                    .map(move |found| (s, found))
            })
            .collect();
        for (start, found) in tries {
            if !identities_on_numbers(cand, claim, &found, given, library) {
                continue;
            }
            // A letter the item binds, the k of Σ(k = a to b), is matched
            // afresh in each hypothesis, which may say the same over another
            // letter (`ELABORATION.md`), as `Taken::of` keeps only the free.
            let mut found = found;
            found.retain(|name, _| free.contains(name.as_str()));
            let seen: FxIndexSet<ByShape> = used.iter().map(Node::by_shape).collect();
            let mut more = used.to_vec();
            more.extend(
                first
                    .iter()
                    .filter(|f| !seen.contains(&f.by_shape()))
                    .cloned(),
            );
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
                free,
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

/// Every binding under which one conjunct of the claim is the candidate, a
/// conjunct of the item's conclusion; none where it is not.
///
/// Every way and not the first, since the claim may fit more than one way
/// and the facts decide which: "S, R, T are collinear" fits "T, R, S" with
/// T := S as well as with T := T, and `{a, b} ⊆ S` fits `{v, w} ⊆ S` with
/// a := v and with a := w.
///
/// A candidate applying a property the binding already holds, `P(u)` with P
/// decided inside the braces, says the property's body, and where that body
/// is a conjunction the claim may take any conjunct of it, as it may of a
/// conclusion written out: `k ∈ T` from `u ∈ {S ⊆ X : k ∈ S and …}`.
fn claim_matched(
    cand: &Node,
    claim: &Node,
    binding: &Binding,
    variables: &BTreeSet<String>,
    sites: &Sites,
    library: &Library,
) -> Vec<Binding> {
    let ctx = &library.ctx;
    let found = match_every_way(cand, claim, binding, variables, sites, ctx);
    if !found.is_empty() {
        return found;
    }
    let Some(said) = property_said(cand, binding, variables, ctx) else {
        return Vec::new();
    };
    let parts = conjuncts(&said, library);
    if parts.len() < 2 {
        return Vec::new();
    }
    // The body is the citing page's, and its letters are the page's even
    // where one is spelt as a letter of the item: only the item's letters
    // the property is applied to are matched. The page's X in `X ∈ S`, with
    // the item's X bound to {1, …, X}, is the page's X.
    let applied_to: BTreeSet<String> = cand.children[1]
        .names()
        .into_iter()
        .filter(|n| variables.contains(n))
        .collect();
    parts
        .iter()
        .flat_map(|part| match_every_way(part, claim, binding, &applied_to, sites, ctx))
        .collect()
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
    not_numbers(dropped, &instance, claim, given, library)
}

/// Of what dropping identity elements left, `dropped`, those the facts do
/// not say are numbers, with the letters `instance` and `claim` bind.
pub fn not_numbers(
    dropped: Vec<Node>,
    instance: &Node,
    claim: &Node,
    given: &[Node],
    library: &Library,
) -> Vec<Node> {
    let ctx = &library.ctx;
    if dropped.is_empty() {
        return dropped;
    }
    // A letter the claim or the instance binds over a number system, for
    // all of it or for some, is said to be in it by its binder, as a `let`
    // says it; what is left is spelt in the instance's letters where the
    // two bind different ones.
    let mut bound = Introduced::new();
    for node in claim.walk().into_iter().chain(instance.walk()) {
        if let [name, set, _] = node.children.as_slice() {
            let binds = library.exists.contains(&node.notation())
                || library.every.contains(&node.notation());
            if binds
                && name.is_name()
                && set.notation() == crate::notations::NUMBER_SYSTEMS
            {
                if let Some(system) = rules::System::of_sign(&set.text) {
                    bound.insert(name.text.to_string(), system);
                }
            }
        }
    }
    dropped
        .into_iter()
        .filter(|left| {
            !a_number_said_once(left, given, &bound, ctx)
                && !given.iter().any(|f| {
                    library.members.contains(&f.notation())
                        && matches!(f.children.as_slice(), [term, set]
                            if set.notation() == crate::notations::NUMBER_SYSTEMS
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
                // A place the side stands at only once an identity element
                // is dropped, Σ + 0 for Σ, drops it there, before the putting.
                let at_sites = if dropped_at_sites(start, was, ctx) {
                    vec![now.clone()]
                } else {
                    Vec::new()
                };
                let left_over = not_numbers(at_sites, start, aim, facts, library);
                if !left_over.is_empty() {
                    return left_over;
                }
            }
        }
    }
    Vec::new()
}

/// Whether a place in `start` that `was` stands at, as `put_everywhere`
/// finds the places, is `was` only once an identity element is dropped:
/// what is put there is then what is left of the place.
fn dropped_at_sites(start: &Node, was: &Node, ctx: &Context) -> bool {
    let inside = |c: &Node| crate::matching::put_places(c, was, was, ctx).is_some();
    if start.children.iter().any(inside) {
        return start.children.iter().any(|c| dropped_at_sites(c, was, ctx));
    }
    alike_top(start, was, ctx) && !identities_dropped(start, was, ctx).is_empty()
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
    // A line saying the link as it stands, or the other way round, drops
    // nothing: `t + 0 = t` is `t = t + 0` read from its right.
    let as_it_stands = |s: &Node| {
        identities_dropped(s, link, ctx).is_empty() && alike(s, link, ctx, &none, &none)
    };
    if says
        .iter()
        .flat_map(|s| either_way(s, library))
        .any(|s| as_it_stands(&s))
    {
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
    each_match(groups, claims, seed, library, &mut |at| {
        unnumbered(at.candidate, at.claim, &at.found, facts, library)
    })
}

/// A claim matched against a conclusion an item offers (`each_match`).
struct Matched<'m> {
    offer: &'m Offer,
    /// The conclusion, as one candidate of the offer.
    candidate: &'m Node,
    /// What the reading of the conclusion asks first.
    first: &'m [Node],
    claim: &'m Node,
    found: Binding,
}

/// Each claim matched against each conclusion the groups offer under the
/// seed, and the first thing `left` finds left unsaid at a match; empty
/// where it finds nothing at any.
fn each_match(
    groups: &[Group],
    claims: &[Node],
    seed: &Binding,
    library: &Library,
    left: &mut dyn FnMut(Matched) -> Vec<Node>,
) -> Vec<Node> {
    let (whole, split) = (whole_claim(claims, library), split_claims(claims, library));
    for of in groups {
        let offer = Offer::of(of, library);
        for claim in offer.claims_read(&whole, &split) {
            for (candidate, first) in &offer.candidates {
                let Some(found) = match_tree(
                    candidate,
                    claim,
                    seed,
                    &offer.variables,
                    &offer.sites,
                    &library.ctx,
                ) else {
                    continue;
                };
                let unsaid = left(Matched {
                    offer: &offer,
                    candidate,
                    first,
                    claim,
                    found,
                });
                if !unsaid.is_empty() {
                    return unsaid;
                }
            }
        }
    }
    Vec::new()
}

/// What a claim the item concludes from a "there is" leaves unsaid of the
/// witness, where that is why no group takes it: each claim matched against
/// each conclusion the groups offer under the seed, the "there is" its
/// reading asks first matched by its body against each fact, as `supply`
/// matches it, and the witness's membership of its set where no fact says
/// it (`unwitnessed`), `m² ∈ ℤ` for `3 divides p² + q²` from `p² + q² =
/// 3m²`. Empty where no such reading leaves one.
pub fn witnesses_unsaid(
    groups: &[Group],
    claims: &[Node],
    facts: &[Node],
    seed: &Binding,
    library: &Library,
) -> Vec<Node> {
    each_match(groups, claims, seed, library, &mut |at| {
        let sites = &at.offer.sites;
        for exists in at.first {
            if !library.exists.contains(&exists.notation()) {
                continue;
            }
            let read = body_reading(exists, &at.found, &at.offer.variables, library);
            for fact in facts {
                let Some(got) = match_tree(
                    read.body,
                    fact,
                    &read.inside,
                    &read.seen,
                    sites,
                    &library.ctx,
                ) else {
                    continue;
                };
                let unsaid: Vec<Node> =
                    unwitnessed(exists, &got, facts, &read.seen, library, sites)
                        .into_iter()
                        .filter_map(|Unwitnessed { name, domain }| {
                            let value = got.get(&name.text)?;
                            let set = substitute_apart(domain, &got, &library.ctx);
                            Some(bound_in(Bound::Member, value, &set, library.env.g))
                        })
                        .collect();
                if !unsaid.is_empty() {
                    return unsaid;
                }
            }
        }
        Vec::new()
    })
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
    /// The letters `binding` leaves out, each with the value the search gave
    /// it: where a "there is" was supplied, the witness a line names for it.
    pub bound: Binding,
    /// The conclusion of the group each sentence of the claim takes, in the
    /// claim's order; none for an obtain, which takes the group's "there
    /// is" whole.
    pub concluded: Vec<Concluded>,
    /// What the readings taken ask a fact to state first, in the item's
    /// letters (`readings`); the facts that state it are `first_facts`.
    pub asks_first: Vec<Node>,
    /// For an obtain, the sentence of the group that says the "there is",
    /// by its place among the group's sentences.
    pub obtained: Option<usize>,
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
        let free = of.free_names(&library.ctx.binders);
        let mut bound = binding.clone();
        bound.retain(|name, _| !free.contains(name.as_str()));
        binding.retain(|name, _| free.contains(name.as_str()));
        Taken {
            group,
            binding,
            bound,
            concluded,
            asks_first: Vec::new(),
            obtained: None,
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
        let variables = group.letters(&trees);
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
            &offer.free,
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
            &offer.free,
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
    /// Of those, the ones free in the item's statements: a letter it binds,
    /// a sum's index, is matched afresh wherever it is bound.
    free: BTreeSet<String>,
    /// Where a property or function the item binds is applied.
    sites: Sites,
}

impl Offer {
    fn of(group: &Group, library: &Library) -> Offer {
        let (want, gives) = (&group.wants, &group.gives);
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
        let variables = group.letters(&trees);
        let free = group.free_names(&library.ctx.binders);
        // A conclusion is a sentence, so one that is a bare letter of the
        // item's is a statement letter.
        let letter = matches!(gives.as_slice(), [one]
            if one.is_name() && variables.contains(one.text.as_str()));
        Offer {
            letter,
            candidates,
            from,
            ways,
            need,
            variables,
            free,
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
    claims: &[Node],
    seed: &Binding,
    library: &Library,
) -> bool {
    !obtained(groups, facts, claims, seed, library).is_declined()
}

/// The first group of an item that gives a "there is" from the facts, with
/// the binding the facts fix; declined where none does.
///
/// The facts supply the group's hypotheses as well as what the reading asks
/// first, so that every letter the item says the "there is" of is bound: the
/// x of `x(n) → L as n → ∞` is fixed by that hypothesis alone. A letter the
/// citation gives no value and no line fixes, the n of odd-part's `let n ∈
/// ℕ`, is fixed first by what the step claims of the names it obtains
/// (`fixed_by_claim`): the facts put many things in ℕ, the page's 2 among
/// them, and only the claim says which one the "there is" is of.
pub fn obtained(
    groups: &[Group],
    facts: &[Node],
    claims: &[Node],
    seed: &Binding,
    library: &Library,
) -> Route<Taken> {
    for (group, of) in groups.iter().enumerate() {
        let (wants, gives) = (&of.wants, &of.gives);
        let asked: Vec<Node> = wants
            .iter()
            .flat_map(|(_, t)| conjuncts(t, library))
            .collect();
        for (sentence, concl) in gives.iter().enumerate() {
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
                let variables = of.letters(&need);
                let mut start = seed.clone();
                for (name, value) in
                    fixed_by_claim(&target, claims, seed, &variables, library)
                {
                    start.entry(name).or_insert(value);
                }
                let found =
                    supply(&need, facts, &start, &variables, library, &sites, false);
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
                        taken.obtained = Some(sentence);
                        return Built(taken);
                    }
                }
            }
        }
    }
    Route::no("no group of the item gives a \"there is\" from the facts named")
}

/// What an obtain's claim fixes of the item's letters: the claim says the
/// body of the "there is" with the names obtained for its bound letters, so
/// the parts of the body are supplied by the sentences of the claim, each
/// by its own, the bound letters matched as the item's are, and what that
/// gives the item's own letters is kept. Empty where the item gives no
/// "there is" written as one, or the claim says something else, which
/// `check_obtained_claims` reports.
fn fixed_by_claim(
    target: &Node,
    claims: &[Node],
    seed: &Binding,
    variables: &BTreeSet<String>,
    library: &Library,
) -> Binding {
    let said: Vec<Node> = claims.iter().flat_map(|c| conjuncts(c, library)).collect();
    let mut fixed = Binding::new();
    for part in conjuncts(target, library) {
        // The letters each level binds, and the body under the last.
        let mut bound: BTreeSet<String> = BTreeSet::new();
        let mut body = &part;
        while body.notation() == THERE_IS && body.children.len() == 3 {
            let letter = &body.children[0];
            if !letter.is_name() {
                break;
            }
            bound.insert(letter.text.to_string());
            body = &body.children[2];
        }
        if bound.is_empty() {
            continue;
        }
        let mut open = variables.clone();
        open.extend(bound.iter().cloned());
        let pieces = conjuncts(body, library);
        let Some(binding) =
            supply(&pieces, &said, seed, &open, library, &Sites::new(), false)
        else {
            continue;
        };
        for (name, value) in binding {
            if variables.contains(name.as_str())
                && !bound.contains(name.as_str())
                && !seed.contains_key(&name)
            {
                fixed.entry(name).or_insert(value);
            }
        }
    }
    fixed
}

/// Whether one part of what a definition says is a "there is", with a
/// property it applies read as what the binding says the property is.
fn existential(part: &Node, binding: &Binding, library: &Library) -> bool {
    let mut part = part.clone();
    if library.ctx.props.contains_key(&part.notation())
        && part.children.len() == 2
        && part.children[0].is_name()
    {
        let Some(stands) = binding.get(&part.children[0].text) else {
            return false;
        };
        if stands.notation() != PROPERTY_OF {
            return false;
        }
        let terms: Binding = binding
            .iter()
            .filter(|(_, v)| v.notation() != PROPERTY_OF)
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        let arg = substitute_apart(&part.children[1], &terms, &library.ctx);
        let mut at = Binding::new();
        at.insert(stands.text, arg);
        part = substitute_apart(&stands.children[0], &at, &library.ctx);
    }
    library.exists.contains(&part.notation())
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
    for group in groups {
        let (want, gives) = (&group.wants, &group.gives);
        let mut trees = gives.clone();
        trees.extend(want.iter().map(|(_, t)| t.clone()));
        let variables = group.letters(&trees);
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
