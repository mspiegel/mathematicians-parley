//! A citation supplies what the item asks, and claims what it concludes.

use std::borrow::Cow;
use std::collections::BTreeSet;

use indexmap::{IndexMap, IndexSet};

use super::library::{
    claimed_member, conjuncts, finished, readings, Group, Known, Library,
};
use super::Report;
use crate::corpus::proof::requires_item;
use crate::corpus::{
    cited_item, define_parts, for_pieces, references, DefineParts, Method, Step,
    Theorem,
};
use crate::formula::{walk, Node, NodeId};
use crate::matching::{
    binding_sites, instantiation, match_tree, substitute, substitute_apart, Binding,
    PROPERTY,
};
use crate::outcome::Built;
use crate::rules;
use crate::sorts::sentences;
use crate::text::squash;

type Sites = IndexSet<NodeId>;

fn names_of(trees: &[Node]) -> BTreeSet<String> {
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
/// what to do with each way once it is complete.
struct Ways<'v> {
    path: Vec<usize>,
    found: &'v mut dyn FnMut(&[usize]),
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
fn search(
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
            (ways.found)(&ways.path);
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
                let mut arg = first.children[1].clone();
                if arg.is_name() {
                    if let Some(bound) = binding.get(&arg.text) {
                        arg = bound.clone();
                    }
                }
                let mut at = Binding::new();
                at.insert(stands.text.clone(), arg.clone());
                first = substitute_apart(&stands.children[0], &at, ctx);
                // The formula a property stands for is the step's own, so a
                // name in it is the step's, even spelt as one of the item's.
                // Only an argument still to be matched is the item's to fill.
                open_names =
                    Cow::Owned(if arg.is_name() && variables.contains(&arg.text) {
                        [arg.text.clone()].into_iter().collect()
                    } else {
                        BTreeSet::new()
                    });
            }
        }
    }
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
                if let Some(smaller) = narrowed(&first, fact, binding) {
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
            let pinned =
                *pinned.get_or_insert_with(|| all_bound(&first, variables, binding));
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
fn narrowed(pattern: &Node, fact: &Node, binding: &Binding) -> Option<Node> {
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
    let asked = substitute(&pattern.children[1], &terms);
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

/// Every sentence of the claim takes a reading of the conclusion, and what
/// those readings ask for is then supplied by the facts.
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
) -> bool {
    let Some((claim, later)) = claims.split_first() else {
        let mut all = need.to_vec();
        all.extend(used.iter().cloned());
        return supply(&all, given, binding, variables, library, sites, true).is_some();
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
        if take(
            later, candidates, &found, &more, need, given, variables, library, sites,
        ) {
            return true;
        }
    }
    false
}

/// Whether one group of an item's conclusions covers what is claimed.
pub fn concludes(
    groups: &[Group],
    claims: &[Node],
    facts: &[Node],
    seed: &Binding,
    library: &Library,
) -> bool {
    // A conclusion is offered conjunct by conjunct, so a claim is asked for
    // the same way: `u ∈ Y and u ∈ Z` is the two facts a reading gives.
    let claims: Vec<Node> = claims.iter().flat_map(|c| conjuncts(c, library)).collect();
    for Group { wants: want, gives } in groups {
        let mut candidates: Vec<(Node, Vec<Node>)> = Vec::new();
        let mut sites = Sites::new();
        for concl in gives {
            binding_sites(concl, &library.ctx, &[], &mut sites);
            for (target, extra) in readings(concl, library) {
                let first: Vec<Node> =
                    extra.iter().flat_map(|e| conjuncts(e, library)).collect();
                for c in conjuncts(&target, library) {
                    candidates.push((c, first.clone()));
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
        if take(
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
            return true;
        }
    }
    false
}

/// Whether the item gives a "there is" from what the step names.
///
/// An obtain claims the body of what the item says there is, which
/// `concludes` does not read. What it does read is the way to the
/// existential: an item that gives one only from a line saying n is odd
/// needs that line as surely as it needs any other.
fn obtains(
    groups: &[Group],
    facts: &[Node],
    seed: &Binding,
    library: &Library,
) -> bool {
    for Group { gives, .. } in groups {
        for concl in gives {
            let mut sites = Sites::new();
            binding_sites(concl, &library.ctx, &[], &mut sites);
            for (target, extra) in readings(concl, library) {
                // The "there is" is the reading's target or a part of it, and
                // may be a property the definition applies, which the line
                // the step cites decides.
                let need: Vec<Node> =
                    extra.iter().flat_map(|e| conjuncts(e, library)).collect();
                let variables = names_of(&need);
                let found =
                    supply(&need, facts, seed, &variables, library, &sites, false);
                if let Some(found) = found {
                    if conjuncts(&target, library)
                        .iter()
                        .any(|part| existential(part, &found, library))
                    {
                        return true;
                    }
                }
            }
        }
    }
    false
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
        let arg = substitute(&part.children[1], &terms);
        let mut at = Binding::new();
        at.insert(stands.text.clone(), arg);
        part = substitute_apart(&stands.children[0], &at, &library.ctx);
    }
    library.exists.contains(&part.notation)
}

/// The requires lines of a step whose item does not conclude them, as
/// (line, item) pairs.
fn unconcluded(step: &Step, known: &Known, library: &Library) -> Vec<(usize, String)> {
    let scope = known.scope(step);
    let mut out = Vec::new();
    for req in &step.requires {
        let Some((named, _)) = requires_item(&req.how) else {
            continue;
        };
        let Some(groups) = library.groups(&step.just.item(&named)) else {
            continue;
        };
        let claims: Vec<Node> = sentences(&req.fact)
            .iter()
            .filter_map(|s| known.read(s))
            .collect();
        if claims.is_empty() {
            continue;
        }
        let (refs, _bad) = references(&req.how);
        let mut supplied: Vec<String> = Vec::new();
        for r in &refs {
            if let Some(text) = scope.get(r) {
                supplied.extend(sentences(text));
            }
        }
        // A requires line may not cite another, but the facts the lines above
        // it state are established for the same step and are what a dull fact
        // its own citation asks for is written as. A line below it is not yet
        // established (`SYNTAX.md`).
        supplied.extend(
            step.requires
                .iter()
                .take_while(|o| o.line != req.line)
                .map(|o| o.fact.clone()),
        );
        let mut read: Vec<Node> =
            supplied.iter().filter_map(|s| known.read(s)).collect();
        // A step said of every member in one line: its requires lines speak
        // of the member, whose membership the claim gives (`SYNTAX.md`).
        if step.openers.is_empty() {
            let claimed: Vec<Node> = sentences(&step.claim_text())
                .iter()
                .filter_map(|s| known.read(s))
                .collect();
            if let [claim] = claimed.as_slice() {
                if let Some((member, _)) = claimed_member(claim, library, &known.sorts)
                {
                    read.push(member);
                }
            }
        }
        let mut seed = Binding::new();
        for (name, value) in instantiation(&req.how) {
            if let Some(got) = known.read(&value) {
                seed.insert(name, got);
            }
        }
        // The facts a step's own citation is given, so that an item cited
        // on a requires line reaches what it reaches cited by a step.
        let parts = finished(read, claims, seed, library, known);
        // One use of the item, read as `concludes` reads it, or the item
        // applied as often as it takes (`derives`), which reads its
        // conclusions only as they stand. Neither covers the other.
        if concludes(&groups, &parts.claims, &parts.facts, &parts.seed, library) {
            continue;
        }
        if parts
            .claims
            .iter()
            .all(|c| derives(c, &groups, &parts.facts, library, 5))
        {
            continue;
        }
        out.push((req.line, named));
    }
    out
}

/// The fact follows from the cited item applied as often as it takes.
///
/// A closure line names a principle, not one use of it: `2k² + 2k ∈ ℤ`
/// cites the closure of the integers once where the kernel applies it three
/// times, and a reader wants the one line. So the item's own conclusions are
/// matched against the claim and against whatever they then ask for, and
/// nothing else is allowed in.
fn derives(
    claim: &Node,
    groups: &[Group],
    facts: &[Node],
    library: &Library,
    depth: i32,
) -> bool {
    if depth <= 0 {
        return false;
    }
    if facts.iter().any(|f| f.shape() == claim.shape()) {
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
                derives(&substitute(t, &binding), groups, facts, library, depth - 1)
            }) {
                return true;
            }
        }
    }
    false
}

/// The hypotheses of the item a step cites that nothing it names supplies,
/// or None where they are supplied or the step cites no item.
fn unsupplied(step: &Step, known: &Known, library: &Library) -> Option<Vec<String>> {
    let item = cited_item(&step.just)?;
    // A pointer that resolves to nothing is `check_citations`'s.
    let groups = library.groups(&step.just.item(&item))?;
    let parts = known.parts(step, library);
    let mut missing = None;
    for Group { wants: want, .. } in groups.iter() {
        if want.is_empty() {
            return None;
        }
        let trees: Vec<Node> = want.iter().map(|(_, t)| t.clone()).collect();
        let variables = names_of(&trees);
        // Where a binder applies a function or a property to what it binds,
        // that is what decides it, here as in the conclusion.
        let mut sites = Sites::new();
        for t in &trees {
            binding_sites(t, &library.ctx, &[], &mut sites);
        }
        if supply(
            &trees,
            &parts.facts,
            &parts.seed,
            &variables,
            library,
            &sites,
            false,
        )
        .is_some()
        {
            return None;
        }
        missing = Some(want.iter().map(|(t, _)| t.clone()).collect());
    }
    missing
}

/// Every way the step's facts supply the hypotheses of the item it cites, as
/// the facts each way uses; None where that cannot be said, because the step
/// cites nothing that has hypotheses to supply.
///
/// This is `unsupplied` searched to the end rather than to the first way.
fn ways_supplied(
    step: &Step,
    known: &Known,
    library: &Library,
) -> Option<Vec<Vec<Node>>> {
    let item = cited_item(&step.just)?;
    let groups = library.groups(&step.just.item(&item))?;
    let parts = known.parts(step, library);
    let mut out: Vec<Vec<Node>> = Vec::new();
    for Group { wants: want, .. } in groups.iter() {
        if want.is_empty() {
            return None;
        }
        let trees: Vec<Node> = want.iter().map(|(_, t)| t.clone()).collect();
        let variables = names_of(&trees);
        let mut sites = Sites::new();
        for t in &trees {
            binding_sites(t, &library.ctx, &[], &mut sites);
        }
        let mut record = |taken: &[usize]| {
            out.push(taken.iter().map(|&i| parts.facts[i].clone()).collect());
        };
        let mut ways = Ways {
            path: Vec::new(),
            found: &mut record,
        };
        let mut used = vec![false; parts.facts.len()];
        let _ = search(
            &trees,
            &parts.facts,
            &mut used,
            &parts.seed,
            &variables,
            library,
            &sites,
            false,
            Some(&mut ways),
        );
    }
    Some(out)
}

/// Every fact of `some` is among `all`, as many times as it is in `some`,
/// facts being the same when they are spelt the same.
fn within(some: &[Node], all: &[Node]) -> bool {
    let mut left: IndexMap<&str, usize> = IndexMap::new();
    for f in all {
        *left.entry(f.shape()).or_default() += 1;
    }
    some.iter().all(|f| match left.get_mut(f.shape()) {
        Some(n) if *n > 0 => {
            *n -= 1;
            true
        }
        _ => false,
    })
}

/// A citation supplies the hypotheses of what it cites.
///
/// They come from the lines named in `from` and from the `requires` lines,
/// each of which states one fact. A cited line supplies every sentence of
/// its claim, because a claim of several sentences is their conjunction.
///
/// The item is read as a pattern and the facts are ground, so a citation
/// that writes no instantiation is checked the same way as one that does.
/// Where an instantiation is written it seeds the binding, which makes it
/// checked rather than taken on trust.
pub fn check_hypotheses(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        if let Some(missing) = unsupplied(step, known, library) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} cites {}, which asks for {}, and what it cites does not supply them",
                    step.number,
                    cited_item(&step.just).unwrap_or_default(),
                    missing.join("; ")
                ),
            );
        }
    }
}

/// A citation's claim is what the item concludes, under the binding its
/// hypotheses fixed.
pub fn check_conclusion(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        let just = &step.just;
        if !just.head.is_item() {
            continue;
        }
        let head = just.head.to_string();
        let Some(groups) = library.groups(&just.item(&head)) else {
            continue;
        };
        let parts = known.parts(step, library);
        if parts.claims.is_empty() {
            continue;
        }
        if !concludes(&groups, &parts.claims, &parts.facts, &parts.seed, library) {
            report.say(
                &thm.path,
                just.line,
                format!(
                    "step {} claims something that {head} does not conclude",
                    step.number
                ),
            );
        }
    }
}

/// An obtain reaches a "there is" of the item it names.
///
/// What it claims is that existential's body, which `check_conclusion` does
/// not read. It does read the way there: a definition that gives one only
/// from a line saying n is odd, cited by an obtain that cites no such line,
/// has nothing to unfold.
pub fn check_obtained(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        let just = &step.just;
        let Some(item) = cited_item(just) else {
            continue;
        };
        if !just.head.is(Method::Obtain) {
            continue;
        }
        let Some(groups) = library.groups(&just.item(&item)) else {
            continue;
        };
        let parts = known.parts(step, library);
        if !obtains(&groups, &parts.facts, &parts.seed, library) {
            report.say(
                &thm.path,
                just.line,
                format!(
                    "step {} obtains from {item}, which says there is one only from something the step does not cite",
                    step.number
                ),
            );
        }
    }
}

/// A requires line needs what the item it cites concludes.
///
/// A step's citation is matched this way already. A requires line carries
/// the same kind of pointer to the same kind of item, and was checked only
/// for resolving, so an item that did not cover the fact went unnoticed.
pub fn check_requires(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        for (no, named) in unconcluded(step, known, library) {
            report.say(
                &thm.path,
                no,
                format!(
                    "the requires line of step {} needs something that {named} does not conclude",
                    step.number
                ),
            );
        }
    }
}

/// Whether a requires line below `req` in its step rests on what `req` says
/// is a member, or not zero, by a method that asks it of its atoms and the
/// terms it divides by (`METHODS.md`): `requires |PQ| ∈ ℝ` above `requires
/// |PQ|·|P′R′| ∈ ℝ: membership`, `requires d ∈ ℝ` above `requires 0 < d:
/// inequalities, from 3.1`, or `requires b − a ≠ 0` above `requires (f(a) −
/// f(b))/(b − a) ∈ ℝ: membership`. An order between terms is what
/// `inequalities` reasons from, so `requires sin(∠PQR) > 0` is asked for by
/// `requires sin(∠PQR) ≠ 0: inequalities` below it. Such a line is asked
/// for as surely as an item's hypothesis is (`SYNTAX.md`: a requires line
/// rests on the lines above it).
fn built_on(req: &crate::corpus::Requires, step: &Step, known: &Known) -> bool {
    const ASKING: [&str; 3] = ["membership", "inequalities", "algebra"];
    let Some(said) = known.read(&req.fact) else {
        return false;
    };
    // t ∈ X names t, and t ≠ u, read as not t = u, names t: a method asks
    // them of its atoms. t < u names both sides, and only `inequalities`
    // reads an order.
    let (held, asking): (Vec<&Node>, &[&str]) = match said.notation.as_str() {
        "membership" if said.children.len() == 2 => (vec![&said.children[0]], &ASKING),
        "logical-not"
            if said.children.len() == 1
                && said.children[0].notation == "equality"
                && said.children[0].children.len() == 2 =>
        {
            (vec![&said.children[0].children[0]], &ASKING)
        }
        "order" if said.children.len() == 2 => (
            said.children
                .iter()
                .filter(|c| c.notation != "numeral")
                .collect(),
            &["inequalities"],
        ),
        _ => return false,
    };
    let atoms: Vec<String> = held.iter().map(|h| h.shape().to_string()).collect();
    step.requires
        .iter()
        .skip_while(|r| r.line != req.line)
        .skip(1)
        .filter(|r| {
            let how = str::trim(&r.how);
            asking
                .iter()
                .any(|m| how == *m || how.starts_with(&format!("{m},")))
        })
        .filter_map(|r| known.read(&r.fact))
        .any(|n| {
            let held = if n.notation == "membership" && n.children.len() == 2 {
                &n.children[0]
            } else {
                &n
            };
            atoms.iter().any(|atom| {
                held.shape() != *atom
                    && held.walk().iter().any(|part| part.shape() == *atom)
            })
        })
}

/// The requires lines a cited item's function hypotheses ask for.
///
/// `let t : {a, …, b} → ℝ` in a sum item, where the step's summand is what t
/// stands for, says every term is real. That is not a line the page writes:
/// the terms are built from numbers the step names, and the elaborator
/// builds each term's membership from theirs, as `algebra` builds a
/// compound's from its atoms'. So what the hypothesis asks is the membership
/// of each name the summand holds that the sum does not bind: C(m, k)·x^(m −
/// k)·y^k asks x ∈ ℝ, y ∈ ℝ and m ∈ ℕ₀, and nothing of k.
///
/// `let g : D → ℝ` where g stands for a function the proof defines asks
/// what g maps between, said whole and as the item says it: `g := g, D :=
/// [a, b]` asks g : [a, b] → ℝ and nothing else of g. The checker reads the
/// define as its rule, and the kernel asks it of every value the rule gives.
struct FamilyAsks {
    held: BTreeSet<String>,
    values: Vec<Node>,
    types: Vec<Node>,
}

fn family_asks(step: &Step, known: &Known, library: &Library) -> FamilyAsks {
    let just = &step.just;
    let groups = cited_item(just)
        .and_then(|item| library.groups(&just.item(&item)))
        .expect("a step whose item was just read");
    let parts = known.parts(step, library);
    let mut held = BTreeSet::new();
    let mut values = Vec::new();
    // The item's function types under what the citation writes for its
    // letters, `f := F`, where that makes the function one the proof
    // defines. What the step claims is no guide to the letters: an `obtain`
    // claims the witness, not the item's conclusion.
    let types = library
        .function_types(&just.item(&cited_item(just).expect("a cited item")))
        .iter()
        .map(|t| substitute(t, &parts.seed))
        .filter(|t| t.children[0].notation == PROPERTY)
        .collect();
    for Group { wants: want, gives } in groups.iter() {
        let mut trees = gives.clone();
        trees.extend(want.iter().map(|(_, t)| t.clone()));
        let mut sites = Sites::new();
        for t in &trees {
            binding_sites(t, &library.ctx, &[], &mut sites);
        }
        let variables = names_of(&trees);
        // What a function letter stands for is read where the item applies
        // it: its conclusions against what the step claims, and its
        // hypotheses against what the step cites, since an `obtain` claims
        // the witness and says nothing of the function.
        let mut pairs: Vec<(Node, &Node)> = Vec::new();
        for concl in gives {
            for (target, _extra) in readings(concl, library) {
                for cand in conjuncts(&target, library) {
                    for claim in &parts.claims {
                        pairs.push((cand.clone(), claim));
                    }
                }
            }
        }
        for (_, hyp) in want.iter() {
            for fact in &parts.facts {
                pairs.push((hyp.clone(), fact));
            }
        }
        for (pattern, ground) in &pairs {
            let found = match_tree(
                pattern,
                ground,
                &parts.seed,
                &variables,
                &sites,
                &library.ctx,
            );
            for value in found.iter().flat_map(|b| b.values()) {
                if value.notation == PROPERTY {
                    for n in value.children[0].names() {
                        if n != value.text {
                            held.insert(n);
                        }
                    }
                    values.push(value.clone());
                }
            }
        }
    }
    FamilyAsks {
        held,
        values,
        types,
    }
}

impl FamilyAsks {
    /// Whether one requires line's fact is a membership the item's function
    /// hypotheses ask for.
    fn asks(&self, fact: &str, known: &Known) -> bool {
        let Some(node) = known.read(fact) else {
            return false;
        };
        if node.notation == "function-type" {
            return self.types.iter().any(|t| t.shape() == node.shape());
        }
        // Or the hypothesis said whole, of every value the function takes:
        // `x : ℕ → ℝ` where x(n) is a partial sum of the reciprocals of T
        // asks that every partial sum be real. T is a defined function and
        // no name a membership could be asked of, so what is compared is the
        // value itself, read at the name the line binds.
        if node.notation == "for-all" && node.children.len() == 3 {
            let (bound, body) = (&node.children[0], &node.children[2]);
            if body.notation != "membership"
                || body.children[1].notation != "number-systems"
            {
                return false;
            }
            return self.values.iter().any(|v| {
                let mut at = Binding::new();
                at.insert(v.text.clone(), bound.clone());
                substitute(&v.children[0], &at).shape() == body.children[0].shape()
            });
        }
        node.notation == "membership"
            && node.children[1].notation == "number-systems"
            && !node.children[0].names().is_empty()
            && node.children[0].names().is_subset(&self.held)
    }
}

/// What the functions a proof defines ask of what the step's claim applies
/// them to: `define M(X) := …, for X ∈ 𝒫A` and a claim holding M(X) ask
/// `X ∈ 𝒫A`, since M(X) is M's rule only there. The checker reads the name
/// as its rule without asking, and the kernel does not (`SYNTAX.md`: a
/// define may name a function).
fn domains_asked(thm: &Theorem, step: &Step) -> BTreeSet<String> {
    let claim: Vec<char> = step.claim_text().chars().collect();
    let mut out = BTreeSet::new();
    // Each function by name, with the domain of each argument in order.
    let mut functions: Vec<(String, Vec<String>)> = Vec::new();
    for d in &thm.defines {
        match define_parts(&d.text) {
            Built(DefineParts::Recursion(r)) => {
                for name in &r.names {
                    functions.push((name.clone(), vec![r.domain.clone()]));
                }
            }
            Built(DefineParts::One(one)) if !one.params.is_empty() => {
                functions.push((
                    one.name.clone(),
                    one.params.iter().map(|p| p.domain.clone()).collect(),
                ));
            }
            _ => {}
        }
    }
    let find = |needle: &[char], from: usize| -> Option<usize> {
        if needle.len() > claim.len() {
            return None;
        }
        (from..=claim.len() - needle.len())
            .find(|&i| claim[i..i + needle.len()] == *needle)
    };
    for (name, domains) in &functions {
        let needle: Vec<char> = format!("{name}(").chars().collect();
        let name_len = name.chars().count();
        let mut at = 0;
        while let Some(found) = find(&needle, at) {
            at = found;
            if at > 0
                && (claim[at - 1].is_alphanumeric() || "_′".contains(claim[at - 1]))
            {
                at += 1;
                continue;
            }
            let start = at + name_len;
            let mut depth: i64 = 0;
            for end in start..claim.len() {
                depth += match claim[end] {
                    '(' => 1,
                    ')' => -1,
                    _ => 0,
                };
                if depth == 0 {
                    let args: String = claim[start + 1..end].iter().collect();
                    let args = for_pieces(&args);
                    if args.len() != domains.len() {
                        break;
                    }
                    for (arg, domain) in args.iter().zip(domains) {
                        out.insert(squash(&format!("{arg} ∈ {domain}")));
                        // A power set's member is a part, which the page may
                        // say with ⊆: `for X ⊆ A` asks C ⊆ A of M(C).
                        if let Some(inner) = domain.strip_prefix('𝒫') {
                            let inner = if inner.starts_with('(')
                                && inner.ends_with(')')
                                && inner.len() >= 2
                            {
                                &inner[1..inner.len() - 1]
                            } else {
                                inner
                            };
                            out.insert(squash(&format!("{arg} ⊆ {inner}")));
                        }
                    }
                    break;
                }
            }
            at += 1;
        }
    }
    out
}

/// What an item citation names, it needs.
///
/// `DATABASE.md` holds that a named thing doing no work is an error, the
/// shape of a `target` that never fires. For a step citing an item, the
/// item's statement says what is needed and the two checks above say
/// whether it is supplied; taking each named line away in turn and asking
/// them again says which lines supply it. One whose absence changes nothing
/// was supplying nothing. A requires line another one of the step leans on
/// is kept by the second check. A define is not asked about: citing one
/// names what a symbol means and supplies no fact.
pub fn check_surplus(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    let defines: BTreeSet<&str> =
        thm.defines.iter().map(|d| d.label.as_str()).collect();

    let holds = |step: &Step| -> bool {
        if unsupplied(step, known, library).is_some()
            || !unconcluded(step, known, library).is_empty()
        {
            return false;
        }
        // What the step claims follows from what the item concludes and what
        // the step names: a definition read either way takes the other side
        // from a cited line, which asks for it as surely as a hypothesis
        // does.
        let item = cited_item(&step.just).unwrap_or_default();
        let Some(groups) = library.groups(&step.just.item(&item)) else {
            return false;
        };
        let parts = known.parts(step, library);
        if step.just.head.is(Method::Obtain) {
            return obtains(&groups, &parts.facts, &parts.seed, library);
        }
        parts.claims.is_empty()
            || concludes(&groups, &parts.claims, &parts.facts, &parts.seed, library)
    };

    for step in &thm.steps {
        let just = &step.just;
        let Some(item) = cited_item(just) else {
            continue;
        };
        if library.groups(&just.item(&item)).is_none() || !holds(step) {
            continue;
        }
        let mut refs: IndexSet<&String> = IndexSet::new();
        refs.extend(just.refs.iter());
        // Taking a line away leaves a step whose facts are some of these, so
        // a way that step could supply the item is one of the ways these do.
        // Where no way these supply it fits in what is left, the step without
        // the line is not supplied, and asking again would only say so; the
        // one search here takes the place of a search for each line, each
        // of which had to try everything to find nothing.
        let ways = ways_supplied(step, known, library);
        let facts = known.parts(step, library);
        for r in refs {
            if defines.contains(r.as_str()) {
                continue;
            }
            let mut lighter = step.clone();
            lighter.just.refs = just.refs.iter().filter(|x| *x != r).cloned().collect();
            if let Some(ways) = &ways {
                let left = known.parts(&lighter, library);
                // What the argument above rests on, asked rather than assumed.
                if within(&left.facts, &facts.facts)
                    && !ways.iter().any(|way| within(way, &left.facts))
                {
                    continue;
                }
            }
            if holds(&lighter) {
                report.say(
                    &thm.path,
                    just.line,
                    format!(
                        "step {} cites {r}, and {item} asks for nothing it says",
                        step.number
                    ),
                );
            }
        }
        let asks = family_asks(step, known, library);
        let in_domain = domains_asked(thm, step);
        for (i, req) in step.requires.iter().enumerate() {
            let mut lighter = step.clone();
            lighter.requires.remove(i);
            if holds(&lighter)
                && !asks.asks(&req.fact, known)
                && !in_domain.contains(&squash(&req.fact))
                && !built_on(req, step, known)
            {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of step {} says {}, and neither {item} nor the step's other lines ask for it",
                        step.number, req.fact
                    ),
                );
            }
        }
    }
}
