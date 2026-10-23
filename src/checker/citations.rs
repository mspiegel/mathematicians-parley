//! A citation supplies what the item asks, and claims what it concludes.

use std::cell::OnceCell;
use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use super::formulas::chain_links;
use super::library::{
    introduced, listed_seed, typed_in_scope, typed_seed, Known, Search,
};
use super::record::{Cited, FirstAt};
use super::structure::letters_in_scope;
use super::Report;
use crate::citing::{
    asked, bound_in, claimed_member, concludes, conjuncts, derives, filled, finished,
    function_values, identities_unsaid, index_system, obtained, obtains, range_system,
    readings, said_once, search, stood_for, substitution_unsaid, supplies, supply,
    taken, taken_ways, type_said_otherwise, with_parts, witnesses_unsaid, Bound,
    Concluded, Group, Introduced, Library, Parts, Sites, Taken, Ways,
};
use crate::corpus::proof::{reason_as_step, Requires};
use crate::corpus::skeleton::Source;
use crate::corpus::{
    define_parts, DefineParts, FileScope, Head, Item, Method, Step, Theorem,
};
use crate::formula::page::{self, conjoined, Written};
use crate::formula::symbol::Symbol;
use crate::formula::{ByShape, Node, Sort};
use crate::matching::{
    alike, binding_sites, match_tree, standard, substitute_apart, Binding, Context,
    FxIndexMap, FxIndexSet,
};
use crate::notations::{
    APPLICATION, APPLICATION_TO_TWO, BICONDITIONAL, CONDITIONAL, EQUALITY, FOR_ALL,
    FOR_ALL_PART, FOR_ALL_SETS, FUNCTION_ON, FUNCTION_TYPE, IMPLICATION, INTEGER_RANGE,
    LOGICAL_NOT, MEMBERSHIP, NUMBER_SYSTEMS, NUMERAL, ORDER, PLUS, POWERSET,
    PROPERTY_OF, SUBSET, THERE_IS, THERE_IS_SOME,
};
use crate::outcome::{Built, Declined, Route};
use crate::rules::{self, System};
use crate::sorts::TYPING;

/// A requires line whose cited item does not give its fact.
struct Unconcluded {
    /// The requires line.
    line: usize,
    /// The item it cites, as it names it.
    item: String,
    /// The item's hypotheses the line's facts do not supply, where that is
    /// why; None where they are supplied and the item concludes something
    /// else.
    missing: Option<Vec<String>>,
}

/// The requires lines of a step whose item does not conclude them.
fn unconcluded(step: &Step, known: &Known, library: &Library) -> Vec<Unconcluded> {
    let mut out = Vec::new();
    for req in &step.requires {
        let Some((named, _)) = req.cited_item() else {
            continue;
        };
        let Some(groups) = library.groups(&step.just.item(&named)) else {
            continue;
        };
        let Some(parts) = requires_parts(step, req, &[], known, library) else {
            continue;
        };
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
        let alone = || Some(Rc::new(concluded_alone(&groups, &parts, library)));
        out.push(Unconcluded {
            line: req.line,
            item: named,
            missing: missing_hypotheses(&groups, &parts, false, &alone, library),
        });
    }
    out
}

/// What a requires line's citation supplies and claims: the line's fact is
/// its claim, and its facts are the lines its reason names, the requires
/// lines above it, and the member a claim said of every member names, each
/// read with the defines the line cites, all but those `without` names.
/// None where the fact does not read, which `check_formulas` reports.
fn requires_parts(
    step: &Step,
    req: &Requires,
    without: &[&str],
    known: &Known,
    library: &Library,
) -> Option<Parts> {
    let scope = known.scope(step);
    let mut refs = req.lines().to_vec();
    refs.retain(|r| !without.contains(&r.as_str()));
    // A define is written out where the line cites it (`Known::citing`).
    let item = req.cited_item().map(|(named, _)| step.just.item(&named));
    let defined = known.citing_item(&refs, item.as_deref());
    let read_all = |written: &Written| -> Vec<Node> {
        written
            .sentences()
            .iter()
            .filter_map(|s| known.read_citing(s, &defined))
            .collect()
    };
    let mut claims = read_all(&req.fact);
    if claims.is_empty() {
        return None;
    }
    let mut read: Vec<Node> = Vec::new();
    // A requires line said of every member, "for all n ∈ ℕ, P", is read at
    // the member as a step is, where the item it cites says no "for all"
    // (`citing::at_a_member`): the membership is a fact, P the claim.
    let at_member = item
        .as_deref()
        .and_then(|name| library.item(name))
        .is_some_and(|i| !i.says_for_all());
    if at_member {
        if let [claim] = claims.as_slice() {
            if let Some((member, body)) = claimed_member(claim, library.env.g) {
                read.push(member);
                claims = vec![body];
            }
        }
    }
    for r in &refs {
        if let Some(written) = scope.get(r) {
            read.extend(known.supplied(written, &defined));
        }
    }
    // A requires line may not cite another, but the facts the lines above
    // it state are established for the same step and are what a dull fact
    // its own citation asks for is written as.
    for o in step.requires_above(req.line) {
        read.extend(read_all(&o.fact));
    }
    // A step said of every member in one line: its requires lines speak
    // of the member, whose membership the claim gives (`SYNTAX.md`).
    if step.openers.is_empty() {
        if let [claim] = read_all(&step.claim).as_slice() {
            if let Some((member, _)) = claimed_member(claim, library.env.g) {
                read.push(member);
            }
        }
    }
    let letters = req
        .cited_item()
        .and_then(|(named, _)| library.item_sorts(&step.just.item(&named)));
    let mut seed = known.seed(req.values(), &defined, letters);
    if let Some((named, _)) = req.cited_item() {
        listed_seed(
            &mut seed,
            &step.just.item(&named),
            req.line,
            known,
            library,
            &defined,
        );
    }
    // The facts a step's own citation is given, so that an item cited
    // on a requires line reaches what it reaches cited by a step, the
    // memberships the page says once among them.
    let mut parts = finished(read, claims, seed, library, &known.sorts);
    let typed = super::library::typed_in_scope(known, step);
    said_once(
        &mut parts,
        &introduced(known, step),
        &super::library::points_introduced(known, step),
        &typed,
        library,
        &known.sorts,
    );
    if let Some((named, _)) = req.cited_item() {
        typed_seed(&mut parts, &step.just.item(&named), step, known, library);
    }
    Some(parts)
}

/// What the item an obtain cites says there is, at the step: the item's
/// statements, each letter as the step's lines fix it (`obtained`). None
/// where the step obtains from no item, or from a definition that unfolds,
/// which gives the existence the step claims, reached from the claim and
/// never asked of the item; declined where no group of the item gives a
/// "there is" from what the step names.
pub fn obtained_there(
    step: &Step,
    library: &Library,
    known: &Known,
) -> Option<Route<Vec<Node>>> {
    if !step.just.head.is(Method::Obtain) {
        return None;
    }
    let name = step.just.item(&step.just.cited_item()?);
    if library.item(&name)?.unfolds() {
        return None;
    }
    let groups = library.groups(&name)?;
    let route = searched(step, Search::Obtains, known, library)?;
    Some(route.borrowed().map(|taken| {
        // An item saying "A ↔ there is …" gives the "there is", the
        // reading whose target it is, as the build obtains from it.
        groups[taken.group]
            .gives
            .iter()
            .map(|said| {
                let there_is = readings(said, library)
                    .into_iter()
                    .map(|r| r.claimed)
                    .find(|t| library.exists.contains(&t.notation()))
                    .unwrap_or_else(|| said.clone());
                filled(&there_is, &taken.binding, &library.ctx)
            })
            .collect()
    }))
}

/// How a step's citation of an item is read: the group it takes and the
/// binding, by `taken` for a step that concludes what it claims and by
/// `obtained` for an obtain, over the parts the checks read; None where the
/// step cites no item or no group reads the citation, which the checks
/// report.
pub fn cited(step: &Step, library: &Library, known: &Known) -> Option<Cited> {
    let item = step.just.item(&step.just.cited_item()?);
    let groups = library.groups(&item)?;
    let parts = known.parts(step, library);
    let read = searched(step, search_of(step), known, library)?;
    let Built(taken) = &*read else {
        return None;
    };
    let before: usize = groups[..taken.group].iter().map(|g| g.gives.len()).sum();
    let stated = taken.first_facts(&groups, &parts.facts, library);
    let firsts = firsts_at(step, &step.just.refs, &item, &stated, known, library);
    Some(Cited {
        item,
        group: taken.group,
        obtained: taken.obtained,
        concluded: across_groups(taken, before),
        firsts,
        binding: taken.binding.clone(),
        bound: taken.bound.clone(),
        written: parts.seed.clone(),
    })
}

/// Each requires line's citation of an item, by the line it is on
/// (`cited_requires`), and the citation of the reason under a let saying a
/// kind of number, read as a requires line of the step below the let, as
/// `check_requires` reads it.
pub fn requires_cited(
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> IndexMap<usize, Cited> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        for req in &step.requires {
            if let Some(read) = cited_requires(step, req, library, known) {
                out.insert(req.line, read);
            }
        }
    }
    for d in &thm.defines {
        // A let whose kind does not read is reported where the checker
        // judges the let, and the build builds nothing with a problem.
        let Ok(Some(kinded)) = d.kinded(&thm.path, &known.env.g.members) else {
            continue;
        };
        let Some(after) = thm.step_after(d.line) else {
            continue;
        };
        let under = Step {
            requires: vec![kinded.shown.clone()],
            ..after.clone()
        };
        if let Some(read) = cited_requires(&under, &kinded.shown, library, known) {
            out.insert(kinded.shown.line, read);
        }
    }
    out
}

/// How a requires line's citation of an item is read, over the parts the
/// line's check reads (`requires_parts`): what its reason names, the lines
/// above it, and the member its step's claim is said of. None where the
/// line cites no item or no group concludes its fact, the item then applied
/// as often as it takes (`check_requires`).
pub fn cited_requires(
    step: &Step,
    req: &Requires,
    library: &Library,
    known: &Known,
) -> Option<Cited> {
    let (named, _) = req.cited_item()?;
    let item = step.just.item(&named);
    let groups = library.groups(&item)?;
    let parts = requires_parts(step, req, &[], known, library)?;
    let Built(taken) =
        taken(&groups, &parts.claims, &parts.facts, &parts.seed, library)
    else {
        return None;
    };
    let before: usize = groups[..taken.group].iter().map(|g| g.gives.len()).sum();
    let stated = taken.first_facts(&groups, &parts.facts, library);
    let firsts = firsts_at(step, req.lines(), &item, &stated, known, library);
    Some(Cited {
        item,
        group: taken.group,
        obtained: taken.obtained,
        concluded: across_groups(&taken, before),
        firsts,
        binding: taken.binding,
        bound: taken.bound,
        written: parts.seed,
    })
}

/// Where each of `firsts` stands among the lines `refs` names at `step`: the
/// sentence of a line it is, or is a part of, or the line where it is the
/// line's sentences together, each read as the citation of `item` reads
/// them (`Known::supplied`). A fact no line names says has no place.
fn firsts_at(
    step: &Step,
    refs: &[String],
    item: &str,
    firsts: &[Node],
    known: &Known,
    library: &Library,
) -> Vec<FirstAt> {
    let scope = known.scope(step);
    let defined = known.citing_item(refs, Some(item));
    let mut out = Vec::new();
    for first in firsts {
        let found = refs.iter().find_map(|r| {
            let written = scope.get(r)?;
            line_states(
                first,
                r,
                &known.said_parts(written, Some(&defined)),
                library,
            )
        });
        if let Some(at) = found.filter(|at| !out.contains(at)) {
            out.push(at);
        }
    }
    out
}

/// Where `fact` stands in the line `line`, whose sentences read as `parts`
/// (`firsts_at`).
fn line_states(
    fact: &Node,
    line: &str,
    parts: &[Option<Node>],
    library: &Library,
) -> Option<FirstAt> {
    let ctx = &library.ctx;
    let none = IndexMap::new();
    // Each read in the standard order the fact is in.
    let states = |n: &Node| alike(&standard(n, ctx), fact, ctx, &none, &none);
    for (i, part) in parts.iter().enumerate() {
        let Some(sentence) = part else {
            continue;
        };
        if states(sentence) {
            return Some(FirstAt {
                line: line.to_string(),
                sentence: Some(i),
                part: None,
            });
        }
        // Counted as written.
        if let Some(j) = conjuncts(sentence, library).iter().position(states) {
            return Some(FirstAt {
                line: line.to_string(),
                sentence: Some(i),
                part: Some(j),
            });
        }
    }
    let whole = conjoined(library.env.g, parts.iter().flatten().cloned().collect())?;
    states(&whole).then(|| FirstAt {
        line: line.to_string(),
        sentence: None,
        part: None,
    })
}

/// What `taken` concludes, each sentence counted across the item's groups,
/// `before` being the sentences of the groups ahead of the one it takes.
fn across_groups(taken: &Taken, before: usize) -> Vec<Concluded> {
    taken
        .concluded
        .iter()
        .map(|c| Concluded {
            sentence: before + c.sentence,
            way: c.way,
        })
        .collect()
}

/// What a step citing an item, other than to obtain, makes each of its
/// letters, as the matcher reads the citation (`taken`): the values it
/// writes and what its claim and lines fix. None where the step cites no
/// item, or no group of it concludes the claim.
pub fn bound_there(step: &Step, library: &Library, known: &Known) -> Option<Binding> {
    if step.just.head.is(Method::Obtain) {
        return None;
    }
    step.just.cited_item()?;
    let read = searched(step, Search::Takes, known, library)?;
    let Built(taken) = &*read else {
        return None;
    };
    Some(taken.binding.clone())
}

/// The hypotheses of the item a step cites that nothing it names supplies,
/// or None where they are supplied or the step cites no item.
fn unsupplied(step: &Step, known: &Known, library: &Library) -> Option<Vec<String>> {
    let item = step.just.cited_item()?;
    // A pointer that resolves to nothing is `check_citations`'s.
    let groups = library.groups(&step.just.item(&item))?;
    let parts = known.parts(step, library);
    let takes = !searched(step, Search::Takes, known, library)?.is_declined();
    let alone = || searched(step, Search::Alone, known, library);
    missing_hypotheses(&groups, &parts, takes, &alone, library)
}

/// The hypotheses of an item that a citation's facts do not supply, as the
/// item writes them; None where every one is supplied, or where a group of
/// the item asks for nothing. A step's citation and a requires line's are
/// asked the same way. `takes` is whether a group covers the claim
/// (`Search::Takes`), and `alone` the group whose conclusions alone do
/// (`Search::Alone`), asked only where it is wanted.
fn missing_hypotheses(
    groups: &[Group],
    parts: &Parts,
    takes: bool,
    alone: &dyn Fn() -> Option<Rc<Route<Taken>>>,
    library: &Library,
) -> Option<Vec<String>> {
    // The hypotheses are supplied under the binding the claim fixes as well,
    // where a property is fixed only by what it is said of in the claim:
    // count-step's P(k + 1) is `a(k + 1) = 0` because the claim counts the i
    // with a(i) = 0. A group the citation takes has them supplied.
    if !parts.claims.is_empty() && takes {
        return None;
    }
    // Where the claim is what a group concludes, the hypotheses missing are
    // those of that group nothing supplies under what the claim fixes, and
    // not every hypothesis it has: floor-between's x ∈ ℝ at x := A + N is
    // said once, and only k ∈ ℤ at k := ⌊A⌋ + N is not supplied.
    let alone = (!parts.claims.is_empty()).then(alone).flatten();
    if let Some(Built(alone)) = alone.as_deref() {
        // Each is said at what the claim fixes, in the page's notation, so
        // that `P or Q` with P := 2 = P reads `2 = P or Q` and does not
        // seem to name the proof's own P; and at what the citation writes,
        // which fixes a letter the conclusion does not hold: c := m.
        let mut fixed = parts.seed.clone();
        for (name, value) in &alone.binding {
            fixed.insert(*name, value.clone());
        }
        let group = &groups[alone.group];
        let unmet: Vec<String> = group
            .wants
            .iter()
            .filter(|(_, tree)| {
                !supplied_alone(tree, group, parts, &alone.binding, library)
            })
            .map(|(_, tree)| library.env.g.print(&filled(tree, &fixed, &library.ctx)))
            .collect();
        if !unmet.is_empty() {
            return Some(unmet);
        }
    }
    let mut missing = None;
    for group in groups.iter() {
        let want = &group.wants;
        if want.is_empty() {
            return None;
        }
        let trees: Vec<Node> = want.iter().map(|(_, t)| t.clone()).collect();
        let variables = group.letters(&trees);
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
        // Each under what the citation writes for its letters: `c := m`
        // shows gcd(m, 3), not the item's gcd(c, 3). Those the facts supply
        // one at a time are left out, as 2 ∈ ℤ at d := 2 is, which is said
        // once; where every one is supplied alone and not all together, all
        // are named.
        let print = |tree: &Node| {
            library
                .env
                .g
                .print(&filled(tree, &parts.seed, &library.ctx))
        };
        let unmet: Vec<String> = want
            .iter()
            .filter(|(_, tree)| {
                !supplied_alone(tree, group, parts, &parts.seed, library)
            })
            .map(|(_, tree)| print(tree))
            .collect();
        missing = Some(if unmet.is_empty() {
            want.iter().map(|(_, tree)| print(tree)).collect()
        } else {
            unmet
        });
    }
    missing
}

/// The search `how` of the item a step cites, over the step's parts, made
/// once however many checks ask it (`Known::searches`). None where the step
/// cites no item or the item has no groups, which `check_citations`
/// reports.
pub fn searched(
    step: &Step,
    how: Search,
    known: &Known,
    library: &Library,
) -> Option<Rc<Route<Taken>>> {
    let item = step.just.item(&step.just.cited_item()?);
    let groups = library.groups(&item)?;
    let parts = known.parts(step, library);
    let key = (
        Rc::as_ptr(&parts) as usize,
        Rc::as_ptr(&groups) as usize,
        how,
    );
    if let Some(found) = known.searches.borrow().get(&key) {
        return Some(found.clone());
    }
    let made = Rc::new(match how {
        Search::Takes => {
            taken(&groups, &parts.claims, &parts.facts, &parts.seed, library)
        }
        Search::Obtains => obtained(&groups, &parts.facts, &parts.seed, library),
        Search::Alone => concluded_alone(&groups, &parts, library),
    });
    known.searches.borrow_mut().insert(key, made.clone());
    Some(made)
}

/// `searched` for what the step's method reads: an obtain obtains, and
/// every other citation takes.
fn search_of(step: &Step) -> Search {
    if step.just.head.is(Method::Obtain) {
        Search::Obtains
    } else {
        Search::Takes
    }
}

/// The group whose conclusion the claim is, read from the claim and the
/// values the citation gives, with what that fixes; its hypotheses are not
/// asked. Declined where no conclusion of the item is the claim.
fn concluded_alone(groups: &[Group], parts: &Parts, library: &Library) -> Route<Taken> {
    let gives_only: Vec<Group> = groups
        .iter()
        .map(|g| Group {
            wants: Vec::new(),
            gives: g.gives.clone(),
            functions: g.functions.clone(),
            identities: g.identities.clone(),
        })
        .collect();
    taken(
        &gives_only,
        &parts.claims,
        &parts.facts,
        &parts.seed,
        library,
    )
}

/// Whether the citation's facts supply one hypothesis on its own, under the
/// binding the claim fixed.
fn supplied_alone(
    want: &Node,
    group: &Group,
    parts: &Parts,
    binding: &Binding,
    library: &Library,
) -> bool {
    let trees = [want.clone()];
    let variables = group.letters(&trees);
    let mut sites = Sites::new();
    binding_sites(want, &library.ctx, &[], &mut sites);
    supply(
        &trees,
        &parts.facts,
        binding,
        &variables,
        library,
        &sites,
        false,
    )
    .is_some()
}

/// Every way the step's facts supply the hypotheses of the item it cites, as
/// the facts each way uses; None where that cannot be said, because the step
/// cites nothing that has hypotheses to supply.
///
/// This is `unsupplied` searched to the end rather than to the first way, by
/// both of its routes: the claim taking a group of the item, and a search
/// with nothing fixed. A way is the facts it took, each once, though a fact
/// the binding has pinned may supply two hypotheses.
fn ways_supplied(
    step: &Step,
    known: &Known,
    library: &Library,
) -> Option<Vec<Vec<Node>>> {
    let item = step.just.cited_item()?;
    let groups = library.groups(&step.just.item(&item))?;
    let parts = known.parts(step, library);
    let mut out: Vec<Vec<Node>> = Vec::new();
    let took = |path: &[usize]| -> Vec<Node> {
        let distinct: BTreeSet<usize> = path.iter().copied().collect();
        distinct
            .into_iter()
            .map(|i| parts.facts[i].clone())
            .collect()
    };
    // A step whose claim the item concludes is supplied by the ways that
    // conclude it: the item's letters are what matching its conclusion
    // against the claim fixes, and its hypotheses are supplied under that.
    // Its hypotheses searched alone would bind the letters to anything the
    // facts hold, which is not what the step does and, with few pairs
    // written, is a search over every arrangement of the facts. An `obtain`
    // claims the body of what the item concludes, not the conclusion, and
    // is supplied by its hypotheses alone.
    if !parts.claims.is_empty() && !step.just.head.is(Method::Obtain) {
        taken_ways(
            &groups,
            &parts.claims,
            &parts.facts,
            &parts.seed,
            library,
            &mut |path| out.push(took(path)),
        );
        return Some(out);
    }
    for group in groups.iter() {
        let want = &group.wants;
        if want.is_empty() {
            return None;
        }
        let trees: Vec<Node> = want.iter().map(|(_, t)| t.clone()).collect();
        let variables = group.letters(&trees);
        let mut sites = Sites::new();
        for t in &trees {
            binding_sites(t, &library.ctx, &[], &mut sites);
        }
        let mut record = |path: &[usize], _: &Binding| out.push(took(path));
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

/// The two lists say the same things in the same order, facts being the
/// same when they are spelt the same.
fn same_shapes(one: &[Node], other: &[Node]) -> bool {
    one.len() == other.len() && one.iter().zip(other).all(|(a, b)| a.same_shape(b))
}

/// Every fact of `some` is among `all`, as many times as it is in `some`,
/// facts being the same when they are spelt the same.
fn within(some: &[Node], all: &[Node]) -> bool {
    let mut left: FxIndexMap<ByShape, usize> = FxIndexMap::default();
    for f in all {
        *left.entry(f.by_shape()).or_default() += 1;
    }
    some.iter().all(|f| match left.get_mut(&f.by_shape()) {
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
            let them = if missing.len() == 1 { "it" } else { "them" };
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} cites {}, which asks for {}, and what it cites does not supply {them}",
                    step.number,
                    step.just.cited_item().unwrap_or_default(),
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
        // A claim that is what the item concludes, where only a hypothesis
        // is not supplied, is said once, by `check_hypotheses`, which names
        // the hypothesis.
        let found =
            |how| searched(step, how, known, library).is_some_and(|r| !r.is_declined());
        let hypotheses_said =
            || found(Search::Alone) && unsupplied(step, known, library).is_some();
        if !found(Search::Takes) && !hypotheses_said() {
            // A claim that is the conclusion with an identity element dropped
            // from something not said to be a number is told that, and not
            // that it is something else.
            let unsaid = identities_unsaid(
                &groups,
                &parts.claims,
                &parts.facts,
                &parts.seed,
                library,
            );
            // A claim the item concludes from a "there is" whose witness
            // nothing named puts in its set is told which membership.
            let witnesses = || {
                witnesses_unsaid(
                    &groups,
                    &parts.claims,
                    &parts.facts,
                    &parts.seed,
                    library,
                )
            };
            let said = match unsaid.first() {
                Some(left) => format!(
                    "step {} drops an identity element from what {head} concludes, and nothing says {} is a number; a requires line says it",
                    step.number,
                    known.print(left)
                ),
                None => match witnesses().first() {
                    Some(member) => format!(
                        "step {} reads what {head} concludes from a \"there is\", and nothing it names says {}",
                        step.number,
                        known.print(member)
                    ),
                    None => format!(
                        "step {} claims something that {head} does not conclude",
                        step.number
                    ),
                },
            };
            report.say(&thm.path, just.line, said);
        }
    }
}

/// A theorem stated over a sequence it defines by recursion speaks of that
/// sequence, and a step citing it speaks of its own sequence of the name,
/// as the build reads it (`Elaborator::in_its_names`). The citation holds
/// only where the two are one recursion: the same names in the same order,
/// each with the same value at 0 and the same rule at k + 1, once the
/// letters the citation fills are put in and the index is read as the
/// citing define's. Otherwise what the theorem says is about another
/// sequence.
pub fn check_recursions_cited(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        let mut citations: Vec<(usize, String, Option<Cited>)> = Vec::new();
        if let Some(named) = step.just.cited_item() {
            citations.push((step.just.line, named, cited(step, library, known)));
        }
        for req in &step.requires {
            if let Some((named, _)) = req.cited_item() {
                let read = cited_requires(step, req, library, known);
                citations.push((req.line, named, read));
            }
        }
        // A citation no group reads is `check_conclusion`'s and
        // `check_requires`'s to report.
        for (line, named, read) in citations {
            let Some(read) = read else {
                continue;
            };
            let (Some(Item::Theorem(other)), Some(sorts)) =
                (library.item(&read.item), library.proved_sorts(&read.item))
            else {
                continue;
            };
            for (theirs_line, theirs) in other.stated_recursions() {
                let theirs_at = (theirs_line, &theirs);
                if let Some(why) = recursion_differs(
                    thm,
                    other,
                    sorts,
                    theirs_at,
                    &read.binding,
                    known,
                ) {
                    report.say(
                        &thm.path,
                        line,
                        format!(
                            "step {} cites {named}, which is stated over {}, defined by recursion there; {why}",
                            step.number,
                            theirs.names.join(", ")
                        ),
                    );
                }
            }
        }
    }
}

/// How the citing proof's sequences differ from those `theirs`, a define by
/// recursion of the theorem `other` on its line `theirs_line`, read with
/// `sorts`, gives: in the names, or in the first value or rule that is not
/// the same once `binding` is put in and the index renamed. None where they
/// are one recursion.
fn recursion_differs(
    thm: &Theorem,
    other: &Theorem,
    sorts: &crate::formula::Sorts,
    (theirs_line, theirs): (usize, &crate::corpus::Recursion),
    binding: &Binding,
    known: &Known,
) -> Option<String> {
    let ours = thm
        .defines
        .iter()
        .find_map(|d| match define_parts(&d.text) {
            Built(DefineParts::Recursion(r)) if r.names.contains(&theirs.names[0]) => {
                Some((d, r))
            }
            _ => None,
        });
    let Some((define, ours)) = ours else {
        return Some(format!(
            "this proof defines no {} by recursion",
            theirs.names[0]
        ));
    };
    let label = &define.label;
    if ours.names != theirs.names {
        return Some(format!(
            "{label} here gives {}, and the theorem's define gives {}",
            ours.names.join(", "),
            theirs.names.join(", ")
        ));
    }
    let g = known.env.g;
    let mut theirs_local = sorts.clone();
    theirs_local.insert(theirs.index.clone(), Sort::of("number"));
    let mut ours_local = known.sorts.clone();
    ours_local.insert(ours.index.clone(), Sort::of("number"));
    let mut put = binding.clone();
    put.insert(
        Symbol::of(&theirs.index),
        Node::name(Sort::of("number"), &ours.index),
    );
    for (rules_theirs, rules_ours, at) in [
        (&theirs.start, &ours.start, None),
        (&theirs.step, &ours.step, Some(&ours.index)),
    ] {
        for name in &ours.names {
            let (Some(a), Some(b)) = (rules_theirs.get(name), rules_ours.get(name))
            else {
                continue;
            };
            // A rule that does not read is `check_recursions`'s to report, in
            // the theorem that writes it.
            let read = |rule: Written, local: &crate::formula::Sorts| {
                rule.formula().and_then(|s| s.read(g, local))
            };
            let (Ok(a_tree), Ok(b_tree)) = (
                read(a.written(&other.path, theirs_line), &theirs_local),
                read(b.written(&thm.path, define.line), &ours_local),
            ) else {
                continue;
            };
            let a_tree = substitute_apart(&a_tree, &put, known.ctx);
            // The rules as written, not as alike: a sequence by recursion is
            // the term its rules build, and F(k) + 1 + 0 builds another term
            // than F(k) + 1, which the kernel will not fit to it.
            let as_written = |t: &Node| standard(t, known.ctx);
            if !as_written(&a_tree).same_shape(&as_written(&b_tree)) {
                let place = match at {
                    None => format!("{name}(0)"),
                    Some(k) => format!("{name}({k} + 1)"),
                };
                return Some(format!(
                    "there {place} is {}, and {label} here says it is {}",
                    known.print(&a_tree),
                    str::trim(b.text())
                ));
            }
        }
    }
    None
}

/// A definition folded from what its "there is" says of a witness is about
/// one letter, its subject, and with no pair for it the subject is the
/// proof's letter of the same name (`SYNTAX.md`, "No pair says what goes
/// without saying"): `mun:odd, from H3`, where odd is about n and the proof
/// has an N and no n, writes `n := N`. A definition is folded so where its
/// right side is a "there is", the claim is not one, and no line the step
/// names is one, as the elaborator reads it too (`Elaborator::reading`,
/// `subject_given`).
pub fn check_subjects(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    let shape = super::record::CheckedTheorem::of(thm);
    for step in &thm.steps {
        let just = &step.just;
        if !just.head.is_item() || just.head.is(Method::Obtain) {
            continue;
        }
        let name = just.item(&just.head.to_string());
        let Some(Item::Record(record)) = library.item(&name) else {
            continue;
        };
        if !record.kind.unfolds() {
            continue;
        }
        let Some(whole) = library
            .groups(&name)
            .and_then(|groups| groups.first().and_then(|g| g.gives.first().cloned()))
        else {
            continue;
        };
        let [left, right] = whole.children.as_slice() else {
            continue;
        };
        if !library.bicond.contains(&whole.notation())
            || !library.exists.contains(&right.notation())
        {
            continue;
        }
        let parts = known.parts(step, library);
        let refs: Vec<&str> = just.refs.iter().map(String::as_str).collect();
        let cites_one = known
            .lines_say(step, &refs, library)
            .iter()
            .any(|n| library.exists.contains(&n.notation()));
        let claims_one = parts
            .claims
            .iter()
            .any(|n| library.exists.contains(&n.notation()));
        if cites_one || claims_one || parts.claims.is_empty() {
            continue;
        }
        let subject = left.leftmost();
        let letter = subject.text;
        if !subject.is_name() || just.values.names().any(|n| n == letter) {
            continue;
        }
        // The proof's letter of the same name is one in scope at the step,
        // which is the letter the build gives the subject.
        let in_scope = letters_in_scope(thm, &shape, step, known);
        if !in_scope.contains(letter.as_str()) {
            report.say(
                &thm.path,
                just.line,
                format!(
                    "{} is about {letter}, and the step gives {letter} no value and the proof has no {letter}; write it, as {letter} := t",
                    just.head
                ),
            );
        }
    }
}

/// A `join` claims the sentences of the lines it cites put together and
/// infers nothing (`SYNTAX.md`): each sentence of its claim is one a cited
/// line says, and each cited line says one of them. They are compared as
/// formulas (`Known::alike`), and the claim may group them otherwise.
pub fn check_joins(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        if !step.just.head.is(Method::Join) {
            continue;
        }
        // Putting lines together asks nothing of them, so no requires line
        // under a join is used.
        if let Some(first) = step.requires.first() {
            report.say(
                &thm.path,
                first.line,
                format!(
                    "step {} is a join, which asks nothing of the lines it puts together, and carries a requires line",
                    step.number
                ),
            );
        }
        let Some(claim) = known.whole_as_written(&step.claim) else {
            continue;
        };
        let claimed = conjuncts(&claim, library);
        // A reference to nothing is `check_references`'s to report.
        let scope = known.scope(step);
        let mut cited: Vec<(&String, Vec<Node>)> = Vec::new();
        for r in &step.just.refs {
            let Some(said) = scope.get(r).and_then(|s| known.stated_as_written(s))
            else {
                continue;
            };
            cited.push((r, conjuncts(&said, library)));
        }
        if cited.len() != step.just.refs.len() {
            continue;
        }
        let said = |n: &Node| {
            cited
                .iter()
                .any(|(_, parts)| parts.iter().any(|p| known.alike(p, n)))
        };
        if let Some(extra) = claimed.iter().find(|n| !said(n)) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} joins {} and claims {}, which no line it joins says",
                    step.number,
                    step.just.refs.join(", "),
                    known.print(extra)
                ),
            );
            continue;
        }
        for (r, parts) in &cited {
            if !parts
                .iter()
                .any(|p| claimed.iter().any(|n| known.alike(p, n)))
            {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} joins {r}, and claims nothing it says",
                        step.number
                    ),
                );
            }
        }
    }
}

/// An item's `let f : D → E` filled by a function no `let` types, `let F be
/// a function on A`, asks that type of the citation as a hypothesis, which
/// a line the step names or a requires line says (`SYNTAX.md`, a cited item
/// whose let a citation fills with a function that declares no type). A
/// function the proof defines is `check_surplus`'s and the define's to
/// read.
pub fn check_function_types(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let defines: BTreeSet<String> =
        defined_functions(thm.defines.iter().chain(&scopes[thm.scope].defines))
            .into_iter()
            .map(|f| f.name)
            .collect();
    for step in &thm.steps {
        let Some(item) = step.just.cited_item() else {
            continue;
        };
        if library.groups(&step.just.item(&item)).is_none() {
            continue;
        }
        let asks = family_asks(step, known, library);
        let parts = known.parts(step, library);
        for t in &asks.types {
            let function = &t.asked.children[0];
            if !function.is_name() || defines.contains(function.text.as_str()) {
                continue;
            }
            // A function the citation leaves the item's own letter is not
            // one of the page's.
            if !t.filled {
                continue;
            }
            if parts.facts.iter().any(|f| t.stated_by(f, known)) {
                continue;
            }
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} cites {item}, which asks {}, and no line the step names gives {} a type; cite the line stating it, or say it in a requires line",
                    step.number,
                    known.print(&t.asked),
                    known.print(function)
                ),
            );
        }
        let what = format!("step {}", step.number);
        terms_unsaid(report, thm, step, step.just.line, &what, library, known);
    }
    for step in &thm.steps {
        for req in &step.requires {
            let Some(as_step) = requires_read_as_step(step, req) else {
                continue;
            };
            let named = as_step.just.cited_item().map(|c| as_step.just.item(&c));
            if !named.is_some_and(|n| library.groups(&n).is_some()) {
                continue;
            }
            let what =
                format!("the requires line {} of step {}", req.fact, step.number);
            terms_unsaid(report, thm, &as_step, req.line, &what, library, known);
        }
    }
}

/// A sum item's function hypothesis, `t : {a, …, b} → ℝ`, where the
/// citation makes t a term that is no number by what the page says once
/// (`AskedType::needs_saying`), asks a line the citation names to say it at
/// every point: a divisor's `≠ 0` is written, a sum's term's too
/// (`SYNTAX.md`).
fn terms_unsaid(
    report: &mut Report,
    thm: &Theorem,
    step: &Step,
    line: usize,
    what: &str,
    library: &Library,
    known: &Known,
) {
    let Some(item) = step.just.cited_item() else {
        return;
    };
    let asks = family_asks(step, known, library);
    let parts = known.parts(step, library);
    for t in &asks.types {
        let Some((letter, term)) = t.pointwise() else {
            continue;
        };
        let [_, domain, codomain] = t.asked.children.as_slice() else {
            continue;
        };
        // A term dividing by the type's letter is said at every point by a
        // line; one holding a sum whose term divides by that sum's index is
        // a number where `membership` would build it, the sum's term said
        // at every point by a line the citation names.
        let needs_saying = t.needs_saying(&asks.letters);
        let inner = !t.inner_sums(&asks.letters).is_empty();
        let untyped = applies_untyped(term, thm, &parts.facts, known);
        if !needs_saying && !inner && !untyped {
            continue;
        }
        if parts
            .facts
            .iter()
            .any(|f| t.said_pointwise(f, known, &asks.ctx))
        {
            continue;
        }
        if !needs_saying && term_built(t, step, &parts.facts, known, library) {
            continue;
        }
        report.say(
            &thm.path,
            line,
            format!(
                "{what} cites {item}, which asks that every term {} is in {}, and it is no number by what the page says once; cite a line saying for all {letter} ∈ {}, {} ∈ {}",
                known.print(term),
                known.print(codomain),
                known.print(domain),
                known.print(term),
                known.print(codomain),
            ),
        );
    }
}

/// Whether `term` applies a sequence a define by recursion of the proof
/// gives, and no fact among `facts` gives its type. Nothing says what such
/// a sequence's values are, so F(j)² is no number by what the page says
/// once, as F(j) is not (`check_defined_types`). A function defined by a
/// rule is a number where its rule is, as the build reads it
/// (`Elaborator::map_into`).
fn applies_untyped(term: &Node, thm: &Theorem, facts: &[Node], known: &Known) -> bool {
    let defines = thm
        .defines
        .iter()
        .chain(&known.env.scopes[thm.scope].defines);
    let sequences: Vec<String> = defined_functions(defines)
        .into_iter()
        .filter(|d| d.recursive)
        .map(|d| d.name)
        .collect();
    term.walk().iter().any(|node| {
        let (APPLICATION, [f, _]) = (node.notation(), node.children.as_slice()) else {
            return false;
        };
        sequences.contains(&f.text.to_string())
            && !facts.iter().any(|fact| {
                TYPING.contains(&fact.notation())
                    && fact.children.first().is_some_and(|g| g.text == f.text)
            })
    })
}

/// Whether the term a function hypothesis `t : D → E` asks at every point
/// of D is in E as `membership` builds it (`methods::membership::holds`),
/// from the facts a citation is given, its letter at a point of D.
fn term_built(
    asked: &AskedType,
    step: &Step,
    facts: &[Node],
    known: &Known,
    library: &Library,
) -> bool {
    let (Some((letter, term)), [_, domain, codomain]) =
        (asked.pointwise(), asked.asked.children.as_slice())
    else {
        return false;
    };
    let Some(system) = (codomain.notation() == NUMBER_SYSTEMS)
        .then(|| System::of_sign(&codomain.text))
        .flatten()
    else {
        return false;
    };
    let mut letters = super::library::introduced(known, step);
    let mut ranged = IndexMap::new();
    match (domain.notation(), domain.children.as_slice()) {
        (NUMBER_SYSTEMS, _) => {
            if let Some(s) = System::of_sign(&domain.text) {
                letters.insert(letter.to_string(), s);
            }
        }
        (INTEGER_RANGE, [start, end]) => {
            if let Some(s) = range_system(domain) {
                letters.insert(letter.to_string(), s);
            }
            ranged.insert(
                letter.to_string(),
                crate::methods::membership::Range {
                    start: start.clone(),
                    end: end.clone(),
                },
            );
        }
        _ => return false,
    }
    let mut typed = typed_in_scope(known, step);
    typed.extend(
        facts
            .iter()
            .filter(|f| f.notation() == FUNCTION_TYPE)
            .cloned(),
    );
    let given = crate::methods::membership::Facts {
        facts,
        letters,
        ranged,
        typed: &typed,
        in_sums: &typed,
        targets: &library.targets,
        ctx: known.ctx,
    };
    crate::methods::membership::holds(term, system, &given)
}

/// A `substitute` claims the line it puts its equation into with one side
/// put for the other at some of the places it stands, or with no line to
/// put it into, `t = t′` where t′ is t so rewritten (`SYNTAX.md`). A line
/// of several sentences offers the whole and each of its parts, as the
/// elaborator offers them.
pub fn check_substitutes(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        // A justification matching no production has no reading, and
        // `check_justification_form` says so; what the substitution makes
        // is asked only of one that reads.
        if !step.just.head.is(Method::Substitute) || step.just.unproduced.is_some() {
            continue;
        }
        let equation = step
            .just
            .equation
            .as_ref()
            .and_then(|e| known.whole_as_written(e));
        let (Some(equation), Some(claim)) =
            (equation, known.whole_as_written(&step.claim))
        else {
            continue;
        };
        let [left, right] = equation.children.as_slice() else {
            continue;
        };
        // The equation is part of the line it is taken from (`SYNTAX.md`,
        // substitute), as that line writes it or turned, and of a define of
        // a name the name and what it names. A reference to nothing is
        // `check_references`'s to report.
        let defined = |r: &str| thm.defines.iter().any(|d| d.label == r);
        // An equation worked out where it stands, `(arithmetic)`, is a fact
        // of numerals `arithmetic` decides (`METHODS.md`, arithmetic).
        if let (Some(Source::Arithmetic), Some(written)) =
            (&step.just.source, &step.just.equation)
        {
            let worked =
                super::formulas::arithmetic_worked(written, known, &library.targets);
            if let super::formulas::Worked::Fails(why) = worked {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} takes {} from arithmetic, which {why}",
                        step.number,
                        known.print(&equation)
                    ),
                );
                continue;
            }
        }
        let source = step.just.source.as_ref().map(|s| s.named().to_string());
        if let Some(source) = source {
            // A define of a name says its equation, as a link citing it
            // reads it; a define of a function is the elaborator's.
            let said = if defined(&source) {
                super::formulas::define_equation(thm, step, &source, known)
            } else {
                let scope = known.scope(step);
                scope.get(&source).and_then(|s| known.stated_as_written(s))
            };
            if let Some(said) = said {
                let turned = equation.with_children(vec![right.clone(), left.clone()]);
                let mut parts = vec![said.clone()];
                parts.extend(supplies(&said, library));
                let there = parts
                    .iter()
                    .any(|p| known.alike(p, &equation) || known.alike(p, &turned));
                if !there {
                    report.say(
                        &thm.path,
                        step.just.line,
                        format!(
                            "step {} takes {} from {source}, which does not say it",
                            step.number,
                            known.print(&equation)
                        ),
                    );
                    continue;
                }
            }
        }
        // What the equation is put into, and what that must make: the line
        // named, or one side of the claim, which is t = t′ either way round.
        let into = step.just.into.as_ref().map(|p| p.named().to_string());
        let ways: Vec<(Vec<Node>, Node)> = match into {
            Some(into) => {
                // A define states no sentence for the equation to be put
                // into: the step that wants it written out writes it and
                // cites the define.
                if defined(&into) {
                    report.say(
                        &thm.path,
                        step.just.line,
                        format!(
                            "step {} puts its equation into {into}, which is a define and no line; a step citing {into} writes the line it gives",
                            step.number
                        ),
                    );
                    continue;
                }
                // A reference to nothing is `check_references`'s to report.
                let scope = known.scope(step);
                let Some(said) =
                    scope.get(&into).and_then(|s| known.stated_as_written(s))
                else {
                    continue;
                };
                let mut starts = vec![said.clone()];
                starts.extend(conjuncts(&said, library));
                vec![(starts, claim.clone())]
            }
            None => match claim.children.as_slice() {
                [t, rewritten] if known.ctx.equations.contains(&claim.notation()) => {
                    vec![
                        (vec![t.clone()], rewritten.clone()),
                        (vec![rewritten.clone()], t.clone()),
                    ]
                }
                _ => Vec::new(),
            },
        };
        let found = ways.iter().find(|(starts, aim)| {
            starts
                .iter()
                .any(|start| known.substituted(start, aim, left, right))
        });
        let made = found.is_some();
        if let Some((starts, aim)) = found {
            // An identity element the putting makes and the claim leaves out
            // is dropped from a number, which a line says where the page
            // does not say it once.
            let facts = known.parts(step, library).facts.clone();
            let unsaid = substitution_unsaid(starts, aim, left, right, &facts, library);
            if let Some(left) = unsaid.first() {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} drops an identity element from what the substitution makes, and nothing says {} is a number; a requires line says it",
                        step.number,
                        known.print(left)
                    ),
                );
            }
        }
        if !made {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} claims {}, which putting one side of {} for the other does not make",
                    step.number,
                    known.print(&claim),
                    known.print(&equation)
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
        let Some(item) = just.cited_item() else {
            continue;
        };
        if !just.head.is(Method::Obtain) {
            continue;
        }
        let Some(groups) = library.groups(&just.item(&item)) else {
            continue;
        };
        let parts = known.parts(step, library);
        // A hypothesis nothing supplies is `check_hypotheses`'s to name; the
        // way to the "there is" fails for it, and saying so again would
        // point at the line the step does cite.
        if !obtains(&groups, &parts.facts, &parts.seed, library)
            && unsupplied(step, known, library).is_none()
        {
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

/// What an obtain claims is the "there is" it obtains from, with its letters
/// the names obtained: a membership for each name, then the body
/// (`SYNTAX.md`). The "there is" is the line the step names, or what the
/// item it cites gives there. A definition that unfolds gives the existence
/// the step claims, which the elaborator reaches from the claim. The claim's
/// first sentences are the memberships, one for each name: one written
/// `x ∈ S` is compared with the "there is"'s, and one a notation spells its
/// own way (`f : X → Y`, `C ⊆ A`) is the elaborator's to read. The sentences
/// after them are the body, compared with its parts in any order. Each is
/// compared as one formula (`Known::alike`).
pub fn check_obtained_claims(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        let just = &step.just;
        if !just.head.is(Method::Obtain) {
            continue;
        }
        if just.obtained.is_empty() {
            continue;
        }
        let names: Vec<&str> = just.obtained.iter().map(String::as_str).collect();
        let existence = match just.cited_item() {
            None => {
                let Some(stated) = just
                    .refs
                    .first()
                    .and_then(|r| known.scope(step).get(r).cloned())
                else {
                    continue;
                };
                let defined = known.citing_step(step);
                let said = known.said_parts(&stated, Some(&defined));
                // A line of several sentences gives its one "there is",
                // as the build takes it; with none or several the line
                // states no one existence to obtain from.
                if let [one] = said.as_slice() {
                    one.clone()
                } else if said.iter().any(Option::is_none) {
                    continue; // `check_formulas` says a sentence does not read
                } else {
                    let existences: Vec<&Node> = said
                        .iter()
                        .flatten()
                        .filter(|s| library.ctx.existences.contains(&s.notation()))
                        .collect();
                    match existences.as_slice() {
                        [one] => Some((*one).clone()),
                        none_or_more => {
                            let says = if none_or_more.is_empty() {
                                "says no \"there is\""
                            } else {
                                "says more than one \"there is\"; obtain from a line that says one"
                            };
                            report.say(
                                &thm.path,
                                just.line,
                                format!(
                                    "step {} obtains {} from a line, which {says}",
                                    step.number,
                                    names.join(", ")
                                ),
                            );
                            continue;
                        }
                    }
                }
            }
            Some(item) => {
                let name = just.item(&item);
                let Some(groups) = library.groups(&name) else {
                    continue;
                };
                // A definition unfolded is its right side at the step's own
                // values: from `n is even ↔ there is k ∈ ℤ with n = 2k`,
                // `mun:even n := P` obtains a k with P = 2k.
                if library.item(&name).is_some_and(|i| i.unfolds()) {
                    let Some(read) = searched(step, Search::Obtains, known, library)
                    else {
                        continue;
                    };
                    let Built(taken) = &*read else {
                        continue;
                    };
                    let seed = &taken.binding;
                    groups
                        .iter()
                        .flat_map(|g| &g.gives)
                        .filter(|g| {
                            g.notation() == BICONDITIONAL && g.children.len() == 2
                        })
                        .map(|g| filled(&g.children[1], seed, &library.ctx))
                        .find(|right| exhibited(right, library).is_some())
                } else {
                    let Some(read) = searched(step, Search::Obtains, known, library)
                    else {
                        continue;
                    };
                    let Built(taken) = &*read else {
                        continue; // `check_obtained` reports it
                    };
                    groups[taken.group]
                        .gives
                        .iter()
                        .map(|g| filled(g, &taken.binding, &library.ctx))
                        .find(|g| exhibited(g, library).is_some())
                }
            }
        };
        let Some(existence) = existence else {
            continue;
        };
        // The letters in the order the "there is" binds them, each the name
        // obtained in its place.
        let mut order: Vec<(&Node, &Node)> = Vec::new();
        let mut body = &existence;
        while order.len() < names.len() {
            let Some(last) = body.children.last() else {
                break;
            };
            let kids = &body.children;
            match body.notation() {
                THERE_IS if kids.len() == 3 => order.push((&kids[0], &kids[1])),
                _ => break,
            }
            body = last;
        }
        if order.len() != names.len() {
            // A line or an item that says no "there is" at all where one is
            // left to take has nothing to obtain; another spelling of one, a
            // part or a function, is the elaborator's to read.
            if !library.ctx.existences.contains(&body.notation()) {
                let from = just.cited_item().unwrap_or_else(|| "a line".to_string());
                report.say(
                    &thm.path,
                    just.line,
                    format!(
                        "step {} obtains {} from {from}, which says no \"there is\" of as many",
                        step.number,
                        names.join(", ")
                    ),
                );
            }
            continue;
        }
        let mut put = Binding::new();
        for ((letter, _), name) in order.iter().zip(&names) {
            if letter.text != *name {
                let written = Written::new(*name, &thm.path, just.line);
                let Some(named) = written
                    .formula()
                    .ok()
                    .and_then(|s| known.read_as_written(&s))
                else {
                    continue;
                };
                put.insert(letter.text, named);
            }
        }
        let Some(said) = step
            .claim
            .sentences()
            .iter()
            .map(|s| known.read(step, s))
            .collect::<Option<Vec<Node>>>()
        else {
            continue; // `check_formulas` says it does not read
        };
        // A membership written `x ∈ S` is the one the "there is" gives, and
        // `X ⊆ A` is `X ∈ 𝒫A` written the other way; one its notation spells
        // otherwise, `f : X → Y`, is the elaborator's to read.
        for ((letter, domain), claimed) in order.iter().zip(&said) {
            let member = match (claimed.notation(), domain.notation()) {
                (SUBSET, POWERSET) if domain.children.len() == 1 => {
                    bound_in(Bound::Part, letter, &domain.children[0], library.env.g)
                }
                _ => bound_in(Bound::Member, letter, domain, library.env.g),
            };
            let member = substitute_apart(&member, &put, &library.ctx);
            if claimed.notation() == member.notation() && !known.alike(claimed, &member)
            {
                report.say(
                    &thm.path,
                    step.line,
                    format!(
                        "step {} claims {}, and what it obtains says {}",
                        step.number,
                        known.print(claimed),
                        known.print(&member)
                    ),
                );
            }
        }
        let owes: Vec<Node> = conjuncts(body, library)
            .iter()
            .map(|w| substitute_apart(w, &put, &library.ctx))
            .collect();
        let claimed: Vec<Node> = said
            .iter()
            .skip(names.len())
            .flat_map(|c| conjuncts(c, library))
            .collect();
        let mut left: Vec<&Node> = owes.iter().collect();
        let all =
            claimed
                .iter()
                .all(|c| match left.iter().position(|o| known.alike(c, o)) {
                    Some(at) => {
                        left.remove(at);
                        true
                    }
                    None => false,
                });
        if !all || !left.is_empty() {
            let says: Vec<String> = owes.iter().map(|o| known.print(o)).collect();
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {} claims other than what it obtains, which says {}",
                    step.number,
                    says.join(". ")
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
        for found in unconcluded(step, known, library) {
            let said = match &found.missing {
                Some(missing) => format!(
                    "the requires line of step {} cites {}, which asks for {}, and what it cites does not supply {}",
                    step.number,
                    found.item,
                    missing.join("; "),
                    if missing.len() == 1 { "it" } else { "them" }
                ),
                None => format!(
                    "the requires line of step {} needs something that {} does not conclude",
                    step.number, found.item
                ),
            };
            report.say(&thm.path, found.line, said);
        }
    }
}

/// A let saying what kind of number its name is gives the reason on the
/// line under it, and the reason shows the term the let names is one, as a
/// requires line's reason shows its fact: it is read as a requires line of
/// the step below the let, whose scope the let stands in (`SYNTAX.md`,
/// naming a thing).
pub fn check_kinds(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for d in &thm.defines {
        let kinded = match d.kinded(&thm.path, &known.env.g.members) {
            Ok(Some(kinded)) => kinded,
            Ok(None) => continue,
            Err(problem) => {
                report.problems.push(problem);
                continue;
            }
        };
        let Some(after) = thm.step_after(d.line) else {
            report.say(
                &thm.path,
                d.line,
                format!(
                    "let {} stands below every step, where no step uses it",
                    d.label
                ),
            );
            continue;
        };
        let under = Step {
            requires: vec![kinded.shown.clone()],
            ..after.clone()
        };
        for found in unconcluded(&under, known, library) {
            let said = match &found.missing {
                Some(missing) => format!(
                    "the reason under let {} cites {}, which asks for {}, and what it cites does not supply {}",
                    d.label,
                    found.item,
                    missing.join("; "),
                    if missing.len() == 1 { "it" } else { "them" }
                ),
                None => format!(
                    "the reason under let {} needs {}, which {} does not conclude",
                    d.label, kinded.shown.fact, found.item
                ),
            };
            report.say(&thm.path, found.line, said);
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
/// `requires sin(∠PQR) ≠ 0: inequalities` below it. An equation names both
/// its sides, so `requires deg(u) = |S|` is asked for by `requires deg(u) ∈
/// ℤ: membership` below it. The term may reach the line below through a line
/// it cites or another requires line above it, as `requires deg(x) ∈ ℕ₀:
/// membership, from 2` rests on `requires |S| ∈ ℕ₀` where line 2 says deg(x)
/// = |S|. Such a line is asked for as surely as an item's hypothesis is
/// (`SYNTAX.md`: a requires line rests on the lines above it).
fn built_on(req: &crate::corpus::Requires, step: &Step, known: &Known) -> bool {
    const ASKING: [&str; 3] = ["membership", "inequalities", "algebra"];
    let Some(said) = known.whole(step, &req.fact) else {
        return false;
    };
    // t ∈ X names t: a method asks it of its atoms. t ≠ 0, read as not
    // t = 0, names t, which `membership` and `algebra` ask of a divisor, and
    // says it written either way round, 0 ≠ t as well; `inequalities` takes
    // two terms differing only from a line it cites, not from one above
    // (`METHODS.md`). t < u names both sides, and only `inequalities` reads
    // an order. t = u names both sides too, and a line below may say of one
    // what it says of the other, so there a term the line below holds whole
    // is one it rests on.
    let (held, asking, whole): (Vec<&Node>, &[&str], bool) = match said.notation() {
        MEMBERSHIP if said.children.len() == 2 => {
            (vec![&said.children[0]], &ASKING, false)
        }
        LOGICAL_NOT
            if said.children.len() == 1
                && said.children[0].notation() == EQUALITY
                && said.children[0].children.len() == 2 =>
        {
            (
                said.children[0]
                    .children
                    .iter()
                    .filter(|c| c.notation() != NUMERAL)
                    .collect(),
                &["membership", "algebra"],
                false,
            )
        }
        ORDER if said.children.len() == 2 => (
            said.children
                .iter()
                .filter(|c| c.notation() != NUMERAL)
                .collect(),
            &["inequalities"],
            false,
        ),
        EQUALITY if said.children.len() == 2 => (
            said.children
                .iter()
                .filter(|c| c.notation() != NUMERAL)
                .collect(),
            &ASKING,
            true,
        ),
        _ => return false,
    };
    let atoms: Vec<&Node> = held;
    let holds_atom = |n: &Node| {
        atoms
            .iter()
            .any(|atom| n.walk().iter().any(|part| part.same_shape(atom)))
    };
    let scope = known.scope(step);
    step.requires
        .iter()
        .skip_while(|r| r.line != req.line)
        .skip(1)
        .filter(|r| {
            let how = str::trim(&r.how);
            // A manipulation, `weakening, from 8`, is a row of `inequalities`
            // and asks its atoms real as that method does.
            let manipulated = asking.contains(&"inequalities")
                && matches!(&r.by, Ok(by) if matches!(by.head, Head::Manipulation(_)));
            manipulated
                || asking
                    .iter()
                    .any(|m| how == *m || how.starts_with(&format!("{m},")))
        })
        .filter_map(|r| known.whole(step, &r.fact).map(|n| (r, n)))
        .any(|(r, n)| {
            let held = if n.notation() == MEMBERSHIP && n.children.len() == 2 {
                &n.children[0]
            } else {
                &n
            };
            let written = atoms.iter().any(|atom| {
                (whole || !held.same_shape(atom))
                    && held.walk().iter().any(|part| part.same_shape(atom))
            });
            // Or it holds the term once the defines it cites are written
            // out: `U(0) ∈ ℝ: membership, from D6` divides by 10^0, which
            // D6's U(k) = (N(k) + 1)/10^k makes of U(0).
            let lower = known.citing_item(r.lines(), None);
            let defined_out = r
                .fact
                .sentences()
                .iter()
                .filter_map(|s| known.read_citing(s, &lower))
                .any(|line| holds_atom(&line));
            // A line the lower one cites, or another requires line above it,
            // carries the term to it: `deg(x) ∈ ℕ₀: membership, from 2` rests
            // on `|S| ∈ ℕ₀` above it where line 2 says deg(x) = |S|, and so
            // does `deg(x) ∈ ℤ: membership` under `requires deg(x) = |S|`.
            let defined = known.citing_step(step);
            let cited = r
                .lines()
                .iter()
                .filter_map(|c| scope.get(c))
                .flat_map(|written| known.supplied(written, &defined))
                .any(|line| holds_atom(&line));
            let above = step
                .requires
                .iter()
                .take_while(|o| o.line != r.line)
                .filter(|o| o.line != req.line)
                .flat_map(|o| known.said(step, &o.fact))
                .any(|line| holds_atom(&line));
            written || defined_out || cited || above
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
    types: Vec<AskedType>,
    /// The number systems the page says once its letters are in at the
    /// step, which say whether a term's divisor is a positive integer.
    letters: Introduced,
    /// Which notations bind, so that a value is compared up to the letters
    /// it binds.
    ctx: Context,
}

/// A function type an item asks of a citation, under what the citation
/// writes for its letters.
struct AskedType {
    /// `F : D → E` for the item's `let f : D → E` at `f := F`.
    asked: Node,
    /// The item's letters among its sets that the citation leaves unfilled,
    /// which the line stating the type fills: D and E above.
    open: BTreeSet<String>,
    /// Whether the citation says what the item's function stands for, so
    /// that the type is asked of one of the page's functions.
    filled: bool,
    /// What the match of the citation makes the function where it is a
    /// rule, a sum's summand `k ↦ 1/T(k)` for the item's t.
    rule: Option<Node>,
}

impl AskedType {
    /// The term a sum's function hypothesis asks at every point and the
    /// letter it is asked at: `1/T(k)` and k, of `t : {1, …, n} → ℝ` where
    /// the citation makes t the summand. None for a type the citation
    /// fills with a named function.
    fn pointwise(&self) -> Option<(&str, &Node)> {
        let f = self.asked.children.first()?;
        let f = if f.notation() == PROPERTY_OF {
            f
        } else {
            self.rule.as_ref()?
        };
        Some((f.text.as_str(), f.children.first()?))
    }

    /// Whether the term the type asks at every point must be said there: it
    /// divides by something holding the type's letter that the page does
    /// not say once is a positive integer, `letters` its letters, as 1/T(k)
    /// and 1/(k(k + 1)/2) do. A divisor's `≠ 0` is written there
    /// (`SYNTAX.md`), and no line outside the sum can speak of its letter,
    /// so the term is said at every point by a line the citation names.
    fn needs_saying(&self, letters: &Introduced) -> bool {
        let (Some((letter, term)), Some(domain)) =
            (self.pointwise(), self.asked.children.get(1))
        else {
            return false;
        };
        let inside = match domain.notation() {
            INTEGER_RANGE => range_system(domain),
            NUMBER_SYSTEMS => System::of_sign(&domain.text),
            _ => None,
        };
        let mut letters = letters.clone();
        if let Some(inside) = inside {
            letters.insert(letter.to_string(), inside);
        }
        crate::methods::membership::divides_by(term, letter, &letters)
    }

    /// The sums inside the term the type asks at every point whose own
    /// term divides by their index as `needs_saying` reads it, `letters`
    /// the page's: Σ(k = 1 to n) 1/T(k) inside `x : ℕ → ℝ` at x := n ↦
    /// Σ(k = 1 to n) 1/T(k).
    fn inner_sums(&self, letters: &Introduced) -> Vec<Node> {
        let Some((_, term)) = self.pointwise() else {
            return Vec::new();
        };
        term.walk()
            .into_iter()
            .filter(|part| {
                crate::methods::membership::Summed::of(part).is_some_and(|s| {
                    let mut letters = letters.clone();
                    if let Some(inside) = index_system(s.start) {
                        letters.insert(s.index.to_string(), inside);
                    }
                    crate::methods::membership::divides_by(s.body, s.index, &letters)
                })
            })
            .collect()
    }

    /// Whether `node` says an inner sum's term at every point of its range
    /// (`inner_sums`), in the type's codomain.
    fn says_inner_term(
        &self,
        node: &Node,
        letters: &Introduced,
        ctx: &Context,
    ) -> bool {
        let Some(codomain) = self.asked.children.get(2) else {
            return false;
        };
        let Some(system) = System::of_sign(&codomain.text) else {
            return false;
        };
        self.inner_sums(letters).iter().any(|sum| {
            crate::methods::membership::Summed::of(sum).is_some_and(|s| {
                crate::methods::membership::said_pointwise(node, &s, system, ctx)
            })
        })
    }

    /// Whether `node` says, at every point of a set holding the type's
    /// domain, that the term is in the type's codomain: `for all k ∈ ℕ,
    /// 1/T(k) ∈ ℝ` for `t : {1, …, n} → ℝ`, ℕ holding every member of a
    /// range from 1.
    fn said_pointwise(&self, node: &Node, known: &Known, ctx: &Context) -> bool {
        let (Some((letter, term)), [_, domain, codomain]) =
            (self.pointwise(), self.asked.children.as_slice())
        else {
            return false;
        };
        let [bound, set, body] = node.children.as_slice() else {
            return false;
        };
        if node.notation() != FOR_ALL || body.notation() != MEMBERSHIP {
            return false;
        }
        let [value, into] = body.children.as_slice() else {
            return false;
        };
        let at = Binding::from([(Symbol::of(letter), bound.clone())]);
        let holds = known.alike(set, domain)
            || (set.notation() == NUMBER_SYSTEMS
                && range_system(domain).is_some_and(|inside| {
                    System::of_sign(&set.text).is_some_and(|s| inside.within(s))
                }));
        let lands = known.alike(into, codomain)
            || (into.notation() == NUMBER_SYSTEMS
                && codomain.notation() == NUMBER_SYSTEMS
                && System::maybe_within(
                    System::of_sign(&into.text),
                    System::of_sign(&codomain.text),
                ));
        holds && lands && known.alike(&substitute_apart(term, &at, ctx), value)
    }

    /// Whether `node` states this type, an open letter standing for any set.
    fn stated_by(&self, node: &Node, known: &Known) -> bool {
        let (asked, said) = (&self.asked, node);
        asked.notation() == said.notation()
            && asked.children.len() == said.children.len()
            && asked.children.iter().zip(&said.children).all(|(a, s)| {
                (a.is_name() && self.open.contains(a.text.as_str()))
                    || known.alike(a, s)
            })
    }
}

fn family_asks(step: &Step, known: &Known, library: &Library) -> FamilyAsks {
    let just = &step.just;
    let groups = just
        .cited_item()
        .and_then(|item| library.groups(&just.item(&item)))
        .expect("a step whose item was just read");
    let parts = known.parts(step, library);
    let mut held = BTreeSet::new();
    let mut values = Vec::new();
    // The item's function types under what the citation writes for its
    // letters, `f := F`, where that makes the function one no `let` types:
    // one the proof defines, its rule, where the step cites the define and
    // the rule is written out, or its name, where it does not; or one a let
    // says only is a function on a set. A type a let declares is not asked
    // for (`GRAMMAR.md`, the function's type is a declaration). What the
    // step claims is no guide to the letters: an `obtain` claims the
    // witness, not the item's conclusion.
    let declared: BTreeSet<Symbol> = typed_in_scope(known, step)
        .iter()
        .map(|t| t.children[0].text)
        .collect();
    // What the citation writes, and what the match of the item against the
    // claim and the cited lines fixes beside it: `g is continuous on D`
    // claimed by `def:continuous-on` makes the item's f the page's g
    // whether or not the step writes f := g.
    let mut fixed = parts.seed.clone();
    // What the match makes a function the item applies, a rule: a sum's
    // summand, which a type asks of every point (`AskedType::pointwise`).
    let mut rules = Binding::new();
    // An obtain claims the witness, and is read for what it obtains through.
    let read = searched(step, search_of(step), known, library);
    if let Some(Built(taken)) = read.as_deref() {
        for (name, value) in &taken.binding {
            if value.notation() == PROPERTY_OF {
                rules.insert(*name, value.clone());
            } else if !fixed.contains_key(name) {
                fixed.insert(*name, value.clone());
            }
        }
    }
    let types = library
        .function_types(&just.item(&just.cited_item().expect("a cited item")))
        .iter()
        .map(|t| AskedType {
            asked: substitute_apart(t, &fixed, &library.ctx),
            open: t.children[1..]
                .iter()
                .filter(|s| s.is_name() && !fixed.contains_key(&s.text))
                .map(|s| s.text.to_string())
                .collect(),
            filled: fixed.contains_key(&t.children[0].text),
            rule: rules.get(t.children[0].text.as_str()).cloned(),
        })
        // A letter the citation leaves unfilled is the item's own, whatever
        // the page calls by the same name: sum-termwise's u, read as a rule,
        // is no page's `let u : ℕ → ℝ`.
        .filter(|t| {
            let function = &t.asked.children[0];
            function.notation() == PROPERTY_OF
                || (function.is_name()
                    && (!t.filled || !declared.contains(&function.text)))
        })
        .collect();
    for group in groups.iter() {
        let (want, gives) = (&group.wants, &group.gives);
        let mut trees = gives.clone();
        trees.extend(want.iter().map(|(_, t)| t.clone()));
        let mut sites = Sites::new();
        for t in &trees {
            binding_sites(t, &library.ctx, &[], &mut sites);
        }
        let variables = group.letters(&trees);
        // What a function letter stands for is read where the item applies
        // it: its conclusions against what the step claims, and its
        // hypotheses against what the step cites, since an `obtain` claims
        // the witness and says nothing of the function.
        let mut pairs: Vec<(Node, &Node)> = Vec::new();
        for concl in gives {
            for reading in readings(concl, library) {
                for cand in conjuncts(&reading.claimed, library) {
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
                if value.notation() == PROPERTY_OF {
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
        letters: super::library::introduced(known, step),
        ctx: library.ctx.clone(),
    }
}

impl FamilyAsks {
    /// Whether `node`, a line the citation names, states what a function
    /// hypothesis asks: its type, or a sum's term at every point.
    fn states(&self, node: &Node, known: &Known) -> bool {
        self.types.iter().any(|t| {
            t.stated_by(node, known)
                || t.said_pointwise(node, known, &self.ctx)
                || t.says_inner_term(node, &self.letters, &self.ctx)
        })
    }

    /// Whether one requires line's fact is a membership the item's function
    /// hypotheses ask for, read as the checks of its step read it.
    fn asks(&self, step: &Step, fact: &Written, known: &Known) -> bool {
        let Some(node) = known.whole(step, fact) else {
            return false;
        };
        if node.notation() == FUNCTION_TYPE {
            return self.types.iter().any(|t| t.stated_by(&node, known));
        }
        if self
            .types
            .iter()
            .any(|t| t.said_pointwise(&node, known, &self.ctx))
        {
            return true;
        }
        // Or the hypothesis said whole, of every value the function takes:
        // `x : ℕ → ℝ` where x(n) is a partial sum of the reciprocals of T
        // asks that every partial sum be real. T is a defined function and
        // no name a membership could be asked of, so what is compared is the
        // value itself, read at the name the line binds.
        if node.notation() == FOR_ALL && node.children.len() == 3 {
            let (bound, body) = (&node.children[0], &node.children[2]);
            if body.notation() != MEMBERSHIP
                || body.children[1].notation() != NUMBER_SYSTEMS
            {
                return false;
            }
            // A function the proof defines, whose type the item asks over a
            // set the define may not name: the type said of every point,
            // `for all i ∈ {1, …, k + 1}, t(i) ∈ ℝ`, which holds where
            // `t : {1, …, k + 1} → ℝ` does not, t's domain being the
            // define's.
            let (set, value) = (&node.children[1], &body.children[0]);
            let pointwise = value.notation() == APPLICATION
                && value.children.len() == 2
                && known.alike(&value.children[1], bound)
                && self.types.iter().any(|t| {
                    let [f, d, e] = t.asked.children.as_slice() else {
                        return false;
                    };
                    f.is_name()
                        && known.alike(f, &value.children[0])
                        && ((d.is_name() && t.open.contains(d.text.as_str()))
                            || known.alike(d, set))
                        && known.alike(e, &body.children[1])
                });
            if pointwise {
                return true;
            }
            // The line's letter is put into the value apart from what the
            // value binds, and the two compared up to their bound letters:
            // `Σ(n = 1 to k) 1/T(n)` at k is `Σ(a = 1 to k) 1/T(a)`.
            let none = IndexMap::new();
            return self.values.iter().any(|v| {
                let mut at = Binding::new();
                at.insert(v.text, bound.clone());
                let value = substitute_apart(&v.children[0], &at, &self.ctx);
                alike(&value, &body.children[0], &self.ctx, &none, &none)
            });
        }
        node.notation() == MEMBERSHIP
            && node.children[1].notation() == NUMBER_SYSTEMS
            && !node.children[0].names().is_empty()
            && node.children[0].names().is_subset(&self.held)
    }
}

/// What the functions a proof defines ask of what the step's claim applies
/// them to: `define M(X) := …, for X ∈ 𝒫A` and a claim holding M(X) ask
/// `X ∈ 𝒫A`, since M(X) is M's rule only there. The checker reads the name
/// as its rule without asking, and the kernel does not (`SYNTAX.md`: a
/// define may name a function).
fn domains_asked(
    thm: &Theorem,
    step: &Step,
    scopes: &[FileScope],
    known: &Known,
) -> FxIndexSet<ByShape> {
    let functions =
        defined_functions(thm.defines.iter().chain(&scopes[thm.scope].defines));
    let Some(claim) = known.whole_as_written(&step.claim) else {
        return FxIndexSet::default(); // `check_formulas` says it does not read
    };
    applied(&functions, &claim, false, known)
        .into_iter()
        .flat_map(|a| a.says)
        .map(ByShape)
        .collect()
}

/// A defined function by name, with the domain of each argument in order.
#[derive(Clone)]
pub(super) struct Defined {
    name: String,
    label: String,
    /// Each argument's domain, as the define writes it.
    domains: Vec<Written>,
    /// Defined by recursion, whose domain is its step clause's index: the
    /// clause at k + 1 holds for k in the domain, and the base clause for
    /// its one argument.
    recursive: bool,
}

/// A cited item's `let f : D → E` asks nothing of a function the citing
/// proof introduces with a type, `let g : X → Y`, whose type is its sort,
/// as a letter's membership is (`READERS.md`, a function's type). Of any
/// other f it asks a fact, which the step names, in its `from` or by a
/// requires line (R1): a function the proof defines has no type until a
/// line says one, `G : [a, b] → ℝ` by `function-into`.
pub fn check_defined_types(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let defines: Vec<&crate::corpus::DefineLine> = thm
        .defines
        .iter()
        .chain(&scopes[thm.scope].defines)
        .collect();
    let mut defined: IndexMap<String, Option<DefinedRule>> =
        defined_functions(defines.iter().copied())
            .into_iter()
            .map(|d| (d.name, None))
            .collect();
    for d in &defines {
        // A define that does not read is said where it is written, by
        // `check_formulas` of a theorem's and `check_file_defines` of a
        // file's.
        if let Ok(Some(rule)) = DefinedRule::of(d, known) {
            defined.insert(rule.name.clone(), Some(rule));
        }
    }
    for step in &thm.steps {
        let letters = super::library::introduced(known, step);
        let at = DefinedAt {
            defined: &defined,
            letters: &letters,
        };
        if let Some(item) = step.just.cited_item() {
            let name = step.just.item(&item);
            let parts = known.parts(step, library);
            for said in defined_types_unsaid(&parts, &name, &at, library, known) {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} cites {item}, which asks for {}, and nothing it cites or requires says it; a requires line says it, as {}, from a line saying the values on a set holding {}",
                        step.number,
                        known.print(&said),
                        values_everywhere(&said, known),
                        said.children.get(1).map(|d| known.print(d)).unwrap_or_default()
                    ),
                );
            }
        }
        for req in &step.requires {
            let Some((item, _)) = req.cited_item() else {
                continue;
            };
            let name = step.just.item(&item);
            let Some(parts) = requires_parts(step, req, &[], known, library) else {
                continue;
            };
            for said in defined_types_unsaid(&parts, &name, &at, library, known) {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of step {} cites {item}, which asks for {}, and nothing it cites says it",
                        step.number,
                        known.print(&said)
                    ),
                );
            }
        }
    }
}

/// A function a define gives of one argument, read: `t(j) = j + 1, for j ∈
/// ℕ` is t with letter j, domain ℕ and rule j + 1.
struct DefinedRule {
    name: String,
    letter: String,
    domain: Node,
    rule: Node,
}

impl DefinedRule {
    /// The define's function of one argument, read with its argument's
    /// sort; None for a define of anything else. A part that does not read
    /// is a defect.
    fn of(
        d: &crate::corpus::DefineLine,
        known: &Known,
    ) -> crate::Checked<Option<DefinedRule>> {
        let Built(DefineParts::One(one)) = define_parts(&d.text) else {
            return Ok(None);
        };
        let [param] = one.params.as_slice() else {
            return Ok(None);
        };
        let local = crate::sorts::define_sorts(&one, &known.sorts);
        let rule = d.rule(&one.body).formula()?.read(known.env.g, &local)?;
        let domain = known.parse(&d.domain(param).formula()?)?;
        Ok(Some(DefinedRule {
            name: one.name.clone(),
            letter: param.name.clone(),
            domain,
            rule,
        }))
    }

    /// Whether the type `f : D → E` asked of this function is said once
    /// (`SYNTAX.md`, "A define with a parameter also states what its
    /// function is on"): its domain holds D, and its rule at a point of D
    /// is in E by what the page says once, with `letters` the step's.
    fn typed_once(
        &self,
        domain: &Node,
        codomain: &Node,
        letters: &Introduced,
        known: &Known,
    ) -> bool {
        let Some(into) = (codomain.notation() == NUMBER_SYSTEMS)
            .then(|| System::of_sign(&codomain.text))
            .flatten()
        else {
            return false;
        };
        let inside = match domain.notation() {
            INTEGER_RANGE => range_system(domain),
            NUMBER_SYSTEMS => System::of_sign(&domain.text),
            _ => None,
        };
        let holds = known.alike(&self.domain, domain)
            || (self.domain.notation() == NUMBER_SYSTEMS
                && System::of_sign(&self.domain.text)
                    .zip(inside)
                    .is_some_and(|(own, asked)| asked.within(own)));
        let Some(inside) = inside.filter(|_| holds) else {
            return false;
        };
        let mut letters = letters.clone();
        letters.insert(self.letter.clone(), inside);
        crate::citing::within(
            &self.rule,
            into,
            &letters,
            &|d| crate::citing::nonzero_said_once(d, &letters),
            &|_, _| false,
        )
    }
}

/// The functions the theorem and its file define, each with its rule where
/// it is of one argument, and the letters the page says once at a step.
struct DefinedAt<'a> {
    defined: &'a IndexMap<String, Option<DefinedRule>>,
    letters: &'a Introduced,
}

/// Each type the item named asks of a function `at` defines
/// (`check_defined_types`), at what its letters stand for, that no fact of
/// `parts` says and that is not said once of its rule.
fn defined_types_unsaid(
    parts: &Parts,
    name: &str,
    at: &DefinedAt,
    library: &Library,
    known: &Known,
) -> Vec<Node> {
    let typed = library.function_types(name);
    if typed.is_empty() {
        return Vec::new();
    }
    let stands = stood_for(parts, name, library);
    let mut out = Vec::new();
    for t in &typed {
        let Some(v) = t.children.first().and_then(|f| stands.get(&f.text)) else {
            continue;
        };
        if !v.is_name() {
            continue;
        }
        let Some(rule) = at.defined.get(v.text.as_str()) else {
            continue;
        };
        let typed = substitute_apart(t, &stands, &library.ctx);
        let said = parts.facts.iter().any(|fact| {
            TYPING.contains(&fact.notation())
                && fact.children.first().is_some_and(|g| g.text == v.text)
        });
        let once = rule.as_ref().is_some_and(|r| {
            r.typed_once(&typed.children[1], &typed.children[2], at.letters, known)
        });
        if !said && !once && !values_said(&typed, &parts.facts, library) {
            out.push(typed);
        }
    }
    out
}

/// A function's type `f : D → E` said of its values, `for all k ∈ D, f(k)
/// ∈ E`, as a message writes it (`values_said`).
fn values_everywhere(typed: &Node, known: &Known) -> String {
    match typed.children.as_slice() {
        [f, domain, codomain] => format!(
            "for all k ∈ {}, {}(k) ∈ {}",
            known.print(domain),
            known.print(f),
            known.print(codomain)
        ),
        _ => known.print(typed),
    }
}

/// Whether a fact says a function's type `f : D → E` of its values, `for
/// all k ∈ D, f(k) ∈ E`, as a step citing a sum's item over a range writes
/// it of a defined function (`tests/elaborator/a-for-all-over-a-range`).
fn values_said(typed: &Node, facts: &[Node], library: &Library) -> bool {
    let [f, domain, codomain] = typed.children.as_slice() else {
        return false;
    };
    let g = library.env.g;
    let k = Node::name(domain.sort.held().unwrap_or_else(Sort::none), "k");
    let Some(value) = page::made_as(g, "_(_)", vec![f.clone(), k.clone()]) else {
        return false;
    };
    let member = bound_in(Bound::Member, &value, codomain, library.env.g);
    let Some(every) =
        page::made_as(g, "for all _ ∈ _, _", vec![k, domain.clone(), member])
    else {
        return false;
    };
    let none = IndexMap::new();
    facts
        .iter()
        .any(|fact| crate::matching::alike(fact, &every, &library.ctx, &none, &none))
}

/// The functions some defines name.
pub(super) fn defined_functions<'d>(
    defines: impl Iterator<Item = &'d crate::corpus::DefineLine>,
) -> Vec<Defined> {
    let mut functions = Vec::new();
    for d in defines {
        match define_parts(&d.text) {
            Built(DefineParts::Recursion(r)) => {
                for name in &r.names {
                    functions.push(Defined {
                        name: name.clone(),
                        label: d.label.clone(),
                        domains: vec![d.formula(&r.domain)],
                        recursive: true,
                    });
                }
            }
            Built(DefineParts::One(one)) if !one.params.is_empty() => {
                functions.push(Defined {
                    name: one.name.clone(),
                    label: d.label.clone(),
                    domains: one.params.iter().map(|p| d.domain(p)).collect(),
                    recursive: false,
                });
            }
            _ => {}
        }
    }
    functions
}

/// Whether a requires line claims `f is a function on A`, the one fact a
/// define it names gives without a line saying it.
fn claims_function_on(req: &Requires, known: &Known) -> bool {
    known
        .whole_as_written(&req.fact)
        .is_some_and(|claim| claim.notation() == FUNCTION_ON)
}

/// Why a requires line `f is a function on A`, from a define it names, is
/// not given by it: a define gives a function on the one domain it writes,
/// as a map of one argument, which the build proves it on (`define_on`), so
/// f is to be such a function of a define the line names and A that domain.
/// None where it is, and for a line claiming anything else.
fn function_on_unshown(
    thm: &Theorem,
    req: &Requires,
    known: &Known,
    scopes: &[FileScope],
) -> Option<String> {
    let claim = known.whole_as_written(&req.fact)?;
    let (FUNCTION_ON, [function, on]) = (claim.notation(), claim.children.as_slice())
    else {
        return None;
    };
    let named = req.lines();
    let defines = thm.defines.iter().chain(&scopes[thm.scope].defines);
    let given = defined_functions(defines)
        .into_iter()
        .find(|f| f.name == function.text && named.contains(&f.label));
    let Some(given) = given else {
        return Some(format!(
            "no define it names gives {}",
            known.print(function)
        ));
    };
    // A sequence by recursion is a map of one argument, its index, on the
    // set the index runs over.
    let [domain] = given.domains.as_slice() else {
        return Some(format!(
            "{} gives {} of {} arguments, and a function on one domain is a map of one argument",
            given.label,
            known.print(function),
            given.domains.len()
        ));
    };
    let domain = known.read_as_written(&domain.formula().ok()?)?;
    (!known.alike(&domain, on)).then(|| {
        format!(
            "{} gives {} on {}",
            given.label,
            known.print(function),
            known.print(&domain)
        )
    })
}

/// One argument a defined function is applied to in a claim, and the
/// facts any one of which says it is in the function's domain, as written.
pub(super) struct Applied {
    label: String,
    arg: Node,
    says: Vec<Node>,
}

/// The applications whose domains a step citing a define asks. A step whose
/// reason is the define itself evaluates the function where an application
/// is a whole side of its equation, as `s(s(a)) = (s(a) + 1) mod 10`
/// evaluates s at s(a); an application elsewhere in the claim, the s(a)
/// inside, is a term carried as it stands and asks nothing. Any other step
/// citing the define asks of every application in its claim.
fn evaluated(
    step: &Step,
    used: &[Defined],
    known: &Known,
    library: &Library,
) -> Vec<Applied> {
    let direct = step.just.head == crate::corpus::Head::Define
        && used
            .iter()
            .any(|f| step.just.defined.as_deref() == Some(f.label.as_str()));
    let Some(claim) = known.whole_as_written(&step.claim) else {
        return Vec::new(); // `check_formulas` says it does not read
    };
    if !(direct
        && claim.children.len() == 2
        && library.ctx.equations.contains(&claim.notation()))
    {
        return applied(used, &claim, false, known);
    }
    claim
        .children
        .iter()
        .flat_map(|side| applied(used, side, true, known))
        .collect()
}

/// Every application of the functions in `claim`, a tree as written, each
/// argument with what says it is in its domain; where `leading`, only an
/// application the claim begins with, as `s(s(a))` begins with the outer s
/// and `f(x) + 1` with f(x).
fn applied(
    functions: &[Defined],
    claim: &Node,
    leading: bool,
    known: &Known,
) -> Vec<Applied> {
    let nodes: Vec<Node> = if leading {
        let mut spine = vec![claim.clone()];
        while let Some(first) = spine.last().and_then(|n| n.children.first().cloned()) {
            spine.push(first);
        }
        spine
    } else {
        claim.walk()
    };
    // A domain that does not read is `check_formulas`'s to report.
    let read = |w: &Written| known.read_as_written(&w.formula().ok()?);
    let (g, sorts) = (known.env.g, &known.sorts);
    let mut out = Vec::new();
    for Defined {
        name,
        label,
        domains,
        recursive,
    } in functions
    {
        for node in &nodes {
            let [function, args @ ..] = node.children.as_slice() else {
                continue;
            };
            if !matches!(node.notation(), APPLICATION | APPLICATION_TO_TWO)
                || !function.is_name()
                || &function.text != name
                || args.len() != domains.len()
            {
                continue;
            }
            for (arg, domain) in args.iter().zip(domains) {
                // A recursion's step at m asks m; any other argument is its
                // value at 0, which asks nothing.
                let member = if *recursive {
                    match (arg.spelling(), arg.children.as_slice()) {
                        (PLUS, [index, one])
                            if one.notation() == NUMERAL && one.text == "1" =>
                        {
                            index.clone()
                        }
                        _ => continue,
                    }
                } else {
                    arg.clone()
                };
                let Some(set) = read(domain) else {
                    continue;
                };
                let within = |form: &'static str, set: &Node| {
                    page::filled(form, g, sorts, &[("x", &member), ("S", set)]).ok()
                };
                let mut says: Vec<Node> = within("x ∈ S", &set).into_iter().collect();
                // A power set's member is a part, which the page may say with
                // ⊆: `for X ⊆ A` asks C ⊆ A of M(C).
                if let (POWERSET, [inner]) = (set.notation(), set.children.as_slice()) {
                    says.extend(within("x ⊆ S", inner));
                }
                if says.is_empty() {
                    continue;
                }
                out.push(Applied {
                    label: label.clone(),
                    arg: arg.clone(),
                    says,
                });
            }
        }
    }
    out
}

/// The indices of the sums anywhere in a formula, by the places the
/// notation database declares each sum holds its index in.
fn sum_indices(node: &Node, ctx: &Context, out: &mut BTreeSet<String>) {
    if ctx.sums.contains(&node.notation()) {
        let (held, _) = ctx.held_body(node.notation());
        for at in held {
            if let Some(letter) = node.children.get(at).filter(|c| c.is_name()) {
                out.insert(letter.text.to_string());
            }
        }
    }
    for child in &node.children {
        sum_indices(child, ctx, out);
    }
}

/// A define used for what it is has each argument in its domain.
///
/// `define S(m) := Σ(j = 1 to m) j, for m ∈ ℕ` gives S(k + 1) its rule only
/// where k + 1 ∈ ℕ, so a step citing the define, itself or on a calculation
/// line, writes a requires line for each argument's domain it does not
/// otherwise have (`SYNTAX.md`). A built-up argument is no exception, as an
/// item's hypothesis of one is not: what is cited or required says it, with
/// what each of those implies.
pub fn check_define_domains(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let functions =
        defined_functions(thm.defines.iter().chain(&scopes[thm.scope].defines));
    if functions.is_empty() {
        return;
    }
    let needs = |asked: &Applied| known.print(&asked.says[0]);
    for step in &thm.steps {
        for asked in domains_unsaid(step, &functions, known, library) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} cites {} at {}, so it needs {}, and nothing it cites or requires says it",
                    step.number,
                    asked.label,
                    known.print(&asked.arg),
                    needs(&asked)
                ),
            );
        }
        // A requires line whose reason is a method or an item is the step it
        // would be, and cites a define as a step does.
        for req in &step.requires {
            let Some(as_step) = requires_read_as_step(step, req) else {
                continue;
            };
            for asked in domains_unsaid(&as_step, &functions, known, library) {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line {} of step {} cites {} at {}, so it needs {}, and nothing it cites or the requires lines above it say it",
                        str::trim(req.fact.text()),
                        step.number,
                        asked.label,
                        known.print(&asked.arg),
                        needs(&asked)
                    ),
                );
            }
        }
    }
}

/// A requires line whose reason is a method or an item, read as the step it
/// would be (`requires_as_step`), with the requires lines above it as its
/// own, since it rests on them (`ELABORATION.md`, R2); None for a reason
/// that is only `from`, which is read from the lines it names, and for one
/// the skeleton reader could not cut, which `check_reason` reports.
fn requires_read_as_step(step: &Step, req: &Requires) -> Option<Step> {
    let Ok(by) = &req.by else {
        return None;
    };
    if !matches!(by.head, Head::Method(_) | Head::Item { .. }) {
        return None;
    }
    let mut as_step = reason_as_step(step, req, by);
    as_step.requires = step.requires_above(req.line).cloned().collect();
    Some(as_step)
}

/// What a step citing a define, itself or on a calculation line, needs of
/// each argument's domain and nothing it cites or requires says, with what
/// each of those implies: each application once.
pub(super) fn domains_unsaid(
    step: &Step,
    functions: &[Defined],
    known: &Known,
    library: &Library,
) -> Vec<Applied> {
    let links = chain_links(&step.just, &known.thm.path);
    let mut cited: BTreeSet<String> = step.just.refs.iter().cloned().collect();
    cited.extend(
        links
            .iter()
            .filter_map(|l| l.line.cited())
            .map(String::from),
    );
    let used: Vec<Defined> = functions
        .iter()
        .filter(|f| cited.contains(&f.label))
        .cloned()
        .collect();
    if used.is_empty() {
        return Vec::new();
    }
    let parts = known.parts(step, library);
    let mut facts = parts.facts.clone();
    let from_links: Vec<String> = links
        .iter()
        .filter_map(|l| l.line.cited())
        .map(String::from)
        .collect();
    let refs: Vec<&str> = from_links.iter().map(String::as_str).collect();
    facts.extend(known.lines_say(step, &refs, library));
    // A claim said of every member puts the member in its domain.
    facts.extend(
        parts
            .claims
            .iter()
            .filter_map(|c| claimed_member(c, library.env.g))
            .map(|(member, _)| member),
    );
    let facts =
        finished(facts, Vec::new(), Binding::new(), library, &known.sorts).facts;
    // A sum's index is in the range the sum runs over, and what holds it is a
    // term of the sum, whose values are a family's (`family_asks`).
    let mut indices: BTreeSet<String> = BTreeSet::new();
    for claim in &parts.claims {
        sum_indices(claim, &library.ctx, &mut indices);
    }
    let shapes: FxIndexSet<ByShape> = facts.iter().map(Node::by_shape).collect();
    let defined = known.citing_step(step);
    let mut seen: FxIndexSet<ByShape> = FxIndexSet::default();
    let mut out = Vec::new();
    for asked in evaluated(step, &used, known, library) {
        if !asked.arg.names().is_disjoint(&indices) {
            continue;
        }
        // Compared with the facts as they are read, defines written out.
        let said = asked
            .says
            .iter()
            .any(|s| shapes.contains(&known.as_cited(s, &defined).by_shape()));
        if said || !seen.insert(asked.says[0].by_shape()) {
            continue;
        }
        out.push(asked);
    }
    out
}

/// An exhibit's lines say every part of its body at one value.
///
/// `exhibit, from L` claims a bare "there is", and the lines L state its
/// body with some value in place of the bound letter (`SYNTAX.md`). Each
/// part is stated, the value's membership of the domain among them: "there
/// is d ∈ ℤ with d > 1, d divides p" at d = 2 asks 2 ∈ ℤ and 2 > 1 as
/// surely as 2 divides p, since `READERS.md` writes a dull fact wherever
/// what a step rests on demands it, a numeral's included.
pub fn check_exhibited(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in thm.steps.iter().filter(|s| s.just.head.is(Method::Exhibit)) {
        check_exhibit(report, thm, step, library, known);
        check_exhibit_cites_used(report, thm, step, library, known);
    }
}

/// An exhibit uses each line it cites (`DATABASE.md`, a named thing doing
/// no work is an error): with the line taken away, what the exhibit needs
/// of its value is left unsaid. An exhibit that does not hold with all its
/// lines is reported by `check_exhibit`, and asked nothing here.
fn check_exhibit_cites_used(
    report: &mut Report,
    thm: &Theorem,
    step: &Step,
    library: &Library,
    known: &Known,
) {
    let mut whole = Report::default();
    check_exhibit(&mut whole, thm, step, library, known);
    if !whole.problems.is_empty() {
        return;
    }
    let refs = &step.just.refs;
    let mut seen = BTreeSet::new();
    for r in refs.iter().filter(|r| seen.insert(r.as_str())) {
        let mut lighter = step.clone();
        lighter.just.refs = refs.iter().filter(|x| *x != r).cloned().collect();
        let mut scratch = Report::default();
        check_exhibit(&mut scratch, thm, &lighter, library, known);
        if scratch.problems.is_empty() && !shows_value(step, r, library, known) {
            report.say(
                &thm.path,
                step.just.line,
                format!("step {} cites {r} and uses nothing it says", step.number),
            );
        }
    }
}

/// Whether the line `r` an exhibit cites states a part of its body, short
/// of a letter's membership of its domain, at some value: the line shows
/// the reader the value (`SYNTAX.md`, `exhibit`: "the reader finds the
/// value by comparing"), as `p·q = p·q` shows n := q for "there is n ∈ ℕ
/// with p·q = p·n", though the equation would name its value itself.
fn shows_value(step: &Step, r: &str, library: &Library, known: &Known) -> bool {
    let scope = known.scope(step);
    let Some(written) = scope.get(r) else {
        return false;
    };
    let said = known.supplied(written, &known.citing_step(step));
    let parts = known.parts(step, library);
    parts.claims.iter().any(|claim| {
        let Some(Exhibited { wants, letters }) = exhibited(claim, library) else {
            return false;
        };
        let mut sites = Sites::new();
        for t in &wants {
            binding_sites(t, &library.ctx, &[], &mut sites);
        }
        wants
            .iter()
            .filter(|w| {
                !(w.notation() == MEMBERSHIP
                    && w.children
                        .first()
                        .is_some_and(|t| letters.contains(t.text.as_str())))
            })
            .any(|w| {
                // The line itself says the part at the value, and not only
                // an equation true of itself there, n = n of q = n.
                supply(
                    std::slice::from_ref(w),
                    &said,
                    &Binding::new(),
                    &letters,
                    library,
                    &sites,
                    true,
                )
                .is_some_and(|at| {
                    let there = substitute_apart(w, &at, &library.ctx);
                    said.iter().any(|s| known.alike(s, &there))
                })
            })
    })
}

/// One exhibit's claim, a "there is", each part of it said of one value by
/// what the step cites or requires.
fn check_exhibit(
    report: &mut Report,
    thm: &Theorem,
    step: &Step,
    library: &Library,
    known: &Known,
) {
    let parts = known.parts(step, library);
    let written: Vec<Node> = step
        .claim
        .sentences()
        .iter()
        .filter_map(|s| known.read_as_written(s))
        .collect();
    let facts = exhibit_facts(&parts.facts, library);
    for (claim, as_written) in parts.claims.iter().zip(&written) {
        // An exhibit claims a "there is" and shows a value for it
        // (`SYNTAX.md`, `exhibit`).
        let Some(ex) = exhibited(claim, library) else {
            if library.ctx.existences.contains(&claim.notation()) {
                continue;
            }
            report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} is an exhibit, and {} is no \"there is\" for it to give a value of",
                        step.number,
                        known.print(as_written)
                    ),
                );
            continue;
        };
        if shown_value(&ex, &facts, library, known).is_some() {
            continue;
        }
        let Some(at) = most_said_value(&ex, &facts, library, known) else {
            report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} exhibits a value, and nothing it cites or requires says the claim's body of any one value",
                        step.number
                    ),
                );
            continue;
        };
        let Exhibited { wants, letters } = ex;
        let shown = exhibited(as_written, library)
            .map(|e| e.wants)
            .filter(|w| w.len() == wants.len())
            .unwrap_or_else(|| wants.clone());
        let values: Vec<String> = letters
            .iter()
            .filter_map(|l| {
                at.get(l.as_str())
                    .map(|v| format!("{l} := {}", known.print(v)))
            })
            .collect();
        for (want, show) in wants.iter().zip(&shown) {
            if holds_at(want, &at, &facts, library, known) {
                continue;
            }
            report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} exhibits {}, so it needs {}, and nothing it cites or requires says it",
                        step.number,
                        values.join(", "),
                        known.print(&substitute_apart(show, &at, &library.ctx))
                    ),
                );
        }
    }
}

/// What an exhibit reads its values from: what the step cites and
/// requires, with the parts of each and the types said otherwise.
fn exhibit_facts(cited: &[Node], library: &Library) -> Vec<Node> {
    let mut facts = with_parts(cited, library);
    let typed: Vec<Node> = facts
        .iter()
        .filter_map(|f| type_said_otherwise(f, library))
        .collect();
    facts.extend(typed);
    facts
}

/// Where each property in what an exhibit asks may decide what it stands
/// for (`binding_sites`).
fn exhibit_sites(wants: &[Node], library: &Library) -> Sites {
    let mut sites = Sites::new();
    for t in wants {
        binding_sites(t, &library.ctx, &[], &mut sites);
    }
    sites
}

/// A term equals itself, which no line need write: gH = aH at a = g is
/// stated by nothing and needs nothing.
fn equal_to_itself(w: &Node, known: &Known) -> bool {
    w.notation() == EQUALITY
        && w.children.len() == 2
        && known.alike(&w.children[0], &w.children[1])
}

/// The value an exhibit shows, each letter bound: one under which the facts
/// state every part of what it asks, or every part but the equations, each
/// of which is then a term equal to itself. None where no value is shown,
/// which `check_exhibit` reports.
fn exhibit_value(
    ex: &Exhibited,
    facts: &[Node],
    library: &Library,
    known: &Known,
) -> Option<Binding> {
    let sites = exhibit_sites(&ex.wants, library);
    let stated = |wants: &[Node]| {
        supply(
            wants,
            facts,
            &Binding::new(),
            &ex.letters,
            library,
            &sites,
            true,
        )
    };
    let (equations, rest): (Vec<Node>, Vec<Node>) = ex
        .wants
        .iter()
        .cloned()
        .partition(|w| w.notation() == EQUALITY && w.children.len() == 2);
    stated(&ex.wants).or_else(|| {
        if equations.is_empty() {
            return None;
        }
        stated(&rest).filter(|at| {
            equations
                .iter()
                .all(|e| equal_to_itself(&substitute_apart(e, at, &library.ctx), known))
        })
    })
}

/// Whether a part `w` of what an exhibit asks holds at the value `at`: it is
/// then an equation of a term with itself, or a fact says it, alike but for
/// what goes without saying (`Known::alike`), as x = −(b + T)/3 says
/// x = −(b + 1·T)/3.
fn holds_at(
    w: &Node,
    at: &Binding,
    facts: &[Node],
    library: &Library,
    known: &Known,
) -> bool {
    let w = substitute_apart(w, at, &library.ctx);
    equal_to_itself(&w, known) || facts.iter().any(|f| known.alike(f, &w))
}

/// The value the most parts of what an exhibit asks are said of, each
/// part's own line suggesting one, every letter bound; None where no part
/// suggests one.
fn most_said_value(
    ex: &Exhibited,
    facts: &[Node],
    library: &Library,
    known: &Known,
) -> Option<Binding> {
    let Exhibited { wants, letters } = ex;
    let sites = exhibit_sites(wants, library);
    // A letter's bare membership, n ∈ ℕ, fits every number in ℕ, and
    // a numeral's membership is said once (`said_once`), so the value
    // it suggests is no reading of the claim: what the body says is
    // asked first, and wins where as many parts are said of each.
    let bare = |w: &Node| {
        w.notation() == MEMBERSHIP
            && w.children
                .first()
                .is_some_and(|t| letters.contains(t.text.as_str()))
    };
    let mut best: Option<(usize, Binding)> = None;
    for w in wants
        .iter()
        .filter(|w| !bare(w))
        .chain(wants.iter().filter(|w| bare(w)))
    {
        let Some(at) = supply(
            std::slice::from_ref(w),
            facts,
            &Binding::new(),
            letters,
            library,
            &sites,
            true,
        ) else {
            continue;
        };
        if !letters.iter().all(|l| at.contains_key(l.as_str())) {
            continue;
        }
        let count = wants
            .iter()
            .filter(|w| holds_at(w, &at, facts, library, known))
            .count();
        if best.as_ref().is_none_or(|(most, _)| count > *most) {
            best = Some((count, at));
        }
    }
    best.map(|(_, at)| at)
}

/// The value an exhibit shows, as `check_exhibit` accepts one: the value
/// `exhibit_value` reads, where the facts state each part, and otherwise
/// the value the most parts are said of where every part holds there
/// (`holds_at`). None where the exhibit shows no value.
fn shown_value(
    ex: &Exhibited,
    facts: &[Node],
    library: &Library,
    known: &Known,
) -> Option<Binding> {
    exhibit_value(ex, facts, library, known).or_else(|| {
        most_said_value(ex, facts, library, known).filter(|at| {
            ex.wants
                .iter()
                .all(|w| holds_at(w, at, facts, library, known))
        })
    })
}

/// The values each exhibit step shows, by the line the step is on: for each
/// sentence of its claim, the value each letter of its "there is" stands
/// for, as `check_exhibit` reads it; None for a sentence that is no "there
/// is" the step gives a value of. The build exhibits these values.
pub fn exhibit_values(
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> IndexMap<usize, Vec<Option<Binding>>> {
    thm.steps
        .iter()
        .filter(|s| s.just.head.is(Method::Exhibit))
        .map(|step| {
            let parts = known.parts(step, library);
            let facts = exhibit_facts(&parts.facts, library);
            let values = parts
                .claims
                .iter()
                .map(|claim| {
                    exhibited(claim, library)
                        .and_then(|ex| shown_value(&ex, &facts, library, known))
                })
                .collect();
            (step.line, values)
        })
        .collect()
}

/// What a "there is" asks of the value exhibited for it: each letter in its
/// domain, then each part of the body; and the letters.
struct Exhibited {
    wants: Vec<Node>,
    letters: BTreeSet<String>,
}

fn exhibited(claim: &Node, library: &Library) -> Option<Exhibited> {
    // The letters and their domains, then the body: a "there is" whose body
    // is a "there is" again, as "there are k, m, n ∈ ℕ with …" builds, binds
    // each letter in turn. "There is s ∈ S" binds its letter over nothing,
    // and asks only that the value is in S.
    let mut bound: Vec<(&Node, &Node)> = Vec::new();
    let mut body = Some(claim);
    while let Some(at) = body {
        match (at.notation(), at.children.as_slice()) {
            (THERE_IS, [letter, domain, inner]) => {
                bound.push((letter, domain));
                body = Some(inner);
            }
            (THERE_IS_SOME, [letter, domain]) => {
                bound.push((letter, domain));
                body = None;
            }
            _ => break,
        }
    }
    if bound.is_empty() {
        return None;
    }
    let mut wants: Vec<Node> = bound
        .iter()
        .map(|(letter, domain)| bound_in(Bound::Member, letter, domain, library.env.g))
        .collect();
    if let Some(body) = body {
        wants.extend(conjuncts(body, library));
    }
    let letters = bound.iter().map(|(l, _)| l.text.to_string()).collect();
    Some(Exhibited { wants, letters })
}

/// An instantiation's values are in the domains they are put in.
///
/// `instantiate v := t in line L, from L2`: line L says "for all v ∈ X, B",
/// and L2 supplies t ∈ X (`SYNTAX.md`), or a requires line does. A numeral
/// is no exception: `y := 1` in "for all x, y ∈ ℤ" asks 1 ∈ ℤ, written
/// `requires 1 ∈ ℤ: arithmetic`, as a cited item's hypothesis does.
pub fn check_instantiated(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        if !step.just.head.is(Method::Instantiate) {
            continue;
        }
        let Some(target) = step.just.target.clone() else {
            continue;
        };
        let Some(line) = known.scope(step).get(&target).cloned() else {
            continue;
        };
        let parts = known.parts(step, library);
        // A value that does not read is the elaborator's to report.
        let written: IndexMap<String, Node> = step
            .just
            .values
            .read(known.env.g, &known.sorts)
            .unwrap_or_default()
            .into_iter()
            .map(|v| (v.name, v.value))
            .collect();
        let defined = known.citing_step(step);
        let said = known
            .said_parts(&line, Some(&defined))
            .into_iter()
            .zip(known.said_parts(&line, None));
        // What the values put in the domains need, each found among the
        // step's facts; unjudged where a domain is one `bound_in` does not
        // read, or a membership is missing and reported.
        let mut wants: Vec<Node> = Vec::new();
        let mut judged = true;
        for (read, as_written) in said {
            let (Some(read), Some(as_written)) = (read, as_written) else {
                judged = false;
                continue;
            };
            // A cited line may meet a condition of the line as well, "if ε
            // > 0 then" in "for all ε > 0", which the elaborator judges.
            if read
                .walk()
                .iter()
                .any(|n| matches!(n.notation(), IMPLICATION | CONDITIONAL))
            {
                judged = false;
            }
            let binders = binders_of(&read);
            if !binders
                .iter()
                .any(|b| parts.seed.contains_key(&b.letter.text))
            {
                continue;
            }
            // A domain may name the letters bound before it, and only those.
            // What is compared is read with defined names written out; what
            // a message says is the page's own spelling.
            let mut outer = Binding::new();
            let mut outer_written = Binding::new();
            for (b, w) in binders.iter().zip(binders_of(&as_written)) {
                let Some(value) = parts.seed.get(&b.letter.text) else {
                    continue;
                };
                let domain = substitute_apart(&b.domain, &outer, &library.ctx);
                outer.insert(b.letter.text, value.clone());
                let want = bound_in(b.how, value, &domain, library.env.g);
                let value_written = written
                    .get(b.letter.text.as_str())
                    .cloned()
                    .unwrap_or_else(|| value.clone());
                let domain_written =
                    substitute_apart(&w.domain, &outer_written, &library.ctx);
                outer_written.insert(w.letter.text, value_written.clone());
                if parts.facts.iter().any(|f| known.alike(f, &want)) {
                    wants.push(want);
                    continue;
                }
                judged = false;
                let needed =
                    bound_in(b.how, &value_written, &domain_written, library.env.g);
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} puts {} for {} in line {target}, so it needs {}, and nothing it cites or requires says it",
                        step.number,
                        known.print(&value_written),
                        b.letter.text,
                        known.print(&needed)
                    ),
                );
            }
        }
        // A line the step cites supplies a value's membership of its domain
        // (`SYNTAX.md`, instantiate), so one whose absence leaves every
        // membership supplied supplies none: `instantiate x := x in H2, from
        // K2` where K2 lets x ∈ ℝ, which is said once.
        if !judged || wants.is_empty() {
            continue;
        }
        let defines: BTreeSet<&str> =
            thm.defines.iter().map(|d| d.label.as_str()).collect();
        for r in step
            .just
            .refs
            .iter()
            .filter(|r| **r != target && !defines.contains(r.as_str()))
        {
            let mut lighter = step.clone();
            lighter.just.refs.retain(|x| x != r);
            let left = known.parts(&lighter, library);
            if wants
                .iter()
                .all(|w| left.facts.iter().any(|f| known.alike(f, w)))
            {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} cites {r}, and no value it puts in line {target} needs what it says",
                        step.number
                    ),
                );
            }
        }
    }
}

/// One binder of a "for all": the letter, the domain, and how a value is
/// said to be in it, `x ∈ S`, or `x ⊆ S` for a part.
struct Binder {
    letter: Node,
    domain: Node,
    how: Bound,
}

/// An instantiation claims what its line says at the values it writes
/// (`SYNTAX.md`, instantiate): the "for all" of the line binding the names
/// it gives values, read at those values, and where what that says is an
/// implication, what it concludes, its conditions being the lines the step
/// cites. Compared as one formula (`Known::alike`), a claim of several
/// sentences as their conjunction.
pub fn check_instance_claimed(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        if !step.just.head.is(Method::Instantiate) {
            continue;
        }
        let Some(target) = step.just.target.clone() else {
            continue;
        };
        // A line or claim that does not read is another check's to report.
        let (Some(line), Some(claim)) = (
            known.scope(step).get(&target).cloned(),
            known.whole(step, &step.claim),
        ) else {
            continue;
        };
        let named = known.parts(step, library);
        let seed = &named.seed;
        let defined = known.citing_step(step);
        let parts: Vec<Node> = known
            .said_parts(&line, Some(&defined))
            .into_iter()
            .flatten()
            .flat_map(|said| {
                let mut all = vec![said.clone()];
                all.extend(supplies(&said, library));
                all
            })
            .collect();
        let fits: Vec<Fit> = parts.iter().map(|said| fit_of(said, seed)).collect();
        // The part instantiated is one the values fit: a part they leave
        // values over gives no instance, however its own letters fall.
        let instances: Vec<Node> = parts
            .iter()
            .zip(&fits)
            .filter(|(_, fit)| **fit == Fit::Fits)
            .filter_map(|(said, _)| instance_at(said, seed, library))
            .collect();
        if !fits.contains(&Fit::Fits) {
            let why = if fits.contains(&Fit::Skips) {
                "quantifies a name the step gives no value, before the ones it does"
            } else if fits.contains(&Fit::Over) {
                "quantifies fewer names than the step gives values"
            } else {
                "claims nothing of every such name"
            };
            report.say(
                &thm.path,
                step.just.line,
                format!("step {} instantiates {target}, which {why}", step.number),
            );
            continue;
        }
        if instances.is_empty() {
            continue;
        }
        // The instance reaching the claim, and each condition met on the way
        // among what the step names; one it does not supply is said.
        let reached: Vec<Vec<Node>> = instances
            .iter()
            .filter_map(|i| concludes_claim(i, &claim, known))
            .collect();
        if let Some(conditions) = reached.iter().min_by_key(|c| c.len()) {
            // A condition of several parts is met where each part is.
            let unmet = conditions.iter().find(|c| {
                !conjuncts(c, library)
                    .iter()
                    .all(|part| named.facts.iter().any(|f| known.alike(f, part)))
            });
            if let Some(unmet) = unmet {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "instantiating at that term wants {}, which step {} does not supply",
                        known.print(unmet),
                        step.number
                    ),
                );
            }
            continue;
        }
        // Said as the page writes the claim, not as it is compared.
        let written = known
            .whole_as_written(&step.claim)
            .map_or_else(|| step.claim_text(), |w| known.print(&w));
        report.say(
            &thm.path,
            step.just.line,
            format!(
                "{target} at those terms says {}, and the step claims {written}",
                known.print(&instances[0]),
            ),
        );
    }
}

/// What `said` says at the values `seed` gives the letters it binds, where
/// it is a "for all" binding at least one of them; None otherwise.
/// How an instantiation's values meet a sentence of the line it names
/// (`SYNTAX.md`, `instantiate`): the values are for the sentence's leading
/// "for all" letters, outermost first, each one given.
#[derive(PartialEq)]
enum Fit {
    /// The values are for a run of its leading binders.
    Fits,
    /// A leading binder has no value before one that does.
    Skips,
    /// Values are left when its leading binders end.
    Over,
    /// No leading binder is one the values are for.
    Nothing,
}

/// How `seed`, the step's values by letter, meets the sentence `said`.
fn fit_of(said: &Node, seed: &Binding) -> Fit {
    let mut body = said;
    let mut taken = 0;
    let mut skipped = false;
    loop {
        let (letter, inner) = match (body.notation(), body.children.as_slice()) {
            (FOR_ALL | FOR_ALL_PART, [letter, _, inner]) => (letter, inner),
            (FOR_ALL_SETS, [letter, inner]) => (letter, inner),
            _ => break,
        };
        if seed.contains_key(&letter.text) {
            if skipped {
                return Fit::Skips;
            }
            taken += 1;
        } else if taken > 0 {
            break;
        } else {
            skipped = true;
        }
        body = inner;
    }
    match taken {
        0 => Fit::Nothing,
        n if n < seed.len() => Fit::Over,
        _ => Fit::Fits,
    }
}

fn instance_at(said: &Node, seed: &Binding, library: &Library) -> Option<Node> {
    let mut body = said.clone();
    let mut put = Binding::new();
    loop {
        // "for all x ∈ S, B" and "for all X ⊆ A, B" bind x over a set;
        // "for all sets X, B" binds X over every set.
        let (letter, inner) = match (body.notation(), body.children.as_slice()) {
            (FOR_ALL | FOR_ALL_PART, [letter, _, inner]) => (letter, inner),
            (FOR_ALL_SETS, [letter, inner]) => (letter, inner),
            _ => break,
        };
        let Some(value) = seed.get(&letter.text) else {
            break;
        };
        put.insert(letter.text, value.clone());
        body = inner.clone();
    }
    (!put.is_empty()).then(|| substitute_apart(&body, &put, &library.ctx))
}

/// The conditions an instance asks on its way to the claim: none where it
/// is the claim, and each implication's condition taken off until what is
/// left is; None where it never is.
fn concludes_claim(instance: &Node, claim: &Node, known: &Known) -> Option<Vec<Node>> {
    let mut at = instance.clone();
    let mut asked = Vec::new();
    loop {
        if known.alike(&at, claim) {
            return Some(asked);
        }
        match (at.notation(), at.children.as_slice()) {
            (IMPLICATION | CONDITIONAL, [condition, then]) => {
                asked.push(condition.clone());
                at = then.clone();
            }
            _ => return None,
        }
    }
}

/// The binders a sentence opens with, outermost first.
fn binders_of(node: &Node) -> Vec<Binder> {
    let mut out = Vec::new();
    let mut node = node.clone();
    loop {
        let how = match node.notation() {
            FOR_ALL => Bound::Member,
            FOR_ALL_PART => Bound::Part,
            _ => break,
        };
        if node.children.len() != 3 {
            break;
        }
        out.push(Binder {
            letter: node.children[0].clone(),
            domain: node.children[1].clone(),
            how,
        });
        node = node.children[2].clone();
    }
    out
}

/// A requires line says something the step's other lines do not.
///
/// Every line does work (R3), and a fact the step already has does none:
/// `requires k ∈ ℝ: membership` under `requires k ∈ ℤ` says what k ∈ ℤ says
/// (`READERS.md`, what a membership line says). What the step has without
/// the line is the lines it cites, the requires lines above it, the lines
/// below it whose reason is a bare `from`, and what each of those implies.
/// Any other line below may rest on this one (R2): `2^p − 1 ∈ ℕ:
/// mun:prime-nat` below `2^p − 1 ∈ ℤ` implies it and needs it, where `m ∈
/// ℕ₀: from H3` rests on H3 alone. One line written twice is flagged where
/// it is written the second time. This holds on every step, whatever its
/// reason, so the checker and the elaborator need not each judge it.
///
/// What the step's own citations give is not in hand on a requires line
/// below, which sees only its own reason and the lines above it (R2). So a
/// line whose fact only the step's citations give is flagged only where no
/// line below needs it (`needed_below`), as the elaborator's R3 judges it.
pub fn check_repeated(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        for (i, req) in step.requires.iter().enumerate() {
            let Some(said) = known.whole(step, &req.fact) else {
                continue;
            };
            let mut lighter = step.clone();
            lighter.requires = step
                .requires
                .iter()
                .enumerate()
                .filter(|(j, o)| {
                    *j < i
                        || (*j > i
                            && str::trim(&o.how).starts_with("from ")
                            && !same_fact(known, &o.fact, &req.fact))
                })
                .map(|(_, o)| o.clone())
                .collect();
            let says =
                |parts: &Parts| parts.facts.iter().any(|f| known.alike(f, &said));
            let mut uncited = lighter.clone();
            uncited.just.refs.clear();
            let bounded = bound_below(step, i, &said, known);
            let repeated = (says(&known.parts(&uncited, library)) && !bounded)
                || (says(&known.parts(&lighter, library))
                    && !bounded
                    && !needed_below(step, i, &said, known, library));
            if repeated {
                // A membership the page says once is said where its letters
                // are introduced, and the step's lines may say nothing.
                let why = match membership_said_once(&said, step, known) {
                    Some(named) if named.is_empty() => {
                        "which the page says once".to_string()
                    }
                    Some(named) => format!(
                        "which the page says once, where {} {} introduced",
                        named.join(" and "),
                        if named.len() == 1 { "is" } else { "are" }
                    ),
                    None => "which the step's other lines already say".to_string(),
                };
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of step {} says {}, {why}",
                        step.number,
                        str::trim(req.fact.text())
                    ),
                );
            }
        }
    }
}

/// Whether two requires lines state one fact, compared as formulas
/// (`Known::alike`). One that does not read states nothing another does,
/// and is `check_formulas`'s to report.
fn same_fact(known: &Known, a: &Written, b: &Written) -> bool {
    match (known.whole_as_written(a), known.whole_as_written(b)) {
        (Some(a), Some(b)) => known.alike(&a, &b),
        _ => false,
    }
}

/// A requires line whose reason is only `from` uses each line it names.
///
/// Such a line reads its fact off the lines it names and the requires lines
/// above it (`ELABORATION.md`, R2), so a named line whose absence leaves the
/// fact read off is one it uses nothing of: `requires d(n) ∈ ℤ: from H1, K6`
/// where H1 says d : ℕ → ℤ and K6 lets n ∈ ℕ, which is said once. A fact is
/// read off where the facts say it, or say a function's type and a point of
/// its domain, a membership said once among them. The elaborator judges the
/// same by what the line's proof rests on (`Elaborator::does_work`).
pub fn check_from_lines(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    // The defines a line may name: the theorem's own and its file's.
    let defines: BTreeSet<&str> = thm
        .defines
        .iter()
        .chain(&scopes[thm.scope].defines)
        .map(|d| d.label.as_str())
        .collect();
    // A let's reason is read as a requires line of the step below it.
    let under = super::formulas::reasons_under_lets(thm, known);
    for step in thm.steps.iter().chain(under.iter().map(|u| &u.step)) {
        for req in &step.requires {
            if !str::trim(&req.how).starts_with("from ") {
                continue;
            }
            let read_off = |without: &[&str]| -> bool {
                let Some(parts) = requires_parts(step, req, without, known, library)
                else {
                    return false;
                };
                let mut facts = parts.facts.clone();
                facts.extend(function_values(&parts.facts, library.env, &known.sorts));
                parts
                    .claims
                    .iter()
                    .all(|c| facts.iter().any(|f| known.alike(f, c)))
            };
            // A fact the lines do not give is the line's defect: it claims
            // its lines supply what they do not. They give it where they say
            // it, or as the build proves the line from them alone
            // (`from_lines_give`, `ELABORATION.md`, R2): never from a type
            // in scope the line does not name. A define giving its function
            // on its domain is read apart, by `function_on_unshown`; any
            // other fact a line naming a define claims is read from its
            // lines, as the build reads it.
            let define_gives_function_on =
                req.lines().iter().any(|r| defines.contains(r.as_str()))
                    && claims_function_on(req, known);
            if !read_off(&[]) {
                if define_gives_function_on {
                    if let Some(why) = function_on_unshown(thm, req, known, scopes) {
                        report.say(
                            &thm.path,
                            req.line,
                            format!(
                                "{} does not give {}: {why}",
                                str::trim(&req.how),
                                str::trim(req.fact.text())
                            ),
                        );
                    }
                    continue;
                }
                let supplied =
                    requires_parts(step, req, &[], known, library).map(|parts| {
                        parts.claims.iter().all(|c| {
                            from_lines_give(
                                c,
                                &parts.facts,
                                step,
                                known,
                                library,
                                crate::methods::membership::holds,
                            )
                        })
                    });
                if supplied == Some(false) {
                    report.say(
                        &thm.path,
                        req.line,
                        format!(
                            "{} does not reach {}, which this line claims it supplies",
                            str::trim(&req.how),
                            str::trim(req.fact.text())
                        ),
                    );
                }
                if supplied != Some(true) {
                    continue;
                }
            }
            // Read off, or given as the build proves the line from its lines
            // (`from_lines_give`): d(k) ∈ ℝ from d : ℕ₀ → ℤ at a k said once.
            let gives = |without: &[&str]| -> bool {
                read_off(without)
                    || requires_parts(step, req, without, known, library).is_some_and(
                        |parts| {
                            parts.claims.iter().all(|c| {
                                from_lines_give(
                                    c,
                                    &parts.facts,
                                    step,
                                    known,
                                    library,
                                    crate::methods::membership::read_off,
                                )
                            })
                        },
                    )
            };
            let refs = req.lines();
            let spare: Vec<&str> = refs
                .iter()
                .map(String::as_str)
                .filter(|r| gives(&[r]))
                .collect();
            // Lines each spare alone that the fact needs one of say it twice,
            // which `check_repeated` and the elaborator judge.
            if spare.len() > 1 && !gives(&spare) {
                continue;
            }
            for r in spare {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of step {} cites {r}, and {} needs nothing it says",
                        step.number,
                        str::trim(req.fact.text())
                    ),
                );
            }
        }
    }
}

/// How a membership is decided from facts (`methods::membership`).
type Member = fn(&Node, System, &crate::methods::membership::Facts) -> bool;

/// Whether the facts a bare `from` line reads give `claim` as the build
/// proves it from them (`ELABORATION.md`, R2), beside what they state and
/// supply: a membership the membership decider builds from them, a typed
/// function's value at a point of its domain among them; or an instance of
/// a "for all" among them, at a member the page says once is in its set, or
/// over a set inside its set (`SYNTAX.md`, a line said of every member).
/// Only the facts' own function types are offered, as the line rests on
/// its reason alone. `member` decides a membership: `holds` for whether
/// the lines reach the fact at all, as the build proves it, and `read_off`,
/// the page's rule, for whether a line among them is needed.
fn from_lines_give(
    claim: &Node,
    facts: &[Node],
    step: &Step,
    known: &Known,
    library: &Library,
    member: Member,
) -> bool {
    let letters = super::library::introduced(known, step);
    if let (MEMBERSHIP, [term, set]) = (claim.notation(), claim.children.as_slice()) {
        if let Some(system) = (set.notation() == NUMBER_SYSTEMS)
            .then(|| System::of_sign(&set.text))
            .flatten()
        {
            let typed: Vec<Node> = facts
                .iter()
                .filter(|f| f.notation() == FUNCTION_TYPE)
                .cloned()
                .collect();
            let given = crate::methods::membership::Facts {
                facts,
                letters: letters.clone(),
                ranged: IndexMap::new(),
                typed: &typed,
                in_sums: &[],
                targets: &library.targets,
                ctx: known.ctx,
            };
            if member(term, system, &given) {
                return true;
            }
        }
    }
    facts.iter().any(|f| {
        let (FOR_ALL, [bound, over, body]) = (f.notation(), f.children.as_slice())
        else {
            return false;
        };
        if let (FOR_ALL, [letter, inner, said]) =
            (claim.notation(), claim.children.as_slice())
        {
            let put = Binding::from([(bound.text, letter.clone())]);
            return (known.alike(inner, over)
                || crate::citing::set_within(inner, over))
                && known.alike(&substitute_apart(body, &put, known.ctx), said);
        }
        // At a member: the claim is the body, or one part of it, there.
        let variables = BTreeSet::from([bound.text.to_string()]);
        conjuncts(body, library).iter().any(|part| {
            let Some(fit) = match_tree(
                part,
                claim,
                &Binding::new(),
                &variables,
                &IndexSet::new(),
                known.ctx,
            ) else {
                return false;
            };
            fit.get(&bound.text)
                .is_some_and(|member| member_in(member, over, &letters, step, known))
        })
    })
}

/// Where `fact` is a membership the page says once at `step` (`member_in`),
/// the letters of its term the page introduces, where it says so; None for
/// any other fact.
pub(super) fn membership_said_once(
    fact: &Node,
    step: &Step,
    known: &Known,
) -> Option<Vec<String>> {
    let (MEMBERSHIP, [term, set]) = (fact.notation(), fact.children.as_slice()) else {
        return None;
    };
    let letters = super::library::introduced(known, step);
    member_in(term, set, &letters, step, known).then(|| {
        term.names()
            .into_iter()
            .filter(|n| letters.contains_key(n.as_str()))
            .collect()
    })
}

/// Whether `member` is in `set` as the page says it: by the membership it
/// says once, in a number system; or as the member of a step said of every
/// member of a set inside `set`, which its requires lines speak of
/// (`SYNTAX.md`, a step said of every member).
fn member_in(
    member: &Node,
    set: &Node,
    letters: &crate::citing::Introduced,
    step: &Step,
    known: &Known,
) -> bool {
    let said_once = set.notation() == NUMBER_SYSTEMS
        && System::of_sign(&set.text).is_some_and(|system| {
            crate::citing::within(
                member,
                system,
                letters,
                &|d| crate::citing::nonzero_said_once(d, letters),
                &|_, _| false,
            )
        });
    if said_once {
        return true;
    }
    let Some(claimed) = known.step_member(step) else {
        return false;
    };
    matches!(
        (claimed.notation(), claimed.children.as_slice()),
        (MEMBERSHIP, [bound, over])
            if bound.is_name()
                && member.is_name()
                && bound.text == member.text
                && (known.alike(over, set) || crate::citing::set_within(over, set))
    )
}

/// Whether the line `r` says a function's type, `H : [a, b] → ℝ`. A
/// citation of a function's value or of an item about a function names it
/// beside the function (`READERS.md`, a function's type cited for its
/// values). A point in a function's domain, `k ∈ {1, …, n}`, is asked about
/// as any other line is: the item's sets are the function's
/// (`citing::typed_seed`), so the search needs the line, and one cited for
/// what a range says once, k ∈ ℤ, is cited for nothing.
fn in_a_domain(step: &Step, r: &str, known: &Known) -> bool {
    let scope = known.scope(step);
    let Some(stated) = scope.get(r) else {
        return false;
    };
    known
        .said_parts(stated, None)
        .into_iter()
        .flatten()
        .any(|n| n.notation() == FUNCTION_TYPE)
}

/// Whether `lighter`, `step` with a line taken away, is no longer supplied.
/// Taking a line away leaves a step whose facts are some of `step`'s, so a
/// way that step could supply the item, by either route, is one of the ways
/// `step`'s do (`ways`, found the first time a line asks). Where no way they
/// supply it fits in what is left, the step without the line is not
/// supplied; the one search takes the place of a search for each line.
fn fails_without(
    step: &Step,
    lighter: &Step,
    ways: &OnceCell<Option<Vec<Vec<Node>>>>,
    facts: &Parts,
    known: &Known,
    library: &Library,
) -> bool {
    let Some(ways) = ways.get_or_init(|| ways_supplied(step, known, library)) else {
        return false;
    };
    let left = known.parts(lighter, library);
    // What the argument rests on, asked rather than assumed: the facts left
    // are among these, and the claim and the seed are these, so the claim's
    // route is the one the ways were found by.
    within(&left.facts, &facts.facts)
        && same_shapes(&left.claims, &facts.claims)
        && same_shapes(
            &left.seed.values().cloned().collect::<Vec<_>>(),
            &facts.seed.values().cloned().collect::<Vec<_>>(),
        )
        && left.seed.keys().eq(facts.seed.keys())
        && !ways.iter().any(|way| within(way, &left.facts))
}

/// Whether a requires line below the step's `i`-th states a bound on the term
/// `said` puts in ℕ or ℕ₀, which that membership implies (`SYNTAX.md`, what a
/// membership line says) and the same membership said once does not
/// (`READERS.md`): `requires m·n ≥ 0` below `requires m·n ∈ ℕ`.
fn bound_below(step: &Step, i: usize, said: &Node, known: &Known) -> bool {
    let [term, set] = said.children.as_slice() else {
        return false;
    };
    let system = rules::system_of(&set.text);
    if said.notation() != MEMBERSHIP || rules::implied(system).is_empty() {
        return false;
    }
    step.requires[i + 1..].iter().any(|o| {
        known.whole(step, &o.fact).is_some_and(|f| {
            matches!(f.notation(), ORDER | EQUALITY)
                && f.walk().iter().any(|n| known.alike(n, term))
        })
    })
}

/// Whether a requires line below the step's `i`-th rests on what it says,
/// `said`: one citing a record that asks for it (`citing::asked`), or one
/// whose method asks it of the terms the line names (`built_on`).
fn needed_below(
    step: &Step,
    i: usize,
    said: &Node,
    known: &Known,
    library: &Library,
) -> bool {
    let req = &step.requires[i];
    if built_on(req, step, known) {
        return true;
    }
    step.requires[i + 1..].iter().any(|o| {
        let Some((named, _)) = o.cited_item() else {
            return false;
        };
        let Some(parts) = requires_parts(step, o, &[], known, library) else {
            return false;
        };
        match asked(&step.just.item(&named), &parts, library) {
            Built(asks) => asks.hypotheses.iter().any(|h| known.alike(h, said)),
            Declined(_) => false,
        }
    })
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
    scopes: &[FileScope],
) {
    let defines: BTreeSet<&str> =
        thm.defines.iter().map(|d| d.label.as_str()).collect();
    let functions =
        defined_functions(thm.defines.iter().chain(&scopes[thm.scope].defines));

    // A step holds where its item is supplied and concluded, and every
    // define it cites has its arguments in their domains: a line saying one
    // is in its domain does work as surely as one supplying a hypothesis.
    // `requires_concluded` says its requires lines' items are known to
    // conclude them: a requires line's parts are read from its own lines
    // and none the step cites, so a step that holds holds that still with a
    // cited line taken away.
    let holds_given = |step: &Step, requires_concluded: bool| -> bool {
        if unsupplied(step, known, library).is_some()
            || (!requires_concluded && !unconcluded(step, known, library).is_empty())
            || !domains_unsaid(step, &functions, known, library).is_empty()
        {
            return false;
        }
        // What the step claims follows from what the item concludes and what
        // the step names: a definition read either way takes the other side
        // from a cited line, which asks for it as surely as a hypothesis
        // does.
        let found = |how| searched(step, how, known, library).map(|r| !r.is_declined());
        if step.just.head.is(Method::Obtain) {
            return found(Search::Obtains).unwrap_or(false);
        }
        let Some(takes) = found(Search::Takes) else {
            return false;
        };
        known.parts(step, library).claims.is_empty() || takes
    };
    let holds = |step: &Step| holds_given(step, false);

    for step in &thm.steps {
        // A requires line citing an item is the step it would be, whatever
        // its own step's reason, and what its reason names it needs as a
        // step's citation does: a line cited only for a membership said once
        // is cited for nothing there too.
        for req in &step.requires {
            // A reason citing an item is one the reader cut.
            let (Some((named, _)), Ok(by)) = (req.cited_item(), &req.by) else {
                continue;
            };
            let as_step = reason_as_step(step, req, by);
            if library.groups(&as_step.just.item(&named)).is_none() || !holds(&as_step)
            {
                continue;
            }
            let ways: OnceCell<Option<Vec<Vec<Node>>>> = OnceCell::new();
            let facts = known.parts(&as_step, library);
            let mut named_refs: IndexSet<&String> = IndexSet::new();
            named_refs.extend(as_step.just.refs.iter());
            let asks = family_asks(&as_step, known, library);
            let scope = known.scope(step);
            for r in named_refs {
                if defines.contains(r.as_str()) || in_a_domain(step, r, known) {
                    continue;
                }
                // A line saying a sum's term at every point, or a type, the
                // item's function hypothesis asks, does work.
                let states = scope
                    .get(r)
                    .and_then(|s| known.stated_as_written(s))
                    .is_some_and(|n| asks.states(&n, known));
                if states {
                    continue;
                }
                let mut lighter = as_step.clone();
                lighter.just.refs = as_step
                    .just
                    .refs
                    .iter()
                    .filter(|x| *x != r)
                    .cloned()
                    .collect();
                if !fails_without(&as_step, &lighter, &ways, &facts, known, library)
                    && holds_given(&lighter, true)
                {
                    report.say(
                        &thm.path,
                        req.line,
                        format!(
                            "the requires line of step {} cites {r}, and {named} asks for nothing it says",
                            step.number
                        ),
                    );
                }
            }
        }
        let just = &step.just;
        let Some(item) = just.cited_item() else {
            continue;
        };
        if library.groups(&just.item(&item)).is_none() || !holds(step) {
            continue;
        }
        let mut refs: IndexSet<&String> = IndexSet::new();
        refs.extend(just.refs.iter());
        // The ways the step supplies its item, searched once and only if a
        // line asks (`fails_without`).
        let ways: OnceCell<Option<Vec<Vec<Node>>>> = OnceCell::new();
        let facts = known.parts(step, library);
        let lost_without = |lighter: &Step| {
            fails_without(step, lighter, &ways, &facts, known, library)
        };
        let asks = family_asks(step, known, library);
        let scope = known.scope(step);
        // Each line the step does without, taken away alone: a cited line,
        // and a requires line by its index.
        let mut spare_refs: Vec<&String> = Vec::new();
        let mut spare_requires: Vec<usize> = Vec::new();
        for r in refs {
            if defines.contains(r.as_str()) {
                continue;
            }
            // A line stating a function type the item asks for does work,
            // and so does one saying a sum's term at every point.
            let says_type = scope
                .get(r)
                .and_then(|s| known.stated_as_written(s))
                .is_some_and(|n| asks.states(&n, known));
            if says_type {
                continue;
            }
            let mut lighter = step.clone();
            lighter.just.refs = just.refs.iter().filter(|x| *x != r).cloned().collect();
            if !lost_without(&lighter) && holds_given(&lighter, true) {
                spare_refs.push(r);
            }
        }
        // Compared as formulas, so that `x∈ℤ` is `x ∈ ℤ`.
        let in_domain = domains_asked(thm, step, scopes, known);
        // What the step ends on by dropping an identity element asks to be
        // a number (`formulas::ends_asking`).
        let ends = super::formulas::ends_asking(thm, step, known, library, &[]);
        for (i, req) in step.requires.iter().enumerate() {
            let mut lighter = step.clone();
            lighter.requires.remove(i);
            let domain = known
                .whole_as_written(&req.fact)
                .is_some_and(|n| in_domain.contains(&n.by_shape()));
            let ended = known.whole_as_written(&req.fact).is_some_and(|n| {
                n.notation() == MEMBERSHIP
                    && ends.iter().any(|u| known.alike(&n.children[0], &u.left))
            });
            // What keeps a line without a search is asked before the search.
            if !asks.asks(step, &req.fact, known)
                && !domain
                && !ended
                && !built_on(req, step, known)
                && !lost_without(&lighter)
                && holds(&lighter)
            {
                spare_requires.push(i);
            }
        }
        // Lines that are each spare alone, and that the step cannot do
        // without all at once, say one hypothesis twice: the item asks for
        // what they say, and one of them is enough.
        let mut without_all = step.clone();
        without_all.just.refs.retain(|x| !spare_refs.contains(&x));
        without_all.requires = step
            .requires
            .iter()
            .enumerate()
            .filter(|(i, _)| !spare_requires.contains(i))
            .map(|(_, o)| o.clone())
            .collect();
        let twice = spare_refs.len() + spare_requires.len() > 1
            && (lost_without(&without_all) || !holds(&without_all));
        if twice {
            let mut named: Vec<String> =
                spare_refs.iter().map(|r| r.to_string()).collect();
            named.extend(spare_requires.iter().map(|&i| {
                format!(
                    "the requires line {}",
                    str::trim(step.requires[i].fact.text())
                )
            }));
            report.say(
                &thm.path,
                just.line,
                format!(
                    "step {} supplies one hypothesis of {item} twice, by {}; one of them is enough",
                    step.number,
                    named.join(" and ")
                ),
            );
            continue;
        }
        for r in spare_refs {
            report.say(
                &thm.path,
                just.line,
                format!(
                    "step {} cites {r}, and {item} asks for nothing it says",
                    step.number
                ),
            );
        }
        for i in spare_requires {
            let req = &step.requires[i];
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
