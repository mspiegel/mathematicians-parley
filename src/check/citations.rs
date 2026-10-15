//! A citation supplies what the item asks, and claims what it concludes.

use std::cell::OnceCell;
use std::collections::BTreeSet;

use indexmap::{IndexMap, IndexSet};

use super::formulas::chain_links;
use super::library::{introduced, listed_seed, typed_in_scope, typed_seed, Known};
use super::structure::instantiated_line;
use super::Report;
use crate::citing::{
    asked, bound_in, claimed_member, concludes, conjuncts, derives, filled, finished,
    function_values, identities_unsaid, names_of, obtained, obtains, readings,
    said_once, search, substitution_unsaid, supply, taken, taken_ways, with_parts,
    Group, Library, Parts, Sites, Taken, Ways,
};
use crate::corpus::proof::{
    requires_as_step, requires_item, substituted, substituted_into,
    substitution_source, Requires, METHODS,
};
use crate::corpus::{
    cited_item, define_parts, references, DefineParts, FileScope, Item, Method, Step,
    Theorem,
};
use crate::formula::page::{self, Written};
use crate::formula::{Node, Sort};
use crate::matching::{
    alike, binding_sites, match_tree, substitute_apart, Binding, Context, PROPERTY,
};
use crate::outcome::{Built, Declined, Route};
use crate::regex;
use crate::rules;
use crate::text::squash;

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
        let Some((named, _)) = requires_item(&req.how) else {
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
        out.push(Unconcluded {
            line: req.line,
            item: named,
            missing: missing_hypotheses(&groups, &parts, library),
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
    let (mut refs, _bad) = references(&req.how);
    refs.retain(|r| !without.contains(&r.as_str()));
    // A define is written out where the line cites it (`Known::citing`).
    let item = requires_item(&req.how).map(|(named, _)| step.just.item(&named));
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
            if let Some((member, body)) = claimed_member(claim, library, &known.sorts) {
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
            if let Some((member, _)) = claimed_member(claim, library, &known.sorts) {
                read.push(member);
            }
        }
    }
    let mut seed = known.seed(&req.values, &defined);
    if let Some((named, _)) = requires_item(&req.how) {
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
    said_once(&mut parts, &introduced(known, step), library, &known.sorts);
    if let Some((named, _)) = requires_item(&req.how) {
        typed_seed(&mut parts, &step.just.item(&named), step, known, library);
    }
    Some(parts)
}

/// What the record each requires line cites asks of it, and what the
/// record each obtain cites says there is, as this checker reads the page:
/// one line per hypothesis or sentence, in the page's notation, and one
/// saying the shared matcher declines where it does. `tests/agree.rs`
/// compares them with the elaborator's (`Elaborator::list_asked`), since
/// the two read the page each its own way before they ask `citing` alike.
pub fn answers(thm: &Theorem, library: &Library, known: &Known) -> Vec<String> {
    let mut out = Vec::new();
    for step in &thm.steps {
        for req in &step.requires {
            let Some((named, _)) = requires_item(&req.how) else {
                continue;
            };
            let name = step.just.item(&named);
            if !matches!(library.item(&name), Some(Item::Record(_))) {
                continue;
            }
            let Some(parts) = requires_parts(step, req, &[], known, library) else {
                continue;
            };
            let at = format!("{}:{} | asked | {named}", thm.path, req.line);
            match asked(&name, &parts, library) {
                Built(asks) => {
                    for h in &asks.hypotheses {
                        out.push(format!("{at} | {}", known.print(h)));
                    }
                }
                Declined(_) => out.push(format!("{at} | declines")),
            }
        }
        if !step.just.head.is(Method::Obtain) {
            continue;
        }
        let Some(item) = cited_item(&step.just) else {
            continue;
        };
        let Some(Item::Record(record)) = library.item(&step.just.item(&item)) else {
            continue;
        };
        let Some(there) = obtained_there(step, library, known) else {
            continue;
        };
        let at = format!(
            "{}:{} | obtained | {}",
            thm.path,
            step.line,
            record.qualified()
        );
        match there {
            Built(said) => {
                for said in &said {
                    out.push(format!("{at} | {}", known.print(said)));
                }
            }
            Declined(_) => out.push(format!("{at} | declines")),
        }
    }
    out
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
    let name = step.just.item(&cited_item(&step.just)?);
    if library.item(&name)?.unfolds() {
        return None;
    }
    let groups = library.groups(&name)?;
    let parts = known.parts(step, library);
    Some(
        obtained(&groups, &parts.facts, &parts.seed, library).map(|taken| {
            // An item saying "A ↔ there is …" gives the "there is", the
            // reading whose target it is, as the build obtains from it.
            groups[taken.group]
                .gives
                .iter()
                .map(|said| {
                    let there_is = readings(said, library)
                        .into_iter()
                        .map(|(target, _)| target)
                        .find(|t| library.exists.contains(&t.notation))
                        .unwrap_or_else(|| said.clone());
                    filled(&there_is, &taken.binding, &library.ctx)
                })
                .collect()
        }),
    )
}

/// What a step citing a corpus theorem, other than to obtain, makes each of
/// its letters, as the matcher reads the citation (`taken`): the values it
/// writes and what its claim and lines fix. None where the step cites no
/// theorem, or no group of it concludes the claim.
pub fn bound_there(
    step: &Step,
    library: &Library,
    known: &Known,
) -> Option<IndexMap<String, Node>> {
    if step.just.head.is(Method::Obtain) {
        return None;
    }
    let name = step.just.item(&cited_item(&step.just)?);
    if !matches!(library.item(&name)?, Item::Theorem(_)) {
        return None;
    }
    let groups = library.groups(&name)?;
    let parts = known.parts(step, library);
    let Built(taken) =
        taken(&groups, &parts.claims, &parts.facts, &parts.seed, library)
    else {
        return None;
    };
    Some(taken.binding.into_iter().collect())
}

/// The hypotheses of the item a step cites that nothing it names supplies,
/// or None where they are supplied or the step cites no item.
fn unsupplied(step: &Step, known: &Known, library: &Library) -> Option<Vec<String>> {
    let item = cited_item(&step.just)?;
    // A pointer that resolves to nothing is `check_citations`'s.
    let groups = library.groups(&step.just.item(&item))?;
    let parts = known.parts(step, library);
    missing_hypotheses(&groups, &parts, library)
}

/// The hypotheses of an item that a citation's facts do not supply, as the
/// item writes them; None where every one is supplied, or where a group of
/// the item asks for nothing. A step's citation and a requires line's are
/// asked the same way.
fn missing_hypotheses(
    groups: &[Group],
    parts: &Parts,
    library: &Library,
) -> Option<Vec<String>> {
    // The hypotheses are supplied under the binding the claim fixes as well,
    // where a property is fixed only by what it is said of in the claim:
    // count-step's P(k + 1) is `a(k + 1) = 0` because the claim counts the i
    // with a(i) = 0. A group the citation takes has them supplied.
    if !parts.claims.is_empty()
        && !taken(groups, &parts.claims, &parts.facts, &parts.seed, library)
            .is_declined()
    {
        return None;
    }
    // Where the claim is what a group concludes, the hypotheses missing are
    // those of that group nothing supplies under what the claim fixes, and
    // not every hypothesis it has: floor-between's x ∈ ℝ at x := A + N is
    // said once, and only k ∈ ℤ at k := ⌊A⌋ + N is not supplied.
    if let Some(Built(alone)) =
        (!parts.claims.is_empty()).then(|| concluded_alone(groups, parts, library))
    {
        // Each is said at what the claim fixes, in the page's notation, so
        // that `P or Q` with P := 2 = P reads `2 = P or Q` and does not
        // seem to name the proof's own P; and at what the citation writes,
        // which fixes a letter the conclusion does not hold: c := m.
        let mut fixed = parts.seed.clone();
        for (name, value) in &alone.binding {
            fixed.insert(name.clone(), value.clone());
        }
        let unmet: Vec<String> = groups[alone.group]
            .wants
            .iter()
            .filter(|(_, tree)| !supplied_alone(tree, parts, &alone.binding, library))
            .map(|(_, tree)| library.env.g.print(&filled(tree, &fixed, &library.ctx)))
            .collect();
        if !unmet.is_empty() {
            return Some(unmet);
        }
    }
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
        // Each under what the citation writes for its letters: `c := m`
        // shows gcd(m, 3), not the item's gcd(c, 3).
        missing = Some(
            want.iter()
                .map(|(_, tree)| {
                    library
                        .env
                        .g
                        .print(&filled(tree, &parts.seed, &library.ctx))
                })
                .collect(),
        );
    }
    missing
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
    parts: &Parts,
    binding: &Binding,
    library: &Library,
) -> bool {
    let trees = [want.clone()];
    let variables = names_of(&trees);
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
    let item = cited_item(&step.just)?;
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
    one.len() == other.len()
        && one.iter().zip(other).all(|(a, b)| a.shape() == b.shape())
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
            let them = if missing.len() == 1 { "it" } else { "them" };
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} cites {}, which asks for {}, and what it cites does not supply {them}",
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
        // A claim that is what the item concludes, where only a hypothesis
        // is not supplied, is said once, by `check_hypotheses`, which names
        // the hypothesis.
        let hypotheses_said = || {
            !concluded_alone(&groups, &parts, library).is_declined()
                && unsupplied(step, known, library).is_some()
        };
        if !concludes(&groups, &parts.claims, &parts.facts, &parts.seed, library)
            && !hypotheses_said()
        {
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
            let said = match unsaid.first() {
                Some(left) => format!(
                    "step {} drops an identity element from what {head} concludes, and nothing says {} is a number; a requires line says it",
                    step.number,
                    known.print(left)
                ),
                None => format!(
                    "step {} claims something that {head} does not conclude",
                    step.number
                ),
            };
            report.say(&thm.path, just.line, said);
        }
    }
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
        if !library.bicond.contains(&whole.notation)
            || !library.exists.contains(&right.notation)
        {
            continue;
        }
        let parts = known.parts(step, library);
        let refs: Vec<&str> = just.refs.iter().map(String::as_str).collect();
        let cites_one = known
            .lines_say(step, &refs, library)
            .iter()
            .any(|n| library.exists.contains(&n.notation));
        let claims_one = parts
            .claims
            .iter()
            .any(|n| library.exists.contains(&n.notation));
        if cites_one || claims_one || parts.claims.is_empty() {
            continue;
        }
        let mut subject = left.clone();
        while let Some(first) = subject.children.first().cloned() {
            subject = first;
        }
        let letter = subject.text.clone();
        if !subject.is_name() || just.values.names().any(|n| n == letter) {
            continue;
        }
        if !known.sorts.introduces(&letter) {
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
        let Some(item) = cited_item(&step.just) else {
            continue;
        };
        if library.groups(&step.just.item(&item)).is_none() {
            continue;
        }
        let asks = family_asks(step, known, library);
        let parts = known.parts(step, library);
        for t in &asks.types {
            let function = &t.asked.children[0];
            if !function.is_name() || defines.contains(&function.text) {
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
    }
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
        if !step.just.head.is(Method::Substitute) {
            continue;
        }
        let equation =
            substituted(&step.just, &thm.path).and_then(|e| known.whole_as_written(&e));
        let (Some(equation), Some(claim)) =
            (equation, known.whole_as_written(&step.claim))
        else {
            continue;
        };
        let [left, right] = equation.children.as_slice() else {
            continue;
        };
        // The equation is part of the line it is taken from (`SYNTAX.md`,
        // substitute), as that line writes it or turned. A reference to
        // nothing is `check_references`'s to report, and a define, whose
        // equation is the name and what it names and no sentence a line
        // states, the elaborator's.
        let defined = |r: &str| thm.defines.iter().any(|d| d.label == r);
        if let Some(source) = substitution_source(&step.just).filter(|s| !defined(s)) {
            let scope = known.scope(step);
            if let Some(said) =
                scope.get(&source).and_then(|s| known.stated_as_written(s))
            {
                let turned = Node::new(
                    &equation.notation,
                    equation.sort.clone(),
                    vec![right.clone(), left.clone()],
                    &equation.text,
                );
                let mut parts = vec![said.clone()];
                parts.extend(conjuncts(&said, library));
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
        let ways: Vec<(Vec<Node>, Node)> = match substituted_into(&step.just) {
            Some(into) => {
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
                [t, rewritten] if known.ctx.equations.contains(&claim.notation) => {
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
        let Some(names) = OBTAINED_NAMES.captures(&just.text) else {
            continue;
        };
        let names: Vec<&str> = names[1].split(',').map(str::trim).collect();
        let existence = match cited_item(just) {
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
                let [one] = said.as_slice() else {
                    continue;
                };
                one.clone()
            }
            Some(item) => {
                let name = just.item(&item);
                if library.item(&name).is_some_and(|i| i.unfolds()) {
                    continue;
                }
                let Some(groups) = library.groups(&name) else {
                    continue;
                };
                let parts = known.parts(step, library);
                let Built(taken) =
                    obtained(&groups, &parts.facts, &parts.seed, library)
                else {
                    continue; // `check_obtained` reports it
                };
                groups[taken.group]
                    .gives
                    .iter()
                    .map(|g| filled(g, &taken.binding, &library.ctx))
                    .find(|g| exhibited(g, library, known).is_some())
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
            match body.notation.as_str() {
                "there-is" if kids.len() == 3 => order.push((&kids[0], &kids[1])),
                _ => break,
            }
            body = last;
        }
        if order.len() != names.len() {
            // A line that says no "there is" at all where one is left to
            // take has nothing to obtain; another spelling of one, a part
            // or a function, is the elaborator's to read.
            if cited_item(just).is_none() && !body.notation.starts_with("there") {
                report.say(
                    &thm.path,
                    just.line,
                    format!(
                        "step {} obtains {} from a line that says no \"there is\" of as many",
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
                    .sentence()
                    .ok()
                    .and_then(|s| known.read_as_written(&s))
                else {
                    continue;
                };
                put.insert(letter.text.clone(), named);
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
        // A membership written `x ∈ S` is the one the "there is" gives; one
        // its notation spells otherwise is the elaborator's to read.
        for ((letter, domain), claimed) in order.iter().zip(&said) {
            let Some(member) =
                bound_in("x ∈ S", None, letter, domain, library, &known.sorts)
            else {
                continue;
            };
            let member = substitute_apart(&member, &put, &library.ctx);
            if claimed.notation == member.notation && !known.alike(claimed, &member) {
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

regex!(OBTAINED_NAMES, r"^obtain\s+(.+?)(?::\s|\s+from\s)");

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
        let _ = requires_read_as_step(report, thm, &under, &kinded.shown);
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
    let (held, asking, whole): (Vec<&Node>, &[&str], bool) =
        match said.notation.as_str() {
            "membership" if said.children.len() == 2 => {
                (vec![&said.children[0]], &ASKING, false)
            }
            "logical-not"
                if said.children.len() == 1
                    && said.children[0].notation == "equality"
                    && said.children[0].children.len() == 2 =>
            {
                (
                    said.children[0]
                        .children
                        .iter()
                        .filter(|c| c.notation != "numeral")
                        .collect(),
                    &["membership", "algebra"],
                    false,
                )
            }
            "order" if said.children.len() == 2 => (
                said.children
                    .iter()
                    .filter(|c| c.notation != "numeral")
                    .collect(),
                &["inequalities"],
                false,
            ),
            "equality" if said.children.len() == 2 => (
                said.children
                    .iter()
                    .filter(|c| c.notation != "numeral")
                    .collect(),
                &ASKING,
                true,
            ),
            _ => return false,
        };
    let atoms: Vec<String> = held.iter().map(|h| h.shape().to_string()).collect();
    let holds_atom = |n: &Node| {
        atoms
            .iter()
            .any(|atom| n.walk().iter().any(|part| part.shape() == *atom))
    };
    let scope = known.scope(step);
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
        .filter_map(|r| known.whole(step, &r.fact).map(|n| (r, n)))
        .any(|(r, n)| {
            let held = if n.notation == "membership" && n.children.len() == 2 {
                &n.children[0]
            } else {
                &n
            };
            let written = atoms.iter().any(|atom| {
                (whole || held.shape() != *atom)
                    && held.walk().iter().any(|part| part.shape() == *atom)
            });
            // A line the lower one cites, or another requires line above it,
            // carries the term to it: `deg(x) ∈ ℕ₀: membership, from 2` rests
            // on `|S| ∈ ℕ₀` above it where line 2 says deg(x) = |S|, and so
            // does `deg(x) ∈ ℤ: membership` under `requires deg(x) = |S|`.
            let defined = known.citing_step(step);
            let cited = references(&r.how)
                .0
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
            written || cited || above
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
}

impl AskedType {
    /// Whether `node` states this type, an open letter standing for any set.
    fn stated_by(&self, node: &Node, known: &Known) -> bool {
        let (asked, said) = (&self.asked, node);
        asked.notation == said.notation
            && asked.children.len() == said.children.len()
            && asked.children.iter().zip(&said.children).all(|(a, s)| {
                (a.is_name() && self.open.contains(&a.text)) || known.alike(a, s)
            })
    }
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
    // letters, `f := F`, where that makes the function one no `let` types:
    // one the proof defines, its rule, where the step cites the define and
    // the rule is written out, or its name, where it does not; or one a let
    // says only is a function on a set. A type a let declares is not asked
    // for (`GRAMMAR.md`, the function's type is a declaration). What the
    // step claims is no guide to the letters: an `obtain` claims the
    // witness, not the item's conclusion.
    let declared: BTreeSet<String> = typed_in_scope(known, step)
        .iter()
        .map(|t| t.children[0].text.clone())
        .collect();
    // What the citation writes, and what the match of the item against the
    // claim and the cited lines fixes beside it: `g is continuous on D`
    // claimed by `def:continuous-on` makes the item's f the page's g
    // whether or not the step writes f := g.
    let mut fixed = parts.seed.clone();
    if let Built(taken) =
        taken(&groups, &parts.claims, &parts.facts, &parts.seed, library)
    {
        for (name, value) in taken.binding {
            if value.notation != PROPERTY && !fixed.contains_key(&name) {
                fixed.insert(name, value);
            }
        }
    }
    let types = library
        .function_types(&just.item(&cited_item(just).expect("a cited item")))
        .iter()
        .map(|t| AskedType {
            asked: substitute_apart(t, &fixed, &library.ctx),
            open: t.children[1..]
                .iter()
                .filter(|s| s.is_name() && !fixed.contains_key(&s.text))
                .map(|s| s.text.clone())
                .collect(),
            filled: fixed.contains_key(&t.children[0].text),
        })
        .filter(|t| {
            let function = &t.asked.children[0];
            function.notation == PROPERTY
                || (function.is_name() && !declared.contains(&function.text))
        })
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
        ctx: library.ctx.clone(),
    }
}

impl FamilyAsks {
    /// Whether one requires line's fact is a membership the item's function
    /// hypotheses ask for, read as the checks of its step read it.
    fn asks(&self, step: &Step, fact: &Written, known: &Known) -> bool {
        let Some(node) = known.whole(step, fact) else {
            return false;
        };
        if node.notation == "function-type" {
            return self.types.iter().any(|t| t.stated_by(&node, known));
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
            // A function the proof defines, whose type the item asks over a
            // set the define may not name: the type said of every point,
            // `for all i ∈ {1, …, k + 1}, t(i) ∈ ℝ`, which holds where
            // `t : {1, …, k + 1} → ℝ` does not, t's domain being the
            // define's.
            let (set, value) = (&node.children[1], &body.children[0]);
            let pointwise = value.notation == "application"
                && value.children.len() == 2
                && known.alike(&value.children[1], bound)
                && self.types.iter().any(|t| {
                    let [f, d, e] = t.asked.children.as_slice() else {
                        return false;
                    };
                    f.is_name()
                        && known.alike(f, &value.children[0])
                        && ((d.is_name() && t.open.contains(&d.text))
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
                at.insert(v.text.clone(), bound.clone());
                let value = substitute_apart(&v.children[0], &at, &self.ctx);
                alike(&value, &body.children[0], &self.ctx, &none, &none)
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
fn domains_asked(
    thm: &Theorem,
    step: &Step,
    scopes: &[FileScope],
    known: &Known,
) -> BTreeSet<String> {
    let functions =
        defined_functions(thm.defines.iter().chain(&scopes[thm.scope].defines));
    let Some(claim) = known.whole_as_written(&step.claim) else {
        return BTreeSet::new(); // `check_formulas` says it does not read
    };
    applied(&functions, &claim, false, known)
        .into_iter()
        .flat_map(|a| a.says)
        .map(|s| s.shape().to_string())
        .collect()
}

/// A defined function by name, with the domain of each argument in order.
#[derive(Clone)]
struct Defined {
    name: String,
    label: String,
    /// Each argument's domain, as the define writes it.
    domains: Vec<Written>,
    /// Defined by recursion, whose domain is its step clause's index: the
    /// clause at k + 1 holds for k in the domain, and the base clause for
    /// its one argument.
    recursive: bool,
}

/// The functions some defines name.
fn defined_functions<'d>(
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
                    domains: one.params.iter().map(|p| d.formula(&p.domain)).collect(),
                    recursive: false,
                });
            }
            _ => {}
        }
    }
    functions
}

/// One argument a defined function is applied to in a claim, and the
/// facts any one of which says it is in the function's domain, as written.
struct Applied {
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
        && library.ctx.equations.contains(&claim.notation))
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
    let read = |w: &Written| known.read_as_written(&w.sentence().ok()?);
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
            if !matches!(node.notation.as_str(), "application" | "application-to-two")
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
                    match (
                        arg.notation.as_str(),
                        arg.text.as_str(),
                        arg.children.as_slice(),
                    ) {
                        ("additive", "+", [index, one])
                            if one.notation == "numeral" && one.text == "1" =>
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
                if let ("powerset", [inner]) =
                    (set.notation.as_str(), set.children.as_slice())
                {
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
    if ctx.sums.contains(&node.notation) {
        let (held, _) = ctx.held_body(&node.notation);
        for at in held {
            if let Some(letter) = node.children.get(at).filter(|c| c.is_name()) {
                out.insert(letter.text.clone());
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
            let Some(as_step) = requires_read_as_step(report, thm, step, req) else {
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
/// that is only `from`, which is read from the lines it names. A reason that
/// does not read is reported.
fn requires_read_as_step(
    report: &mut Report,
    thm: &Theorem,
    step: &Step,
    req: &Requires,
) -> Option<Step> {
    let how = str::trim(&req.how);
    let method = METHODS.iter().any(|m| {
        how == m.as_str()
            || how.starts_with(&format!("{} ", m.as_str()))
            || how.starts_with(&format!("{},", m.as_str()))
    });
    if requires_item(how).is_none() && !method {
        return None;
    }
    match requires_as_step(step, req, &thm.path) {
        Ok(mut as_step) => {
            as_step.requires = step.requires_above(req.line).cloned().collect();
            Some(as_step)
        }
        Err(problem) => {
            report.problems.push(problem);
            None
        }
    }
}

/// What a step citing a define, itself or on a calculation line, needs of
/// each argument's domain and nothing it cites or requires says, with what
/// each of those implies: each application once.
fn domains_unsaid(
    step: &Step,
    functions: &[Defined],
    known: &Known,
    library: &Library,
) -> Vec<Applied> {
    let links = chain_links(&step.just, &known.thm.path);
    let mut cited: BTreeSet<String> = step.just.refs.iter().cloned().collect();
    for link in &links {
        cited.extend(references(&link.line.cite).0);
    }
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
        .flat_map(|l| references(&l.line.cite).0)
        .collect();
    let refs: Vec<&str> = from_links.iter().map(String::as_str).collect();
    facts.extend(known.lines_say(step, &refs, library));
    // A claim said of every member puts the member in its domain.
    facts.extend(
        parts
            .claims
            .iter()
            .filter_map(|c| claimed_member(c, library, &known.sorts))
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
    let shapes: BTreeSet<&str> = facts.iter().map(|f| f.shape()).collect();
    let defined = known.citing_step(step);
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut out = Vec::new();
    for asked in evaluated(step, &used, known, library) {
        if !asked.arg.names().is_disjoint(&indices) {
            continue;
        }
        // Compared with the facts as they are read, defines written out.
        let said = asked
            .says
            .iter()
            .any(|s| shapes.contains(known.as_cited(s, &defined).shape()));
        if said || !seen.insert(asked.says[0].shape().to_string()) {
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
    for step in &thm.steps {
        if !step.just.head.is(Method::Exhibit) {
            continue;
        }
        let parts = known.parts(step, library);
        let written: Vec<Node> = step
            .claim
            .sentences()
            .iter()
            .filter_map(|s| known.read_as_written(s))
            .collect();
        for (claim, as_written) in parts.claims.iter().zip(&written) {
            let Some(Exhibited { wants, letters }) = exhibited(claim, library, known)
            else {
                continue;
            };
            let mut sites = Sites::new();
            for t in &wants {
                binding_sites(t, &library.ctx, &[], &mut sites);
            }
            let facts = with_parts(&parts.facts, library);
            let stated = |wants: &[Node]| {
                supply(
                    wants,
                    &facts,
                    &Binding::new(),
                    &letters,
                    library,
                    &sites,
                    true,
                )
            };
            // A term equals itself, which no line need write: gH = aH at
            // a = g is stated by nothing and needs nothing.
            let itself = |w: &Node| {
                w.notation == "equality"
                    && w.children.len() == 2
                    && known.alike(&w.children[0], &w.children[1])
            };
            let (equations, rest): (Vec<Node>, Vec<Node>) = wants
                .iter()
                .cloned()
                .partition(|w| w.notation == "equality" && w.children.len() == 2);
            let said = stated(&wants).is_some()
                || (!equations.is_empty()
                    && stated(&rest).is_some_and(|at| {
                        equations
                            .iter()
                            .all(|e| itself(&substitute_apart(e, &at, &library.ctx)))
                    }));
            if said {
                continue;
            }
            // The value is the one the most parts are said of, each part's
            // own line suggesting one; what is not said of it is what the
            // step needs.
            let holds = |w: &Node, at: &Binding| {
                let w = substitute_apart(w, at, &library.ctx);
                itself(&w) || facts.iter().any(|f| known.alike(f, &w))
            };
            // A letter's bare membership, n ∈ ℕ, fits every number in ℕ, and
            // a numeral's membership is said once (`said_once`), so the value
            // it suggests is no reading of the claim: what the body says is
            // asked first, and wins where as many parts are said of each.
            let bare = |w: &Node| {
                w.notation == "membership"
                    && w.children
                        .first()
                        .is_some_and(|t| letters.contains(&t.text))
            };
            let mut best: Option<(usize, Binding)> = None;
            for w in wants
                .iter()
                .filter(|w| !bare(w))
                .chain(wants.iter().filter(|w| bare(w)))
            {
                let Some(at) = stated(std::slice::from_ref(w)) else {
                    continue;
                };
                if !letters.iter().all(|l| at.contains_key(l)) {
                    continue;
                }
                let count = wants.iter().filter(|w| holds(w, &at)).count();
                if best.as_ref().is_none_or(|(most, _)| count > *most) {
                    best = Some((count, at));
                }
            }
            let Some((_, at)) = best else {
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
            let shown = exhibited(as_written, library, known)
                .map(|e| e.wants)
                .filter(|w| w.len() == wants.len())
                .unwrap_or_else(|| wants.clone());
            let values: Vec<String> = letters
                .iter()
                .filter_map(|l| at.get(l).map(|v| format!("{l} := {}", known.print(v))))
                .collect();
            for (want, show) in wants.iter().zip(&shown) {
                if holds(want, &at) {
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
}

/// What a "there is" asks of the value exhibited for it: each letter in its
/// domain, then each part of the body; and the letters.
struct Exhibited {
    wants: Vec<Node>,
    letters: BTreeSet<String>,
}

fn exhibited(claim: &Node, library: &Library, known: &Known) -> Option<Exhibited> {
    // The letters and their domains, then the body: a "there is" whose body
    // is a "there is" again, as "there are k, m, n ∈ ℕ with …" builds, binds
    // each letter in turn.
    let mut bound: Vec<(&Node, &Node)> = Vec::new();
    let mut body = claim;
    loop {
        match body.notation.as_str() {
            "there-is" if body.children.len() == 3 => {
                bound.push((&body.children[0], &body.children[1]));
            }
            _ => break,
        }
        body = body.children.last()?;
    }
    if bound.is_empty() {
        return None;
    }
    let mut wants: Vec<Node> = bound
        .iter()
        .filter_map(|(letter, domain)| {
            bound_in("x ∈ S", None, letter, domain, library, &known.sorts)
        })
        .collect();
    wants.extend(conjuncts(body, library));
    let letters = bound.iter().map(|(l, _)| l.text.clone()).collect();
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
        let Some(target) = instantiated_line(&step.just.text) else {
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
                .any(|n| ["implication", "conditional"].contains(&n.notation.as_str()))
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
                outer.insert(b.letter.text.clone(), value.clone());
                let Some(want) = bound_in(
                    b.how,
                    b.held.clone(),
                    value,
                    &domain,
                    library,
                    &known.sorts,
                ) else {
                    judged = false;
                    continue;
                };
                let value_written = written
                    .get(&b.letter.text)
                    .cloned()
                    .unwrap_or_else(|| value.clone());
                let domain_written =
                    substitute_apart(&w.domain, &outer_written, &library.ctx);
                outer_written.insert(w.letter.text.clone(), value_written.clone());
                if parts.facts.iter().any(|f| known.alike(f, &want)) {
                    wants.push(want);
                    continue;
                }
                judged = false;
                let needed = bound_in(
                    b.how,
                    b.held.clone(),
                    &value_written,
                    &domain_written,
                    library,
                    &known.sorts,
                )
                .unwrap_or(want);
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
/// said to be in it — `x ∈ S`, or `x ⊆ S` for a part, with the sort the
/// letter then has.
struct Binder {
    letter: Node,
    domain: Node,
    how: &'static str,
    held: Option<Sort>,
}

/// The binders a sentence opens with, outermost first.
fn binders_of(node: &Node) -> Vec<Binder> {
    let mut out = Vec::new();
    let mut node = node.clone();
    loop {
        let (how, held) = match node.notation.as_str() {
            "for-all" => ("x ∈ S", None),
            "for-all-part" => ("x ⊆ S", Some(Sort::of("set"))),
            _ => break,
        };
        if node.children.len() != 3 {
            break;
        }
        out.push(Binder {
            letter: node.children[0].clone(),
            domain: node.children[1].clone(),
            how,
            held,
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
                            && squash(o.fact.text()) != squash(req.fact.text()))
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
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of step {} says {}, which the step's other lines already say",
                        step.number,
                        str::trim(req.fact.text())
                    ),
                );
            }
        }
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
) {
    for step in &thm.steps {
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
            if !read_off(&[]) {
                continue;
            }
            let (refs, _bad) = references(&req.how);
            let spare: Vec<&str> = refs
                .iter()
                .map(String::as_str)
                .filter(|r| read_off(&[r]))
                .collect();
            // Lines each spare alone that the fact needs one of say it twice,
            // which `check_repeated` and the elaborator judge.
            if spare.len() > 1 && !read_off(&spare) {
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
        .any(|n| n.notation == "function-type")
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
    if said.notation != "membership" || rules::implied(system).is_empty() {
        return false;
    }
    step.requires[i + 1..].iter().any(|o| {
        known.whole(step, &o.fact).is_some_and(|f| {
            matches!(f.notation.as_str(), "order" | "equality")
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
        let Some((named, _)) = requires_item(&o.how) else {
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
    let holds = |step: &Step| -> bool {
        if unsupplied(step, known, library).is_some()
            || !unconcluded(step, known, library).is_empty()
            || !domains_unsaid(step, &functions, known, library).is_empty()
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
        // A requires line citing an item is the step it would be, whatever
        // its own step's reason, and what its reason names it needs as a
        // step's citation does: a line cited only for a membership said once
        // is cited for nothing there too.
        for req in &step.requires {
            let Some((named, _)) = requires_item(&req.how) else {
                continue;
            };
            let Ok(as_step) = requires_as_step(step, req, &thm.path) else {
                continue;
            };
            if library.groups(&as_step.just.item(&named)).is_none() || !holds(&as_step)
            {
                continue;
            }
            let ways: OnceCell<Option<Vec<Vec<Node>>>> = OnceCell::new();
            let facts = known.parts(&as_step, library);
            let mut named_refs: IndexSet<&String> = IndexSet::new();
            named_refs.extend(as_step.just.refs.iter());
            for r in named_refs {
                if defines.contains(r.as_str()) || in_a_domain(step, r, known) {
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
                    && holds(&lighter)
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
        let Some(item) = cited_item(just) else {
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
            // A line stating a function type the item asks for does work.
            let says_type = scope
                .get(r)
                .and_then(|s| known.stated_as_written(s))
                .is_some_and(|n| asks.types.iter().any(|t| t.stated_by(&n, known)));
            if says_type {
                continue;
            }
            let mut lighter = step.clone();
            lighter.just.refs = just.refs.iter().filter(|x| *x != r).cloned().collect();
            if !lost_without(&lighter) && holds(&lighter) {
                spare_refs.push(r);
            }
        }
        // Compared as formulas, so that `x∈ℤ` is `x ∈ ℤ`.
        let in_domain = domains_asked(thm, step, scopes, known);
        for (i, req) in step.requires.iter().enumerate() {
            let mut lighter = step.clone();
            lighter.requires.remove(i);
            let domain = known
                .whole_as_written(&req.fact)
                .is_some_and(|n| in_domain.contains(n.shape()));
            // What keeps a line without a search is asked before the search.
            if !asks.asks(step, &req.fact, known)
                && !domain
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
