//! A citation supplies what the item asks, and claims what it concludes.

use std::cell::OnceCell;
use std::collections::BTreeSet;

use indexmap::{IndexMap, IndexSet};

use super::formulas::chain_links;
use super::library::Known;
use super::structure::instantiated_line;
use super::Report;
use crate::citing::{
    asked, bound_in, claimed_member, concludes, conjuncts, derives, filled, finished,
    names_of, obtained, obtains, readings, search, supply, taken, taken_ways,
    with_parts, Group, Library, Parts, Sites, Ways,
};
use crate::corpus::proof::{requires_as_step, requires_item, Requires, METHODS};
use crate::corpus::{
    cited_item, define_parts, for_pieces, references, step_index, DefineParts,
    FileScope, Item, Method, Step, Theorem,
};
use crate::formula::{Node, Sort};
use crate::matching::{
    alike, binding_sites, instantiation, match_tree, substitute_apart, Binding,
    Context, PROPERTY,
};
use crate::outcome::{Built, Declined};
use crate::sorts::{sentences, supplied_by};
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
        let Some(parts) = requires_parts(step, req, known, library) else {
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
/// read with the defines the line cites. None where the fact does not read,
/// which `check_formulas` reports.
fn requires_parts(
    step: &Step,
    req: &Requires,
    known: &Known,
    library: &Library,
) -> Option<Parts> {
    let scope = known.scope(step);
    let (refs, _bad) = references(&req.how);
    // A define is written out where the line cites it (`Known::citing`).
    let defined = known.citing(&refs);
    let read_one = |s: &str| known.read_citing(s, &defined);
    let claims: Vec<Node> = sentences(&req.fact)
        .iter()
        .filter_map(|s| read_one(s))
        .collect();
    if claims.is_empty() {
        return None;
    }
    let mut supplied: Vec<String> = Vec::new();
    for r in &refs {
        if let Some(text) = scope.get(r) {
            supplied.extend(supplied_by(text));
        }
    }
    // A requires line may not cite another, but the facts the lines above
    // it state are established for the same step and are what a dull fact
    // its own citation asks for is written as.
    supplied.extend(step.requires_above(req.line).map(|o| o.fact.clone()));
    let mut read: Vec<Node> = supplied.iter().filter_map(|s| read_one(s)).collect();
    // A step said of every member in one line: its requires lines speak
    // of the member, whose membership the claim gives (`SYNTAX.md`).
    if step.openers.is_empty() {
        let claimed: Vec<Node> = sentences(&step.claim_text())
            .iter()
            .filter_map(|s| read_one(s))
            .collect();
        if let [claim] = claimed.as_slice() {
            if let Some((member, _)) = claimed_member(claim, library, &known.sorts) {
                read.push(member);
            }
        }
    }
    let mut seed = Binding::new();
    for (name, value) in instantiation(&req.how) {
        if let Some(got) = read_one(&value) {
            seed.insert(name, got);
        }
    }
    // The facts a step's own citation is given, so that an item cited
    // on a requires line reaches what it reaches cited by a step.
    Some(finished(read, claims, seed, library, &known.sorts))
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
            let Some(parts) = requires_parts(step, req, known, library) else {
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
        let name = step.just.item(&item);
        // A definition that unfolds gives the existence the step claims, which
        // the elaborator reaches from the claim and never asks the item for.
        let Some(Item::Record(record)) = library.item(&name) else {
            continue;
        };
        if Item::Record(record).unfolds() {
            continue;
        }
        let Some(groups) = library.groups(&name) else {
            continue;
        };
        let at = format!(
            "{}:{} | obtained | {}",
            thm.path,
            step.line,
            record.qualified()
        );
        let parts = known.parts(step, library);
        match obtained(&groups, &parts.facts, &parts.seed, library) {
            Built(taken) => {
                for said in &groups[taken.group].gives {
                    let said = filled(said, &taken.binding, &library.ctx);
                    out.push(format!("{at} | {}", known.print(&said)));
                }
            }
            Declined(_) => out.push(format!("{at} | declines")),
        }
    }
    out
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
    if !parts.claims.is_empty() {
        taken_ways(
            &groups,
            &parts.claims,
            &parts.facts,
            &parts.seed,
            library,
            &mut |path| out.push(took(path)),
        );
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
        for found in unconcluded(step, known, library) {
            let said = match &found.missing {
                Some(missing) => format!(
                    "the requires line of step {} cites {}, which asks for {}, and what it cites does not supply them",
                    step.number,
                    found.item,
                    missing.join("; ")
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
    let Some(said) = known.read(step, &req.fact) else {
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
        .filter_map(|r| known.read(step, &r.fact).map(|n| (r, n)))
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
            let cited = references(&r.how)
                .0
                .iter()
                .filter_map(|c| scope.get(c))
                .flat_map(|text| supplied_by(text))
                .filter_map(|s| known.read(step, &s))
                .any(|line| holds_atom(&line));
            let above = step
                .requires
                .iter()
                .take_while(|o| o.line != r.line)
                .filter(|o| o.line != req.line)
                .filter_map(|o| known.read(step, &o.fact))
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
    types: Vec<Node>,
    /// Which notations bind, so that a value is compared up to the letters
    /// it binds.
    ctx: Context,
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
    // defines: its rule, where the step cites the define and the rule is
    // written out, or its name, where it does not. What the step claims is
    // no guide to the letters: an `obtain` claims the witness, not the
    // item's conclusion.
    let defines: BTreeSet<String> = defined_functions(known.thm.defines.iter())
        .into_iter()
        .map(|f| f.name)
        .collect();
    let types = library
        .function_types(&just.item(&cited_item(just).expect("a cited item")))
        .iter()
        .map(|t| substitute_apart(t, &parts.seed, &library.ctx))
        .filter(|t| {
            let function = &t.children[0];
            function.notation == PROPERTY
                || (function.is_name() && defines.contains(&function.text))
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
    fn asks(&self, step: &Step, fact: &str, known: &Known) -> bool {
        let Some(node) = known.read(step, fact) else {
            return false;
        };
        if node.notation == "function-type" {
            return self.types.iter().any(|t| known.alike(t, &node));
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
fn domains_asked(thm: &Theorem, step: &Step, scopes: &[FileScope]) -> BTreeSet<String> {
    let functions =
        defined_functions(thm.defines.iter().chain(&scopes[thm.scope].defines));
    applied(&functions, &step.claim_text())
        .into_iter()
        .flat_map(|a| a.says)
        .collect()
}

/// A defined function by name, with the domain of each argument in order.
#[derive(Clone)]
struct Defined {
    name: String,
    label: String,
    domains: Vec<String>,
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
                        domains: vec![r.domain.clone()],
                        recursive: true,
                    });
                }
            }
            Built(DefineParts::One(one)) if !one.params.is_empty() => {
                functions.push(Defined {
                    name: one.name.clone(),
                    label: d.label.clone(),
                    domains: one.params.iter().map(|p| p.domain.clone()).collect(),
                    recursive: false,
                });
            }
            _ => {}
        }
    }
    functions
}

/// One argument a defined function is applied to in a text, and the
/// facts any one of which says it is in the function's domain.
struct Applied {
    label: String,
    arg: String,
    says: Vec<String>,
    /// Where in the text the application begins, in characters.
    start: usize,
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
    let text = step.claim_text();
    let direct = step.just.head == crate::corpus::Head::Define
        && used
            .iter()
            .any(|f| step.just.defined.as_deref() == Some(f.label.as_str()));
    let claim = known.read_as_written(&text);
    let sides = match &claim {
        Some(c)
            if direct
                && c.children.len() == 2
                && library.ctx.equations.contains(&c.notation) =>
        {
            &c.children
        }
        _ => return applied(used, &text),
    };
    sides
        .iter()
        .flat_map(|side| {
            let said = known.print(side);
            applied(used, &said)
                .into_iter()
                .filter(|a| a.start == 0)
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Every application of the functions in `text`, each argument with what
/// says it is in its domain.
fn applied(functions: &[Defined], text: &str) -> Vec<Applied> {
    let claim: Vec<char> = text.chars().collect();
    let mut out = Vec::new();
    let find = |needle: &[char], from: usize| -> Option<usize> {
        if needle.len() > claim.len() {
            return None;
        }
        (from..=claim.len() - needle.len())
            .find(|&i| claim[i..i + needle.len()] == *needle)
    };
    for Defined {
        name,
        label,
        domains,
        recursive,
    } in functions
    {
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
                        // A recursion's step at m asks m; any other argument
                        // is its value at 0, which asks nothing.
                        let member = if *recursive {
                            match step_index(arg) {
                                Some(index) => index,
                                None => continue,
                            }
                        } else {
                            arg.to_string()
                        };
                        let mut says = vec![squash(&format!("{member} ∈ {domain}"))];
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
                            says.push(squash(&format!("{member} ⊆ {inner}")));
                        }
                        out.push(Applied {
                            label: label.clone(),
                            arg: str::trim(arg).to_string(),
                            says,
                            start: at,
                        });
                    }
                    break;
                }
            }
            at += 1;
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
    let needs = |asked: &Applied| {
        known
            .read_as_written(&asked.says[0])
            .map(|n| known.print(&n))
            .unwrap_or_else(|| asked.says[0].clone())
    };
    for step in &thm.steps {
        for asked in domains_unsaid(step, &functions, known, library) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} cites {} at {}, so it needs {}, and nothing it cites or requires says it",
                    step.number,
                    asked.label,
                    asked.arg,
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
                        str::trim(&req.fact),
                        step.number,
                        asked.label,
                        asked.arg,
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
    let links = chain_links(&step.just);
    let mut cited: BTreeSet<String> = step.just.refs.iter().cloned().collect();
    for link in &links {
        cited.extend(references(&link.cite).0);
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
    let from_links: Vec<String> =
        links.iter().flat_map(|l| references(&l.cite).0).collect();
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
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut out = Vec::new();
    for asked in evaluated(step, &used, known, library) {
        let holds_index = known
            .read_as_written(&asked.arg)
            .is_some_and(|a| !a.names().is_disjoint(&indices));
        if holds_index {
            continue;
        }
        let said = asked.says.iter().any(|s| {
            known
                .read(step, s)
                .is_some_and(|n| shapes.contains(n.shape()))
        });
        if said || !seen.insert(asked.says[0].clone()) {
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
        let written: Vec<Node> = sentences(&step.claim_text())
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
            let mut best: Option<(usize, Binding)> = None;
            for w in &wants {
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
            "there-are" if body.children.len() == 5 => {
                bound.push((&body.children[0], &body.children[1]));
                bound.push((&body.children[2], &body.children[3]));
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
        let Some(text) = known.scope(step).get(&target).cloned() else {
            continue;
        };
        let parts = known.parts(step, library);
        let written: IndexMap<String, String> =
            instantiation(&step.just.text).into_iter().collect();
        for sentence in sentences(&text) {
            let (Some(read), Some(as_written)) = (
                known.read(step, &sentence),
                known.read_as_written(&sentence),
            ) else {
                continue;
            };
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
                    continue;
                };
                let value_written = written
                    .get(&b.letter.text)
                    .and_then(|v| known.read_as_written(v))
                    .unwrap_or_else(|| value.clone());
                let domain_written =
                    substitute_apart(&w.domain, &outer_written, &library.ctx);
                outer_written.insert(w.letter.text.clone(), value_written.clone());
                if parts.facts.iter().any(|f| known.alike(f, &want)) {
                    continue;
                }
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
            let Some(said) = known.read(step, &req.fact) else {
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
                            && squash(&o.fact) != squash(&req.fact))
                })
                .map(|(_, o)| o.clone())
                .collect();
            let says =
                |parts: &Parts| parts.facts.iter().any(|f| known.alike(f, &said));
            let mut uncited = lighter.clone();
            uncited.just.refs.clear();
            let repeated = says(&known.parts(&uncited, library))
                || (says(&known.parts(&lighter, library))
                    && !needed_below(step, i, &said, known, library));
            if repeated {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of step {} says {}, which the step's other lines already say",
                        step.number,
                        str::trim(&req.fact)
                    ),
                );
            }
        }
    }
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
        let Some(parts) = requires_parts(step, o, known, library) else {
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
        // a way that step could supply the item, by either route, is one of
        // the ways these do. Where no way these supply it fits in what is
        // left, the step without the line is not supplied, and asking again
        // would only say so; the one search here takes the place of a search
        // for each line, each of which had to try everything to find nothing.
        // Found the first time a line asks, since a step whose every line is
        // kept without a search never needs them.
        let ways: OnceCell<Option<Vec<Vec<Node>>>> = OnceCell::new();
        let facts = known.parts(step, library);
        let fails_without = |lighter: &Step| -> bool {
            let Some(ways) = ways.get_or_init(|| ways_supplied(step, known, library))
            else {
                return false;
            };
            let left = known.parts(lighter, library);
            // What the argument rests on, asked rather than assumed: the
            // facts left are among these, and the claim and the seed are
            // these, so the claim's route is the one the ways were found by.
            within(&left.facts, &facts.facts)
                && same_shapes(&left.claims, &facts.claims)
                && same_shapes(
                    &left.seed.values().cloned().collect::<Vec<_>>(),
                    &facts.seed.values().cloned().collect::<Vec<_>>(),
                )
                && left.seed.keys().eq(facts.seed.keys())
                && !ways.iter().any(|way| within(way, &left.facts))
        };
        for r in refs {
            if defines.contains(r.as_str()) {
                continue;
            }
            let mut lighter = step.clone();
            lighter.just.refs = just.refs.iter().filter(|x| *x != r).cloned().collect();
            if !fails_without(&lighter) && holds(&lighter) {
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
        // Compared as formulas, so that `x∈ℤ` is `x ∈ ℤ`.
        let in_domain: BTreeSet<String> = domains_asked(thm, step, scopes)
            .iter()
            .filter_map(|s| known.read_as_written(s))
            .map(|n| n.shape().to_string())
            .collect();
        for (i, req) in step.requires.iter().enumerate() {
            let mut lighter = step.clone();
            lighter.requires.remove(i);
            let domain = known
                .read_as_written(&req.fact)
                .is_some_and(|n| in_domain.contains(n.shape()));
            // What keeps a line without a search is asked before the search.
            if !asks.asks(step, &req.fact, known)
                && !domain
                && !built_on(req, step, known)
                && !fails_without(&lighter)
                && holds(&lighter)
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
