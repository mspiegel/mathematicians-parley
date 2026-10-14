//! What a citation supplies and claims, as the search reads them.

use crate::corpus::{Head, Step};
use crate::formula::page;
use crate::formula::{Node, Sort, Sorts, Whole};
use crate::matching::{standard, substitute_apart, substitute_apart_by, Binding};
use crate::outcome::Built;
use crate::rules;
use crate::sorts::{element_sort, Env};

use super::conclude::taken;
use super::library::{with_parts, Library};

/// A claim "for all k ∈ X, P" read at a member: the membership k ∈ X, which
/// the step then has as a fact, and P, which it then claims (`SYNTAX.md`, a
/// step said of every member). Which reading a citation takes is read off the
/// item, not tried: an item whose conclusions say no "for all" anywhere is
/// applied at a member, and one whose conclusions say one, as `upper-bound`
/// unfolds to one, is read as written. A define says one equation, and is
/// read at a member.
pub fn at_a_member(
    step: &Step,
    claims: &[Node],
    library: &Library,
    sorts: &Sorts,
) -> Option<(Node, Node)> {
    let [claim] = claims else {
        return None;
    };
    let just = &step.just;
    // A define says what its name is equal to, never a "for all", so a
    // step citing one for a "for all" is read at a member.
    if just.head != Head::Define {
        if !just.head.is_item() {
            return None;
        }
        let item = library.item(&just.item(&just.head.to_string()))?;
        if item.says_for_all() {
            return None;
        }
    }
    claimed_member(claim, library, sorts)
}

/// The citation's seed with what the citing proof says a function of the
/// item maps between. The item's `let f : D → E` asks for nothing a line
/// writes, but where f stands for a function a line in scope types, D and E
/// are that type's sets: without them, `x ∈ D` would be met by any
/// membership of x, 5 ∈ ℕ among them, for a function on {0, …, 1}. What f
/// stands for is what the citation names it, or else what the citation
/// takes it to be. `ours` is the function types the lines in scope at the
/// citing step say, `v : {0, …, n} → V`, as the citing tool reads them.
pub fn typed_seed(parts: &mut Parts, name: &str, ours: &[Node], library: &Library) {
    let typed = library.function_types(name);
    if typed.is_empty() || ours.is_empty() {
        return;
    }
    let mut stands = parts.seed.clone();
    if let Some(groups) = library.groups(name) {
        let taken = taken(&groups, &parts.claims, &parts.facts, &parts.seed, library);
        if let Built(t) = taken {
            for (letter, value) in t.binding {
                stands.entry(letter).or_insert(value);
            }
        }
    }
    for t in &typed {
        let [f, d, e] = t.children.as_slice() else {
            continue;
        };
        let Some(v) = stands.get(&f.text).filter(|v| v.is_name()) else {
            continue;
        };
        let Some(said) = ours.iter().find(|s| s.children[0].text == v.text) else {
            continue;
        };
        for (letter, set) in [(d, &said.children[1]), (e, &said.children[2])] {
            if letter.is_name() && !parts.seed.contains_key(&letter.text) {
                parts
                    .seed
                    .insert(letter.text.clone(), standard(set, &library.ctx));
            }
        }
    }
}

/// What a citation supplies, what it claims, and what it says its variables
/// stand for.
pub struct Parts {
    pub facts: Vec<Node>,
    pub claims: Vec<Node>,
    pub seed: Binding,
}

/// The parts of a citation from the facts as read: each with its parts, what
/// a membership implies, and what a function's type says at a point, each
/// read with the citing theorem's `sorts`, and all in the standard order
/// the item's patterns are in (`matching::standard`).
pub fn finished(
    facts: Vec<Node>,
    claims: Vec<Node>,
    seed: Binding,
    library: &Library,
    sorts: &Sorts,
) -> Parts {
    let ctx = &library.ctx;
    let facts: Vec<Node> = facts.iter().map(|f| standard(f, ctx)).collect();
    let claims = claims.iter().map(|c| standard(c, ctx)).collect();
    let seed = seed
        .into_iter()
        .map(|(name, value)| (name, standard(&value, ctx)))
        .collect();
    let mut facts = with_parts(&facts, library);
    let implied: Vec<Node> = facts
        .iter()
        .flat_map(|f| implied_facts(f, library.env, sorts))
        .collect();
    facts.extend(implied);
    let valued = function_values(&facts, library.env, sorts);
    let implied: Vec<Node> = valued
        .iter()
        .flat_map(|f| implied_facts(f, library.env, sorts))
        .collect();
    facts.extend(valued);
    facts.extend(implied);
    // What a membership implies is read from the rules' own spelling,
    // `x ≥ 1`, and is put in the same order.
    let facts = facts.iter().map(|f| standard(f, ctx)).collect();
    Parts {
        facts,
        claims,
        seed,
    }
}

/// What a claim "for all k ∈ X, P" gives a step that proves it in one line:
/// the membership k ∈ X, and P. "for all X ⊆ A" gives X ⊆ A. None for any
/// other claim.
pub fn claimed_member(
    claim: &Node,
    library: &Library,
    sorts: &Sorts,
) -> Option<(Node, Node)> {
    // "for all X ⊆ A" ranges over the parts of A, and a member is one.
    let (written, held_as) = match claim.notation.as_str() {
        "for-all" => ("x ∈ S", None),
        "for-all-part" => ("x ⊆ S", Some(Sort::of("set"))),
        _ => return None,
    };
    if claim.children.len() != 3 {
        return None;
    }
    let (letter, domain, body) =
        (&claim.children[0], &claim.children[1], &claim.children[2]);
    let said = bound_in(written, held_as, letter, domain, library, sorts)?;
    Some((said, body.clone()))
}

/// What a binder says of the letter it binds: `x ∈ S`, or `x ⊆ S` as
/// `written` has it, at the letter and the domain.
pub fn bound_in(
    written: &'static str,
    held_as: Option<Sort>,
    letter: &Node,
    domain: &Node,
    library: &Library,
    sorts: &Sorts,
) -> Option<Node> {
    // What a set holds is often not settled on the node; a membership of
    // it reads whatever the letter is.
    let held = held_as.unwrap_or_else(|| {
        domain
            .sort
            .held()
            .unwrap_or_else(|| element_sort(&domain.text, sorts))
    });
    let held = if held.is_unsorted() {
        Sort::of("any")
    } else {
        held
    };
    let mut local = sorts.clone();
    local.insert("x".into(), held);
    local.insert("S".into(), domain.sort.clone());
    let said = page::template(written, library.env.g, &local).ok()?;
    let mut put = Binding::new();
    put.insert("x".into(), letter.clone());
    put.insert("S".into(), domain.clone());
    Some(substitute_apart(&said, &put, &library.ctx))
}

/// Whether `fact` has the form `form` writes, with its letters `x` and `S`
/// standing for whatever is in their places, and what they stand for put in
/// `put`.
fn fits_form(form: &Node, fact: &Node, put: &mut Binding) -> bool {
    if form.is_name() && (form.text == "x" || form.text == "S") {
        return match put.get(&form.text) {
            Some(held) => held.shape() == fact.shape(),
            None => {
                put.insert(form.text.clone(), fact.clone());
                true
            }
        };
    }
    form.notation == fact.notation
        && form.text == fact.text
        && form.children.len() == fact.children.len()
        && form
            .children
            .iter()
            .zip(&fact.children)
            .all(|(f, g)| fits_form(f, g, put))
}

fn template(said: &'static str, env: Env, sorts: &Sorts) -> Node {
    page::template(said, env.g, sorts).unwrap_or_else(|p| {
        panic!("the notation database no longer reads {said:?}, which a membership implies: {p}")
    })
}

/// What a function's type and a membership of its domain say together: the
/// value there is in the codomain. `let a : {1, …, n} → ℝ` and `let k ∈ {1,
/// …, n}`, cited together, say a(k) ∈ ℝ (`READERS.md`, a function's type
/// cited for its values).
pub fn function_values(facts: &[Node], env: Env, sorts: &Sorts) -> Vec<Node> {
    let mut out = Vec::new();
    for typed in facts {
        if typed.notation != "function-type" || typed.children.len() != 3 {
            continue;
        }
        let (function, domain, codomain) =
            (&typed.children[0], &typed.children[1], &typed.children[2]);
        for member in facts {
            if member.notation != "membership"
                || member.children.len() != 2
                || member.children[1].shape() != domain.shape()
            {
                continue;
            }
            let point = &member.children[0];
            // A letter a binder introduces has no sort of its own yet, and
            // takes what the function's domain holds.
            let from_type = match function.sort.full() {
                Some(Whole::Function(domain, _)) => Sort::whole((**domain).clone()),
                _ => None,
            };
            let at = match (point.sort.full(), from_type) {
                (None, Some(domain)) => domain,
                _ => point.sort.clone(),
            };
            let mut local = sorts.clone();
            local.insert("f".into(), function.sort.clone());
            local.insert("x".into(), at);
            local.insert("S".into(), codomain.sort.clone());
            let Ok(said) = page::template("f(x) ∈ S", env.g, &local) else {
                continue;
            };
            let mut put = Binding::new();
            put.insert("f".into(), function.clone());
            put.insert("x".into(), point.clone());
            put.insert("S".into(), codomain.clone());
            out.push(substitute_apart_by(&said, &put, &env.g.binders()));
        }
    }
    out
}

/// What a fact the page writes as a part of a set, `C ⊆ A`, or as a member
/// of a power set, `C ∈ 𝒫A`, says in the other form (`rules::PARTS`); None
/// for a fact written otherwise, though its term be the same, as "g is
/// differentiable on (a, b)" is (a, b) ⊆ dom g′ in the kernel. The
/// elaborator asks this of its page reading of a fact, so both tools apply
/// the rule to the same lines.
pub fn part_said_otherwise(fact: &Node, env: Env, sorts: &Sorts) -> Option<Node> {
    let mut sets = sorts.clone();
    sets.insert("x".into(), Sort::of("set"));
    sets.insert("S".into(), Sort::of("set"));
    for (premise, conclusion, _) in rules::PARTS {
        let mut put = Binding::new();
        if fits_form(&template(premise, env, &sets), fact, &mut put) {
            return Some(substitute_apart_by(
                &template(conclusion, env, &sets),
                &put,
                &env.g.binders(),
            ));
        }
    }
    None
}

/// What a membership fact also says, by the tables in `rules`, which the
/// elaborator reads as well.
///
/// `k ∈ ℕ` also says k ∈ ℤ, k ∈ ℝ and the rest, and k ≥ 1 and k ≠ 0
/// (`SYNTAX.md`, what a membership line says). A part of a set is a member
/// of its power set and the other way round, so `C ⊆ A` also says C ∈ 𝒫A,
/// which is what `for all X ⊆ A` ranges over (`rules::PARTS`). Anything
/// else says only itself: a range is no number system, and a member of one
/// is whole by `mun:range-integer`.
pub fn implied_facts(fact: &Node, env: Env, sorts: &Sorts) -> Vec<Node> {
    if let Some(other) = part_said_otherwise(fact, env, sorts) {
        return vec![other];
    }
    let both = fact.children.len() == 2;
    if fact.notation != "membership"
        || !both
        || fact.children[1].notation != "number-systems"
    {
        return Vec::new();
    }
    let term = fact.children[0].clone();
    let system = rules::system_of(&fact.children[1].text);
    let mut local = sorts.clone();
    local.insert("x".into(), Sort::of("number"));
    let binders = env.g.binders();
    // Each says one thing of x, `x ∈ ℝ` or `x ≥ 0`: a membership is `x ∈ S`
    // with the number system at S.
    let mut said: Vec<Node> = rules::SYSTEM_OF
        .iter()
        .filter(|(_, big)| {
            Some(*big) != system && rules::within_path(system, Some(big)).is_some()
        })
        .map(|(sign, _)| {
            // S is read as the number system that fills it, whatever the
            // page's S is.
            let set = template(sign, env, &local);
            let mut systems = local.clone();
            systems.insert("S".into(), set.sort.clone());
            let put = Binding::from([
                ("x".to_string(), term.clone()),
                ("S".to_string(), set),
            ]);
            substitute_apart_by(&template("x ∈ S", env, &systems), &put, &binders)
        })
        .collect();
    let put = Binding::from([("x".to_string(), term)]);
    said.extend(rules::implied(system).iter().map(|(form, _)| {
        substitute_apart_by(&template(form, env, &local), &put, &binders)
    }));
    said
}
