//! What a citation supplies and claims, as the search reads them.

use crate::formula::{parse_here, Node, Sort, Sorts, Whole};
use crate::matching::{substitute, Binding};
use crate::rules;
use crate::sorts::{element_sort, Env};

use super::library::{with_parts, Library};

/// What a citation supplies, what it claims, and what it says its variables
/// stand for.
pub struct Parts {
    pub facts: Vec<Node>,
    pub claims: Vec<Node>,
    pub seed: Binding,
}

/// The parts of a citation from the facts as read: each with its parts, what
/// a membership implies, and what a function's type says at a point, each
/// read with the citing theorem's `sorts`.
pub fn finished(
    facts: Vec<Node>,
    claims: Vec<Node>,
    seed: Binding,
    library: &Library,
    sorts: &Sorts,
) -> Parts {
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
    written: &str,
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
    let said = parse_here(written, library.env.g, &local).ok()?;
    let mut put = Binding::new();
    put.insert("x".into(), letter.clone());
    put.insert("S".into(), domain.clone());
    Some(substitute(&said, &put))
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

fn template(said: &str, env: Env, sorts: &Sorts) -> Node {
    parse_here(said, env.g, sorts).unwrap_or_else(|p| {
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
            let Ok(said) = parse_here("f(x) ∈ S", env.g, &local) else {
                continue;
            };
            let mut put = Binding::new();
            put.insert("f".into(), function.clone());
            put.insert("x".into(), point.clone());
            put.insert("S".into(), codomain.clone());
            out.push(substitute(&said, &put));
        }
    }
    out
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
    let mut sets = sorts.clone();
    sets.insert("x".into(), Sort::of("set"));
    sets.insert("S".into(), Sort::of("set"));
    for (premise, conclusion, _) in rules::PARTS {
        let mut put = Binding::new();
        if fits_form(&template(premise, env, &sets), fact, &mut put) {
            return vec![substitute(&template(conclusion, env, &sets), &put)];
        }
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
    let mut templates: Vec<String> = rules::SYSTEM_OF
        .iter()
        .filter(|(_, big)| {
            Some(*big) != system && rules::within_path(system, Some(big)).is_some()
        })
        .map(|(sign, _)| format!("x ∈ {sign}"))
        .collect();
    templates.extend(
        rules::implied(system)
            .iter()
            .map(|(said, _)| said.to_string()),
    );
    let mut local = sorts.clone();
    local.insert("x".into(), Sort::of("number"));
    let mut put = Binding::new();
    put.insert("x".into(), term);
    templates
        .iter()
        .map(|t| substitute(&template(t, env, &local), &put))
        .collect()
}
