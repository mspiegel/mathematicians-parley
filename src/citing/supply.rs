//! Whether a citation's facts supply the patterns an item asks for.

use std::borrow::Cow;
use std::collections::BTreeSet;
use std::sync::atomic::{AtomicUsize, Ordering};

use indexmap::{IndexMap, IndexSet};

use crate::formula::{Node, NodeId};
use crate::matching::{
    alike, match_tree, substitute_apart, Binding, Context, PROPERTY,
};
use crate::rules;

use super::library::{either_way, Library};

/// The places in a pattern where a binder applies a property or a function to
/// what it binds, which decide what the property or function stands for
/// (`matching::binding_sites`).
pub type Sites = IndexSet<NodeId>;

/// Every name the trees use.
pub fn names_of(trees: &[Node]) -> BTreeSet<String> {
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

/// The fact that states `pattern` under `binding`, the first one that does
/// in the facts' order, as the search takes it; None where none does, or
/// where the pattern needs no line.
pub fn supplier<'f>(
    pattern: &Node,
    facts: &'f [Node],
    binding: &Binding,
    variables: &BTreeSet<String>,
    library: &Library,
    sites: &Sites,
) -> Option<&'f Node> {
    let used = vec![false; facts.len()];
    fits(
        pattern, facts, &used, binding, variables, library, sites, true,
    )
    .into_iter()
    .find_map(|fit| fit.fact)
    .map(|i| &facts[i])
}

/// A search asked for every way the facts supply the hypotheses, rather
/// than the first: the facts the attempt in hand has taken, by index, and
/// what to do with each way once it is complete, given the facts it took
/// and the binding it supplied them under.
pub struct Ways<'v> {
    pub path: Vec<usize>,
    pub found: &'v mut dyn FnMut(&[usize], &Binding),
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
pub fn search(
    patterns: &[Node],
    facts: &[Node],
    used: &mut Vec<bool>,
    binding: &Binding,
    variables: &BTreeSet<String>,
    library: &Library,
    sites: &Sites,
    reuse: bool,
    ways: Option<&mut Ways>,
) -> Option<Binding> {
    let patterns: Vec<&Node> = patterns.iter().collect();
    let mut asked = 0;
    let out = searched(
        &patterns, facts, used, binding, variables, library, sites, reuse, ways,
        &mut asked,
    );
    LARGEST.fetch_max(asked, Ordering::Relaxed);
    out
}

/// The most hypotheses one search has tried to supply, counting each time
/// one is asked again under another binding, over every search this process
/// has made.
static LARGEST: AtomicUsize = AtomicUsize::new(0);

/// The size of the largest search this process has made: how many times it
/// asked a hypothesis of the facts.
pub fn largest_search() -> usize {
    LARGEST.load(Ordering::Relaxed)
}

/// A candidate the search has tried for one hypothesis: the fact it takes,
/// by its shape, and the binding it leaves, each value by its shape.
#[derive(PartialEq)]
struct Tried {
    fact: Option<String>,
    binding: Vec<String>,
}

/// `search` over the hypotheses still to supply, counting in `asked` each
/// one it takes up.
///
/// It takes up the hypothesis the fewest facts fit, as the binding stands.
/// A hypothesis asked while its letters are open fits every fact of its
/// shape, `k ∈ ℕ` every fact putting a number in ℕ, and taken first it
/// multiplies the search by those facts, while one that nothing fits is
/// found out only after every arrangement of them: a step citing the wrong
/// line for six letters ran for hours in written order. Taken last, the
/// open hypothesis is a closed fact, looked up, and the one nothing fits
/// ends the search at once.
///
/// That a hypothesis nothing fits ends the search holds where fixing more
/// letters only narrows what fits it (`settled`). One that can be fitted
/// more ways once letters are fixed is taken up only when no other is left,
/// in written order.
#[allow(clippy::too_many_arguments)]
fn searched(
    patterns: &[&Node],
    facts: &[Node],
    used: &mut Vec<bool>,
    binding: &Binding,
    variables: &BTreeSet<String>,
    library: &Library,
    sites: &Sites,
    reuse: bool,
    mut ways: Option<&mut Ways>,
    asked: &mut usize,
) -> Option<Binding> {
    if patterns.is_empty() {
        if let Some(ways) = ways {
            (ways.found)(&ways.path, binding);
            return None;
        }
        return Some(binding.clone());
    }
    *asked += 1;
    let fitting = |p: &Node, used: &[bool]| {
        fits(p, facts, used, binding, variables, library, sites, reuse)
    };
    let mut fewest: Option<(usize, Vec<Fit>)> = None;
    for (at, p) in patterns.iter().enumerate() {
        if !settled(p, binding, variables, library) {
            continue;
        }
        let these = fitting(p, used);
        if these.is_empty() {
            return None;
        }
        if fewest.as_ref().is_none_or(|(_, f)| these.len() < f.len()) {
            fewest = Some((at, these));
        }
    }
    let (at, these) = match fewest {
        Some(f) => f,
        None => (0, fitting(patterns[0], used)),
    };
    let rest: Vec<&Node> = patterns
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != at)
        .map(|(_, p)| *p)
        .collect();
    // A fact stated twice among the facts, by a line and by the parts of
    // another, fits as two candidates that bind alike; the search below
    // each is the same, and a way is told by the facts it takes, so only
    // the first is tried. Thirty hypotheses with two copies each are 2^30
    // ways otherwise, which a graph given in full asks.
    let mut tried: Vec<Tried> = Vec::new();
    for fit in these {
        let key = Tried {
            fact: fit.fact.map(|i| facts[i].shape().to_string()),
            binding: fit
                .binding
                .iter()
                .map(|(k, v)| format!("{k} := {}", v.shape()))
                .collect(),
        };
        if tried.contains(&key) {
            continue;
        }
        tried.push(key);
        if let (true, Some(i)) = (fit.takes, fit.fact) {
            used[i] = true;
        }
        // A fact that supplies a hypothesis is one the way uses, taken for
        // the hypotheses after it or not.
        if let (Some(ways), Some(i)) = (ways.as_deref_mut(), fit.fact) {
            ways.path.push(i);
        }
        let done = searched(
            &rest,
            facts,
            used,
            &fit.binding,
            variables,
            library,
            sites,
            reuse,
            ways.as_deref_mut(),
            asked,
        );
        if let (Some(ways), Some(_)) = (ways.as_deref_mut(), fit.fact) {
            ways.path.pop();
        }
        if let (true, Some(i)) = (fit.takes, fit.fact) {
            used[i] = false;
        }
        if done.is_some() {
            return done;
        }
    }
    None
}

/// Whether fixing more letters can only narrow what fits a hypothesis, so
/// that one nothing fits now is one nothing will.
///
/// Three readings widen as letters are fixed. A property applied, `P(a)`,
/// is the formula P stands for once another hypothesis has said what that
/// is, and the formula may be a "there is" an instance gives. A "for all"
/// is read over a smaller domain once its letters are fixed (`narrowed`).
/// A "there is" whose body is an equation is met by no line once one side
/// is closed (`self_evident`). A hypothesis with none of these, or with
/// every letter fixed, is matched as it is written.
fn settled(
    pattern: &Node,
    binding: &Binding,
    variables: &BTreeSet<String>,
    library: &Library,
) -> bool {
    if all_bound(pattern, variables, binding) {
        return true;
    }
    let applied = library.ctx.props.contains_key(&pattern.notation)
        && pattern.children.len() == 2
        && pattern.children[0].is_name();
    !(applied
        || pattern.notation == "for-all"
        || library.exists.contains(&pattern.notation))
}

/// One way a fact supplies a hypothesis: the binding it is supplied under,
/// the fact by its index (none where the hypothesis needs no line), and
/// whether the fact is taken from the hypotheses after it.
struct Fit {
    fact: Option<usize>,
    binding: Binding,
    takes: bool,
}

/// Every way the facts `used` does not mark supply one hypothesis under the
/// binding, in the order they are tried.
#[allow(clippy::too_many_arguments)]
fn fits(
    first: &Node,
    facts: &[Node],
    used: &[bool],
    binding: &Binding,
    variables: &BTreeSet<String>,
    library: &Library,
    sites: &Sites,
    reuse: bool,
) -> Vec<Fit> {
    let mut out = Vec::new();
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
                // The argument is read through the binding whole: P(k + 1)
                // with k bound to o asks the property of o + 1.
                let terms: Binding = binding
                    .iter()
                    .filter(|(_, t)| t.notation != PROPERTY)
                    .map(|(v, t)| (v.clone(), t.clone()))
                    .collect();
                let arg = substitute_apart(&first.children[1], &terms, ctx);
                let mut at = Binding::new();
                at.insert(stands.text.clone(), arg.clone());
                first = substitute_apart(&stands.children[0], &at, ctx);
                // The formula a property stands for is the step's own, so a
                // name in it is the step's, even spelt as one of the item's.
                // Only a letter of the argument still to be matched is the
                // item's to fill.
                let unbound: BTreeSet<String> = arg
                    .names()
                    .iter()
                    .map(|n| n.to_string())
                    .filter(|n| variables.contains(n) && !binding.contains_key(n))
                    .collect();
                open_names = Cow::Owned(unbound);
            }
        }
    }
    // An equation whose two sides are one once the binding is put in needs
    // no line (`SYNTAX.md`, "An identity element goes without saying"):
    // |X| = m at X := A and m := |A|.
    if ctx.equations.contains(&first.notation)
        && first.children.len() == 2
        && all_bound(&first, variables, binding)
    {
        let terms: Binding = binding
            .iter()
            .filter(|(_, t)| t.notation != PROPERTY)
            .map(|(v, t)| (v.clone(), t.clone()))
            .collect();
        let put = |side: &Node| substitute_apart(side, &terms, ctx);
        let none = IndexMap::new();
        if alike(
            &put(&first.children[0]),
            &put(&first.children[1]),
            ctx,
            &none,
            &none,
        ) {
            out.push(Fit {
                fact: None,
                binding: binding.clone(),
                takes: false,
            });
        }
    }
    // An equation, or the denial of one, is searched for each way round
    // (`either_way`): which way the hypothesis is read is decided by the
    // hypotheses after it as much as by the fact it is matched with.
    for first in either_way(&first, library) {
        let mut body_form: Option<(Node, BTreeSet<String>)> = None;
        if library.exists.contains(&first.notation) && first.children.len() > 2 {
            let (pairs, body) = existential_levels(&first, library);
            let mut seen = open_names.as_ref().clone();
            for (name, _) in pairs {
                if name.is_name() {
                    seen.insert(name.text.clone());
                }
            }
            body_form = Some((body.clone(), seen));
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
                    if let Some(smaller) = narrowed(&first, fact, binding, ctx) {
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
                let pinned = *pinned
                    .get_or_insert_with(|| all_bound(&first, variables, binding));
                out.push(Fit {
                    fact: Some(i),
                    binding: found,
                    takes: !(reuse || pinned),
                });
            }
        }
        // An equation the body asks whose one side names no open letter is
        // the same on both sides once the witnesses are read off the other,
        // and needs no line (`SYNTAX.md`, the literal-instance rule):
        // t = a·m + b·n at t := a·x + b·y is met by m := x and n := y.
        if let Some((body, seen)) = &body_form {
            if let Some(same) = self_evident(body, binding, seen, ctx) {
                if let Some(found) = match_tree(body, &same, binding, seen, sites, ctx)
                {
                    let remaining: Vec<Node> = facts
                        .iter()
                        .zip(used.iter())
                        .filter(|(_, u)| !**u)
                        .map(|(f, _)| f.clone())
                        .collect();
                    if witnessed_in(&first, &found, &remaining, seen, library, sites) {
                        out.push(Fit {
                            fact: None,
                            binding: found,
                            takes: false,
                        });
                    }
                }
            }
        }
    }
    // An equation the item asks outright is met the same way, after every
    // fact: `a mod m = r` at m := 3 and r := x mod 3 is x mod 3 = x mod 3
    // with a := x, which needs no line.
    if let Some(same) = self_evident(&first, binding, &open_names, ctx) {
        if let Some(found) = match_tree(&first, &same, binding, &open_names, sites, ctx)
        {
            out.push(Fit {
                fact: None,
                binding: found,
                takes: false,
            });
        }
    }
    out
}

/// The equation L = L, where `body` is an equation one side of which, L
/// under the binding, names no letter still open; else None.
fn self_evident(
    body: &Node,
    binding: &Binding,
    open: &BTreeSet<String>,
    ctx: &Context,
) -> Option<Node> {
    if !ctx.equations.contains(&body.notation) || body.children.len() != 2 {
        return None;
    }
    let closed = |side: &Node| {
        side.names()
            .iter()
            .all(|n| !open.contains(n.as_str()) || binding.contains_key(n.as_str()))
    };
    let side = body.children.iter().find(|s| closed(s))?;
    if body.children.iter().all(closed) {
        return None;
    }
    let terms: Binding = binding
        .iter()
        .filter(|(_, t)| t.notation != PROPERTY)
        .map(|(v, t)| (v.clone(), t.clone()))
        .collect();
    let spelt = substitute_apart(side, &terms, ctx);
    Some(Node::new(
        &body.notation,
        body.sort.clone(),
        vec![spelt.clone(), spelt],
        &body.text,
    ))
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
fn narrowed(
    pattern: &Node,
    fact: &Node,
    binding: &Binding,
    ctx: &Context,
) -> Option<Node> {
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
    let asked = substitute_apart(&pattern.children[1], &terms, ctx);
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

/// The names a "there is" binds, each with its domain, outermost first, and
/// the body they are said of. A "there is" holds its body last and names its
/// variable and domain before it; one whose body is a "there is" again, as
/// "there are m, n ∈ ℤ with …" builds, binds each in turn, so a "there is"
/// of several names is read the same way as one of one.
fn existential_levels<'n>(
    exists: &'n Node,
    library: &Library,
) -> (Vec<(&'n Node, &'n Node)>, &'n Node) {
    let mut pairs = Vec::new();
    let mut body = exists;
    while library.exists.contains(&body.notation) && body.children.len() == 3 {
        pairs.push((&body.children[0], &body.children[1]));
        body = &body.children[2];
    }
    (pairs, body)
}

/// Whether `fact` says `value : X → Y`, where `domain` is the functions from
/// X to Y: what "there is f : X → Y with …" runs over is that set, and the
/// line naming its witness, as an obtain from it does, says the function's
/// type (`there-is-function`).
fn typed_into(
    fact: &Node,
    value: &Node,
    domain: &Node,
    binding: &Binding,
    variables: &BTreeSet<String>,
    library: &Library,
    sites: &Sites,
) -> bool {
    let ([from, to], [f, x, y]) =
        (domain.children.as_slice(), fact.children.as_slice())
    else {
        return false;
    };
    if domain.notation != "functions-from"
        || fact.notation != "function-type"
        || f.shape() != value.shape()
    {
        return false;
    }
    let ctx = &library.ctx;
    match_tree(from, x, binding, variables, sites, ctx)
        .and_then(|at| match_tree(to, y, &at, variables, sites, ctx))
        .is_some()
}

/// Whether one of the facts puts each value a "there is" was given in the
/// domain it ranges over.
fn witnessed_in(
    exists: &Node,
    binding: &Binding,
    facts: &[Node],
    variables: &BTreeSet<String>,
    library: &Library,
    sites: &Sites,
) -> bool {
    let (pairs, _) = existential_levels(exists, library);
    for (name, domain) in pairs {
        if !name.is_name() {
            continue;
        }
        let Some(value) = binding.get(&name.text) else {
            return false;
        };
        let witnessed = facts.iter().any(|f| {
            let member = library.members.contains(&f.notation)
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
                .is_some();
            member || typed_into(f, value, domain, binding, variables, library, sites)
        });
        if !witnessed {
            return false;
        }
    }
    true
}
