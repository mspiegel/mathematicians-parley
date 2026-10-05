//! Matching an item's hypothesis against the fact a step supplies for it.
//!
//! The match is one-way: the item is a pattern whose names stand for
//! anything, and the fact is ground. `mun:stdlib/sets/subset-transitive`
//! assumes X ⊆ Y and Y ⊆ Z, and a step citing it from two lines claiming
//! S ⊆ [a, b] and [a, b] ⊆ ℝ supplies them with X, Y, Z standing for S,
//! [a, b] and ℝ. A name that appears twice must stand for the same thing
//! both times, which is what makes the middle Y load-bearing.
//!
//! A citation may write its instantiation, and the written pairs seed the
//! binding, so they are checked rather than trusted; a citation that writes
//! none is read the same way.

use std::collections::BTreeSet;

use indexmap::{IndexMap, IndexSet};

use crate::corpus::{Record, RecordKind};
use crate::formula::{Binds, Node, NodeId, Notation};
use crate::regex;

// An instantiation value may itself contain a comma, as `e := gcd(a, b)`
// does, so the list is split at the commas that sit outside brackets rather
// than by a pattern that stops at the first one.
regex!(ASSIGN, r"^([^\s,]+)\s*:=\s*(.+)");
regex!(
    INSTANTIATION_END,
    format!(
        r",\s*from\b|\s+in\s+(?:line\b|{}|[A-Z]+[0-9]*\b)",
        crate::corpus::ITEM_PREFIX
    )
);
regex!(
    INSTANTIATION_HEAD,
    format!(
        r"^(?:{}[^\s]+\s*|instantiate\s+)",
        crate::corpus::ITEM_PREFIX
    )
);

/// The `v := t` pairs of a justification, in order.
pub fn instantiation(text: &str) -> Vec<(String, String)> {
    // An `instantiate` says where it lands, and that is a line, an item or a
    // bare label — the three the reader takes for the target. A value stops
    // at whichever of them follows it, and `IH` is a label.
    let mut body = match INSTANTIATION_END.find(text) {
        Some(m) => &text[..m.start()],
        None => text,
    };
    if let Some(head) = INSTANTIATION_HEAD.find(body) {
        body = &body[head.end()..];
    }
    let mut out = Vec::new();
    for piece in split_commas(body) {
        if let Some(m) = ASSIGN.captures(str::trim(piece)) {
            out.push((str::trim(&m[1]).to_string(), str::trim(&m[2]).to_string()));
        }
    }
    out
}

/// Split on the commas outside brackets.
pub fn split_commas(text: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth: i64 = 0;
    let mut start = 0;
    for (i, ch) in text.char_indices() {
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => {
                out.push(&text[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(&text[start..]);
    out.into_iter()
        .filter(|p| !str::trim(p).is_empty())
        .collect()
}

/// What a property stands for: a formula with one name marked as its hole.
/// This notation is never parsed from anything; it exists only inside a
/// binding.
pub const PROPERTY: &str = "property-of";

/// What the names of a pattern have been matched to.
pub type Binding = IndexMap<String, Node>;

/// What a match needs to know of the notations: which bind a variable,
/// which apply a property or a function, and which are equations.
#[derive(Clone, Debug, Default)]
pub struct Context {
    pub binders: IndexMap<String, Binds>,
    /// For each application, whether it applies a `property` or a
    /// `function`.
    pub props: IndexMap<String, String>,
    pub equations: IndexSet<String>,
    /// The notations saying a function is a function on a set (`wfn`).
    pub functions_on: IndexSet<String>,
    /// The notations writing a sum (`csu`).
    pub sums: IndexSet<String>,
}

impl Context {
    pub fn new(notations: &[Notation], records: &[Record]) -> Context {
        let (binders, props) = binding_context(notations);
        Context {
            binders,
            props,
            equations: equations(records),
            functions_on: functions_on(records),
            sums: sums(records),
        }
    }

    /// The places of a binder that hold the letters it binds, and those of
    /// the body they are bound in; neither for a notation that binds none.
    pub fn held_body(&self, notation: &str) -> (Vec<usize>, Vec<usize>) {
        match self.binders.get(notation) {
            Some(b) => (b.held.clone(), b.body.clone()),
            None => (Vec::new(), Vec::new()),
        }
    }
}

/// Which notations bind a variable, and which apply a property or a
/// function.
///
/// Both are read from the declarations: a binder is a notation with a
/// `binds` line, and an application is one whose first hole takes a property
/// or a function and whose second takes what that applies to. The second map
/// says which of the two each applies, because a function is read as a
/// family only where a binder applies it to what it binds. Nothing here is
/// known by name.
pub fn binding_context(
    notations: &[Notation],
) -> (IndexMap<String, Binds>, IndexMap<String, String>) {
    let mut binders = IndexMap::new();
    let mut props = IndexMap::new();
    for n in notations {
        if let Some(first) = n.holes.first() {
            if (first == "property" || first == "function") && applies_first(n) {
                props.insert(n.key().to_string(), first.clone());
            }
        }
        if let Some(b) = n.node_binds() {
            binders.insert(n.key().to_string(), b);
        }
    }
    (binders, props)
}

/// The notation's second hole takes what its first applies to: `f(x)` puts
/// an α where f is a function from α, and `P(x)` where P is a property of
/// α. `f is a function on X` and `f : X → Y` take a set of α there, and say
/// something of f rather than apply it.
fn applies_first(n: &Notation) -> bool {
    let Some(sort) = &n.sort else {
        return false;
    };
    let Some((holes, _)) = sort.rsplit_once(" → ") else {
        return false;
    };
    let holes: Vec<&str> = holes.split(", ").map(str::trim).collect();
    let domain = holes[0]
        .strip_prefix("function from ")
        .and_then(|rest| rest.split_once(" to "))
        .map(|(from, _)| from)
        .or_else(|| holes[0].strip_prefix("property of "));
    domain.is_some() && holes.get(1).copied() == domain
}

/// The occurrences of a property that may decide what it stands for.
///
/// Only one may: the occurrence inside the braces, applied to the very
/// variable the braces bind. There the answer is forced, because a property
/// is introduced before the braces open and so cannot mention what they
/// bind, and every occurrence of that variable in the condition must
/// therefore be the hole. An occurrence outside is applied to an ordinary
/// name the property is allowed to mention, where several readings would
/// fit, so it is checked against what the inside one decided and never
/// allowed to decide.
pub fn binding_sites(
    pattern: &Node,
    ctx: &Context,
    bound: &[String],
    out: &mut IndexSet<NodeId>,
) {
    if ctx.props.contains_key(&pattern.notation)
        && pattern.children.len() == 2
        && pattern.children[1].is_name()
        && bound.contains(&pattern.children[1].text)
    {
        out.insert(pattern.id());
    }
    let (held, body) = ctx.held_body(&pattern.notation);
    let own: Vec<String> = held
        .iter()
        .filter(|&&at| pattern.children[at].is_name())
        .map(|&at| pattern.children[at].text.clone())
        .collect();
    for (i, child) in pattern.children.iter().enumerate() {
        if body.contains(&i) {
            let mut inner = bound.to_vec();
            inner.extend(own.iter().cloned());
            binding_sites(child, ctx, &inner, out);
        } else {
            binding_sites(child, ctx, bound, out);
        }
    }
}

regex!(WCEQ, r"^wceq\b");

/// The notations that are equations, taken from what they target in the
/// kernel, `wceq`, rather than named here. An equation's two sides say the
/// same read either way round (`SYNTAX.md`).
pub fn equations(records: &[Record]) -> IndexSet<String> {
    records
        .iter()
        .filter(|r| {
            r.kind == RecordKind::Notation
                && WCEQ.is_match(str::trim(r.field_or_empty("metamath")))
        })
        .map(|r| r.name.clone())
        .collect()
}

/// The notations whose `metamath` is set.mm's `Fn`: what a define with a
/// parameter says of its function.
pub fn functions_on(records: &[Record]) -> IndexSet<String> {
    records
        .iter()
        .filter(|r| {
            r.kind == RecordKind::Notation
                && str::trim(r.field_or_empty("metamath")) == "wfn"
        })
        .map(|r| r.name.clone())
        .collect()
}

/// The notations whose `metamath` is set.mm's `csu`, a sum over some range.
pub fn sums(records: &[Record]) -> IndexSet<String> {
    records
        .iter()
        .filter(|r| {
            r.kind == RecordKind::Notation
                && str::trim(r.field_or_empty("metamath")).starts_with("csu ")
        })
        .map(|r| r.name.clone())
        .collect()
}

/// The ways b's parts may stand against a's: as written, and turned round
/// where a is an equation.
pub fn orders(a: &Node, b: &Node, equations: &IndexSet<String>) -> Vec<Vec<Node>> {
    if equations.contains(&a.notation) && b.children.len() == 2 {
        let mut turned = b.children.clone();
        turned.reverse();
        return vec![b.children.clone(), turned];
    }
    vec![b.children.clone()]
}

/// Bind the pattern's variables so that it becomes the ground tree.
///
/// Returns the binding, or None where the pattern does not fit. Two trees
/// are compared up to the letters they bind and the order of an equation's
/// sides (`alike`), and a binder of the pattern's may take the ground's
/// letter (`bound_as`).
pub fn match_tree(
    pattern: &Node,
    ground: &Node,
    binding: &Binding,
    variables: &BTreeSet<String>,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
) -> Option<Binding> {
    // Most matches are refused at the root, by a notation that differs, and
    // the binding is copied only for one that is not.
    if refused_at_root(pattern, ground, variables, ctx) {
        return None;
    }
    let mut out = binding.clone();
    fit(pattern, ground, &mut out, variables, sites, ctx).then_some(out)
}

/// The pattern is one of the variables being bound.
fn is_variable(pattern: &Node, variables: &BTreeSet<String>) -> bool {
    pattern.is_name() && variables.contains(&pattern.text)
}

/// The pattern applies a property or function that is one of the variables.
fn applies_variable(
    pattern: &Node,
    variables: &BTreeSet<String>,
    ctx: &Context,
) -> bool {
    ctx.props.contains_key(&pattern.notation)
        && pattern.children.len() == 2
        && pattern.children[0].is_name()
        && variables.contains(&pattern.children[0].text)
}

/// The two nodes differ in what they are, so no binding makes one the other.
fn differs(pattern: &Node, ground: &Node) -> bool {
    pattern.notation != ground.notation
        || pattern.text != ground.text
        || pattern.children.len() != ground.children.len()
}

/// `fit` would give back false at the root without looking at the binding.
fn refused_at_root(
    pattern: &Node,
    ground: &Node,
    variables: &BTreeSet<String>,
    ctx: &Context,
) -> bool {
    !is_variable(pattern, variables)
        && !applies_variable(pattern, variables, ctx)
        && differs(pattern, ground)
}

/// `match_tree` into one binding, growing it in place.
///
/// Matching only ever adds a variable the binding does not have, and adds it
/// at the end, so an attempt that fails is undone by cutting the binding
/// back to the length it had before. Copying the binding at every node of
/// every attempt instead measured at a quarter of a check. When this gives
/// back false, the binding is as it was.
fn fit(
    pattern: &Node,
    ground: &Node,
    binding: &mut Binding,
    variables: &BTreeSet<String>,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
) -> bool {
    if is_variable(pattern, variables) {
        if let Some(seen) = binding.get(&pattern.text) {
            return alike(seen, ground, ctx, &IndexMap::new(), &IndexMap::new());
        }
        binding.insert(pattern.text.clone(), ground.clone());
        return true;
    }
    if applies_variable(pattern, variables, ctx) {
        if ctx.props.get(&pattern.notation).map(String::as_str) != Some("function") {
            return property(pattern, ground, binding, sites, ctx);
        }
        if let Some(fits) = family(pattern, ground, binding, sites, ctx) {
            return fits;
        }
    }
    if differs(pattern, ground) {
        return false;
    }
    let pattern = bound_as(pattern, ground, variables, ctx);
    let before = binding.len();
    for children in orders(&pattern, ground, &ctx.equations) {
        let all = pattern
            .children
            .iter()
            .zip(children.iter())
            .all(|(a, b)| fit(a, b, binding, variables, sites, ctx));
        if all {
            return true;
        }
        binding.truncate(before);
    }
    false
}

/// The pattern with the letter it binds spelt as the ground spells it,
/// where the letter is no variable of the pattern's and the ground's letter
/// is free nowhere in it; the pattern as it is otherwise.
///
/// A definition's formula read at a term binds a letter of its own, and a
/// line saying the same thing may bind another: `there is b ∈ G with gH =
/// bH` answers K's `there is g ∈ G with X = gH` at X := gH.
fn bound_as(
    pattern: &Node,
    ground: &Node,
    variables: &BTreeSet<String>,
    ctx: &Context,
) -> Node {
    let (held, body) = ctx.held_body(&pattern.notation);
    let mut pattern = pattern.clone();
    for at in held {
        let ours = pattern.children[at].clone();
        let theirs = ground.children[at].clone();
        if !ours.is_name()
            || !theirs.is_name()
            || ours.text == theirs.text
            || variables.contains(&ours.text)
            || pattern.names().contains(&theirs.text)
        {
            continue;
        }
        let mut swap = Binding::new();
        swap.insert(ours.text.clone(), theirs.clone());
        let children = pattern
            .children
            .iter()
            .enumerate()
            .map(|(i, c)| {
                if i == at {
                    theirs.clone()
                } else if body.contains(&i) {
                    substitute(c, &swap)
                } else {
                    c.clone()
                }
            })
            .collect();
        pattern = Node::new(
            &pattern.notation,
            pattern.sort.clone(),
            children,
            &pattern.text,
        );
    }
    pattern
}

/// Whether two trees are one formula, spelt alike but for the letters they
/// bind: `there is a ∈ G with Z = aH` and `there is b ∈ G with Z = bH` are
/// one claim, and neither says anything of a or of b.
///
/// A letter one of them binds is paired with the letter the other binds in
/// the same place, and a free letter must be the same letter on both sides,
/// never one the other side binds. An equation is alike either way round
/// (`orders`).
pub fn alike(
    a: &Node,
    b: &Node,
    ctx: &Context,
    ours: &IndexMap<String, String>,
    theirs: &IndexMap<String, String>,
) -> bool {
    if a.is_name() && b.is_name() {
        if ours.contains_key(&a.text) || theirs.contains_key(&b.text) {
            return ours.get(&a.text) == Some(&b.text)
                && theirs.get(&b.text) == Some(&a.text);
        }
        return a.text == b.text;
    }
    if a.notation != b.notation
        || a.text != b.text
        || a.children.len() != b.children.len()
    {
        return false;
    }
    let Some(shape) = ctx.binders.get(&a.notation) else {
        return orders(a, b, &ctx.equations).iter().any(|kids| {
            a.children
                .iter()
                .zip(kids.iter())
                .all(|(x, y)| alike(x, y, ctx, ours, theirs))
        });
    };
    let pairs: Vec<(&Node, &Node)> = shape
        .held
        .iter()
        .map(|&at| (&a.children[at], &b.children[at]))
        .collect();
    if pairs.iter().any(|(x, y)| !x.is_name() || !y.is_name()) {
        return a.shape() == b.shape();
    }
    let mut inner_ours = ours.clone();
    let mut inner_theirs = theirs.clone();
    for (x, y) in &pairs {
        inner_ours.insert(x.text.clone(), y.text.clone());
    }
    for (x, y) in &pairs {
        inner_theirs.insert(y.text.clone(), x.text.clone());
    }
    a.children
        .iter()
        .zip(b.children.iter())
        .enumerate()
        .all(|(i, (p, q))| {
            if shape.held.contains(&i) {
                return true;
            }
            if shape.body.contains(&i) {
                alike(p, q, ctx, &inner_ours, &inner_theirs)
            } else {
                alike(p, q, ctx, ours, theirs)
            }
        })
}

/// Whether two trees are one formula, compared from the top.
pub fn alike_top(a: &Node, b: &Node, ctx: &Context) -> bool {
    alike(a, b, ctx, &IndexMap::new(), &IndexMap::new())
}

/// P applied to something, where P is one of the pattern's variables.
fn property(
    pattern: &Node,
    ground: &Node,
    binding: &mut Binding,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
) -> bool {
    let name = &pattern.children[0].text;
    let arg = read_at(&pattern.children[1], binding);
    let Some(stands) = binding.get(name) else {
        if !sites.contains(&pattern.id()) || !arg.is_name() {
            return false; // only the inside occurrence decides
        }
        binding.insert(
            name.clone(),
            Node::new(
                PROPERTY,
                crate::formula::Sort::of("property"),
                vec![ground.clone()],
                &arg.text,
            ),
        );
        return true;
    };
    if stands.notation != PROPERTY {
        return false;
    }
    let mut at = Binding::new();
    at.insert(stands.text.clone(), arg);
    let filled = substitute_apart(&stands.children[0], &at, ctx);
    alike_top(&filled, ground, ctx)
}

/// What a property or a function is applied to, in the ground's terms.
///
/// Every name in it the match has bound is what it was bound to: an item's
/// `t(n + 1)` asks of the step's summand at m + 1 where n is m, and its
/// `t(k − c)` at k − 1 where c is 1. What is bound to a property is not a
/// term, and is left alone.
fn read_at(arg: &Node, binding: &Binding) -> Node {
    let terms: Binding = binding
        .iter()
        .filter(|(_, t)| t.notation != PROPERTY)
        .map(|(v, t)| (v.clone(), t.clone()))
        .collect();
    substitute(arg, &terms)
}

/// t applied to something, where t is a function the pattern names.
///
/// Under a binder that applies it to what it binds, t is whatever is summed
/// or said there, read as a term with that variable as its hole: an item
/// summing t(k) over k is about d(k)·10^k − d(k) when that is the step's
/// summand. It is read so only where the term is not itself a function
/// applied to the variable, since there t is simply that function, and the
/// item's other mentions of t, which are not applications, still name it.
///
/// Gives back whether the match fits, where this decides it, growing the
/// binding where it fits; None where it does not decide, and the
/// application is matched as it stands.
fn family(
    pattern: &Node,
    ground: &Node,
    binding: &mut Binding,
    sites: &IndexSet<NodeId>,
    ctx: &Context,
) -> Option<bool> {
    let name = &pattern.children[0].text;
    let arg = read_at(&pattern.children[1], binding);
    let stands = binding.get(name);
    if let Some(stands) = stands {
        if stands.notation == PROPERTY {
            let mut at = Binding::new();
            at.insert(stands.text.clone(), arg);
            let filled = substitute_apart(&stands.children[0], &at, ctx);
            return Some(alike_top(&filled, ground, ctx));
        }
    }
    let plain = ground.notation == pattern.notation
        && ground.children.len() == 2
        && ground.children[1].shape() == arg.shape();
    if stands.is_none() && sites.contains(&pattern.id()) && arg.is_name() && !plain {
        binding.insert(
            name.clone(),
            Node::new(
                PROPERTY,
                crate::formula::Sort::of("property"),
                vec![ground.clone()],
                &arg.text,
            ),
        );
        return Some(true);
    }
    None
}

/// What a define with arguments stands for: `define S(m) := …` is a
/// function, and S(t) is its body with t for m; `define G(a, n) := …` is a
/// function of two, and G(s, t) is its body with s for a and t for n.
#[derive(Clone, Debug)]
pub struct Rule {
    /// The arguments, in the order the name takes them, each with its
    /// domain.
    pub params: Vec<crate::corpus::Param>,
    pub body: Node,
}

impl Rule {
    /// The rule with `values` put for its arguments, in order; None where
    /// the count differs.
    pub fn at(&self, values: &[Node]) -> Option<Node> {
        if values.len() != self.params.len() {
            return None;
        }
        let mut put = Binding::new();
        for (p, v) in self.params.iter().zip(values) {
            put.insert(p.name.clone(), v.clone());
        }
        Some(substitute(&self.body, &put))
    }
}

/// What a defined name stands for: a term, or a function's rule.
#[derive(Clone, Debug)]
pub enum Defined {
    Term(Node),
    Rule(Rule),
}

pub type Definitions = IndexMap<String, Defined>;

/// The tree with every defined name replaced by the term it names.
///
/// A define abbreviates and asserts nothing, so the two are one formula when
/// two formulas are compared: a step claiming `𝒫X = U ∪ T` and a theorem
/// concluding the same thing with the sets written out say the same thing. A
/// define may be written in terms of an earlier one, so this repeats, and
/// the depth is bounded because nothing stops a file naming something after
/// itself.
///
/// A defined function is read where it is applied: S(k + 1) is the rule with
/// k + 1 for its parameter. Standing alone it is the rule itself, a property
/// with the parameter as its hole, which is what an item's function letter
/// is bound to where the item applies it under a binder. So `f : S → S` and
/// every f(r) lying in S are about one thing, however each is written.
pub fn expand(node: &Node, definitions: &Definitions) -> Node {
    expand_to(node, definitions, 8)
}

fn expand_to(node: &Node, definitions: &Definitions, depth: i32) -> Node {
    if definitions.is_empty() || depth <= 0 {
        return node.clone();
    }
    if node.is_name() {
        match definitions.get(&node.text) {
            // A function of one argument standing alone is its rule, a
            // property with the argument as its hole. One of two has no such
            // reading, and its name stands as written.
            Some(Defined::Rule(rule)) if rule.params.len() == 1 => {
                return Node::new(
                    PROPERTY,
                    crate::formula::Sort::of("property"),
                    vec![expand_to(&rule.body, definitions, depth - 1)],
                    &rule.params[0].name,
                );
            }
            Some(Defined::Term(t)) => return expand_to(t, definitions, depth - 1),
            _ => {}
        }
    }
    if matches!(node.notation.as_str(), "application" | "application-to-two")
        && node.children.len() >= 2
        && node.children[0].is_name()
    {
        if let Some(Defined::Rule(rule)) = definitions.get(&node.children[0].text) {
            let values: Vec<Node> = node.children[1..]
                .iter()
                .map(|c| expand_to(c, definitions, depth))
                .collect();
            if let Some(at) = rule.at(&values) {
                return expand_to(&at, definitions, depth - 1);
            }
        }
    }
    if node.children.is_empty() {
        return node.clone();
    }
    Node::new(
        &node.notation,
        node.sort.clone(),
        node.children
            .iter()
            .map(|c| expand_to(c, definitions, depth))
            .collect(),
        &node.text,
    )
}

/// The tree with each bound name replaced by what it stands for.
pub fn substitute(node: &Node, binding: &Binding) -> Node {
    if node.notation == "name" || node.notation == "numeral" {
        return binding
            .get(&node.text)
            .cloned()
            .unwrap_or_else(|| node.clone());
    }
    Node::new(
        &node.notation,
        node.sort.clone(),
        node.children
            .iter()
            .map(|c| substitute(c, binding))
            .collect(),
        &node.text,
    )
}

/// Letters a binder is renamed to, where a value put under it would be
/// caught.
pub fn fresh_letters() -> Vec<String> {
    let mut out: Vec<String> = ('a'..='z').map(|c| c.to_string()).collect();
    out.extend(('a'..='z').map(|c| format!("{c}'")));
    out
}

/// `substitute`, keeping what a binder binds apart from what is put under
/// it: K's `there is g ∈ G with X = gH` at X := gH is `there is a ∈ G with
/// gH = aH`, and never `there is g ∈ G with gH = gH`, which catches the g of
/// gH and says something else. A binder whose letter a value mentions is
/// spelt with a letter nothing there uses; one naming a letter the binding
/// replaces keeps it, as the letter is its own inside.
pub fn substitute_apart(node: &Node, binding: &Binding, ctx: &Context) -> Node {
    if node.notation == "name" || node.notation == "numeral" {
        return binding
            .get(&node.text)
            .cloned()
            .unwrap_or_else(|| node.clone());
    }
    let (held, body) = ctx.held_body(&node.notation);
    if held.is_empty() || held.iter().any(|&at| !node.children[at].is_name()) {
        return Node::new(
            &node.notation,
            node.sort.clone(),
            node.children
                .iter()
                .map(|c| substitute_apart(c, binding, ctx))
                .collect(),
            &node.text,
        );
    }
    let own: BTreeSet<String> = held
        .iter()
        .map(|&at| node.children[at].text.clone())
        .collect();
    let inner: Binding = binding
        .iter()
        .filter(|(k, _)| !own.contains(*k))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let mut used = node.names();
    for v in binding.values() {
        used.extend(v.names());
    }
    let mut spelt: IndexMap<usize, Node> = IndexMap::new();
    let mut renamed = inner.clone();
    for &at in &held {
        let var = &node.children[at];
        if inner.values().any(|v| v.names().contains(&var.text)) {
            let letter = fresh_letters()
                .into_iter()
                .find(|c| !used.contains(c))
                .unwrap_or_default();
            let fresh = Node::leaf("name", var.sort.clone(), &letter);
            used.insert(letter);
            spelt.insert(at, fresh.clone());
            renamed.insert(var.text.clone(), fresh);
        }
    }
    let children = node
        .children
        .iter()
        .enumerate()
        .map(|(i, c)| {
            if held.contains(&i) {
                spelt.get(&i).cloned().unwrap_or_else(|| c.clone())
            } else if body.contains(&i) {
                substitute_apart(c, &renamed, ctx)
            } else {
                substitute_apart(c, binding, ctx)
            }
        })
        .collect();
    Node::new(&node.notation, node.sort.clone(), children, &node.text)
}
