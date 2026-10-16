//! A page tree as the kernel term the deciders read, made without set.mm.
//!
//! A notation's `target` is reverse Polish over set.mm's labels, and reading
//! reverse Polish needs each label's arity, which set.mm declares. The
//! deciders only look inside numbers and the operations on them, so a fixed
//! table gives the arity of those labels (`VOCABULARY`), and a target using
//! any other label is one atom: the decider treats it as it treats a letter.
//! `tests/vocabulary.rs` holds the table to set.mm.

use indexmap::IndexMap;
use num_bigint::BigUint;

use crate::formula::{Grammar, Node};
use crate::mm::kernel::Term;
use crate::targets;

use super::numerals::numeral_term;

/// The labels a decider reads, with how many terms each takes.
pub const VOCABULARY: &[(&str, usize)] = &[
    ("co", 3),
    ("caddc", 0),
    ("cmin", 0),
    ("cmul", 0),
    ("cdiv", 0),
    ("cexp", 0),
    ("cneg", 1),
    ("cdc", 2),
    ("wceq", 2),
    ("wne", 2),
    ("wn", 1),
    ("wa", 2),
    ("w3a", 3),
    ("wbr", 3),
    ("clt", 0),
    ("cle", 0),
    ("cdvds", 0),
    ("wcel", 2),
    ("cn", 0),
    ("cn0", 0),
    ("cz", 0),
    ("cq", 0),
    ("cr", 0),
    ("cc", 0),
    ("cmo", 0),
    ("csu", 3),
    ("cfz", 0),
    ("cpr", 2),
    ("ctp", 3),
    ("csn", 1),
    ("cun", 2),
    ("c0", 0),
    ("crab", 3),
    ("wral", 3),
    ("cfv", 2),
    ("cfa", 0),
    ("chash", 0),
    ("cprime", 0),
    ("cc0", 0),
    ("c1", 0),
    ("c2", 0),
    ("c3", 0),
    ("c4", 0),
    ("c5", 0),
    ("c6", 0),
    ("c7", 0),
    ("c8", 0),
    ("c9", 0),
];

/// What marks an atom's label, so that no atom reads as a label the
/// deciders know.
const ATOM: &str = "§";

/// The notations' targets, by notation and literal, as the build reads them
/// (`targets::terms`).
pub struct Targets {
    terms: IndexMap<String, Vec<Option<String>>>,
    literals: IndexMap<String, Vec<String>>,
    /// What each library function builds, by its name (`builds`).
    builds: IndexMap<String, String>,
    /// For a pattern a hole of which repeats, by its notation and literal:
    /// how many holes the pattern writes, and what each further one adds,
    /// `_ csn cun` for a list of four elements or more (`Repeat`).
    repeats: IndexMap<(String, String), Repeats>,
}

/// How a node holds more children than its pattern's holes: the holes the
/// pattern writes, and what each further child adds to the term the ones
/// before it built, `_` standing for that child.
struct Repeats {
    holes: usize,
    building: String,
}

/// An operation a term applies, read off its target: the label, `cmo`, and
/// the parts in the order its holes take them.
pub struct Operation<'n> {
    pub label: String,
    pub parts: Vec<&'n Node>,
}

impl Targets {
    pub fn of(g: &Grammar, records: &[crate::corpus::Record]) -> Targets {
        let mut literals: IndexMap<String, Vec<String>> = IndexMap::new();
        for n in &g.notations {
            literals
                .entry(n.name.clone())
                .or_default()
                .push(n.literal.clone());
        }
        let builds = g
            .functions
            .iter()
            .map(|(name, f)| (name.clone(), f.builds.clone()))
            .collect();
        let repeats = g
            .notations
            .iter()
            .filter_map(|n| {
                let r = n.repeat.as_ref()?;
                Some((
                    (n.key().to_string(), n.literal.clone()),
                    Repeats {
                        holes: n.holes.len(),
                        building: r.building.clone(),
                    },
                ))
            })
            .collect();
        Targets {
            terms: targets::terms(records),
            literals,
            builds,
            repeats,
        }
    }

    /// The operation `node` applies where its target, a notation's or a
    /// library function's, is set.mm's form of one, `_1 _2 OP co`: a mod b
    /// is `cmo` of a and b. None for any other term.
    pub fn operation<'n>(&self, node: &'n Node) -> Option<Operation<'n>> {
        // A library function's value is what its `builds` line makes; any
        // other term is what its notation's target makes.
        let applied =
            matches!(node.notation.as_str(), "application" | "application-to-two");
        let library = match node.children.as_slice() {
            [head, args @ ..] if applied && head.is_name() => {
                self.builds.get(&head.text).map(|b| (b.as_str(), args))
            }
            _ => None,
        };
        let (pattern, holes): (&str, &'n [Node]) = match library {
            Some(found) => found,
            None => (self.pattern(node)?, &node.children),
        };
        let [first, second, label, "co"] =
            pattern.split_whitespace().collect::<Vec<_>>().as_slice()[..]
        else {
            return None;
        };
        let hole = |t: &str| -> Option<&'n Node> {
            let at: usize = t.strip_prefix('_')?.parse().ok()?;
            holes.get(at.checked_sub(1)?)
        };
        Some(Operation {
            label: label.to_string(),
            parts: vec![hole(first)?, hole(second)?],
        })
    }

    /// The target of the pattern `node` was built from; None for a
    /// notation with none.
    fn pattern(&self, node: &Node) -> Option<&str> {
        let entries = self.terms.get(&node.notation)?;
        let at = self
            .literals
            .get(&node.notation)
            .and_then(|o| o.iter().position(|l| *l == node.text))
            .unwrap_or(0);
        entries.get(at)?.as_deref()
    }
}

/// `node` as a kernel term: numerals and the operations `VOCABULARY` holds
/// built out, and every other part, a letter included, one atom named by
/// how the page writes it.
pub fn term_of_node(node: &Node, targets: &Targets) -> Term {
    term_under(node, targets, &[])
}

/// `term_of_node` inside the finite sums that bind `indices`: an atom
/// holding one of them says so, its name followed by the index's own atom,
/// as set.mm's term holds the index's variable. So the summand a(k)·t of
/// Σ(k = 1 to n) is read as a part that holds k times one that does not,
/// which reading a sum as linear asks (`field::linear_sum`).
fn term_under(node: &Node, targets: &Targets, indices: &[&Node]) -> Term {
    if node.notation == "numeral" {
        if let Ok(value) = node.text.parse::<BigUint>() {
            return numeral_term(&value);
        }
    }
    if node.is_name() || node.literal.is_some() {
        return atom(node, indices);
    }
    let Some(pattern) = targets.pattern(node) else {
        return atom(node, indices);
    };
    // A sum's first hole is its index, which the rest are read inside.
    let mut inside: Vec<&Node> = indices.to_vec();
    if pattern.split_whitespace().any(|t| t == "csu") {
        if let Some(index) = node.children.first().filter(|i| i.is_name()) {
            inside.push(index);
        }
    }
    let holes: Vec<Term> = node
        .children
        .iter()
        .map(|c| term_under(c, targets, &inside))
        .collect();
    // A list longer than its pattern: the pattern's holes built, and each
    // further child added as the record's `repeats` says.
    let repeats = targets
        .repeats
        .get(&(node.notation.clone(), node.text.clone()))
        .filter(|r| holes.len() > r.holes);
    let made = match repeats {
        Some(r) => {
            let (written, further) = holes.split_at(r.holes);
            built(pattern, written).and_then(|start| {
                further
                    .iter()
                    .try_fold(start, |acc, child| built_onto(&r.building, &acc, child))
            })
        }
        None => built(pattern, &holes),
    };
    made.unwrap_or_else(|| atom(node, indices))
}

/// What a repeated hole's `building` makes of the term built so far and
/// one further child: `_ csn cun` joins `so_far` with the child's singleton.
fn built_onto(building: &str, so_far: &Term, child: &Term) -> Option<Term> {
    let mut stack = vec![so_far.clone()];
    for token in building.split_whitespace() {
        if token == "_" {
            stack.push(child.clone());
            continue;
        }
        let (_, arity) = VOCABULARY.iter().find(|(label, _)| *label == token)?;
        if stack.len() < *arity {
            return None;
        }
        let args = stack.split_off(stack.len() - arity);
        stack.push(Term::apply(token, args));
    }
    match stack.as_slice() {
        [one] => Some(one.clone()),
        _ => None,
    }
}

/// The atom a part of the page the deciders do not look inside stands as,
/// followed by the atom of each index in `indices` it holds and is not.
fn atom(node: &Node, indices: &[&Node]) -> Term {
    let mut name = format!("{ATOM}{}", node.shape());
    let names = node.names();
    for index in indices {
        let itself = node.is_name() && node.text == index.text;
        if !itself && names.contains(&index.text) {
            name.push(' ');
            name.push_str(&format!("{ATOM}{}", index.shape()));
        }
    }
    Term::apply(&name, Vec::new())
}

/// The term `pattern` builds with `holes` in it, where every label it uses
/// is one `VOCABULARY` holds; None where one is not.
fn built(pattern: &str, holes: &[Term]) -> Option<Term> {
    let mut stack: Vec<Term> = Vec::new();
    for token in pattern.split_whitespace() {
        if let Some(n) = token.strip_prefix('_') {
            let at: usize = n.parse().ok()?;
            stack.push(holes.get(at.checked_sub(1)?)?.clone());
            continue;
        }
        // A part of the structure a theorem is about, `@ends` the ends of its
        // graph's edges, is one term throughout the theorem, and an atom.
        if token.starts_with('@') {
            stack.push(Term::apply(token, Vec::new()));
            continue;
        }
        let (_, arity) = VOCABULARY.iter().find(|(label, _)| *label == token)?;
        if stack.len() < *arity {
            return None;
        }
        let args = stack.split_off(stack.len() - arity);
        stack.push(Term::apply(token, args));
    }
    match stack.as_slice() {
        [one] => Some(one.clone()),
        _ => None,
    }
}
