//! A page tree as the kernel term the deciders read, made without set.mm.
//!
//! A notation's `target` is reverse Polish over set.mm's labels, and reading
//! reverse Polish needs each label's arity, which set.mm declares. The
//! deciders only look inside numbers and the operations on them, so a fixed
//! table gives the arity of those labels (`VOCABULARY`), and a target using
//! any other label is one atom: the decider treats it as it treats a letter.
//! The gate's labels stage holds the table to set.mm (`tools::labels`).

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
        Targets {
            terms: targets::terms(records),
            literals,
            builds,
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

    /// Whether any part of `node` is built by a target that uses `label`:
    /// a part the deciders read, by labels `VOCABULARY` does not hold, as
    /// more than an atom (a finite sum, `csu`, read as linear).
    pub fn uses(&self, node: &Node, label: &str) -> bool {
        node.walk().iter().any(|part| {
            self.pattern(part)
                .is_some_and(|p| p.split_whitespace().any(|t| t == label))
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
    if node.notation == "numeral" {
        if let Ok(value) = node.text.parse::<BigUint>() {
            return numeral_term(&value);
        }
    }
    if node.is_name() || node.literal.is_some() {
        return atom(node);
    }
    let Some(pattern) = targets.pattern(node) else {
        return atom(node);
    };
    let holes: Vec<Term> = node
        .children
        .iter()
        .map(|c| term_of_node(c, targets))
        .collect();
    built(pattern, &holes).unwrap_or_else(|| atom(node))
}

/// The atom a part of the page the deciders do not look inside stands as.
fn atom(node: &Node) -> Term {
    Term::apply(&format!("{ATOM}{}", node.shape()), Vec::new())
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
