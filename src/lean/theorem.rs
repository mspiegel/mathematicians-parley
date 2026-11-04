//! One theorem of the corpus written as a Lean theorem, step by step.
//!
//! Each step is a `have` whose type is the step's claim and whose proof is
//! what its method is in Lean (`LEAN.md`, "What each method becomes"). A
//! step that owns a block proves its claim by the block's steps, opened by
//! what the block's lines introduce. Tactics see every line above them, as
//! Mathlib's proofs do. A comment above each step says where it stands on
//! the page, and each line written records the step it was written for, so
//! that a line Lean refuses is reported against the page.

use indexmap::IndexMap;

use super::expr::{LetterType, Printed, Writer};
use super::items::{Item, Sentence};
use super::names::{line_name, snake};
use super::statement::{binders, introduces, Asked, Binder};
use super::templates::Templates;
use crate::checker::record::Cited;
use crate::checker::{CheckedCorpus, CheckedTheorem};
use crate::citing::Way;
use crate::corpus::{Head, Intro, Justification, Method, Step, Theorem};
use crate::formula::page::Written;
use crate::formula::Node;
use crate::notations::{BICONDITIONAL, CONDITIONAL, EQUALITY, IMPLICATION, ORDER};
use crate::outcome::Route;

/// A Lean file, and for each of its lines the place on the page it was
/// written for.
#[derive(Clone, Debug, Default)]
pub struct LeanFile {
    pub text: String,
    pub origins: Vec<Origin>,
}

/// Where a line of a Lean file comes from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Origin {
    /// The line of the Lean file, from 1.
    pub line: usize,
    /// The line of the proof file it was written for.
    pub page_line: usize,
    /// What it was written for.
    pub spot: Spot,
}

/// What a line of a Lean file was written for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Spot {
    /// The theorem's statement, or a line of the file around it.
    Statement,
    /// A step, by its number as the page writes it.
    Step(String),
}

/// What writing a theorem reads: the corpus as checked, the notations and
/// items in Lean, and the theorems of the corpus as items in Lean.
pub struct Sources<'a> {
    pub checked: &'a CheckedCorpus,
    pub templates: &'a Templates,
    /// What each notation is to the methods' decisions, which `algebra`
    /// asks for its multipliers.
    pub targets: &'a crate::methods::terms::Targets,
    /// Every item a citation may name that has a Lean form, by full name:
    /// the library's records and the corpus's theorems.
    pub items: &'a IndexMap<String, Item>,
    /// What the checker matches terms with, its identity elements among
    /// them, so that a step is read as the checker decided it.
    pub ctx: &'a crate::matching::Context,
}

/// The theorem as an item of the library: its statement's binders, and its
/// `then` sentences joined into one Lean statement, each taken by its
/// projection.
/// The least type a theorem writes its relations of numbers in: ℝ for one
/// about a limit, which holds a limit, or a quantifier over ℝ with one over
/// ℕ or ℕ₀ inside it, the shape "for all ε > 0 there is N with … for all
/// n ≥ N"; ℤ otherwise. A claim about natural numbers in such a proof meets
/// lines in ℝ, and is written in ℝ from the start.
fn floor_of(rec: &CheckedTheorem) -> super::templates::Num {
    use super::expr::{system_of, System};
    use super::templates::Num;
    let quantified_over = |n: &Node| -> Option<System> {
        let [_, set, _] = n.children.as_slice() else {
            return None;
        };
        matches!(
            n.notation(),
            crate::notations::FOR_ALL | crate::notations::THERE_IS
        )
        .then(|| system_of(set))
        .flatten()
    };
    let limit_shape = |n: &Node| {
        quantified_over(n) == Some(System::Type(Num::Real))
            && n.children[2].walk().iter().any(|m| {
                matches!(
                    quantified_over(m),
                    Some(System::Positive | System::NonNegative)
                )
            })
    };
    let about_limits = rec.page.entries().any(|(_, node)| {
        node.walk().iter().any(|n| {
            matches!(&*n.notation_name(), "tends-to" | "function-limit")
                || limit_shape(n)
        })
    });
    if about_limits {
        Num::Real
    } else {
        Num::Int
    }
}

/// The terms a theorem puts in a hole of type ℝ, the A/B of ⌊A/B⌋ (set.mm's
/// floor being of reals), as the page prints them: each is a real wherever
/// the theorem writes it, so that a line about it meets the floor's.
fn held_real(rec: &CheckedTheorem, writer: &Writer) -> Vec<String> {
    let mut out = Vec::new();
    for (_, node) in rec.page.entries() {
        for n in node.walk() {
            // A letter has its own type; a term of numerals alone, the 2 of
            // √2, takes the type of where it stands.
            for arg in writer.always_real_args(&n) {
                let printed = writer.grammar.print(arg);
                let of_letters = arg.walk().iter().any(|m| m.is_name());
                if !arg.is_name() && of_letters && !out.contains(&printed) {
                    out.push(printed);
                }
            }
        }
    }
    out
}

pub fn as_item(sources: &Sources, thm: &Theorem, rec: &CheckedTheorem) -> Route<Item> {
    let mut writer = Writer::new(&sources.checked.grammar, sources.templates);
    writer.floor = floor_of(rec);
    writer.reals = held_real(rec, &writer);
    let stated = match statement(&mut writer, thm, rec) {
        Route::Built(s) => s,
        Route::Declined(d) => return Route::Declined(d),
    };
    let module = super::names::module_of(&thm.qualified());
    let decl = format!("{module}.{}", snake(&thm.name));
    let n = stated.conclusion.len();
    let mut written: Vec<Node> = hypothesis_sentences(thm, rec)
        .into_iter()
        .flat_map(|(_, s)| s.into_iter().map(|(node, _)| node))
        .collect();
    written.extend(stated.conclusion.iter().map(|c| c.says.clone()));
    let mut arithmetic = super::readback::page_arithmetic(&writer, &written);
    for (op, n) in recursion_arithmetic(&writer, thm, rec) {
        *arithmetic.entry(op).or_insert(0) += n;
    }
    let sentences = stated
        .conclusion
        .into_iter()
        .enumerate()
        .map(|(i, c)| Sentence {
            decl: decl.clone(),
            binders: stated.binders.clone(),
            says: c.says,
            prop: c.prop.text,
            part: projection(i, n),
            arithmetic: arithmetic.clone(),
            general: None,
            domains: writer.domains.clone(),
        })
        .collect();
    Route::Built(Item {
        module,
        sentences,
        proofs: Vec::new(),
    })
}

/// The parts of an "and" as its tree nests them, in order: ((A ∧ B) ∧ C)
/// gives A, B, C; anything else is one part.
fn and_parts(node: &Node) -> Vec<&Node> {
    match (node.notation(), node.children.as_slice()) {
        (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [l, r],
        ) => {
            let mut out = and_parts(l);
            out.extend(and_parts(r));
            out
        }
        _ => vec![node],
    }
}

/// The projection that takes part `i` of an "and" as its tree nests it,
/// `.1.2` for B of ((A ∧ B) ∧ C); None where it has no part `i`.
fn leaf_path(node: &Node, i: usize) -> Option<String> {
    match (node.notation(), node.children.as_slice()) {
        (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [l, r],
        ) => {
            let left = and_parts(l).len();
            if i < left {
                leaf_path(l, i).map(|p| format!(".1{p}"))
            } else {
                leaf_path(r, i - left).map(|p| format!(".2{p}"))
            }
        }
        _ => (i == 0).then(String::new),
    }
}

/// The projection that takes sentence `i` of `n` joined by `∧`, which
/// chains to the right: `.1`, `.2.1`, …, and the last `.2.2…`.
fn projection(i: usize, n: usize) -> String {
    if n == 1 {
        return String::new();
    }
    let mut out = ".2".repeat(i);
    if i + 1 < n {
        out.push_str(".1");
    }
    out
}

/// Each `let` and `assume` line of a theorem, by its label, with each of
/// its sentences and the Lean name of the hypothesis it is: the label, or
/// `H3a`, `H3b` for a line of several sentences.
fn hypothesis_sentences(
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Vec<(String, Vec<(Node, String)>)> {
    let mut out = Vec::new();
    for (i, h) in thm.hypotheses.iter().enumerate() {
        let label = h.label.clone().unwrap_or_else(|| format!("H{}", i + 1));
        let mut nodes: Vec<Node> = h
            .body(&thm.path)
            .sentences()
            .iter()
            .filter_map(|s| rec.page.get(s).cloned())
            .collect();
        // A `let` the page does not read as a formula, `f : A → B be
        // one-to-one`, says what the checker reads it to assert.
        if nodes.is_empty() {
            nodes = rec.asserted.get(i).cloned().unwrap_or_default();
        }
        let base = line_name(&label);
        let n = nodes.len();
        let said = nodes
            .into_iter()
            .enumerate()
            .map(|(k, node)| {
                let name = if n == 1 {
                    base.clone()
                } else {
                    format!("{base}{}", (b'a' + k as u8) as char)
                };
                (node, name)
            })
            .collect();
        out.push((label, said));
    }
    out
}

/// A tree of the statement with each name a define of it, or of its file,
/// gives written out as the term it names, as the checker reads the
/// statement (`CheckedTheorem::statement_definitions`).
fn defined_out(node: &Node, rec: &CheckedTheorem, writer: &Writer) -> Node {
    let put: crate::matching::Binding = rec
        .statement_definitions
        .iter()
        .filter_map(|(name, d)| match d {
            crate::matching::Defined::Term(t) => {
                Some((crate::formula::symbol::Symbol::of(name), t.clone()))
            }
            crate::matching::Defined::Rule(_) => None,
        })
        .collect();
    if put.is_empty() {
        return node.clone();
    }
    crate::matching::substitute_apart_by(node, &put, &writer.grammar.binders())
}

/// The defines a theorem's statement is read with, each a name and the term
/// it stands for, in the order defined.
fn statement_terms(rec: &CheckedTheorem) -> Vec<(String, Node)> {
    rec.statement_definitions
        .iter()
        .filter_map(|(name, d)| match d {
            crate::matching::Defined::Term(t) => Some((name.clone(), t.clone())),
            crate::matching::Defined::Rule(_) => None,
        })
        .collect()
}

/// What a theorem states, in Lean.
struct Statement {
    /// Its binders, from its `let` and `assume` lines.
    binders: Vec<Binder>,
    /// Each sentence of its `then` line.
    conclusion: Vec<Concluded>,
}

/// One sentence a theorem concludes: its tree, and its Lean text.
struct Concluded {
    says: Node,
    prop: Printed,
}

/// The number type of `let A be an element` where later lines say A is in
/// sets of numbers, A ∈ ℝ ∖ ℚ: the widest of those sets' types. None where
/// no line puts A in a set of numbers.
fn element_number_type(
    name: &str,
    rec: &CheckedTheorem,
    writer: &Writer,
) -> Option<LetterType> {
    rec.page
        .entries()
        .flat_map(|(_, node)| node.walk())
        .filter_map(|n| match n.children.as_slice() {
            [x, set]
                if n.notation() == crate::notations::MEMBERSHIP
                    && x.is_name()
                    && *x.text == *name =>
            {
                match writer.set_members(set)? {
                    super::expr::Members::Numbers(at) => Some(at),
                    _ => None,
                }
            }
            _ => None,
        })
        .max()
        .map(LetterType::Number)
}

/// A theorem's binders, from its `let` and `assume` lines, and each
/// sentence of its `then` line with its Lean text.
/// A function the header lets by its value, `let f(x) = 2x + 1, for x ∈ ℝ`:
/// as the page reads a let, a letter of the type the value computes in,
/// taking the domain's numbers (integers for ℕ, ℕ₀ or a range, as the
/// writer's sequences do), and the equation for every x as one hypothesis
/// named by the label.
fn header_function(
    writer: &mut Writer,
    d: &crate::corpus::DefineLine,
    def: &crate::corpus::Define,
    rec: &CheckedTheorem,
) -> Route<Vec<Binder>> {
    use super::templates::Num;
    let [param] = def.params.as_slice() else {
        return Route::no("a function the header lets of more than one argument");
    };
    let read: Vec<&Node> = rec
        .page
        .entries()
        .filter(|(key, _)| key.line == d.line)
        .map(|(_, node)| node)
        .collect();
    let over = |n: &&&Node| {
        matches!(
            n.notation(),
            crate::notations::NUMBER_SYSTEMS | crate::notations::INTEGER_RANGE
        )
    };
    // The domain: a number system or range written in the line, or a set,
    // a letter or a set the header itself defines, written out.
    let domain = match read.iter().find(over) {
        Some(n) => (**n).clone(),
        None => {
            let sets: Vec<&&Node> = read
                .iter()
                .filter(|n| !(n.is_name() && *n.text == *param.name))
                .filter(|n| {
                    let out = defined_out(n, rec, writer);
                    writer.set_members(&out).is_some()
                })
                .collect();
            match sets.as_slice() {
                [one] => defined_out(one, rec, writer),
                _ => {
                    return Route::no(
                        "a function the header lets on no set Lean has a type for",
                    )
                }
            }
        }
    };
    let bodies: Vec<&&Node> = read
        .iter()
        .filter(|n| !over(n))
        .filter(|n| !(n.is_name() && *n.text == *param.name))
        .filter(|n| writer.set_members(&defined_out(n, rec, writer)).is_none())
        .collect();
    let [body] = bodies.as_slice() else {
        return Route::no(
            "a function the header lets whose value did not read as one term",
        );
    };
    // What it takes: the domain's numbers, integers for ℕ, ℕ₀ or a range
    // as the writer's sequences take; or the things of a set of things.
    let takes = match super::expr::system_of(&domain) {
        Some(system) => super::expr::Members::Numbers(
            super::expr::letter_type(system).max(Num::Int),
        ),
        None if domain.notation() == crate::notations::INTEGER_RANGE => {
            super::expr::Members::Numbers(Num::Int)
        }
        None => match writer.set_members(&domain) {
            Some(m) => m,
            None => {
                return Route::no(
                    "a function the header lets on no set Lean has a type for",
                )
            }
        },
    };
    let before = writer.letters.insert(param.name.clone(), takes.letter());
    // Said for every x of the domain: all of a type, or each member of a
    // set, x ∈ D, as the writer writes that membership.
    let whole_type = matches!(
        super::expr::system_of(&domain),
        Some(super::expr::System::Type(_))
    );
    let guard = match whole_type {
        true => Route::Built(None),
        false => {
            let x = Node::name(crate::formula::Sort::none(), &param.name);
            let member = Node::of(
                crate::notations::IN,
                crate::formula::Sort::none(),
                vec![x, domain.clone()],
            );
            writer.formula(&member).map(|p| Some(p.text))
        }
    };
    let value = match &takes {
        super::expr::Members::Numbers(from) => match writer.carrier(body) {
            Route::Built(to) => writer
                .number_fixed(body, to)
                .map(|v| (LetterType::Function { from: *from, to }, v)),
            Route::Declined(why) => Route::Declined(why),
        },
        m => match writer.member_kind(body) {
            Some(to) => writer.set_term(body).map(|v| {
                (
                    LetterType::Map {
                        from: m.clone(),
                        to,
                    },
                    v,
                )
            }),
            None => {
                Route::no("a function the header lets whose value has no Lean type")
            }
        },
    };
    match before {
        Some(ty) => writer.letters.insert(param.name.clone(), ty),
        None => writer.letters.shift_remove(&param.name),
    };
    let ((ty, value), guard) = match (value, guard) {
        (Route::Built(v), Route::Built(g)) => (v, g),
        (Route::Declined(why), _) | (_, Route::Declined(why)) => {
            return Route::Declined(why)
        }
    };
    writer.letters.insert(def.name.clone(), ty.clone());
    // On a set, D ∖ {c}: that set is its domain, within which its images,
    // preimages and limits are taken (`domain_of`).
    if !whole_type {
        let written = match &takes {
            super::expr::Members::Numbers(n) => writer.numbers_at(&domain, *n),
            _ => writer.set_term(&domain),
        };
        match written {
            Route::Built(p) => {
                writer
                    .domains
                    .insert(def.name.clone(), p.at(super::expr::MAX));
            }
            Route::Declined(why) => return Route::Declined(why),
        }
    }
    let f = super::names::letter(&def.name);
    let x = super::names::letter(&param.name);
    let guard = guard.map_or(String::new(), |g| format!("{g} → "));
    Route::Built(vec![
        Binder::Letter {
            name: f.clone(),
            page: def.name.clone(),
            general: false,
            ty,
        },
        Binder::Fact {
            name: line_name(&d.label),
            says: format!(
                "∀ {x} : {}, {guard}{f} {x} = {}",
                takes.lean(),
                value.at(51)
            ),
            line: None,
        },
    ])
}

/// One function's rules of a recursion, as the checker read them: its name,
/// its value at 0, and its value at k + 1.
struct RecursionRule<'r> {
    name: &'r String,
    start: Node,
    step: Node,
}

/// Each function's rules of a recursion, as the checker read them.
fn recursion_rules<'r>(
    r: &'r crate::corpus::Recursion,
    d: &crate::corpus::DefineLine,
    rec: &CheckedTheorem,
) -> Route<Vec<RecursionRule<'r>>> {
    let mut out = Vec::new();
    for name in &r.names {
        let (Some(start), Some(step)) = (
            r.start.get(name).and_then(|rule| rule_tree(rule, d, rec)),
            r.step.get(name).and_then(|rule| rule_tree(rule, d, rec)),
        ) else {
            return Route::no(format!(
                "a recursion whose rules for {name} did not read"
            ));
        };
        out.push(RecursionRule { name, start, step });
    }
    Route::Built(out)
}

/// A rule of a recursion as the checker read it; None where it read none.
fn rule_tree(
    rule: &crate::corpus::RuleText,
    d: &crate::corpus::DefineLine,
    rec: &CheckedTheorem,
) -> Option<Node> {
    match rule.written(&d.path, d.line).sentences().as_slice() {
        [one] => rec.page.get(one).cloned(),
        _ => None,
    }
}

/// The arithmetic the page writes in the recursions a theorem's header
/// lets, as their hypothesis states them (`header_recursions`): each rule's
/// value, and the k + 1 each function is applied to in its step.
fn recursion_arithmetic(
    writer: &Writer,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> std::collections::BTreeMap<String, usize> {
    let mut out = std::collections::BTreeMap::new();
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        let r = match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(r)) => r,
            // A function the header lets by its value: the value, which its
            // hypothesis states (`header_function`).
            Route::Built(crate::corpus::DefineParts::One(one))
                if !one.params.is_empty() =>
            {
                let values: Vec<Node> = rec
                    .page
                    .entries()
                    .filter(|(key, _)| key.line == d.line)
                    .map(|(_, n)| n.clone())
                    .filter(|n| {
                        !matches!(
                            n.notation(),
                            crate::notations::NUMBER_SYSTEMS
                                | crate::notations::INTEGER_RANGE
                        )
                    })
                    .filter(|n| !n.is_name())
                    .collect();
                for (op, n) in super::readback::page_arithmetic(writer, &values) {
                    *out.entry(op).or_insert(0) += n;
                }
                continue;
            }
            _ => continue,
        };
        let Route::Built(rules) = recursion_rules(&r, d, rec) else {
            continue;
        };
        let values: Vec<Node> = rules
            .iter()
            .flat_map(|rule| [rule.start.clone(), rule.step.clone()])
            .collect();
        for (op, n) in super::readback::page_arithmetic(writer, &values) {
            *out.entry(op).or_insert(0) += n;
        }
        *out.entry("addition".to_string()).or_insert(0) += rules.len();
    }
    out
}

/// The recursions a theorem's header lets,
/// `let F(0) = 0, G(0) = 1, F(k + 1) = G(k), G(k + 1) = F(k) + G(k), for k ∈ ℕ₀`:
/// as the page reads a let,
/// letters for its functions, of ℤ into the type its rules compute in, and
/// its rules one hypothesis named by its label, its step for k ≥ 0. Of
/// every pair F, G the rules hold of, which agree from 0 on, the theorem
/// says what it says of the Fibonacci numbers. A recursion from 1, over ℕ,
/// is declined.
fn header_recursions(
    writer: &mut Writer,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Route<Vec<Binder>> {
    use super::templates::Num;
    let mut out = Vec::new();
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        let r = match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(r)) => r,
            // A function the header lets by its value, f(x) = 2x + 1, for x
            // ∈ ℝ: a function letter, and that equation for every x.
            Route::Built(crate::corpus::DefineParts::One(one))
                if !one.params.is_empty() =>
            {
                match header_function(writer, d, &one, rec) {
                    Route::Built(b) => {
                        out.extend(b);
                        continue;
                    }
                    Route::Declined(why) => return Route::Declined(why),
                }
            }
            _ => continue,
        };
        if r.domain.trim() != "ℕ₀" {
            return Route::no("a recursion over other than ℕ₀");
        }
        let rules = match recursion_rules(&r, d, rec) {
            Route::Built(rules) => rules,
            Route::Declined(d) => return Route::Declined(d),
        };
        // The functions take integers, as the writer's sequences do, so
        // that F(k) of a sum's index is written as it stands; the rules say
        // what they are from 0. What they give is the type their rules
        // compute in, an integer at least.
        let index = r.index.clone();
        let before = writer
            .letters
            .insert(index.clone(), LetterType::Number(Num::Int));
        let mut to = Num::Int;
        for name in &r.names {
            writer
                .letters
                .insert(name.clone(), LetterType::Function { from: Num::Int, to });
        }
        for rule in &rules {
            for n in [&rule.start, &rule.step] {
                match writer.carrier(n) {
                    Route::Built(c) => to = to.max(c),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        }
        for name in &r.names {
            writer
                .letters
                .insert(name.clone(), LetterType::Function { from: Num::Int, to });
        }
        let k = super::names::letter(&index);
        let mut starts = Vec::new();
        let mut steps = Vec::new();
        for rule in &rules {
            let f = super::names::letter(rule.name);
            let (s, t) = match (
                writer.number_fixed(&rule.start, to),
                writer.number_fixed(&rule.step, to),
            ) {
                (Route::Built(s), Route::Built(t)) => (s, t),
                (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                    return Route::Declined(d)
                }
            };
            starts.push(format!("{f} 0 = {}", s.at(51)));
            steps.push(format!("{f} ({k} + 1) = {}", t.at(51)));
        }
        match before {
            Some(ty) => writer.letters.insert(index.clone(), ty),
            None => writer.letters.shift_remove(&index),
        };
        for name in &r.names {
            out.push(Binder::Letter {
                name: super::names::letter(name),
                page: name.clone(),
                general: false,
                ty: LetterType::Function { from: Num::Int, to },
            });
        }
        out.push(Binder::Fact {
            name: line_name(&d.label),
            says: format!(
                "{} ∧ ∀ {k} : ℤ, 0 ≤ {k} → {}",
                starts.join(" ∧ "),
                steps.join(" ∧ ")
            ),
            line: None,
        });
    }
    Route::Built(out)
}

/// Hypothesis sentences, each its tree and its Lean name, as `binders`
/// takes them.
fn asked_of(written: &[(Node, String)]) -> Vec<Asked<'_>> {
    written
        .iter()
        .map(|(node, name)| Asked {
            node,
            name: name.clone(),
        })
        .collect()
}

fn statement(
    writer: &mut Writer,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Route<Statement> {
    let said = hypothesis_sentences(thm, rec);
    // A `let` that is no formula, `A be a set` or `x be an element`, gives
    // its letter the type its sort settles, ahead of the lines that use it.
    let mut binders_of_sets = Vec::new();
    let mut read: usize = said.iter().map(|(_, s)| s.len()).sum();
    for (i, h) in thm.hypotheses.iter().enumerate() {
        let body = h.body(&thm.path);
        if body.sentences().iter().all(|s| rec.page.get(s).is_some()) {
            continue;
        }
        use crate::sorts::introduction::{Form, Introduction};
        let name = match Introduction::read(body.clone()).form {
            Form::Set(name)
            | Form::Element(name)
            | Form::Property { name, .. }
            | Form::FunctionOn { name, .. } => name,
            // `let G be a group with operation · and identity e`: the type
            // of its elements with Mathlib's group on it, and e its 1. What
            // else the line asserts, that G is finite, is among `said`.
            Form::Group {
                group, identity, ..
            } => {
                writer.letters.insert(group.clone(), LetterType::Group);
                writer
                    .letters
                    .insert(identity, LetterType::Identity(group.clone()));
                binders_of_sets.push(Binder::Letter {
                    name: super::names::letter(&group),
                    page: group,
                    general: false,
                    ty: LetterType::Group,
                });
                if rec.asserted.get(i).is_none_or(Vec::is_empty) {
                    read += body.sentences().len();
                }
                continue;
            }
            _ => continue,
        };
        // An element nothing settles a sort of, `let B be an element` of a
        // B only listed, {B}, is a thing.
        let unsorted_element =
            matches!(Introduction::read(body.clone()).form, Form::Element(_))
                && rec.sorts.get(&name).is_none();
        let Some(ty) = rec
            .sorts
            .get(&name)
            .and_then(super::sets::set_letter_type)
            .or_else(|| element_number_type(&name, rec, writer))
            .or_else(|| {
                unsorted_element
                    .then_some(LetterType::Member(super::expr::Members::Things))
            })
        else {
            continue;
        };
        writer.letters.insert(name.clone(), ty.clone());
        binders_of_sets.push(Binder::Letter {
            name: super::names::letter(&name),
            page: name,
            general: false,
            ty,
        });
        // A line that asserts something of its letter, F is a function on
        // A, is read among `said` already.
        if rec.asserted.get(i).is_none_or(Vec::is_empty) {
            read += body.sentences().len();
        }
    }
    let written: usize = thm
        .hypotheses
        .iter()
        .map(|h| h.body(&thm.path).sentences().len())
        .sum();
    if read != written {
        return Route::no("a hypothesis the checker did not read");
    }
    // A define the statement is read with is written out in it: Lean's
    // statement says what the name stands for, and the proof names it again
    // (`theorem`, `set`).
    // The hypotheses above a recursion or function the header lets are
    // read before it, as its rules may use their letters, F(0) = M; those
    // below after it, as they may use its functions.
    let recursion_line = thm
        .defines
        .iter()
        .filter(|d| d.line < thm.conclusion_line)
        .filter(|d| match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(_)) => true,
            Route::Built(crate::corpus::DefineParts::One(one)) => {
                !one.params.is_empty()
            }
            _ => false,
        })
        .map(|d| d.line)
        .min();
    let above = |label: &str| {
        let line = thm
            .hypotheses
            .iter()
            .find(|h| h.label.as_deref() == Some(label))
            .map(|h| h.line);
        match (recursion_line, line) {
            (Some(r), Some(l)) => l < r,
            _ => true,
        }
    };
    let mut written_above: Vec<(Node, String)> = Vec::new();
    let mut written_below: Vec<(Node, String)> = Vec::new();
    for (label, s) in &said {
        let into = match above(label) {
            true => &mut written_above,
            false => &mut written_below,
        };
        for (node, name) in s {
            into.push((defined_out(node, rec, writer), name.clone()));
        }
    }
    let first = match binders(writer, &asked_of(&written_above)) {
        Route::Built(b) => b,
        Route::Declined(d) => return Route::Declined(d),
    };
    let recursions = match header_recursions(writer, thm, rec) {
        Route::Built(b) => b,
        Route::Declined(d) => return Route::Declined(d),
    };
    let binders = match binders(writer, &asked_of(&written_below)) {
        Route::Built(b) => binders_of_sets
            .into_iter()
            .chain(first)
            .chain(recursions)
            .chain(b)
            .collect::<Vec<_>>(),
        Route::Declined(d) => return Route::Declined(d),
    };
    let mut conclusion = Vec::new();
    for s in thm.stated().sentences() {
        let Some(node) = rec.page.get(&s) else {
            return Route::no(format!("{}, which the checker did not read", s.text()));
        };
        let node = &defined_out(node, rec, writer);
        let prop = match writer.formula(node) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        conclusion.push(Concluded {
            says: node.clone(),
            prop,
        });
    }
    Route::Built(Statement {
        binders,
        conclusion,
    })
}

/// Writes one theorem's proof.
struct Proof<'a> {
    sources: &'a Sources<'a>,
    thm: &'a Theorem,
    rec: &'a CheckedTheorem,
    writer: Writer<'a>,
    lines: Vec<String>,
    origins: Vec<Origin>,
    /// The Lean names of each line the page can cite, by the reference
    /// that cites it: a step's number or a label.
    named: IndexMap<String, Vec<String>>,
    /// What each line the page can cite says, sentence by sentence, with
    /// the Lean name of each sentence's proof, by the reference that cites
    /// it.
    trees: IndexMap<String, Vec<(Node, String)>>,
    /// The defines written so far, by their index in the theorem's.
    defined: indexmap::IndexSet<usize>,
    /// While a calculation's rows are written, the type it is worked out
    /// in: a row's claim alone, Σ j² = 1², may hold in a narrower type than
    /// the calculation's ℚ, which a citation in the row is applied at.
    worked_in: std::cell::Cell<Option<super::templates::Num>>,
    /// The lines whose numbers a citation was given while its step was
    /// written, A/B of `A/B ∈ ℤ`, which the step's goal is put in terms of.
    said_used: std::cell::RefCell<Vec<SaidUsed>>,
    /// The labels of the defines that name the number their reason shows,
    /// `let e = p/d, a positive integer` (`kinded_witness`): their equation
    /// is a line about an obtained number, cited as any line is, not a
    /// `set` written out.
    witnessed: std::collections::BTreeSet<String>,
}

/// A line whose number a citation was given: its Lean name, and the term
/// it says is in ℤ or ℚ as the page prints it.
struct SaidUsed {
    line: String,
    term: String,
}

/// A recursion the header lets, as a step cites it.
struct CitedRecursion {
    rule: crate::corpus::Recursion,
    /// The Lean name of its hypothesis, `hD1`.
    hypothesis: String,
    /// Whether a rule of it is by cases, F(k) if b(k) = 0, G(k) otherwise.
    by_cases: bool,
}

/// The theorem written as a Lean file's declaration: its statement and its
/// proof, with an origin for every line, counted from the first line of
/// the declaration.
pub fn theorem(
    sources: &Sources,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Route<LeanFile> {
    let mut proof = Proof {
        sources,
        thm,
        rec,
        writer: Writer::new(&sources.checked.grammar, sources.templates),
        lines: Vec::new(),
        origins: Vec::new(),
        named: IndexMap::new(),
        trees: IndexMap::new(),
        defined: indexmap::IndexSet::new(),
        worked_in: std::cell::Cell::new(None),
        said_used: std::cell::RefCell::new(Vec::new()),
        witnessed: std::collections::BTreeSet::new(),
    };
    proof.writer.floor = floor_of(rec);
    proof.writer.reals = held_real(rec, &proof.writer);
    let Statement {
        binders,
        conclusion,
    } = match statement(&mut proof.writer, thm, rec) {
        Route::Built(s) => s,
        Route::Declined(d) => return Route::Declined(d),
    };
    // A hypothesis Lean's types give, M ∈ ℕ₀ of a natural M, has no binder
    // and is no line in Lean: a step that uses it has the type.
    let bound: std::collections::BTreeSet<&str> =
        binders.iter().map(Binder::name).collect();
    for (label, said) in hypothesis_sentences(thm, rec) {
        let said: Vec<(Node, String)> = said
            .into_iter()
            .filter(|(_, n)| bound.contains(n.as_str()))
            .collect();
        let names: Vec<String> = said.iter().map(|(_, n)| n.clone()).collect();
        proof.named.insert(label.clone(), names);
        proof.trees.insert(label, said);
    }
    // A recursion or a function the statement lets is cited by its label,
    // as its hypothesis (`header_recursions`).
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        let function = match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(_)) => true,
            Route::Built(crate::corpus::DefineParts::One(one)) => {
                !one.params.is_empty()
            }
            _ => false,
        };
        if function {
            proof
                .named
                .insert(d.label.clone(), vec![line_name(&d.label)]);
        }
    }
    let props: Vec<String> = conclusion.iter().map(|c| c.prop.at(36)).collect();
    let binders: Vec<String> =
        super::statement::things_binder(&binders, &props.join(" "))
            .into_iter()
            .chain(binders.iter().map(Binder::lean))
            .collect();
    let space = if binders.is_empty() { "" } else { " " };
    // Lean's budget for one declaration, 200000 heartbeats, for each 30
    // steps of the proof: a long proof is many steps, each of the usual
    // cost, which the one default would cut off part way. A proof of 37
    // steps citing items over ℚ and ℝ took 16 seconds and more than one.
    let budget = match thm.steps.len().div_ceil(30) {
        0 | 1 => String::new(),
        n => format!("set_option maxHeartbeats {} in\n", 200_000 * n),
    };
    proof.push(
        format!(
            "{budget}theorem {}{space}{} :\n    {} := by",
            snake(&thm.name),
            binders.join(" "),
            props.join(" ∧ ")
        ),
        thm.line,
        Spot::Statement,
    );
    // The names the statement wrote out, named again for the proof.
    // Only those the theorem's page writes: a file's other defines are its
    // other theorems'.
    let written: std::collections::BTreeSet<String> = rec
        .page
        .entries()
        .flat_map(|(_, node)| node.names())
        .collect();
    for (name, body) in statement_terms(rec) {
        if !written.contains(&name) {
            continue;
        }
        let own = thm.defines.iter().position(|d| {
            d.line < thm.conclusion_line
                && matches!(
                    crate::corpus::define_parts(&d.text),
                    Route::Built(crate::corpus::DefineParts::One(ref one)) if one.name == name
                )
        });
        let named = match own {
            Some(d) => proof.define(d, 1),
            None => proof.define_outside(&name, &body),
        };
        if let Route::Declined(d) = named {
            return Route::Declined(d);
        }
    }
    let top: Vec<usize> = (0..thm.steps.len())
        .filter(|&i| rec.places[i].is_none())
        .collect();
    if let Route::Declined(d) = proof.steps(&top, 1) {
        return Route::Declined(d);
    }
    if conclusion.len() > 1 {
        proof.push(
            format!(
                "  exact ⟨{}⟩",
                vec!["by parley_side"; conclusion.len()].join(", ")
            ),
            thm.conclusion_line,
            Spot::Statement,
        );
    } else {
        let close = match conclusion.as_slice() {
            [one] => proof.closing(top.last().copied(), &one.says),
            _ => "parley_side".to_string(),
        };
        proof.push(
            format!("  all_goals {close}"),
            thm.conclusion_line,
            Spot::Statement,
        );
    }
    let mut text = String::new();
    let mut origins = Vec::new();
    let mut at = 1;
    for (line, origin) in proof.lines.iter().zip(proof.origins) {
        for _ in line.lines() {
            origins.push(Origin {
                line: at,
                ..origin.clone()
            });
            at += 1;
        }
        text.push_str(line);
        text.push('\n');
    }
    Route::Built(LeanFile { text, origins })
}

/// Indentation for a depth of nesting.
fn pad(depth: usize) -> String {
    "  ".repeat(depth)
}

/// What proves a claim: a justification, and what the checker read of the
/// item it cites. A step has one, and so does each of its requires lines
/// and each line of a calculation that gives a reason of its own.
#[derive(Clone, Copy)]
struct Reason<'r> {
    just: &'r Justification,
    cited: Option<&'r Cited>,
}

impl<'a> Proof<'a> {
    fn push(&mut self, line: String, page_line: usize, spot: Spot) {
        self.lines.push(line);
        self.origins.push(Origin {
            line: 0,
            page_line,
            spot,
        });
    }

    fn step_spot(step: &Step) -> Spot {
        Spot::Step(match step.number.number() {
            Some(n) => n.to_string(),
            None => "the theorem".to_string(),
        })
    }

    /// The steps, in order, each at the depth given.
    fn steps(&mut self, indices: &[usize], depth: usize) -> Route<()> {
        for &i in indices {
            if let Route::Declined(d) = self.step(i, depth) {
                // Named by the innermost step it comes from: a block's
                // decline already names the step inside it.
                let reason = d.reason();
                if reason.starts_with("step ") {
                    return Route::Declined(d);
                }
                let number = &self.thm.steps[i].number;
                return Route::no(format!("step {number}: {reason}"));
            }
        }
        Route::Built(())
    }

    /// A step's claim: each sentence, read, with its Lean text; a
    /// membership Lean's types already give is left out, since nothing
    /// needs saying.
    fn claim(&self, step: &Step) -> Route<Vec<(Node, Printed)>> {
        self.claimed(step).map(|c| {
            c.into_iter()
                .map(|(_, node, printed)| (node, printed))
                .collect()
        })
    }

    /// `claim`, each sentence with its place among the page's: a sentence
    /// Lean's types already give, √x ∈ ℝ, is left out, and a citation is
    /// read at the place the checker counted.
    fn claimed(&self, step: &Step) -> Route<Vec<(usize, Node, Printed)>> {
        let mut out = Vec::new();
        for (at, s) in step.claim.sentences().into_iter().enumerate() {
            let Some(node) = self.rec.page.get(&s) else {
                return Route::no(format!(
                    "{}, which the checker did not read",
                    s.text()
                ));
            };
            // A claim of numerals alone is written in the type of the lines
            // it is reached from, where any are cited.
            let printed = if node.names().is_empty() {
                let mut floor = super::templates::Num::Int;
                for c in self.cited_parts(&step.just.refs) {
                    for side in
                        c.node.children.iter().filter(|s| self.writer.is_number(s))
                    {
                        if let Route::Built(n) = self.writer.carrier(side) {
                            floor = floor.max(n);
                        }
                    }
                }
                self.writer.closed_formula(node, floor)
            } else {
                self.writer.formula(node)
            };
            let printed = match printed {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            if printed.text != "True" {
                out.push((at, node.clone(), printed));
            }
        }
        Route::Built(out)
    }

    /// The Lean names of a step's sentences: `s2` for one, `s2a`, `s2b` for
    /// several.
    fn names_of(step: &Step, count: usize) -> Vec<String> {
        let base = match step.number.number() {
            Some(n) => line_name(&n.to_string()),
            None => "sThm".to_string(),
        };
        if count == 1 {
            return vec![base];
        }
        (0..count)
            .map(|i| format!("{base}{}", (b'a' + i as u8) as char))
            .collect()
    }

    /// The letters a step's claim introduces, `k ∈ ℤ`, added to those in
    /// scope. A claim of a letter already in scope introduces nothing: it
    /// says something of the letter, which `lift` takes up.
    fn introduce(&mut self, step: &Step) {
        for s in step.claim.sentences() {
            if let Some(node) = self.rec.page.get(&s) {
                let letter = introduces(node)
                    .map(|(l, _)| l)
                    .or_else(|| super::statement::range_letter(node));
                let known = letter
                    .is_some_and(|l| self.writer.letters.contains_key(l.as_str()));
                if known {
                    continue;
                }
                if let Some((letter, system)) = introduces(node) {
                    self.writer.letters.insert(
                        letter,
                        LetterType::Number(super::expr::letter_type(system)),
                    );
                } else if let Some(letter) = super::statement::range_letter(node) {
                    self.writer
                        .letters
                        .insert(letter, LetterType::Number(super::templates::Num::Int));
                } else if let Some((letter, members)) = self.set_member_said(node) {
                    self.writer.letters.insert(letter, members.letter());
                } else if let Some(letter) =
                    super::statement::introduces_polynomial(node)
                {
                    self.writer.letters.insert(
                        letter,
                        LetterType::Function {
                            from: super::templates::Num::Complex,
                            to: super::templates::Num::Complex,
                        },
                    );
                }
            }
        }
    }

    /// The letter a line says is a member of a set, `x ∈ A`, where the
    /// letter is new and the writer has a type for A's members.
    fn set_member_said(&self, node: &Node) -> Option<(String, super::expr::Members)> {
        let [x, set] = node.children.as_slice() else {
            return None;
        };
        let new = node.notation() == crate::notations::MEMBERSHIP
            && x.is_name()
            && !self.writer.letters.contains_key(x.text.as_str());
        new.then(|| self.writer.members_of(set))
            .flatten()
            .map(|m| (x.text.to_string(), m))
    }

    fn step(&mut self, i: usize, depth: usize) -> Route<()> {
        let step = &self.thm.steps[i];
        // The defines written above this step in its block, where the
        // checker opens them.
        let due: Vec<usize> = (0..self.thm.defines.len())
            .filter(|&d| {
                !self.defined.contains(&d)
                    && self.thm.defines[d].line < step.line
                    && self.thm.defines[d].line > self.thm.conclusion_line
                    && self.rec.defines.get(d).copied().flatten() == self.rec.places[i]
            })
            .collect();
        for d in due {
            if let Route::Declined(why) = self.define(d, depth) {
                return Route::Declined(why);
            }
        }
        let spot = Self::step_spot(step);
        let p = pad(depth);
        self.push(
            format!("{p}-- {}. {}", step.number, step.just.text.trim()),
            step.line,
            spot.clone(),
        );
        // The claim's first sentence as the page reads it, whose leading
        // "for all" binds letters its requires lines may speak of.
        let claimed = step
            .claim
            .sentences()
            .first()
            .and_then(|s| self.rec.page.get(s))
            .cloned();
        for (k, r) in step.requires.iter().enumerate() {
            let node = match self.tree(&r.fact) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            // A requires line of a letter the claim says "for all" of, x²
            // ≥ 0 of every x ∈ [0, 1], is said under the claim's binders and
            // proved with its letters given.
            let under = claimed
                .as_ref()
                .filter(|c| bound_in(c, &node))
                .map(|c| under_binders(c, &node));
            let stated = under.clone().unwrap_or_else(|| node.clone());
            let fact = match self.writer.formula(&stated) {
                Route::Built(f) => f,
                Route::Declined(d) => return Route::Declined(d),
            };
            if fact.text == "True" {
                continue;
            }
            let Ok(just) = &r.by else {
                return Route::no("a requires line whose reason does not read");
            };
            let reason = Reason {
                just,
                cited: self.rec.cited_requires.get(&r.line),
            };
            let proof = match &under {
                None => self.proof_of(reason, 0, &node),
                Some(wrapped) => {
                    let (intros, _, inner) = self.peel(wrapped);
                    let outer = std::mem::replace(&mut self.writer, inner);
                    let proof = self.proof_of(reason, 0, &node);
                    self.writer = outer;
                    proof.map(|p| {
                        format!("by intro {}; {}", intros.join(" "), as_tactic(&p))
                    })
                }
            };
            let proof = match proof {
                Route::Built(t) => t,
                Route::Declined(d) => return Route::Declined(d),
            };
            let name = format!("r{}_{}", step.line, k + 1);
            self.push(
                indented(&format!("{p}have {name} : {} := {proof}", fact.text), &p),
                r.line,
                spot.clone(),
            );
        }
        if let Head::Method(Method::Obtain) = step.just.head {
            return self.obtain(i, depth);
        }
        self.introduce(step);
        let claim = match self.claim(step) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let names = Self::names_of(step, claim.len());
        if let Some(n) = step.number.number() {
            self.named.insert(n.to_string(), names.clone());
            let said = claim
                .iter()
                .zip(&names)
                .map(|((node, _), name)| (node.clone(), name.clone()))
                .collect();
            self.trees.insert(n.to_string(), said);
        }
        if let Head::Method(m) = step.just.head {
            // A calculation's lines are its proof, written as Lean's calc;
            // every other block's steps stand in it.
            if m.takes_block() && m != Method::Calculation {
                // The lines inside a block are out of scope after it, and
                // the claim the block proves is no line in scope inside it.
                let own = step.number.number().map(|n| n.to_string());
                let claimed = own.as_ref().and_then(|n| self.trees.shift_remove(n));
                let visible: std::collections::BTreeSet<String> =
                    self.trees.keys().cloned().collect();
                let written = self.block(i, m, &claim, &names, depth);
                self.trees.retain(|k, _| visible.contains(k));
                if let (Some(n), Some(said)) = (own, claimed) {
                    self.trees.insert(n, said);
                }
                return written;
            }
        }
        let reason = Reason {
            just: &step.just,
            cited: self.rec.cited[i].as_ref(),
        };
        let places: Vec<usize> = match self.claimed(step) {
            Route::Built(c) => c.into_iter().map(|(at, _, _)| at).collect(),
            Route::Declined(d) => return Route::Declined(d),
        };
        for (k, (node, prop)) in claim.iter().enumerate() {
            // A citation for a claim said "for all k ∈ …" of an item said of
            // one k, its letters given values in the claim's k: the item
            // cited at that k, given as a method takes it (`peel`). An item
            // that says the "for all" itself is cited whole.
            let cites_for_all = matches!(reason.just.head, Head::Item { .. })
                && node.notation() == crate::notations::FOR_ALL
                && self.cited_at_bound_letter(reason.cited, node);
            let proof = if cites_for_all {
                let (intros, body, inner) = self.peel(node);
                let outer = std::mem::replace(&mut self.writer, inner);
                let proof = self.proof_of(reason, places[k], body);
                self.writer = outer;
                proof.map(|p| match intros.is_empty() {
                    true => p,
                    false => {
                        format!("by intro {}; {}", intros.join(" "), as_tactic(&p))
                    }
                })
            } else {
                self.proof_of(reason, places[k], node)
            };
            let proof = match proof {
                Route::Built(t) => t,
                Route::Declined(d) => return Route::Declined(d),
            };
            self.push(
                indented(
                    &format!("{p}have {} : {} := {proof}", names[k], prop.text),
                    &p,
                ),
                step.line,
                spot.clone(),
            );
            self.lift(node, &names[k], step.line, &spot, &p);
        }
        if step.impossible {
            // A line of roots or of π, ln, exp, sin or cos, √2 − 1 = 0, is
            // shown false by real arithmetic; any other by `norm_num`.
            let real = claim.iter().any(|(node, _)| {
                node.walk().iter().any(|n| {
                    matches!(&*n.notation_name(), "square-root" | "pi")
                        || n.children.first().is_some_and(|f| {
                            matches!(&*f.text, "cos" | "sin" | "exp" | "ln" | "tan")
                        })
                })
            });
            let refute = if real { "parley_real" } else { "norm_num" };
            if let Some(last) = names.last() {
                self.push(
                    format!("{p}exact absurd {last} (by {refute})"),
                    step.line,
                    spot,
                );
            }
        }
        Route::Built(())
    }

    /// A line that shows a letter of ℤ is in ℕ or ℕ₀, `k ∈ ℕ`, makes the
    /// letter a natural number from there on, by Mathlib's `lift`: a later
    /// line may then use it where ℕ is wanted, as an exponent. The line is
    /// given to `lift` as a term, so that it is kept in scope.
    fn lift(&mut self, node: &Node, line: &str, at: usize, spot: &Spot, p: &str) {
        let [term, set] = node.children.as_slice() else {
            return;
        };
        if node.notation() != crate::notations::MEMBERSHIP || !term.is_name() {
            return;
        }
        let integer = LetterType::Number(super::templates::Num::Int);
        if self.writer.letters.get(term.text.as_str()) != Some(&integer) {
            return;
        }
        let nonneg = match super::expr::system_of(set) {
            Some(super::expr::System::Positive) => format!("{line}.le"),
            Some(super::expr::System::NonNegative) => format!("(id {line})"),
            _ => return,
        };
        let letter = super::names::letter(&term.text);
        self.push(
            format!("{p}lift {letter} to ℕ using {nonneg}"),
            at,
            spot.clone(),
        );
        self.writer.letters.insert(
            term.text.to_string(),
            LetterType::Number(super::templates::Num::Nat),
        );
    }

    /// A sentence of the page as the checker read it.
    fn tree(&self, written: &Written) -> Route<Node> {
        match written
            .sentences()
            .first()
            .and_then(|s| self.rec.page.get(s))
        {
            Some(node) => Route::Built(node.clone()),
            None => Route::no(format!(
                "{}, which the checker did not read",
                written.text()
            )),
        }
    }

    /// The widest fixed type a hole of the claim takes, ℝ of ⌊A/B⌋, which
    /// a term in that hole is computed in; ℤ where there is none.
    fn held_in(&self, claim: &Node) -> super::templates::Num {
        claim
            .walk()
            .iter()
            .filter_map(|n| self.writer.template(n).built())
            .flat_map(|t| t.holes.iter())
            .filter_map(|s| match s {
                super::templates::Slot::Fixed(n) => Some(*n),
                _ => None,
            })
            .fold(super::templates::Num::Int, std::cmp::Ord::max)
    }

    /// The proof of sentence `k` of a claim, by its reason.
    fn proof_of(&self, reason: Reason, k: usize, node: &Node) -> Route<String> {
        if let Some(witness) = self.said_member(node) {
            return Route::Built(format!("by {witness}"));
        }
        self.said_used.borrow_mut().clear();
        let proof = match self.proof_by_reason(reason, k, node) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A citation given a line's number, ⌊m⌋ = m for the m of `A/B ∈
        // ℤ`, meets a goal that has the line's term, ⌊A/B⌋: the goal is put
        // in terms of the number first.
        let used = std::mem::take(&mut *self.said_used.borrow_mut());
        let specs = self.specs_in(node, &used);
        Route::Built(match specs.is_empty() {
            true => proof,
            false => format!("by rw [{specs}]; {}", as_tactic(&proof)),
        })
    }

    /// Whether a citation gives its item's letters values in a letter the
    /// claim's leading "for all" binds: the item is cited at that letter.
    fn cited_at_bound_letter(
        &self,
        cited: Option<&crate::checker::record::Cited>,
        claim: &Node,
    ) -> bool {
        let Some(cited) = cited else {
            return false;
        };
        let mut bound = Vec::new();
        let mut body = claim;
        while let (crate::notations::FOR_ALL, [letter, _, inner]) =
            (body.notation(), body.children.as_slice())
        {
            bound.push(letter.text);
            body = inner;
        }
        // A letter free in a value: a value that binds it itself, Q := "for
        // all x, …", says the "for all" whole.
        let binders = self.sources.checked.grammar.binders();
        cited.binding.values().any(|v| {
            crate::matching::free_names(v, &binders)
                .iter()
                .any(|n| bound.iter().any(|b| **b == **n))
        })
    }

    /// The hypothesis of a function the theorem's header lets by its value,
    /// which a step cites by its label; None for any other citation.
    fn header_function_cited(&self, just: &Justification) -> Option<String> {
        self.header_function_named(just.defined.as_deref()?)
    }

    /// The hypothesis of a function the theorem's header lets by its value,
    /// by its label; None for any other label.
    fn header_function_named(&self, label: &str) -> Option<String> {
        let d = self
            .thm
            .defines
            .iter()
            .find(|d| d.label == label && d.line < self.thm.conclusion_line)?;
        match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::One(one))
                if !one.params.is_empty() =>
            {
                Some(line_name(&d.label))
            }
            _ => None,
        }
    }

    /// The recursion of the theorem's header a step cites by its label, with
    /// that label; None for a citation of any other define.
    fn recursion_cited(&self, just: &Justification) -> Option<CitedRecursion> {
        let label = just.defined.as_deref()?;
        let d = self
            .thm
            .defines
            .iter()
            .find(|d| d.label == label && d.line < self.thm.conclusion_line)?;
        let by_cases = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == d.line)
            .any(|(_, n)| n.walk().iter().any(|m| &*m.notation_name() == "by-cases"));
        match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(rule)) => {
                Some(CitedRecursion {
                    rule,
                    hypothesis: line_name(&d.label),
                    by_cases,
                })
            }
            _ => None,
        }
    }

    /// A step citing a recursion's rule, F(k + 1) = G(k): the first of the
    /// claim's applications of its functions, F(a), says which. At the
    /// numeral 0 it is F's start; at any other a it is F's step at a − 1,
    /// with a − 1 + 1 put back as a, and the arguments put in one form. A
    /// rule by cases is taken at the case the cited lines say: an equation
    /// its condition, `ite_eq_left`; one denied, `otherwise`, `ite_eq_right`.
    /// Its condition is put at a first, a − 1 + 1 inside it as a, for the
    /// cited line to match.
    fn recursion_clause(
        &self,
        cited: &CitedRecursion,
        cases: &[super::algebra::Cited],
        claim: &Node,
        writer: &Writer,
    ) -> Route<String> {
        let (r, hyp) = (&cited.rule, &cited.hypothesis);
        let mut case_rewrites = String::new();
        if cited.by_cases {
            for c in cases {
                let lemma = match (c.node.notation(), c.node.children.as_slice()) {
                    (EQUALITY, _) => "ite_eq_left",
                    (crate::notations::LOGICAL_NOT, [inner])
                        if inner.notation() == EQUALITY =>
                    {
                        "ite_eq_right"
                    }
                    _ => continue,
                };
                case_rewrites.push_str(&format!(" rw [{lemma} {}] at h;", c.proof));
            }
        }
        let cancel = match case_rewrites.is_empty() {
            true => "sub_add_cancel",
            false => "sub_add_cancel, add_sub_cancel_right",
        };
        let applied = claim.walk().into_iter().find_map(|n| {
            let [f, a] = n.children.as_slice() else {
                return None;
            };
            let at = r.names.iter().position(|name| *name == *f.text)?;
            (n.notation() == crate::notations::APPLICATION).then(|| (at, a.clone()))
        });
        let Some((at, arg)) = applied else {
            return Route::no("a recursion cited for a claim of none of its functions");
        };
        let n = r.names.len();
        // The hypothesis is the starts and then the steps, joined by ∧.
        let start = projection(at, n + 1);
        let steps = projection(n, n + 1);
        let step = projection(at, n);
        if arg.notation() == crate::notations::NUMERAL && &*arg.text == "0" {
            return Route::Built(format!(
                "by have h := {hyp}{start}; (try ring_nf at h ⊢); linarith"
            ));
        }
        let a = match writer.number_fixed(&arg, super::templates::Num::Int) {
            Route::Built(a) => a,
            Route::Declined(d) => return Route::Declined(d),
        };
        Route::Built(format!(
            "by have h := ({hyp}{steps} ({} - 1) (by omega)){step}; simp only [{cancel}] at h;{case_rewrites} (try ring_nf at h ⊢); linarith",
            a.at(66)
        ))
    }

    /// A claim that a term of a wider type is an integer or a rational,
    /// (A + B) − B ∈ ℚ of reals, where some part of it a line says is in
    /// that type: the term written there, that part the number the line
    /// gives, as Lean's witness. A citation of an item over ℚ gives such a
    /// claim nothing, as of rationals it holds by their type.
    fn said_member(&self, node: &Node) -> Option<String> {
        let [term, set] = node.children.as_slice() else {
            return None;
        };
        use super::templates::Num;
        // The type the term is said to be in, and the type its parts are
        // said to be in: ℕ₀ is said of an integer, its parts integers.
        let (claimed, ty) = match super::expr::system_of(set)? {
            super::expr::System::Type(t @ (Num::Int | Num::Rat)) => (t, t),
            super::expr::System::NonNegative => (Num::Nat, Num::Int),
            _ => return None,
        };
        let wide = self.writer.carrier(term).built()?;
        if node.notation() != crate::notations::MEMBERSHIP || wide <= ty {
            return None;
        }
        let mut writer = self.writer.with_letters(self.writer.letters.clone());
        let mut lines = Vec::new();
        // The parts within the term: the term itself is what the step
        // claims, and a letter of the type said is in it already; a letter
        // of a wider type, A ∈ ℝ, may be said an integer.
        let whole = writer.grammar.print(term);
        for part in term.walk() {
            let typed = part.is_name()
                && writer.carrier(&part).built().is_some_and(|c| c <= ty);
            if typed
                || part.notation() == crate::notations::NUMERAL
                || writer.grammar.print(&part) == whole
            {
                continue;
            }
            if let Some(line) = self.said_integer(&part, ty) {
                let spec = format!("Classical.choose_spec {line}");
                if lines.contains(&spec) {
                    continue;
                }
                writer.integers.push(super::expr::SaidInteger {
                    term: writer.grammar.print(&part),
                    proof: line.clone(),
                    ty,
                });
                lines.push(spec);
            }
        }
        if lines.is_empty() {
            return None;
        }
        let witness = writer.number_fixed(term, ty).built()?.text;
        let specs = lines.join(", ");
        Some(match claimed {
            // In ℕ₀: the integer's `toNat`, which is the integer, as it is
            // not negative.
            Num::Nat => format!(
                "(exact ⟨({witness}).toNat, by rw [show ((({witness}).toNat : ℕ) : {wide_t}) = ((({witness}) : ℤ) : {wide_t}) by exact_mod_cast Int.toNat_of_nonneg (by parley_side)]; push_cast; (try simp only [{specs}]); first | done | parley_ring⟩)",
                wide_t = writer.type_name(wide)
            ),
            _ => format!(
                "(exact ⟨{witness}, by push_cast; (try simp only [{specs}]); first | done | parley_ring⟩)"
            ),
        })
    }

    fn proof_by_reason(&self, reason: Reason, k: usize, node: &Node) -> Route<String> {
        match &reason.just.head {
            Head::Item { .. } => self.citation(reason, k, node),
            Head::Method(m) => {
                // A claim said of every member of a set is proved of one,
                // taken as the method's letter.
                let (intros, body, writer) = self.peel(node);
                let tactic = match self.method_proof(reason, *m, body, &writer) {
                    Route::Built(t) => t,
                    Route::Declined(d) => return Route::Declined(d),
                };
                if intros.is_empty() {
                    return Route::Built(tactic);
                }
                let inner = tactic.strip_prefix("by ").unwrap_or(&tactic);
                Route::Built(format!("by intro {}; {inner}", intros.join(" ")))
            }
            // A step citing a define claims its equation, which Lean's `set`
            // put in scope under the define's label.
            Head::Define => match self.recursion_cited(reason.just) {
                // A rule said for every n, F(n + 1) = 2F(n): said of one n.
                Some(r) => {
                    let (intros, body, writer) = self.peel(node);
                    let cases = self.cited_parts(&reason.just.from);
                    self.recursion_clause(&r, &cases, body, &writer).map(|t| {
                        match intros.is_empty() {
                            true => t,
                            false => format!(
                                "by intro {}; {}",
                                intros.join(" "),
                                as_tactic(&t)
                            ),
                        }
                    })
                }
                // A function the header lets by its value: its equation
                // put in, f(a) its value at a, and the claim closed.
                None => match self.header_function_cited(reason.just) {
                    Some(hyp) => Route::Built(format!(
                        "by (try simp only [{hyp}]); first | done | parley_side"
                    )),
                    None => Route::Built("by parley_side".to_string()),
                },
            },
            // A requires line's lines, or one manipulation of one of them:
            // the fact is what they say, or follows from it by arithmetic.
            Head::Lines | Head::Manipulation(_) => {
                Route::Built("by parley_side".to_string())
            }
        }
    }

    /// A claim's leading "for all" taken off: the names its letters and
    /// their guards are introduced by, the body, and the letters in scope
    /// with the claim's own added.
    fn peel<'n>(&self, node: &'n Node) -> (Vec<String>, &'n Node, Writer<'a>) {
        let mut writer = self.writer.with_letters(self.writer.letters.clone());
        let mut intros = Vec::new();
        let mut body = node;
        while body.notation() == crate::notations::FOR_ALL {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let name = super::names::letter(&letter.text);
            // Over a range, a number system or another set of numbers, [0,
            // 1]: the letter of the numbers' type, and where the type does
            // not say it, the fact that it is in the set. Over a set of
            // things, sets or a group's elements, a member of their type,
            // and the fact.
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
                (LetterType::Number(super::templates::Num::Int), true)
            } else {
                match (super::expr::system_of(set), self.writer.set_members(set)) {
                    (Some(s), _) => (
                        LetterType::Number(super::expr::letter_type(s)),
                        s == super::expr::System::Positive,
                    ),
                    (None, Some(super::expr::Members::Numbers(n))) => {
                        (LetterType::Number(n), true)
                    }
                    (None, Some(m)) => (LetterType::Member(m), true),
                    (None, None) => break,
                }
            };
            writer.letters.insert(letter.text.to_string(), ty);
            intros.push(name.clone());
            if guarded {
                intros.push(format!("h_{name}"));
            }
            body = inner;
        }
        (intros, body, writer)
    }

    /// The proof of a claim by a method that closes it, with the letters
    /// `writer` holds.
    fn method_proof(
        &self,
        reason: Reason,
        m: Method,
        node: &Node,
        writer: &Writer,
    ) -> Route<String> {
        let just = reason.just;
        Route::Built(match m {
            Method::Algebra => {
                // A cited equation of a narrower type is combined as the
                // claim's type has it.
                let mut cited = self.cited_parts(&just.refs);
                for c in &mut cited {
                    if let Some(read) = self.read_at_claim(c, node) {
                        *c = read;
                    }
                }
                // A define the step cites is written out, in the claim and
                // in each line it cites, as the checker reads the step: in
                // Lean, its equation rewrites them all, and the casts it
                // leaves are pushed in. Lines are widened after, as they
                // then read.
                let defines = self.cited_defines(&just.refs);
                let mut claim = node.clone();
                for d in &defines {
                    claim = self.put_define(&claim, d);
                    cited.retain(|c| c.proof != d.proof);
                    for c in &mut cited {
                        c.node = self.put_define(&c.node, d);
                    }
                }
                let mut haves = Vec::new();
                for c in &mut cited {
                    match self.widened(&c.node, &c.proof, &claim, writer) {
                        Route::Built(w) => {
                            haves.extend(w.have);
                            c.proof = w.name;
                        }
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // Each read with its identity elements dropped, as the
                // checker decides it: F(0 + 1) and F(1) are one term.
                let ctx = self.sources.ctx;
                let claim = crate::matching::bare(&claim, ctx);
                for c in &mut cited {
                    c.node = crate::matching::bare(&c.node, ctx);
                }
                let proof = match super::algebra::algebra(
                    writer,
                    self.sources.targets,
                    &claim,
                    &cited,
                ) {
                    Route::Built(t) => t,
                    declined => return declined,
                };
                let mut lines = written_out(&defines);
                lines.extend(haves);
                return Route::Built(with_haves(&lines, &proof));
            }
            Method::Arithmetic => "by parley_arith".to_string(),
            // Arithmetic of real numbers, √8 = 2√2 or ln(2) ≠ 0: its own
            // tactic, which tries `parley_arith` first (`RealTactics`).
            Method::RealArithmetic => "by parley_real".to_string(),
            // Rows are linear moves on the line the first row cites, so the
            // claim follows from that line by linear arithmetic, as a step
            // with no rows does from the lines it cites.
            // An order is left to the ways of orders alone; a chain of
            // equations, A = B = C, to `parley_side`.
            Method::Inequalities | Method::Transitivity | Method::Antisymmetry => {
                // A cited "for all", a(n) = 1 − 1/2ⁿ for every n, is read
                // at the claim's letter, which linear arithmetic can use.
                let read: Vec<String> = self
                    .cited_parts(&just.refs)
                    .iter()
                    .filter_map(|c| self.read_at_claim(c, node))
                    .map(|at| format!("have := {}", at.proof))
                    .collect();
                let close = match node.notation() == ORDER {
                    true => "parley_order",
                    false => "parley_side",
                };
                match read.as_slice() {
                    [] => format!("by {close}"),
                    _ => format!("by {}; {close}", read.join("; ")),
                }
            }
            Method::Inspection => "by parley_side".to_string(),
            Method::Substitute => return self.substitute(just, node, writer),
            Method::Calculation => return self.calculation(just, writer),
            Method::Exhibit => return self.exhibit(just, node),
            Method::Instantiate => return self.instantiate(just, node, writer),
            Method::Membership => return self.membership(just, node, writer),
            Method::Restate | Method::Join => "by parley_side".to_string(),
            other => {
                return Route::no(format!(
                    "the method {} is not written in Lean yet",
                    other.as_str()
                ))
            }
        })
    }

    /// A define in a proof, `let t = 1/j, a real number`: Lean's `set`, of
    /// the type the line names, or else of the least that holds its value,
    /// whose hypothesis is the define's equation, named by its label.
    fn define(&mut self, d: usize, depth: usize) -> Route<()> {
        self.defined.insert(d);
        let line = &self.thm.defines[d];
        let crate::outcome::Route::Built(crate::corpus::DefineParts::One(def)) =
            crate::corpus::define_parts(&line.text)
        else {
            return Route::no("a define of a function or a phrase");
        };
        if !def.params.is_empty() {
            return self.define_function(d, &def, depth);
        }
        let bodies: Vec<&Node> = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == line.line)
            .map(|(_, node)| node)
            .collect();
        let [body] = bodies.as_slice() else {
            return Route::no(
                "a define whose value the checker did not read as one term",
            );
        };
        let body = (*body).clone();
        // A name for an element or a set, `let b = a⁻¹`: of the type its
        // value has, written as the writer writes such terms.
        let set_like = self
            .writer
            .member_kind(&body)
            .map(|m| m.letter())
            .or_else(|| self.writer.members_of(&body).map(LetterType::Set));
        if let Some(ty) = set_like.filter(|_| def.kind.is_none()) {
            let value = match self.writer.set_term(&body) {
                Route::Built(v) => v,
                Route::Declined(why) => return Route::Declined(why),
            };
            self.name_value(d, &def.name, ty, &value.text, body, depth);
            return Route::Built(());
        }
        use super::templates::Num;
        let ty = match def.kind.as_deref() {
            Some("a real number") => Num::Real,
            Some("a rational number") => Num::Rat,
            Some("an integer") => Num::Int,
            // A whole number above or at 0 is an integer; that it is not
            // negative is a fact the line's reason shows, not a type.
            Some(
                "a positive integer" | "a natural number" | "a nonnegative integer",
            ) => Num::Int,
            Some("a complex number") => Num::Complex,
            Some(other) => return Route::no(format!("a define of {other}")),
            None => match self.writer.carrier(&body) {
                Route::Built(n) => n,
                Route::Declined(why) => return Route::Declined(why),
            },
        };
        // A whole number whose value is wider, `let e = p/d, a positive
        // integer`: Lean's ℤ division would round, so the name is the
        // number its reason shows the value to be.
        let wider = match self.writer.carrier(&body) {
            Route::Built(n) => n > ty,
            Route::Declined(why) => return Route::Declined(why),
        };
        if def.kind.is_some() && wider {
            return self.kinded_witness(d, &def.name, body, depth);
        }
        let value = match self.writer.number_fixed(&body, ty) {
            Route::Built(v) => v,
            Route::Declined(why) => return Route::Declined(why),
        };
        self.name_value(
            d,
            &def.name,
            LetterType::Number(ty),
            &value.text,
            body,
            depth,
        );
        Route::Built(())
    }

    /// What closes a block or a theorem once its steps are written: its last
    /// step by name, `exact s3`, where that step says what is owed as Lean
    /// writes both, and otherwise `parley_side`, which finds the line. What
    /// is owed is the claim, or of a "for all" whose letter the block lets,
    /// what it says at that letter.
    fn closing(&self, last: Option<usize>, owed: &Node) -> String {
        let side = "parley_side".to_string();
        let owed = match owed.children.as_slice() {
            [letter, _, body]
                if owed.notation() == crate::notations::FOR_ALL
                    && self.writer.letters.contains_key(letter.text.as_str()) =>
            {
                body
            }
            _ => owed,
        };
        let Some(number) = last.and_then(|i| self.thm.steps[i].number.number()) else {
            return side;
        };
        let Some([(said, name)]) =
            self.trees.get(&number.to_string()).map(Vec::as_slice)
        else {
            return side;
        };
        match (self.writer.formula(said), self.writer.formula(owed)) {
            (Route::Built(a), Route::Built(b)) if a.text == b.text => {
                format!("exact {name}")
            }
            _ => side,
        }
    }

    /// A define's name given its value, `set b : G := a⁻¹ with hD1`: the
    /// letter of its type, and the line's equation, b = a⁻¹, by its label.
    fn name_value(
        &mut self,
        d: usize,
        name: &str,
        ty: LetterType,
        value: &str,
        body: Node,
        depth: usize,
    ) {
        let line = &self.thm.defines[d];
        let label = line_name(&line.label);
        let (at, page_label) = (line.line, line.label.clone());
        self.push(
            format!(
                "{}set {} : {} := {value} with {label}",
                pad(depth),
                super::names::letter(name),
                ty.lean()
            ),
            at,
            Spot::Statement,
        );
        self.writer.letters.insert(name.to_string(), ty);
        let letter = Node::name(body.sort.clone(), name);
        let equation = Node::of(
            crate::notations::EQUALS,
            crate::formula::node::Sort::of("formula"),
            vec![letter, body],
        );
        self.named.insert(page_label.clone(), vec![label.clone()]);
        self.trees.insert(page_label, vec![(equation, label)]);
    }

    /// A define naming a whole number its value is shown to be, `let e =
    /// p/d, a positive integer` with `p/d ∈ ℕ` its reason's fact: that
    /// fact proved by the reason, as a requires line is, and the name taken
    /// from it, `obtain ⟨e, hD1_pos, hD1⟩`, so that the define's equation
    /// e = p/d is said in the value's type.
    fn kinded_witness(
        &mut self,
        d: usize,
        name: &str,
        body: Node,
        depth: usize,
    ) -> Route<()> {
        let line = &self.thm.defines[d];
        let members = &self.sources.checked.grammar.members;
        let kinded = match line.kinded(&self.thm.path, members) {
            Ok(Some(k)) => k,
            Ok(None) => return Route::no("a define of a kind with no reason"),
            Err(p) => return Route::no(p.to_string()),
        };
        let fact = match self.tree(&kinded.shown.fact) {
            Route::Built(n) => n,
            Route::Declined(why) => return Route::Declined(why),
        };
        let [_, set] = fact.children.as_slice() else {
            return Route::no("a kind's fact that is no membership");
        };
        // ℕ says its witness is above 0 beside its value; ℕ₀ and ℤ only the
        // value.
        let (ty, positive) = match super::expr::system_of(set) {
            Some(super::expr::System::Positive) => (super::templates::Num::Nat, true),
            Some(super::expr::System::NonNegative) => {
                (super::templates::Num::Nat, false)
            }
            Some(super::expr::System::Type(super::templates::Num::Int)) => {
                (super::templates::Num::Int, false)
            }
            _ => return Route::no("a define of a kind other than ℕ, ℕ₀ or ℤ"),
        };
        let fact_text = match self.writer.formula(&fact) {
            Route::Built(f) => f.text,
            Route::Declined(why) => return Route::Declined(why),
        };
        let Ok(just) = &kinded.shown.by else {
            return Route::no("a define whose reason does not read");
        };
        let reason = Reason {
            just,
            cited: self.rec.cited_requires.get(&kinded.shown.line),
        };
        let proof = match self.proof_of(reason, 0, &fact) {
            Route::Built(p) => p,
            Route::Declined(why) => return Route::Declined(why),
        };
        let label = line_name(&line.label);
        let (at, page_label) = (line.line, line.label.clone());
        let letter = super::names::letter(name);
        let parts = match positive {
            true => format!("{letter}, {label}_pos, {label}"),
            false => format!("{letter}, {label}"),
        };
        self.push(
            format!(
                "{p}have {label}_kind : {fact_text} := {proof}\n{p}obtain ⟨{parts}⟩ := {label}_kind",
                p = pad(depth)
            ),
            at,
            Spot::Statement,
        );
        self.writer
            .letters
            .insert(name.to_string(), LetterType::Number(ty));
        let equation = Node::of(
            crate::notations::EQUALS,
            crate::formula::node::Sort::of("formula"),
            vec![Node::name(body.sort.clone(), name), body],
        );
        self.named.insert(page_label.clone(), vec![label.clone()]);
        self.witnessed.insert(page_label.clone());
        self.trees.insert(page_label, vec![(equation, label)]);
        Route::Built(())
    }

    /// A define of a function of one number in a proof, `let S(m) =
    /// Σ(j = 1 to m) 3^j, for m ∈ ℕ`: Lean's `set` of a function from the
    /// type of the set its argument runs over to the least type holding its
    /// value, whose hypothesis, named by the label, a step citing the define
    /// unfolds it by (`written_out`).
    fn define_function(
        &mut self,
        d: usize,
        def: &crate::corpus::Define,
        depth: usize,
    ) -> Route<()> {
        let line = &self.thm.defines[d];
        let [param] = def.params.as_slice() else {
            return Route::no("a define of a function of more than one argument");
        };
        // The checker reads the line's argument, the set it runs over and
        // the value apart.
        let read: Vec<&Node> = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == line.line)
            .map(|(_, node)| node)
            .collect();
        let over = |n: &&&Node| {
            matches!(
                n.notation(),
                crate::notations::NUMBER_SYSTEMS | crate::notations::INTEGER_RANGE
            )
        };
        // Over a number system, a range, or a set of numbers, X of X ⊆ ℤ.
        let of_numbers = |n: &&&Node| {
            !(n.is_name() && *n.text == *param.name)
                && matches!(
                    self.writer.set_members(n),
                    Some(super::expr::Members::Numbers(_))
                )
        };
        let Some(domain) = read
            .iter()
            .find(over)
            .or_else(|| read.iter().find(of_numbers))
        else {
            return Route::no("a define of a function on other than a number system");
        };
        let bodies: Vec<&&Node> = read
            .iter()
            .filter(|n| !over(n) && !of_numbers(n))
            .filter(|n| !(n.is_name() && *n.text == *param.name))
            .collect();
        let [body] = bodies.as_slice() else {
            return Route::no(
                "a define whose value the checker did not read as one term",
            );
        };
        // A function on ℕ, ℕ₀ or a range {0, …, m} takes integers, as the
        // writer's sequences do, so that q(j) of a sum's index is written
        // as it stands; its values off the range are none of the page's.
        let from = match (
            super::expr::system_of(domain),
            self.writer.set_members(domain),
        ) {
            (Some(system), _) => {
                super::expr::letter_type(system).max(super::templates::Num::Int)
            }
            (None, _) if domain.notation() == crate::notations::INTEGER_RANGE => {
                super::templates::Num::Int
            }
            (None, Some(super::expr::Members::Numbers(n))) => {
                n.max(super::templates::Num::Int)
            }
            (None, _) => {
                return Route::no(
                    "a define of a function on a set Lean has no type for",
                )
            }
        };
        // The value is read with the argument a number of that type, and
        // the argument is no letter of the proof's after it.
        let before = self
            .writer
            .letters
            .insert(param.name.clone(), LetterType::Number(from));
        let value = match self.writer.carrier(body) {
            Route::Built(to) => self.writer.number_fixed(body, to).map(|v| (to, v)),
            Route::Declined(why) => Route::Declined(why),
        };
        match before {
            Some(ty) => self.writer.letters.insert(param.name.clone(), ty),
            None => self.writer.letters.shift_remove(&param.name),
        };
        let (to, value) = match value {
            Route::Built(v) => v,
            Route::Declined(why) => return Route::Declined(why),
        };
        let name = super::names::letter(&def.name);
        let label = line_name(&line.label);
        self.push(
            format!(
                "{}set {name} : {} → {} := fun {} => {} with {label}",
                pad(depth),
                from.lean(),
                to.lean(),
                super::names::letter(&param.name),
                value.text
            ),
            line.line,
            Spot::Statement,
        );
        self.writer
            .letters
            .insert(def.name.clone(), LetterType::Function { from, to });
        self.named.insert(line.label.clone(), vec![label]);
        Route::Built(())
    }

    /// A define of the theorem's file, outside the theorem, that its
    /// statement is read with: Lean's `set`, of the least type holding the
    /// term it names, its equation named by the name.
    fn define_outside(&mut self, name: &str, body: &Node) -> Route<()> {
        let ty = match self.writer.carrier(body) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        };
        let value = match self.writer.number_fixed(body, ty) {
            Route::Built(v) => v,
            Route::Declined(d) => return Route::Declined(d),
        };
        let lean = super::names::letter(name);
        self.push(
            format!(
                "  set {lean} : {} := {} with h_{lean}",
                self.writer.type_name(ty),
                value.text
            ),
            self.thm.line,
            Spot::Statement,
        );
        self.writer
            .letters
            .insert(name.to_string(), LetterType::Number(ty));
        Route::Built(())
    }

    /// `exhibit`: the claim's "there is", with the values the checker read
    /// for its letters, and what it says of them left to `parley_side`.
    fn exhibit(&self, just: &Justification, node: &Node) -> Route<String> {
        let Some(step) = self.thm.steps.iter().find(|s| s.just.line == just.line)
        else {
            return Route::no("an exhibit that is no step's");
        };
        let Some(binding) = self
            .rec
            .exhibited
            .get(&step.line)
            .and_then(|all| all.iter().flatten().next())
        else {
            return Route::no("an exhibit the checker read no values for");
        };
        // there is a ∈ X with nothing said of a, `∃ a ∈ X, True`: the
        // member, that it is in X, and nothing.
        if let ("there-is-some", [letter, set]) =
            (&*node.notation_name(), node.children.as_slice())
        {
            let Some(value) = binding.get(&letter.text) else {
                return Route::no(format!("no value for {}", letter.text));
            };
            let Some(members) = self.writer.set_members(set) else {
                return Route::no("there is some member of a set with no Lean type");
            };
            return self
                .writer
                .element_term(value, &members)
                .map(|v| format!("⟨{}, by parley_set_side, trivial⟩", v.text));
        }
        let mut parts = Vec::new();
        let mut known = Vec::new();
        let mut body = node;
        while body.notation() == crate::notations::THERE_IS {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let Some(value) = binding.get(&letter.text) else {
                return Route::no(format!("no value for {}", letter.text));
            };
            // A member of a set: the value as the writer writes a member,
            // and its membership left to `parley_side`.
            if let Some(members) = self.writer.members_of(set) {
                match self.writer.element_term(value, &members) {
                    Route::Built(p) => parts.push(p.text),
                    Route::Declined(d) => return Route::Declined(d),
                }
                parts.push(format!("by {}parley_side", known.concat()));
                body = inner;
                continue;
            }
            // A polynomial: the function, and that it is one.
            if &*set.notation_name() == "polynomials" {
                match self.writer.set_term(value) {
                    Route::Built(p) => parts.push(p.text),
                    Route::Declined(d) => return Route::Declined(d),
                }
                parts.push(format!("by {}parley_side", known.concat()));
                body = inner;
                continue;
            }
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
                (super::templates::Num::Int, true)
            } else {
                match super::expr::system_of(set) {
                    Some(s) => (
                        super::expr::letter_type(s),
                        s == super::expr::System::Positive,
                    ),
                    None => {
                        return Route::no("a value of a letter of no number system")
                    }
                }
            };
            match self.witness(value, ty) {
                Route::Built(w) => {
                    parts.push(w.term);
                    known.extend(w.known);
                }
                Route::Declined(d) => return Route::Declined(d),
            }
            if guarded {
                parts.push(format!("by {}parley_side", known.concat()));
            }
            body = inner;
        }
        if parts.is_empty() {
            return Route::no("an exhibit of no \"there is\"");
        }
        parts.push(facts_shaped(body, &known.concat()));
        Route::Built(format!("⟨{}⟩", parts.join(", ")))
    }

    /// `instantiate`: the "for all" line at the values given, each guard
    /// left to `parley_side`, and an "if" in it applied where the claim is
    /// what it gives.
    fn instantiate(
        &self,
        just: &Justification,
        node: &Node,
        writer: &Writer,
    ) -> Route<String> {
        let Some(target) = just
            .target
            .as_deref()
            .or(just.refs.first().map(String::as_str))
        else {
            return Route::no("an instantiate of no line");
        };
        // The sentence, or the part of one, of the line that says "for all".
        let parts = self.cited_parts(&[target.to_string()]);
        // Of several, the one that asks the fewest conditions of the values.
        let conditions = |n: &Node| -> usize {
            let mut body = n;
            let mut asked = 0;
            while let [_, set, inner] = body.children.as_slice() {
                if body.notation() != crate::notations::FOR_ALL {
                    break;
                }
                let guarded = set.notation() == crate::notations::INTEGER_RANGE
                    || super::expr::system_of(set)
                        == Some(super::expr::System::Positive);
                asked += usize::from(guarded);
                body = inner;
            }
            asked + usize::from(matches!(body.notation(), CONDITIONAL | IMPLICATION))
        };
        let Some(part) = parts
            .iter()
            .filter(|c| c.node.notation() == crate::notations::FOR_ALL)
            .min_by_key(|c| conditions(&c.node))
        else {
            return Route::no(format!(
                "instantiate in {target}, which says no \"for all\""
            ));
        };
        // With no values given, the line is read at the block's letter, as
        // the checker reads it.
        if just.values.is_empty() {
            if let Some(read) = self.read_at_claim(part, node) {
                return Route::Built(close(node, &read.proof));
            }
        }
        let (line, name) = (&part.node, &part.proof);
        let mut args = vec![name.clone()];
        let mut to_nat: Vec<String> = Vec::new();
        let mut body = line;
        while body.notation() == crate::notations::FOR_ALL {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            // A letter given no value is read at the block's letter of its
            // type the claim writes and the line does not, as the checker
            // reads it.
            let value = match just.values.pairs().find(|(n, _)| *n == &*letter.text) {
                Some((_, given)) => match self.tree(given) {
                    Route::Built(v) => v,
                    Route::Declined(d) => return Route::Declined(d),
                },
                None => {
                    // The names the line writes free: a letter it binds
                    // itself, as the block's may be named, is not one.
                    let own = crate::matching::free_names(
                        line,
                        &self.sources.checked.grammar.binders(),
                    );
                    // A range's letter is an integer.
                    let ty = if set.notation() == crate::notations::INTEGER_RANGE {
                        Some(super::templates::Num::Int)
                    } else {
                        super::expr::system_of(set).map(super::expr::letter_type)
                    };
                    // A set's letter is a member of its kind.
                    let member = writer.members_of(set).map(|m| m.letter());
                    let at: Vec<String> = node
                        .names()
                        .into_iter()
                        .filter(|n| !own.contains(n))
                        .filter(|n| {
                            let has = writer.letters.get(n.as_str());
                            ty.is_some_and(|t| has == Some(&LetterType::Number(t)))
                                || (member.is_some() && has == member.as_ref())
                        })
                        .collect();
                    // A claim that is itself a "for all" keeps the letters
                    // given no value: the line is read at those given.
                    let [at] = at.as_slice() else {
                        if node.notation() == crate::notations::FOR_ALL {
                            break;
                        }
                        return Route::no(format!("no value for {}", letter.text));
                    };
                    Node::name(letter.sort.clone(), at)
                }
            };
            // A member of a set: the value, and that it is in the set.
            if let Some(members) = writer.members_of(set) {
                match writer.element_term(&value, &members) {
                    Route::Built(p) => args.push(p.at(super::expr::MAX)),
                    Route::Declined(d) => return Route::Declined(d),
                }
                args.push("(by parley_side)".to_string());
                body = inner;
                continue;
            }
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
                (super::templates::Num::Int, true)
            } else {
                match super::expr::system_of(set) {
                    Some(s) => (
                        super::expr::letter_type(s),
                        s == super::expr::System::Positive,
                    ),
                    None => {
                        return Route::no("a value of a letter of no number system")
                    }
                }
            };
            // A letter of ℕ given an integer the page shows is in ℕ, b²
            // with b ∈ ℤ, takes its `toNat`, whose cast back is the integer
            // once it is not negative.
            let natural = ty == super::templates::Num::Nat;
            let in_nat = writer.number_fixed(&value, ty);
            match (in_nat, natural) {
                (Route::Built(p), _) => {
                    args.push(p.at(super::expr::MAX));
                    if guarded {
                        args.push("(by parley_side)".to_string());
                    }
                }
                (Route::Declined(_), true) => {
                    let int =
                        match writer.number_fixed(&value, super::templates::Num::Int) {
                            Route::Built(p) => p.at(super::expr::MAX),
                            Route::Declined(d) => return Route::Declined(d),
                        };
                    args.push(format!("{int}.toNat"));
                    if guarded {
                        args.push(format!(
                            "(Int.lt_toNat.mpr (show ((0 : ℕ) : ℤ) < {int} by parley_side))"
                        ));
                    }
                    to_nat.push(int);
                }
                (Route::Declined(d), false) => return Route::Declined(d),
            }
            body = inner;
        }
        let gives = matches!(body.notation(), CONDITIONAL | IMPLICATION)
            && !matches!(node.notation(), CONDITIONAL | IMPLICATION);
        if gives {
            args.push("(by parley_side)".to_string());
        }
        let term = format!("({})", args.join(" "));
        if to_nat.is_empty() {
            return Route::Built(close(node, &term));
        }
        let rewrites: Vec<String> = to_nat
            .iter()
            .map(|t| format!("Int.toNat_of_nonneg (show (0 : ℤ) ≤ {t} by parley_side)"))
            .collect();
        Route::Built(format!(
            "by have h := {term}; rw [{}] at h; exact h",
            rewrites.join(", ")
        ))
    }

    /// The defines among the lines a step cites, each as its equation says
    /// it: the checker reads such a step with them written out.
    fn cited_defines(&self, refs: &[String]) -> Vec<CitedDefine> {
        let mut out: Vec<CitedDefine> = refs
            .iter()
            .filter(|r| self.thm.defines.iter().any(|d| d.label == **r))
            .filter(|r| !self.witnessed.contains(*r))
            .flat_map(|r| self.trees.get(r).into_iter().flatten())
            .filter_map(|(n, proof)| match n.children.as_slice() {
                [name, value] if n.notation() == EQUALITY && name.is_name() => {
                    Some(CitedDefine {
                        name: name.clone(),
                        value: value.clone(),
                        proof: proof.clone(),
                        param: None,
                    })
                }
                _ => None,
            })
            .collect();
        out.extend(refs.iter().filter_map(|r| self.cited_function_define(r)));
        out
    }

    /// A define of a function of one argument a step cites by its label,
    /// q(j) = F(j)²: its name, its body, its argument and the name of the
    /// line Lean's `set` gives it; None for any other reference.
    fn cited_function_define(&self, label: &str) -> Option<CitedDefine> {
        let line = self
            .thm
            .defines
            .iter()
            .find(|d| d.label == label && d.line > self.thm.conclusion_line)?;
        let Route::Built(crate::corpus::DefineParts::One(def)) =
            crate::corpus::define_parts(&line.text)
        else {
            return None;
        };
        let [param] = def.params.as_slice() else {
            return None;
        };
        let bodies: Vec<&Node> = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == line.line)
            .map(|(_, node)| node)
            .filter(|n| n.notation() != crate::notations::NUMBER_SYSTEMS)
            .filter(|n| !(n.is_name() && *n.text == *param.name))
            .collect();
        let [body] = bodies.as_slice() else {
            return None;
        };
        let proof = self.named.get(label)?.first()?.clone();
        Some(CitedDefine {
            name: Node::name(crate::formula::Sort::none(), &def.name),
            value: (*body).clone(),
            proof,
            param: Some(param.name.clone()),
        })
    }

    /// A line with a cited define put in: its name for its value, or each
    /// application q(a) of a function's for its body at a.
    fn put_define(&self, node: &Node, d: &CitedDefine) -> Node {
        let Some(param) = &d.param else {
            return put_for(node, &d.name, &d.value);
        };
        if let (crate::notations::APPLICATION, [f, a]) =
            (node.notation(), node.children.as_slice())
        {
            if f.is_name() && f.text == d.name.text {
                let a = self.put_define(a, d);
                let put = crate::matching::Binding::from([(
                    crate::formula::symbol::Symbol::of(param),
                    a,
                )]);
                return crate::matching::substitute_apart_by(
                    &d.value,
                    &put,
                    &self.sources.checked.grammar.binders(),
                );
            }
        }
        if node.children.is_empty() {
            return node.clone();
        }
        node.with_children(
            node.children
                .iter()
                .map(|c| self.put_define(c, d))
                .collect(),
        )
    }

    /// `substitute`: the claim is a line, or the left side of a calculation's
    /// link, with a term put for another by an equation, which a line says
    /// or arithmetic works out.
    fn substitute(
        &self,
        just: &Justification,
        claim: &Node,
        writer: &Writer,
    ) -> Route<String> {
        if !just.rows.is_empty() {
            return self.substitute_rows(just, writer);
        }
        // Substituting from a function the header lets by its value: its
        // equation for every x, put in where f is applied.
        if let Some(crate::corpus::skeleton::Source::At(place)) = &just.source {
            if let Some(hyp) = self.header_function_named(place.named()) {
                return Route::Built(format!(
                    "by (try simp only [{hyp}] at *); first | done | parley_side"
                ));
            }
        }
        let mut haves = Vec::new();
        // The equation's own name, where it is widened to the claim's type.
        let mut stated: Option<String> = None;
        // The equation put in, as a tree.
        let mut put: Option<Node> = None;
        let equation = match (&just.source, &just.equation) {
            (Some(crate::corpus::skeleton::Source::At(place)), written) => {
                // Of a line saying several things, the equation the step
                // writes, as Lean writes both; else the one that turns the
                // claim's left side into its right, as a calculation's row
                // "= 0² + 0²  substitute D1" puts B = 0 of "A = 0 and B = 0";
                // else its first equation.
                let wanted = written
                    .as_ref()
                    .and_then(|w| self.tree(w).built())
                    .and_then(|n| self.writer.formula(&n).built())
                    .map(|p| p.text);
                let parts = self.cited_parts(&[place.named().to_string()]);
                let grammar = &self.sources.checked.grammar;
                let chosen = parts
                    .iter()
                    .find(|c| {
                        wanted.is_some()
                            && self.writer.formula(&c.node).built().map(|p| p.text)
                                == wanted
                    })
                    .or_else(|| {
                        (claim.notation() == crate::notations::EQUALITY)
                            .then(|| {
                                parts.iter().find(|c| {
                                    c.node.notation() == crate::notations::EQUALITY
                                        && makes_claim(&c.node, claim, grammar)
                                })
                            })
                            .flatten()
                    })
                    .or_else(|| {
                        parts
                            .iter()
                            .find(|c| c.node.notation() == crate::notations::EQUALITY)
                    })
                    .or(parts.first())
                    .map(|c| (c.node.clone(), c.proof.clone()));
                // Put into a line Lean's types give, `⌊A⌋ ∈ ℤ`, the claim is
                // a membership the equation shows.
                if let Some((line, name)) = &chosen {
                    if let Some(proof) =
                        member_by_equation(&self.writer, line, name, claim)
                    {
                        return Route::Built(proof);
                    }
                }
                match chosen.as_ref().map(|(n, p)| (n, p)) {
                    Some((line, name)) => match self.widened(line, name, claim, writer)
                    {
                        Route::Built(w) => {
                            haves.extend(w.have);
                            stated = Some(name.clone());
                            put = Some(line.clone());
                            w.name
                        }
                        Route::Declined(d) => return Route::Declined(d),
                    },
                    None => {
                        return Route::no(format!(
                            "substitute from {}, which has no Lean name",
                            place.named()
                        ))
                    }
                }
            }
            (_, Some(written)) => {
                let node = match self.tree(written) {
                    Route::Built(n) => n,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // An equation shown by real arithmetic where it is put, ln(8)
                // = 3·ln(2) (real arithmetic), is the real arithmetic's.
                let real = matches!(
                    just.source,
                    Some(crate::corpus::skeleton::Source::RealArithmetic)
                );
                let tactic = if real { "parley_real" } else { "parley_side" };
                match self.writer.formula(&node) {
                    Route::Built(p) => format!("(show {} by {tactic})", p.text),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            _ => return Route::Built("by parley_side".to_string()),
        };
        // The line put into, cast up to the claim's type where it is
        // narrower. Of a line saying several things, the one the equation
        // turns into the claim; else the one that says what the claim does,
        // divides where the claim divides; else the first.
        let grammar = &self.sources.checked.grammar;
        let turns = |part: &Node| -> bool {
            let Some([left, right]) = put.as_ref().map(|e| e.children.as_slice())
            else {
                return false;
            };
            let want = grammar.print(claim);
            [(left, right), (right, left)].iter().any(|(from, to)| {
                grammar.print(&put_term(part, from, to, grammar)) == want
            })
        };
        // Where no part turns into the claim with the equation put for every
        // place, the equation is put for some places only, gcd(a, b) ∣ b
        // from b ∣ b, and each part that says what the claim does is offered.
        // A "for all" of the line is judged by what it says at the block's
        // letter, p(x) = (x − a)·q(x) + p(a) of "… for all x ∈ ℂ" at x, and
        // put into by its own name, which the tactic rewrites under the
        // quantifier.
        let at_claim = |node: &Node| -> Node {
            let cited = super::algebra::Cited {
                node: node.clone(),
                proof: String::new(),
            };
            self.read_at_claim(&cited, claim)
                .map_or_else(|| node.clone(), |at| at.node)
        };
        let candidates: Vec<&(Node, String)> = just
            .into
            .as_ref()
            .and_then(|place| self.trees.get(place.named()))
            .map(|t| {
                let turned: Vec<_> = t
                    .iter()
                    .filter(|(n, _)| turns(&at_claim(n)))
                    .take(1)
                    .collect();
                if !turned.is_empty() {
                    return turned;
                }
                let alike: Vec<_> = t
                    .iter()
                    .filter(|(n, _)| at_claim(n).notation() == claim.notation())
                    .collect();
                if !alike.is_empty() {
                    return alike;
                }
                t.iter().take(1).collect()
            })
            .unwrap_or_default();
        let mut into = Vec::new();
        for (line, name) in candidates {
            match self.widened(line, name, claim, writer) {
                Route::Built(w) => {
                    haves.extend(w.have);
                    into.push(w.name);
                }
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // The equation is put in at the type its term has where it stands:
        // widened to the claim's, or as stated, where the term sits in a
        // part of a fixed type, (4 − 2)! of a claim in ℚ.
        // Of several lines, each is rewritten into before any is simplified,
        // since a simplification that loops ends the search (`parley_put_at`).
        let own = stated.filter(|s| *s != equation);
        let mut ways: Vec<String> = Vec::new();
        let tactics: &[&str] = if into.len() > 1 {
            &["parley_put_at", "parley_subst_at"]
        } else {
            &["parley_subst_at"]
        };
        for tactic in tactics {
            for line in &into {
                ways.push(format!("{tactic} {equation} {line}"));
                if let Some(own) = &own {
                    ways.push(format!("{tactic} {own} {line}"));
                }
            }
        }
        if into.is_empty() {
            ways.push(format!("parley_subst {equation}"));
            if let Some(own) = &own {
                ways.push(format!("parley_subst {own}"));
            }
        }
        let tactic = match ways.as_slice() {
            [one] => format!("by {one}"),
            _ => format!("by first | {}", ways.join(" | ")),
        };
        Route::Built(with_haves(&haves, &tactic))
    }

    /// A cited "for all" of one letter, read where a closure method reads
    /// it: at the one letter of the claim of its type that it does not
    /// itself name, the letter of the block the step stands in. None where
    /// the line says no such "for all", or the claim has no one such letter.
    fn read_at_claim(
        &self,
        cited: &super::algebra::Cited,
        claim: &Node,
    ) -> Option<super::algebra::Cited> {
        self.read_at_letters(cited, &claim.names())
    }

    /// `read_at_claim`, at the one letter among `names` of the type the
    /// "for all" ranges over that it does not itself name.
    fn read_at_letters(
        &self,
        cited: &super::algebra::Cited,
        names: &std::collections::BTreeSet<String>,
    ) -> Option<super::algebra::Cited> {
        let [letter, set, body] = cited.node.children.as_slice() else {
            return None;
        };
        if cited.node.notation() != crate::notations::FOR_ALL || !letter.is_name() {
            return None;
        }
        // A guarded "for all", over ℕ, asks a proof besides the letter, that
        // it is above 0, which the lines in scope give; one over any other
        // set, ℝ ∖ {5} or B, that the letter is in it.
        let (ty, guard) = match super::expr::system_of(set) {
            Some(system) => (
                LetterType::Number(super::expr::letter_type(system)),
                match system == super::expr::System::Positive {
                    true => " (by parley_side)",
                    false => "",
                },
            ),
            None => (
                self.writer.set_members(set)?.letter(),
                " (by parley_set_side)",
            ),
        };
        // The names the line writes free: the letter it binds may be named
        // as the block's is.
        let own = crate::matching::free_names(
            &cited.node,
            &self.sources.checked.grammar.binders(),
        );
        let candidates: Vec<&String> = names
            .iter()
            .filter(|n| !own.contains(*n))
            .filter(|n| self.writer.letters.get(n.as_str()) == Some(&ty))
            .collect();
        let [at] = candidates.as_slice() else {
            return None;
        };
        let put = crate::matching::Binding::from([(
            letter.text,
            Node::name(letter.sort.clone(), at),
        )]);
        let read = crate::matching::substitute_apart_by(
            body,
            &put,
            &self.sources.checked.grammar.binders(),
        );
        Some(super::algebra::Cited {
            node: read,
            proof: format!("({} {}{guard})", cited.proof, super::names::letter(at)),
        })
    }

    /// `membership`. A term of a wider type said to be in a number system,
    /// an integer or a real, is one by a cited equation (`member_by_equation`).
    /// Any other membership is what the lines and the letters' types give.
    fn membership(
        &self,
        just: &Justification,
        node: &Node,
        writer: &Writer,
    ) -> Route<String> {
        for cited in self.cited_parts(&just.refs) {
            if let Some(proof) =
                member_by_equation(writer, &cited.node, &cited.proof, node)
            {
                return Route::Built(proof);
            }
        }
        Route::Built("by parley_side".to_string())
    }

    /// `substitute` in rows: each row the row above with the change its
    /// reason proves put in, the first row the line it cites, and the last
    /// the claim.
    fn substitute_rows(&self, just: &Justification, writer: &Writer) -> Route<String> {
        let Some(Ok(rows)) =
            crate::corpus::proof::substitute_rows(just, &self.thm.path)
        else {
            return Route::no("substitute rows that do not cut");
        };
        let Some(first) = rows.first() else {
            return Route::no("substitute rows with no row");
        };
        let Some(mut above) = self
            .named
            .get(first.cite.trim())
            .and_then(|n| n.first())
            .cloned()
        else {
            return Route::no(format!(
                "a first row citing {}, which has no Lean name",
                first.cite
            ));
        };
        let mut haves = Vec::new();
        for (k, row) in rows.iter().enumerate().skip(1) {
            let row_node = match self.tree(&row.formula) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            let row_text = match writer.formula(&row_node) {
                Route::Built(p) => p.text,
                Route::Declined(d) => return Route::Declined(d),
            };
            let Some(reason) = &row.reason else {
                return Route::no("a row after the first with no reason");
            };
            let Ok(by) = &reason.by else {
                return Route::no("a row whose reason does not read");
            };
            let change = match self.tree(&reason.fact) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            let change_text = match writer.formula(&change) {
                Route::Built(p) => p.text,
                Route::Declined(d) => return Route::Declined(d),
            };
            let proof = match self.proof_of(
                Reason {
                    just: by,
                    cited: self.rec.cited_requires.get(&reason.line),
                },
                0,
                &change,
            ) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            let change_name = format!("c{k}");
            haves.push(format!("have {change_name} : {change_text} := {proof}"));
            let used = match self.widened(&change, &change_name, &row_node, writer) {
                Route::Built(w) => {
                    haves.extend(w.have);
                    w.name
                }
                Route::Declined(d) => return Route::Declined(d),
            };
            let row_name = format!("row{k}");
            // At the type the term has where it stands, as `substitute`
            // puts its equation in.
            let put = if used == change_name {
                format!("parley_subst_at {used} {above}")
            } else {
                format!(
                    "first | parley_subst_at {used} {above} | parley_subst_at {change_name} {above}"
                )
            };
            haves.push(format!("have {row_name} : {row_text} := by {put}"));
            above = row_name;
        }
        Route::Built(with_haves(&haves, &format!("by exact {above}")))
    }

    /// An equation a line says, as a term to rewrite the claim with: the
    /// line itself, or, where the line is computed in a narrower type than
    /// the claim, the line cast up to the claim's type, since Lean rewrites
    /// a term only with an equation of its own type.
    fn widened(
        &self,
        line: &Node,
        name: &str,
        claim: &Node,
        writer: &Writer,
    ) -> Route<Widened> {
        let same = || {
            Route::Built(Widened {
                have: None,
                name: name.to_string(),
            })
        };
        let numbers = |n: &Node| -> Vec<Node> {
            n.children
                .iter()
                .filter(|c| writer.is_number(c))
                .cloned()
                .collect()
        };
        let sides = numbers(line);
        if line.notation() != crate::notations::EQUALITY || sides.len() != 2 {
            return same();
        }
        // The line's type as it was written: from the writer's floor.
        let mut own = writer.floor;
        for s in &sides {
            match writer.carrier(s) {
                Route::Built(n) => own = own.max(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // The claim's type, or the calculation's where the claim is a row.
        let mut wanted = self.worked_in.get().map_or(own, |w| w.max(own));
        for s in numbers(claim) {
            match writer.carrier(&s) {
                Route::Built(n) => wanted = wanted.max(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        if wanted == own {
            return same();
        }
        let mut printed = Vec::new();
        for s in &sides {
            match writer.number(s, wanted) {
                Route::Built(p) => printed.push(p.at(51)),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // Numerals alone are told their type.
        if !sides.iter().any(|s| writer.pinned(s)) {
            printed[0] = format!("({} : {})", printed[0], writer.type_name(wanted));
        }
        // The equation mapped into the wider type, its casts pushed in, and
        // compared with what is wanted up to the ring's laws.
        let wide = format!("{}_w", name.replace('.', "_"));
        Route::Built(Widened {
            have: Some(format!(
                "have {wide} : {} = {} := by have h := congrArg (fun x : {} => (x : {})) {name}; push_cast at h; linear_combination (norm := parley_norm) h",
                printed[0],
                printed[1],
                writer.type_name(own),
                writer.type_name(wanted)
            )),
            name: wide,
        })
    }

    /// `calculation`: the chain as Lean's `calc`, every term in one type,
    /// each link proved by its reason.
    fn calculation(&self, just: &Justification, writer: &Writer) -> Route<String> {
        let Some(Ok(chain)) = crate::corpus::proof::chain(just, &self.thm.path) else {
            return Route::no("a calculation whose lines do not cut");
        };
        let mut terms = vec![match self.tree(&chain.start) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        }];
        for line in &chain.lines {
            match self.tree(&line.term) {
                Route::Built(n) => terms.push(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // A chain of sets or of their members, A ∩ B = B ∩ A = ∅ or
        // F(F⁻¹(C)) = F(x), is written as sets are, and has no number type
        // to work in.
        let of_sets = terms
            .iter()
            .any(|t| writer.members_of(t).is_some() || writer.member_kind(t).is_some());
        // A chain of counts, |A| = |∅| = 0, is in ℕ∞ (`sets::count_term`).
        let of_counts = terms.iter().any(Writer::counts);
        // From the writer's floor, as the claim it proves is written.
        let mut at = writer.floor;
        let mut printed = Vec::new();
        if of_counts {
            for t in &terms {
                match writer.count_term(t) {
                    Route::Built(p) => printed.push(p.at(51)),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        } else if of_sets {
            for t in &terms {
                match writer.set_term(t) {
                    Route::Built(p) => printed.push(p.at(51)),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        } else {
            for t in &terms {
                match writer.carrier(t) {
                    Route::Built(n) => at = at.max(n),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            for t in &terms {
                match writer.number(t, at) {
                    Route::Built(p) => printed.push(p.at(51)),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            // A first term whose type nothing in it fixes, numerals alone or
            // a power whose letters are only in its exponent, is told its
            // type.
            if !writer.pinned(&terms[0]) {
                printed[0] = format!("({} : {})", printed[0], writer.type_name(at));
            }
        }
        // The claim, the first term and the last, is stated in its own
        // least type, from the writer's floor; a chain worked out in a wider
        // one moves the goal there first, as `qify` or `rify` does.
        let of_numbers = !of_sets && !of_counts;
        let mut own = writer.floor;
        for t in [terms.first(), terms.last()].into_iter().flatten() {
            if !of_numbers {
                break;
            }
            if let Route::Built(n) = writer.carrier(t) {
                own = own.max(n);
            }
        }
        // The chain is worked in `at`, its first term told the type where
        // nothing in it fixes one; a claim in a narrower type, 3^q = 2^p in
        // ℤ beside ln and exp in ℝ, is moved up to it first.
        let mut out = match (of_numbers && own < at, at) {
            (true, super::templates::Num::Rat) => String::from("by\n  qify\n  calc "),
            (true, super::templates::Num::Real) => String::from("by\n  rify\n  calc "),
            _ => String::from("by\n  calc "),
        };
        out.push_str(&printed[0]);
        let single = chain.lines.len() == 1;
        for (k, line) in chain.lines.iter().enumerate() {
            let relation = match line.relation.as_str() {
                r @ ("=" | "<" | ">" | "≤" | "≥") => r.to_string(),
                "≡" => {
                    let Some(modulus) = &line.modulus else {
                        return Route::no("a congruence with no modulus");
                    };
                    let modulus = match self.tree(modulus) {
                        Route::Built(m) => m,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    match writer.number_fixed(&modulus, super::templates::Num::Int) {
                        Route::Built(m) => format!("≡ {{}} [ZMOD {}]", m.text),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                other => return Route::no(format!("a calculation joined by {other}")),
            };
            let proof = match &line.reason {
                Some(r) => {
                    let Ok(by) = &r.by else {
                        return Route::no(
                            "a calculation line whose reason does not read",
                        );
                    };
                    let fact = match self.tree(&r.fact) {
                        Route::Built(n) => n,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    let reason = Reason {
                        just: by,
                        cited: self.rec.cited_requires.get(&r.line),
                    };
                    self.worked_in.set(Some(at));
                    let proof = self.proof_of(reason, 0, &fact);
                    self.worked_in.set(None);
                    match proof {
                        Route::Built(p) => p,
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // A row citing a define, S(1) = Σ(j = 1 to 1) j(j + 1) by
                // D1, unfolds it and pushes in the casts that leaves; a
                // header's function, its equation guarded by its domain, at
                // an argument linear arithmetic shows is in it.
                None if let Some(cite) = line.cited() => {
                    let define = self
                        .thm
                        .defines
                        .iter()
                        .any(|d| d.label == cite)
                        .then(|| self.named.get(cite).and_then(|n| n.first()))
                        .flatten();
                    match define {
                        Some(h) => format!(
                            "by first | (simp (disch := omega) only [{h}]; push_cast; norm_num; done) | parley_side"
                        ),
                        None => "by parley_side".to_string(),
                    }
                }
                // A row the page works out by real arithmetic, = 3·ln(2).
                None if line.cite == crate::corpus::Method::RealArithmetic.as_str() => {
                    "by parley_real".to_string()
                }
                None => "by norm_num".to_string(),
            };
            let term = &printed[k + 1];
            // A congruence writes its modulus after the term it reaches.
            let link = if relation.contains("{}") {
                relation.replace("{}", term)
            } else {
                format!("{relation} {term}")
            };
            // A chain of one link is that link, and its proof the step's:
            // Lean's calc would read the line after a lone link as another.
            if single {
                return Route::Built(proof);
            }
            // A proof of several lines stands under its link, deeper than
            // the link's own lines.
            let proof = proof.replace('\n', "\n      ");
            if k == 0 {
                out.push_str(&format!(" {link} := {proof}"));
            } else {
                out.push_str(&format!("\n    _ {link} := {proof}"));
            }
        }
        Route::Built(out)
    }

    /// Each sentence of the lines `refs` names, each conjunction taken apart
    /// into its parts, with the Lean term that proves each part.
    fn cited_parts(&self, refs: &[String]) -> Vec<super::algebra::Cited> {
        let mut out = Vec::new();
        for r in refs {
            for (node, name) in self.trees.get(r).into_iter().flatten() {
                conjuncts(node, name.clone(), &mut out);
            }
        }
        out
    }

    /// Where the item's set letter `name` is the domain of one of its maps,
    /// the domain of the map the citation gives for it, as Lean writes it;
    /// None where the letter is no map's domain.
    fn given_domain(
        &self,
        sentence: &Sentence,
        name: &str,
        binding: &crate::matching::Binding,
    ) -> Option<Route<String>> {
        let (map, _) = sentence.domains.iter().find(|(_, d)| d.as_str() == name)?;
        let given = binding.get(&crate::formula::symbol::Symbol::of(map));
        Some(match given {
            Some(g) if g.is_name() => match self.writer.domain_of(&g.text) {
                Some(d) => Route::Built(d),
                None => Route::no(format!("{}, whose domain no line gives", g.text)),
            },
            _ => Route::no(format!(
                "a map's domain where its map {map} is given no letter"
            )),
        })
    }

    /// Of what a reading gives, an "and" of several parts, the part that
    /// says the claim, as Lean writes both at the citation's values, by its
    /// place among the parts (`and_parts`). None where no one part does.
    fn part_saying(
        &self,
        read: &Node,
        cited: &crate::checker::record::Cited,
        claim: &Node,
    ) -> Option<usize> {
        let parts = and_parts(read);
        if parts.len() < 2 {
            return None;
        }
        let wanted = self.writer.formula(claim).built()?.text;
        let binders = self.sources.checked.grammar.binders();
        let saying: Vec<usize> = parts
            .iter()
            .enumerate()
            .filter(|(_, part)| {
                let at = crate::matching::substitute_apart_by(
                    part,
                    &cited.binding,
                    &binders,
                );
                self.writer
                    .formula(&at)
                    .built()
                    .is_some_and(|p| p.text == wanted)
            })
            .map(|(i, _)| i)
            .collect();
        match saying.as_slice() {
            [one] => Some(*one),
            _ => None,
        }
    }

    /// The name of the cited line that says an item's hypothesis at the
    /// citation's values, where its Lean text and the hypothesis's are one;
    /// None where no line does, or the hypothesis does not write.
    fn line_saying(
        &self,
        hypothesis: &Node,
        binding: &crate::matching::Binding,
        cited_lines: &[super::algebra::Cited],
        binders: &[Binder],
    ) -> Option<String> {
        // The item asks its hypothesis in its own letters' types: a number
        // given a letter of another type, or of the general one, is cast,
        // and the line, written in its own types, says something else in
        // Lean. Each number letter of the hypothesis must take its value
        // with no cast.
        let uncast = hypothesis.names().iter().all(|page| {
            let Some(Binder::Letter { ty, general, .. }) = binders
                .iter()
                .find(|b| matches!(b, Binder::Letter { page: p, .. } if p == page))
            else {
                return true;
            };
            let LetterType::Number(n) = ty else {
                return true;
            };
            let value = binding.get(&crate::formula::symbol::Symbol::of(page));
            !general
                && value.is_some_and(|v| {
                    self.writer.carrier(v).built()
                        == Some((*n).max(super::templates::Num::Int))
                        && *n != super::templates::Num::Nat
                })
        });
        if !uncast {
            return None;
        }
        let at = crate::matching::substitute_apart_by(
            hypothesis,
            binding,
            &self.sources.checked.grammar.binders(),
        );
        let wanted = self.writer.formula(&at).built()?.text;
        cited_lines
            .iter()
            .find(|c| {
                self.writer
                    .formula(&c.node)
                    .built()
                    .is_some_and(|p| p.text == wanted)
            })
            .map(|c| c.proof.clone())
    }

    /// The Lean term an item's sentence is at a citation: the theorem with
    /// each letter given its value, and each hypothesis given by the line
    /// cited that says it as Lean writes both, or else left to
    /// `parley_side`.
    fn instance(
        &self,
        sentence: &Sentence,
        binding: &crate::matching::Binding,
        claim: Option<&Node>,
        cited_lines: &[super::algebra::Cited],
    ) -> Route<String> {
        // The type an item's general letters take: the least that holds the
        // claim and every value given them, a field's at least where the
        // item divides.
        let general = match sentence.general {
            Some(g) => {
                let least = if g.field {
                    super::templates::Num::Rat
                } else {
                    super::templates::Num::Int
                };
                // At the writer's floor at least, where claims are written
                // in ℝ inside a block that lets a real number.
                let least = least.max(self.writer.floor);
                let mut at = self.worked_in.get().map_or(least, |w| w.max(least));
                let numbers: Vec<&Node> = claim
                    .into_iter()
                    .flat_map(|c| c.children.iter())
                    .filter(|c| self.writer.is_number(c))
                    .collect();
                for n in numbers {
                    match self.writer.carrier(n) {
                        Route::Built(c) => at = at.max(c),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // A term the claim puts in a hole of a fixed type, ⌊A/B⌋ in
                // ℝ's, is of that type.
                if let Some(c) = claim {
                    at = at.max(self.held_in(c));
                }
                for b in &sentence.binders {
                    let Binder::Letter {
                        page,
                        ty,
                        general: true,
                        ..
                    } = b
                    else {
                        continue;
                    };
                    let Some(value) =
                        binding.get(&crate::formula::symbol::Symbol::of(page))
                    else {
                        continue;
                    };
                    match self.given_type(value, ty) {
                        Route::Built(c) => at = at.max(c),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                Some(at)
            }
            None => None,
        };
        // The type an item's things are where they are given numbers, x ∈
        // {u, w} cited of 1 and 2: the least that holds the claim and every
        // number given them.
        let things_at = {
            // From ℕ: a set of naturals given for a set of things, S ⊆ ℕ,
            // is of naturals, and a number given raises it to ℤ at least.
            let mut at = self.worked_in.get().unwrap_or(super::templates::Num::Nat);
            let numbers = claim
                .into_iter()
                .flat_map(|c| c.children.iter())
                .chain(sentence.binders.iter().filter_map(|b| match b {
                    Binder::Letter {
                        page,
                        ty: LetterType::Member(super::expr::Members::Things),
                        ..
                    } => binding.get(&crate::formula::symbol::Symbol::of(page)),
                    _ => None,
                }))
                .filter(|n| self.writer.is_number(n));
            // A term of natural letters, b·d, is a natural; any other
            // number is an integer at least.
            for n in numbers {
                let of_letters = n.walk().iter().any(|m| m.is_name());
                if of_letters && self.writer.natural(n) {
                    continue;
                }
                if let Route::Built(c) = self.writer.carrier(n) {
                    at = at.max(c);
                }
            }
            // A set of things given a set of numbers, X := ℝ, sets the
            // things' type at least to that set's.
            for b in &sentence.binders {
                let Binder::Letter {
                    page,
                    ty: LetterType::Set(super::expr::Members::Things),
                    ..
                } = b
                else {
                    continue;
                };
                let given = binding.get(&crate::formula::symbol::Symbol::of(page));
                if let Some(super::expr::Members::Numbers(n)) =
                    given.and_then(|v| self.writer.set_members(v))
                {
                    at = at.max(n);
                }
            }
            at
        };
        // Whether the citation gives the item's things numbers: a set of
        // things given a set of numbers, X := {2n : n ∈ ℤ}.
        let things_are_numbers = sentence.binders.iter().any(|b| match b {
            Binder::Letter {
                page,
                ty: LetterType::Set(super::expr::Members::Things),
                ..
            } => matches!(
                binding
                    .get(&crate::formula::symbol::Symbol::of(page))
                    .and_then(|v| self.writer.set_members(v)),
                Some(super::expr::Members::Numbers(_))
            ),
            _ => false,
        });
        let mut args = Vec::new();
        // Each ℕ letter given an integer's `toNat`: the letter, and the
        // integer.
        let mut to_nat: Vec<(String, String)> = Vec::new();
        for b in &sentence.binders {
            match b {
                Binder::Letter {
                    name,
                    page,
                    ty,
                    general: in_general,
                } => {
                    let Some(value) =
                        binding.get(&crate::formula::symbol::Symbol::of(page))
                    else {
                        // A set the citation gives no value: a map's domain,
                        // the X of `f : X → W`, is the domain of what f is
                        // given, within which its images are taken; the Z a
                        // map goes into is all of its type, which every map
                        // goes into; anything else is left to Lean.
                        let fill =
                            match (ty, self.given_domain(sentence, name, binding)) {
                                (LetterType::Set(_), Some(Route::Built(d))) => d,
                                (LetterType::Set(_), Some(Route::Declined(d))) => {
                                    return Route::Declined(d)
                                }
                                (LetterType::Set(_), None) => "Set.univ".to_string(),
                                // A function of a recursion the file lets, F of
                                // D1, is the citing theorem's F, which the same
                                // define lets.
                                (LetterType::Function { .. }, _)
                                    if self.writer.letters.get(page.as_str())
                                        == Some(ty) =>
                                {
                                    super::names::letter(page)
                                }
                                _ => "_".to_string(),
                            };
                        args.push(format!("({name} := {fill})"));
                        continue;
                    };
                    let printed = match (ty, general.filter(|_| *in_general)) {
                        (LetterType::Number(_), Some(at)) => {
                            self.writer.number_fixed(value, at)
                        }
                        // A letter of ℕ given an integer the page shows is
                        // not negative, M − 1, takes its `toNat`, and the
                        // instance is rewritten back below.
                        (LetterType::Number(super::templates::Num::Nat), None) => {
                            match self
                                .writer
                                .number_fixed(value, super::templates::Num::Nat)
                            {
                                Route::Built(p) => Route::Built(p),
                                // A real a line says is in ℕ₀, |A| ∈ ℕ₀: the
                                // natural number that line gives.
                                Route::Declined(d) => match self
                                    .said_integer(value, super::templates::Num::Nat)
                                {
                                    Some(line) => {
                                        let printed = super::expr::Printed::atom(
                                            format!("(Classical.choose {line})"),
                                        );
                                        self.said_used.borrow_mut().push(SaidUsed {
                                            line,
                                            term: self.writer.grammar.print(value),
                                        });
                                        Route::Built(printed)
                                    }
                                    // An integer the page shows is not
                                    // negative, M − 1: its `toNat`.
                                    None => match self
                                        .writer
                                        .number_fixed(value, super::templates::Num::Int)
                                    {
                                        Route::Built(p) => {
                                            let int = p.at(super::expr::MAX);
                                            to_nat.push((name.clone(), int.clone()));
                                            Route::Built(super::expr::Printed::atom(
                                                format!("{int}.toNat"),
                                            ))
                                        }
                                        Route::Declined(_) => Route::Declined(d),
                                    },
                                },
                            }
                        }
                        // A value of a wider type that a line says is in the
                        // letter's, A + B ∈ ℚ of reals: the number that line
                        // gives.
                        (LetterType::Number(n), None) => {
                            match self.writer.number_fixed(value, *n) {
                                Route::Declined(d) => {
                                    match self.said_integer(value, *n) {
                                        Some(line) => {
                                            let printed = super::expr::Printed::atom(
                                                format!("(Classical.choose {line})"),
                                            );
                                            self.said_used.borrow_mut().push(
                                                SaidUsed {
                                                    line,
                                                    term: self
                                                        .writer
                                                        .grammar
                                                        .print(value),
                                                },
                                            );
                                            Route::Built(printed)
                                        }
                                        None => Route::Declined(d),
                                    }
                                }
                                built => built,
                            }
                        }
                        // A property given by what it says of t, `fun t : α
                        // => …`, t a member of what the property is of.
                        (LetterType::Property(members), _) => {
                            // Of things the citation gives numbers, the
                            // numbers at the type the things are taken at.
                            let (of, lean) = match (members, things_are_numbers) {
                                (super::expr::Members::Things, true) => (
                                    LetterType::Number(things_at),
                                    things_at.lean().to_string(),
                                ),
                                _ => (members.letter(), members.lean()),
                            };
                            match (&*value.notation_name(), value.children.as_slice()) {
                                ("property-of", [body]) => {
                                    let mut letters = self.writer.letters.clone();
                                    letters.insert(value.text.to_string(), of);
                                    let inner = self.writer.with_letters(letters);
                                    inner.formula(body).map(|b| {
                                        super::expr::Printed::atom(format!(
                                            "(fun {} : {} => {})",
                                            super::names::letter(&value.text),
                                            lean,
                                            b.text
                                        ))
                                    })
                                }
                                _ if value.is_name() => {
                                    Route::Built(super::expr::Printed::atom(
                                        super::names::letter(&value.text),
                                    ))
                                }
                                _ => Route::no(
                                    "a property given by other than what it says",
                                ),
                            }
                        }
                        // A function given for a function letter, of the
                        // same types.
                        // A function given by its values, k ↦ t, a sum's
                        // term: `fun k : ℤ => t`, t in what it gives.
                        (LetterType::Function { from, to }, given)
                            if &*value.notation_name() == "property-of" =>
                        {
                            // A function into the general type gives the
                            // type chosen for it.
                            let gives = given.unwrap_or(*to);
                            match value.children.as_slice() {
                                [body] => {
                                    let mut letters = self.writer.letters.clone();
                                    letters.insert(
                                        value.text.to_string(),
                                        LetterType::Number(*from),
                                    );
                                    let inner = self.writer.with_letters(letters);
                                    inner.number_fixed(body, gives).map(|b| {
                                        super::expr::Printed::atom(format!(
                                            "(fun {} : {} => {})",
                                            super::names::letter(&value.text),
                                            from.lean(),
                                            b.text
                                        ))
                                    })
                                }
                                _ => Route::no(
                                    "a function by its values of other than one body",
                                ),
                            }
                        }
                        (LetterType::Function { from, to }, given) => {
                            match self.writer.function_type(value) {
                                Route::Built(t)
                                    if t == (*from, given.unwrap_or(*to)) =>
                                {
                                    Route::Built(self.writer.function_printed(value))
                                }
                                // A function that takes the letter's numbers
                                // and gives numbers within its type, t of ℤ
                                // into ℤ for f of ℕ into ℝ: t between casts.
                                Route::Built((takes, gives))
                                    if *from <= takes
                                        && gives <= given.unwrap_or(*to) =>
                                {
                                    let wanted = given.unwrap_or(*to);
                                    Route::Built(super::expr::Printed::atom(format!(
                                        "(fun x : {} => (({} (x : {}) : {}) : {}))",
                                        from.lean(),
                                        self.writer.function_printed(value).text,
                                        takes.lean(),
                                        gives.lean(),
                                        wanted.lean()
                                    )))
                                }
                                Route::Built(_) => Route::no(
                                    "a function given for a letter of other types",
                                ),
                                Route::Declined(d) => Route::Declined(d),
                            }
                        }
                        (LetterType::Statement, _) => self.writer.formula(value),
                        // A thing given a number: the number, at the type
                        // the things are taken at here.
                        (LetterType::Member(super::expr::Members::Things), _)
                            if self.writer.is_number(value) =>
                        {
                            self.writer.number_fixed(value, things_at)
                        }
                        // A set of things given a set of numbers: the set at
                        // the type the things are taken at here.
                        (LetterType::Set(super::expr::Members::Things), _)
                            if matches!(
                                self.writer.set_members(value),
                                Some(super::expr::Members::Numbers(_))
                            ) =>
                        {
                            self.writer.numbers_at(value, things_at)
                        }
                        // A map of things given by its values on numbers,
                        // n ↦ 2n: `fun n => 2 * n`, at the type the things
                        // are taken at here.
                        (LetterType::Map { .. }, _)
                            if &*value.notation_name() == "property-of" =>
                        {
                            match value.children.as_slice() {
                                [body] => {
                                    let mut letters = self.writer.letters.clone();
                                    letters.insert(
                                        value.text.to_string(),
                                        LetterType::Number(things_at),
                                    );
                                    let inner = self.writer.with_letters(letters);
                                    inner.number_fixed(body, things_at).map(|b| {
                                        super::expr::Printed::atom(format!(
                                            "(fun {} : {} => {})",
                                            super::names::letter(&value.text),
                                            things_at.lean(),
                                            b.text
                                        ))
                                    })
                                }
                                _ => Route::no(
                                    "a map by its values of other than one body",
                                ),
                            }
                        }
                        // A set, a member or a map given for one: the term
                        // as the writer writes a set's.
                        (
                            LetterType::Set(_)
                            | LetterType::Member(_)
                            | LetterType::Map { .. },
                            _,
                        ) => self.writer.set_term(value),
                        // A group given for a group, or a subgroup for a
                        // subgroup: its Lean name, the type or the
                        // `Subgroup G` itself, not the set it stands for.
                        (LetterType::Group | LetterType::Subgroup(_), _) => {
                            Route::Built(super::expr::Printed::atom(
                                super::names::letter(&value.text),
                            ))
                        }
                        // The identity is no binder: `1` of the group.
                        (LetterType::Identity(_), _) => {
                            Route::no("an identity given as a letter of an item")
                        }
                    };
                    match printed {
                        Route::Built(p) => args.push(format!("({name} := {})", p.text)),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // A fact asked of a letter given an integer's `toNat` is
                // asked of the integer: the `toNat` is rewritten back first,
                // as `simp` on a cast of a `toNat` may recurse past Lean's
                // limit, which no `first` recovers from.
                Binder::Fact { .. } if !to_nat.is_empty() => {
                    let rewrites: Vec<String> = to_nat
                        .iter()
                        .map(|(_, int)| {
                            format!("Int.toNat_of_nonneg (show (0 : ℤ) ≤ {int} by parley_side)")
                        })
                        .collect();
                    args.push(format!(
                        "(by (try rw [{}]); parley_side)",
                        rewrites.join(", ")
                    ));
                }
                // A hypothesis a cited line says, as Lean writes both: the
                // line by its name.
                Binder::Fact {
                    line: Some(line), ..
                } => match self.line_saying(
                    line,
                    binding,
                    cited_lines,
                    &sentence.binders,
                ) {
                    Some(name) => args.push(name),
                    None => args.push("(by parley_side)".to_string()),
                },
                Binder::Fact { .. } => args.push("(by parley_side)".to_string()),
            }
        }
        let mut head = if args.is_empty() {
            sentence.decl.clone()
        } else {
            format!("({} {})", sentence.decl, args.join(" "))
        };
        // Each `toNat` given a letter cast back to the integer it is, where
        // the statement casts the letter up. One said only of naturals,
        // nat0-nonzero's `0 < m`, has nothing to rewrite, and the claim is
        // closed from it by `omega`, which reads `toNat` (`parley_side`).
        // The statement is the writer's own Lean text, so the cast is looked
        // for as the writer prints it.
        for (letter, int) in &to_nat {
            if !sentence.prop.contains(&format!("({letter} : ")) {
                continue;
            }
            head = format!(
                "(Int.toNat_of_nonneg (show (0 : ℤ) ≤ {int} by parley_side) ▸ {head})"
            );
        }
        Route::Built(format!("{head}{}", sentence.part))
    }

    /// The type a value given a general letter is in: a number's own, a
    /// function by its values k ↦ t the type of t with k of the type the
    /// function takes, and a function letter's what it gives.
    fn given_type(
        &self,
        value: &Node,
        ty: &LetterType,
    ) -> Route<super::templates::Num> {
        match (ty, value.children.as_slice()) {
            (LetterType::Function { from, .. }, [body])
                if &*value.notation_name() == "property-of" =>
            {
                let mut letters = self.writer.letters.clone();
                letters.insert(value.text.to_string(), LetterType::Number(*from));
                self.writer.with_letters(letters).carrier(body)
            }
            (LetterType::Function { .. }, _) => {
                self.writer.function_type(value).map(|(_, to)| to)
            }
            _ => self.writer.carrier(value),
        }
    }

    /// The item a reason cites, in Lean.
    fn cited_item<'r>(&self, reason: Reason<'r>) -> Route<(&Item, &'r Cited)>
    where
        'a: 'r,
    {
        let Some(cited) = reason.cited else {
            return Route::no("a citation the checker did not read");
        };
        match self.sources.items.get(&cited.item) {
            Some(item) => Route::Built((item, cited)),
            None => Route::no(format!("{} has no Lean form", cited.item)),
        }
    }

    /// Sentence `k` of a claim, by the item its reason cites.
    fn citation(&self, reason: Reason, k: usize, node: &Node) -> Route<String> {
        let (item, cited) = match self.cited_item(reason) {
            Route::Built(x) => x,
            Route::Declined(d) => return Route::Declined(d),
        };
        let Some(concluded) = cited.concluded.get(k) else {
            return Route::no("a claim sentence no conclusion of the item gives");
        };
        let Some(sentence) = item.sentences.get(concluded.sentence) else {
            return Route::no("a conclusion the item does not have in Lean");
        };
        let lines = self.cited_parts(&reason.just.refs);
        let inst = match self.instance(sentence, &cited.binding, Some(node), &lines) {
            Route::Built(t) => t,
            Route::Declined(d) => return Route::Declined(d),
        };
        let iff = sentence.says.notation() == BICONDITIONAL;
        let implication = matches!(sentence.says.notation(), CONDITIONAL | IMPLICATION);
        let term = match concluded.way {
            Way::AsWritten => inst,
            Way::Forward if iff => format!("({inst}).mp (by parley_side)"),
            Way::Forward if implication => format!("{inst} (by parley_side)"),
            Way::Forward => {
                return Route::no("a forward reading of a sentence that is no ↔ or if")
            }
            Way::Backward => {
                let witness = match self.witnesses(sentence, cited, &reason.just.refs) {
                    Route::Built(w) => w,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // What the definition's left side says, read in the claim's
                // own words where the two say one thing otherwise: an item
                // over any ring says "∈ ℕ₀" `∃ m : ℕ, ↑m = x`, a claim of
                // integers `0 ≤ x` (`parley_side`).
                // A claim a requires line above already states, "0 ≤ b − c"
                // for "b − c ∈ ℕ₀", is that line: tried first, as it is
                // quick and the others may search long.
                return Route::Built(format!(
                    "by first | (assumption; done) | exact ({inst}).mpr {witness} | (have h := ({inst}).mpr {witness}; parley_side)"
                ));
            }
        };
        // Several sentences of the claim taken by one reading are its "and"
        // set apart, each the projection of its place among them.
        let same: Vec<usize> = cited
            .concluded
            .iter()
            .enumerate()
            .filter(|(_, c)| **c == *concluded)
            .map(|(i, _)| i)
            .collect();
        // A claim that is itself the "and", read as its parts, is the whole.
        let whole = matches!(
            node.notation(),
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION
        );
        // What the reading gives: a definition's right side, a theorem's
        // sentence; its "and" is taken apart as its tree nests it.
        let read = match (iff, sentence.says.children.as_slice()) {
            (true, [_, right]) => right,
            _ => &sentence.says,
        };
        let term = match same.iter().position(|&i| i == k) {
            Some(at) if same.len() > 1 && !whole => {
                match leaf_path(read, at) {
                    Some(path) => format!("({term}){path}"),
                    None => return Route::no(
                        "a reading whose \"and\" has fewer parts than its sentences",
                    ),
                }
            }
            // One sentence of the claim that is one part of the "and" the
            // reading gives, "for all d …" of "p > 1 and for all d …": that
            // part, found by its Lean text at the citation's values.
            _ if !whole && same.len() == 1 && concluded.way == Way::Forward && iff => {
                match self
                    .part_saying(read, cited, node)
                    .and_then(|at| leaf_path(read, at))
                {
                    Some(path) => format!("({term}){path}"),
                    None => term,
                }
            }
            _ => term,
        };
        // A define the step cites is written out first, as for algebra.
        let defines = self.cited_defines(&reason.just.refs);
        // An item that says a natural power of an integer is one gives the
        // claim nothing to read where the claim's exponent is an integer
        // the page shows not negative, 2^(n − 1); the writer gives the
        // witness.
        let closed = match self.writer.integer_power_witness(node) {
            Some(witness) => format!(
                "by first | exact {witness} | exact ({})",
                close(node, &term)
            ),
            None => close(node, &term),
        };
        Route::Built(with_haves(&written_out(&defines), &closed))
    }

    /// The proof of the right side of a definition a step folds: its
    /// witnesses, where it is a "there is", and its body left to
    /// `parley_side`.
    fn witnesses(
        &self,
        sentence: &Sentence,
        cited: &crate::checker::record::Cited,
        refs: &[String],
    ) -> Route<String> {
        let [_, right] = sentence.says.children.as_slice() else {
            return Route::no("a definition of other than two sides");
        };
        // A witness that is a letter bound by the line cited, the k of its
        // "there is k", is no value in scope: the line says the right side
        // whole.
        let bound_here: std::collections::BTreeSet<String> = self
            .cited_parts(refs)
            .iter()
            .filter(|c| c.node.notation() == crate::notations::THERE_IS)
            .filter_map(|c| c.node.children.first())
            .filter(|l| l.is_name())
            .map(|l| l.text.to_string())
            .collect();
        let bound_by_line = cited
            .bound
            .values()
            .any(|v| v.is_name() && bound_here.contains(v.text.as_str()));
        if bound_by_line {
            return Route::Built("(by parley_side)".to_string());
        }
        let mut parts = Vec::new();
        // What a line said of a witness the page wrote as a fraction that
        // is an integer, put in scope where the witness's facts are proved.
        let mut known = Vec::new();
        let mut body = right;
        while body.notation() == crate::notations::THERE_IS {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let Some(value) = cited.bound.get(&letter.text) else {
                return Route::no(format!("no witness for {}", letter.text));
            };
            let system = super::expr::system_of(set);
            let Some(s) = system else {
                // A witness in a set: the value, a number at its own type
                // or a member as the writer writes one, and that it is in
                // the set.
                let term = match self.writer.carrier(value) {
                    Route::Built(at) if self.writer.is_number(value) => {
                        self.writer.number_fixed(value, at)
                    }
                    _ => self.writer.set_term(value),
                };
                match term {
                    Route::Built(p) => parts.push(p.text),
                    Route::Declined(d) => return Route::Declined(d),
                }
                parts.push(format!("by {}parley_side", known.concat()));
                body = inner;
                continue;
            };
            let ty = super::expr::letter_type(s);
            match self.witness(value, ty) {
                Route::Built(w) => {
                    parts.push(w.term);
                    known.extend(w.known);
                }
                Route::Declined(d) => return Route::Declined(d),
            }
            if system == Some(super::expr::System::Positive) {
                parts.push(format!("by {}parley_side", known.concat()));
            }
            body = inner;
        }
        if parts.is_empty() {
            return Route::Built("(by parley_side)".to_string());
        }
        parts.push(format!("by {}parley_side", known.concat()));
        Route::Built(format!("⟨{}⟩", parts.join(", ")))
    }

    /// A witness of a "there is" over `ty`: the value as Lean computes it
    /// there, or, for a value the page writes as a fraction that a line
    /// says is an integer, the integer that line gives, with what it says
    /// of it put in scope where the witness's facts are proved.
    fn witness(&self, value: &Node, ty: super::templates::Num) -> Route<Witness> {
        match self.writer.number_fixed(value, ty) {
            Route::Built(p) => Route::Built(Witness {
                term: p.text,
                known: None,
            }),
            Route::Declined(d) => match self.said_integer(value, ty) {
                Some(line) => Route::Built(Witness {
                    term: format!("Classical.choose {line}"),
                    known: Some(format!("have := Classical.choose_spec {line}; ")),
                }),
                // An integer the lines show is not negative, b·m of a
                // natural b and a positive integer m, given for a natural:
                // its `toNat`, with that it is the integer known.
                None if ty == super::templates::Num::Nat => {
                    match self.writer.number_fixed(value, super::templates::Num::Int) {
                        Route::Built(p) => {
                            let int = p.at(super::expr::MAX);
                            Route::Built(Witness {
                                term: format!("{int}.toNat"),
                                known: Some(format!(
                                    "(try simp only [parley_cast_toNat (show (0 : ℤ) ≤ {int} by parley_side)]); (try push_cast); "
                                )),
                            })
                        }
                        Route::Declined(_) => Route::Declined(d),
                    }
                }
                None => Route::Declined(d),
            },
        }
    }

    /// The Lean name of a line in scope saying a term is an integer, `(N −
    /// 1)/2 ∈ ℤ`, where `value` is that term as Lean writes it; None where
    /// no line says so. Lean states that line as `∃ m : ℤ, (m : ℚ) = …`, so
    /// the integer is the witness it gives.
    fn said_integer(&self, value: &Node, ty: super::templates::Num) -> Option<String> {
        // Lean states each as `∃ m : T, ↑m = x` of a term wider than T: ℤ,
        // ℚ, and ℕ₀ of a term wider than ℤ, as ℕ, an integer's being `0 ≤
        // x`. ℕ adds that m is above 0, and is not one of them.
        let at = self.writer.carrier(value).built()?;
        let system = match ty {
            super::templates::Num::Int | super::templates::Num::Rat => {
                super::expr::System::Type(ty)
            }
            super::templates::Num::Nat if at > super::templates::Num::Int => {
                super::expr::System::NonNegative
            }
            _ => return None,
        };
        let wanted = self.writer.number(value, at).built()?.text;
        // The latest such line: an earlier one may stand in a block the
        // step is not in.
        self.trees
            .values()
            .rev()
            .flatten()
            .find_map(|(node, name)| {
                let [term, set] = node.children.as_slice() else {
                    return None;
                };
                let integer = node.notation() == crate::notations::MEMBERSHIP
                    && super::expr::system_of(set) == Some(system);
                let same = self.writer.number(term, at).built().map(|p| p.text)
                    == Some(wanted.clone());
                (integer && same).then(|| name.clone())
            })
    }

    /// `obtain`: the witnesses of a "there is" an item gives, named as the
    /// claim names them.
    /// The "there is" an `obtain` takes its witnesses from: a line of the
    /// page it names, or a sentence of the item it cites.
    fn obtained_from(&self, i: usize) -> Route<Obtained> {
        let step = &self.thm.steps[i];
        if self.rec.cited[i].is_none() && step.just.obtained_from.is_none() {
            // The sentence, or the part of one, of the lines named that
            // says "there is".
            // A "for all" line is read at the block's letter, as the checker
            // reads it.
            let mut names = std::collections::BTreeSet::new();
            for s in step.claim.sentences() {
                if let Some(n) = self.rec.page.get(&s) {
                    names.extend(n.names());
                }
            }
            names.retain(|n| !step.just.obtained.contains(n));
            return match self
                .cited_parts(&step.just.from)
                .into_iter()
                .map(|c| self.read_at_letters(&c, &names).unwrap_or(c))
                .find(|c| {
                    c.node.notation() == crate::notations::THERE_IS
                        || &*c.node.notation_name() == "there-is-some"
                }) {
                Some(c) => Route::Built(Obtained {
                    term: c.proof,
                    says: c.node,
                }),
                None => Route::no("an obtain from no line that says \"there is\""),
            };
        }
        let reason = Reason {
            just: &step.just,
            cited: self.rec.cited[i].as_ref(),
        };
        let (item, cited) = match self.cited_item(reason) {
            Route::Built(x) => x,
            Route::Declined(d) => return Route::Declined(d),
        };
        let Some(at) = cited.obtained else {
            return Route::no("an obtain that takes no sentence of its item");
        };
        let before: usize = match self.sources.checked.library.groups.get(&cited.item) {
            Some(Some(groups)) => {
                groups[..cited.group].iter().map(|g| g.gives.len()).sum()
            }
            _ => 0,
        };
        let Some(sentence) = item.sentences.get(before + at) else {
            return Route::no("an obtain of a sentence the item does not have in Lean");
        };
        let mut binding = cited.binding.clone();
        for (k, v) in &cited.written {
            binding.entry(*k).or_insert_with(|| v.clone());
        }
        let lines = self.cited_parts(&step.just.from);
        let inst = match self.instance(sentence, &binding, None, &lines) {
            Route::Built(t) => t,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A definition's right side is the "there is"; a theorem's sentence
        // is one.
        let iff = sentence.says.notation() == BICONDITIONAL;
        let says = match (iff, sentence.says.children.as_slice()) {
            (true, [_, right]) => right.clone(),
            _ => sentence.says.clone(),
        };
        // At the citation's values, a property given applied where the
        // sentence applies it: P(d) of set-builder is "there are m, n with
        // d = a·m + b·n".
        let says =
            read_at_values(&says, &binding, &self.sources.checked.grammar.binders());
        Route::Built(Obtained {
            term: if iff {
                format!("({inst}).mp (by parley_side)")
            } else {
                inst
            },
            says,
        })
    }

    fn obtain(&mut self, i: usize, depth: usize) -> Route<()> {
        self.said_used.borrow_mut().clear();
        let source = match self.obtained_from(i) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        let used = std::mem::take(&mut *self.said_used.borrow_mut());
        let step = &self.thm.steps[i];
        self.introduce(step);
        let claim = match self.claim(step) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let names = Self::names_of(step, claim.len());
        if let Some(n) = step.number.number() {
            self.named.insert(n.to_string(), names.clone());
            let said = claim
                .iter()
                .zip(&names)
                .map(|((node, _), name)| (node.clone(), name.clone()))
                .collect();
            self.trees.insert(n.to_string(), said);
        }
        // Lean nests a "there is" as the page does: each letter, then the
        // fact its range gives where Lean's type does not, then what is said
        // of them all. The claim's sentence about each letter's range is
        // that fact; its other sentences are what is said.
        let mut guards: IndexMap<String, String> = IndexMap::new();
        let mut body: Vec<String> = Vec::new();
        for ((node, _), name) in claim.iter().zip(&names) {
            // A letter's fact of being in a set, x ∈ A, as of a range.
            let in_set = match node.children.as_slice() {
                [x, set]
                    if node.notation() == crate::notations::MEMBERSHIP
                        && x.is_name()
                        && self.writer.members_of(set).is_some() =>
                {
                    Some(x.text.to_string())
                }
                _ => None,
            };
            let letter = introduces(node)
                .map(|(l, _)| l)
                .or_else(|| super::statement::range_letter(node))
                .or(in_set)
                .or_else(|| super::statement::introduces_polynomial(node));
            match letter.filter(|l| step.just.obtained.contains(l)) {
                Some(l) => {
                    guards.insert(l, name.clone());
                }
                None => body.push(name.clone()),
            }
        }
        // there is a ∈ X with nothing said, `∃ a ∈ X, True`: the letter, the
        // fact that it is in X, and nothing.
        if let ("there-is-some", [obtained]) =
            (&*source.says.notation_name(), step.just.obtained.as_slice())
        {
            let guard = guards
                .get(obtained)
                .cloned()
                .unwrap_or_else(|| "_".to_string());
            self.push(
                format!(
                    "{}obtain ⟨{}, {guard}, _⟩ := {}",
                    pad(depth),
                    super::names::letter(obtained),
                    source.term
                ),
                step.line,
                Self::step_spot(step),
            );
            return Route::Built(());
        }
        let mut pattern = Vec::new();
        let mut said = &source.says;
        // A "there is" the sentence says after an "and", u ∈ X and (there
        // are m, n with …): what comes before it, unnamed, and then it.
        while let (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [_, right],
        ) = (said.notation(), said.children.as_slice())
        {
            if right.notation() != crate::notations::THERE_IS {
                break;
            }
            pattern.push("_".to_string());
            said = right;
        }
        for obtained in &step.just.obtained {
            let [_, set, inner] = said.children.as_slice() else {
                return Route::no(
                    "an obtain of more letters than its \"there is\" binds",
                );
            };
            if said.notation() != crate::notations::THERE_IS {
                return Route::no(
                    "an obtain of more letters than its \"there is\" binds",
                );
            }
            pattern.push(super::names::letter(obtained));
            // Lean writes "there is s ∈ S" with the membership beside s
            // for every S but a number system its type gives, ℤ, ℚ, ℝ or
            // ℂ, and ℕ₀; the page's ℕ adds that s is above 0.
            let guarded = set.notation() == crate::notations::INTEGER_RANGE
                || super::expr::system_of(set) == Some(super::expr::System::Positive)
                || super::expr::system_of(set).is_none();
            if guarded {
                pattern.push(
                    guards
                        .get(obtained)
                        .cloned()
                        .unwrap_or_else(|| "_".to_string()),
                );
            }
            said = inner;
        }
        // What is said of the letters, taken apart as Lean nests its "and":
        // ((d > 1 ∧ d ∣ p) ∧ d ∣ q) is ⟨⟨a, b⟩, c⟩.
        if !body.is_empty() {
            let mut names = body.into_iter();
            let shaped = shaped_pattern(said, &mut names);
            if names.next().is_some() {
                return Route::no(
                    "an obtain whose sentences are not the parts of its \"there is\"",
                );
            }
            pattern.push(shaped);
        }
        let p = pad(depth);
        self.push(
            format!("{p}obtain ⟨{}⟩ := {}", pattern.join(", "), source.term),
            step.line,
            Self::step_spot(step),
        );
        // An item given a line's number, x := the rational of `√2 ∈ ℚ`,
        // gives its facts of that number; a sentence the page says of the
        // line's term, √2 = p/q, is that fact with the goal put in terms of
        // the number.
        for ((node, prop), name) in claim.iter().zip(&names) {
            let specs = self.specs_in(node, &used);
            if specs.is_empty() {
                continue;
            }
            self.push(
                format!(
                    "{p}have {name} : {} := by rw [{specs}]; exact_mod_cast {name}",
                    prop.text
                ),
                step.line,
                Self::step_spot(step),
            );
        }
        Route::Built(())
    }

    /// The rewrites that put a claim in terms of the numbers lines give,
    /// `← Classical.choose_spec hS` for each line used whose term the claim
    /// has, joined for `rw`; empty where it has none.
    fn specs_in(&self, claim: &Node, used: &[SaidUsed]) -> String {
        let parts: Vec<String> = claim
            .walk()
            .iter()
            .map(|n| self.writer.grammar.print(n))
            .collect();
        let mut specs: Vec<String> = Vec::new();
        for u in used {
            let spec = format!("← Classical.choose_spec {}", u.line);
            if parts.contains(&u.term) && !specs.contains(&spec) {
                specs.push(spec);
            }
        }
        specs.join(", ")
    }

    /// A step that owns a block: its claim proved by the block's steps,
    /// opened by its lines.
    fn block(
        &mut self,
        i: usize,
        method: Method,
        claim: &[(Node, Printed)],
        names: &[String],
        depth: usize,
    ) -> Route<()> {
        let step = &self.thm.steps[i];
        let spot = Self::step_spot(step);
        // A claim Lean's types already make true needs no proof, and what
        // the block shows inside it is cited nowhere outside it.
        if claim.is_empty() {
            self.push(
                format!("{}-- what this block shows, Lean's types give", pad(depth)),
                step.line,
                spot,
            );
            return Route::Built(());
        }
        // A claim of several sentences is proved as their "and", and taken
        // apart after into each sentence's name.
        let Some((claimed, _)) = claim.first() else {
            return Route::no("a block with no claim");
        };
        if claim.len() > 1 && method == Method::Induction {
            return Route::no("an induction whose claim is several sentences");
        }
        let (whole, prop) = match claim {
            [(_, prop)] => (names[0].clone(), prop.text.clone()),
            _ => (
                format!("{}_all", names[0]),
                claim
                    .iter()
                    .map(|(_, p)| p.at(36))
                    .collect::<Vec<_>>()
                    .join(" ∧ "),
            ),
        };
        let Some(block_at) = self.rec.blocks.iter().position(|b| b.owner == i) else {
            return Route::no("a block the checker did not record");
        };
        let block = self.rec.blocks[block_at].clone();
        let p = pad(depth);
        let inner = pad(depth + 1);
        self.push(
            format!("{p}have {whole} : {prop} := by"),
            step.line,
            spot.clone(),
        );
        let kept = self.writer.letters.clone();
        let floor = self.writer.floor;
        // The lines in scope as the block opens: a line one case or
        // direction says is no line of the next.
        let kept_lines = self.trees.clone();
        let parts: Vec<Option<usize>> = if step.parts.is_empty() {
            vec![None]
        } else {
            (0..step.parts.len()).map(Some).collect()
        };
        match method {
            Method::Proof | Method::Contradiction => {
                if let Route::Declined(d) = self.open(step, None, depth + 1) {
                    return Route::Declined(d);
                }
                let children: Vec<usize> = block.children.clone();
                if let Route::Declined(d) = self.steps(&children, depth + 1) {
                    return Route::Declined(d);
                }
                // A block may end on a line shown impossible, which closes
                // it; what is left, if anything, its last line gives.
                let close = match method {
                    Method::Proof if claim.len() == 1 => {
                        self.closing(children.last().copied(), claimed)
                    }
                    _ => "parley_side".to_string(),
                };
                self.push(format!("{inner}all_goals {close}"), step.line, spot.clone());
            }
            Method::Cases => {
                // The sentence, or the part of one, of the lines named that
                // says "or".
                // A "for all" line is read at the letters the cases assume,
                // as the checker reads it.
                let mut letters = std::collections::BTreeSet::new();
                for o in &step.openers {
                    for s in o.body(&self.thm.path).sentences() {
                        if let Some(n) = self.rec.page.get(&s) {
                            letters.extend(n.names());
                        }
                    }
                }
                let Some(said) = self
                    .cited_parts(&step.just.from)
                    .into_iter()
                    .map(|c| self.read_at_letters(&c, &letters).unwrap_or(c))
                    .find(|c| c.node.notation() == crate::notations::DISJUNCTION)
                else {
                    return Route::no("cases from no line that says \"or\"");
                };
                let source = said.proof.clone();
                let labels: Vec<String> = parts
                    .iter()
                    .map(|part| {
                        step.openers
                            .iter()
                            .find(|o| o.part == *part)
                            .map(|o| line_name(&o.label))
                            .unwrap_or_else(|| "_".to_string())
                    })
                    .collect();
                // The pattern follows the "or" as the page groups it: a ∨ b
                // ∨ c read from the left is (a ∨ b) ∨ c.
                // Cases that group the "or" otherwise, a ∨ b as one case of
                // a ∨ b ∨ c ∨ d, take it restated as the cases say it, each
                // case a part of an "or" read from the right.
                let mut names = labels.iter();
                let pattern = or_pattern(&said.node, &mut names);
                let line = if disjuncts(&said.node) == labels.len() {
                    format!("{inner}rcases {source} with {pattern}")
                } else {
                    let mut says = Vec::new();
                    for part in &parts {
                        let node =
                            step.openers.iter().find(|o| o.part == *part).and_then(
                                |o| {
                                    o.body(&self.thm.path)
                                        .sentences()
                                        .first()
                                        .and_then(|s| self.rec.page.get(s))
                                        .cloned()
                                },
                            );
                        let Some(node) = node else {
                            return Route::no("a case that assumes nothing");
                        };
                        match self.writer.formula(&node) {
                            Route::Built(p) => says.push(format!("({})", p.text)),
                            Route::Declined(d) => return Route::Declined(d),
                        }
                    }
                    format!(
                        "{inner}rcases (show {} by have := {source}; tauto) with {}",
                        says.join(" ∨ "),
                        labels.join(" | ")
                    )
                };
                self.push(line, step.line, spot.clone());
                for (part, label) in parts.iter().zip(&labels) {
                    // Each case starts from the letters as the block found
                    // them: one a case lifts to ℕ, m ∈ ℕ₀ where it assumes
                    // m ≥ 0, is no natural in the next.
                    self.writer.letters = kept.clone();
                    self.writer.floor = floor;
                    self.trees = kept_lines.clone();
                    self.named.insert(label.clone(), vec![label.clone()]);
                    // What the case assumes, for a step that cites it.
                    if let Some(o) = step.openers.iter().find(|o| o.part == *part) {
                        let nodes: Vec<Node> = o
                            .body(&self.thm.path)
                            .sentences()
                            .iter()
                            .filter_map(|s| self.rec.page.get(s).cloned())
                            .collect();
                        if let [node] = nodes.as_slice() {
                            self.trees.insert(
                                o.label.clone(),
                                vec![(node.clone(), label.clone())],
                            );
                        }
                    }
                    let children: Vec<usize> = block
                        .children
                        .iter()
                        .copied()
                        .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                        .collect();
                    self.push(format!("{inner}· skip"), step.line, spot.clone());
                    if let Route::Declined(d) = self.steps(&children, depth + 2) {
                        return Route::Declined(d);
                    }
                    self.push(
                        format!("{inner}  all_goals parley_side"),
                        step.line,
                        spot.clone(),
                    );
                }
            }
            Method::Induction => {
                if let Route::Declined(d) =
                    self.induction(step, &block, claimed, &parts, depth + 1)
                {
                    return Route::Declined(d);
                }
            }
            Method::BothDirections => {
                self.push(format!("{inner}constructor"), step.line, spot.clone());
                for part in &parts {
                    self.trees = kept_lines.clone();
                    self.push(format!("{inner}· skip"), step.line, spot.clone());
                    if let Route::Declined(d) = self.open(step, *part, depth + 2) {
                        return Route::Declined(d);
                    }
                    let children: Vec<usize> = block
                        .children
                        .iter()
                        .copied()
                        .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                        .collect();
                    if let Route::Declined(d) = self.steps(&children, depth + 2) {
                        return Route::Declined(d);
                    }
                    self.push(
                        format!("{inner}  all_goals parley_side"),
                        step.line,
                        spot.clone(),
                    );
                }
            }
            other => {
                return Route::no(format!(
                    "the method {} is not written in Lean yet",
                    other.as_str()
                ))
            }
        }
        self.writer.letters = kept;
        self.writer.floor = floor;
        if claim.len() > 1 {
            self.push(
                format!("{p}obtain ⟨{}⟩ := {whole}", names.join(", ")),
                step.line,
                spot,
            );
        }
        Route::Built(())
    }

    /// `induction`: "for all k ∈ ℕ₀" from 0 is Lean's induction on k, and
    /// "for all k ∈ ℕ" from 1 is `Nat.le_induction` from 1; the step part's
    /// induction hypothesis keeps the page's label.
    fn induction(
        &mut self,
        step: &Step,
        block: &crate::checker::record::Block,
        claimed: &Node,
        parts: &[Option<usize>],
        depth: usize,
    ) -> Route<()> {
        let p = pad(depth);
        let spot = Self::step_spot(step);
        let [letter, set, body] = claimed.children.as_slice() else {
            return Route::no("an induction whose claim says no \"for all\"");
        };
        if claimed.notation() != crate::notations::FOR_ALL || !letter.is_name() {
            return Route::no("an induction whose claim says no \"for all\"");
        }
        let name = super::names::letter(&letter.text);
        let start = step.just.start.as_deref().unwrap_or("");
        let from_one = match (super::expr::system_of(set), start) {
            (Some(super::expr::System::NonNegative), "0") => false,
            (Some(super::expr::System::Positive), "1") => true,
            _ => return Route::no("an induction from other than the start of ℕ or ℕ₀"),
        };
        self.writer.letters.insert(
            letter.text.to_string(),
            LetterType::Number(super::templates::Num::Nat),
        );
        if from_one {
            self.push(format!("{p}intro {name} h_{name}"), step.line, spot.clone());
            // The guard put as Nat.le_induction reads it, in its place, so
            // that the induction hypothesis does not ask it again.
            self.push(
                format!("{p}replace h_{name} : 1 ≤ {name} := h_{name}"),
                step.line,
                spot.clone(),
            );
            self.push(
                format!("{p}induction {name}, h_{name} using Nat.le_induction with"),
                step.line,
                spot.clone(),
            );
        } else {
            self.push(format!("{p}intro {name}"), step.line, spot.clone());
            self.push(format!("{p}induction {name} with"), step.line, spot.clone());
        }
        for part in parts {
            let marker = part
                .and_then(|k| step.parts.get(k))
                .map(|(m, _)| m.as_str())
                .unwrap_or("");
            let openers: Vec<&crate::corpus::Opener> =
                step.openers.iter().filter(|o| o.part == *part).collect();
            match marker {
                "base" => {
                    let case = if from_one { "base" } else { "zero" };
                    self.push(format!("{p}| {case} =>"), step.line, spot.clone());
                }
                "step" => {
                    let hypothesis = openers
                        .iter()
                        .find(|o| o.is_hypothesis)
                        .map(|o| line_name(&o.label))
                        .unwrap_or_else(|| "IH".to_string());
                    if let Some(o) = openers.iter().find(|o| o.is_hypothesis) {
                        self.named.insert(o.label.clone(), vec![hypothesis.clone()]);
                        self.trees.insert(
                            o.label.clone(),
                            vec![(body.clone(), hypothesis.clone())],
                        );
                    }
                    let guard = openers
                        .iter()
                        .find(|o| !o.is_hypothesis && o.kind == Intro::Let)
                        .map(|o| line_name(&o.label))
                        .unwrap_or_else(|| format!("h_{name}"));
                    let case = if from_one {
                        format!("succ {name} {guard} {hypothesis}")
                    } else {
                        format!("succ {name} {hypothesis}")
                    };
                    self.push(format!("{p}| {case} =>"), step.line, spot.clone());
                }
                other => return Route::no(format!("an induction part {other:?}")),
            }
            // A case proved by its own `proof` block: its lines, other than
            // the induction's letter and hypothesis, are opened as a
            // `proof` block's are.
            let own: Vec<crate::corpus::Opener> = openers
                .iter()
                .filter(|o| !o.is_hypothesis)
                .filter(|o| !self.introduces_letter(o, &letter.text))
                .map(|o| (*o).clone())
                .collect();
            if let Route::Declined(d) = self.open_lines(step, &own, depth + 1) {
                return Route::Declined(d);
            }
            let children: Vec<usize> = block
                .children
                .iter()
                .copied()
                .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                .collect();
            if let Route::Declined(d) = self.steps(&children, depth + 1) {
                return Route::Declined(d);
            }
            self.push(
                format!("{p}  all_goals parley_side"),
                step.line,
                spot.clone(),
            );
        }
        Route::Built(())
    }

    /// Whether an opening line is the `let` of a letter, the induction's.
    fn introduces_letter(&self, o: &crate::corpus::Opener, letter: &str) -> bool {
        o.kind == Intro::Let
            && o.body(&self.thm.path)
                .sentences()
                .iter()
                .filter_map(|s| self.rec.page.get(s))
                .any(|n| introduces(n).is_some_and(|(l, _)| l == letter))
    }

    /// The lines that open a `proof` or `contradiction` block: each `let`
    /// introduces its letter, each `assume` its fact, and a `suppose` the
    /// opposite of the claim.
    fn open(&mut self, step: &Step, part: Option<usize>, depth: usize) -> Route<()> {
        let openers: Vec<crate::corpus::Opener> = step
            .openers
            .iter()
            .filter(|o| o.part == part)
            .cloned()
            .collect();
        self.open_lines(step, &openers, depth)
    }

    /// The opening lines given, each introduced as `open` introduces it.
    fn open_lines(
        &mut self,
        step: &Step,
        openers: &[crate::corpus::Opener],
        depth: usize,
    ) -> Route<()> {
        let p = pad(depth);
        let spot = Self::step_spot(step);
        for o in openers {
            let label = line_name(&o.label);
            self.named.insert(o.label.clone(), vec![label.clone()]);
            let body = o.body(&self.thm.path);
            let mut nodes: Vec<Node> = body
                .sentences()
                .iter()
                .filter_map(|s| self.rec.page.get(s).cloned())
                .collect();
            // A `let` the page does not read as a formula, `let X ⊆ A`, says
            // what the checker reads it to assert.
            if nodes.is_empty() {
                nodes = self
                    .rec
                    .opener_asserted
                    .get(&o.line)
                    .cloned()
                    .unwrap_or_default();
            }
            match o.kind {
                Intro::Let => {
                    for node in &nodes {
                        if let Some(letter) = super::statement::range_letter(node) {
                            self.writer.letters.insert(
                                letter.clone(),
                                LetterType::Number(super::templates::Num::Int),
                            );
                            let letter = super::names::letter(&letter);
                            self.trees.insert(
                                o.label.clone(),
                                vec![(node.clone(), label.clone())],
                            );
                            self.push(
                                format!("{p}intro {letter} {label}"),
                                o.line,
                                spot.clone(),
                            );
                            // The range's bounds beside it, which linear
                            // arithmetic reads, the membership kept for the
                            // items given it; a claim may state the bounds
                            // already.
                            self.push(
                                format!("{p}try have {label}_bounds := Finset.mem_Icc.mp {label}"),
                                o.line,
                                spot.clone(),
                            );
                            continue;
                        }
                        if let Some((letter, ty)) =
                            super::statement::introduces_function(node)
                        {
                            self.writer.letters.insert(letter.clone(), ty);
                            self.push(
                                format!("{p}intro {}", super::names::letter(&letter)),
                                o.line,
                                spot.clone(),
                            );
                            continue;
                        }
                        // `let t ∈ S` of a set S: the member and the fact
                        // that it is one, as "for all t ∈ S" gives them.
                        // `let X ⊆ A` likewise gives a set and the fact.
                        if let [t, set] = node.children.as_slice() {
                            let member = node.notation()
                                == crate::notations::MEMBERSHIP
                                && t.is_name();
                            let part =
                                &*node.notation_name() == "subset" && t.is_name();
                            let ty = match (member, part) {
                                (true, _) => {
                                    self.writer.members_of(set).map(|m| m.letter())
                                }
                                (_, true) => {
                                    self.writer.set_members(set).map(LetterType::Set)
                                }
                                _ => None,
                            };
                            if let Some(ty) = ty {
                                self.writer.letters.insert(t.text.to_string(), ty);
                                self.trees.insert(
                                    o.label.clone(),
                                    vec![(node.clone(), label.clone())],
                                );
                                self.push(
                                    format!(
                                        "{p}intro {} {label}",
                                        super::names::letter(&t.text)
                                    ),
                                    o.line,
                                    spot.clone(),
                                );
                                continue;
                            }
                        }
                        let Some((letter, system)) = introduces(node) else {
                            return Route::no(
                                "a let that introduces no letter of a number system",
                            );
                        };
                        self.writer.letters.insert(
                            letter.clone(),
                            LetterType::Number(super::expr::letter_type(system)),
                        );
                        // A block that lets a real number, the ε of a limit,
                        // writes its claims in ℝ at least: a claim about
                        // natural numbers there meets lines in ℝ.
                        let at = super::expr::letter_type(system);
                        if at >= super::templates::Num::Real {
                            self.writer.floor =
                                self.writer.floor.max(super::templates::Num::Real);
                        }
                        let letter = super::names::letter(&letter);
                        if system == super::expr::System::Positive {
                            self.push(
                                format!("{p}intro {letter} {label}"),
                                o.line,
                                spot.clone(),
                            );
                        } else {
                            self.push(
                                format!("{p}intro {letter}"),
                                o.line,
                                spot.clone(),
                            );
                        }
                    }
                }
                Intro::Assume => {
                    // A line of several sentences is the "and" of them,
                    // each sentence taken by its projection.
                    let n = nodes.len();
                    let said = nodes
                        .iter()
                        .enumerate()
                        .map(|(k, node)| {
                            (node.clone(), format!("{label}{}", projection(k, n)))
                        })
                        .collect();
                    self.trees.insert(o.label.clone(), said);
                    self.push(format!("{p}intro {label}"), o.line, spot.clone());
                }
                Intro::Suppose => {
                    let Some(node) = nodes.first() else {
                        return Route::no("a suppose the checker did not read");
                    };
                    let says = match self.writer.formula(node) {
                        Route::Built(s) => s,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    self.trees
                        .insert(o.label.clone(), vec![(node.clone(), label.clone())]);
                    // The block's claim denied, and the suppose line proved
                    // from that denial in the words the page chose for it.
                    self.push(format!("{p}by_contra hc_{label}"), o.line, spot.clone());
                    self.push(
                        format!(
                            "{p}have {label} : {} := by parley_suppose hc_{label}",
                            says.text
                        ),
                        o.line,
                        spot.clone(),
                    );
                }
            }
        }
        Route::Built(())
    }
}

/// What an `obtain` takes its witnesses from: the Lean term that proves the
/// "there is", and the "there is" itself.
struct Obtained {
    term: String,
    says: Node,
}

/// A cited line as a step uses it: the name to use, and the `have` that
/// casts it up to the claim's type where it is narrower.
struct Widened {
    have: Option<String>,
    name: String,
}

/// A tactic proof with `have` lines written before it, inside its `by`.
fn with_haves(haves: &[String], tactic: &str) -> String {
    if haves.is_empty() {
        return tactic.to_string();
    }
    let body = tactic.strip_prefix("by ").unwrap_or(tactic);
    let mut out = String::from("by");
    for h in haves {
        out.push_str(&format!("\n  {h}"));
    }
    out.push_str(&format!("\n  {}", body.replace('\n', "\n  ")));
    out
}

/// A claim `s ∈ S`, S ℤ, ℚ or ℝ and s of a wider type, shown by an
/// equation, `name`, one side of which is in S already: that side is the
/// witness, and the equation, with the casts pushed in, its proof. None
/// where the claim or the equation is not so.
fn member_by_equation(
    writer: &Writer,
    equation: &Node,
    name: &str,
    claim: &Node,
) -> Option<String> {
    let [term, set] = claim.children.as_slice() else {
        return None;
    };
    if claim.notation() != crate::notations::MEMBERSHIP
        || set.notation() != crate::notations::NUMBER_SYSTEMS
        || equation.notation() != EQUALITY
    {
        return None;
    }
    let super::expr::System::Type(n) = super::expr::system_of(set)? else {
        return None;
    };
    if writer.carrier(term).built()? <= n {
        return None;
    }
    equation.children.iter().find_map(|side| {
        let fits = writer.carrier(side).built().is_some_and(|c| c <= n);
        if !fits || side.names().is_empty() && !writer.is_number(side) {
            return None;
        }
        let w = writer.number_fixed(side, n).built()?;
        Some(format!(
            "⟨{}, by first | (push_cast; linarith [{name}]) | (rw [{name}]; push_cast; ring) | (rw [← {name}]; push_cast; ring) | exact {name} | exact {name}.symm⟩",
            w.text
        ))
    })
}

/// A witness as Lean writes it, and the tactic that puts what a line says
/// of it in scope, where it is an integer a line gives.
struct Witness {
    term: String,
    known: Option<String>,
}

/// A define a step cites: its letter, the term it names, and the Lean name
/// of its equation.
struct CitedDefine {
    name: Node,
    value: Node,
    proof: String,
    /// The argument of a function's define, the j of q(j) = F(j)², which
    /// each application q(a) puts a for; None for a define of a term.
    param: Option<String>,
}

/// The tactic lines that write the defines out wherever they stand, and
/// push in the casts that leaves; none where no define is cited.
fn written_out(defines: &[CitedDefine]) -> Vec<String> {
    if defines.is_empty() {
        return Vec::new();
    }
    let rewrites: Vec<&str> = defines.iter().map(|d| d.proof.as_str()).collect();
    vec![
        format!("try simp only [{}] at *", rewrites.join(", ")),
        "try push_cast at *".to_string(),
    ]
}

/// `node` with `to` put for each part that is `from`, the two compared as
/// the grammar prints them.
/// Whether putting one side of `equation` for the other in the left side of
/// `claim`, an equation, gives its right side.
fn makes_claim(
    equation: &Node,
    claim: &Node,
    grammar: &crate::formula::Grammar,
) -> bool {
    let (Some([from, to]), Some([left, right])) = (
        equation.children.as_slice().first_chunk::<2>(),
        claim.children.as_slice().first_chunk::<2>(),
    ) else {
        return false;
    };
    let want = grammar.print(right);
    [(from, to), (to, from)]
        .iter()
        .any(|(a, b)| grammar.print(&put_term(left, a, b, grammar)) == want)
}

fn put_term(
    node: &Node,
    from: &Node,
    to: &Node,
    grammar: &crate::formula::Grammar,
) -> Node {
    if grammar.print(node) == grammar.print(from) {
        return to.clone();
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| put_term(c, from, to, grammar))
            .collect(),
    )
}

/// `node` with `value` put for each place the letter `name` stands.
fn put_for(node: &Node, name: &Node, value: &Node) -> Node {
    if node.is_name() && node.text == name.text {
        return value.clone();
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| put_for(c, name, value))
            .collect(),
    )
}

/// How many statements an "or" joins, however it groups them.
fn disjuncts(node: &Node) -> usize {
    if node.notation() == crate::notations::DISJUNCTION {
        node.children.iter().map(disjuncts).sum()
    } else {
        1
    }
}

/// An `rcases` pattern for an "or" as its tree groups it, each disjunct
/// named in turn from `names`: `(C1 | C2) | C3` for (a ∨ b) ∨ c.
fn or_pattern(node: &Node, names: &mut std::slice::Iter<'_, String>) -> String {
    if let ([left, right], crate::notations::DISJUNCTION) =
        (node.children.as_slice(), node.notation())
    {
        let l = or_pattern(left, names);
        let r = or_pattern(right, names);
        let l = if left.notation() == crate::notations::DISJUNCTION {
            format!("({l})")
        } else {
            l
        };
        return format!("{l} | {r}");
    }
    names.next().cloned().unwrap_or_else(|| "_".to_string())
}

/// A line whose proof runs over several lines, each line after the first
/// indented by `pad` as the first is.
fn indented(text: &str, pad: &str) -> String {
    text.replace('\n', &format!("\n{pad}"))
}

/// A sentence's parts, a conjunction taken apart by Lean's projections,
/// `H3.1` and `H3.2`, as the tree joins them.
fn conjuncts(node: &Node, proof: String, out: &mut Vec<super::algebra::Cited>) {
    let joined = matches!(
        node.notation(),
        crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION
    );
    if let ([left, right], true) = (node.children.as_slice(), joined) {
        conjuncts(left, format!("{proof}.1"), out);
        conjuncts(right, format!("{proof}.2"), out);
        return;
    }
    out.push(super::algebra::Cited {
        node: node.clone(),
        proof,
    });
}

/// A claim proved from a term that gives it, as the claim's shape asks:
/// an equation by the ring identity between the two, an order by linear
/// arithmetic, anything else as it stands.
/// A sentence of an item with each property the citation gives by what it
/// says, P := t ↦ …, applied where the sentence applies it: P(u) its body
/// with u's value for t. The item's other letters stay as its statement
/// has them, as Lean's statement of it does.
fn read_at_values(
    node: &Node,
    binding: &crate::matching::Binding,
    binders: &crate::matching::FxIndexMap<
        crate::formula::notation_id::NotationId,
        crate::formula::notation::Binds,
    >,
) -> Node {
    if let ("holds-of", [p, arg]) = (&*node.notation_name(), node.children.as_slice()) {
        if let Some(stands) = binding.get(&p.text) {
            if let ("property-of", [body]) =
                (&*stands.notation_name(), stands.children.as_slice())
            {
                let arg = crate::matching::substitute_apart_by(arg, binding, binders);
                let put = crate::matching::Binding::from([(stands.text, arg)]);
                return crate::matching::substitute_apart_by(body, &put, binders);
            }
        }
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| read_at_values(c, binding, binders))
            .collect(),
    )
}

/// Whether a fact speaks of a letter the claim's leading "for all" binds.
fn bound_in(claim: &Node, fact: &Node) -> bool {
    let mut body = claim;
    let mut bound = Vec::new();
    while let (crate::notations::FOR_ALL, [letter, _, inner]) =
        (body.notation(), body.children.as_slice())
    {
        bound.push(letter.text.to_string());
        body = inner;
    }
    let names = fact.names();
    bound.iter().any(|b| names.iter().any(|n| **n == **b))
}

/// The fact under the claim's leading "for all" binders, x² ≥ 0 as "for
/// all x ∈ [0, 1], x² ≥ 0".
fn under_binders(claim: &Node, fact: &Node) -> Node {
    match (claim.notation(), claim.children.as_slice()) {
        (crate::notations::FOR_ALL, [letter, set, inner]) => claim.with_children(vec![
            letter.clone(),
            set.clone(),
            under_binders(inner, fact),
        ]),
        _ => fact.clone(),
    }
}

/// What an exhibit says of its values, taken apart as Lean nests its "and",
/// each part left to `parley_side` with what the witnesses give known: a
/// part alone is a line in scope, where the whole "and" may send `simp`
/// past its depth.
fn facts_shaped(said: &Node, known: &str) -> String {
    match (said.notation(), said.children.as_slice()) {
        (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [l, r],
        ) => {
            format!("⟨{}, {}⟩", facts_shaped(l, known), facts_shaped(r, known))
        }
        _ => format!("by {known}parley_side"),
    }
}

/// An `obtain` pattern for a sentence, one name to each part of its "and"
/// as it nests, the names taken in order; a part left with no name is `_`.
fn shaped_pattern(said: &Node, names: &mut impl Iterator<Item = String>) -> String {
    match (said.notation(), said.children.as_slice()) {
        (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [l, r],
        ) => {
            let left = shaped_pattern(l, names);
            let right = shaped_pattern(r, names);
            format!("⟨{left}, {right}⟩")
        }
        _ => names.next().unwrap_or_else(|| "_".to_string()),
    }
}

/// A proof as a tactic to stand among `first`'s alternatives: its own
/// tactics where it is a `by` block, as an error inside a nested `by`,
/// `exact (by …)`, is logged and does not fail the alternative, so `first`
/// would not go on to the next.
fn as_tactic(proof: &str) -> String {
    match proof.strip_prefix("by ") {
        Some(t) => format!("({t})"),
        None => format!("exact ({proof})"),
    }
}

fn close(claim: &Node, term: &str) -> String {
    // An equation or order between sets, members or counts is closed as
    // any other claim: the closers for numbers work in a field or a ring.
    let of_numbers = claim
        .children
        .iter()
        .all(|c| c.sort.is("number") && !Writer::counts(c));
    match claim.notation() {
        // An instance whose casts sit otherwise than the claim's, ↑(0 : ℕ)
        // for 0, is taken with them pushed in, and one whose equation the
        // claim turns round, as a cited rule written a + b = c claimed as
        // c = a + b, is taken negated. A corpus theorem stated in a
        // wider type than the claim, ℝ for a claim in ℚ, has the claim moved
        // up to it.
        EQUALITY if of_numbers => {
            // A remainder of integers written with `%`, beside an item of
            // set.mm's mod of real numbers: the item's put as `%` first.
            let of_mod = claim.walk().iter().any(|n| &*n.notation_name() == "mod");
            let as_remainder = match of_mod {
                true => format!(
                    " | (have h := {term}; simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h)"
                ),
                false => String::new(),
            };
            // A term given a natural as an integer's `toNat`, rewritten back
            // by `▸` (`instance`): an error elaborating it against the goal,
            // as `exact_mod_cast` does, is logged and does not fail the
            // alternative, so it is cast from a `have`, which fails.
            // A claim of exp, sin or cos, whose items are stated over ℂ: the
            // item read back in ℝ.
            let of_complex = match claim.walk().iter().any(|n| {
                n.notation() == crate::notations::APPLICATION
                    && n.children
                        .first()
                        .is_some_and(|f| matches!(&*f.text, "exp" | "sin" | "cos"))
            }) {
                true => format!(" | (have h := {term}; parley_of_complex h)"),
                false => String::new(),
            };
            let by_to_nat = term.contains("Int.toNat_of_nonneg");
            // The `▸` of a `toNat` rewrites its cast to ℤ only; one cast to
            // ℚ or ℝ, (1 − 2y).toNat in ℚ, is put back as the integer by
            // `parley_cast_toNat`.
            let cast = match by_to_nat {
                true => format!(
                    "(have h := {term}; exact_mod_cast h) | (have h := {term}; exact_mod_cast h.symm) | (have h := {term}; simp (disch := parley_side) only [parley_cast_toNat] at h; (try push_cast at h ⊢); linear_combination (norm := parley_norm) h)"
                ),
                false => format!("exact_mod_cast {term} | exact_mod_cast ({term}).symm"),
            };
            format!(
                "by first | linear_combination (norm := parley_norm) {term} | (have h := {term}; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := {term}; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | {cast} | (have h := {term}; rify; linear_combination (norm := parley_norm) h) | (have h := {term}; qify; linear_combination (norm := parley_norm) h) | (have h := {term}; parley_int_power h){as_remainder}{of_complex} | (have h := {term}; parley_side)"
            )
        }
        // A numeral given to a letter of ℕ arrives cast, ((3 : ℕ) : ℤ),
        // which linarith reads only once the cast is pushed in.
        // An item over ℝ cited for a claim the page computes in ℚ gives
        // the claim cast up, which exact_mod_cast brings down.
        ORDER if of_numbers => format!(
            "by first | linarith [{term}] | (have h := {term}; push_cast at h; linarith) | exact_mod_cast {term} | (have h := {term}; parley_side)"
        ),
        // A relation said either way round, a congruence or a ↔, as the
        // claim writes it. Here and above, the last way takes the
        // citation's "and" apart: a definition unfolded to "p > 1 and for
        // all d …" gives either half. A claim with a listed set in it, which
        // may be in another order than the item's, {w, u} for {u, w}, is put
        // in one order on both sides.
        _ => {
            let listed = claim.walk().iter().any(|n| {
                matches!(
                    &*n.notation_name(),
                    "listed-two" | "listed-three" | "listed-four"
                )
            });
            // An equation of sets, member by member, which takes a listed
            // set in any order and of any size; another relation, its pairs
            // turned round.
            let reorder = match (listed, claim.notation() == EQUALITY) {
                (true, true) => format!(
                    " | (have h := {term}; ext x; rw [Set.ext_iff] at h; specialize h x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢; tauto)"
                ),
                (true, false) => format!(
                    " | (have h := {term}; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h)"
                ),
                (false, _) => String::new(),
            };
            format!(
                "by first | exact {term} | exact ({term}).symm | simpa using {term} | exact_mod_cast {term}{reorder} | (have h := {term}; parley_side)"
            )
        }
    }
}
