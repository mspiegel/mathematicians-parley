//! Reading a set.mm statement as a term.
//!
//! A proof is written in reverse Polish and a statement is written in full,
//! and the elaborator needs to go between them. Turning a term into a
//! statement is substitution; turning a statement into a term is parsing,
//! and set.mm's syntax axioms are the grammar. They are an ordinary
//! context-free grammar — some fifteen hundred productions, none longer than
//! sixteen symbols — so this is an ordinary chart parse.
//!
//! What it buys is that a lemma can be matched rather than described.
//! Without it the database would have to say which of a lemma's variables
//! each part of a readable statement fills, and what each of its essential
//! hypotheses asks for. With it, the lemma's own statement says both.
//!
//! A statement writes its parts in reading order and a proof pushes them in
//! the order the database declares them, which is not the same: `( A F B )`
//! reads A, F, B and pushes A, B, F. So each rule carries the permutation
//! between them.

use std::cell::{OnceCell, RefCell};
use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use super::library::{Kind, Signature, Signatures};
use crate::outcome::{Checked, Problem};
use crate::text::repr;

/// The typecodes a syntax axiom builds.
pub const TYPECODES: [&str; 3] = ["wff", "class", "setvar"];

/// One symbol of a production: a constant token, or a hole of a typecode.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Symbol {
    Token(String),
    Hole(String),
}

/// One syntax axiom, as a production of the grammar.
#[derive(Debug)]
struct Rule {
    label: Rc<str>,
    yields: String,
    symbols: Vec<Symbol>,
    /// The push position of each part, in reading order.
    order: Vec<usize>,
}

struct TermData {
    label: Option<Rc<str>>,
    children: Vec<Term>,
    variable: Option<Rc<str>>,
    names: OnceCell<Rc<BTreeSet<Rc<str>>>>,
    rpn: RefCell<Option<(u64, Rc<str>)>>,
}

/// A parsed statement: a constructor applied to terms, or a variable.
///
/// A term is built and then only read, so both of the walks below are kept
/// once they have been made. Terms are shared, and a term parsed twice from
/// the same tokens is the same term.
#[derive(Clone)]
pub struct Term(Rc<TermData>);

impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0.variable {
            Some(v) => write!(f, "{v}"),
            None => {
                write!(f, "{}(", self.0.label.as_deref().unwrap_or(""))?;
                for (i, c) in self.0.children.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{c:?}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// What each variable is pushed by: its floating hypothesis's label.
///
/// A term keeps the reverse Polish it was last written as, with the map it
/// was written by, so each map carries an identity of its own: one built
/// later never answers for one dropped before it.
#[derive(Debug)]
pub struct FloatLabels {
    id: u64,
    map: IndexMap<String, String>,
}

static NEXT_LABELS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

impl FloatLabels {
    pub fn new(map: IndexMap<String, String>) -> FloatLabels {
        let id = NEXT_LABELS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        FloatLabels { id, map }
    }

    pub fn get(&self, var: &str) -> Option<&String> {
        self.map.get(var)
    }

    pub fn contains(&self, var: &str) -> bool {
        self.map.contains_key(var)
    }

    pub fn map(&self) -> &IndexMap<String, String> {
        &self.map
    }
}

impl Clone for FloatLabels {
    fn clone(&self) -> FloatLabels {
        FloatLabels::new(self.map.clone())
    }
}

impl Term {
    pub fn apply(label: &str, children: Vec<Term>) -> Term {
        Term::make(Some(Rc::from(label)), children, None)
    }

    pub fn var(name: &str) -> Term {
        Term::make(None, Vec::new(), Some(Rc::from(name)))
    }

    fn make(
        label: Option<Rc<str>>,
        children: Vec<Term>,
        variable: Option<Rc<str>>,
    ) -> Term {
        Term(Rc::new(TermData {
            label,
            children,
            variable,
            names: OnceCell::new(),
            rpn: RefCell::new(None),
        }))
    }

    pub fn label(&self) -> Option<&str> {
        self.0.label.as_deref()
    }

    pub fn children(&self) -> &[Term] {
        &self.0.children
    }

    pub fn variable(&self) -> Option<&str> {
        self.0.variable.as_deref()
    }

    pub fn same_object(&self, other: &Term) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }

    /// The term as a proof writes it, pushing what each label wants.
    pub fn rpn(&self, labels: &FloatLabels) -> Rc<str> {
        let key = labels.id;
        if let Some((held, said)) = &*self.0.rpn.borrow() {
            if *held == key {
                return said.clone();
            }
        }
        let said: Rc<str> = match &self.0.variable {
            Some(v) => Rc::from(labels.get(v).map(String::as_str).unwrap_or("")),
            None => {
                let mut parts: Vec<Rc<str>> =
                    self.0.children.iter().map(|c| c.rpn(labels)).collect();
                parts.push(self.0.label.clone().unwrap_or_else(|| Rc::from("")));
                let joined: Vec<&str> = parts.iter().map(|p| &**p).collect();
                Rc::from(joined.join(" "))
            }
        };
        *self.0.rpn.borrow_mut() = Some((key, said.clone()));
        said
    }

    /// The variables the term mentions.
    pub fn names(&self) -> Rc<BTreeSet<Rc<str>>> {
        self.0
            .names
            .get_or_init(|| {
                let mut out = BTreeSet::new();
                match &self.0.variable {
                    Some(v) => {
                        out.insert(v.clone());
                    }
                    None => {
                        for c in &self.0.children {
                            out.extend(c.names().iter().cloned());
                        }
                    }
                }
                Rc::new(out)
            })
            .clone()
    }

    pub fn substitute(&self, binding: &IndexMap<String, Term>) -> Term {
        if let Some(v) = &self.0.variable {
            return binding.get(&**v).cloned().unwrap_or_else(|| self.clone());
        }
        Term::make(
            self.0.label.clone(),
            self.0
                .children
                .iter()
                .map(|c| c.substitute(binding))
                .collect(),
            None,
        )
    }
}

/// Whether two terms are one term.
pub fn same(a: &Term, b: &Term) -> bool {
    if a.variable().is_some() || b.variable().is_some() {
        return a.variable() == b.variable();
    }
    a.label() == b.label()
        && a.children().len() == b.children().len()
        && a.children()
            .iter()
            .zip(b.children())
            .all(|(x, y)| same(x, y))
}

/// Bind the pattern's variables so that it becomes the ground term.
pub fn match_term(
    pattern: &Term,
    ground: &Term,
    binding: &IndexMap<String, Term>,
    variables: &IndexSet<String>,
) -> Option<IndexMap<String, Term>> {
    if let Some(v) = pattern.variable() {
        if variables.contains(v) {
            if let Some(seen) = binding.get(v) {
                return same(seen, ground).then(|| binding.clone());
            }
            let mut out = binding.clone();
            out.insert(v.to_string(), ground.clone());
            return Some(out);
        }
    }
    if pattern.variable().is_some() || ground.variable().is_some() {
        return (pattern.variable() == ground.variable()).then(|| binding.clone());
    }
    if pattern.label() != ground.label()
        || pattern.children().len() != ground.children().len()
    {
        return None;
    }
    let mut binding = binding.clone();
    for (a, b) in pattern.children().iter().zip(ground.children()) {
        binding = match_term(a, b, &binding, variables)?;
    }
    Some(binding)
}

#[derive(Clone)]
struct Item {
    rule: usize,
    dot: usize,
    origin: usize,
    parts: Rc<Vec<Term>>,
}

/// set.mm's syntax axioms, ready to parse with.
pub struct Syntax {
    rules: Vec<Rule>,
    by_yield: IndexMap<String, Vec<usize>>,
    /// Each variable's typecode, and the label of its float.
    pub typecode: IndexMap<String, String>,
    pub label: FloatLabels,
    spelt: RefCell<IndexMap<(Vec<String>, String), Term>>,
}

impl Syntax {
    pub fn new(signatures: &Signatures) -> Syntax {
        let mut typecode = IndexMap::new();
        let mut floats = IndexMap::new();
        for sig in signatures.values() {
            if sig.kind == Kind::Float {
                typecode.insert(sig.statement[1].clone(), sig.statement[0].clone());
                floats.insert(sig.statement[1].clone(), sig.label.clone());
            }
        }
        let label = FloatLabels::new(floats);
        let mut rules = Vec::new();
        let mut by_yield: IndexMap<String, Vec<usize>> = TYPECODES
            .iter()
            .map(|t| (t.to_string(), Vec::new()))
            .collect();
        for sig in signatures.values() {
            if sig.kind != Kind::Axiom
                || !TYPECODES.contains(&sig.statement[0].as_str())
            {
                continue;
            }
            let mut symbols = Vec::new();
            let mut reading: Vec<&str> = Vec::new();
            for token in &sig.statement[1..] {
                match typecode.get(token) {
                    Some(kind) => {
                        symbols.push(Symbol::Hole(kind.clone()));
                        reading.push(token);
                    }
                    None => symbols.push(Symbol::Token(token.clone())),
                }
            }
            let order = if reading.is_empty() {
                Vec::new()
            } else {
                sig.push()
                    .iter()
                    .map(|v| reading.iter().position(|r| r == v).unwrap_or(0))
                    .collect()
            };
            let at = rules.len();
            by_yield
                .entry(sig.statement[0].clone())
                .or_default()
                .push(at);
            rules.push(Rule {
                label: Rc::from(sig.label.as_str()),
                yields: sig.statement[0].clone(),
                symbols,
                order,
            });
        }
        Syntax {
            rules,
            by_yield,
            typecode,
            label,
            spelt: RefCell::new(IndexMap::new()),
        }
    }

    fn build(&self, rule: usize, parts: &[Term]) -> Term {
        let rule = &self.rules[rule];
        Term::make(
            Some(rule.label.clone()),
            rule.order.iter().map(|&i| parts[i].clone()).collect(),
            None,
        )
    }

    /// The term these tokens spell, or a defect if they spell none.
    pub fn parse(&self, tokens: &[&str], start: &str) -> Checked<Term> {
        let key: (Vec<String>, String) = (
            tokens.iter().map(|t| t.to_string()).collect(),
            start.to_string(),
        );
        if let Some(held) = self.spelt.borrow().get(&key) {
            return Ok(held.clone());
        }
        let found = self.spell(tokens, start)?;
        self.spelt.borrow_mut().insert(key, found.clone());
        Ok(found)
    }

    /// A labelled statement's claim, as a term.
    pub fn statement(&self, signature: &Signature) -> Checked<Term> {
        let tokens: Vec<&str> = signature.statement[1..]
            .iter()
            .map(String::as_str)
            .collect();
        self.parse(&tokens, "wff")
    }

    /// What these tokens spell, worked out rather than remembered.
    fn spell(&self, tokens: &[&str], start: &str) -> Checked<Term> {
        // A statement may be one variable and nothing else, which no rule
        // produces: `vtocl3` concludes `ps`.
        if tokens.len() == 1
            && self.typecode.get(tokens[0]).map(String::as_str) == Some(start)
        {
            return Ok(Term::var(tokens[0]));
        }
        let n = tokens.len();
        let mut chart: Vec<IndexMap<(usize, usize, usize), Item>> =
            (0..=n).map(|_| IndexMap::new()).collect();
        // What has been offered at a position, so it is offered once. set.mm
        // has hundreds of productions yielding `class`, and every item
        // waiting for one would otherwise offer them all again.
        let mut told: IndexSet<(usize, String)> = IndexSet::new();
        told.insert((0, start.to_string()));
        let empty = Rc::new(Vec::new());
        for &rule in self.by_yield.get(start).map_or(&[][..], Vec::as_slice) {
            add(&mut chart[0], rule, 0, 0, empty.clone());
        }
        for i in 0..=n {
            let mut queue: Vec<Item> = chart[i].values().cloned().collect();
            let mut seen = 0;
            while seen < queue.len() {
                let item = queue[seen].clone();
                seen += 1;
                let rule = &self.rules[item.rule];
                if item.dot == rule.symbols.len() {
                    let made = self.build(item.rule, &item.parts);
                    let older: Vec<Item> =
                        chart[item.origin].values().cloned().collect();
                    for o in older {
                        let orule = &self.rules[o.rule];
                        if o.dot == orule.symbols.len() {
                            continue;
                        }
                        match &orule.symbols[o.dot] {
                            Symbol::Hole(what) if *what == rule.yields => {}
                            _ => continue,
                        }
                        let mut parts = (*o.parts).clone();
                        parts.push(made.clone());
                        if let Some(added) = add(
                            &mut chart[i],
                            o.rule,
                            o.dot + 1,
                            o.origin,
                            Rc::new(parts),
                        ) {
                            queue.push(added);
                        }
                    }
                    continue;
                }
                match &rule.symbols[item.dot] {
                    Symbol::Hole(what) => {
                        if told.insert((i, what.clone())) {
                            for &other in
                                self.by_yield.get(what).map_or(&[][..], Vec::as_slice)
                            {
                                if let Some(added) =
                                    add(&mut chart[i], other, 0, i, empty.clone())
                                {
                                    queue.push(added);
                                }
                            }
                        }
                        // A variable of the statement stands for itself.
                        if i < n && self.typecode.get(tokens[i]) == Some(what) {
                            let mut parts = (*item.parts).clone();
                            parts.push(Term::var(tokens[i]));
                            add(
                                &mut chart[i + 1],
                                item.rule,
                                item.dot + 1,
                                item.origin,
                                Rc::new(parts),
                            );
                        }
                    }
                    Symbol::Token(what) => {
                        if i < n && tokens[i] == what {
                            add(
                                &mut chart[i + 1],
                                item.rule,
                                item.dot + 1,
                                item.origin,
                                item.parts.clone(),
                            );
                        }
                    }
                }
            }
        }
        for item in chart[n].values() {
            let rule = &self.rules[item.rule];
            if item.origin == 0
                && item.dot == rule.symbols.len()
                && rule.yields == start
            {
                return Ok(self.build(item.rule, &item.parts));
            }
        }
        Err(Problem::new(
            "",
            0,
            format!("cannot read {}", repr(&tokens.join(" "))),
        ))
    }
}

/// Put one item in a chart row, and give it back if it is new.
fn add(
    row: &mut IndexMap<(usize, usize, usize), Item>,
    rule: usize,
    dot: usize,
    origin: usize,
    parts: Rc<Vec<Term>>,
) -> Option<Item> {
    let key = (rule, dot, origin);
    if row.contains_key(&key) {
        return None;
    }
    let item = Item {
        rule,
        dot,
        origin,
        parts,
    };
    row.insert(key, item.clone());
    Some(item)
}
