//! Writing Metamath, in the two ways this project writes it.
//!
//! A Metamath statement is a flat run of tokens and a proof is a flat run of
//! labels in reverse Polish. Neither is comfortable to type, so everything
//! that produces one goes through this module.
//!
//! The constructors below build reverse Polish directly: `mul(a, b)` is the
//! product of two terms already in reverse Polish. They are what the
//! hand-written comparison proofs use, and they need nothing but themselves.
//!
//! [`Builder`] goes the other way. A statement is written once, in the
//! notation set.mm writes it in, and `rpn` parses it; `ap` assembles one
//! proof step from a label and what it is applied to, reading the push order
//! off the label's own signature. Nothing is transcribed into stack order by
//! hand. It needs the library, because only the library knows what a label
//! wants pushed.
//!
//! A term and a proof are different types here. A term is its reverse Polish
//! text; a proof is the steps it was built as, and what on the page it rests
//! on. [`Builder::term`] joins text and cannot be handed a proof;
//! [`Builder::proof`] builds a proof and refuses text that does not end in a
//! label whose statement is `|-`.

use std::cell::{OnceCell, RefCell};
use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::IndexMap;

use super::kernel::{FloatLabels, Syntax};
use super::library::{Kind, Signature, Signatures};
use crate::outcome::Checked;

/// One label applied to the steps it takes, and what kind of thing that
/// builds: a `wff`, a `class`, a `setvar`, or a proof (`|-`).
///
/// A proof is built as steps that refer to their parts rather than copying
/// them. Written out in normal format, the intermediate value theorem's
/// proof is 63.6 million labels and only 3,030 distinct subproofs; built as
/// text it took gigabytes.
#[derive(Debug)]
pub struct Step {
    pub label: Rc<str>,
    pub kids: Vec<StepRef>,
    pub typecode: Rc<str>,
}

pub type StepRef = Rc<Step>;

/// Steps in normal format, written without recursion: these run to millions
/// of labels and deeper than a stack is deep.
pub fn spelt(items: &[StepRef]) -> String {
    let mut out: Vec<&str> = Vec::new();
    let mut work: Vec<(&StepRef, bool)> =
        items.iter().rev().map(|s| (s, false)).collect();
    while let Some((step, done)) = work.pop() {
        if done || step.kids.is_empty() {
            out.push(&step.label);
            continue;
        }
        work.push((step, true));
        work.extend(step.kids.iter().rev().map(|k| (k, false)));
    }
    out.join(" ")
}

/// A proof, and what on the page it rests on.
///
/// `origin` names the things a reader can point at — a hypothesis, a
/// block's assumption, a proved line, a `requires` line — that went into
/// this proof. Library labels are not among them: they are what the page
/// never writes.
///
/// It is not text, and has no `Display`: `text` is what it spells, for
/// reading it. Code that handled a proof as a string and so lost what it
/// rests on would leave a proof resting on nothing, which every check of
/// what a step names would pass.
#[derive(Clone, Debug)]
pub struct Proof {
    pub items: Vec<StepRef>,
    pub origin: BTreeSet<String>,
}

impl Proof {
    /// The proof in normal format, for reading it; nothing builds it.
    pub fn text(&self) -> String {
        spelt(&self.items)
    }

    /// The label applied last, which says what the proof is of.
    pub fn last(&self) -> &str {
        &self.items[self.items.len() - 1].label
    }

    /// The same proof, resting also on `more`.
    pub fn resting(mut self, more: impl IntoIterator<Item = String>) -> Proof {
        self.origin.extend(more);
        self
    }
}

/// One part of a proof being built: labels as text, or a proof.
#[derive(Clone, Copy)]
pub enum Part<'a> {
    Text(&'a str),
    Proof(&'a Proof),
}

impl<'a> From<&'a str> for Part<'a> {
    fn from(text: &'a str) -> Part<'a> {
        Part::Text(text)
    }
}

impl<'a> From<&'a String> for Part<'a> {
    fn from(text: &'a String) -> Part<'a> {
        Part::Text(text)
    }
}

impl<'a> From<&'a Proof> for Part<'a> {
    fn from(proof: &'a Proof) -> Part<'a> {
        Part::Proof(proof)
    }
}

/// Tokens in order, skipping any that are empty, as text: a term or a
/// formula in reverse Polish.
pub fn seq(parts: &[&str]) -> String {
    parts
        .iter()
        .filter(|p| !p.is_empty())
        .copied()
        .collect::<Vec<_>>()
        .join(" ")
}

/// Tokens in order, skipping any that are empty, from any mix of `&str` and
/// `String`: `seq!(claim, th, pf, "a1i")`.
#[macro_export]
macro_rules! seq {
    ($($part:expr),* $(,)?) => {
        $crate::mm::spell::seq(&[$(::std::convert::AsRef::<str>::as_ref(&$part)),*])
    };
}

// Terms. `co` is Metamath's binary operation and most of the rest are it
// with the operator filled in. Each takes `&str` or `String` alike, so a
// term built inline is passed as it is.
pub fn co(a: impl AsRef<str>, b: impl AsRef<str>, f: impl AsRef<str>) -> String {
    seq!(a, b, f, "co")
}
pub fn mul(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    co(a, b, "cmul")
}
pub fn add(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    co(a, b, "caddc")
}
pub fn sub(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    co(a, b, "cmin")
}
pub fn div(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    co(a, b, "cdiv")
}
pub fn exp(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    co(a, b, "cexp")
}
pub fn fz(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    co(a, b, "cfz")
}
pub fn neg(a: impl AsRef<str>) -> String {
    seq!(a, "cneg")
}
pub fn summ(
    range: impl AsRef<str>,
    body: impl AsRef<str>,
    v: impl AsRef<str>,
) -> String {
    seq!(range, body, v, "csu")
}

// Formulas.
pub fn cel(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    seq!(a, b, "wcel")
}
pub fn br(a: impl AsRef<str>, b: impl AsRef<str>, r: impl AsRef<str>) -> String {
    seq!(a, b, r, "wbr")
}
pub fn lt(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    br(a, b, "clt")
}
pub fn le(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    br(a, b, "cle")
}
pub fn dvds(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    br(a, b, "cdvds")
}
pub fn eq(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    seq!(a, b, "wceq")
}
pub fn ne(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    seq!(a, b, "wne")
}
pub fn wa(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    seq!(a, b, "wa")
}
pub fn wo(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    seq!(a, b, "wo")
}
pub fn wi(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    seq!(a, b, "wi")
}
pub fn wb(a: impl AsRef<str>, b: impl AsRef<str>) -> String {
    seq!(a, b, "wb")
}
pub fn wn(a: impl AsRef<str>) -> String {
    seq!(a, "wn")
}
pub fn w3a(a: impl AsRef<str>, b: impl AsRef<str>, c: impl AsRef<str>) -> String {
    seq!(a, b, c, "w3a")
}
pub fn rex(body: impl AsRef<str>, v: impl AsRef<str>, over: impl AsRef<str>) -> String {
    seq!(body, v, over, "wrex")
}

/// What a step binds each of its label's variables to, in reverse Polish.
pub type Binds = IndexMap<String, String>;

/// A binding written out: `binds! { "ph" => b.wff(..), "A" => b.class(..) }`.
#[macro_export]
macro_rules! binds {
    ($($var:expr => $term:expr),* $(,)?) => {{
        #[allow(unused_mut)]
        let mut out = $crate::mm::spell::Binds::new();
        $(out.insert(String::from($var), String::from($term));)*
        out
    }};
}

/// A binding with more bound, or bound otherwise: `{**w, 'ps': ...}`.
pub fn with(base: &Binds, more: Binds) -> Binds {
    let mut out = base.clone();
    out.extend(more);
    out
}

/// How many things a label takes, what it builds, and the kind of each
/// thing it takes where that is known.
#[derive(Clone, Debug)]
struct Taking {
    takes: usize,
    typecode: Rc<str>,
    kinds: Option<Vec<String>>,
}

/// Statements in set.mm's notation, proofs in stack order.
pub struct Builder {
    pub sigs: Signatures,
    syntax: OnceCell<Syntax>,
    /// Each variable's float, shared so that a caller may hold it while it
    /// builds.
    pub flabel: Rc<FloatLabels>,
    /// Where each label stands in the library, which is the order floats
    /// are pushed in.
    pub forder: IndexMap<String, usize>,
    /// What a theorem of this corpus that a proof cites takes, where the
    /// library does not have it.
    pub arities: IndexMap<String, Signature>,
    arity_of: RefCell<IndexMap<String, Taking>>,
    term_steps: RefCell<IndexMap<String, Vec<StepRef>>>,
}

impl Builder {
    pub fn new(sigs: Signatures) -> Builder {
        let mut flabel = IndexMap::new();
        for (label, s) in &sigs {
            if s.kind == Kind::Float {
                flabel.insert(s.statement[1].clone(), label.clone());
            }
        }
        let forder = sigs
            .keys()
            .enumerate()
            .map(|(i, l)| (l.clone(), i))
            .collect();
        Builder {
            sigs,
            syntax: OnceCell::new(),
            flabel: Rc::new(FloatLabels::new(flabel)),
            forder,
            arities: IndexMap::new(),
            arity_of: RefCell::new(IndexMap::new()),
            term_steps: RefCell::new(IndexMap::new()),
        }
    }

    /// set.mm's syntax axioms, built the first time one is parsed.
    pub fn syntax(&self) -> &Syntax {
        self.syntax.get_or_init(|| Syntax::new(&self.sigs))
    }

    /// Register a lemma this file proves, so a later one may apply it.
    pub fn define(&mut self, label: &str, statement: &str) {
        let tokens: Vec<String> =
            statement.split_whitespace().map(String::from).collect();
        let mut free: Vec<&String> = tokens
            .iter()
            .filter(|t| self.flabel.contains(t))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        free.sort_by_key(|v| self.forder[self.flabel.get(v).unwrap()]);
        let floats = free
            .iter()
            .map(|v| {
                let float = &self.sigs[self.flabel.get(v).unwrap()];
                (float.statement[0].clone(), (*v).clone())
            })
            .collect();
        self.sigs.insert(
            label.to_string(),
            Signature {
                label: label.to_string(),
                kind: Kind::Theorem,
                statement: tokens,
                floats,
                essentials: Vec::new(),
                disjoint: BTreeSet::new(),
            },
        );
    }

    /// Register a hypothesis a lemma of this file states, so its proof may
    /// rest on it: a step taking nothing and giving the statement.
    pub fn hypothesis(&mut self, label: &str, statement: &str) {
        self.sigs.insert(
            label.to_string(),
            Signature {
                label: label.to_string(),
                kind: Kind::Essential,
                statement: statement.split_whitespace().map(String::from).collect(),
                floats: Vec::new(),
                essentials: Vec::new(),
                disjoint: BTreeSet::new(),
            },
        );
    }

    /// A term written in set.mm's notation, as the labels that build it.
    pub fn rpn(&self, text: &str, start: &str) -> Checked<String> {
        let tokens: Vec<&str> = text.split_whitespace().collect();
        let term = self.syntax().parse(&tokens, start)?;
        Ok(term.rpn(&self.flabel).to_string())
    }

    /// The label that pushes a variable: its floating hypothesis.
    pub fn float(&self, var: &str) -> String {
        self.flabel
            .get(var)
            .cloned()
            .unwrap_or_else(|| panic!("no float for {var}"))
    }

    /// A proof that is one label taking nothing: a hypothesis, or a closed
    /// lemma such as `1z`.
    pub fn step(&self, label: &str) -> Proof {
        self.proof(&[Part::Text(label)])
    }

    /// A class written in set.mm's notation, in reverse Polish.
    pub fn class(&self, text: &str) -> String {
        self.rpn(text, "class")
            .unwrap_or_else(|p| panic!("{text:?} is not a class: {p}"))
    }

    /// A formula written in set.mm's notation, in reverse Polish.
    pub fn wff(&self, text: &str) -> String {
        self.rpn(text, "wff")
            .unwrap_or_else(|p| panic!("{text:?} is not a formula: {p}"))
    }

    /// One step: what the label wants pushed, then what it is applied to.
    ///
    /// The floating hypotheses go first, in the order set.mm declares them,
    /// each as the term bound to it or as its own variable where the step
    /// leaves it open; then the proofs of the essential hypotheses, in the
    /// order the label lists them.
    pub fn ap(&self, label: &str, binds: &Binds, essentials: &[&Proof]) -> Proof {
        let sig = self
            .sigs
            .get(label)
            .unwrap_or_else(|| panic!("no label {label} to apply"));
        let pushed: Vec<String> = sig
            .floats
            .iter()
            .map(|(_, var)| match binds.get(var) {
                Some(t) => t.clone(),
                None => self.flabel.get(var).cloned().unwrap_or_default(),
            })
            .collect();
        let mut parts: Vec<Part> = pushed.iter().map(Part::from).collect();
        parts.extend(essentials.iter().map(|p| Part::Proof(p)));
        parts.push(Part::Text(label));
        self.proof(&parts)
    }

    /// Tokens in order, skipping any that are empty: a term.
    pub fn term(&self, parts: &[&str]) -> String {
        seq(parts)
    }

    /// Whether reverse Polish ending in this label is a proof: the label's
    /// statement is set.mm's `|-`.
    pub fn proves(&self, label: &str) -> bool {
        self.sigs
            .get(label)
            .is_some_and(|s| s.statement.first().map(String::as_str) == Some("|-"))
    }

    /// A proof, from labels and proofs in order: resting on what its parts
    /// rest on. Each part is checked against what its label takes, so a
    /// proof handed where a class belongs is refused at the call that made
    /// it, and not by the verifier later.
    pub fn proof(&self, parts: &[Part]) -> Proof {
        let parts: Vec<Part> = parts
            .iter()
            .copied()
            .filter(|p| !matches!(p, Part::Text("")))
            .collect();
        let end = match parts.last() {
            Some(Part::Proof(p)) => p.last().to_string(),
            Some(Part::Text(t)) => t.rsplit(' ').next().unwrap_or("").to_string(),
            None => String::new(),
        };
        if !self.proves(&end) {
            panic!("reverse Polish ending in {end:?} is a term, not a proof");
        }
        let mut stack: Vec<StepRef> = Vec::new();
        let mut origin = BTreeSet::new();
        for part in &parts {
            match part {
                Part::Proof(p) => {
                    stack.extend(p.items.iter().cloned());
                    origin.extend(p.origin.iter().cloned());
                }
                Part::Text(t) => self.read_onto(t, &mut stack),
            }
        }
        Proof {
            items: stack,
            origin,
        }
    }

    /// The labels of `text` applied onto `stack`.
    ///
    /// Text that builds whole things of its own — a term, a scope — is read
    /// once and its steps shared wherever it is written again. Text that
    /// takes what is already on the stack, a bare `syl`, is applied where it
    /// stands.
    fn read_onto(&self, text: &str, stack: &mut Vec<StepRef>) {
        if let Some(known) = self.term_steps.borrow().get(text) {
            stack.extend(known.iter().cloned());
            return;
        }
        let base = stack.len();
        let mut low = base;
        for label in text.split_whitespace() {
            let taking = self.taking(label);
            if stack.len() < taking.takes {
                panic!(
                    "{label} takes {} things and has {}: …{}",
                    taking.takes,
                    stack.len(),
                    tail(text, 60)
                );
            }
            let kids: Vec<StepRef> = stack.split_off(stack.len() - taking.takes);
            if let Some(kinds) = &taking.kinds {
                for (n, (kid, kind)) in kids.iter().zip(kinds).enumerate() {
                    if &*kid.typecode != kind {
                        panic!(
                            "{label} takes a {kind} in place {} and is handed a {}: …{}",
                            n + 1,
                            kid.typecode,
                            tail(&spelt(std::slice::from_ref(kid)), 60)
                        );
                    }
                }
            }
            low = low.min(stack.len());
            stack.push(Rc::new(Step {
                label: Rc::from(label),
                kids,
                typecode: taking.typecode,
            }));
        }
        if low >= base {
            self.term_steps
                .borrow_mut()
                .insert(text.to_string(), stack[base..].to_vec());
        }
    }

    fn taking(&self, label: &str) -> Taking {
        if let Some(found) = self.arity_of.borrow().get(label) {
            return found.clone();
        }
        let found = match self.sigs.get(label) {
            Some(sig) => {
                let mut kinds: Vec<String> =
                    sig.floats.iter().map(|(t, _)| t.clone()).collect();
                kinds.extend(std::iter::repeat_n(
                    "|-".to_string(),
                    sig.essentials.len(),
                ));
                Taking {
                    takes: kinds.len(),
                    typecode: Rc::from(sig.statement[0].as_str()),
                    kinds: if sig.kind == Kind::Float {
                        None
                    } else {
                        Some(kinds)
                    },
                }
            }
            None => {
                // A theorem this corpus proves and a proof cites is not in
                // the library, and what it takes is known only by count.
                let sig = self.arities.get(label).unwrap_or_else(|| {
                    panic!("no label {label} in the library or the corpus")
                });
                Taking {
                    takes: sig.floats.len() + sig.essentials.len(),
                    typecode: Rc::from(sig.statement[0].as_str()),
                    kinds: None,
                }
            }
        };
        self.arity_of
            .borrow_mut()
            .insert(label.to_string(), found.clone());
        found
    }
}

/// The last `n` characters of a text, for a message.
fn tail(text: &str, n: usize) -> String {
    let chars: Vec<char> = text.chars().collect();
    chars[chars.len().saturating_sub(n)..].iter().collect()
}
