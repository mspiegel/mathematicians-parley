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
use super::library::{Kind, Layered, Signature};
use super::rpn::{Rpn, Spell};
use crate::formula::symbol::Symbol;
use crate::matching::FxIndexMap;

/// One label applied to the steps it takes, and what kind of thing that
/// builds: a `wff`, a `class`, a `setvar`, or a proof (`|-`).
///
/// A proof is built as steps that refer to their parts rather than copying
/// them. Written out in normal format, the intermediate value theorem's
/// proof is 63.6 million labels and only 3,030 distinct subproofs; built as
/// text it took gigabytes.
#[derive(Debug)]
pub struct Step {
    pub label: Symbol,
    pub kids: Vec<StepRef>,
    pub typecode: Symbol,
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
            out.push(step.label.as_str());
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
        self.items[self.items.len() - 1].label.as_str()
    }

    /// The same proof, resting also on `more`.
    pub fn resting(mut self, more: impl IntoIterator<Item = String>) -> Proof {
        self.origin.extend(more);
        self
    }
}

/// One part of a proof being built: labels as text or as tokens, or a
/// proof.
#[derive(Clone, Copy)]
pub enum Part<'a> {
    Text(&'a str),
    Tokens(&'a Rpn),
    Proof(&'a Proof),
}

impl<'a> From<&'a Rpn> for Part<'a> {
    fn from(rpn: &'a Rpn) -> Part<'a> {
        Part::Tokens(rpn)
    }
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

/// Tokens in order, from any mix of tokens and text:
/// `seq!(claim, th, pf, "a1i")`.
#[macro_export]
macro_rules! seq {
    ($($part:expr),* $(,)?) => {
        $crate::mm::Rpn::of(&[$(&$part as &dyn $crate::mm::Spell),*])
    };
}

// Terms. `co` is Metamath's binary operation and most of the rest are it
// with the operator filled in. Each takes tokens or text alike (`Spell`),
// so a term built inline is passed as it is.
pub fn co(a: impl Spell, b: impl Spell, f: impl Spell) -> Rpn {
    seq!(a, b, f, "co")
}
pub fn mul(a: impl Spell, b: impl Spell) -> Rpn {
    co(a, b, "cmul")
}
pub fn add(a: impl Spell, b: impl Spell) -> Rpn {
    co(a, b, "caddc")
}
pub fn sub(a: impl Spell, b: impl Spell) -> Rpn {
    co(a, b, "cmin")
}
pub fn div(a: impl Spell, b: impl Spell) -> Rpn {
    co(a, b, "cdiv")
}
pub fn exp(a: impl Spell, b: impl Spell) -> Rpn {
    co(a, b, "cexp")
}
pub fn fz(a: impl Spell, b: impl Spell) -> Rpn {
    co(a, b, "cfz")
}
pub fn neg(a: impl Spell) -> Rpn {
    seq!(a, "cneg")
}
pub fn summ(range: impl Spell, body: impl Spell, v: impl Spell) -> Rpn {
    seq!(range, body, v, "csu")
}

// Formulas.
pub fn cel(a: impl Spell, b: impl Spell) -> Rpn {
    seq!(a, b, "wcel")
}
pub fn br(a: impl Spell, b: impl Spell, r: impl Spell) -> Rpn {
    seq!(a, b, r, "wbr")
}
pub fn lt(a: impl Spell, b: impl Spell) -> Rpn {
    br(a, b, "clt")
}
pub fn le(a: impl Spell, b: impl Spell) -> Rpn {
    br(a, b, "cle")
}
pub fn dvds(a: impl Spell, b: impl Spell) -> Rpn {
    br(a, b, "cdvds")
}
pub fn eq(a: impl Spell, b: impl Spell) -> Rpn {
    seq!(a, b, "wceq")
}
pub fn ne(a: impl Spell, b: impl Spell) -> Rpn {
    seq!(a, b, "wne")
}
pub fn wa(a: impl Spell, b: impl Spell) -> Rpn {
    seq!(a, b, "wa")
}
pub fn wo(a: impl Spell, b: impl Spell) -> Rpn {
    seq!(a, b, "wo")
}
pub fn wi(a: impl Spell, b: impl Spell) -> Rpn {
    seq!(a, b, "wi")
}
pub fn wb(a: impl Spell, b: impl Spell) -> Rpn {
    seq!(a, b, "wb")
}
pub fn wn(a: impl Spell) -> Rpn {
    seq!(a, "wn")
}
pub fn w3a(a: impl Spell, b: impl Spell, c: impl Spell) -> Rpn {
    seq!(a, b, c, "w3a")
}
pub fn rex(body: impl Spell, v: impl Spell, over: impl Spell) -> Rpn {
    seq!(body, v, over, "wrex")
}

/// What a step binds each of its label's variables to, in reverse Polish.
pub type Binds = IndexMap<String, Rpn>;

/// A binding written out: `binds! { "ph" => t!(..), "A" => &term }`.
#[macro_export]
macro_rules! binds {
    ($($var:expr => $term:expr),* $(,)?) => {{
        #[allow(unused_mut)]
        let mut out = $crate::mm::spell::Binds::new();
        $(out.insert(String::from($var), $crate::mm::Rpn::spelt(&$term));)*
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
    /// The label, as the library holds it.
    label: Symbol,
    takes: usize,
    typecode: Symbol,
    kinds: Option<Vec<Symbol>>,
}

/// Statements in set.mm's notation, proofs in stack order.
pub struct Builder {
    pub sigs: Layered,
    syntax: OnceCell<Rc<Syntax>>,
    /// Each variable's float, shared so that a caller may hold it while it
    /// builds.
    pub flabel: Rc<FloatLabels>,
    /// How many labels there were when the builder was made: a label's
    /// place among those is the order floats are pushed in
    /// (`float_order`).
    ordered: usize,
    /// What a theorem of this corpus that a proof cites takes and states,
    /// where the library does not have it.
    pub arities: IndexMap<String, Signature>,
    arity_of: RefCell<FxIndexMap<Symbol, Taking>>,
    term_steps: RefCell<FxIndexMap<String, Vec<StepRef>>>,
    /// What each run of tokens that builds whole things of its own was
    /// built as (`read_tokens_onto`).
    token_steps: RefCell<FxIndexMap<Rpn, Vec<StepRef>>>,
    /// What each step built says, by the step (`says`).
    said: RefCell<FxIndexMap<usize, Said>>,
    /// What a step was built as that the kernel would refuse, oldest first,
    /// until the elaborator takes it (`fault`).
    faults: RefCell<Vec<String>>,
    /// Each token's print, worked out once (`Print::token`).
    prints: RefCell<rustc_hash::FxHashMap<Symbol, Print>>,
}

/// What one step says, kept by the step it was worked out for; the step is
/// held weakly, so a step dropped and its address reused is not taken for
/// another.
struct Said {
    step: std::rc::Weak<Step>,
    /// The expression after its typecode, or None where it rests on a label
    /// whose statement the builder does not have.
    says: Option<Print>,
}

/// An expression by its print: its tokens hashed as a polynomial, two ways,
/// and its length. Two expressions with one print are one expression but
/// for a collision of both hashes. A print of a term put into a statement
/// is worked out from the print of the term, so what a step says is held in
/// the same small space however long it is; kept as tokens, the statements
/// of the birthday problem's proof doubled the build's memory.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Print {
    hash: [u64; 2],
    len: u64,
}

/// 2^61 − 1, a prime, and the two bases the prints are taken in.
const MODULUS: u64 = (1 << 61) - 1;
const BASES: [u64; 2] = [1_000_003, 998_244_353];

fn mul_mod(a: u64, b: u64) -> u64 {
    ((u128::from(a) * u128::from(b)) % u128::from(MODULUS)) as u64
}

fn pow_mod(mut base: u64, mut exp: u64) -> u64 {
    let mut out = 1;
    while exp > 0 {
        if exp & 1 == 1 {
            out = mul_mod(out, base);
        }
        base = mul_mod(base, base);
        exp >>= 1;
    }
    out
}

impl Print {
    const EMPTY: Print = Print {
        hash: [0, 0],
        len: 0,
    };

    /// One token.
    fn token(text: &str) -> Print {
        use std::hash::{Hash, Hasher};
        let mut hash = [0; 2];
        for (n, h) in hash.iter_mut().enumerate() {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            (n, text).hash(&mut hasher);
            *h = hasher.finish() % MODULUS;
        }
        Print { hash, len: 1 }
    }

    /// This expression followed by `then`.
    fn then(self, then: Print) -> Print {
        let mut hash = [0; 2];
        for (n, h) in hash.iter_mut().enumerate() {
            let shifted = mul_mod(self.hash[n], pow_mod(BASES[n], then.len));
            *h = (shifted + then.hash[n]) % MODULUS;
        }
        Print {
            hash,
            len: self.len + then.len,
        }
    }
}

impl Builder {
    pub fn new(sigs: impl Into<Layered>) -> Builder {
        let sigs: Layered = sigs.into();
        let mut flabel = IndexMap::new();
        for (label, s) in sigs.iter() {
            if s.kind == Kind::Float {
                flabel.insert(s.statement[1], *label);
            }
        }
        let ordered = sigs.len();
        Builder {
            sigs,
            syntax: OnceCell::new(),
            flabel: Rc::new(FloatLabels::new(flabel)),
            ordered,
            arities: IndexMap::new(),
            arity_of: RefCell::new(FxIndexMap::default()),
            term_steps: RefCell::new(FxIndexMap::default()),
            token_steps: RefCell::new(FxIndexMap::default()),
            said: RefCell::new(FxIndexMap::default()),
            faults: RefCell::new(Vec::new()),
            prints: RefCell::new(rustc_hash::FxHashMap::default()),
        }
    }

    /// A token's print, worked out the first time it is asked.
    fn print_of(&self, token: Symbol) -> Print {
        if let Some(&found) = self.prints.borrow().get(&token) {
            return found;
        }
        let made = Print::token(token.as_str());
        self.prints.borrow_mut().insert(token, made);
        made
    }

    /// Where a label stands among those the builder was made with, the
    /// order floats are pushed in; None for a label added since, or none.
    pub fn float_order(&self, label: &str) -> Option<usize> {
        self.sigs.index_of(label).filter(|at| *at < self.ordered)
    }

    /// The first step of `proof` that the kernel would refuse, said; None
    /// where every label in it is applied as its statement says (`says`).
    ///
    /// A fault the verifier finds names only the theorem; asked of each
    /// line as it is kept, this names the line. Only what is kept is asked:
    /// a route may build a step, find it does not fit, and drop it.
    pub fn fault(&self, proof: &Proof) -> Option<String> {
        for step in &proof.items {
            self.says(step);
        }
        let mut faults = self.faults.borrow_mut();
        let first = faults.first().cloned();
        faults.clear();
        first
    }

    /// What the step proves or builds after its typecode, by its print,
    /// worked out from the statements of the labels it applies, as a
    /// verifier works it out. Each application is checked on the way: what
    /// it is handed for each essential hypothesis proves that hypothesis,
    /// and no two variables it keeps apart (`$d`) are given terms sharing a
    /// variable. A step that is not is a fault (`fault`). None where the
    /// step rests on a label whose statement the builder does not have
    /// (`stated`).
    ///
    /// Steps are shared, so each is worked out once; and worked out without
    /// recursion, since a proof runs deeper than a stack.
    fn says(&self, root: &StepRef) -> Option<Print> {
        let key = |s: &StepRef| Rc::as_ptr(s) as usize;
        let known = |s: &StepRef| -> Option<Option<Print>> {
            let said = self.said.borrow();
            let entry = said.get(&key(s))?;
            let same = entry
                .step
                .upgrade()
                .is_some_and(|held| Rc::ptr_eq(&held, s));
            same.then_some(entry.says)
        };
        let mut work: Vec<(StepRef, bool)> = vec![(root.clone(), false)];
        while let Some((step, ready)) = work.pop() {
            if known(&step).is_some() {
                continue;
            }
            if !ready {
                work.push((step.clone(), true));
                for kid in step.kids.iter().rev() {
                    if known(kid).is_none() {
                        work.push((kid.clone(), false));
                    }
                }
                continue;
            }
            let kids: Option<Vec<Print>> =
                step.kids.iter().map(|k| known(k).flatten()).collect();
            let says = kids.and_then(|kids| self.applied(&step, &kids));
            self.said.borrow_mut().insert(
                key(&step),
                Said {
                    step: Rc::downgrade(&step),
                    says,
                },
            );
        }
        known(root).flatten()
    }

    /// What `step` says after its typecode, from what its kids say, and
    /// each fault in the application recorded.
    fn applied(&self, step: &Step, kids: &[Print]) -> Option<Print> {
        let sig = self.stated(&step.label)?;
        if kids.len() != sig.floats.len() + sig.essentials.len() {
            return None;
        }
        let (floats, essentials) = kids.split_at(sig.floats.len());
        let put: FxIndexMap<Symbol, Print> = sig
            .floats
            .iter()
            .zip(floats)
            .map(|(&(_, var), kid)| (var, *kid))
            .collect();
        let filled = |tokens: &[Symbol]| -> Print {
            tokens.iter().fold(Print::EMPTY, |out, t| {
                out.then(put.get(t).copied().unwrap_or_else(|| self.print_of(*t)))
            })
        };
        let given = &step.kids[sig.floats.len()..];
        for (n, ((asked, print), kid)) in
            sig.essentials.iter().zip(essentials).zip(given).enumerate()
        {
            if asked[0] != kid.typecode || filled(&asked[1..]) != *print {
                let floats = &step.kids[..sig.floats.len()];
                self.faults.borrow_mut().push(format!(
                    "{} asks in its hypothesis {} for {} and is handed a proof of {}",
                    step.label,
                    n + 1,
                    shortened(&self.filled_text(sig, floats, asked)),
                    shortened(&self.spelt_statement(kid).unwrap_or_default())
                ));
            }
        }
        for &(x, y) in &sig.disjoint {
            let at = |v: Symbol| sig.floats.iter().position(|&(_, f)| f == v);
            let (Some(a), Some(b)) = (at(x), at(y)) else {
                continue;
            };
            let theirs = self.variables(&step.kids[b]);
            let shared = self
                .variables(&step.kids[a])
                .into_iter()
                .find(|v| theirs.contains(v));
            if let Some(v) = shared {
                self.faults.borrow_mut().push(format!(
                    "{} keeps {x} and {y} apart and is given {v} in both",
                    step.label
                ));
            }
        }
        Some(filled(&sig.statement[1..]))
    }

    /// The variables a term's steps write: those of the floats it rests on.
    fn variables(&self, term: &Step) -> BTreeSet<Symbol> {
        let mut out = BTreeSet::new();
        let mut work = vec![term];
        while let Some(step) = work.pop() {
            match self.sigs.get(&step.label) {
                Some(sig) if sig.kind == Kind::Float => {
                    out.insert(sig.statement[1]);
                }
                _ => work.extend(step.kids.iter().map(|k| &**k)),
            }
        }
        out
    }

    /// A label's statement, or one of its hypotheses, with the terms of
    /// `floats` put for its variables, as text: for a message.
    fn filled_text(
        &self,
        sig: &Signature,
        floats: &[StepRef],
        tokens: &[Symbol],
    ) -> Vec<String> {
        let mut out = Vec::new();
        for t in tokens {
            match sig.floats.iter().position(|(_, v)| v == t) {
                Some(n) => match self.spelt_statement(&floats[n]) {
                    Some(term) => out.extend(term.into_iter().skip(1)),
                    None => out.push(t.to_string()),
                },
                None => out.push(t.to_string()),
            }
        }
        out
    }

    /// The signature a label is applied by: the library's, or for a theorem
    /// of the corpus cited from another file, the one its citation records
    /// (`arities`). None where the builder has neither.
    fn stated(&self, label: &str) -> Option<&Signature> {
        self.sigs.get(label).or_else(|| self.arities.get(label))
    }

    /// What a step says, as text, its typecode first: for a message. None
    /// where it rests on a label whose statement the builder does not have.
    fn spelt_statement(&self, step: &Step) -> Option<Vec<String>> {
        let sig = self.stated(&step.label)?;
        let floats = step.kids.get(..sig.floats.len())?;
        Some(self.filled_text(sig, floats, &sig.statement))
    }

    /// set.mm's syntax axioms, built the first time one is parsed unless
    /// one has been handed over (`share_syntax`).
    pub fn syntax(&self) -> &Syntax {
        self.syntax.get_or_init(|| Rc::new(Syntax::new(&self.sigs)))
    }

    /// Parse with a syntax built once for many builders, and the statements
    /// it has read already. It must be the syntax these signatures give,
    /// which is the caller's to know; a builder that has parsed already
    /// keeps its own.
    pub fn share_syntax(&self, syntax: Rc<Syntax>) {
        let _ = self.syntax.set(syntax);
    }

    /// Register a lemma this file proves, so a later one may apply it.
    pub fn define(&mut self, label: &str, statement: &str) {
        self.define_with_hyps(label, statement, &[]);
    }

    /// Register a lemma stated as a deduction, with the hypotheses it takes
    /// in order. Its variables are those of the statement and the
    /// hypotheses together, as `proved` writes them.
    pub fn define_with_hyps(&mut self, label: &str, statement: &str, hyps: &[&str]) {
        let tokens: Vec<Symbol> =
            statement.split_whitespace().map(Symbol::of).collect();
        let essentials: Vec<Vec<Symbol>> = hyps
            .iter()
            .map(|h| h.split_whitespace().map(Symbol::of).collect())
            .collect();
        let mut free: Vec<Symbol> = tokens
            .iter()
            .chain(essentials.iter().flatten())
            .filter(|t| self.flabel.contains(t))
            .copied()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        free.sort_by_key(|v| {
            self.float_order(self.flabel.get(v).unwrap().as_str())
                .unwrap_or(usize::MAX)
        });
        let floats = free
            .iter()
            .map(|&v| {
                let float = &self.sigs[self.flabel.get(&v).unwrap().as_str()];
                (float.statement[0], v)
            })
            .collect();
        let label = Symbol::of(label);
        self.sigs.insert(
            label,
            Signature {
                label,
                kind: Kind::Theorem,
                statement: tokens,
                floats,
                essentials,
                disjoint: BTreeSet::new(),
            },
        );
    }

    /// Register a hypothesis a lemma of this file states, so its proof may
    /// rest on it: a step taking nothing and giving the statement.
    pub fn hypothesis(&mut self, label: &str, statement: &str) {
        let label = Symbol::of(label);
        self.sigs.insert(
            label,
            Signature {
                label,
                kind: Kind::Essential,
                statement: statement.split_whitespace().map(Symbol::of).collect(),
                floats: Vec::new(),
                essentials: Vec::new(),
                disjoint: BTreeSet::new(),
            },
        );
    }

    /// The label that pushes a variable: its floating hypothesis.
    pub fn float(&self, var: &str) -> String {
        self.flabel
            .get(var)
            .unwrap_or_else(|| panic!("no float for {var}"))
            .to_string()
    }

    /// A proof that is one label taking nothing: a hypothesis, or a closed
    /// lemma such as `1z`.
    pub fn step(&self, label: &str) -> Proof {
        self.proof(&[Part::Text(label)])
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
        let pushed: Vec<Rpn> = sig
            .floats
            .iter()
            .map(|(_, var)| match binds.get(var.as_str()) {
                Some(t) => t.clone(),
                None => Rpn::from(self.flabel.get(var).into_iter().collect::<Vec<_>>()),
            })
            .collect();
        let mut parts: Vec<Part> = pushed.iter().map(Part::from).collect();
        parts.extend(essentials.iter().map(|p| Part::Proof(p)));
        parts.push(Part::Text(label));
        self.proof(&parts)
    }

    /// Whether reverse Polish ending in this label is a proof: the label's
    /// statement is set.mm's `|-`.
    pub fn proves(&self, label: &str) -> bool {
        self.sigs
            .get(label)
            .is_some_and(|s| s.statement.first().is_some_and(|t| *t == "|-"))
    }

    /// A proof, from labels and proofs in order: resting on what its parts
    /// rest on. Each part is checked against what its label takes, so a
    /// proof handed where a class belongs is refused at the call that made
    /// it, and not by the verifier later.
    pub fn proof(&self, parts: &[Part]) -> Proof {
        let parts: Vec<Part> = parts
            .iter()
            .copied()
            .filter(|p| match p {
                Part::Text(t) => !t.is_empty(),
                Part::Tokens(r) => !r.is_empty(),
                Part::Proof(_) => true,
            })
            .collect();
        let end = match parts.last() {
            Some(Part::Proof(p)) => p.last().to_string(),
            Some(Part::Text(t)) => t.rsplit(' ').next().unwrap_or("").to_string(),
            Some(Part::Tokens(r)) => r.last().map(String::from).unwrap_or_default(),
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
                Part::Tokens(r) => self.read_tokens_onto(r, &mut stack),
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
        let low =
            self.applied_onto(text.split_whitespace(), stack, &|| text.to_string());
        if low >= base {
            self.term_steps
                .borrow_mut()
                .insert(text.to_string(), stack[base..].to_vec());
        }
    }

    /// The labels of `rpn` applied onto `stack`, as `read_onto` applies
    /// text's, and kept as it keeps them.
    fn read_tokens_onto(&self, rpn: &Rpn, stack: &mut Vec<StepRef>) {
        if let Some(known) = self.token_steps.borrow().get(rpn) {
            stack.extend(known.iter().cloned());
            return;
        }
        let base = stack.len();
        let labels = rpn.tokens().iter().map(|t| t.as_str());
        let low = self.applied_onto(labels, stack, &|| rpn.to_string());
        if low >= base {
            self.token_steps
                .borrow_mut()
                .insert(rpn.clone(), stack[base..].to_vec());
        }
    }

    /// Each label applied in turn onto `stack`, checked against what it
    /// takes; `written` says what was being read, for a message. The lowest
    /// the stack fell while they were applied.
    fn applied_onto<'t>(
        &self,
        labels: impl Iterator<Item = &'t str>,
        stack: &mut Vec<StepRef>,
        written: &dyn Fn() -> String,
    ) -> usize {
        let mut low = stack.len();
        for label in labels {
            let taking = self.taking(label);
            if stack.len() < taking.takes {
                panic!(
                    "{label} takes {} things and has {}: …{}",
                    taking.takes,
                    stack.len(),
                    tail(&written(), 60)
                );
            }
            let kids: Vec<StepRef> = stack.split_off(stack.len() - taking.takes);
            if let Some(kinds) = &taking.kinds {
                for (n, (kid, kind)) in kids.iter().zip(kinds).enumerate() {
                    if kid.typecode != *kind {
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
                label: taking.label,
                kids,
                typecode: taking.typecode,
            }));
        }
        low
    }

    fn taking(&self, label: &str) -> Taking {
        if let Some(found) = self.arity_of.borrow().get(label) {
            return found.clone();
        }
        let found = match self.sigs.get(label) {
            Some(sig) => {
                let mut kinds: Vec<Symbol> =
                    sig.floats.iter().map(|&(t, _)| t).collect();
                kinds.extend(std::iter::repeat_n(
                    Symbol::of("|-"),
                    sig.essentials.len(),
                ));
                Taking {
                    label: sig.label,
                    takes: kinds.len(),
                    typecode: sig.statement[0],
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
                    label: sig.label,
                    takes: sig.floats.len() + sig.essentials.len(),
                    typecode: sig.statement[0],
                    kinds: None,
                }
            }
        };
        self.arity_of
            .borrow_mut()
            .insert(found.label, found.clone());
        found
    }
}

/// A statement as a message prints it: its first 200 characters.
fn shortened(tokens: &[String]) -> String {
    let text = tokens.join(" ");
    match text.char_indices().nth(200) {
        Some((at, _)) => format!("{} …", &text[..at]),
        None => text,
    }
}

/// The last `n` characters of a text, for a message.
fn tail(text: &str, n: usize) -> String {
    let chars: Vec<char> = text.chars().collect();
    chars[chars.len().saturating_sub(n)..].iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mm::library::read_texts;

    /// A database small enough to read: implication, modus ponens, three
    /// axioms to hand it, and one that keeps two set variables apart.
    fn builder() -> Builder {
        Builder::new(read_texts(&["
            $c wff setvar |- ( -> ) = $.
            $v ph ps x y $.
            wph $f wff ph $. wps $f wff ps $.
            vx $f setvar x $. vy $f setvar y $.
            wi $a wff ( ph -> ps ) $.
            weq $a wff x = y $.
            ${ mp.1 $e |- ph $. mp.2 $e |- ( ph -> ps ) $. ax-mp $a |- ps $. $}
            a1 $a |- ph $.
            a2 $a |- ( ph -> ps ) $.
            a3 $a |- ( ps -> ph ) $.
            ${ $d x y $. apart $a |- x = y $. $}
        "]))
    }

    #[test]
    fn a_label_applied_as_its_statement_says_is_no_fault() {
        let b = builder();
        let ph = b.ap("a1", &binds! {"ph" => "wph"}, &[]);
        let imp = b.ap("a2", &binds! {"ph" => "wph", "ps" => "wps"}, &[]);
        let proof = b.ap(
            "ax-mp",
            &binds! {"ph" => "wph", "ps" => "wps"},
            &[&ph, &imp],
        );
        assert_eq!(b.fault(&proof), None);
        let apart = b.ap("apart", &binds! {"x" => "vx", "y" => "vy"}, &[]);
        assert_eq!(b.fault(&apart), None);
    }

    #[test]
    fn a_hypothesis_handed_another_statement_is_a_fault() {
        let b = builder();
        let ph = b.ap("a1", &binds! {"ph" => "wph"}, &[]);
        let turned = b.ap("a3", &binds! {"ph" => "wph", "ps" => "wps"}, &[]);
        let proof = b.ap(
            "ax-mp",
            &binds! {"ph" => "wph", "ps" => "wps"},
            &[&ph, &turned],
        );
        assert_eq!(
            b.fault(&proof).as_deref(),
            Some("ax-mp asks in its hypothesis 2 for |- ( ph -> ps ) and is handed a proof of |- ( ps -> ph )")
        );
    }

    #[test]
    fn variables_kept_apart_given_one_letter_are_a_fault() {
        let b = builder();
        let same = b.ap("apart", &binds! {"x" => "vx", "y" => "vx"}, &[]);
        assert_eq!(
            b.fault(&same).as_deref(),
            Some("apart keeps x and y apart and is given x in both")
        );
    }
}
