//! What the elaborator holds while it works on one theorem.
//!
//! The elaborator is seven parts that share some fifty fields. The fields
//! are one struct, and each part is an `impl` block in a module of its own:
//! reading, scopes, provenance, tables, the matcher, the calculators, and
//! the step loop in `elaborate`. What the whole corpus shares —
//! the grammar, the database, set.mm — is borrowed; what belongs to this
//! theorem is owned, and goes when the theorem is written.

use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use super::{Facts, Lines};
use crate::corpus::{written_text, FileScope, Item, Record, Step, Theorem};
use crate::fancy;
use crate::formula::{Grammar, Node, Sorts};
use crate::matching::{binding_context, equations, Defined};
use crate::mm::kernel::{match_term, term_of, FloatLabels, Term, VarSet};
use crate::mm::library::{render, Layered, Signature};
use crate::mm::spell::{Binds, Builder, Proof};
use crate::outcome::{Checked, Decline, Problem, Route};
use crate::targets::{self, Commuting};

/// Variables for a name the proof does not spell: what a `define` renames
/// its body's binders to, and what an `obtain` introduces. A name the text
/// does spell keeps its own letter, so this holds what a reader is least
/// likely to write. After them come the letters readers write most, which a
/// proof spelling them never draws, and last set.mm's primed and
/// double-primed setvars, which no reader writes: Lagrange's theorem spells
/// fifteen letters and fixes some twenty names in its blocks.
pub const SPARE_VARS: [&str; 72] = [
    "vm", "vk", "vj", "vi", "vp", "vq", "vr", "vs", "vt", "vu", "vo", "vl", "vg", "vh",
    "vf", "vw", "vv", "ve", "vd", "vc", "vb", "va", "vn", "vz", "vy", "vx", "bnjvam",
    "bnjvbm", "bnjvcm", "bnjvdm", "bnjvem", "bnjvfm", "bnjvgm", "bnjvhm", "bnjvim",
    "bnjvjm", "bnjvkm", "bnjvlm", "bnjvmm", "bnjvnm", "bnjvpm", "bnjvqm", "bnjvrm",
    "bnjvtm", "bnjvum", "bnjvwm", "bnjvxm", "bnjvym", "bnjvzm", "bnjvan", "bnjvbn",
    "bnjvcn", "bnjvdn", "bnjven", "bnjvfn", "bnjvgn", "bnjvhn", "bnjvin", "bnjvjn",
    "bnjvkn", "bnjvln", "bnjvmn", "bnjvnn", "bnjvpn", "bnjvqn", "bnjvrn", "bnjvtn",
    "bnjvun", "bnjvwn", "bnjvxn", "bnjvyn", "bnjvzn",
];

// A letter standing alone as a name, as `k` does in `Σ(k = 0 to m)`, and not
// inside a word such as `calculation`.
fancy!(LETTER, r"(?<![A-Za-z])[A-Za-z](?![A-Za-z])");

/// A kernel term's variables and what each stands for.
pub type Binding = IndexMap<String, Term>;

/// The variables a lemma's statement mentions, which a match may bind.
pub type Vars = BTreeSet<Rc<str>>;

/// One scope frame: the scope with an assumption conjoined, the assumption,
/// and what is known there.
#[derive(Clone)]
pub struct Frame {
    pub scope: String,
    pub added: Option<String>,
    pub facts: Facts,
}

/// A shape a `target` pattern reads as, so a rewrite can walk down it.
#[derive(Clone, Debug)]
pub enum Shape {
    Hole(usize),
    Const(String),
    /// A constructor, the operation it wraps where that is a constant, and
    /// its arguments.
    App(String, Option<String>, Vec<Shape>),
}

/// What a scope a step opened discharges into where the scope ends.
#[derive(Clone)]
pub enum Closer {
    /// An `obtain`'s existential, eliminated around the goal.
    Obtain(Rc<ObtainCloser>),
    /// A `define`'s equation, eliminated around the goal.
    Define(Rc<DefineCloser>),
}

pub struct ObtainCloser {
    pub line: usize,
    pub scope: String,
    pub ex: String,
    pub p_ex: Proof,
    pub body: String,
    pub outer: String,
    pub inner: String,
    pub pushed: Vec<String>,
    pub layers: Vec<(String, String)>,
    pub discharge: &'static str,
}

pub struct DefineCloser {
    pub scope: String,
    pub said: String,
    pub var: String,
    pub ex: String,
    pub p_ex: Proof,
    pub line: usize,
    pub label: String,
}

/// A block being elaborated: what it opened over and what it opened.
pub struct Block {
    pub owner: Step,
    pub outer: String,
    pub outside: Facts,
    /// Index into the scope frames.
    pub frame: usize,
    pub scope: String,
    pub facts: Facts,
    /// A contradiction's supposition.
    pub supposed: Option<String>,
    /// An induction's name and spare.
    pub over: Option<String>,
    pub base: Option<String>,
    /// The setvar a fix introduced.
    pub variable: Option<String>,
    /// The names in hand before it opened, and which variable each binder
    /// had; and which each had while it was open.
    pub named: IndexMap<String, String>,
    pub bound: IndexMap<String, String>,
    pub inner: IndexMap<String, String>,
    /// Cases: part number -> what it assumes, and its label.
    pub assumed: IndexMap<usize, (Node, String)>,
    pub entered: Option<usize>,
    pub case_opened_at: Option<usize>,
    pub opened_at: usize,
    pub claim: String,
    pub proof: Option<Proof>,
    /// Part number -> the last fact in it: claim, proof, and the scope it was
    /// proved under.
    pub parts: IndexMap<usize, (String, Proof, String)>,
}

/// What a lemma is for, read off what it states.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    /// Takes a thing in one number system to another.
    Carrier,
    /// Any other side condition.
    Side,
}

/// Each declared lemma, with what its readings forwards and backwards can end
/// on, and its role.
pub type LemmaIndex = IndexMap<String, ([IndexSet<HeadKey>; 2], Role)>;

/// How a lemma's conclusion constrains what it can match.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum HeadKey {
    Any,
    Member(String),
    Head(String),
}

pub struct Elaborator<'a> {
    pub thm: &'a Theorem,
    pub g: &'a Grammar,
    pub items: &'a IndexMap<String, Item<'a>>,
    pub records: &'a [Record],
    pub scopes: &'a [FileScope],
    /// The sort of each name, as the grammar reads it now.
    pub sorts_now: Sorts,
    pub b: Builder,
    pub terms: IndexMap<String, Vec<Option<String>>>,
    pub equations: IndexSet<String>,
    /// Letters the notations' own targets bind and the proof writes.
    pub taken: IndexSet<String>,
    pub spare: Vec<String>,
    pub commutes: Vec<Commuting>,
    /// Corpus theorems this proof leans on.
    pub cited: Vec<String>,
    /// What the last step of the contradiction block being elaborated
    /// contradicts, which the block closes on with that step's own line.
    pub contradicted: Option<String>,
    /// Whether the step being elaborated sits directly inside a
    /// contradiction.
    pub in_contradiction: bool,
    pub shapes: IndexMap<String, Shape>,
    /// Where the elaborator has got to, for whatever it reads there.
    pub at: usize,
    /// Readable name -> kernel term.
    pub names: IndexMap<String, String>,
    /// Readable name -> the set it was let into.
    pub sets: IndexMap<String, String>,
    /// (label, statement) for each statement taken as stated.
    pub axioms: Vec<(String, String)>,
    /// Setvars the conclusion quantifies over.
    pub reserved: IndexSet<String>,
    /// Map -> its rule spelt apart (`rule_apart`).
    pub rules_read: IndexMap<String, Term>,
    /// `requires` terms being discharged now.
    pub supplying: IndexSet<String>,
    /// By page item, what its proof was built on.
    pub rests_on: IndexMap<String, BTreeSet<String>>,
    /// (from system, to system) -> one lemma.
    pub bridges: Option<IndexMap<(String, String), String>>,
    /// Declared lemma -> what its readings end on, and its role.
    pub lemma_heads: Option<LemmaIndex>,
    /// Term and bound letters -> its standard form.
    pub standards: IndexMap<(String, Vars), Term>,
    /// Whether the facts are being read in standard form, so that the
    /// comparisons the reading makes are offered the facts as they stand.
    pub reading_facts: bool,
    /// The rules of the standard form set.mm has, plain and conditional,
    /// read once.
    pub rewrite_rules: Option<[Vec<super::matcher::Rewrite>; 2]>,
    /// Letters `same` reads as blanks.
    pub binding: Vars,
    /// The lines what is being proved cites, in the order it writes them.
    pub citing: IndexSet<String>,
    /// What the proof being built may rest on.
    pub resting: Option<BTreeSet<String>>,
    /// By step line, what its method combined.
    pub combined: IndexMap<usize, IndexSet<String>>,
    /// Labels of sort lines and `define` lines.
    pub sorts: BTreeSet<String>,
    /// Side conditions the step being proved wrote, with the scope each was
    /// proved under.
    pub written: IndexMap<String, (String, Proof)>,
    pub saying: IndexSet<String>,
    pub rewriting: IndexSet<String>,
    pub numbering: IndexSet<String>,
    /// (membership, scope) -> what it came to.
    pub numbers: IndexMap<(String, String), Route<Proof>>,
    /// Binder name -> the setvar it stands for, and back.
    pub bound_as: IndexMap<String, String>,
    pub written_as: IndexMap<String, String>,
    /// Statement -> how it is pushed, stated once.
    pub assumed: IndexMap<String, Proof>,
    /// How far down the `define` lines we have read.
    pub unread: usize,
    /// A defined name's setvar -> the term it names.
    pub definitions: IndexMap<String, String>,
    /// Name -> tree, while a statement is read.
    pub from_outside: IndexMap<String, Defined>,
    /// A define by recursion: its label -> each name's map; its seq term ->
    /// (step, start, how many names); and while a step rule is read, each
    /// name -> its part of the state.
    pub recursion_maps: IndexMap<String, IndexMap<String, String>>,
    pub recursions: IndexMap<String, (String, String, usize)>,
    pub recurring: IndexMap<String, String>,
    pub file_given: bool,
    pub last: Option<String>,
    /// The scope frames, innermost last.
    pub frames: Vec<Frame>,
    pub lines: Lines,
    /// Notation -> the literals of its patterns, in the order the `pattern`
    /// and `target` fields both use.
    pub literals: IndexMap<String, Vec<String>>,
    /// Notation -> the holes each binder introduces a name in.
    pub binders: IndexMap<String, Vec<usize>>,
    /// The statement a cited theorem's file proves, where it is known.
    pub statements: &'a dyn Fn(&str) -> Option<String>,
    /// Whether the search is offered every fact in scope (`Options`).
    pub whole_scope: bool,
}

impl<'a> Elaborator<'a> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        thm: &'a Theorem,
        g: &'a Grammar,
        items: &'a IndexMap<String, Item<'a>>,
        sigs: Layered,
        records: &'a [Record],
        scopes: &'a [FileScope],
        sorts_now: Sorts,
        statements: &'a dyn Fn(&str) -> Option<String>,
    ) -> Elaborator<'a> {
        let b = Builder::new(sigs);
        let terms = targets::terms(records);
        let mut taken: IndexSet<String> = IndexSet::new();
        for entries in terms.values() {
            for e in entries.iter().flatten() {
                for t in e.split_whitespace() {
                    taken.insert(t.to_string());
                }
            }
        }
        let text = written_text(thm);
        for m in LETTER.find_iter(&text).flatten() {
            if let Some(label) = b.flabel.get(m.as_str()) {
                taken.insert(label.clone());
            }
        }
        let spare = SPARE_VARS
            .iter()
            .filter(|v| !taken.contains(**v))
            .map(|v| v.to_string())
            .collect();
        let mut literals: IndexMap<String, Vec<String>> = IndexMap::new();
        for n in &g.notations {
            literals
                .entry(n.name.clone())
                .or_default()
                .push(n.literal.clone());
        }
        let binders = binding_context(&g.notations)
            .0
            .into_iter()
            .map(|(name, b)| (name, b.held))
            .collect();
        Elaborator {
            thm,
            g,
            items,
            records,
            scopes,
            sorts_now,
            b,
            equations: equations(records),
            taken,
            spare,
            commutes: targets::commuting(records),
            cited: Vec::new(),
            contradicted: None,
            in_contradiction: false,
            shapes: IndexMap::new(),
            at: thm.line,
            names: IndexMap::new(),
            sets: IndexMap::new(),
            axioms: Vec::new(),
            reserved: IndexSet::new(),
            rules_read: IndexMap::new(),
            supplying: IndexSet::new(),
            rests_on: IndexMap::new(),
            bridges: None,
            lemma_heads: None,
            standards: IndexMap::new(),
            reading_facts: false,
            rewrite_rules: None,
            binding: Vars::new(),
            citing: IndexSet::new(),
            resting: None,
            combined: IndexMap::new(),
            sorts: BTreeSet::new(),
            written: IndexMap::new(),
            saying: IndexSet::new(),
            rewriting: IndexSet::new(),
            numbering: IndexSet::new(),
            numbers: IndexMap::new(),
            bound_as: IndexMap::new(),
            written_as: IndexMap::new(),
            assumed: IndexMap::new(),
            unread: 0,
            definitions: IndexMap::new(),
            from_outside: IndexMap::new(),
            recursion_maps: IndexMap::new(),
            recursions: IndexMap::new(),
            recurring: IndexMap::new(),
            file_given: false,
            last: None,
            frames: Vec::new(),
            lines: Lines::new(),
            literals,
            binders,
            terms,
            statements,
            whole_scope: false,
        }
    }

    /// Something a person has to fix, and where in the proof it is: every
    /// defect raised here is a place in the text this elaborator is reading,
    /// in the file the theorem was read from.
    pub fn defect(&self, line: usize, message: impl Into<String>) -> Problem {
        Problem::new(&self.thm.path, line, message)
    }

    /// This route does not apply, and why, in the terms as they stand. The
    /// words are put together only if something reads them.
    pub fn no<T>(
        &self,
        shape: impl Into<std::borrow::Cow<'static, str>>,
        terms: &[&str],
    ) -> Route<T> {
        Route::Declined(Decline::shaped(
            shape,
            terms.iter().map(|t| t.to_string()).collect(),
        ))
    }

    /// A decline's reason, with its terms written as a Metamath file writes
    /// them.
    pub fn say(&self, decline: &Decline) -> String {
        decline.render(|t| self.render(t))
    }

    /// A term written the way a Metamath file writes it.
    pub fn render(&self, rpn: &str) -> String {
        render(rpn, &self.b.sigs)
    }

    pub fn flabel(&self) -> &FloatLabels {
        &self.b.flabel
    }

    /// The label of a variable's float, or the name itself where it has none.
    pub fn float_of(&self, var: &str) -> String {
        self.b
            .flabel
            .get(var)
            .cloned()
            .unwrap_or_else(|| var.to_string())
    }

    /// A term the proof holds, read back as a tree.
    pub fn to_term(&self, rpn: &str) -> Term {
        term_of(rpn, &self.b.sigs)
    }

    /// A term as a proof spells it.
    pub fn rpn(&self, term: &Term) -> String {
        term.rpn(&self.b.flabel).to_string()
    }

    pub fn sig(&self, label: &str) -> &Signature {
        self.b
            .sigs
            .get(label)
            .unwrap_or_else(|| panic!("no label {label} in the library"))
    }

    /// The typecode of what a label builds.
    pub fn typecode(&self, label: &str) -> &str {
        &self.sig(label).statement[0]
    }

    /// Whether a label is a set variable's float.
    pub fn is_setvar(&self, label: &str) -> bool {
        self.b
            .sigs
            .get(label)
            .is_some_and(|s| s.statement[0] == "setvar")
    }

    /// What a labelled statement claims, as a term.
    pub fn statement(&self, label: &str) -> Term {
        let sig = self.sig(label);
        self.b
            .syntax()
            .statement(sig)
            .unwrap_or_else(|p| panic!("{label} does not parse: {p}"))
    }

    /// An essential hypothesis's claim, as a term.
    pub fn essential(&self, tokens: &[String]) -> Term {
        let words: Vec<&str> = tokens[1..].iter().map(String::as_str).collect();
        self.b
            .syntax()
            .parse(&words, "wff")
            .unwrap_or_else(|p| panic!("{words:?} does not parse: {p}"))
    }

    /// A binding of kernel terms, as the strings `ap` wants pushed.
    pub fn spelt(&self, binding: &Binding) -> Binds {
        binding
            .iter()
            .map(|(v, t)| (v.clone(), self.rpn(t)))
            .collect()
    }

    /// The set variable a setvar's label stands for, as a term.
    pub fn var_of(&self, label: &str) -> Term {
        Term::var(&self.sig(label).statement[1])
    }

    /// The setvar labels every name the proof holds as `x cv` stands for.
    pub fn names_held(&self) -> IndexSet<String> {
        self.names
            .values()
            .filter(|t| t.ends_with(" cv"))
            .filter_map(|t| t.split(' ').next().map(String::from))
            .collect()
    }

    /// A proof that is one label taking nothing.
    pub fn step(&self, label: &str) -> Proof {
        self.b.step(label)
    }
}

/// Bind the pattern's variables so that it becomes the ground term.
pub fn fit<V: VarSet + ?Sized>(
    pattern: &Term,
    ground: &Term,
    binding: &Binding,
    variables: &V,
) -> Option<Binding> {
    match_term(pattern, ground, binding, variables)
}

/// `fit` up to the letters a lemma was given of its own: `fresh` stands for
/// the lemma's bound variables as the lemma is applied, and a fact binds its
/// own letters there, so the pattern is fitted with those left open, what it
/// says of every other variable is kept, and the fresh letters stay.
pub fn fit_respelt<V: VarSet + ?Sized>(
    pattern: &Term,
    ground: &Term,
    binding: &Binding,
    variables: &V,
    fresh: &Binding,
) -> Option<Binding> {
    if fresh.is_empty() {
        return fit(pattern, ground, binding, variables);
    }
    let mut open = binding.clone();
    for k in fresh.keys() {
        open.shift_remove(k);
    }
    let filled = fit(pattern, ground, &open, variables)?;
    let mut out = binding.clone();
    for (k, v) in filled {
        if !fresh.contains_key(&k) {
            out.entry(k).or_insert(v);
        }
    }
    Some(out)
}

/// The variables a term mentions, as a set a match may bind.
pub fn names_of(term: &Term) -> Vars {
    (*term.names()).clone()
}

/// The steps of a block, as their numbers are written.
pub fn number_of(step: &Step) -> String {
    step.number
        .0
        .iter()
        .map(|p| p.to_string())
        .collect::<Vec<_>>()
        .join(".")
}

/// What was built, or a defect at `line` in the file being elaborated.
pub fn built_or<T>(
    route: Route<T>,
    el: &Elaborator,
    line: usize,
    message: impl FnOnce(&Decline) -> String,
) -> Checked<T> {
    match route {
        Route::Built(t) => Ok(t),
        Route::Declined(d) => Err(el.defect(line, message(&d))),
    }
}
