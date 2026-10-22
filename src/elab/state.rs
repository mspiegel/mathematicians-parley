//! What the elaborator holds while it works on one theorem.
//!
//! The elaborator is seven parts that share some fifty fields. The fields
//! are one struct, and each part is an `impl` block in a module of its own:
//! reading, scopes, provenance, tables, the matcher, the calculators, and
//! the step loop in `elaborate`. What the whole corpus shares —
//! the grammar, the database, set.mm — is borrowed; what belongs to this
//! theorem is owned, and goes when the theorem is written.

use std::cell::{OnceCell, RefCell};
use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use super::{Facts, Lines, Written};
use crate::checker::record::CheckedTheorem;
use crate::checker::LibraryReading;
use crate::citing;
use crate::corpus::{written_text, FileScope, Item, Record, Step, Theorem};
use crate::formula::notation_id::{LiteralId, NotationId, Spelling};
use crate::formula::symbol::Symbol;
use crate::formula::{Grammar, Node, Sorts};
use crate::matching::{binding_context, Defined, FxIndexMap};
use crate::mm::kernel::{match_term, term_of, FloatLabels, Term, VarSet};
use crate::mm::library::{render, Layered, Signature};
use crate::mm::spell::{Binds, Builder, Proof};
use crate::mm::Rpn;
use crate::outcome::{Decline, Problem, Route};
use crate::sorts::Env;
use crate::targets::{self, Commuting, Identity};

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

/// Every letter standing alone as a name in `text`, as `k` does in `Σ(k =
/// 0 to m)`, and not inside a word such as `calculation`.
fn lone_letters(text: &str) -> Vec<String> {
    let chars: Vec<char> = text.chars().collect();
    (0..chars.len())
        .filter(|&i| {
            letter_at(&chars, i)
                && !(i > 0 && letter_at(&chars, i - 1))
                && !letter_at(&chars, i + 1)
        })
        .map(|i| chars[i].to_string())
        .collect()
}

/// Whether the character at `i` is a Latin letter.
fn letter_at(chars: &[char], i: usize) -> bool {
    chars.get(i).is_some_and(char::is_ascii_alphabetic)
}

/// A kernel term's variables and what each stands for.
pub type Binding = IndexMap<Symbol, Term>;

/// The variables a lemma's statement mentions, which a match may bind.
pub type Vars = BTreeSet<Symbol>;

/// One scope frame: the scope with an assumption conjoined, the assumption,
/// and what is known there.
#[derive(Clone)]
pub struct Frame {
    pub scope: Rpn,
    pub added: Option<Rpn>,
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
    pub scope: Rpn,
    pub ex: Rpn,
    pub p_ex: Proof,
    pub body: Rpn,
    pub outer: Rpn,
    pub inner: Rpn,
    pub pushed: Vec<Rpn>,
    /// Each layer's variable, by its float, and the set it ranges over.
    pub layers: Vec<(String, Rpn)>,
    pub discharge: &'static str,
}

pub struct DefineCloser {
    pub scope: Rpn,
    pub said: Rpn,
    pub var: String,
    pub ex: Rpn,
    pub p_ex: Proof,
    pub line: usize,
    pub label: String,
}

/// A block being elaborated: what it opened over and what it opened.
pub struct Block {
    pub owner: Step,
    pub outer: Rpn,
    pub outside: Facts,
    /// Index into the scope frames.
    pub frame: usize,
    pub scope: Rpn,
    pub facts: Facts,
    /// A contradiction's supposition.
    pub supposed: Option<Rpn>,
    /// An induction's name and spare.
    pub over: Option<String>,
    pub base: Option<String>,
    /// The setvar a `proof` block's `let` introduced.
    pub variable: Option<String>,
    /// What each opener of a `proof` block laid down, as it is written, in
    /// order: the scope its steps are proved under.
    pub opened: Vec<Rpn>,
    /// The names in hand before it opened, and which variable each binder
    /// had; and which each had while it was open.
    pub named: IndexMap<String, Rpn>,
    pub bound: IndexMap<String, String>,
    pub inner: IndexMap<String, String>,
    /// The lines in hand before it opened, which closing it gives back: a
    /// label its openers or steps give again, `J` in a block inside a block
    /// labelling a line `J`, is the outer line again once it closes, as the
    /// checker reads a label in scope.
    pub lines: Lines,
    /// Cases: part number -> what it assumes, and its label.
    pub assumed: IndexMap<usize, (Node, String)>,
    pub entered: Option<usize>,
    pub case_opened_at: Option<usize>,
    pub opened_at: usize,
    pub claim: Rpn,
    pub proof: Option<Proof>,
    /// Part number -> the last fact in it.
    pub parts: IndexMap<usize, PartEnd>,
}

/// What a part of a block ends on.
#[derive(Clone)]
pub struct PartEnd {
    pub claim: Rpn,
    pub proof: Proof,
    /// The scope the claim is proved under.
    pub scope: Rpn,
    /// What is known there, which is what carrying the claim to the instance
    /// the block wants may rest on (`Elaborator::reached`).
    pub facts: Facts,
}

/// What a contradiction block's last step contradicts: the claim, and the
/// proof of it the block closes on, the named line's own even where another
/// line says the same.
#[derive(Clone)]
pub struct Contradicted {
    pub claim: Rpn,
    pub proof: Proof,
    /// Where one of the two denies the other with its points named in
    /// another order, as `not (A, B, C are collinear)` does `C, A, B are
    /// collinear`: the one that asserts, carried to the order its denial
    /// names, while the block's scope still holds.
    pub reordered: Option<ProvedClaim>,
}

/// A claim and its proof under the scope it was proved in.
#[derive(Clone)]
pub struct ProvedClaim {
    pub claim: Rpn,
    pub proof: Proof,
}

/// How a define by recursion is built in set.mm (`recursion_terms`).
#[derive(Clone, Debug)]
pub struct Recurrence {
    /// The map from a state to the next, `(x ∈ _V ↦ …)`; for an indexed
    /// recursion the map of two, `(z ∈ _V, w ∈ _V ↦ …)`, taking the state
    /// and the input at the next index.
    pub step: Rpn,
    /// The values at 0, as one state.
    pub start: Rpn,
    /// How many names the define gives.
    pub count: usize,
    /// For a recursion whose rules name the index, the input `(i ∈ ℕ₀ ↦ ⟨i,
    /// start⟩)` that hands each step its index; None for one whose rules
    /// see only the values.
    pub input: Option<Rpn>,
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
    Member(Rpn),
    Head(String),
}

pub struct Elaborator<'a> {
    pub thm: &'a Theorem,
    /// The theorem as the checker reads it (`checker::CheckedTheorem`): the
    /// block each step stands in, where each define is in scope, the sorts,
    /// and the functions typed at each step.
    pub checked: CheckedTheorem,
    /// The step being elaborated, by its index in the theorem's steps; None
    /// before the first.
    pub step_now: Option<usize>,
    pub g: &'a Grammar,
    pub items: &'a IndexMap<String, Item<'a>>,
    pub records: &'a [Record],
    pub scopes: &'a [FileScope],
    /// The sort of each name, as the grammar reads it now.
    pub sorts_now: Sorts,
    pub b: Builder,
    /// Notation record -> the `target` entry of each of its patterns.
    pub terms: FxIndexMap<NotationId, Vec<Option<String>>>,
    /// Letters the notations' own targets bind and the proof writes.
    pub taken: IndexSet<String>,
    pub spare: Vec<String>,
    pub commutes: Vec<Commuting>,
    /// The identity elements the notation records declare, which a literal
    /// instance is written without (`Row::Identity`).
    pub identities: Vec<Identity>,
    /// For each method, the words whose records name it in their `decided`
    /// field, each the kernel form of what its `then` line defines, read
    /// when a method first asks (`decided_by`).
    pub decided: IndexMap<String, Vec<Term>>,
    /// Corpus theorems this proof leans on.
    pub cited: Vec<String>,
    /// What the last step of the contradiction block being elaborated
    /// contradicts, which the block closes on with that step's own line.
    pub contradicted: Option<Contradicted>,
    /// Whether the step being elaborated sits directly inside a
    /// contradiction.
    pub in_contradiction: bool,
    pub shapes: IndexMap<String, Shape>,
    /// Where the elaborator has got to, for whatever it reads there.
    pub at: usize,
    /// Readable name -> kernel term.
    pub names: IndexMap<String, Rpn>,
    /// Readable name -> the set it was let into.
    pub sets: IndexMap<String, Rpn>,
    /// Readable name -> its membership as each line introducing it says it:
    /// the claim, its proof, and the scope that proof is under, carried to
    /// any scope inside that one (`introduced_membership`). Two cases may
    /// each obtain a δ, so a name may be introduced more than once.
    pub introduced: IndexMap<String, Vec<(Rpn, Proof, Rpn)>>,
    /// Setvars the conclusion quantifies over, and those a step said of
    /// every member was proved over: none is a letter nothing holds.
    pub reserved: IndexSet<String>,
    /// Map -> its rule spelt apart (`rule_apart`).
    pub rules_read: IndexMap<Rpn, Term>,
    /// `requires` terms being discharged now.
    pub supplying: IndexSet<Rpn>,
    /// Terms whose membership is being read from an equation now, so that
    /// `x = y` and `y = x` do not send `part` from one to the other.
    pub equating: IndexSet<Rpn>,
    /// (from system, to system) -> one lemma.
    pub bridges: Option<IndexMap<(String, String), String>>,
    /// Declared lemma -> what its readings end on, and its role.
    pub lemma_heads: Option<LemmaIndex>,
    /// Term, bound letters and the defined names it may read -> its standard
    /// form.
    pub standards: IndexMap<(Rpn, Vars, String), Term>,
    /// Claim -> the key a fact of it is stored and found by
    /// (`Elaborator::fact_key`), which depends on the claim alone.
    pub fact_keys: IndexMap<Rpn, Rpn>,
    /// Reverse Polish -> the tree it builds (`to_term`), which depends on the
    /// tokens and the labels' signatures alone, and a label's signature does
    /// not change once declared. Reading the same tokens again was a sixth of
    /// a run that elaborates every theorem.
    trees: RefCell<FxIndexMap<Rpn, Term>>,
    /// Whether the facts are being read in standard form, so that the
    /// comparisons the reading makes are offered the facts as they stand.
    pub reading_facts: bool,
    /// While a step said of every member is proved at one, that member's
    /// membership: what the claim's "for all k ∈ X" gives the step, as a
    /// cited line would.
    pub member: Option<Rpn>,
    /// While `algebra` proves a step, the one letter nothing holds that
    /// every finite sum it reads is written over, so that sums over
    /// different letters are one atom; None outside it, where a sum is one.
    pub sum_letter: Option<String>,
    /// (scope, sum) -> ( scope -> sum e. CC ), for each sum a linear reading
    /// wrote, proved from its terms when it was written.
    pub sums_in_cc: IndexMap<(Rpn, Rpn), Proof>,
    /// The rules of the standard form set.mm has, plain and conditional,
    /// read once.
    pub rewrite_rules: Option<[Rc<[super::matcher::Rewrite]>; 2]>,
    /// Each library label's statement as a term, read from its text the
    /// first time it is asked (`statement`). A label the theorem adds is
    /// read each time, since what it says is the theorem's to change.
    pub statements_read: RefCell<FxIndexMap<String, Term>>,
    /// Letters `same` reads as blanks.
    pub binding: Vars,
    /// The lines what is being proved cites, in the order it writes them.
    pub citing: IndexSet<String>,
    /// How many families' values are being read: a sum's terms, or what an
    /// item asks of every member. There a function's type gives its values
    /// as the sort it is (`function_value`).
    pub in_family: usize,
    /// The sums the step being elaborated writes that the page says are
    /// numbers once, as kernel terms (`CheckedTheorem::said_sums`).
    pub said_sums: BTreeSet<Rpn>,
    /// Whether the order being proved is a plain `inequalities` step's,
    /// which adds its facts as they stand (`linear::certificate`'s `alike`).
    pub adding_only: bool,
    /// Where messages are being tested, each sentence said back as another
    /// term (`Options::say_back`).
    pub said_back: Option<Vec<String>>,
    /// What the proof being built may rest on.
    pub resting: Option<BTreeSet<String>>,
    /// How many searches for a divisor's `≠ 0` enclose this point. That a
    /// divisor is not zero is the page's to say, so no membership said once
    /// is offered on the way to it (`introduced_membership`, `not_zero`).
    pub beyond_once: u32,
    /// Labels of sort lines and `define` lines.
    pub sorts: BTreeSet<String>,
    /// Side conditions the step being proved wrote, with the scope each was
    /// proved under.
    pub written: Written,
    pub saying: IndexSet<Rpn>,
    pub rewriting: IndexSet<Rpn>,
    pub numbering: IndexSet<Rpn>,
    /// (membership, scope) -> what it came to.
    pub numbers: IndexMap<(Rpn, Rpn), Route<Proof>>,
    /// Binder name -> the setvar it stands for, and back.
    pub bound_as: IndexMap<String, String>,
    pub written_as: IndexMap<String, String>,
    /// How far down the `define` lines we have read.
    pub unread: usize,
    /// A defined name's setvar -> the term it names.
    pub definitions: IndexMap<String, Rpn>,
    /// A defined name's setvar -> the label of the define that names it, which
    /// a step cites to read the name as what it names.
    pub defined_by: IndexMap<String, String>,
    /// Name -> tree, while a statement is read.
    pub from_outside: IndexMap<String, Defined>,
    /// A define by recursion: its label -> each name's map; its seq term ->
    /// how it is built; and while a step rule is read, each name -> its part
    /// of the state.
    pub recursion_maps: IndexMap<String, IndexMap<String, Rpn>>,
    pub recursions: IndexMap<Rpn, Recurrence>,
    pub recurring: IndexMap<String, Rpn>,
    pub file_given: bool,
    pub last: Option<String>,
    /// The scope frames, innermost last.
    pub frames: Vec<Frame>,
    pub lines: Lines,
    /// Notation record -> the literals of its patterns, in the order the
    /// `pattern` and `target` fields both use, each as a spelling of the
    /// record's own notation.
    pub literals: FxIndexMap<NotationId, Vec<Spelling>>,
    /// Notation -> the holes each binder introduces a name in.
    pub binders: FxIndexMap<NotationId, Vec<usize>>,
    /// The statement a cited theorem's file proves, where it is known.
    pub statements: &'a dyn Fn(&str) -> Option<String>,
    /// Whether the search is offered every fact in scope (`Options`).
    pub whole_scope: bool,
    /// Whether the route proving a defined function's type is off
    /// (`Options::map_types_off`).
    pub map_types_off: bool,
    /// What each record asks a citation and concludes, read as the checker
    /// reads it (`citing`), the first time a citation asks.
    pub item_library: OnceCell<Rc<citing::Library<'a>>>,
    /// Every item a citation may name, as the checker read it.
    pub library_read: &'a LibraryReading,
    /// Every reading the grammar has, in the order a term is read back to
    /// the page by (`reading_table`), made the first time one is.
    pub(super) readings: OnceCell<Vec<super::spoken::Ranked>>,
}

impl<'a> Elaborator<'a> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        thm: &'a Theorem,
        checked: CheckedTheorem,
        g: &'a Grammar,
        items: &'a IndexMap<String, Item<'a>>,
        sigs: Layered,
        records: &'a [Record],
        library_read: &'a LibraryReading,
        scopes: &'a [FileScope],
        statements: &'a dyn Fn(&str) -> Option<String>,
    ) -> Elaborator<'a> {
        let sorts_now = checked.sorts.clone();
        let b = Builder::new(sigs);
        let terms: FxIndexMap<NotationId, Vec<Option<String>>> =
            targets::terms(records)
                .into_iter()
                .map(|(name, entries)| (NotationId::of(&name), entries))
                .collect();
        let mut taken: IndexSet<String> = IndexSet::new();
        for entries in terms.values() {
            for e in entries.iter().flatten() {
                for t in e.split_whitespace() {
                    taken.insert(t.to_string());
                }
            }
        }
        // Every single letter the page shows anywhere, in a formula, a label
        // or a word, keeps its kernel variable: a spare one never looks like
        // a letter on the page. This reads no formula; it is wider than the
        // names the formulas write (`sorts::names_written`), and narrowing it
        // to those would rename the spare variables of elaborated proofs.
        let text = written_text(thm);
        for letter in lone_letters(&text) {
            if let Some(label) = b.flabel.get(&letter) {
                taken.insert(label.to_string());
            }
        }
        let spare = SPARE_VARS
            .iter()
            .filter(|v| !taken.contains(**v))
            .map(|v| v.to_string())
            .collect();
        let mut literals: FxIndexMap<NotationId, Vec<Spelling>> = FxIndexMap::default();
        for n in &g.notations {
            literals.entry(n.record_id).or_default().push(Spelling::new(
                n.record_id,
                LiteralId::of(n.record_id, &n.literal),
            ));
        }
        let binders = binding_context(&g.notations)
            .0
            .into_iter()
            .map(|(notation, b)| (notation, b.held))
            .collect();
        Elaborator {
            thm,
            checked,
            step_now: None,
            g,
            items,
            records,
            scopes,
            sorts_now,
            b,
            taken,
            spare,
            commutes: targets::commuting(records),
            identities: targets::identities(records),
            decided: IndexMap::new(),
            cited: Vec::new(),
            contradicted: None,
            in_contradiction: false,
            shapes: IndexMap::new(),
            at: thm.line,
            names: IndexMap::new(),
            sets: IndexMap::new(),
            introduced: IndexMap::new(),
            reserved: IndexSet::new(),
            rules_read: IndexMap::new(),
            supplying: IndexSet::new(),
            equating: IndexSet::new(),
            bridges: None,
            lemma_heads: None,
            standards: IndexMap::new(),
            fact_keys: IndexMap::new(),
            trees: RefCell::new(FxIndexMap::default()),
            reading_facts: false,
            member: None,
            sum_letter: None,
            sums_in_cc: IndexMap::new(),
            rewrite_rules: None,
            statements_read: RefCell::new(FxIndexMap::default()),
            binding: Vars::new(),
            citing: IndexSet::new(),
            in_family: 0,
            said_sums: BTreeSet::new(),
            adding_only: false,
            said_back: None,
            resting: None,
            beyond_once: 0,
            sorts: BTreeSet::new(),
            written: Written::new(),
            saying: IndexSet::new(),
            rewriting: IndexSet::new(),
            numbering: IndexSet::new(),
            numbers: IndexMap::new(),
            bound_as: IndexMap::new(),
            written_as: IndexMap::new(),
            unread: 0,
            definitions: IndexMap::new(),
            defined_by: IndexMap::new(),
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
            map_types_off: false,
            item_library: OnceCell::new(),
            library_read,
            readings: OnceCell::new(),
        }
    }

    /// What each record asks a citation and concludes, read once. Only
    /// records: a theorem of the corpus is cited by what its own file proves.
    pub fn item_library(&self) -> Rc<citing::Library<'a>> {
        let library = self.item_library.get_or_init(|| {
            let env = Env {
                g: self.g,
                scopes: self.scopes,
            };
            // The corpus theorems this theorem cites, which a citation
            // matches as it matches a record: each with the sorts the
            // checker read its statement with (`cited_statement`).
            let mut proved = IndexMap::new();
            for (name, _) in crate::corpus::proof::cited_items(self.thm) {
                if let (Some(Item::Theorem(t)), Some(cited)) =
                    (self.items.get(&name), self.library_read.cited.get(&name))
                {
                    proved.entry(name).or_insert_with(|| citing::Proved {
                        thm: t,
                        sorts: std::borrow::Cow::Borrowed(&cited.sorts),
                    });
                }
            }
            Rc::new(citing::Library::read_by_checker(
                self.records,
                std::borrow::Cow::Borrowed(&self.library_read.record_sorts),
                proved,
                env,
                &self.library_read.groups,
            ))
        });
        library.clone()
    }

    /// Something a person has to fix, and where in the proof it is: every
    /// defect raised here is a place in the text this elaborator is reading,
    /// in the file the theorem was read from.
    pub fn defect(&self, line: usize, message: impl Into<String>) -> Problem {
        Problem::new(&self.thm.path, line, message)
    }

    /// A page shape the build stops at that the checker refuses
    /// (`Problem::internal`): a guard the guard audit found the checker
    /// holds, which a page the checker accepts never reaches.
    pub fn unreached(&self, line: usize, message: impl Into<String>) -> Problem {
        Problem::internal(&self.thm.path, line, message)
    }

    /// This route does not apply, and why, in the terms as they stand. The
    /// words are put together only if something reads them.
    pub fn no<T>(
        &self,
        shape: impl Into<std::borrow::Cow<'static, str>>,
        terms: &[&Rpn],
    ) -> Route<T> {
        Route::Declined(Decline::shaped(
            shape,
            terms.iter().map(|t| t.to_string()).collect(),
        ))
    }

    /// A decline's reason, with its terms written as a Metamath file writes
    /// them. A decline holds its terms as text, as every route's does.
    pub fn say(&self, decline: &Decline) -> String {
        decline.render(|t| self.render(&Rpn::read(t)))
    }

    /// A term as a message names it: in the page's notation, or the way a
    /// Metamath file writes it where some part has no page reading
    /// (`spoken`).
    pub fn render(&self, rpn: &Rpn) -> String {
        self.spoken(rpn).unwrap_or_else(|| self.kernel_text(rpn))
    }

    /// A term the way a Metamath file writes it, for the file itself.
    pub fn kernel_text(&self, rpn: &Rpn) -> String {
        render(&rpn.to_string(), &self.b.sigs)
    }

    pub fn flabel(&self) -> &FloatLabels {
        &self.b.flabel
    }

    /// The label of a variable's float, or the name itself where it has none.
    pub fn float_of(&self, var: &str) -> String {
        self.b
            .flabel
            .get(var)
            .map_or_else(|| var.to_string(), |f| f.to_string())
    }

    /// A term the proof holds, read back as a tree.
    pub fn to_term(&self, rpn: &Rpn) -> Term {
        if let Some(found) = self.trees.borrow().get(rpn) {
            return found.clone();
        }
        let made = term_of(rpn, &self.b.sigs);
        self.trees.borrow_mut().insert(rpn.clone(), made.clone());
        made
    }

    /// A term as a proof spells it.
    pub fn rpn(&self, term: &Term) -> Rpn {
        term.rpn(&self.b.flabel)
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
        if let Some(read) = self.statements_read.borrow().get(label) {
            return read.clone();
        }
        let sig = self.sig(label);
        let read = self
            .b
            .syntax()
            .statement(sig)
            .unwrap_or_else(|p| panic!("{label} does not parse: {p}"));
        if self.b.sigs.is_library(label) {
            self.statements_read
                .borrow_mut()
                .insert(label.to_string(), read.clone());
        }
        read
    }

    /// An essential hypothesis's claim, as a term.
    pub fn essential(&self, tokens: &[Symbol]) -> Term {
        let words: Vec<&str> = tokens[1..].iter().map(|t| t.as_str()).collect();
        self.b
            .syntax()
            .parse(&words, "wff")
            .unwrap_or_else(|p| panic!("{words:?} does not parse: {p}"))
    }

    /// A binding of kernel terms, as the reverse Polish `ap` wants pushed.
    pub fn spelt(&self, binding: &Binding) -> Binds {
        binding
            .iter()
            .map(|(v, t)| (v.to_string(), self.rpn(t)))
            .collect()
    }

    /// The set variable a setvar's label stands for, as a term.
    pub fn var_of(&self, label: &str) -> Term {
        Term::var(self.sig(label).statement[1])
    }

    /// The setvar labels every name the proof holds as `x cv` stands for.
    pub fn names_held(&self) -> IndexSet<String> {
        self.names
            .values()
            .filter(|t| t.len() > 1 && t.ends_with(&["cv"]))
            .filter_map(|t| t.first().map(String::from))
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
