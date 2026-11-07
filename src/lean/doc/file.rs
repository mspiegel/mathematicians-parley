//! Lean declarations as values: what one says, how it is proved, and the
//! terms and tactics a file's imports are read from.

use std::collections::BTreeSet;

use super::tactic::{Proof, Tactic, TacticArg};
use super::term::{LeanType, Term, TermKind};

/// Something a declaration writes whose modules Lean is asked for
/// (`lean/scripts/ModulesOf.lean`): a constant by its full name, or a
/// sample of a term's or a tactic's syntax.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lookup {
    Const(String),
    Term(String),
    Tactic(String),
    /// Declarations as Lean text, elaborated for the constants their
    /// proofs use: a module of records' own proofs.
    Command(String),
}

impl Lookup {
    /// The kind the lookup script reads it as.
    pub fn kind(&self) -> &'static str {
        match self {
            Lookup::Const(_) => "const",
            Lookup::Term(_) => "term",
            Lookup::Tactic(_) => "tactic",
            Lookup::Command(_) => "command",
        }
    }

    /// The constant's name, or the sample.
    pub fn key(&self) -> &str {
        match self {
            Lookup::Const(k)
            | Lookup::Term(k)
            | Lookup::Tactic(k)
            | Lookup::Command(k) => k,
        }
    }

    /// The lookup of a kind and a key as the script writes them; None for a
    /// kind it does not read.
    pub fn of(kind: &str, key: &str) -> Option<Lookup> {
        match kind {
            "const" => Some(Lookup::Const(key.to_string())),
            "term" => Some(Lookup::Term(key.to_string())),
            "tactic" => Some(Lookup::Tactic(key.to_string())),
            "command" => Some(Lookup::Command(key.to_string())),
            _ => None,
        }
    }
}

/// A binder of a declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Binder {
    /// A letter of a type, `(x : ℝ)`, or types with their classes, `{α :
    /// Type*}`: its Lean text, and the type where it is one the model
    /// has.
    Typed { text: String, ty: Option<LeanType> },
    /// A hypothesis, `(h : says)`.
    Fact { name: String, says: Term },
}

/// One line of a proof by tactics, at the depth of its blocks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub depth: usize,
    pub tactic: Tactic,
}

/// How a declaration is proved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclProof {
    /// `:= by` and the steps on the lines below it.
    Steps(Vec<Step>),
    /// `:=` and a proof a record gives in Lean, with the library modules
    /// its text names, read when the record is read.
    Verbatim {
        text: String,
        modules: BTreeSet<String>,
    },
}

/// A theorem of a Lean file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Declaration {
    /// The heartbeats Lean may spend on it, where more than its default.
    pub heartbeats: Option<u64>,
    pub name: String,
    pub binders: Vec<Binder>,
    pub says: Term,
    pub proof: DeclProof,
}

impl Binder {
    /// The binder as Lean text.
    pub fn text(&self) -> String {
        match self {
            Binder::Typed { text, .. } => text.clone(),
            Binder::Fact { name, says } => format!("({name} : {})", says.text()),
        }
    }
}

impl Step {
    /// The step as Lean text, indented to its depth, each line its tactic
    /// runs over too.
    pub fn text(&self) -> String {
        let pad = "  ".repeat(self.depth);
        let tactic = self.tactic.text().replace('\n', &format!("\n{pad}"));
        format!("{pad}{tactic}")
    }
}

impl Declaration {
    /// The lines that state it, down to `:=` and the `by` of a proof by
    /// tactics.
    pub fn head(&self) -> String {
        let mut out = String::new();
        if let Some(h) = self.heartbeats {
            out.push_str(&format!("set_option maxHeartbeats {h} in\n"));
        }
        let binders: Vec<String> = self.binders.iter().map(Binder::text).collect();
        let space = if binders.is_empty() { "" } else { " " };
        out.push_str(&format!(
            "theorem {}{space}{} :\n    {} :=",
            self.name,
            binders.join(" "),
            self.says.text()
        ));
        if let DeclProof::Steps(_) = self.proof {
            out.push_str(" by");
        }
        out
    }

    /// The declaration as Lean text.
    pub fn text(&self) -> String {
        let mut out = self.head();
        match &self.proof {
            DeclProof::Steps(steps) => {
                for s in steps {
                    out.push('\n');
                    out.push_str(&s.text());
                }
            }
            DeclProof::Verbatim { text, .. } => {
                out.push_str("\n  ");
                out.push_str(text);
            }
        }
        out
    }

    /// Every term and tactic it writes.
    pub fn parts(&self) -> Parts<'_> {
        let mut parts = Parts::default();
        for b in &self.binders {
            if let Binder::Fact { says, .. } = b {
                parts.term(says);
            }
        }
        parts.term(&self.says);
        if let DeclProof::Steps(steps) = &self.proof {
            for s in steps {
                parts.tactic(&s.tactic);
            }
        }
        parts
    }

    /// What it writes that Lean or Mathlib declares: each constant of
    /// theirs it names, and a sample of each piece of syntax, its
    /// notations, the types it writes, the tactics it calls and its
    /// binders. A record's own proof is Lean text the trees do not hold;
    /// its module is asked of whole (`Lookup::Command`).
    pub fn lookups(&self) -> BTreeSet<Lookup> {
        let mut out = BTreeSet::new();
        for b in &self.binders {
            if let Binder::Typed { text, .. } = b {
                out.insert(Lookup::Term(format!("∀ {text}, True")));
            }
        }
        let parts = self.parts();
        for t in &parts.terms {
            out.extend(t.named());
            if let Some(sample) = t.sample() {
                out.insert(Lookup::Term(sample));
            }
        }
        for t in &parts.tactics {
            if let Some(sample) = t.sample() {
                out.insert(Lookup::Tactic(sample));
            }
        }
        out
    }

    /// The library modules a record's own proof names.
    pub fn verbatim_modules(&self) -> BTreeSet<String> {
        match &self.proof {
            DeclProof::Verbatim { modules, .. } => modules.clone(),
            DeclProof::Steps(_) => BTreeSet::new(),
        }
    }

    /// Whether it is about sets: a binder, a letter it sets or a term of
    /// Lean's `Set`, a constant of its namespace, or a set counted in ℕ∞.
    pub fn about_sets(&self) -> bool {
        let typed = self.binders.iter().any(|b| match b {
            Binder::Typed { ty: Some(ty), .. } => ty.has_set(),
            _ => false,
        });
        let parts = self.parts();
        let set_letter = parts
            .tactics
            .iter()
            .any(|t| matches!(t, Tactic::Set { ty, .. } if ty.has_set()));
        typed || set_letter || parts.terms.iter().any(|t| t.about_sets())
    }

    /// The proof with the side tactic of sets wherever the side tactic
    /// stands.
    pub fn with_set_side(&mut self) {
        if let DeclProof::Steps(steps) = &mut self.proof {
            for s in steps {
                s.tactic.set_side();
            }
        }
    }
}

/// Every term node and every tactic of a declaration, a proof standing as
/// a term looked into.
#[derive(Default)]
pub struct Parts<'a> {
    pub terms: Vec<&'a Term>,
    pub tactics: Vec<&'a Tactic>,
}

impl<'a> Parts<'a> {
    fn term(&mut self, t: &'a Term) {
        for node in t.walk() {
            self.terms.push(node);
            if let TermKind::By(p) = &node.kind {
                self.proof(p);
            }
        }
    }

    fn proof(&mut self, p: &'a Proof) {
        match p {
            Proof::Term(t) => self.term(t),
            Proof::By(t) => self.tactic(t),
            Proof::Block(ts) => {
                for t in ts {
                    self.tactic(t);
                }
            }
        }
    }

    fn arg(&mut self, a: &'a TacticArg) {
        match a {
            TacticArg::Term(t) | TacticArg::Using(t) => self.term(t),
            TacticArg::Setting { value, .. } => self.tactic(value),
            TacticArg::Rules(rules) => {
                for r in rules {
                    self.term(&r.by);
                }
            }
            TacticArg::Only | TacticArg::Flag(_) | TacticArg::At(_) => {}
        }
    }

    fn tactic(&mut self, t: &'a Tactic) {
        self.tactics.push(t);
        match t {
            Tactic::Exact(term) | Tactic::Fact(term) => self.term(term),
            Tactic::Name { term, .. } => self.term(term),
            Tactic::Call { args, .. } => {
                for a in args {
                    self.arg(a);
                }
            }
            Tactic::First(ts) | Tactic::Seq(ts) => {
                for t in ts {
                    self.tactic(t);
                }
            }
            Tactic::Group(t)
            | Tactic::Try(t)
            | Tactic::AllGoals(t)
            | Tactic::Bullet(t) => self.tactic(t),
            Tactic::Have { says, proof, .. } | Tactic::Replace { says, proof, .. } => {
                self.term(says);
                self.proof(proof);
            }
            Tactic::Obtain { says, from, .. } => {
                if let Some(s) = says {
                    self.term(s);
                }
                self.term(from);
            }
            Tactic::Set { value, .. } => self.term(value),
            Tactic::Rcases { from, .. } => self.term(from),
            Tactic::Induction { using, .. } => self.term(using),
            Tactic::Calc { first, links } => {
                self.term(first);
                for l in links {
                    self.term(&l.term);
                    if let Some(m) = &l.modulus {
                        self.term(m);
                    }
                    self.proof(&l.proof);
                }
            }
            Tactic::Comment(_) | Tactic::Intro(_) | Tactic::Alternative(_) => {}
        }
    }
}
