//! Lean proofs as values: a term, or tactics.

use super::bridges::BridgeTactic;
use super::term::{LeanType, Source, Term};

/// A tactic a proof calls: one the bridges define, or one of Lean's or
/// Mathlib's, by its name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TacticRef {
    Bridge(BridgeTactic),
    Mathlib(&'static str),
}

impl TacticRef {
    /// Its name in Lean.
    pub fn name(self) -> &'static str {
        match self {
            TacticRef::Bridge(t) => t.name(),
            TacticRef::Mathlib(name) => name,
        }
    }

    /// Where it comes from, which a file calling it imports.
    pub fn source(self) -> Source {
        match self {
            TacticRef::Bridge(t) => Source::Bridge(t.module()),
            TacticRef::Mathlib(_) => Source::Mathlib,
        }
    }
}

/// A tactic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tactic {
    /// Tactic text the writer made without a tree. It stands only while
    /// the writer's proofs move to tactics one at a time, and goes when the
    /// last does.
    Raw(String),
    /// `exact t`.
    Exact(Term),
    /// A tactic called by name, with what follows it, in order.
    Call {
        tactic: TacticRef,
        args: Vec<TacticArg>,
    },
    /// `have h := t`: a term's statement named, for the tactics after it.
    Name { name: String, term: Term },
    /// `have := t`: a term's statement put among the facts, unnamed.
    Fact(Term),
    /// `first | a | b`: the first that closes the goal.
    First(Vec<Tactic>),
    /// `a; b`: one after the other.
    Seq(Vec<Tactic>),
    /// `(a)`.
    Group(Box<Tactic>),
    /// `try a`.
    Try(Box<Tactic>),
    /// `all_goals a`.
    AllGoals(Box<Tactic>),
    /// `have name : says := proof`: a line of the page proved, its proof
    /// on one line or several.
    Have {
        name: String,
        says: Term,
        proof: Box<Proof>,
    },
    /// `-- text`: what a step of the page is, above its Lean.
    Comment(String),
    /// `· t`: one goal of several, taken by itself.
    Bullet(Box<Tactic>),
    /// `obtain ⟨a, b⟩ := t`, or `obtain ⟨a, b⟩ : s := t` where it says what
    /// t states: a statement taken apart into names.
    Obtain {
        names: Vec<String>,
        says: Option<Term>,
        from: Term,
    },
    /// `set x : T := v with h`: a letter for a value, and h its equation.
    Set {
        name: String,
        ty: LeanType,
        value: Term,
        with: String,
    },
    /// `intro a b`.
    Intro(Vec<String>),
    /// `replace name : says := proof`.
    Replace {
        name: String,
        says: Term,
        proof: String,
    },
    /// `induction a, b using r with`: the cases follow as alternatives.
    Induction { on: Vec<String>, using: Term },
    /// `| pattern =>`: a case of an induction.
    Alternative(String),
    /// `calc a rel b := p` and `_ rel c := q` below it: a chain of
    /// relations, each link with its proof.
    Calc { first: Term, links: Vec<CalcLink> },
}

/// One link of a `calc`: the relation, the term it reaches, the modulus of
/// a congruence, and the link's proof as Lean text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CalcLink {
    pub relation: String,
    pub term: Term,
    pub modulus: Option<Term>,
    pub proof: String,
}

/// What follows a tactic's name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TacticArg {
    /// A term, as the writer gives it.
    Term(Term),
    /// A setting, `(norm := parley_norm)` or `(disch := omega)`.
    Setting {
        key: &'static str,
        value: Box<Tactic>,
    },
    /// `only`.
    Only,
    /// A flag, `+contextual`.
    Flag(&'static str),
    /// Lemmas or hypotheses to rewrite or simplify by, `[a, ← b]`.
    Rules(Vec<Rule>),
    /// `using t`.
    Using(Term),
    /// Where it works, `at h ⊢`.
    At(Vec<Location>),
}

/// A lemma or hypothesis a rewrite or simplification uses, forwards or
/// backwards.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule {
    pub by: Term,
    pub backwards: bool,
}

/// A place a tactic works at.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Location {
    /// A hypothesis, by its name.
    Hypothesis(String),
    /// The goal, `⊢`.
    Goal,
    /// Everywhere, `*`.
    Everywhere,
}

/// A proof: a term, or tactics after `by`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proof {
    Term(Term),
    /// `by t`, on one line.
    By(Tactic),
    /// `by` and the tactics on the lines below it.
    Block(Vec<Tactic>),
    /// Proof text the writer made without a tree. It stands only while
    /// the writer's proofs move to values one at a time, and goes with
    /// `Tactic::Raw`.
    Raw(String),
}

impl Tactic {
    /// Every tactic of the tree, this one first.
    pub fn walk(&self) -> Vec<&Tactic> {
        let mut out = vec![self];
        let mut i = 0;
        while i < out.len() {
            let node = out[i];
            match node {
                Tactic::First(ts) | Tactic::Seq(ts) => out.extend(ts.iter()),
                Tactic::Group(t)
                | Tactic::Try(t)
                | Tactic::AllGoals(t)
                | Tactic::Bullet(t) => out.push(t),
                Tactic::Call { args, .. } => {
                    out.extend(args.iter().filter_map(|a| match a {
                        TacticArg::Setting { value, .. } => Some(&**value),
                        _ => None,
                    }));
                }
                Tactic::Raw(_)
                | Tactic::Exact(_)
                | Tactic::Name { .. }
                | Tactic::Fact(_)
                | Tactic::Have { .. }
                | Tactic::Comment(_)
                | Tactic::Obtain { .. }
                | Tactic::Set { .. }
                | Tactic::Intro(_)
                | Tactic::Replace { .. }
                | Tactic::Induction { .. }
                | Tactic::Alternative(_)
                | Tactic::Calc { .. } => {}
            }
            i += 1;
        }
        out
    }

    /// The tactics the tree calls by name.
    pub fn called(&self) -> Vec<&TacticRef> {
        self.walk()
            .into_iter()
            .filter_map(|t| match t {
                Tactic::Call { tactic, .. } => Some(tactic),
                _ => None,
            })
            .collect()
    }
}
