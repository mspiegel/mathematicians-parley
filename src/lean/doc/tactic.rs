//! Lean proofs as values: a term, or tactics.

use super::term::{Source, Term};

/// A tactic the bridges or Lean define, by name, and where it comes from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TacticRef {
    pub name: &'static str,
    pub source: Source,
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
    /// A tactic called by name, with its arguments as Lean text after it.
    Call { tactic: TacticRef, args: Vec<Term> },
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
}

/// A proof: a term, or tactics after `by`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Proof {
    Term(Term),
    By(Tactic),
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
                Tactic::Group(t) | Tactic::Try(t) | Tactic::AllGoals(t) => out.push(t),
                Tactic::Raw(_) | Tactic::Exact(_) | Tactic::Call { .. } => {}
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
