//! The tactics the Lean writer calls, built as values (`doc::Tactic`):
//! each names the tactic and the lemmas it uses with where they come from,
//! so that a file imports what its proofs call.

use super::doc::bridges::{BridgeModule, BridgeTactic};
use super::doc::{
    Location, Rule, Source, Tactic, TacticArg, TacticRef, Term, TermKind,
};

/// A tactic of Lean's or Mathlib's, called with these.
pub fn call(name: &'static str, args: Vec<TacticArg>) -> Tactic {
    Tactic::Call {
        tactic: TacticRef::Mathlib(name),
        args,
    }
}

/// A tactic of the bridges, called with these.
pub fn bridge(tactic: BridgeTactic, args: Vec<TacticArg>) -> Tactic {
    Tactic::Call {
        tactic: TacticRef::Bridge(tactic),
        args,
    }
}

/// A hypothesis, by its name.
pub fn hyp(name: &str) -> Term {
    Term {
        kind: TermKind::Letter(name.to_string()),
        ty: None,
    }
}

/// A lemma of Mathlib's, by its name.
pub fn lemma(name: &str) -> Term {
    Term::head(name, Source::Mathlib)
}

/// A lemma of a bridge module, by its full name.
pub fn bridge_lemma(name: &str, module: BridgeModule) -> Term {
    Term::head(name, Source::Bridge(module))
}

/// A proof standing as a term, `by t` inside `⟨w, by t⟩`.
pub fn by_term(proof: super::doc::Proof) -> Term {
    Term {
        kind: TermKind::By(Box::new(proof)),
        ty: None,
    }
}

/// A term's `.symm`, bracketed as an argument where it needs it.
pub fn symm(term: Term) -> Term {
    Term {
        ty: term.ty.clone(),
        kind: TermKind::Field {
            inner: Box::new(term),
            field: "symm".to_string(),
        },
    }
}

/// A term in brackets, `(t)`, as a citation is put before `.symm`.
pub fn bracket(term: Term) -> Term {
    Term {
        ty: term.ty.clone(),
        kind: TermKind::Paren(Box::new(term)),
    }
}

/// The steps one after the other in brackets, `(a; b)`, as one way of a
/// `first`.
pub fn steps(steps: Vec<Tactic>) -> Tactic {
    Tactic::Group(Box::new(Tactic::Seq(steps)))
}

/// `(have h := t; …)`: a term's statement named h, then the tactics that
/// work on it, as one way of a `first`.
pub fn on_h(term: &Term, rest: Vec<Tactic>) -> Tactic {
    let mut all = vec![name_h(term)];
    all.extend(rest);
    steps(all)
}

/// `have h := t`.
pub fn name_h(term: &Term) -> Tactic {
    Tactic::Name {
        name: "h".to_string(),
        term: term.clone(),
    }
}

/// Rules used forwards.
pub fn rules(by: Vec<Term>) -> TacticArg {
    TacticArg::Rules(
        by.into_iter()
            .map(|by| Rule {
                by,
                backwards: false,
            })
            .collect(),
    )
}

/// `at h ⊢`, or `at h`.
pub fn at_h(goal: bool) -> TacticArg {
    let mut places = vec![Location::Hypothesis("h".to_string())];
    if goal {
        places.push(Location::Goal);
    }
    TacticArg::At(places)
}

/// `linear_combination (norm := parley_norm) e`.
pub fn linear_combination(by: Term) -> Tactic {
    call(
        "linear_combination",
        vec![
            TacticArg::Setting {
                key: "norm",
                value: Box::new(bridge(BridgeTactic::Norm, Vec::new())),
            },
            TacticArg::Term(by),
        ],
    )
}

/// `exact_mod_cast t`.
pub fn exact_mod_cast(term: Term) -> Tactic {
    call("exact_mod_cast", vec![TacticArg::Term(term)])
}

/// `push_cast at …`, or at the goal alone where none is given.
pub fn push_cast(at: Option<TacticArg>) -> Tactic {
    call("push_cast", at.into_iter().collect())
}

/// `(try t)`.
pub fn try_(tactic: Tactic) -> Tactic {
    Tactic::Group(Box::new(Tactic::Try(Box::new(tactic))))
}

/// `simp (disch := d) only [rules] at …`, the discharger and location where
/// given; `+contextual` before the discharger where asked.
pub fn simp_only(
    contextual: bool,
    disch: Option<Tactic>,
    by: Vec<Rule>,
    at: Option<TacticArg>,
) -> Tactic {
    let mut args = Vec::new();
    if contextual {
        args.push(TacticArg::Flag("+contextual"));
    }
    if let Some(d) = disch {
        args.push(TacticArg::Setting {
            key: "disch",
            value: Box::new(d),
        });
    }
    args.push(TacticArg::Only);
    args.push(TacticArg::Rules(by));
    args.extend(at);
    call("simp", args)
}

/// `simpa only [rules] using t`: `t` and the goal rewritten alike, Mathlib's
/// lemmas `rules` naming the rewrites.
pub fn simpa_only(rules: Vec<&'static str>, using: Term) -> Tactic {
    call(
        "simpa",
        vec![
            TacticArg::Only,
            TacticArg::Rules(rules.into_iter().map(|r| forwards(lemma(r))).collect()),
            TacticArg::Using(using),
        ],
    )
}

/// `first | a | b`: the ways tried in order, for the reason `why`.
pub fn first(why: super::doc::ListReason, ways: Vec<Tactic>) -> Tactic {
    Tactic::First { why, ways }
}

/// A rule used forwards.
pub fn forwards(by: Term) -> Rule {
    Rule {
        by,
        backwards: false,
    }
}

/// A rule used backwards, `← r`.
pub fn backwards(by: Term) -> Rule {
    Rule {
        by,
        backwards: true,
    }
}
