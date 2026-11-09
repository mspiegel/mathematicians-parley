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

/// Why a step is closed by a `first` list: what no rule decides of it, so
/// that the step tries its ways in order. The register of lists keeps each
/// by its reason (`tests/first_lists.rs`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ListReason {
    /// A cited item's statement and the claim, Lean states in different
    /// types.
    CitedTypesApart,
    /// The two take an exponent to ℕ (`toNat`) in different places.
    CitedToNatApart,
    /// The two hold casts `push_cast` does not move all of.
    CitedCastsUnmoved,
    /// The two, in one type with their casts moved, are apart in the atoms
    /// the ring's laws see.
    CitedAtomsApart,
    /// An equation the checker records no facing of.
    CitedFacingUnknown,
    /// A statement other than an equation or an order, met otherwise than
    /// as written.
    CitedOtherShape,
    /// A claim Lean's types make true.
    CitedClaimTruth,
    /// A claim that counts a set, where a calculation may take its rows in
    /// ℕ∞.
    CitedClaimCounts,
    /// The claim or the item's statement the writer does not state.
    CitedUnstated,
    /// A line and a goal apart in casts the cast table does not settle.
    CastsUnsettled,
    /// A named number's equations put in: the claim as it stands, or once
    /// worked out.
    NamedNumbers,
    /// A function the header lets by its value put in: the claim as it
    /// stands, or once worked out.
    HeaderFunction,
    /// A power's exponent taken to ℕ by a fact in scope or an index's range.
    NaturalPowers,
    /// A calculation row's equation put in by rewriting or substituting.
    RowPut,
    /// A calculation row read off a cited line, as it stands or turned, or
    /// a part of it.
    RowRead,
    /// A define's two sides met with the defines written out.
    DefineSides,
    /// A define by cases, whose case the cited lines show: the record says
    /// nothing of which case holds.
    DefineByCases,
    /// A substitution's equation put in: at its own type, the line's, or in
    /// ℕ, by rewriting or by substituting.
    Substituted,
    /// A definition read backwards, its left side said otherwise than the
    /// claim.
    DefinitionBackwards,
}

impl ListReason {
    /// What the register says of it.
    pub fn text(self) -> &'static str {
        match self {
            ListReason::CitedTypesApart => "cited: item and claim in different types",
            ListReason::CitedToNatApart => "cited: toNat in different places",
            ListReason::CitedCastsUnmoved => "cited: casts push_cast does not move",
            ListReason::CitedAtomsApart => "cited: ring atoms apart",
            ListReason::CitedFacingUnknown => "cited: equation with no facing recorded",
            ListReason::CitedOtherShape => {
                "cited: other shape, met otherwise than written"
            }
            ListReason::CitedClaimTruth => "cited: claim a truth of Lean's types",
            ListReason::CitedClaimCounts => "cited: claim counts a set",
            ListReason::CitedUnstated => "cited: claim or item not stated",
            ListReason::CastsUnsettled => "casts the cast table does not settle",
            ListReason::NamedNumbers => "named numbers put in",
            ListReason::HeaderFunction => "header function put in",
            ListReason::NaturalPowers => "exponents taken to ℕ",
            ListReason::RowPut => "row: equation put in",
            ListReason::RowRead => "row: read off a cited line",
            ListReason::DefineSides => "define: sides with defines written out",
            ListReason::DefineByCases => "define by cases: the case not recorded",
            ListReason::Substituted => "substitute: equation put in",
            ListReason::DefinitionBackwards => "definition read backwards",
        }
    }
}

/// A tactic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tactic {
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
    /// `first | a | b`: the first that closes the goal, tried because of
    /// `why`.
    First { why: ListReason, ways: Vec<Tactic> },
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
    /// `rcases t with p`: a statement taken apart by a pattern.
    Rcases { from: Term, pattern: Pattern },
    /// `replace name : says := proof`.
    Replace {
        name: String,
        says: Term,
        proof: Box<Proof>,
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
/// a congruence, and the link's proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CalcLink {
    pub relation: String,
    pub term: Term,
    pub modulus: Option<Term>,
    pub proof: Proof,
}

/// An `rcases` pattern: a name, or the cases of an "or", `a | b`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Name(String),
    Or(Box<Pattern>, Box<Pattern>),
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
}

impl TacticArg {
    /// The argument with each term a letter, as a tactic's sample takes it
    /// (`Tactic::sample`).
    fn sample(&self) -> TacticArg {
        let a = || Term::letter("a", LeanType::Prop);
        match self {
            TacticArg::Term(_) => TacticArg::Term(a()),
            TacticArg::Using(_) => TacticArg::Using(a()),
            TacticArg::Setting { key, .. } => TacticArg::Setting {
                key,
                value: Box::new(Tactic::Call {
                    tactic: TacticRef::Mathlib("skip"),
                    args: Vec::new(),
                }),
            },
            TacticArg::Rules(rules) => TacticArg::Rules(
                rules
                    .iter()
                    .take(1)
                    .map(|r| Rule {
                        by: a(),
                        backwards: r.backwards,
                    })
                    .collect(),
            ),
            TacticArg::At(_) => {
                TacticArg::At(vec![Location::Hypothesis("h".to_string())])
            }
            TacticArg::Only | TacticArg::Flag(_) => self.clone(),
        }
    }
}

impl Proof {
    /// `Tactic::set_side` of every tactic and term of the proof.
    pub fn set_side(&mut self) {
        match self {
            Proof::Term(t) => t.set_side(),
            Proof::By(t) => t.set_side(),
            Proof::Block(ts) => {
                for t in ts {
                    t.set_side();
                }
            }
        }
    }
}

impl Tactic {
    /// Every tactic of the tree, this one first.
    pub fn walk(&self) -> Vec<&Tactic> {
        let mut out = vec![self];
        let mut i = 0;
        while i < out.len() {
            let node = out[i];
            match node {
                Tactic::First { ways: ts, .. } | Tactic::Seq(ts) => {
                    out.extend(ts.iter())
                }
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
                Tactic::Exact(_)
                | Tactic::Name { .. }
                | Tactic::Fact(_)
                | Tactic::Have { .. }
                | Tactic::Comment(_)
                | Tactic::Obtain { .. }
                | Tactic::Set { .. }
                | Tactic::Intro(_)
                | Tactic::Rcases { .. }
                | Tactic::Replace { .. }
                | Tactic::Induction { .. }
                | Tactic::Alternative(_)
                | Tactic::Calc { .. } => {}
            }
            i += 1;
        }
        out
    }

    /// The side tactic of sets, `parley_set_side`, wherever the side
    /// tactic stands, in the proofs and terms inside included: the proof
    /// is about sets, and its side conditions take their ways as well.
    pub fn set_side(&mut self) {
        match self {
            Tactic::Call { tactic, args } => {
                if *tactic == TacticRef::Bridge(BridgeTactic::Side) {
                    *tactic = TacticRef::Bridge(BridgeTactic::SetSide);
                }
                for a in args {
                    match a {
                        TacticArg::Term(t) | TacticArg::Using(t) => t.set_side(),
                        TacticArg::Setting { value, .. } => value.set_side(),
                        TacticArg::Rules(rules) => {
                            for r in rules {
                                r.by.set_side();
                            }
                        }
                        TacticArg::Only | TacticArg::Flag(_) | TacticArg::At(_) => {}
                    }
                }
            }
            Tactic::Exact(t)
            | Tactic::Fact(t)
            | Tactic::Name { term: t, .. }
            | Tactic::Set { value: t, .. }
            | Tactic::Rcases { from: t, .. }
            | Tactic::Induction { using: t, .. } => t.set_side(),
            Tactic::First { ways: ts, .. } | Tactic::Seq(ts) => {
                for t in ts {
                    t.set_side();
                }
            }
            Tactic::Group(t)
            | Tactic::Try(t)
            | Tactic::AllGoals(t)
            | Tactic::Bullet(t) => t.set_side(),
            Tactic::Have { says, proof, .. } | Tactic::Replace { says, proof, .. } => {
                says.set_side();
                proof.set_side();
            }
            Tactic::Obtain { says, from, .. } => {
                if let Some(s) = says {
                    s.set_side();
                }
                from.set_side();
            }
            Tactic::Calc { first, links } => {
                first.set_side();
                for l in links {
                    l.term.set_side();
                    if let Some(m) = &mut l.modulus {
                        m.set_side();
                    }
                    l.proof.set_side();
                }
            }
            Tactic::Comment(_) | Tactic::Intro(_) | Tactic::Alternative(_) => {}
        }
    }

    /// The tactic's own syntax with each term a letter, `linarith [a]`:
    /// what Lean is asked the modules of. None for a tactic of Lean's own
    /// or of the bridges, and for one made of others, whose own samples
    /// are taken.
    pub fn sample(&self) -> Option<String> {
        match self {
            Tactic::Call {
                tactic: tactic @ TacticRef::Mathlib(_),
                args,
            } => Some(
                Tactic::Call {
                    tactic: *tactic,
                    args: args.iter().map(TacticArg::sample).collect(),
                }
                .text(),
            ),
            Tactic::Set { ty, .. } => Some(
                Tactic::Set {
                    name: "a".to_string(),
                    ty: ty.clone(),
                    value: Term::letter("a", LeanType::Prop),
                    with: "h".to_string(),
                }
                .text(),
            ),
            _ => None,
        }
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
