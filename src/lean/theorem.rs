//! One theorem of the corpus written as a Lean theorem, step by step.
//!
//! Each step is a `have` whose type is the step's claim and whose proof is
//! what its method is in Lean (`LEAN.md`, "What each method becomes"). A
//! step that owns a block proves its claim by the block's steps, opened by
//! what the block's lines introduce. Tactics see every line above them, as
//! Mathlib's proofs do. A comment above each step says where it stands on
//! the page, and each line written records the step it was written for, so
//! that a line Lean refuses is reported against the page.

use indexmap::IndexMap;

use super::doc::bridges::{BridgeModule, BridgeTactic};
use super::doc::{ListReason, Tactic, TacticArg};
use super::expr::{LetterType, Printed, Writer};
use super::items::{Item, Sentence};
use super::names::{line_name, snake};
use super::statement::{binders, introduces, Asked, Binder};
use super::templates::Templates;
use crate::checker::record::{
    Cited, Contradicted, Facing, FirstAt, Negating, Supplied, SuppliedBy, Supposed,
    Unfolded,
};
use crate::checker::{CheckedCorpus, CheckedTheorem};
use crate::citing::Way;
use crate::corpus::{Head, Intro, Justification, Method, Step, Theorem};
use crate::formula::page::Written;
use crate::formula::Node;
use crate::notations::{BICONDITIONAL, CONDITIONAL, EQUALITY, IMPLICATION, ORDER};
use crate::outcome::Route;

/// A theorem's Lean declaration, and for each of its lines the place on
/// the page it was written for.
#[derive(Clone, Debug)]
pub struct LeanFile {
    pub decl: super::doc::file::Declaration,
    pub origins: Vec<Origin>,
    /// Where a citation's item writes a term in another form than the line
    /// it proves.
    pub forms: Vec<FormNote>,
}

/// A citation whose item, read as written, writes a term in another form
/// than the line it proves.
#[derive(Clone, Debug)]
pub struct FormNote {
    /// The line of the proof file the citation is on.
    pub page_line: usize,
    /// The item cited, by its full name.
    pub item: String,
    pub difference: super::doc::forms::FormDifference,
}

/// An item applied to what a citation gives it.
pub struct Instance {
    /// The item's declaration applied to its arguments, with the
    /// projection that takes the sentence: `(Decl (x := v) h).2`.
    pub term: super::expr::Printed,
    /// What it then says: the item's sentence with each letter put for by
    /// the value the citation gives it, to be compared with the line it
    /// proves.
    pub statement: super::expr::Printed,
}

/// A line of a proof as the writer pushes it, which may hold several of the
/// file's lines, and what it was written for; its line number is set where
/// the file is put together.
struct ProofLine {
    /// How deep in the proof's blocks it stands.
    depth: usize,
    tactic: Tactic,
    origin: Origin,
}

/// One sentence of a line the page can cite, with the Lean name of its
/// proof.
#[derive(Clone, Debug)]
struct LineSentence {
    /// Its place among the sentences the line writes, from 0, as the
    /// checker counts a cited line's sentences (`FirstAt::sentence`).
    at: usize,
    node: Node,
    /// The Lean name the sentence is proved under, a hypothesis or a
    /// `have`; None for one proved as a projection of another's, a sentence
    /// of a line that says several.
    name: Option<String>,
    /// The term that proves it: its name, or the projection, `hA1.2.1`.
    proof: Printed,
    /// What it says in Lean, as written where the line is stated
    /// (`Proof::stated`), so that every reading of the line reads it so;
    /// None where the writer there could not write it.
    says: Option<Printed>,
}

impl LineSentence {
    /// A sentence proved under the name `name`.
    fn named(at: usize, node: Node, name: String) -> LineSentence {
        LineSentence {
            at,
            node,
            proof: super::tactics::hyp(&name),
            name: Some(name),
            says: None,
        }
    }

    /// A line's one sentence.
    fn only(node: Node, name: String) -> LineSentence {
        LineSentence::named(0, node, name)
    }

    /// The sentence with the term that proves it.
    fn cited(&self) -> super::algebra::Cited {
        super::algebra::Cited {
            node: self.node.clone(),
            proof: self.proof.clone(),
            says: self.says.clone(),
        }
    }
}

/// How what a block owes is proved from its last step's lines
/// (`Proof::proved_from`).
enum Proved {
    /// By this term.
    Term(Printed),
    /// By the line `line`, once the goal and it are rewritten by Mathlib's
    /// lemmas `rules`.
    Simplified {
        rules: Vec<&'static str>,
        line: Printed,
    },
    /// By the line `line`, its casts and the goal's moved alike by `by`,
    /// once each is rewritten by the `set` equations its letters name
    /// (`forms::CastsApart`).
    Cast {
        apart: super::doc::forms::CastsApart,
        by: CastsBy,
        line: Printed,
    },
    /// By the line `line`, the two apart in casts the cast table does not
    /// say one tactic moves: both pushed down to the letters, where in one
    /// type they are one statement; where the line is in a narrower type
    /// (`CastsApart::lift`), it is then lifted to the goal's. Each side is
    /// first rewritten by the `set` equations its letters name, as
    /// `Proved::Cast` rewrites them.
    Unsettled {
        line: Printed,
        apart: super::doc::forms::CastsApart,
    },
}

/// The tactic that moves the casts of a line and a goal apart only in them,
/// by what the cast table says of both (`cast_proved`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CastsBy {
    /// `exact_mod_cast`: `norm_cast` moves every cast of both, and so
    /// brings them to one form, a line in a narrower type than the goal's
    /// among them.
    NormCast,
    /// `push_cast at h ⊢; exact h`: `push_cast` moves every cast of both to
    /// the letters and numerals and `norm_cast` does not, a numeral
    /// quotient among them, and neither is in a narrower type.
    PushCast,
}

/// The proof of `wanted` from `line`, which says `says`, the two apart only
/// in casts (`apart`): by whichever of `norm_cast` and `push_cast` the cast
/// table says moves every cast of both; by the ways tried in order where
/// neither does, or where only `push_cast` does and the line is in a
/// narrower type, which it does not lift.
fn cast_proved(
    apart: super::doc::forms::CastsApart,
    line: Printed,
    says: &Printed,
    wanted: &Printed,
) -> Option<Proved> {
    use super::casts::{norm_cast_moves_all, push_cast_moves_all_in_sides};
    let by = if norm_cast_moves_all(says) && norm_cast_moves_all(wanted) {
        CastsBy::NormCast
    } else if !apart.lift
        && push_cast_moves_all_in_sides(says)
        && push_cast_moves_all_in_sides(wanted)
    {
        CastsBy::PushCast
    } else {
        return Some(Proved::Unsettled { line, apart });
    };
    Some(Proved::Cast { apart, by, line })
}

impl Proved {
    /// The tactic that closes the goal by it: `exact` of a term.
    fn closer(&self) -> Tactic {
        use super::tactics as t;
        match self {
            Proved::Term(term) => Tactic::Exact(term.clone()),
            Proved::Simplified { rules, line } => {
                t::simpa_only(rules.clone(), line.clone())
            }
            // Casts the table does not say one tactic moves: both pushed down
            // to the letters, where in one type they are one statement; a
            // line in a narrower type is then lifted to the goal's. Lifting
            // where neither is narrower would read a division of casts one
            // way on one side and another on the other. A claim the pushing
            // works out is closed on the way.
            Proved::Unsettled { line, apart } => {
                let rewrite = |by: &[String], at: super::doc::Location| {
                    t::call(
                        "rw",
                        vec![
                            t::rules(by.iter().map(|e| t::hyp(e)).collect()),
                            TacticArg::At(vec![at]),
                        ],
                    )
                };
                let mut steps = Vec::new();
                if !apart.at_given.is_empty() {
                    steps.push(rewrite(
                        &apart.at_given,
                        super::doc::Location::Hypothesis("h".to_string()),
                    ));
                }
                if !apart.at_line.is_empty() {
                    steps.push(rewrite(&apart.at_line, super::doc::Location::Goal));
                }
                let last = match apart.lift {
                    true => t::exact_mod_cast(t::hyp("h")),
                    false => Tactic::Exact(t::hyp("h")),
                };
                steps.push(t::push_cast(Some(t::at_h(true))));
                steps.push(Tactic::AllGoals(Box::new(last)));
                t::on_h(line, steps)
            }
            // Each side rewritten by the `set` equations its letters name, and
            // then the casts moved by the tactic the cast table gives
            // (`CastsBy`).
            Proved::Cast { apart, by, line } => {
                let super::doc::TermKind::Letter(name) = &line.kind else {
                    return match by {
                        CastsBy::NormCast => t::exact_mod_cast(line.clone()),
                        CastsBy::PushCast => t::on_h(
                            line,
                            vec![
                                t::push_cast(Some(t::at_h(true))),
                                Tactic::Exact(t::hyp("h")),
                            ],
                        ),
                    };
                };
                let rewrite = |by: &[String], at: Vec<super::doc::Location>| {
                    t::call(
                        "rw",
                        vec![
                            t::rules(by.iter().map(|e| t::hyp(e)).collect()),
                            TacticArg::At(at),
                        ],
                    )
                };
                let mut steps = Vec::new();
                if !apart.at_given.is_empty() {
                    let at = vec![super::doc::Location::Hypothesis(name.clone())];
                    steps.push(rewrite(&apart.at_given, at));
                }
                if !apart.at_line.is_empty() {
                    steps.push(rewrite(
                        &apart.at_line,
                        vec![super::doc::Location::Goal],
                    ));
                }
                match by {
                    CastsBy::NormCast => steps.push(t::exact_mod_cast(line.clone())),
                    CastsBy::PushCast => {
                        let both = vec![
                            super::doc::Location::Hypothesis(name.clone()),
                            super::doc::Location::Goal,
                        ];
                        steps.push(t::push_cast(Some(TacticArg::At(both))));
                        steps.push(Tactic::Exact(line.clone()));
                    }
                }
                match steps.len() {
                    1 => steps.remove(0),
                    _ => Tactic::Seq(steps),
                }
            }
        }
    }

    /// As a term: a tactic's proof standing as `by t`.
    fn term(self) -> Printed {
        match self {
            Proved::Term(t) => t,
            other => super::tactics::by_term(super::doc::Proof::By(other.closer())),
        }
    }
}

/// The goal left once `intro` has taken `names` binders off it, as Lean
/// takes them: a "for all"'s letter, then its guard, `∀ j, 0 < j → P` to
/// `0 < j → P` and then P, and an "if", `A → B` to B. None where the goal
/// has fewer binders.
fn goal_after_intros(goal: &Printed, names: usize) -> Option<Printed> {
    use super::doc::{LeanType, Op, TermKind};
    let mut goal = goal.clone();
    let mut left = names;
    while left > 0 {
        let bare = match goal.kind {
            TermKind::Paren(inner) => *inner,
            _ => goal,
        };
        left -= 1;
        goal = match bare.kind {
            TermKind::Infix { op, rhs, .. } if op.symbol == "→" => *rhs,
            TermKind::Quantified {
                guard: Some(guard),
                body,
                ..
            } => Printed::infix(Op::of("→")?, *guard, *body, LeanType::Prop),
            TermKind::Quantified { body, .. } => *body,
            _ => return None,
        };
    }
    Some(goal)
}

/// The atoms `ring1` and `linarith` read a statement over: each greatest
/// part that is no sum, difference, product, quotient, negation, numeral,
/// cast or power to a natural exponent, as `push_cast` leaves the casts
/// (`casts::norm_cast_form`). `ring` normalises only the arithmetic between
/// atoms, and an atom is compared as it is written, so
/// `choose (m + 1 - 0) 1` and `choose (m + 1) 1` are two. The exponent of a
/// power is an atom unless it is a numeral.
fn ring_atoms(term: &Printed, out: &mut Vec<Printed>) {
    use super::doc::TermKind;
    match &term.kind {
        TermKind::Numeral(_) => {}
        // An instance's conditions met stand as `True` beside its statement,
        // `True ∧ L p ≤ U p`, whose parts `linarith` takes apart.
        _ if term.is_truth() => {}
        TermKind::Cast { inner, .. }
        | TermKind::Paren(inner)
        | TermKind::Neg(inner) => ring_atoms(inner, out),
        TermKind::Infix { op, lhs, rhs }
            if matches!(
                op.symbol,
                "+" | "-" | "*" | "/" | "=" | "≠" | "<" | ">" | "≤" | "≥" | "∧"
            ) =>
        {
            ring_atoms(lhs, out);
            ring_atoms(rhs, out);
        }
        // A natural exponent is arithmetic `ring` takes apart as well, x^(m
        // + n) as x^m·x^n: its atoms are the exponent's. An integer one,
        // Lean's integer power, `ring` keeps whole unless a numeral.
        TermKind::Infix { op, lhs, rhs } if op.symbol == "^" => {
            ring_atoms(lhs, out);
            let natural =
                rhs.ty == Some(super::doc::LeanType::Num(super::templates::Num::Nat));
            if natural {
                ring_atoms(rhs, out);
            } else if !matches!(
                super::casts::norm_cast_form(rhs).kind,
                TermKind::Numeral(_)
            ) {
                out.push(super::casts::norm_cast_form(rhs));
            }
        }
        _ => out.push(super::casts::norm_cast_form(term)),
    }
}

/// Whether the two statements are over the same atoms (`ring_atoms`), each
/// of the one alike one of the other with the `set` letters read as their
/// values and bound letters renamed (`forms::alike_once_set`), as Lean
/// takes them.
fn same_ring_atoms(
    one: &Printed,
    other: &Printed,
    values: &super::doc::forms::Values,
) -> bool {
    // Each read with its `toNat`s as `parley_norm` reads them.
    let (mut a, mut b) = (Vec::new(), Vec::new());
    ring_atoms(&to_nat_read(one), &mut a);
    ring_atoms(&to_nat_read(other), &mut b);
    let within = |xs: &[Printed], ys: &[Printed]| {
        xs.iter().all(|x| {
            ys.iter()
                .any(|y| super::doc::forms::alike_once_set(x, y, values))
        })
    };
    within(&a, &b) && within(&b, &a)
}

/// The casts a statement as Lean writes it takes, each by its text, a cast
/// of a term to its own type left out, in order.
fn cast_texts(term: &Printed) -> Vec<String> {
    term.walk()
        .into_iter()
        .filter(|t| match &t.kind {
            super::doc::TermKind::Cast { inner, to } => inner.ty.as_ref() != Some(to),
            _ => false,
        })
        .map(|t| t.untyped().text())
        .collect()
}

/// How the checker met one conclusion of a citation with the claim.
#[derive(Clone, Copy)]
struct HowMet<'m> {
    /// Which way the item's equation faces the claim (`Cited::facings`).
    facing: Option<Facing>,
    /// What was taken to meet them: identities dropped, parts paired out of
    /// their places (`Cited::meetings`).
    meeting: Option<&'m crate::matching::Meeting>,
}

/// An equation a substitution puts in that no line says, as Lean has it:
/// a row's change, proved by its reason, `c2 : 3 * 3 + 3 = 12`, put into
/// the row above (`SubstitutedInto::RowAbove`); or a step's own equation,
/// worked out by arithmetic or a define's, put where the record says.
struct GivenEquation {
    /// The equation, its proof and what Lean states for it.
    change: super::algebra::Cited,
    /// The row above, by its name and what it says, for a row's change.
    above: Option<super::algebra::Cited>,
}

/// The claim a citation is met with, as Lean prints it.
#[derive(Clone, Copy)]
struct StepClaim<'p> {
    printed: &'p Printed,
    /// Whether it is the `have` the step states, which shows the form its
    /// counts are in; a claim printed afresh does not.
    stated: bool,
}

/// How an item's statement at a citation's values reads as the claim where
/// the item is stated over more than its values are in, as the record's
/// `Cited::item_letters` say: the lemmas `simpa only` takes it by, or the
/// cast `exact_mod_cast` moves.
#[derive(Clone, Debug, PartialEq, Eq)]
enum CitedBridge {
    Rules(Vec<&'static str>),
    Cast,
}

/// The bridge the record's `item_letters` give a citation of `sentence`
/// (`CitedBridge`); None where every letter's value is in what the item
/// takes it in. Each row is a Lean fact, checked in `CloserTable.lean`:
/// - a set letter given ℕ or ℕ₀, `m ∈ {n : ℤ | 0 < n}` for `0 < m`:
///   `Set.mem_ofPred_eq`, and `Set.mem_sep_iff` for a set-builder over it;
/// - a set letter given a whole type, `∀ x ∈ Set.univ` for `∀ x`:
///   `Set.mem_univ`, `true_implies`;
/// - an item over any ring at integers, ℕ₀ said `∃ m : ℤ, 0 ≤ m ∧ m = n`:
///   `Int.cast_id`, `exists_eq_right`;
/// - an item stated in ℂ at reals, or in ℝ at rationals: the cast,
///   `Complex.ofReal_*` and `Rat.cast_*`, by `exact_mod_cast`.
fn cited_bridge(cited: &Cited, sentence: &Sentence, at: &Cites) -> Option<CitedBridge> {
    use super::templates::Num;
    use crate::rules::System;
    // A claim naming a letter a `set` gives, `b ∈ T`, reads as the item
    // only once the letter is its value, which `simpa only` does not do.
    if at.names_set_letter {
        return None;
    }
    let mut rules: Vec<&'static str> = Vec::new();
    // A set letter given a number system: the set-builder, the system as a
    // set, and `Set.univ` read as membership, all at once, as one step may
    // ask several (`t ∈ {t ∈ Set.univ | P t}`).
    // Only where the item's sentence reads each such letter as a set its
    // members belong to (`read_as_members`): the lemmas read membership,
    // and an image `f '' (X ∩ Y)` they leave as it stands.
    let sets: Vec<_> = cited
        .item_letters
        .iter()
        .filter(|l| l.value_set.is_some())
        .collect();
    if !sets.is_empty() {
        if !sets
            .iter()
            .all(|l| read_as_members(&sentence.says, l.letter))
        {
            return None;
        }
        rules.extend([
            "Set.mem_sep_iff",
            "Set.mem_ofPred_eq",
            "Set.mem_univ",
            "Filter.univ_mem",
            "true_and",
            "true_implies",
        ]);
    }
    // An item over any ring at integers, where the claim is a membership of
    // ℕ or ℕ₀, which the item says `∃ m : ℤ, 0 ≤ m ∧ (m : ℤ) = n`.
    let integers = cited
        .item_letters
        .iter()
        .filter_map(|l| l.value_system)
        .all(|v| v.within(System::Z));
    if sentence.general.is_some() && integers && at.claims_natural {
        rules.extend(["Int.cast_id", "exists_eq_right"]);
    }
    rules.sort_unstable();
    rules.dedup();
    if !rules.is_empty() {
        return Some(CitedBridge::Rules(rules));
    }
    // An item stated in ℂ for a claim Lean states in ℝ, or in ℝ for one in
    // ℚ, the item's letters at values of the claim's field: the cast.
    // `norm_cast` moves a cast out through a function only of a cast,
    // `Complex.exp ↑x` to `↑(Real.exp x)`: a value that is a numeral alone,
    // `Complex.exp 1`, stands at the wider type with no cast to move, so
    // each widened letter's value is one with a letter in it.
    let mut widened = false;
    for l in &cited.item_letters {
        if matches!(
            (l.item_system, l.value_system),
            (Some(System::C | System::R), Some(v)) if Some(v) != l.item_system
        ) {
            if cited
                .binding
                .get(&l.letter)
                .is_none_or(|v| v.names().is_empty())
            {
                return None;
            }
            widened = true;
        }
    }
    let crossed = matches!(
        at.types,
        (Some(Num::Complex), Some(Num::Real)) | (Some(Num::Real), Some(Num::Rat))
    );
    (sentence.general.is_none() && widened && crossed && at.casts_move)
        .then_some(CitedBridge::Cast)
}

/// Whether every place `says` names the letter `set` is the set something
/// belongs to: of `x ∈ X`, `for all x ∈ X`, `there is x ∈ X` or
/// `{t ∈ X | P}`, each of which holds it second.
fn read_as_members(says: &Node, set: crate::formula::symbol::Symbol) -> bool {
    use crate::notations::{FOR_ALL, MEMBERSHIP, SET_BUILDER, THERE_IS};
    let holds = matches!(
        says.notation(),
        MEMBERSHIP | FOR_ALL | THERE_IS | SET_BUILDER
    );
    says.children.iter().enumerate().all(|(i, c)| {
        if c.is_name() && c.text == set {
            holds && i == 1
        } else {
            read_as_members(c, set)
        }
    })
}

/// What a citation's claim says that `cited_bridge` reads: the page's claim
/// and the two statements as the writer states them.
struct Cites {
    /// The claim names a letter a `set` gives.
    names_set_letter: bool,
    /// The claim is a membership of ℕ or ℕ₀.
    claims_natural: bool,
    /// The number types the item's statement and the claim are stated in.
    types: (Option<super::templates::Num>, Option<super::templates::Num>),
    /// The cast table says `norm_cast` moves every cast of both
    /// (`casts::norm_cast_moves_all`).
    casts_move: bool,
}

impl Cites {
    fn of(
        node: &Node,
        says: Option<&Printed>,
        claim: Option<&Printed>,
        values: &super::doc::forms::Values,
    ) -> Cites {
        use super::doc::LeanType;
        let num =
            |t: Option<&Printed>| match t.and_then(super::doc::forms::relation_type) {
                Some(LeanType::Num(n)) => Some(n),
                _ => None,
            };
        let names_set_letter =
            node.names().iter().any(|n| values.contains_key(n.as_str()));
        let claims_natural = node.notation() == crate::notations::MEMBERSHIP
            && node.children.get(1).is_some_and(|set| {
                set.notation() == crate::notations::NUMBER_SYSTEMS
                    && matches!(
                        crate::rules::System::of_sign(&set.text),
                        Some(crate::rules::System::N | crate::rules::System::N0)
                    )
            });
        let moves =
            |t: Option<&Printed>| t.is_some_and(super::casts::norm_cast_moves_all);
        Cites {
            names_set_letter,
            claims_natural,
            types: (num(says), num(claim)),
            casts_move: moves(says) && moves(claim),
        }
    }
}

/// The tactic that reads an item's Lean statement, `item`, as the step's
/// spelling of it, `written`: `parley_instance` where the two are worked in
/// one field, the widest each names (a side's type the writer does not know
/// is no difference; a narrower field the item names, a value of ℚ cast to
/// ℝ, is cast down as `push_cast` takes it); `parley_instance_real` where
/// the item is in ℝ and the step in ℚ alone, which is lifted to ℝ;
/// `parley_instance_cast` where the item is in another wider type, ℂ at
/// reals or ℝ at integers, whose casts are lifted out to the step's.
fn instance_bridge(item: &Printed, written: &Printed) -> BridgeTactic {
    use super::templates::Num;
    let (of_item, of_step) = (fields_of(item), fields_of(written));
    let real_at_rationals = of_step == std::collections::BTreeSet::from([Num::Rat])
        && of_item.contains(&Num::Real)
        && !of_item.contains(&Num::Complex);
    let one_field = of_item.last() == of_step.last();
    match (one_field, real_at_rationals) {
        (true, _) => BridgeTactic::Instance,
        (false, true) => BridgeTactic::InstanceReal,
        (false, false) => BridgeTactic::InstanceCast,
    }
}

/// Whether the statement raises to a complex exponent, `↑x ^ ↑y` in ℂ: that
/// power is the real one only at a base not negative, a fact no cast moves,
/// so an item in ℂ written with one is not read at reals.
fn complex_exponent(term: &Printed) -> bool {
    use super::doc::{LeanType, Op, TermKind};
    let complex = Some(LeanType::Num(super::templates::Num::Complex));
    term.walk().iter().any(|t| {
        matches!(&t.kind, TermKind::Infix { op, rhs, .. }
            if *op == Op::POWER && rhs.ty == complex)
    })
}

/// Whether the step's lines' writing of an item's part, `written`, and Lean's
/// statement of it, `said`, are one statement: written alike and naming the
/// same number types. An item with no letter is stated in one type,
/// `(abs 0 : ℤ) = 0`, which a calculation's row in ℝ writes alike, and the
/// two are then read one as the other by the bridge.
fn one_statement(written: &Printed, said: &Printed) -> bool {
    super::doc::forms::written_alike(written, said)
        && number_types(written) == number_types(said)
}

/// How many integer powers the statement writes under its binders, x^(m − k)
/// in a sum over k, whose exponent's fact holds only there: two statements
/// of one fact that write as many have spelt each such power alike, none
/// taken to `toNat` on one side alone, which `parley_instance` does not join.
fn integer_powers_under_binders(term: &Printed) -> usize {
    use super::doc::{LeanType, Op, TermKind};
    let int = Some(LeanType::Num(super::templates::Num::Int));
    match &term.kind {
        TermKind::Quantified { .. }
        | TermKind::Bound { .. }
        | TermKind::Lambda { .. } => term
            .walk()
            .iter()
            .filter(|t| {
                matches!(&t.kind, TermKind::Infix { op, rhs, .. }
                    if *op == Op::POWER && rhs.ty == int)
            })
            .count(),
        _ => term
            .children()
            .into_iter()
            .map(integer_powers_under_binders)
            .sum(),
    }
}

/// The statement with each `toNat` read as `parley_norm` reads it, by the
/// table of Lean facts it takes them apart by:
/// - of numerals alone, the numeral it works out to (`Int.reduceToNat`),
///   `(2 : ℤ).toNat` as `2`;
/// - of a sum, the sum of the parts' (`Int.toNat_add`), and of a product,
///   the product of the parts' (`Int.toNat_mul`);
/// - of a natural number written in ℤ, that number (`casts::as_natural`,
///   `Int.toNat_natCast`).
///
/// The writer writes `(t).toNat` only of a term the said-once rule puts in
/// ℕ₀ (`Writer::said_whole`), which puts a sum or a product there by its
/// parts: the facts 0 ≤ a and 0 ≤ b these two ask hold, and `omega` reads
/// them in `parley_norm`. A difference's `toNat` stays whole: subtraction in
/// ℕ stops at 0.
fn to_nat_read(term: &Printed) -> Printed {
    use super::doc::{LeanType, TermKind};
    use super::templates::Num;
    let mut out = term.clone();
    for c in out.children_mut() {
        *c = to_nat_read(c);
    }
    let TermKind::ToNat(inner) = &out.kind else {
        return out;
    };
    if let Some(natural) = super::casts::as_natural(inner) {
        return natural;
    }
    if !inner.lettered() {
        return super::doc::forms::ascriptions_dropped(inner);
    }
    match &super::doc::forms::ascriptions_dropped(inner).kind {
        TermKind::Infix { op, lhs, rhs } if matches!(op.symbol, "+" | "*") => {
            let part = |p: &Printed| {
                to_nat_read(&Printed::of(
                    TermKind::ToNat(Box::new(p.clone())),
                    LeanType::Num(Num::Nat),
                ))
            };
            Printed::infix(*op, part(lhs), part(rhs), LeanType::Num(Num::Nat))
        }
        _ => out,
    }
}

/// The `toNat`s a statement as Lean writes it takes, each by its text, in
/// order, read as `parley_norm` reads them (`to_nat_read`), with no
/// ascription of a term to its own type and its bound letters renamed in
/// order (`forms::bound_renamed`).
fn to_nat_texts(term: &Printed) -> Vec<String> {
    use super::doc::TermKind;
    let read = super::doc::forms::bound_renamed(
        &super::doc::forms::ascriptions_dropped(&to_nat_read(term)),
    );
    read.walk()
        .into_iter()
        .filter(|t| match &t.kind {
            TermKind::ToNat(inner) => inner.lettered(),
            _ => false,
        })
        .map(|t| t.untyped().text())
        .collect()
}

/// The writer's conversion that takes a statement worked in a wider field
/// than the claim's down to it, the widest it names beyond the claim's:
/// `parley_of_complex` of ℂ, `parley_rat_of_real` of ℝ for a claim in ℚ.
/// None where it names no wider field.
fn read_down(says: &Printed, claim: &Printed) -> Option<BridgeTactic> {
    use super::templates::Num;
    let claimed = fields_of(claim);
    let wider = fields_of(says)
        .into_iter()
        .filter(|n| !claimed.contains(n))
        .max();
    match wider {
        Some(Num::Complex) => Some(BridgeTactic::OfComplex),
        Some(Num::Real) => Some(BridgeTactic::RatOfReal),
        _ => None,
    }
}

/// The fields a statement as Lean writes it is worked in, ℚ, ℝ or ℂ, of
/// its number types (`number_types`): an exponent's ℕ or an index's ℤ
/// beside them says nothing of the field.
fn fields_of(term: &Printed) -> std::collections::BTreeSet<super::templates::Num> {
    use super::templates::Num;
    number_types(term)
        .into_iter()
        .filter(|n| matches!(n, Num::Rat | Num::Real | Num::Complex))
        .collect()
}

/// The number types a statement as Lean writes it names: those of its
/// terms, and those it casts to.
fn number_types(term: &Printed) -> std::collections::BTreeSet<super::templates::Num> {
    use super::doc::{LeanType, TermKind};
    let mut out = std::collections::BTreeSet::new();
    for t in term.walk() {
        if let Some(LeanType::Num(n)) = &t.ty {
            out.insert(*n);
        }
        if let TermKind::Cast {
            to: LeanType::Num(n),
            ..
        } = &t.kind
        {
            out.insert(*n);
        }
    }
    out
}

/// Lean's statement of a "for all" line once each of its leading letters is
/// given its value (`lean_instance`).
struct LeanInstance {
    /// Each condition taken off, outermost first, at the values.
    conditions: Vec<Printed>,
    /// What is left once they are.
    left: Printed,
}

/// What Lean's statement of a "for all" line, `line`, says once each of its
/// leading letters is given its value of `given` in order, a guard's proof
/// after a value that has one, and then `conditions` of its conditions'
/// proofs: each letter put as its value wherever it stands, a cast of it a
/// cast of the value, `↑1` of `↑x` at x := 1, as Lean instantiates it.
/// Declined where the statement has fewer binders or conditions.
fn lean_instance(
    line: &Printed,
    given: &[(Printed, bool)],
    conditions: usize,
) -> Route<LeanInstance> {
    use super::doc::TermKind;
    let bare = |t: Printed| match t.kind {
        TermKind::Paren(inner) => *inner,
        _ => t,
    };
    let arrow_rhs = |t: Printed| match bare(t).kind {
        TermKind::Infix { op, rhs, .. } if op.symbol == "→" => Some(*rhs),
        _ => None,
    };
    let mut at = line.clone();
    let mut values = std::collections::BTreeMap::new();
    for (value, guarded) in given {
        let TermKind::Quantified {
            letter,
            guard,
            body,
            ..
        } = bare(at).kind
        else {
            return Route::no("a line Lean states with fewer letters than are given");
        };
        values.insert(letter, value.clone());
        at = *body;
        // A guard Lean writes as a condition of the body, `0 < x → P`.
        if *guarded && guard.is_none() {
            at = match arrow_rhs(at) {
                Some(rest) => rest,
                None => return Route::no("a guarded letter Lean states with no guard"),
            };
        }
    }
    let mut taken = Vec::new();
    for _ in 0..conditions {
        let TermKind::Infix { op, lhs, rhs } = bare(at).kind else {
            return Route::no("a line Lean states with fewer conditions");
        };
        if op.symbol != "→" {
            return Route::no("a line Lean states with fewer conditions");
        }
        taken.push(super::doc::forms::substituted_all(&lhs, &values));
        at = *rhs;
    }
    Route::Built(LeanInstance {
        conditions: taken,
        left: super::doc::forms::substituted_all(&at, &values),
    })
}

/// What turns Lean's bound for a membership of ℕ or ℕ₀, `0 < x` or `0 ≤ x`,
/// into the fact the lemma `lemma` says of it (`rules::IMPLIED`): the bound
/// itself, None, or the field of it that says the fact, `ne'` for `x ≠ 0`.
/// None for a lemma not in that table.
fn system_fact_field(lemma: &str) -> Option<Option<&'static str>> {
    match lemma {
        "nngt0" | "nnge1" | "nn0ge0" => Some(None),
        "nnne0" => Some(Some("ne'")),
        _ => None,
    }
}

/// `_`: an argument Lean fills from what the term is used as.
fn elided_term() -> Printed {
    Printed {
        kind: super::doc::TermKind::Elided,
        ty: None,
    }
}

/// A hypothesis applied to arguments by place, `hD1 j h`.
fn hyp_applied(hyp: &str, args: Vec<Printed>) -> Printed {
    Printed {
        kind: super::doc::TermKind::App {
            head: Box::new(super::tactics::hyp(hyp)),
            args: args.into_iter().map(super::doc::Arg::Explicit).collect(),
            explicit: false,
        },
        ty: None,
    }
}

/// The bounds a range line gives, `x ∈ Finset.Icc a b` proved by `proof`:
/// `a ≤ x` and `x ≤ b`, by `Finset.mem_Icc`; none for any other line.
fn range_bounds(says: &Printed, proof: &Printed) -> Vec<(Printed, Printed)> {
    use super::doc::{Arg, LeanType, Op, Source, TermKind};
    let TermKind::Infix { op, lhs, rhs } = &says.kind else {
        return Vec::new();
    };
    let TermKind::App { head, args, .. } = &rhs.kind else {
        return Vec::new();
    };
    let (true, TermKind::Const(c), [Arg::Explicit(a), Arg::Explicit(b)]) =
        (op.symbol == "∈", &head.kind, args.as_slice())
    else {
        return Vec::new();
    };
    if c.name != "Finset.Icc" {
        return Vec::new();
    }
    let both = Printed::applied(
        "Finset.mem_Icc.mp",
        Source::Mathlib,
        vec![proof.clone()],
        LeanType::Prop,
    );
    let side = |field: &str| Printed {
        kind: TermKind::Field {
            inner: Box::new(super::tactics::bracket(both.clone())),
            field: field.to_string(),
        },
        ty: Some(LeanType::Prop),
    };
    let at_most = |l: &Printed, r: &Printed| {
        Printed::infix(Op::AT_MOST, l.clone(), r.clone(), LeanType::Prop)
    };
    vec![(side("1"), at_most(a, lhs)), (side("2"), at_most(lhs, b))]
}

/// The parts of a sentence's "and" as the page writes it, `node`, each as
/// Lean writes it, `says` taken apart alike, with the term that proves the
/// part where `proof` proves the whole, `.1` and `.2` as it nests; a part
/// of a truth has none.
fn and_leaves(
    node: &Node,
    says: &Printed,
    proof: Option<Printed>,
    out: &mut Vec<(Printed, Option<Printed>)>,
) {
    match (page_and(node), and_sides(says)) {
        (Some((nl, nr)), Some((l, r))) => {
            let side = |field: &str| {
                proof
                    .clone()
                    .map(|p| fields(super::tactics::bracket(p), &[field]))
            };
            and_leaves(nl, &l, side("1"), out);
            and_leaves(nr, &r, side("2"), out);
        }
        _ => out.push((says.clone(), proof)),
    }
}

/// The two sides of an "and" the page writes; None for another sentence.
fn page_and(node: &Node) -> Option<(&Node, &Node)> {
    match (node.notation(), node.children.as_slice()) {
        (crate::notations::CONJUNCTION, [l, r]) => Some((l, r)),
        _ => None,
    }
}

/// The proof of `owe`, the sentence `node`, from the proofs of its parts in
/// order, `⟨a, b⟩` as the page's "and" nests (`and_leaves`); None where
/// too few are left.
fn assembled_as(
    node: &Node,
    owe: &Printed,
    proofs: &mut impl Iterator<Item = Proved>,
) -> Option<Proved> {
    match (page_and(node), and_sides(owe)) {
        (Some((nl, nr)), Some((l, r))) => {
            let a = assembled_as(nl, &l, proofs)?.term();
            let b = assembled_as(nr, &r, proofs)?.term();
            Some(Proved::Term(super::expr::anonymous(vec![a, b])))
        }
        _ => proofs.next(),
    }
}

/// `trivial`, the proof of `True`.
fn trivial() -> Printed {
    Printed::constant(
        "trivial",
        super::doc::Source::Core,
        super::doc::LeanType::Prop,
    )
}

/// A proof of `says` turned round: `Ne.symm` of a denied equation, and
/// `.symm` of an equation, a congruence or an "if and only if".
fn turned_proof(proof: Printed, says: &Printed) -> Printed {
    match super::doc::forms::denies_equation(says) {
        true => Printed::applied(
            "Ne.symm",
            super::doc::Source::Core,
            vec![proof],
            super::doc::LeanType::Prop,
        ),
        false => super::tactics::symm(proof),
    }
}

/// A proof of an equation or congruence used the way the checker found it
/// faces the claim (`record::Facing`): as it stands, or `.symm`.
fn faced(proof: Printed, facing: Facing) -> Printed {
    match facing {
        Facing::Straight => proof,
        Facing::Turned => super::tactics::symm(proof),
    }
}

/// The facing of a meeting the checker records as turned or not
/// (`matching::Meeting::turned`).
fn facing_of_turned(turned: bool) -> Facing {
    match turned {
        true => Facing::Turned,
        false => Facing::Straight,
    }
}

/// Mathlib's rewrite that drops an identity element the checker dropped
/// (`matching::Dropped`): `add_zero` of x + 0, `zero_add` of 0 + x, and so
/// for the other operations; None for one it has no rewrite of.
fn identity_lemma(d: &crate::matching::Dropped) -> Option<&'static str> {
    Some(match (d.literal.as_str(), d.hole) {
        ("+", 0) => "zero_add",
        ("+", 1) => "add_zero",
        ("−", 1) => "sub_zero",
        ("·", 0) => "one_mul",
        ("·", 1) => "mul_one",
        ("/", 1) => "div_one",
        (_, 1) if d.operation == "power" => "pow_one",
        _ => return None,
    })
}

/// The two sides of an "and", as Lean writes it: `a ∧ b`, bracketed or
/// not; of several sentences, which group to the right, the first and the
/// rest.
fn and_sides(term: &Printed) -> Option<(Printed, Printed)> {
    use super::doc::{Op, TermKind};
    match &term.kind {
        TermKind::Paren(inner) => and_sides(inner),
        TermKind::Infix { op, lhs, rhs } if *op == Op::AND => {
            Some(((**lhs).clone(), (**rhs).clone()))
        }
        _ => None,
    }
}

/// What a block, a part of one or a theorem owes at its end
/// (`Proof::closing`).
enum Owing<'a> {
    /// The record's sentences as the page writes them (`Owed::written`);
    /// None, or none, for a block that ends on a contradiction.
    Written(Option<&'a [Node]>),
    /// The goal as Lean has it, where Lean makes it itself: an induction's
    /// motive at its start or at the next value, `goal`, with the record's
    /// sentences it says (`nodes`), whose "and" the parts are split by.
    Lean {
        nodes: Option<&'a [Node]>,
        goal: Vec<Printed>,
    },
}

/// What ends a block, a part of one or a theorem (`Proof::closing`).
enum Closing {
    /// Its last step, by name, says what is owed as Lean writes it: the
    /// step's proof proves the goal.
    Last(String),
    /// A tactic that closes the goal.
    Tactic(Box<Tactic>),
    /// Nothing: the last step, shown impossible, closed it.
    Closed,
}

/// A proof given as an argument: a line's name or `(by parley_side)`.
fn proof_arg(proof: super::expr::Printed) -> super::doc::Arg {
    super::doc::Arg::Explicit(proof)
}

/// The module a declaration's full name is in, `Parley.Items.Stdlib.Counting`
/// of `Parley.Items.Stdlib.Counting.mun_card_singleton`.
fn module_of_decl(decl: &str) -> String {
    match decl.rsplit_once('.') {
        Some((module, _)) => module.to_string(),
        None => decl.to_string(),
    }
}

/// Where a line of a Lean file comes from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Origin {
    /// The line of the Lean file, from 1.
    pub line: usize,
    /// The line of the proof file it was written for.
    pub page_line: usize,
    /// What it was written for.
    pub spot: Spot,
}

/// What a line of a Lean file was written for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Spot {
    /// The theorem's statement, or a line of the file around it.
    Statement,
    /// A step, by its number as the page writes it.
    Step(String),
}

/// What writing a theorem reads: the corpus as checked, the notations and
/// items in Lean, and the theorems of the corpus as items in Lean.
pub struct Sources<'a> {
    pub checked: &'a CheckedCorpus,
    pub templates: &'a Templates,
    /// What each notation is to the methods' decisions, which `algebra`
    /// asks for its multipliers.
    pub targets: &'a crate::methods::terms::Targets,
    /// Every item a citation may name that has a Lean form, by full name:
    /// the library's records and the corpus's theorems.
    pub items: &'a IndexMap<String, Item>,
    /// What the checker matches terms with, its identity elements among
    /// them, so that a step is read as the checker decided it.
    pub ctx: &'a crate::matching::Context,
}

/// The terms a theorem puts in a hole of type ℝ, the A/B of ⌊A/B⌋ (set.mm's
/// floor being of reals), as the page prints them: each is a real wherever
/// the theorem writes it, so that a line about it meets the floor's.
fn held_real(rec: &CheckedTheorem, writer: &Writer) -> Vec<String> {
    let mut out = Vec::new();
    for (_, node) in rec.page.entries() {
        for n in node.walk() {
            // A letter has its own type; a term of numerals alone, the 2 of
            // √2, takes the type of where it stands.
            for arg in writer.always_real_args(&n) {
                let printed = writer.grammar.print(arg);
                let of_letters = arg.walk().iter().any(|m| m.is_name());
                if !arg.is_name() && of_letters && !out.contains(&printed) {
                    out.push(printed);
                }
            }
        }
    }
    out
}

/// Why a function a proof defines whose values are sets, I(k) = {|x| : x ∈
/// 𝒫{1, …, k}}, is not written: the writer types a function letter as one
/// into numbers only.
pub const SET_VALUED: &str = "a function a proof defines whose values are sets";

/// Whether the checker reads the name a proof defines as a function whose
/// values are sets.
pub fn set_valued(rec: &CheckedTheorem, name: &str) -> bool {
    matches!(
        rec.sorts.get(name).and_then(|s| s.full()),
        Some(crate::formula::Whole::Function(_, to))
            if matches!(**to, crate::formula::Whole::Set(_))
    )
}

/// The record the writer reads: the checker's with what the theorem's file
/// defines outside it written out (`CheckedTheorem::written`), or as read
/// where it defines nothing so.
pub fn as_written(rec: &CheckedTheorem) -> &CheckedTheorem {
    rec.written.as_deref().unwrap_or(rec)
}

/// The theorem as an item of the library: its statement's binders, and its
/// `then` sentences joined into one Lean statement, each taken by its
/// projection.
pub fn as_item(sources: &Sources, thm: &Theorem, rec: &CheckedTheorem) -> Route<Item> {
    let rec = as_written(rec);
    let mut writer = Writer::new(&sources.checked.grammar, sources.templates);
    writer.reals = held_real(rec, &writer);
    writer.finite_from(&rec.said_finite);
    writer.bounds = rec.statement_bounds.clone();
    writer.whole_bounds = rec.statement_bounds.clone();
    let stated = match statement(&mut writer, thm, rec) {
        Route::Built(s) => s,
        Route::Declined(d) => return Route::Declined(d),
    };
    let module = super::names::module_of(&thm.qualified());
    let decl = format!("{module}.{}", snake(&thm.name));
    let n = stated.conclusion.len();
    let mut written: Vec<Node> = hypothesis_sentences(thm, rec)
        .into_iter()
        .flat_map(|(_, s)| s.into_iter().map(|s| s.node))
        .collect();
    written.extend(stated.conclusion.iter().map(|c| c.says.clone()));
    let mut arithmetic = super::readback::page_arithmetic(&writer, &written);
    for (op, n) in recursion_arithmetic(&writer, thm, rec) {
        *arithmetic.entry(op).or_insert(0) += n;
    }
    let sentences = stated
        .conclusion
        .into_iter()
        .enumerate()
        .map(|(i, c)| Sentence {
            decl: decl.clone(),
            binders: stated.binders.clone(),
            says: c.says,
            prop: c.prop,
            part: projection_path(i, n),
            arithmetic: arithmetic.clone(),
            general: None,
            domains: writer.domains.clone(),
        })
        .collect();
    Route::Built(Item {
        module,
        sentences,
        proofs: Vec::new(),
    })
}

/// The parts of an "and" as its tree nests them, in order: ((A ∧ B) ∧ C)
/// gives A, B, C; anything else is one part.
fn and_parts(node: &Node) -> Vec<&Node> {
    match (node.notation(), node.children.as_slice()) {
        (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [l, r],
        ) => {
            let mut out = and_parts(l);
            out.extend(and_parts(r));
            out
        }
        _ => vec![node],
    }
}

/// The projection that takes part `i` of an "and" as its tree nests it,
/// `.1.2` for B of ((A ∧ B) ∧ C); None where it has no part `i`.
fn leaf_path(node: &Node, i: usize) -> Option<Vec<&'static str>> {
    match (node.notation(), node.children.as_slice()) {
        (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [l, r],
        ) => {
            let left = and_parts(l).len();
            let (side, rest) = match i < left {
                true => ("1", leaf_path(l, i)),
                false => ("2", leaf_path(r, i - left)),
            };
            rest.map(|mut path| {
                path.insert(0, side);
                path
            })
        }
        _ => (i == 0).then(Vec::new),
    }
}

/// A recursion's rules as one hypothesis: its starts, then for every k
/// from 0 its steps, `F 0 = a ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = b`.
fn rules_said(k: &str, starts: Vec<Printed>, steps: Vec<Printed>) -> Printed {
    use super::doc::{LeanType, Op};
    let int = LeanType::Num(super::templates::Num::Int);
    let from_0 = Printed::infix(
        Op::AT_MOST,
        Printed::numeral("0", int.clone()),
        super::tactics::hyp(k),
        LeanType::Prop,
    );
    let every = Printed::of(
        super::doc::TermKind::Quantified {
            quant: super::doc::Quant::ForAll,
            letter: k.to_string(),
            letter_ty: int,
            guard: Some(Box::new(from_0)),
            body: Box::new(conjunction(steps).unwrap_or_else(Printed::truth)),
            bounded: false,
        },
        LeanType::Prop,
    );
    // One chain to the right, the starts and then the steps' "for all",
    // `F 0 = a ∧ G 0 = b ∧ ∀ k : ℤ, …`, whose projections take each.
    let mut parts = starts;
    parts.push(every);
    conjunction(parts).unwrap_or_else(Printed::truth)
}

/// The parts joined by `∧`, which chains to the right; None of no parts.
fn conjunction(parts: Vec<Printed>) -> Option<Printed> {
    parts.into_iter().rev().reduce(|right, left| {
        Printed::infix(super::doc::Op::AND, left, right, super::doc::LeanType::Prop)
    })
}

/// Whether the statement applies a function to a numeral, through brackets
/// and casts: `Complex.cos 0`.
fn function_of_numeral(statement: &Printed) -> bool {
    use super::doc::{Arg, TermKind};
    fn bare(t: &Printed) -> &Printed {
        match &t.kind {
            TermKind::Paren(inner) | TermKind::Cast { inner, .. } => bare(inner),
            _ => t,
        }
    }
    statement.walk().iter().any(|t| {
        let TermKind::App { args, .. } = &t.kind else {
            return false;
        };
        args.iter().any(|a| match a {
            Arg::Explicit(v) | Arg::Named { value: v, .. } => {
                matches!(bare(v).kind, TermKind::Numeral(_))
            }
        })
    })
}

/// Whether the term holds a cast whose term, through brackets, is a
/// `toNat`: `((2^p − 1).toNat : ℤ)`.
fn casts_a_to_nat(term: &Printed) -> bool {
    use super::doc::TermKind;
    fn bare(t: &Printed) -> &Printed {
        match &t.kind {
            TermKind::Paren(inner) => bare(inner),
            _ => t,
        }
    }
    term.walk().iter().any(|t| {
        matches!(&t.kind, TermKind::Cast { inner, .. }
            if matches!(bare(inner).kind, TermKind::ToNat(_)))
    })
}

/// Lean's lemma `name` applied to `args`, a proof.
fn applied(name: &str, args: Vec<super::doc::Arg>) -> Printed {
    Printed {
        kind: super::doc::TermKind::App {
            head: Box::new(super::tactics::lemma(name)),
            args,
            explicit: false,
        },
        ty: Some(super::doc::LeanType::Prop),
    }
}

/// `start` with `letter` put at each of `places`, each a path of children
/// from the top (`matching::SubstitutionPlaces`); a path that leads nowhere
/// puts nothing.
fn mark_places(start: &Node, places: &[Vec<usize>], letter: &Node) -> Node {
    if places.iter().any(|p| p.is_empty()) {
        return letter.clone();
    }
    let kids: Vec<Node> = start
        .children
        .iter()
        .enumerate()
        .map(|(k, child)| {
            let below: Vec<Vec<usize>> = places
                .iter()
                .filter(|p| p.first() == Some(&k))
                .map(|p| p[1..].to_vec())
                .collect();
            match below.is_empty() {
                true => child.clone(),
                false => mark_places(child, &below, letter),
            }
        })
        .collect();
    start.with_children(kids)
}

/// A fact an order step adds, as the writer reads it (`order_fact`).
struct OrderFactTerm {
    /// The term that proves it.
    proof: Printed,
    /// What Lean states it as.
    says: Printed,
    /// The fact as the page writes it, which is stated again in a wider
    /// type where the step works in one.
    node: Node,
    /// Whether `node` states, in a wider type, what `proof` proves. Not of
    /// a define's kind, whose fact the page writes of the define's value
    /// and Lean proves of its letter.
    widens: bool,
}

/// The number type a relation Lean states is in; None for one in no
/// number type, or in an item's general type.
fn number_type(says: &Printed) -> Option<super::templates::Num> {
    match super::doc::forms::relation_type(says)? {
        super::doc::LeanType::Num(n) => Some(n),
        _ => None,
    }
}

/// Whether `norm_cast` carries the relation `narrow` states into `wide`,
/// the same relation in a wider type: not an order from ℚ to ℝ, whose
/// facts of numerals it does not take across, as `supplied_proof` says.
fn cast_crosses(narrow: &Printed, wide: &Printed) -> bool {
    use super::templates::Num;
    let crossing = (number_type(narrow), number_type(wide));
    crossing != (Some(Num::Rat), Some(Num::Real))
        || matches!(relation_symbol(wide), Some("=" | "≠"))
}

/// How Lean writes a disequality with its sides swapped, `b ≠ a` of
/// `a ≠ b`; None of anything else.
fn turned_relation_text(says: &Printed) -> Option<String> {
    use super::doc::TermKind;
    match &says.kind {
        TermKind::Infix { op, lhs, rhs } if op.symbol == "≠" => Some(
            Printed::infix(
                *op,
                (**rhs).clone(),
                (**lhs).clone(),
                super::doc::LeanType::Prop,
            )
            .text(),
        ),
        TermKind::Not(inner) => match &inner.kind {
            TermKind::Infix { op, lhs, rhs } if op.symbol == "=" => {
                let swapped = Printed::infix(
                    *op,
                    (**rhs).clone(),
                    (**lhs).clone(),
                    super::doc::LeanType::Prop,
                );
                Some(
                    Printed::of(
                        TermKind::Not(Box::new(swapped)),
                        super::doc::LeanType::Prop,
                    )
                    .text(),
                )
            }
            _ => None,
        },
        _ => None,
    }
}

/// The equations that tie a numeral over a term to the term's reciprocal,
/// `div_eq_mul_one_div 2 (n + 1)`, for each term `stated` divides by more
/// than one numeral: the checker reads 2/(n + 1) as 2·(1/(n + 1)), one atom
/// with 1/(n + 1) (`METHODS.md`, inequalities, Atoms), where Lean's
/// `linarith` takes each quotient as an atom of its own.
fn reciprocals(stated: &[&Printed]) -> Vec<Printed> {
    use super::doc::{LeanType, Source, TermKind};
    let numeral = |t: &Printed| matches!(&t.kind, TermKind::Numeral(_));
    // Each quotient with the number type of the relation it stands in.
    let mut quotients: Vec<(&Printed, &Printed, Option<super::templates::Num>)> =
        Vec::new();
    for s in stated {
        let ty = number_type(s);
        for term in s.walk() {
            if let TermKind::Infix { op, lhs, rhs } = &term.kind {
                if op.symbol == "/" && numeral(lhs) && !numeral(rhs) {
                    let seen = quotients.iter().any(|(l, r, _)| {
                        l.text() == lhs.text() && r.text() == rhs.text()
                    });
                    if !seen {
                        quotients.push((lhs, rhs, ty));
                    }
                }
            }
        }
    }
    quotients
        .iter()
        .filter(|(lhs, rhs, _)| {
            lhs.text() != "1"
                && quotients
                    .iter()
                    .any(|(l, r, _)| r.text() == rhs.text() && l.text() != lhs.text())
        })
        .map(|(lhs, rhs, ty)| {
            // The numeral at the relation's type, which Lean does not find
            // from the lemma's own.
            let numeral = match ty {
                Some(n) => Printed::cast((*lhs).clone(), LeanType::Num(*n)),
                None => (*lhs).clone(),
            };
            Printed::applied(
                "div_eq_mul_one_div",
                Source::Mathlib,
                vec![numeral, super::tactics::bracket((*rhs).clone())],
                LeanType::Prop,
            )
        })
        .collect()
}

/// `by linarith only [facts]`, as a term. Where `split` holds disequalities
/// an order step takes both ways, each is split first:
/// `(Ne.lt_or_gt d).elim (fun h1 => …) (fun h1 => …)`, with h1, the order
/// each case gives, among the facts below it.
fn split_linarith(split: &[Printed], facts: Vec<Printed>) -> Printed {
    use super::doc::{LeanType, Proof, Source, TacticArg, TermKind};
    use super::tactics as t;
    let Some((apart, rest)) = split.split_first() else {
        let call = t::call("linarith", vec![TacticArg::Only, t::rules(facts)]);
        return t::by_term(Proof::By(call));
    };
    let name = format!("h{}", split.len());
    let mut with = facts;
    with.push(t::hyp(&name));
    let case = Printed::of(
        TermKind::Lambda {
            letters: vec![name],
            body: Box::new(split_linarith(rest, with)),
        },
        LeanType::Prop,
    );
    let either = Printed::applied(
        "Ne.lt_or_gt",
        Source::Mathlib,
        vec![apart.clone()],
        LeanType::Prop,
    );
    Printed::applied(
        "Or.elim",
        Source::Mathlib,
        vec![either, case.clone(), case],
        LeanType::Prop,
    )
}

/// `(fun x : T => body)`: a function by its values, bracketed as an
/// argument.
fn lambda(letter: &str, ty: super::doc::LeanType, body: Printed) -> Printed {
    use super::doc::LeanType;
    let to = body.ty.clone().unwrap_or(LeanType::Prop);
    let fun = Printed::of(
        super::doc::TermKind::Quantified {
            quant: super::doc::Quant::Fun,
            letter: letter.to_string(),
            letter_ty: ty.clone(),
            guard: None,
            body: Box::new(body),
            bounded: false,
        },
        LeanType::Fun {
            from: Box::new(ty),
            to: Box::new(to),
        },
    );
    super::tactics::bracket(fun)
}

/// `(fun x : A => ((f (x : B) : C) : D))`: a function of numbers taken at
/// the members a letter runs over, A, and its values cast up to the type
/// wanted, D, through the types it takes and gives, B and C.
fn mapped_through(
    f: Printed,
    from: super::doc::LeanType,
    takes: super::templates::Num,
    gives: super::templates::Num,
    wanted: super::templates::Num,
) -> Printed {
    use super::doc::LeanType;
    let x = Printed::cast(super::tactics::hyp("x"), LeanType::Num(takes));
    let value = Printed::cast(applied_to(f, x), LeanType::Num(gives));
    lambda("x", from, Printed::cast(value, LeanType::Num(wanted)))
}

/// A function or proof applied to one more argument: `f a b` and `h`
/// give `f a b h`.
fn applied_to(term: Printed, arg: Printed) -> Printed {
    match term.kind {
        super::doc::TermKind::App {
            head,
            mut args,
            explicit,
        } => {
            args.push(super::doc::Arg::Explicit(arg));
            Printed {
                kind: super::doc::TermKind::App {
                    head,
                    args,
                    explicit,
                },
                ty: None,
            }
        }
        kind => Printed {
            kind: super::doc::TermKind::App {
                head: Box::new(Printed { kind, ty: term.ty }),
                args: vec![super::doc::Arg::Explicit(arg)],
                explicit: false,
            },
            ty: None,
        },
    }
}

/// `(h).mp p`: an "if and only if" read forwards, `premise` its left side.
fn forwards_of(iff: Printed, premise: Printed) -> Printed {
    let mp = fields(super::tactics::bracket(iff), &["mp"]);
    applied_to(mp, premise)
}

/// Whether an item's statement, as the writer prints it, counts a set: its
/// count stands in the writer's type, ℤ, where Lean takes the item's own,
/// ℕ or ℕ∞, so no line is known to say it from its printed form.
fn item_counts(statement: &Printed) -> bool {
    use super::doc::CountForm::{Extended, Natural};
    statement.has_count(Natural) || statement.has_count(Extended)
}

/// What a forward reading of an "if and only if" or an "if" reaches, `B` of
/// `A ↔ B` and of `A → B`; None for another statement.
fn consequent(statement: &Printed) -> Option<Printed> {
    match &statement.kind {
        super::doc::TermKind::Paren(inner) => consequent(inner),
        super::doc::TermKind::Infix { op, rhs, .. }
            if matches!(op.symbol, "↔" | "→") =>
        {
            Some((**rhs).clone())
        }
        _ => None,
    }
}

/// The side a backward reading of a definition reaches, `A` of "A if and
/// only if B", as the page's tree has it; None for another sentence.
fn node_antecedent(sentence: &Node) -> Option<&Node> {
    match (sentence.notation(), sentence.children.as_slice()) {
        (BICONDITIONAL, [left, _]) => Some(left),
        _ => None,
    }
}

/// The side a forward reading of a sentence reaches, `B` of "A if and only
/// if B" or of "if A then B", as the page's tree has it; None for another
/// sentence.
fn node_consequent(sentence: &Node) -> Option<&Node> {
    match (sentence.notation(), sentence.children.as_slice()) {
        (BICONDITIONAL | CONDITIONAL | IMPLICATION, [_, right]) => Some(right),
        _ => None,
    }
}

/// The part of an "and" a projection path takes, `.1.2`, as the page's tree
/// nests the "and" (`leaf_path`); None where the sentence has no such part.
fn node_along<'n>(sentence: &'n Node, path: &[&str]) -> Option<&'n Node> {
    let mut at = sentence;
    for side in path {
        at = match (at.notation(), at.children.as_slice(), *side) {
            (
                crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
                [l, _],
                "1",
            ) => l,
            (
                crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
                [_, r],
                _,
            ) => r,
            _ => return None,
        };
    }
    Some(at)
}

/// The part of an "and" a projection path takes, `.1.2`, as Lean writes the
/// "and"; None where the statement has no such part.
fn along(statement: &Printed, path: &[&str]) -> Option<Printed> {
    let mut at = statement.clone();
    for side in path {
        let (l, r) = and_sides(&at)?;
        at = match *side {
            "1" => l,
            _ => r,
        };
    }
    Some(at)
}

/// The right side of an "if and only if", `B` of `A ↔ B`; None for another
/// statement.
fn right_side(statement: &Printed) -> Option<Printed> {
    match &statement.kind {
        super::doc::TermKind::Paren(inner) => right_side(inner),
        super::doc::TermKind::Infix { op, rhs, .. } if op.symbol == "↔" => {
            Some((**rhs).clone())
        }
        _ => None,
    }
}

/// A "there is" given its witness `value`: what its guard then says, where
/// it has one, and its body at the witness; nothing known of either where
/// `statement` is no "there is" over a type, or is not known.
fn exists_at(
    statement: Option<&Printed>,
    value: &Printed,
) -> (Option<Printed>, Option<Printed>) {
    use super::doc::{Quant, TermKind};
    let Some(statement) = statement else {
        return (None, None);
    };
    match &statement.kind {
        TermKind::Paren(inner) => exists_at(Some(inner), value),
        TermKind::Quantified {
            quant: Quant::Exists,
            letter,
            guard,
            body,
            ..
        } => {
            let at = |t: &Printed| super::doc::forms::substituted(t, letter, value);
            (guard.as_deref().map(at), Some(at(body)))
        }
        _ => (None, None),
    }
}

/// The symbol of the relation `statement` states, `<` of `0 < x`; None for
/// a statement that is no relation of two sides.
fn relation_symbol(statement: &Printed) -> Option<&'static str> {
    match &unparenthesized(statement).kind {
        super::doc::TermKind::Infix { op, .. } => Some(op.symbol),
        _ => None,
    }
}

/// `proof` of an order turned by `lemma`, `gt_iff_lt.mp h` of `h : a > b`
/// saying `b < a`.
fn turned_order(lemma: &str, proof: Printed) -> Printed {
    Printed::applied(
        lemma,
        super::doc::Source::Core,
        vec![proof],
        super::doc::LeanType::Prop,
    )
}

/// `term` with its outer brackets taken off.
fn unparenthesized(term: &Printed) -> Printed {
    match &term.kind {
        super::doc::TermKind::Paren(inner) => unparenthesized(inner),
        _ => term.clone(),
    }
}

/// How many statements Lean's `statement` joins by "and", each function
/// applied taken as its body at its value: `L k ∈ Set.univ ∧ (fun y => ∃ k,
/// …) (L k)` joins two.
fn lean_conjuncts(statement: &Printed) -> usize {
    let at = super::doc::forms::beta_reduced(&unparenthesized(statement));
    match &at.kind {
        super::doc::TermKind::Infix { op, lhs, rhs } if op.symbol == "∧" => {
            lean_conjuncts(lhs) + lean_conjuncts(rhs)
        }
        _ => 1,
    }
}

/// Whether `part` is a fact that a term is in a number system that is a
/// Lean type, ℤ or ℝ, which Lean states by the term's type and not as a
/// fact.
fn type_membership(part: &Unfolded) -> bool {
    let Unfolded::Fact { fact, .. } = part else {
        return false;
    };
    match (fact.notation(), fact.children.as_slice()) {
        (crate::notations::MEMBERSHIP, [_, set]) => matches!(
            super::expr::system_of(set),
            Some(super::expr::System::Type(_))
        ),
        _ => false,
    }
}

/// The proofs `first`, then `rest`, as one anonymous constructor: `rest`'s
/// own parts where it is one, as Lean's "and" and "there is" nest to the
/// right; `first`'s one proof alone where `rest` adds nothing.
fn joined(mut first: Vec<Printed>, rest: Printed) -> Printed {
    match rest.kind {
        super::doc::TermKind::Listed {
            brackets: super::doc::Brackets::Angle,
            items,
        } => first.extend(items),
        _ => first.push(rest),
    }
    super::expr::anonymous(first)
}

/// The side of an "if and only if" or an "if" a forward reading starts
/// from, `A` of `A ↔ B` and of `A → B`; None for another statement.
fn left_side(statement: &Printed) -> Option<Printed> {
    match &statement.kind {
        super::doc::TermKind::Paren(inner) => left_side(inner),
        super::doc::TermKind::Infix { op, lhs, .. }
            if matches!(op.symbol, "↔" | "→") =>
        {
            Some((**lhs).clone())
        }
        _ => None,
    }
}

/// A term taken along a projection path, `(t).1.2`.
fn projected(term: Printed, path: &[&str]) -> Printed {
    path.iter()
        .fold(super::tactics::bracket(term), |inner, field| Printed {
            kind: super::doc::TermKind::Field {
                inner: Box::new(inner),
                field: field.to_string(),
            },
            ty: None,
        })
}

/// The fields that take sentence `i` of `n` joined by `∧`, which chains to
/// the right: `["1"]`, `["2", "1"]`, …, and the last `["2", "2", …]`.
fn projection_path(i: usize, n: usize) -> Vec<&'static str> {
    if n == 1 {
        return Vec::new();
    }
    let mut out = vec!["2"; i];
    if i + 1 < n {
        out.push("1");
    }
    out
}

/// A term's fields taken in turn, `h.2.1`.
fn fields(term: Printed, path: &[&str]) -> Printed {
    path.iter().fold(term, |inner, field| Printed {
        kind: super::doc::TermKind::Field {
            inner: Box::new(inner),
            field: field.to_string(),
        },
        ty: None,
    })
}

/// Each `let` and `assume` line of a theorem, by its label, with each of
/// its sentences and the Lean name of the hypothesis it is: the label, or
/// `H3a`, `H3b` for a line of several sentences.
fn hypothesis_sentences(
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Vec<(String, Vec<LineSentence>)> {
    let mut out = Vec::new();
    for (i, h) in thm.hypotheses.iter().enumerate() {
        let label = h.label.clone().unwrap_or_else(|| format!("H{}", i + 1));
        let mut nodes: Vec<(usize, Node)> = h
            .body(&thm.path)
            .sentences()
            .iter()
            .enumerate()
            .filter_map(|(at, s)| rec.page.get(s).map(|n| (at, n.clone())))
            .collect();
        // A `let` the page does not read as a formula, `f : A → B be
        // one-to-one`, says what the checker reads it to assert.
        if nodes.is_empty() {
            nodes = rec
                .asserted
                .get(i)
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .enumerate()
                .collect();
        }
        let base = line_name(&label);
        let n = nodes.len();
        let said = nodes
            .into_iter()
            .enumerate()
            .map(|(k, (at, node))| {
                let name = if n == 1 {
                    base.clone()
                } else {
                    format!("{base}{}", (b'a' + k as u8) as char)
                };
                LineSentence::named(at, node, name)
            })
            .collect();
        out.push((label, said));
    }
    out
}

/// A tree of the statement with each name a define of it, or of its file,
/// gives written out as the term it names, as the checker reads the
/// statement (`CheckedTheorem::statement_definitions`).
fn defined_out(node: &Node, rec: &CheckedTheorem, writer: &Writer) -> Node {
    let put: crate::matching::Binding = rec
        .statement_definitions
        .iter()
        .filter_map(|(name, d)| match d {
            crate::matching::Defined::Term(t) => {
                Some((crate::formula::symbol::Symbol::of(name), t.clone()))
            }
            crate::matching::Defined::Rule(_) => None,
        })
        .collect();
    if put.is_empty() {
        return node.clone();
    }
    crate::matching::substitute_apart_by(node, &put, &writer.grammar.binders())
}

/// The defines a theorem's statement is read with, each a name and the term
/// it stands for, in the order defined.
fn statement_terms(rec: &CheckedTheorem) -> Vec<(String, Node)> {
    rec.statement_definitions
        .iter()
        .filter_map(|(name, d)| match d {
            crate::matching::Defined::Term(t) => Some((name.clone(), t.clone())),
            crate::matching::Defined::Rule(_) => None,
        })
        .collect()
}

/// What a citation gives an item's things (`Proof::things_given`).
#[derive(Default)]
struct ThingsGiven {
    /// The least type that holds the numbers given each type variable's
    /// things, by the variable.
    at: std::collections::BTreeMap<usize, super::templates::Num>,
    /// The type variables whose sets are given sets of numbers, X := {2n :
    /// n ∈ ℤ}.
    numbers: std::collections::BTreeSet<usize>,
    /// What the members are of a set given for each type variable's set
    /// where they are not numbers, sets of integers of X := {e ⊆ {1, …, m}
    /// : |e| = m}.
    others: std::collections::BTreeMap<usize, super::expr::Members>,
}

impl ThingsGiven {
    /// What an item's members are here, its things given numbers or sets
    /// put for them at any depth: a property of sets of α, given sets of
    /// integers, is one of `Set ℤ`. `at` is the type each variable's
    /// numbers are taken at.
    fn put(
        &self,
        members: &super::expr::Members,
        at: &dyn Fn(&usize) -> super::templates::Num,
    ) -> super::expr::Members {
        use super::expr::Members;
        match members {
            Members::Things(var) if self.numbers.contains(var) => {
                Members::Numbers(at(var))
            }
            Members::Things(var) if self.others.contains_key(var) => {
                self.others[var].clone()
            }
            Members::Sets(inner) => Members::Sets(Box::new(self.put(inner, at))),
            other => other.clone(),
        }
    }

    fn raise(&mut self, var: usize, n: super::templates::Num) {
        let at = self.at.entry(var).or_insert(n);
        *at = (*at).max(n);
    }
}

/// What a theorem states, in Lean.
struct Statement {
    /// Its binders, from its `let` and `assume` lines.
    binders: Vec<Binder>,
    /// Each sentence of its `then` line.
    conclusion: Vec<Concluded>,
}

/// One sentence a theorem concludes: its tree, and its Lean text.
struct Concluded {
    says: Node,
    prop: Printed,
}

/// The number type of `let A be an element` where later lines say A is in
/// sets of numbers, A ∈ ℝ ∖ ℚ: the widest of those sets' types, as the
/// checker records it (`CheckedTheorem::element_systems`). None where no
/// line puts A in a set of numbers.
fn element_number_type(name: &str, rec: &CheckedTheorem) -> Option<LetterType> {
    let system = rec.element_systems.get(name)?;
    Some(LetterType::Number(super::expr::recorded_set_type(*system)))
}

/// The type of `let T be a set` where T is a set of numbers the checker
/// records the system of, T of {1, …, i} ∩ T or D of D ⊆ ℝ
/// (`CheckedTheorem::set_systems`): a set of those. None where it records
/// none.
fn recorded_number_set_type(name: &str, rec: &CheckedTheorem) -> Option<LetterType> {
    let system = rec.set_systems.get(name)?;
    Some(LetterType::Set(super::expr::Members::Numbers(
        super::expr::recorded_set_type(*system),
    )))
}

/// A theorem's binders, from its `let` and `assume` lines, and each
/// sentence of its `then` line with its Lean text.
/// A function the header lets by its value, `let f(x) = 2x + 1, for x ∈ ℝ`:
/// as the page reads a let, a letter of the type the value computes in,
/// taking the domain's numbers (integers for ℕ, ℕ₀ or a range, as the
/// writer's sequences do), and the equation for every x as one hypothesis
/// named by the label.
/// A function the header lets by its value, as read: the set its argument
/// is in, its value, what the argument is among, and the argument's
/// membership in the set, where the value is read.
struct HeaderReading {
    domain: Node,
    body: Node,
    takes: super::expr::Members,
    member: Node,
}

/// What `header_function` reads of a function the header lets, and the
/// read-back counts the arithmetic of alike.
fn header_reading(
    writer: &Writer,
    d: &crate::corpus::DefineLine,
    def: &crate::corpus::Define,
    rec: &CheckedTheorem,
) -> Route<HeaderReading> {
    use super::templates::Num;
    if set_valued(rec, &def.name) {
        return Route::left_out(SET_VALUED);
    }
    let [param] = def.params.as_slice() else {
        return Route::no("a function the header lets of more than one argument");
    };
    let read: Vec<&Node> = rec
        .page
        .entries()
        .filter(|(key, _)| key.line == d.line)
        .map(|(_, node)| node)
        .collect();
    let over = |n: &&&Node| {
        matches!(
            n.notation(),
            crate::notations::NUMBER_SYSTEMS | crate::notations::INTEGER_RANGE
        )
    };
    // The domain: a number system or range written in the line, or a set,
    // a letter or a set the header itself defines, written out.
    let domain = match read.iter().find(over) {
        Some(n) => (**n).clone(),
        None => {
            let sets: Vec<&&Node> = read
                .iter()
                .filter(|n| !(n.is_name() && *n.text == *param.name))
                .filter(|n| {
                    let out = defined_out(n, rec, writer);
                    writer.set_members(&out).is_some()
                })
                .collect();
            match sets.as_slice() {
                [one] => defined_out(one, rec, writer),
                _ => {
                    return Route::no(
                        "a function the header lets on no set Lean has a type for",
                    )
                }
            }
        }
    };
    let bodies: Vec<&&Node> = read
        .iter()
        .filter(|n| !over(n))
        .filter(|n| !(n.is_name() && *n.text == *param.name))
        .filter(|n| writer.set_members(&defined_out(n, rec, writer)).is_none())
        .collect();
    let [body] = bodies.as_slice() else {
        return Route::no(
            "a function the header lets whose value did not read as one term",
        );
    };
    // What it takes: the domain's numbers, integers for ℕ, ℕ₀ or a range
    // as the writer's sequences take; or the things of a set of things.
    let takes = match super::expr::system_of(&domain) {
        Some(system) => super::expr::Members::Numbers(
            super::expr::letter_type(system).max(Num::Int),
        ),
        None if domain.notation() == crate::notations::INTEGER_RANGE => {
            super::expr::Members::Numbers(Num::Int)
        }
        None => match writer.set_members(&domain) {
            Some(m) => m,
            None => {
                return Route::no(
                    "a function the header lets on no set Lean has a type for",
                )
            }
        },
    };
    let x = Node::name(crate::formula::Sort::none(), &param.name);
    let member = Node::of(
        crate::notations::IN,
        crate::formula::Sort::none(),
        vec![x, domain.clone()],
    );
    Route::Built(HeaderReading {
        domain,
        body: (**body).clone(),
        takes,
        member,
    })
}

impl HeaderReading {
    /// The writer the value is read with: the argument of what it takes,
    /// knowing it is in the set, √x of x ∈ {y ∈ ℝ : y > 0} the real square
    /// root.
    fn inside<'a>(&self, writer: &Writer<'a>, param: &str) -> Writer<'a> {
        let mut w = writer.with_letters(writer.letters.clone());
        w.letters.insert(param.to_string(), self.takes.letter());
        w.knowing(std::slice::from_ref(&self.member))
    }
}

fn header_function(
    writer: &mut Writer,
    d: &crate::corpus::DefineLine,
    def: &crate::corpus::Define,
    rec: &CheckedTheorem,
) -> Route<Vec<Binder>> {
    use super::templates::Num;
    let HeaderReading {
        domain,
        body,
        takes,
        member,
    } = match header_reading(writer, d, def, rec) {
        Route::Built(r) => r,
        Route::Declined(d) => return Route::Declined(d),
    };
    let [param] = def.params.as_slice() else {
        return Route::no("a function the header lets of more than one argument");
    };
    let body = &body;
    let before = writer.letters.insert(param.name.clone(), takes.letter());
    // Said for every x of the domain: all of a type, or each member of a
    // set, x ∈ D, as the writer writes that membership.
    let whole_type = matches!(
        super::expr::system_of(&domain),
        Some(super::expr::System::Type(_))
    );
    let guard = match whole_type {
        true => Route::Built(None),
        false => writer.formula(&member).map(Some),
    };
    // The value is read where x is in the domain: √x of x ∈ {y ∈ ℝ : y >
    // 0} the real square root.
    let inside = writer.knowing(std::slice::from_ref(&member));
    // A function of a real or complex argument gives values of at least
    // that type, as continuity and derivatives read it: a step of 0 and 1
    // on [0, 1] is a function into ℝ.
    let value = match &takes {
        super::expr::Members::Numbers(from) => match inside.carrier(body) {
            Route::Built(to) => {
                let to = match *from >= Num::Real {
                    true => to.max(*from),
                    false => to,
                };
                inside
                    .number_fixed(body, to)
                    .map(|v| (LetterType::Function { from: *from, to }, v))
            }
            Route::Declined(why) => Route::Declined(why),
        },
        m => match writer.member_kind(body) {
            Some(to) => writer.set_term(body).map(|v| {
                (
                    LetterType::Map {
                        from: m.clone(),
                        to,
                    },
                    v,
                )
            }),
            None => {
                Route::no("a function the header lets whose value has no Lean type")
            }
        },
    };
    match before {
        Some(ty) => writer.letters.insert(param.name.clone(), ty),
        None => writer.letters.shift_remove(&param.name),
    };
    let ((ty, value), guard) = match (value, guard) {
        (Route::Built(v), Route::Built(g)) => (v, g),
        (Route::Declined(why), _) | (_, Route::Declined(why)) => {
            return Route::Declined(why)
        }
    };
    writer.letters.insert(def.name.clone(), ty.clone());
    // On a set, D ∖ {c}: that set is its domain, within which its images,
    // preimages and limits are taken (`domain_of`).
    if !whole_type {
        let written = match &takes {
            super::expr::Members::Numbers(n) => writer.numbers_at(&domain, *n),
            _ => writer.set_term(&domain),
        };
        match written {
            Route::Built(p) => {
                writer.domains.insert(def.name.clone(), p);
            }
            Route::Declined(why) => return Route::Declined(why),
        }
    }
    let f = super::names::letter(&def.name);
    let x = super::names::letter(&param.name);
    // ∀ x : T, guard → f x = value.
    let takes_ty = takes.letter().lean_type();
    let applied = Printed {
        kind: super::doc::TermKind::App {
            head: Box::new(Printed::letter(f.clone(), ty.lean_type())),
            args: vec![super::doc::Arg::Explicit(Printed::letter(
                x.clone(),
                takes_ty.clone(),
            ))],
            explicit: false,
        },
        ty: value.ty.clone(),
    };
    let says = Printed::of(
        super::doc::TermKind::Quantified {
            quant: super::doc::Quant::ForAll,
            letter: x,
            letter_ty: takes_ty,
            guard: guard.map(Box::new),
            body: Box::new(Printed::infix(
                super::doc::Op::EQUALS,
                applied,
                value,
                super::doc::LeanType::Prop,
            )),
            bounded: false,
        },
        super::doc::LeanType::Prop,
    );
    Route::Built(vec![
        Binder::Letter {
            name: f.clone(),
            page: def.name.clone(),
            general: false,
            ty,
        },
        Binder::Fact {
            name: line_name(&d.label),
            says,
            line: None,
        },
    ])
}

/// One function's rules of a recursion, as the checker read them: its name,
/// its value at 0, and its value at k + 1.
struct RecursionRule<'r> {
    name: &'r String,
    start: Node,
    step: Node,
}

/// Each function's rules of a recursion, as the checker read them.
fn recursion_rules<'r>(
    r: &'r crate::corpus::Recursion,
    d: &crate::corpus::DefineLine,
    rec: &CheckedTheorem,
) -> Route<Vec<RecursionRule<'r>>> {
    let mut out = Vec::new();
    for name in &r.names {
        let (Some(start), Some(step)) = (
            r.start.get(name).and_then(|rule| rule_tree(rule, d, rec)),
            r.step.get(name).and_then(|rule| rule_tree(rule, d, rec)),
        ) else {
            return Route::no(format!(
                "a recursion whose rules for {name} did not read"
            ));
        };
        out.push(RecursionRule { name, start, step });
    }
    Route::Built(out)
}

/// A rule of a recursion as the checker read it; None where it read none.
fn rule_tree(
    rule: &crate::corpus::RuleText,
    d: &crate::corpus::DefineLine,
    rec: &CheckedTheorem,
) -> Option<Node> {
    match rule.written(&d.path, d.line).sentences().as_slice() {
        [one] => rec.page.get(one).cloned(),
        _ => None,
    }
}

/// The arithmetic the page writes in the recursions a theorem's header
/// lets, as their hypothesis states them (`header_recursions`): each rule's
/// value, and the k + 1 each function is applied to in its step.
fn recursion_arithmetic(
    writer: &Writer,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> std::collections::BTreeMap<String, usize> {
    let mut out = std::collections::BTreeMap::new();
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        let r = match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(r)) => r,
            // A function the header lets by its value: the value, which its
            // hypothesis states (`header_function`).
            Route::Built(crate::corpus::DefineParts::One(one))
                if !one.params.is_empty() =>
            {
                let values: Vec<Node> = rec
                    .page
                    .entries()
                    .filter(|(key, _)| key.line == d.line)
                    .map(|(_, n)| n.clone())
                    .filter(|n| {
                        !matches!(
                            n.notation(),
                            crate::notations::NUMBER_SYSTEMS
                                | crate::notations::INTEGER_RANGE
                        )
                    })
                    .filter(|n| !n.is_name())
                    .collect();
                // The value as `header_function` reads it, knowing its
                // argument is in the set; the rest as it stands.
                let reading = header_reading(writer, d, &one, rec).built();
                let (inside, rest): (Vec<Node>, Vec<Node>) =
                    values.into_iter().partition(|n| {
                        reading.as_ref().is_some_and(|r| {
                            writer.grammar.print(&r.body) == writer.grammar.print(n)
                        })
                    });
                let mut counts = super::readback::page_arithmetic(writer, &rest);
                if let (Some(r), [param]) = (&reading, one.params.as_slice()) {
                    let w = r.inside(writer, &param.name);
                    for (op, n) in super::readback::page_arithmetic(&w, &inside) {
                        *counts.entry(op).or_insert(0) += n;
                    }
                }
                for (op, n) in counts {
                    *out.entry(op).or_insert(0) += n;
                }
                continue;
            }
            _ => continue,
        };
        let Route::Built(rules) = recursion_rules(&r, d, rec) else {
            continue;
        };
        let values: Vec<Node> = rules
            .iter()
            .flat_map(|rule| [rule.start.clone(), rule.step.clone()])
            .collect();
        for (op, n) in super::readback::page_arithmetic(writer, &values) {
            *out.entry(op).or_insert(0) += n;
        }
        *out.entry("addition".to_string()).or_insert(0) += rules.len();
    }
    out
}

/// The recursions a theorem's header lets,
/// `let F(0) = 0, G(0) = 1, F(k + 1) = G(k), G(k + 1) = F(k) + G(k), for k ∈ ℕ₀`:
/// as the page reads a let,
/// letters for its functions, of ℤ into the type its rules compute in, and
/// its rules one hypothesis named by its label, its step for k ≥ 0. Of
/// every pair F, G the rules hold of, which agree from 0 on, the theorem
/// says what it says of the Fibonacci numbers. A recursion from 1, over ℕ,
/// is declined.
fn header_recursions(
    writer: &mut Writer,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Route<Vec<Binder>> {
    use super::templates::Num;
    let mut out = Vec::new();
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        let r = match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(r)) => r,
            // A function the header lets by its value, f(x) = 2x + 1, for x
            // ∈ ℝ: a function letter, and that equation for every x.
            Route::Built(crate::corpus::DefineParts::One(one))
                if !one.params.is_empty() =>
            {
                match header_function(writer, d, &one, rec) {
                    Route::Built(b) => {
                        out.extend(b);
                        continue;
                    }
                    Route::Declined(why) => return Route::Declined(why),
                }
            }
            _ => continue,
        };
        if r.domain.trim() != "ℕ₀" {
            return Route::no("a recursion over other than ℕ₀");
        }
        let rules = match recursion_rules(&r, d, rec) {
            Route::Built(rules) => rules,
            Route::Declined(d) => return Route::Declined(d),
        };
        // The functions take integers, as the writer's sequences do, so
        // that F(k) of a sum's index is written as it stands; the rules say
        // what they are from 0. What they give is the type their rules
        // compute in, an integer at least.
        let index = r.index.clone();
        let before = writer
            .letters
            .insert(index.clone(), LetterType::Number(Num::Int));
        let mut to = Num::Int;
        for name in &r.names {
            writer
                .letters
                .insert(name.clone(), LetterType::Function { from: Num::Int, to });
        }
        for rule in &rules {
            for n in [&rule.start, &rule.step] {
                match writer.carrier(n) {
                    Route::Built(c) => to = to.max(c),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        }
        for name in &r.names {
            writer
                .letters
                .insert(name.clone(), LetterType::Function { from: Num::Int, to });
        }
        use super::doc::{LeanType, Op};
        let int = LeanType::Num(Num::Int);
        let k = super::names::letter(&index);
        let mut starts = Vec::new();
        let mut steps = Vec::new();
        for rule in &rules {
            let f = super::names::letter(rule.name);
            let (s, t) = match (
                writer.number_fixed(&rule.start, to),
                writer.number_fixed(&rule.step, to),
            ) {
                (Route::Built(s), Route::Built(t)) => (s, t),
                (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                    return Route::Declined(d)
                }
            };
            let at = |arg: Printed| applied_to(super::tactics::hyp(&f), arg);
            let next = Printed::infix(
                Op::PLUS,
                super::tactics::hyp(&k),
                Printed::numeral("1", int.clone()),
                int.clone(),
            );
            starts.push(Printed::infix(
                Op::EQUALS,
                at(Printed::numeral("0", int.clone())),
                s,
                LeanType::Prop,
            ));
            steps.push(Printed::infix(Op::EQUALS, at(next), t, LeanType::Prop));
        }
        match before {
            Some(ty) => writer.letters.insert(index.clone(), ty),
            None => writer.letters.shift_remove(&index),
        };
        for name in &r.names {
            out.push(Binder::Letter {
                name: super::names::letter(name),
                page: name.clone(),
                general: false,
                ty: LetterType::Function { from: Num::Int, to },
            });
        }
        out.push(Binder::Fact {
            name: line_name(&d.label),
            says: rules_said(&k, starts, steps),
            line: None,
        });
    }
    Route::Built(out)
}

/// Hypothesis sentences, each its tree and its Lean name, as `binders`
/// takes them.
fn asked_of(written: &[(Node, String)]) -> Vec<Asked<'_>> {
    written
        .iter()
        .map(|(node, name)| Asked {
            node,
            name: name.clone(),
        })
        .collect()
}

fn statement(
    writer: &mut Writer,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Route<Statement> {
    let said = hypothesis_sentences(thm, rec);
    // A `let` that is no formula, `A be a set` or `x be an element`, gives
    // its letter the type its sort settles, ahead of the lines that use it.
    let mut binders_of_sets = Vec::new();
    let mut read: usize = said.iter().map(|(_, s)| s.len()).sum();
    // The first `let` that is no formula and that no Lean type is given
    // for, `let A be a point`: what keeps the theorem out.
    let mut untyped: Option<String> = None;
    for (i, h) in thm.hypotheses.iter().enumerate() {
        let body = h.body(&thm.path);
        if body.sentences().iter().all(|s| rec.page.get(s).is_some()) {
            continue;
        }
        use crate::sorts::introduction::{Form, Introduction};
        let name = match Introduction::read(body.clone()).form {
            Form::Set(name)
            | Form::Element(name)
            | Form::Property { name, .. }
            | Form::FunctionOn { name, .. } => name,
            // `let G be a group with operation · and identity e`: the type
            // of its elements with Mathlib's group on it, and e its 1. What
            // else the line asserts, that G is finite, is among `said`.
            Form::Group {
                group, identity, ..
            } => {
                writer.letters.insert(group.clone(), LetterType::Group);
                writer
                    .letters
                    .insert(identity, LetterType::Identity(group.clone()));
                binders_of_sets.push(Binder::Letter {
                    name: super::names::letter(&group),
                    page: group,
                    general: false,
                    ty: LetterType::Group,
                });
                if rec.asserted.get(i).is_none_or(Vec::is_empty) {
                    read += body.sentences().len();
                }
                continue;
            }
            _ => {
                untyped.get_or_insert_with(|| body.text().to_string());
                continue;
            }
        };
        // An element nothing settles a sort of, `let B be an element` of a
        // B only listed, {B}, is a thing.
        let unsorted_element =
            matches!(Introduction::read(body.clone()).form, Form::Element(_))
                && rec.sorts.get(&name).is_none();
        let Some(ty) = rec
            .sorts
            .get(&name)
            .and_then(super::sets::set_letter_type)
            .or_else(|| element_number_type(&name, rec))
            .or_else(|| recorded_number_set_type(&name, rec))
            .or_else(|| {
                unsorted_element
                    .then_some(LetterType::Member(super::expr::Members::Things(0)))
            })
        else {
            untyped.get_or_insert_with(|| body.text().to_string());
            continue;
        };
        writer.letters.insert(name.clone(), ty.clone());
        binders_of_sets.push(Binder::Letter {
            name: super::names::letter(&name),
            page: name,
            general: false,
            ty,
        });
        // A line that asserts something of its letter, F is a function on
        // A, is read among `said` already.
        if rec.asserted.get(i).is_none_or(Vec::is_empty) {
            read += body.sentences().len();
        }
    }
    let written: usize = thm
        .hypotheses
        .iter()
        .map(|h| h.body(&thm.path).sentences().len())
        .sum();
    if read != written {
        return match untyped {
            Some(line) => {
                Route::left_out(format!("let {line}, a line Lean has no type for yet"))
            }
            None => Route::no("a hypothesis the checker did not read"),
        };
    }
    // A define the statement is read with is written out in it: Lean's
    // statement says what the name stands for, and the proof names it again
    // (`theorem`, `set`).
    // The hypotheses above a recursion or function the header lets are
    // read before it, as its rules may use their letters, F(0) = M; those
    // below after it, as they may use its functions.
    let recursion_line = thm
        .defines
        .iter()
        .filter(|d| d.line < thm.conclusion_line)
        .filter(|d| match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(_)) => true,
            Route::Built(crate::corpus::DefineParts::One(one)) => {
                !one.params.is_empty()
            }
            _ => false,
        })
        .map(|d| d.line)
        .min();
    let above = |label: &str| {
        let line = thm
            .hypotheses
            .iter()
            .find(|h| h.label.as_deref() == Some(label))
            .map(|h| h.line);
        match (recursion_line, line) {
            (Some(r), Some(l)) => l < r,
            _ => true,
        }
    };
    let mut written_above: Vec<(Node, String)> = Vec::new();
    let mut written_below: Vec<(Node, String)> = Vec::new();
    for (label, s) in &said {
        let into = match above(label) {
            true => &mut written_above,
            false => &mut written_below,
        };
        for s in s {
            if let Some(name) = &s.name {
                into.push((defined_out(&s.node, rec, writer), name.clone()));
            }
        }
    }
    let first = match binders(writer, &asked_of(&written_above), &[]) {
        Route::Built(b) => b,
        Route::Declined(d) => return Route::Declined(d),
    };
    let recursions = match header_recursions(writer, thm, rec) {
        Route::Built(b) => b,
        Route::Declined(d) => return Route::Declined(d),
    };
    let binders = match binders(writer, &asked_of(&written_below), &[]) {
        Route::Built(b) => binders_of_sets
            .into_iter()
            .chain(first)
            .chain(recursions)
            .chain(b)
            .collect::<Vec<_>>(),
        Route::Declined(d) => return Route::Declined(d),
    };
    let mut conclusion = Vec::new();
    for s in thm.stated().sentences() {
        let Some(node) = rec.page.get(&s) else {
            return Route::no(format!("{}, which the checker did not read", s.text()));
        };
        let node = &defined_out(node, rec, writer);
        let prop = match writer.formula(node) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        conclusion.push(Concluded {
            says: node.clone(),
            prop,
        });
    }
    Route::Built(Statement {
        binders,
        conclusion,
    })
}

/// Where a step takes its counts in ℕ∞ to integers (`Proof::count_conversion`).
enum CountConversion {
    /// Nowhere: its lines say their counts one way.
    None,
    /// Before its tactic, the goal and the lines in scope.
    Before,
    /// After its tactic, what it built and the goal together.
    After,
}

/// How a step's lines say their counts (`Proof::count_forms`).
struct CountForms {
    /// One says a count in ℕ∞.
    extended: bool,
    /// One set's count is said both in ℕ∞ and as an integer.
    mixed: bool,
}

/// How one set's count is said across a step's lines.
#[derive(Default)]
struct CountSaid {
    /// In ℕ∞, somewhere.
    extended: bool,
    /// As an integer, somewhere.
    integer: bool,
}

/// Writes one theorem's proof.
struct Proof<'a> {
    sources: &'a Sources<'a>,
    thm: &'a Theorem,
    rec: &'a CheckedTheorem,
    writer: Writer<'a>,
    /// The proof's lines in order, each with what it was written for.
    lines: Vec<ProofLine>,
    /// The Lean names of each line the page can cite, by the reference
    /// that cites it: a step's number or a label. A line said as
    /// projections of one hypothesis, an `assume` of several sentences, is
    /// named by that hypothesis.
    named: IndexMap<String, Vec<String>>,
    /// What each line the page can cite says, sentence by sentence, with
    /// the Lean name of each sentence's proof, by the reference that cites
    /// it.
    trees: IndexMap<String, Vec<LineSentence>>,
    /// The defines written so far, by their index in the theorem's.
    defined: indexmap::IndexSet<usize>,
    /// While a calculation's rows are written, the type it is worked out
    /// in: a row's claim alone, Σ j² = 1², may hold in a narrower type than
    /// the calculation's ℚ, which a citation in the row is applied at.
    worked_in: std::cell::Cell<Option<super::templates::Num>>,
    /// While a calculation's row is written, the row as the calculation
    /// states it in Lean, `_ = ((2 : ℕ) : ℕ∞)` of a chain of counts: what a
    /// citation in the row is compared with.
    row_stated: std::cell::RefCell<Option<Printed>>,
    /// While the part a witness's `refine` leaves open is proved: the step's
    /// `have` states the whole "there is", and the goal is what the claim
    /// says of the witness, as the writer writes the claim with its number
    /// named.
    in_witness: std::cell::Cell<bool>,
    /// The lines whose numbers a citation was given while its step was
    /// written, A/B of `A/B ∈ ℤ`, which the step's goal is put in terms of.
    said_used: std::cell::RefCell<Vec<SaidUsed>>,
    /// Where a citation's item, read as written, writes a term in another
    /// form than the line it proves (`doc::forms`).
    forms: std::cell::RefCell<Vec<FormNote>>,
    /// While a step that names whole numbers is written
    /// (`proof_with_named`), the equations of each with its term: what a
    /// row citing a line in the page's forms is put in terms of.
    named_specs: Vec<Printed>,
    /// The labels of the defines that name the number their reason shows,
    /// `let e = p/d, a positive integer` (`kinded_witness`): their equation
    /// is a line about an obtained number, cited as any line is, not a
    /// `set` written out.
    witnessed: std::collections::BTreeSet<String>,
    /// Each such define's value, m/p, and the letter that names the number,
    /// r: a citation given the value, as the checker reads one from the
    /// define's fact `m/p ∈ ℕ`, is given the letter.
    witness_letters: Vec<WitnessLetter>,
    /// While a step's reason is written, the lines it names, by the keys of
    /// `trees`: the references it cites and its requires lines. A line
    /// saying a term is an integer is one of these (`integer_line`), as
    /// the page puts a term in a system only in the steps that name the
    /// line (`docs/SYNTAX.md`).
    named_now: std::cell::RefCell<Option<std::collections::BTreeSet<String>>>,
    /// While a reason is written, the parts its lines put in a number
    /// system, as the check found them (`CheckedTheorem::held_by_lines`).
    held_now: std::cell::RefCell<Vec<crate::checker::record::HeldByLines>>,
    /// The index of the step being written, whose lines a witness's whole
    /// number is named from (`witness`).
    step_now: std::cell::Cell<Option<usize>>,
}

/// The fact a define of a kind says of its value, as `Proof::kind_shown`
/// reads it.
struct KindShown {
    /// The fact, `gcd(t, w) ∈ ℕ`.
    fact: Node,
    /// The fact in Lean.
    says: Printed,
    /// Its proof by the define's reason.
    proof: super::doc::Proof,
}

/// A whole number a step names for a term Lean does not compute as one,
/// 2^(p − 1): the `have` that names it, and the term written as it.
struct NamedAtom {
    have: Tactic,
    said: super::expr::SaidInteger,
}

/// A line a step names that puts a term in a number system, `p − 1 ∈ ℕ₀`:
/// its Lean name and the system it says.
struct NamedLine {
    name: Printed,
    system: crate::rules::System,
}

/// The Lean name of the line among `facts` that puts the term `t` in
/// `within` or a system inside it, `p − 1 ∈ ℕ₀` asked of ℕ₀, as the check
/// found the line held it (`Proof::held`); None where none does.
fn named_line(
    facts: &[super::algebra::Cited],
    t: &Node,
    within: crate::rules::System,
    ctx: &crate::matching::Context,
) -> Option<NamedLine> {
    facts.iter().find_map(|f| {
        let [x, set] = f.node.children.as_slice() else {
            return None;
        };
        let system = crate::rules::System::of_sign(&set.text)?;
        // Each in its standard spelling, x² as x^2, as the membership method
        // reads them (`methods::membership`).
        let standard = |n: &Node| crate::matching::standard(n, ctx);
        (f.node.notation() == crate::notations::MEMBERSHIP
            && set.notation() == crate::notations::NUMBER_SYSTEMS
            && crate::matching::alike_top(&standard(x), &standard(t), ctx)
            && system.within(within))
        .then(|| NamedLine {
            name: f.proof.clone(),
            system,
        })
    })
}

/// A line a step cites in the witness form, `∃ m : ℤ, ↑m = t ∧ P m`, or its
/// negation, which the step restates of the number it names for t.
struct CitedWitness {
    /// The line's Lean name.
    name: String,
    /// The term t the witness stands for.
    term: Node,
    /// The type the witness is in, ℤ or ℕ.
    whole: super::templates::Num,
    /// Whether the line says no whole number is t with P.
    negated: bool,
}

/// A define that names the number its reason shows its value is.
struct WitnessLetter {
    /// The value, m/p.
    value: Node,
    /// The letter, r.
    letter: Node,
}

/// A line whose number a citation was given: its Lean name, and the term
/// it says is in ℤ or ℚ as the page prints it.
struct SaidUsed {
    line: SaidLine,
    term: String,
}

/// A line saying a term is a whole number, `∃ m : ℤ, ↑m = t`; of ℕ and ℕ₀
/// with its order, `∃ m : ℤ, 0 ≤ m ∧ ↑m = t`; or of a range, `∃ m : ℤ, ↑m
/// = t ∧ m ∈ Finset.Icc a b` (`integer_line`).
#[derive(Clone)]
struct SaidLine {
    /// Its Lean name, or a part of one.
    proof: Printed,
    /// What the line says of its number besides the equation.
    beside: Beside,
}

/// What a `SaidLine` says of its number besides its equation with the term.
#[derive(Clone, Copy, PartialEq)]
enum Beside {
    /// Nothing: `↑m = t`.
    Nothing,
    /// Its order, first: `0 ≤ m ∧ ↑m = t`.
    Order,
    /// Its range, after: `↑m = t ∧ m ∈ Finset.Icc a b`.
    Range,
}

impl SaidLine {
    /// The number it gives, `Classical.choose h`.
    fn chosen(&self, ty: super::templates::Num) -> Printed {
        Printed::applied(
            "Classical.choose",
            super::doc::Source::Core,
            vec![self.proof.clone()],
            super::doc::LeanType::Num(ty),
        )
    }

    /// `Classical.choose_spec h`.
    fn spec(&self) -> Printed {
        Printed::applied(
            "Classical.choose_spec",
            super::doc::Source::Core,
            vec![self.proof.clone()],
            super::doc::LeanType::Prop,
        )
    }

    /// One part of the spec, `.1` or `.2`.
    fn part(&self, field: &str) -> Printed {
        Printed {
            kind: super::doc::TermKind::Field {
                inner: Box::new(super::tactics::bracket(self.spec())),
                field: field.to_string(),
            },
            ty: None,
        }
    }

    /// The number's equation with the term: the spec, or its part that is
    /// the equation where the line says more of the number.
    fn equation(&self) -> Printed {
        match self.beside {
            Beside::Nothing => self.spec(),
            Beside::Order => self.part("2"),
            Beside::Range => self.part("1"),
        }
    }

    /// What else the line says of the number, its order or its range; None
    /// where it says only the equation.
    fn besides(&self) -> Option<Printed> {
        match self.beside {
            Beside::Nothing => None,
            Beside::Order => Some(self.part("1")),
            Beside::Range => Some(self.part("2")),
        }
    }
}

/// A recursion the header lets, as a step cites it.
struct CitedRecursion {
    rule: crate::corpus::Recursion,
    /// The Lean name of its hypothesis, `hD1`.
    hypothesis: String,
    /// Whether a rule of it is by cases, F(k) if b(k) = 0, G(k) otherwise.
    by_cases: bool,
}

/// The theorem written as a Lean file's declaration: its statement and its
/// proof, with an origin for every line, counted from the first line of
/// the declaration.
pub fn theorem(
    sources: &Sources,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Route<LeanFile> {
    let rec = as_written(rec);
    let mut proof = Proof {
        sources,
        thm,
        rec,
        writer: Writer::new(&sources.checked.grammar, sources.templates),
        lines: Vec::new(),
        named: IndexMap::new(),
        trees: IndexMap::new(),
        defined: indexmap::IndexSet::new(),
        worked_in: std::cell::Cell::new(None),
        row_stated: std::cell::RefCell::new(None),
        in_witness: std::cell::Cell::new(false),
        said_used: std::cell::RefCell::new(Vec::new()),
        forms: std::cell::RefCell::new(Vec::new()),
        named_specs: Vec::new(),
        witnessed: std::collections::BTreeSet::new(),
        witness_letters: Vec::new(),
        named_now: std::cell::RefCell::new(None),
        held_now: std::cell::RefCell::new(Vec::new()),
        step_now: std::cell::Cell::new(None),
    };
    proof.writer.reals = held_real(rec, &proof.writer);
    proof.writer.finite_from(&rec.said_finite);
    proof.writer.bounds = rec.statement_bounds.clone();
    proof.writer.whole_bounds = rec.statement_bounds.clone();
    let Statement {
        binders,
        conclusion,
    } = match statement(&mut proof.writer, thm, rec) {
        Route::Built(s) => s,
        Route::Declined(d) => return Route::Declined(d),
    };
    // A hypothesis Lean's types give, M ∈ ℕ₀ of a natural M, has no binder
    // and is no line in Lean: a step that uses it has the type.
    let bound: std::collections::BTreeSet<&str> =
        binders.iter().map(Binder::name).collect();
    for (label, said) in hypothesis_sentences(thm, rec) {
        let said: Vec<LineSentence> = said
            .into_iter()
            .filter(|s| s.name.as_deref().is_some_and(|n| bound.contains(n)))
            .collect();
        let names: Vec<String> = said.iter().filter_map(|s| s.name.clone()).collect();
        proof.named.insert(label.clone(), names);
        proof.store(label, said);
    }
    // A recursion or a function the statement lets is cited by its label,
    // as its hypothesis (`header_recursions`).
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        let function = match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(_)) => true,
            Route::Built(crate::corpus::DefineParts::One(one)) => {
                !one.params.is_empty()
            }
            _ => false,
        };
        if function {
            proof
                .named
                .insert(d.label.clone(), vec![line_name(&d.label)]);
        }
    }
    let props: Vec<&Printed> = conclusion.iter().map(|c| &c.prop).collect();
    let decl_binders: Vec<super::doc::file::Binder> =
        super::statement::things_binder(&binders, &props)
            .into_iter()
            .chain(binders.iter().map(Binder::doc))
            .collect();
    let says = all_of(&props);
    // The names the statement wrote out, named again for the proof.
    // Only those the theorem's page writes: a file's other defines are its
    // other theorems'.
    let written: std::collections::BTreeSet<String> = rec
        .page
        .entries()
        .flat_map(|(_, node)| node.names())
        .collect();
    for (name, body) in statement_terms(rec) {
        if !written.contains(&name) {
            continue;
        }
        let own = thm.defines.iter().position(|d| {
            d.line < thm.conclusion_line
                && matches!(
                    crate::corpus::define_parts(&d.text),
                    Route::Built(crate::corpus::DefineParts::One(ref one)) if one.name == name
                )
        });
        let named = match own {
            Some(d) => proof.define(d, 1),
            None => proof.define_outside(&name, &body),
        };
        if let Route::Declined(d) = named {
            return Route::Declined(d);
        }
    }
    let top: Vec<usize> = (0..thm.steps.len())
        .filter(|&i| rec.places[i].is_none())
        .collect();
    if let Route::Declined(d) = proof.steps(&top, 1) {
        return Route::Declined(d);
    }
    // One term, one form: a square root or real power the lines in scope
    // put at least 0 in one place and not in another is reported, not
    // converted between.
    if let Some(root) = proof.writer.roots_written_both_ways() {
        return Route::no(format!(
            "{root} is written as Mathlib's real one in one place and the principal one in ℂ in another"
        ));
    }
    let owed: Vec<Node> = conclusion.iter().map(|c| c.says.clone()).collect();
    let closing = match proof.closing(top.last().copied(), Owing::Written(Some(&owed)))
    {
        Route::Built(c) => c,
        Route::Declined(d) => return Route::Declined(d),
    };
    proof.close(1, closing, thm.conclusion_line, Spot::Statement);
    let decl = super::doc::file::Declaration {
        name: snake(&thm.name),
        binders: decl_binders,
        says,
        proof: super::doc::file::DeclProof::Steps(Vec::new()),
    };
    // Each line of the file, from 1, and what it was written for: the
    // statement's lines, then each step's.
    let mut origins = Vec::new();
    for _ in decl.head().lines() {
        origins.push(Origin {
            line: origins.len() + 1,
            page_line: thm.line,
            spot: Spot::Statement,
        });
    }
    let mut steps = Vec::new();
    for line in proof.lines {
        let step = super::doc::file::Step {
            depth: line.depth,
            tactic: line.tactic,
        };
        for _ in step.text().lines() {
            origins.push(Origin {
                line: origins.len() + 1,
                ..line.origin.clone()
            });
        }
        steps.push(step);
    }
    let forms = proof.forms.take();
    Route::Built(LeanFile {
        decl: super::doc::file::Declaration {
            proof: super::doc::file::DeclProof::Steps(steps),
            ..decl
        },
        origins,
        forms,
    })
}

/// The sentences of a statement as one, joined by `∧`, each bracketed
/// where it binds more loosely: what a theorem of several says.
fn all_of(props: &[&Printed]) -> Printed {
    let parts = props.iter().map(|p| (*p).clone()).collect();
    super::expr::joined(super::doc::Op::AND, parts, 36).unwrap_or_else(Printed::truth)
}

/// What proves a claim: a justification, and what the checker read of the
/// item it cites. A step has one, and so does each of its requires lines
/// and each line of a calculation that gives a reason of its own.
#[derive(Clone, Copy)]
struct Reason<'r> {
    just: &'r Justification,
    cited: Option<&'r Cited>,
}

impl<'a> Proof<'a> {
    /// `intro a b` as a line of the proof at a depth of its blocks.
    fn intro(
        &mut self,
        depth: usize,
        names: Vec<String>,
        page_line: usize,
        spot: &Spot,
    ) {
        self.push_at(depth, Tactic::Intro(names), page_line, spot.clone());
    }

    /// A tactic as a line of the proof at a depth of its blocks.
    fn push_at(&mut self, depth: usize, tactic: Tactic, page_line: usize, spot: Spot) {
        self.lines.push(ProofLine {
            depth,
            tactic,
            origin: Origin {
                line: 0,
                page_line,
                spot,
            },
        });
    }

    fn step_spot(step: &Step) -> Spot {
        Spot::Step(match step.number.number() {
            Some(n) => n.to_string(),
            None => "the theorem".to_string(),
        })
    }

    /// The steps, in order, each at the depth given.
    fn steps(&mut self, indices: &[usize], depth: usize) -> Route<()> {
        for &i in indices {
            if let Route::Declined(d) = self.step(i, depth) {
                // Named by the innermost step it comes from: a block's
                // decline already names the step inside it.
                let reason = d.reason();
                if reason.starts_with("step ") {
                    return Route::Declined(d);
                }
                let number = &self.thm.steps[i].number;
                return Route::Declined(d.reworded(format!("step {number}: {reason}")));
            }
        }
        Route::Built(())
    }

    /// A step's claim: each sentence, read, with its Lean text; a
    /// membership Lean's types already give is left out, since nothing
    /// needs saying.
    fn claim(&self, step: &Step) -> Route<Vec<(Node, Printed)>> {
        self.claimed(step).map(|c| {
            c.into_iter()
                .map(|(_, node, printed)| (node, printed))
                .collect()
        })
    }

    /// The sentences of a step's claim Lean has a line for, `claimed`, each
    /// by its place on the page and under its name of `names`, in order. A
    /// truth Lean's types give has no line, so its place is kept by none.
    fn claim_sentences(
        claimed: &[(usize, Node, Printed)],
        names: &[String],
    ) -> Vec<LineSentence> {
        // Each with what its `have` states, the line's own statement.
        claimed
            .iter()
            .zip(names)
            .map(|((at, node, printed), name)| LineSentence {
                says: Some(printed.clone()),
                ..LineSentence::named(*at, node.clone(), name.clone())
            })
            .collect()
    }

    /// A claim's sentences as `claimed` gives them, without their places.
    fn without_places(claimed: &[(usize, Node, Printed)]) -> Vec<(Node, Printed)> {
        claimed
            .iter()
            .map(|(_, node, printed)| (node.clone(), printed.clone()))
            .collect()
    }

    /// `claim`, each sentence with its place among the page's: a sentence
    /// Lean's types already give, √x ∈ ℝ, is left out, and a citation is
    /// read at the place the checker counted.
    fn claimed(&self, step: &Step) -> Route<Vec<(usize, Node, Printed)>> {
        self.claimed_all(step).map(|all| {
            all.into_iter()
                .filter(|(_, _, printed)| !printed.is_truth())
                .collect()
        })
    }

    /// Every sentence of a step's claim with its place and its Lean text,
    /// those Lean's types already give among them, as `True`.
    fn claimed_all(&self, step: &Step) -> Route<Vec<(usize, Node, Printed)>> {
        let mut out = Vec::new();
        let sentences: Vec<Option<&Node>> = step
            .claim
            .sentences()
            .iter()
            .map(|s| self.rec.page.get(s))
            .collect();
        for (at, s) in step.claim.sentences().into_iter().enumerate() {
            let Some(node) = self.rec.page.get(&s) else {
                return Route::no(format!(
                    "{}, which the checker did not read",
                    s.text()
                ));
            };
            // A set the claim's other sentences say is finite counts as one
            // here, W of "W is finite and |W| ≥ k", by the one reading of
            // what lines make finite (`citing::finite::finite_sets`); and one
            // the sentence says of itself, a count given as a number at least
            // 1, by the step's bounds as the checker recorded them
            // (`CheckedTheorem::bounds`). A count that may be 0 does not
            // vouch for itself.
            let others: Vec<&Node> = sentences
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != at)
                .filter_map(|(_, o)| *o)
                .collect();
            let positive = |n: &Node| {
                crate::citing::bounds::least(&self.writer, n).is_some_and(|l| l >= 1)
            };
            let grammar = &self.sources.checked.grammar;
            let mut writer = self.writer.with_letters(self.writer.letters.clone());
            let by_others =
                crate::citing::finite::finite_sets(grammar, others, &positive);
            let by_itself =
                crate::citing::finite::finite_sets_vouched(grammar, [node], &positive);
            for (set, why) in by_others.into_iter().chain(by_itself) {
                writer.finite.entry(set).or_insert(why);
            }
            // A claim of numerals alone is written in the type of the lines
            // it is reached from, where any are cited.
            let printed = if node.names().is_empty() {
                let mut floor = super::templates::Num::Int;
                for c in self.cited_parts(&step.just.refs) {
                    for side in
                        c.node.children.iter().filter(|s| self.writer.is_number(s))
                    {
                        if let Route::Built(n) = self.writer.carrier(side) {
                            floor = floor.max(n);
                        }
                    }
                }
                writer.closed_formula(node, floor)
            } else {
                writer.formula(node)
            };
            let printed = match printed {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            out.push((at, node.clone(), printed));
        }
        Route::Built(out)
    }

    /// The Lean names of a step's sentences: `s2` for one, `s2a`, `s2b` for
    /// several.
    fn names_of(step: &Step, count: usize) -> Vec<String> {
        let base = match step.number.number() {
            Some(n) => line_name(&n.to_string()),
            None => "sThm".to_string(),
        };
        if count == 1 {
            return vec![base];
        }
        (0..count)
            .map(|i| format!("{base}{}", (b'a' + i as u8) as char))
            .collect()
    }

    /// The letters a step's claim introduces, `k ∈ ℤ`, added to those in
    /// scope. A claim of a letter already in scope introduces nothing: it
    /// says something of the letter, a fact a later step may use.
    fn introduce(&mut self, step: &Step) {
        for s in step.claim.sentences() {
            if let Some(node) = self.rec.page.get(&s) {
                let letter = introduces(node)
                    .map(|(l, _)| l)
                    .or_else(|| super::statement::range_letter(node));
                let known = letter
                    .is_some_and(|l| self.writer.letters.contains_key(l.as_str()));
                if known {
                    continue;
                }
                if let Some((letter, system)) = introduces(node) {
                    self.writer.introduce(&letter, system);
                } else if let Some(letter) = super::statement::range_letter(node) {
                    // In ℕ or ℕ₀ where the range starts at 1 or 0, as the
                    // page says once (`citing::range_system`).
                    let system = match node.children.get(1) {
                        Some(range) => super::expr::range_letter_system(range),
                        None => super::expr::System::Type(super::templates::Num::Int),
                    };
                    self.writer.introduce(&letter, system);
                } else if let Some((letter, members)) = self.set_member_said(node) {
                    self.writer.letters.insert(letter, members.letter());
                } else if let Some((letter, members)) = self.part_said(node) {
                    self.writer.letters.insert(letter, LetterType::Set(members));
                } else if let Some((letter, ty)) = self.function_said(node) {
                    self.writer.letters.insert(letter, ty);
                } else if let Some(letter) =
                    super::statement::introduces_polynomial(node)
                {
                    self.writer.letters.insert(
                        letter,
                        LetterType::Function {
                            from: super::templates::Num::Complex,
                            to: super::templates::Num::Complex,
                        },
                    );
                }
            }
        }
    }

    /// The letter a line says is a function between sets, `g : {1, …, j} →
    /// ℕ`, where the letter is new, with the type `Writer::function_between`
    /// gives it.
    fn function_said(&self, node: &Node) -> Option<(String, LetterType)> {
        let [g, from, to] = node.children.as_slice() else {
            return None;
        };
        let new = node.notation() == crate::notations::FUNCTION_TYPE
            && g.is_name()
            && !self.writer.letters.contains_key(g.text.as_str());
        new.then(|| self.writer.function_between(from, to))
            .flatten()
            .map(|ty| (g.text.to_string(), ty))
    }

    /// The letter a line says is a part of a set, `W ⊆ X`, where the letter
    /// is new and the writer has a type for X's members: a set of those.
    fn part_said(&self, node: &Node) -> Option<(String, super::expr::Members)> {
        let [w, set] = node.children.as_slice() else {
            return None;
        };
        let new = &*node.notation_name() == "subset"
            && w.is_name()
            && !self.writer.letters.contains_key(w.text.as_str());
        new.then(|| self.writer.members_of(set))
            .flatten()
            .map(|m| (w.text.to_string(), m))
    }

    /// The letter a line says is a member of a set, `x ∈ A`, where the
    /// letter is new and the writer has a type for A's members.
    fn set_member_said(&self, node: &Node) -> Option<(String, super::expr::Members)> {
        let [x, set] = node.children.as_slice() else {
            return None;
        };
        let new = node.notation() == crate::notations::MEMBERSHIP
            && x.is_name()
            && !self.writer.letters.contains_key(x.text.as_str());
        new.then(|| self.writer.members_of(set))
            .flatten()
            .map(|m| (x.text.to_string(), m))
    }

    fn step(&mut self, i: usize, depth: usize) -> Route<()> {
        let step = &self.thm.steps[i];
        // A function the header lets by its value is its equation for every
        // x (`header_function`), which a step citing the define or
        // substituting from it puts in, and a calculation's rows citing it;
        // a step of another method citing it, an algebra from D1, does not.
        let through = !matches!(
            step.just.head,
            crate::corpus::Head::Define
                | crate::corpus::Head::Method(
                    crate::corpus::Method::Substitute
                        | crate::corpus::Method::Calculation
                )
        );
        if through
            && step
                .just
                .refs
                .iter()
                .any(|r| self.header_function_named(r).is_some())
        {
            return Route::left_out(
                "a step cites a function the header lets through a method, which its equation for every x is not put in by",
            );
        }
        // A square root of y − 3 is Mathlib's real one once a line in scope
        // says y − 3 ≥ 0 (`Writer::principal_is_real`), as the check read
        // the lines in scope (`CheckedTheorem::bounds`).
        if let Some(said) = self.rec.bounds.get(i) {
            self.writer.bounds = said.clone();
        }
        // A set a line in scope says is finite, W of a step "W is finite"
        // above, is counted as a natural number from there on, as one the
        // hypotheses make finite is (`CheckedTheorem::finite_at`).
        self.writer.finite = self.rec.said_finite.sets.clone();
        // Of a set both give a reason for, the step's own, from the lines in
        // scope there: R ⊆ X of a finite X, where the theorem has only that R
        // is bound over sets of finite sets, which names no line to prove it
        // from.
        if let Some(said) = self.rec.finite_at.get(i) {
            for (set, why) in said {
                self.writer.finite.insert(set.clone(), why.clone());
            }
        }
        // The defines written above this step in its block, where the
        // checker opens them.
        let due: Vec<usize> = (0..self.thm.defines.len())
            .filter(|&d| {
                !self.defined.contains(&d)
                    && self.thm.defines[d].line < step.line
                    && self.thm.defines[d].line > self.thm.conclusion_line
                    && self.rec.defines.get(d).copied().flatten() == self.rec.places[i]
            })
            .collect();
        for d in due {
            if let Route::Declined(why) = self.define(d, depth) {
                return Route::Declined(why);
            }
        }
        let spot = Self::step_spot(step);
        self.push_at(
            depth,
            Tactic::Comment(format!("{}. {}", step.number, step.just.text.trim())),
            step.line,
            spot.clone(),
        );
        // The claim's first sentence as the page reads it, whose leading
        // "for all" binds letters its requires lines may speak of.
        let claimed = step
            .claim
            .sentences()
            .first()
            .and_then(|s| self.rec.page.get(s))
            .cloned();
        // A requires line is the step's, and the citation on one reads the
        // step's requires lines above it by the step's names.
        self.step_now.set(Some(i));
        for (k, r) in step.requires.iter().enumerate() {
            let node = match self.tree(&r.fact) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            // A requires line of a letter the claim says "for all" of, x²
            // ≥ 0 of every x ∈ [0, 1], is said under the claim's binders and
            // proved with its letters given.
            let under = claimed
                .as_ref()
                .filter(|c| bound_in(c, &node))
                .map(|c| under_binders(c, &node));
            let stated = under.clone().unwrap_or_else(|| node.clone());
            let fact = match self.writer.formula(&stated) {
                Route::Built(f) => f,
                Route::Declined(d) => return Route::Declined(d),
            };
            if fact.is_truth() {
                continue;
            }
            let Ok(just) = &r.by else {
                return Route::no("a requires line whose reason does not read");
            };
            let reason = Reason {
                just,
                cited: self.rec.cited_requires.get(&r.line),
            };
            *self.named_now.borrow_mut() = Some(just.refs.iter().cloned().collect());
            *self.held_now.borrow_mut() = self.held_at(just.line);
            let proof = match &under {
                // Its whole numbers named from the lines its own reason
                // cites, p^(a′ − a) ∈ ℤ from 3.3.
                None => {
                    let facts = self.cited_parts(&just.refs);
                    self.proof_named_from(reason, 0, &node, i, &facts)
                }
                Some(wrapped) => {
                    let (intros, _, inner) = self.peel(wrapped);
                    let outer = std::mem::replace(&mut self.writer, inner);
                    let proof = self.proof_of(reason, 0, &node);
                    self.writer = outer;
                    proof.map(|p| after_intros(&intros, p))
                }
            };
            let proof = match proof {
                Route::Built(t) => t,
                Route::Declined(d) => return Route::Declined(d),
            };
            let name = format!("r{}_{}", step.line, k + 1);
            // A requires line is a line in scope from here, as a step's
            // claim is: what names an integer it says one is. It says what
            // its `have` states, whatever writer later reads it.
            if let Route::Built(node) = self.tree(&r.fact) {
                let mut line = LineSentence::only(node, name.clone());
                line.says = Some(fact.clone());
                self.trees.insert(name.clone(), vec![line]);
            }
            self.push_at(
                depth,
                Tactic::Have {
                    name,
                    says: fact.clone(),
                    proof: Box::new(proof),
                },
                r.line,
                spot.clone(),
            );
        }
        let mut named: std::collections::BTreeSet<String> =
            step_cited_refs(step, &self.thm.path).into_iter().collect();
        named.extend(
            (0..step.requires.len()).map(|k| format!("r{}_{}", step.line, k + 1)),
        );
        *self.named_now.borrow_mut() = Some(named);
        *self.held_now.borrow_mut() = self.held_at(step.just.line);
        self.step_now.set(Some(i));
        if let Head::Method(Method::Obtain) = step.just.head {
            return self.obtain(i, depth);
        }
        self.introduce(step);
        let claimed = match self.claimed(step) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let claim = Self::without_places(&claimed);
        let names = Self::names_of(step, claim.len());
        if let Some(n) = step.number.number() {
            self.named.insert(n.to_string(), names.clone());
            let said = Self::claim_sentences(&claimed, &names);
            self.store(n.to_string(), said);
        }
        if let Head::Method(m) = step.just.head {
            // A calculation's lines are its proof, written as Lean's calc;
            // every other block's steps stand in it.
            if m.takes_block() && m != Method::Calculation {
                // The lines inside a block are out of scope after it, and
                // the claim the block proves is no line in scope inside it.
                let own = step.number.number().map(|n| n.to_string());
                let claimed = own.as_ref().and_then(|n| self.trees.shift_remove(n));
                let visible: std::collections::BTreeSet<String> =
                    self.trees.keys().cloned().collect();
                let written = self.block(i, m, &claim, &names, depth);
                self.trees.retain(|k, _| visible.contains(k));
                if let (Some(n), Some(said)) = (own, claimed) {
                    self.store(n, said);
                }
                return written;
            }
        }
        let reason = Reason {
            just: &step.just,
            cited: self.rec.cited[i].as_ref(),
        };
        let places: Vec<usize> = match self.claimed(step) {
            Route::Built(c) => c.into_iter().map(|(at, _, _)| at).collect(),
            Route::Declined(d) => return Route::Declined(d),
        };
        for (k, (node, prop)) in claim.iter().enumerate() {
            // A citation for a claim said "for all k ∈ …" of an item said of
            // one k, its letters given values in the claim's k: the item
            // cited at that k, given as a method takes it (`peel`). An item
            // that says the "for all" itself is cited whole.
            let cites_for_all = matches!(reason.just.head, Head::Item { .. })
                && node.notation() == crate::notations::FOR_ALL
                && self.cited_at_bound_letter(reason.cited, node);
            let proof = if cites_for_all {
                let (intros, body, inner) = self.peel(node);
                let outer = std::mem::replace(&mut self.writer, inner);
                let proof = self.proof_of(reason, places[k], body);
                self.writer = outer;
                proof.map(|p| match intros.is_empty() {
                    true => p,
                    false => after_intros(&intros, p),
                })
            } else {
                self.proof_with_named(reason, places[k], node, i)
            };
            let proof = match proof {
                Route::Built(t) => t,
                Route::Declined(d) => return Route::Declined(d),
            };
            self.push_at(
                depth,
                Tactic::Have {
                    name: names[k].clone(),
                    says: prop.clone(),
                    proof: Box::new(proof),
                },
                step.line,
                spot.clone(),
            );
        }
        if step.impossible {
            // A line of roots or of π, ln, exp, sin or cos, √2 − 1 = 0, is
            // shown false by real arithmetic; any other by `norm_num`.
            let real = claim.iter().any(|(node, _)| {
                node.walk().iter().any(|n| {
                    matches!(&*n.notation_name(), "square-root" | "pi")
                        || n.children.first().is_some_and(|f| {
                            matches!(&*f.text, "cos" | "sin" | "exp" | "ln" | "tan")
                        })
                })
            });
            use super::tactics as t;
            let refute = match real {
                true => t::bridge(BridgeTactic::Real, vec![]),
                false => t::call("norm_num", vec![]),
            };
            if let Some(last) = names.last() {
                let refuted = super::tactics::by_term(super::doc::Proof::By(refute));
                let absurd = Printed::applied(
                    "absurd",
                    super::doc::Source::Core,
                    vec![t::hyp(last), refuted],
                    super::doc::LeanType::Prop,
                );
                self.push_at(depth, Tactic::Exact(absurd), step.line, spot.clone());
            }
        }
        Route::Built(())
    }

    /// A sentence of the page as the checker read it.
    fn tree(&self, written: &Written) -> Route<Node> {
        match written
            .sentences()
            .first()
            .and_then(|s| self.rec.page.get(s))
        {
            Some(node) => Route::Built(node.clone()),
            None => Route::no(format!(
                "{}, which the checker did not read",
                written.text()
            )),
        }
    }

    /// The widest fixed type a hole of the claim takes, ℝ of ⌊A/B⌋, which
    /// a term in that hole is computed in; ℤ where there is none.
    fn held_in(&self, claim: &Node) -> super::templates::Num {
        claim
            .walk()
            .iter()
            .filter_map(|n| self.writer.template(n).built())
            .flat_map(|t| t.holes.iter())
            .filter_map(|s| match s {
                super::templates::Slot::Fixed(n) => Some(*n),
                _ => None,
            })
            .fold(super::templates::Num::Int, std::cmp::Ord::max)
    }

    /// The proof of sentence `k` of step `i`'s claim, where the claim puts
    /// a term Lean does not compute as a whole number in a slot for one,
    /// "2^p − 1 divides 2^(p − 1)·2", written `∃ m : ℤ, (m : ℚ) = … ∧ …`
    /// (`Writer::slot_witness`): the whole number it is, named from the
    /// lines the step names as Metamath proves its membership from them
    /// (`name_wholes`), given as the witness, and the reason proving the
    /// claim of it. Of any other claim, `proof_of`.
    fn proof_with_named(
        &mut self,
        reason: Reason,
        k: usize,
        node: &Node,
        i: usize,
    ) -> Route<super::doc::Proof> {
        let facts = self.step_facts(i);
        self.proof_named_from(reason, k, node, i, &facts)
    }

    /// `proof_with_named`, its numbers named from `facts`: a step's lines,
    /// or those a requires line's own reason cites.
    fn proof_named_from(
        &mut self,
        reason: Reason,
        k: usize,
        node: &Node,
        i: usize,
        facts: &[super::algebra::Cited],
    ) -> Route<super::doc::Proof> {
        use super::doc::Proof;
        let Some(letters) = self.rec.introduced.get(i).cloned() else {
            return Route::no("a step the checker's record has no letters for");
        };
        // A claim that a term Lean does not compute as a whole number is
        // one, p^(a′ − a) ∈ ℕ, written `∃ m : ℤ, 0 < m ∧ (m : ℚ) = …`
        // (`Writer::in_system`): the number the step's lines name is the
        // witness, and of ℕ or ℕ₀ its order the step's reason, said of it.
        if let Some((term, whole, ordered)) = self.wide_member(node) {
            let mut atoms = Vec::new();
            // Where the step's lines name no such number, the membership is
            // what the lines in scope give (`member_by_integers`).
            if self
                .name_wholes(&term, &letters, whole, facts, &mut atoms)
                .built()
                .is_none()
            {
                // Beside an equation, as the check found it.
                if !ordered {
                    let line = reason.just.line;
                    if let Some(p) =
                        self.member_beside(line, &term, node, &letters, facts)
                    {
                        return Route::Built(p);
                    }
                }
                return self.proof_of(reason, k, node);
            }
            let mut inner = self.writer.with_letters(self.writer.letters.clone());
            inner.integers.extend(atoms.iter().map(|a| a.said.clone()));
            let int = match inner.number_fixed(&term, super::templates::Num::Int) {
                Route::Built(p) => whole_term(p),
                Route::Declined(d) => return Route::Declined(d),
            };
            let specs: Vec<Printed> = atoms.iter().map(|a| spec_of(&a.said)).collect();
            let equal = specs_equal_of(&term, &specs);
            let mut haves: Vec<Tactic> = atoms.iter().map(|a| a.have.clone()).collect();
            if !ordered {
                let shown = Tactic::Exact(super::expr::anonymous(vec![int, equal]));
                return Route::Built(haves_then(haves, Proof::By(shown)));
            }
            let outer = std::mem::replace(&mut self.writer, inner);
            let proof = self.proof_of(reason, k, node);
            self.writer = outer;
            let proof = match proof {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            haves.push(refine(vec![
                int,
                Printed::of(super::doc::TermKind::Open, super::doc::LeanType::Prop),
                equal,
            ]));
            haves.push(tactic_of(&proof));
            return Route::Built(Proof::Block(haves));
        }
        let claimed = self.writer.wide_in_slot(node);
        // The lines the step cites that say something of a whole number a
        // term is, `∃ m : ℤ, (m : ℚ) = 2 ^ (p − 1) ∧ …`, or that none is,
        // `¬ ∃ m : ℤ, …`, by the name they stand under, which a
        // restatement of them takes.
        let cited: Vec<CitedWitness> = self
            .cited_parts(&step_cited_refs(&self.thm.steps[i], &self.thm.path))
            .into_iter()
            .filter(|c| matches!(c.proof.kind, super::doc::TermKind::Letter(_)))
            .filter_map(|c| {
                let (said, negated) =
                    match (c.node.notation(), c.node.children.as_slice()) {
                        (crate::notations::LOGICAL_NOT, [inner]) => (inner, true),
                        _ => (&c.node, false),
                    };
                let (term, whole) = self.writer.wide_in_slot(said)?;
                Some(CitedWitness {
                    name: c.proof.text(),
                    term,
                    whole,
                    negated,
                })
            })
            .collect();
        if claimed.is_none() && cited.is_empty() {
            return self.proof_of(reason, k, node);
        }
        let mut atoms = Vec::new();
        if let Some((term, whole)) = &claimed {
            if let Route::Declined(d) =
                self.name_wholes(term, &letters, *whole, facts, &mut atoms)
            {
                return Route::Declined(d);
            }
        }
        // A cited line whose term no line the step names makes whole is left
        // as it is: the step may not need it so.
        let cited: Vec<_> = cited
            .into_iter()
            .filter(|c| {
                let before = atoms.len();
                let named = self
                    .name_wholes(&c.term, &letters, c.whole, facts, &mut atoms)
                    .built()
                    .is_some();
                if !named {
                    atoms.truncate(before);
                }
                named
            })
            .collect();
        let mut inner = self.writer.with_letters(self.writer.letters.clone());
        inner.integers.extend(atoms.iter().map(|a| a.said.clone()));
        // Each named number's equation with its term: the one a step proves
        // of a power written out, the line's witness's for one it gives.
        let specs: Vec<Printed> = atoms.iter().map(|a| spec_of(&a.said)).collect();
        let equal = specs_equal(&specs);
        let mut haves: Vec<Tactic> = atoms.iter().map(|a| a.have.clone()).collect();
        // Each such cited line, said of the number the step names.
        for c in &cited {
            let int = match inner.number_fixed(&c.term, c.whole) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            let lemma = match (c.whole, c.negated) {
                (super::templates::Num::Nat, false) => "parley_witness_at_nat",
                (super::templates::Num::Nat, true) => "parley_witness_not_at_nat",
                (_, false) => "parley_witness_at",
                (_, true) => "parley_witness_not_at",
            };
            let at = Printed {
                kind: super::doc::TermKind::App {
                    head: Box::new(super::tactics::bridge_lemma(
                        lemma,
                        BridgeModule::PowerTactics,
                    )),
                    args: [super::tactics::hyp(&c.name), int, equal.clone()]
                        .into_iter()
                        .map(super::doc::Arg::Explicit)
                        .collect(),
                    explicit: false,
                },
                ty: Some(super::doc::LeanType::Prop),
            };
            haves.push(Tactic::Name {
                name: c.name.clone(),
                term: at,
            });
            // The line, restated under its own name, says from here on what
            // it says of the number it was restated through, and of no other
            // the step names: `parley_witness_at` puts that one alone
            // (`store`).
            let term = self.writer.grammar.print(&c.term);
            let mut through = self.writer.with_letters(self.writer.letters.clone());
            through.integers.extend(
                atoms
                    .iter()
                    .filter(|a| a.said.term == term)
                    .map(|a| a.said.clone()),
            );
            for s in self.trees.values_mut().flatten() {
                if s.name.as_deref() == Some(c.name.as_str()) {
                    s.says = through.formula(&s.node).built();
                }
            }
        }
        // Each other line the step cites is put in terms of the numbers the
        // step names as well, and cast down to them: 5.7.7's f(a) =
        // (a^(p − 2)) mod p, of reals, as f a = c % p of integers, which a
        // substitution then puts into the restated 5.7.6.
        let mut terms: Vec<Node> = Vec::new();
        for t in claimed
            .iter()
            .map(|(t, _)| t)
            .chain(cited.iter().map(|c| &c.term))
        {
            terms.extend(t.walk());
        }
        let mut rules = Vec::new();
        for a in atoms.iter().filter(|a| a.said.value.is_none()) {
            let Some(term) = terms
                .iter()
                .find(|n| self.writer.grammar.print(n) == a.said.term)
            else {
                continue;
            };
            let line = SaidLine {
                proof: a.said.proof.clone(),
                beside: Beside::Nothing,
            };
            if let Some(rule) = self.spec_at_real(&line, line.equation(), term) {
                rules.push(super::tactics::backwards(rule));
            }
        }
        let witnesses: Vec<&str> = cited.iter().map(|c| c.name.as_str()).collect();
        let others: Vec<String> = self.thm.steps[i]
            .just
            .refs
            .iter()
            .filter_map(|r| self.named.get(r))
            .flatten()
            .filter(|n| !witnesses.contains(&n.as_str()))
            .cloned()
            .collect();
        if !rules.is_empty() {
            use super::doc::Location;
            use super::tactics as t;
            for name in others {
                let at = || TacticArg::At(vec![Location::Hypothesis(name.clone())]);
                haves.push(t::try_(Tactic::Seq(vec![
                    t::call("rw", vec![TacticArg::Rules(rules.clone()), at()]),
                    t::try_(t::call(
                        "rw",
                        vec![TacticArg::Rules(vec![t::forwards(mod_int_cast())]), at()],
                    )),
                    t::call("norm_cast", vec![at()]),
                ])));
            }
        }
        let int = match &claimed {
            Some((term, whole)) => match inner.number_fixed(term, *whole) {
                Route::Built(p) => Some(whole_term(p)),
                Route::Declined(d) => return Route::Declined(d),
            },
            None => None,
        };
        let outer = std::mem::replace(&mut self.writer, inner);
        self.named_specs = specs.clone();
        self.in_witness.set(int.is_some());
        let proof = self.proof_of(reason, k, node);
        self.in_witness.set(false);
        self.named_specs.clear();
        self.writer = outer;
        let proof = match proof {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        match int {
            Some(int) => {
                let open =
                    Printed::of(super::doc::TermKind::Open, super::doc::LeanType::Prop);
                haves.push(refine(vec![int, equal, open]));
                haves.push(tactic_of(&proof));
                Route::Built(Proof::Block(haves))
            }
            None => Route::Built(haves_then(haves, proof)),
        }
    }

    /// Of a claim that a term Lean computes in ℚ or wider is a whole number,
    /// p^(a′ − a) ∈ ℕ, the term, the type its parts are named in (ℤ, the
    /// page's ℕ being integers), and whether the claim orders it, 0 < m or
    /// 0 ≤ m beside the integer m it is; None for any other claim, one of a
    /// letter among them.
    fn wide_member(&self, node: &Node) -> Option<(Node, super::templates::Num, bool)> {
        use super::expr::System;
        use super::templates::Num;
        let [term, set] = node.children.as_slice() else {
            return None;
        };
        if node.notation() != crate::notations::MEMBERSHIP || term.is_name() {
            return None;
        }
        let (whole, ordered) = match super::expr::system_of(set)? {
            System::Positive | System::NonNegative => (Num::Int, true),
            System::Type(Num::Int) => (Num::Int, false),
            _ => return None,
        };
        let wide = self.writer.carrier(term).built()? > Num::Int;
        wide.then(|| (term.clone(), whole, ordered))
    }

    /// The lines step `i` names, by which it names whole numbers: its
    /// requires lines and the lines it cites, each with its Lean name.
    fn step_facts(&self, i: usize) -> Vec<super::algebra::Cited> {
        let step = &self.thm.steps[i];
        let mut facts = Vec::new();
        for (k, r) in step.requires.iter().enumerate() {
            if let Route::Built(node) = self.tree(&r.fact) {
                facts.push(super::algebra::Cited {
                    node,
                    proof: super::tactics::hyp(&format!("r{}_{}", step.line, k + 1)),
                    says: None,
                });
            }
        }
        let cited = self.cited_parts(&step.just.refs);
        // A "for all" line is read at the block's letter the claim names, as
        // the checker reads it: 5.6's "for all a ∈ {2, …, p − 2}, f(a) ∈ ℤ"
        // says f(a) ∈ ℤ at the block's a.
        let mut names = std::collections::BTreeSet::new();
        for s in step.claim.sentences() {
            if let Some(n) = self.rec.page.get(&s) {
                names.extend(n.names());
            }
        }
        for c in &cited {
            if let Some(at) = self.at_recorded_letter(c, &names) {
                conjuncts(&at.node, at.proof, at.says, &mut facts);
            }
        }
        facts.extend(cited);
        let beside = self.shown_beside(i, &facts);
        facts.extend(beside);
        facts
    }

    /// The memberships the checker found step `i` shows by an equation
    /// (`ShownBy::Beside`), each as a line Lean has: the line putting the
    /// equation's other side in its system, rewritten by the equation,
    /// `(by simpa only [← e] using h : ∃ m : ℤ, ↑m = a * f a)`; or, where
    /// the other side is said once and Lean computes it as an integer, that
    /// integer with the equation, `⟨p ^ 2 + q ^ 2, by exact_mod_cast e⟩`.
    /// The facts are the step's, which hold both lines; a membership whose
    /// lines Lean does not hold as the checker read them is left out.
    fn shown_beside(
        &self,
        i: usize,
        facts: &[super::algebra::Cited],
    ) -> Vec<super::algebra::Cited> {
        use super::doc::Proof;
        use super::tactics as t;
        use crate::checker::record::ShownBy;
        let ctx = self.sources.ctx;
        let mut out = Vec::new();
        for shown in self.rec.places_shown.get(i).into_iter().flatten() {
            let ShownBy::Beside(beside) = &shown.by else {
                continue;
            };
            let other = &beside.other;
            let Some(e) = facts
                .iter()
                .find(|f| crate::matching::alike_top(&f.node, &beside.equation, ctx))
            else {
                continue;
            };
            // e is term = other, or other = term where it faces turned.
            let term_first = beside.facing == Facing::Straight;
            // The line the checker found states the other side's membership.
            let held = beside.other_stated.as_ref().and_then(|stated| {
                facts
                    .iter()
                    .find(|f| crate::matching::alike_top(&f.node, stated, ctx))
            });
            let (node, proved) = match held {
                // A line puts the other side in the system: it, rewritten by
                // the equation, which turns the other side into the term.
                Some(h) => {
                    let node = h.node.with_children(vec![
                        shown.term.clone(),
                        h.node.children[1].clone(),
                    ]);
                    let rule = match term_first {
                        true => t::backwards(e.proof.clone()),
                        false => t::forwards(e.proof.clone()),
                    };
                    let simpa = t::call(
                        "simpa",
                        vec![
                            TacticArg::Only,
                            TacticArg::Rules(vec![rule]),
                            TacticArg::Using(h.proof.clone()),
                        ],
                    );
                    (node, t::by_term(Proof::By(simpa)))
                }
                // The other side is said once, an integer Lean computes as
                // one, p² + q² of integers: that integer, and the equation
                // cast down.
                None if shown.system == crate::rules::System::Z => {
                    let int = super::templates::Num::Int;
                    let lean_whole =
                        self.writer.carrier(other).built().is_some_and(|c| c <= int);
                    let Some(number) = self.writer.number_fixed(other, int).built()
                    else {
                        continue;
                    };
                    if !lean_whole {
                        continue;
                    }
                    let Some(set) = crate::formula::page::made_as(
                        &self.sources.checked.grammar,
                        "ℤ",
                        vec![],
                    ) else {
                        continue;
                    };
                    let node = crate::formula::page::made_as(
                        &self.sources.checked.grammar,
                        "_ ∈ _",
                        vec![shown.term.clone(), set],
                    );
                    let Some(node) = node else {
                        continue;
                    };
                    let equal = match term_first {
                        true => t::symm(e.proof.clone()),
                        false => e.proof.clone(),
                    };
                    let cast = t::by_term(Proof::By(t::exact_mod_cast(equal)));
                    (node, super::expr::anonymous(vec![number, cast]))
                }
                None => continue,
            };
            let Route::Built(says) = self.writer.formula(&node) else {
                continue;
            };
            let proof = ascribed(proved, says.clone());
            out.push(super::algebra::Cited {
                node,
                proof,
                says: Some(says),
            });
        }
        out
    }

    /// The whole numbers a term is made of that Lean does not compute as
    /// whole numbers, each named from a line step `i` names, by the said-once
    /// walk both backends read memberships with (`citing::reason_within`,
    /// over the checker's letters), each part the walk does not take apart
    /// held as the check found it (`held_reason`): 2^(p − 1) from the
    /// requires line `p − 1
    /// ∈ ℕ₀`, as `⟨2 ^ (p − 1).toNat, …⟩`; a term a line says is in ℤ, ℕ₀ or
    /// ℕ, from that line. A term made of such by +, − and · is written of
    /// them (`Writer::number`), so it keeps one form. Declined where no line
    /// the step names makes the term a whole number.
    fn name_wholes(
        &self,
        term: &Node,
        letters: &crate::citing::Introduced,
        whole: super::templates::Num,
        facts: &[super::algebra::Cited],
        out: &mut Vec<NamedAtom>,
    ) -> Route<()> {
        let system = match whole {
            super::templates::Num::Nat => crate::rules::System::N0,
            _ => crate::rules::System::Z,
        };
        let said =
            |t: &Node, s: crate::rules::System| self.held_reason(t, s, letters, facts);
        let nonzero = |d: &Node| crate::citing::nonzero_said_once(d, letters);
        let Some(reason) =
            crate::citing::reason_within(term, system, letters, &nonzero, &said)
        else {
            return Route::no(format!(
                "{}, put where a whole number is asked, is one by no line the step names",
                self.writer.grammar.print(term)
            ));
        };
        let top = match self.writer.carrier(term) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        };
        match self.atoms_of(term, &reason, whole, top, facts, out) {
            true => Route::Built(()),
            false => Route::no(format!(
                "{} is a whole number Lean is not shown, by the lines the step names",
                self.writer.grammar.print(term)
            )),
        }
    }

    /// The record's parts held by the lines of the reason on `line`
    /// (`CheckedTheorem::held_by_lines`); none for a line it has none of.
    fn held_at(&self, line: usize) -> Vec<crate::checker::record::HeldByLines> {
        self.rec
            .held_by_lines
            .get(&line)
            .cloned()
            .unwrap_or_default()
    }

    /// How the lines of the reason being written hold `term` in `system`, as
    /// the check found it; None where they do not.
    fn held(
        &self,
        term: &Node,
        system: crate::rules::System,
    ) -> Option<crate::checker::record::LinesHold> {
        let ctx = self.sources.ctx;
        let standard = |n: &Node| crate::matching::standard(n, ctx);
        let term = standard(term);
        self.held_now
            .borrow()
            .iter()
            .find(|h| {
                h.system == system
                    && crate::matching::alike_top(&standard(&h.term), &term, ctx)
            })
            .map(|h| h.by.clone())
    }

    /// Why a part the said-once walk does not take apart is in `system`, as
    /// the check found it (`held`): a line among `facts` stating it, or an
    /// operation the closure table names
    /// (`rules::WHOLE`), x mod n in ℕ₀ where x ∈ ℤ and n ∈ ℕ, built from
    /// its parts the same way. Of an operation whose parts are not the
    /// term's own children, a library function's value, none.
    fn held_reason(
        &self,
        term: &Node,
        system: crate::rules::System,
        letters: &crate::citing::Introduced,
        facts: &[super::algebra::Cited],
    ) -> Option<crate::citing::OnceReason> {
        use crate::checker::record::LinesHold;
        use crate::citing::OnceReason;
        use crate::rules::System;
        // How the check found the part held, of the lines the reason names;
        // a line stating it, or one the equation it stands beside makes
        // (`shown_beside`), is among `facts` under its Lean name.
        match self.held(term, system)? {
            LinesHold::Stated { .. } | LinesHold::Beside { .. } => {
                return named_line(facts, term, system, self.sources.ctx)
                    .map(|_| OnceReason::Stated);
            }
            LinesHold::Closed => {}
        }
        let op = self.sources.targets.operation(term)?;
        let w = crate::rules::WHOLE.iter().find(|w| w.op == op.label)?;
        let (Some(left_in), Some(right_in)) =
            (System::of_label(w.left.1), System::of_label(w.right.1))
        else {
            return None;
        };
        let own = op.parts.len() == term.children.len()
            && op
                .parts
                .iter()
                .zip(&term.children)
                .all(|(p, c)| std::ptr::eq(*p, c));
        if !own || !System::N0.within(system) {
            return None;
        }
        let said = |t: &Node, s: System| self.held_reason(t, s, letters, facts);
        let nonzero = |d: &Node| crate::citing::nonzero_said_once(d, letters);
        let mut parts = Vec::new();
        for (part, within) in op.parts.iter().zip([left_in, right_in]) {
            parts.push(crate::citing::reason_within(
                part, within, letters, &nonzero, &said,
            )?);
        }
        Some(OnceReason::Built(parts))
    }

    /// A membership `t ∈ ℤ` the check found beside an equation, by the line
    /// its reason is on (`CheckedTheorem::members_shown`): the equation's
    /// other side named whole from `facts` (`whole_witness`), and the
    /// equation, among them, turning the goal's t into it, `have other :
    /// ∃ m : ℤ, ↑m = a ^ (p − 2) * a := …; rw [s5_7_4]; exact other`. None
    /// where the check found t otherwise, or the lines do not give it so.
    fn member_beside(
        &self,
        line: usize,
        term: &Node,
        node: &Node,
        letters: &crate::citing::Introduced,
        facts: &[super::algebra::Cited],
    ) -> Option<super::doc::Proof> {
        use super::doc::Proof;
        use super::tactics as t;
        use crate::checker::record::ShownBy;
        let ctx = self.sources.ctx;
        let shown = self.rec.members_shown.get(&line)?;
        let ShownBy::Beside(beside) = &shown.by else {
            return None;
        };
        let other = &beside.other;
        if !crate::matching::alike_top(&shown.term, term, ctx) {
            return None;
        }
        let e = facts
            .iter()
            .find(|f| crate::matching::alike_top(&f.node, &beside.equation, ctx))?;
        let set = node.children.get(1)?.clone();
        let says = self
            .writer
            .formula(&node.with_children(vec![other.clone(), set]))
            .built()?;
        // Of another side Lean already computes whole, k of (N − 1)/2 = k,
        // the equation gives the witness itself (`member_by_equation`).
        if says.is_truth() {
            return None;
        }
        let named = self.whole_witness(other, letters, facts).built()?;
        // Which side the term is (`Besides::facing`).
        let rule = match beside.facing {
            Facing::Straight => t::forwards(e.proof.clone()),
            Facing::Turned => t::backwards(e.proof.clone()),
        };
        // One tactic to a line: the have's own proof may take several.
        Some(Proof::Block(vec![
            Tactic::Have {
                name: "other".to_string(),
                says,
                proof: Box::new(named),
            },
            t::call("rw", vec![TacticArg::Rules(vec![rule])]),
            Tactic::Exact(t::hyp("other")),
        ]))
    }

    /// `∃ m : ℤ, ↑m = t` of a term Lean computes wider, proved as a step
    /// proves its membership (`proof_named_from`): the whole number it is
    /// named from `facts` with `letters` (`name_wholes`), each named number's
    /// have, then `exact ⟨n, equal⟩`.
    fn whole_witness(
        &self,
        term: &Node,
        letters: &crate::citing::Introduced,
        facts: &[super::algebra::Cited],
    ) -> Route<super::doc::Proof> {
        use super::doc::Proof;
        let mut atoms = Vec::new();
        let int = super::templates::Num::Int;
        if let Route::Declined(d) =
            self.name_wholes(term, letters, int, facts, &mut atoms)
        {
            return Route::Declined(d);
        }
        let mut inner = self.writer.with_letters(self.writer.letters.clone());
        inner.integers.extend(atoms.iter().map(|a| a.said.clone()));
        let number = match inner.number_fixed(term, int) {
            Route::Built(p) => whole_term(p),
            Route::Declined(d) => return Route::Declined(d),
        };
        let specs: Vec<Printed> = atoms.iter().map(|a| spec_of(&a.said)).collect();
        let equal = specs_equal_of(term, &specs);
        let haves: Vec<Tactic> = atoms.iter().map(|a| a.have.clone()).collect();
        let shown = Tactic::Exact(super::expr::anonymous(vec![number, equal]));
        Route::Built(haves_then(haves, Proof::By(shown)))
    }

    /// `name_wholes` of one part, whose reason is `reason`, named in
    /// `whole`, ℤ or ℕ: false where a part is none the walk can name.
    fn atoms_of(
        &self,
        term: &Node,
        reason: &crate::citing::OnceReason,
        whole: super::templates::Num,
        top: super::templates::Num,
        facts: &[super::algebra::Cited],
        out: &mut Vec<NamedAtom>,
    ) -> bool {
        use super::templates::Num;
        use crate::citing::OnceReason;
        use crate::rules::System;
        let Some(own) = self.writer.carrier(term).built() else {
            return false;
        };
        // Each equation is stated in the type of the whole term the part is
        // in, ℚ of 2^(p − 1)·(2^p − 1), where it is put into that term's.
        let at = own.max(top);
        let already = match whole {
            Num::Nat => {
                self.writer.natural_form(term) != super::expr::NaturalForm::Integer
            }
            _ => own <= Num::Int,
        };
        if already {
            return true;
        }
        let printed = self.writer.grammar.print(term);
        if out.iter().any(|a| a.said.term == printed) {
            return true;
        }
        let Some(value) = self.writer.number_fixed(term, at).built() else {
            return false;
        };
        use super::doc::{LeanType, Op, Proof};
        use super::tactics as t;
        let name = format!("whole{}", out.len() + 1);
        let ty = self.writer.num_type(at);
        let (have, written) = match (reason, term.notation(), term.children.as_slice())
        {
            // A term a line the step names puts in ℕ, ℕ₀ or ℤ: that line's
            // witness, of ℕ where a natural number is asked.
            (OnceReason::Stated, _, _) => {
                let asked = match whole {
                    Num::Nat => System::N0,
                    _ => System::Z,
                };
                let Some(NamedLine { name: line, system }) =
                    named_line(facts, term, asked, self.sources.ctx)
                else {
                    return false;
                };
                // Of an integer, the line is an order, 0 < 2^p − 1 for ∈ ℕ:
                // the natural number is the integer's `toNat`, written out as
                // σ of an integer takes it, and its equation with the term.
                if own <= Num::Int {
                    let Some(int) = self.writer.number_fixed(term, Num::Int).built()
                    else {
                        return false;
                    };
                    let written = Printed::of(
                        super::doc::TermKind::ToNat(Box::new(t::bracket(int))),
                        LeanType::Num(Num::Nat),
                    );
                    let as_nat =
                        Printed::cast(written.clone(), LeanType::Num(Num::Nat));
                    let says = Printed::infix(
                        Op::EQUALS,
                        Printed::cast(as_nat, ty.clone()),
                        value,
                        LeanType::Prop,
                    );
                    let nonneg = nonneg_of(system, line);
                    out.push(NamedAtom {
                        have: Tactic::Have {
                            name: name.clone(),
                            says,
                            proof: Box::new(Proof::By(t::exact_mod_cast(to_nat_of(
                                nonneg,
                            )))),
                        },
                        said: super::expr::SaidInteger {
                            term: printed,
                            proof: t::hyp(&name),
                            ty: whole,
                            value: Some(written),
                            slot_only: true,
                        },
                    });
                    return true;
                }
                // Of a wider term, the line is a witness: `∃ m : ℤ, 0 ≤ m ∧
                // ↑m = t` for ℕ₀, `0 < m` for ℕ, `↑m = t` for ℤ. A natural
                // number asked is that integer's `toNat`, by its order. The
                // witness's letter is one the term does not write, m₀ of a
                // term in m (`witness_letter`).
                let letter = super::expr::witness_letter(term);
                let m = || t::hyp(&letter);
                let (letter_ty, names, witness) = match (system, whole) {
                    (System::N | System::N0, Num::Nat) => {
                        let m_nat = Printed::of(
                            super::doc::TermKind::ToNat(Box::new(m())),
                            LeanType::Num(Num::Nat),
                        );
                        let same = Printed::infix(
                            Op::EQUALS,
                            Printed::cast(
                                Printed::cast(m_nat.clone(), LeanType::Num(Num::Nat)),
                                ty.clone(),
                            ),
                            Printed::cast(
                                Printed::cast(m(), LeanType::Num(Num::Int)),
                                ty.clone(),
                            ),
                            LeanType::Prop,
                        );
                        let same_by = Proof::By(t::exact_mod_cast(to_nat_of(
                            nonneg_of(system, t::hyp("h0")),
                        )));
                        let rewritten = Proof::By(Tactic::Seq(vec![
                            t::call(
                                "rw",
                                vec![TacticArg::Rules(vec![t::forwards(shown(
                                    same, same_by,
                                ))])],
                            ),
                            t::exact_mod_cast(t::hyp("hm")),
                        ]));
                        (
                            Num::Nat,
                            vec![letter.as_str(), "h0", "hm"],
                            vec![m_nat, super::tactics::by_term(rewritten)],
                        )
                    }
                    (System::N | System::N0, _) => (
                        Num::Int,
                        vec![letter.as_str(), "_", "hm"],
                        vec![
                            m(),
                            super::tactics::by_term(cast_carried(
                                t::hyp("hm"),
                                own,
                                at,
                            )),
                        ],
                    ),
                    _ => (
                        whole,
                        vec![letter.as_str(), "hm"],
                        vec![
                            m(),
                            super::tactics::by_term(cast_carried(
                                t::hyp("hm"),
                                own,
                                at,
                            )),
                        ],
                    ),
                };
                let says = Printed::of(
                    super::doc::TermKind::Quantified {
                        quant: super::doc::Quant::Exists,
                        letter: letter.clone(),
                        letter_ty: LeanType::Num(letter_ty),
                        guard: None,
                        body: Box::new(Printed::infix(
                            Op::EQUALS,
                            Printed::cast(m(), ty.clone()),
                            value,
                            LeanType::Prop,
                        )),
                        bounded: false,
                    },
                    LeanType::Prop,
                );
                let proof = Proof::By(Tactic::Seq(vec![
                    Tactic::Obtain {
                        names: names.iter().map(|n| n.to_string()).collect(),
                        says: None,
                        from: line,
                    },
                    Tactic::Exact(super::expr::anonymous(witness)),
                ]));
                let have = Tactic::Have {
                    name: name.clone(),
                    says,
                    proof: Box::new(proof),
                };
                (have, None)
            }
            // A power to an exponent a line the step names puts in ℕ₀: the
            // base to that exponent's `toNat`, written out, and its equation
            // with the power, from that line.
            (OnceReason::Built(parts), crate::notations::POWER, [base, exponent]) => {
                let [base_reason] = parts.as_slice() else {
                    return false;
                };
                if self.writer.natural_form(exponent)
                    != super::expr::NaturalForm::Integer
                {
                    return self.atoms_of(base, base_reason, whole, top, facts, out);
                }
                let Some(NamedLine { name: line, system }) =
                    named_line(facts, exponent, System::N0, self.sources.ctx)
                else {
                    return false;
                };
                let (Some(b), Some(e), Some(cast_base)) = (
                    self.writer.number_fixed(base, whole).built(),
                    self.writer.number_fixed(exponent, Num::Int).built(),
                    self.writer.number_fixed(base, at).built(),
                ) else {
                    return false;
                };
                let power = Op::POWER;
                let e_nat = Printed::of(
                    super::doc::TermKind::ToNat(Box::new(t::bracket(e))),
                    LeanType::Num(Num::Nat),
                );
                let written =
                    Printed::infix(power, b, e_nat.clone(), LeanType::Num(whole));
                let says = Printed::infix(
                    Op::EQUALS,
                    Printed::infix(
                        power,
                        Printed::cast(cast_base, ty.clone()),
                        e_nat,
                        ty.clone(),
                    ),
                    value,
                    LeanType::Prop,
                );
                let rules = vec![
                    t::backwards(t::lemma("zpow_natCast")),
                    t::forwards(to_nat_of(nonneg_of(system, line))),
                ];
                let have = Tactic::Have {
                    name: name.clone(),
                    says,
                    proof: Box::new(Proof::By(t::call(
                        "rw",
                        vec![TacticArg::Rules(rules)],
                    ))),
                };
                (have, Some(written))
            }
            (OnceReason::Built(parts), _, kids) if parts.len() == kids.len() => {
                return kids.iter().zip(parts).all(|(kid, part)| {
                    self.atoms_of(kid, part, whole, top, facts, out)
                });
            }
            _ => return false,
        };
        out.push(NamedAtom {
            have,
            said: super::expr::SaidInteger {
                term: printed,
                proof: t::hyp(&name),
                ty: whole,
                value: written,
                slot_only: true,
            },
        });
        true
    }

    /// The proof of sentence `k` of a claim, by its reason.
    fn proof_of(
        &self,
        reason: Reason,
        k: usize,
        node: &Node,
    ) -> Route<super::doc::Proof> {
        use super::doc::Proof;
        if let Some(witness) = self.member_by_integers(node) {
            return Route::Built(witness);
        }
        self.said_used.borrow_mut().clear();
        let proof = match self.proof_by_reason(reason, k, node) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A citation given a line's number, ⌊m⌋ = m for the m of `A/B ∈
        // ℤ`, meets a goal that has the line's term, ⌊A/B⌋: the goal is put
        // in terms of the number first.
        let used = std::mem::take(&mut *self.said_used.borrow_mut());
        let specs = self.specs_in(node, &used);
        if specs.is_empty() {
            return Route::Built(proof);
        }
        use super::doc::Location;
        use super::tactics as t;
        let mut steps = vec![t::call("rw", vec![TacticArg::Rules(specs.clone())])];
        // A remainder of the named numbers, now of integers cast to ℝ, is
        // put as their `%`, which a cited item of integers states.
        if takes_remainder(node) {
            steps.push(t::try_(t::call(
                "rw",
                vec![TacticArg::Rules(vec![t::forwards(mod_int_cast())])],
            )));
        }
        // What the citation asks of a named number is said of it: the order
        // a line of ℕ or ℕ₀ gives beside its equation, or the range a line
        // of a range does, and each line the step cites, put in terms of the
        // numbers as the goal is and cast down to them, 5.5.2's mod(a^(p −
        // 2), p) < p as c < p.
        for u in &used {
            if let Some(beside) = u.line.besides() {
                steps.push(Tactic::Fact(beside));
            }
        }
        // A line that gives a number is left as it is: the number is chosen
        // from it, and a rewritten copy would be another line.
        let giving: Vec<String> = used.iter().map(|u| u.line.proof.text()).collect();
        let cited: Vec<String> = reason
            .just
            .refs
            .iter()
            .filter_map(|r| self.named.get(r))
            .flatten()
            .filter(|name| !giving.contains(name))
            .cloned()
            .collect();
        for name in cited {
            let at = || TacticArg::At(vec![Location::Hypothesis(name.clone())]);
            steps.push(t::try_(Tactic::Seq(vec![
                t::call("rw", vec![TacticArg::Rules(specs.clone()), at()]),
                t::call("norm_cast", vec![at()]),
            ])));
        }
        steps.push(tactic_of(&proof));
        Route::Built(Proof::By(Tactic::Seq(steps)))
    }

    /// Whether a citation gives its item's letters values in a letter the
    /// claim's leading "for all" binds: the item is cited at that letter.
    fn cited_at_bound_letter(
        &self,
        cited: Option<&crate::checker::record::Cited>,
        claim: &Node,
    ) -> bool {
        let Some(cited) = cited else {
            return false;
        };
        let mut bound = Vec::new();
        let mut body = claim;
        while let (crate::notations::FOR_ALL, [letter, _, inner]) =
            (body.notation(), body.children.as_slice())
        {
            bound.push(letter.text);
            body = inner;
        }
        // A letter free in a value: a value that binds it itself, Q := "for
        // all x, …", says the "for all" whole, and so does a function by its
        // values, t := k ↦ a(k)², whose k is its own.
        let binders = self.sources.checked.grammar.binders();
        cited.binding.values().any(|v| {
            let own = |n: &str| &*v.notation_name() == "property-of" && *v.text == *n;
            crate::matching::free_names(v, &binders)
                .iter()
                .any(|n| !own(n) && bound.iter().any(|b| **b == **n))
        })
    }

    /// The hypothesis of a function the theorem's header lets by its value,
    /// which a step cites by its label; None for any other citation.
    fn header_function_cited(&self, just: &Justification) -> Option<String> {
        self.header_function_named(just.defined.as_deref()?)
    }

    /// The hypothesis of a function the theorem's header lets by its value,
    /// by its label; None for any other label.
    fn header_function_named(&self, label: &str) -> Option<String> {
        let d = self
            .thm
            .defines
            .iter()
            .find(|d| d.label == label && d.line < self.thm.conclusion_line)?;
        match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::One(one))
                if !one.params.is_empty() =>
            {
                Some(line_name(&d.label))
            }
            _ => None,
        }
    }

    /// Whether the define of that label gives its value by cases, as the
    /// page reads its line (the `by-cases` notation).
    fn define_by_cases(&self, label: &str) -> bool {
        let Some(d) = self.thm.defines.iter().find(|d| d.label == label) else {
            return false;
        };
        self.rec
            .page
            .entries()
            .filter(|(key, _)| key.line == d.line)
            .any(|(_, n)| n.walk().iter().any(|m| &*m.notation_name() == "by-cases"))
    }

    /// The recursion a step cites by its label, the header's or one the
    /// proof lets, whose hypotheses are written alike; None for a citation
    /// of any other define.
    fn recursion_cited(&self, just: &Justification) -> Option<CitedRecursion> {
        let label = just.defined.as_deref()?;
        let d = self.thm.defines.iter().find(|d| d.label == label)?;
        let by_cases = self.define_by_cases(label);
        match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(rule)) => {
                Some(CitedRecursion {
                    rule,
                    hypothesis: line_name(&d.label),
                    by_cases,
                })
            }
            _ => None,
        }
    }

    /// A step citing a recursion's rule, F(k + 1) = G(k): the first of the
    /// claim's applications of its functions, F(a), says which. At the
    /// numeral 0 it is F's start; at any other a it is F's step at a − 1,
    /// with a − 1 + 1 put back as a, and the arguments put in one form. A
    /// rule by cases is taken at the case the cited lines say: an equation
    /// its condition, `ite_eq_left`; one denied, `otherwise`, `ite_eq_right`.
    /// Its condition is put at a first, a − 1 + 1 inside it as a, for the
    /// cited line to match.
    fn recursion_clause(
        &self,
        cited: &CitedRecursion,
        cases: &[super::algebra::Cited],
        claim: &Node,
        writer: &Writer,
    ) -> Route<super::doc::Proof> {
        use super::doc::Proof;
        use super::tactics as t;
        let (r, hyp) = (&cited.rule, &cited.hypothesis);
        let mut case_rewrites: Vec<Tactic> = Vec::new();
        if cited.by_cases {
            for c in cases {
                let lemma = match (c.node.notation(), c.node.children.as_slice()) {
                    (EQUALITY, _) => "ite_eq_left",
                    (crate::notations::LOGICAL_NOT, [inner])
                        if inner.notation() == EQUALITY =>
                    {
                        "ite_eq_right"
                    }
                    _ => continue,
                };
                let rule = Printed::applied(
                    lemma,
                    super::doc::Source::Mathlib,
                    vec![c.proof.clone()],
                    super::doc::LeanType::Prop,
                );
                case_rewrites
                    .push(t::call("rw", vec![t::rules(vec![rule]), t::at_h(false)]));
            }
        }
        let mut cancel = vec![t::forwards(t::lemma("sub_add_cancel"))];
        if !case_rewrites.is_empty() {
            cancel.push(t::forwards(t::lemma("add_sub_cancel_right")));
        }
        let applied = claim.walk().into_iter().find_map(|n| {
            let [f, a] = n.children.as_slice() else {
                return None;
            };
            let at = r.names.iter().position(|name| *name == *f.text)?;
            (n.notation() == crate::notations::APPLICATION).then(|| (at, a.clone()))
        });
        let Some((at, arg)) = applied else {
            return Route::no("a recursion cited for a claim of none of its functions");
        };
        let n = r.names.len();
        // The hypothesis is the starts and then the steps, joined by ∧.
        let start = projection_path(at, n + 1);
        let steps = projection_path(n, n + 1);
        let step = projection_path(at, n);
        let closed = t::call("linarith", vec![]);
        let worked = t::try_(t::call("ring_nf", vec![t::at_h(true)]));
        if arg.notation() == crate::notations::NUMERAL && &*arg.text == "0" {
            return Route::Built(Proof::By(Tactic::Seq(vec![
                t::name_h(&fields(t::hyp(hyp), &start)),
                worked,
                closed,
            ])));
        }
        let a = match writer.number_fixed(&arg, super::templates::Num::Int) {
            Route::Built(a) => a,
            Route::Declined(d) => return Route::Declined(d),
        };
        // The step at a − 1, a bracketed where it is a sum, as `a - 1`
        // reads it.
        let a = match a.prec() < 66 {
            true => t::bracket(a),
            false => a,
        };
        let int = super::doc::LeanType::Num(super::templates::Num::Int);
        let one_less = Printed::infix(
            super::doc::Op::MINUS,
            a,
            Printed::numeral("1", int.clone()),
            int,
        );
        let rule = fields(t::hyp(hyp), &steps);
        let omega = super::tactics::by_term(Proof::By(t::call("omega", vec![])));
        let at = Printed {
            kind: super::doc::TermKind::App {
                head: Box::new(rule),
                args: vec![
                    super::doc::Arg::Explicit(one_less),
                    super::doc::Arg::Explicit(omega),
                ],
                explicit: false,
            },
            ty: None,
        };
        let at_step = fields(t::bracket(at), &step);
        let mut tactics = vec![
            t::name_h(&at_step),
            t::simp_only(false, None, cancel, Some(t::at_h(false))),
        ];
        tactics.extend(case_rewrites);
        tactics.push(worked);
        tactics.push(closed);
        Route::Built(Proof::By(Tactic::Seq(tactics)))
    }

    /// A claim that a term of a wider type is an integer, a rational or a
    /// real, (A + B) − B ∈ ℚ of reals or √b + 1 ∈ ℝ of a square root in ℂ,
    /// where some part of it a line the step names says is in that type, as
    /// the check found it (`integer_line`): the term written there, that
    /// part the number the line gives, as Lean's witness. A citation of an item over ℚ gives such a
    /// claim nothing, as of rationals it holds by their type.
    fn member_by_integers(&self, node: &Node) -> Option<super::doc::Proof> {
        let [term, set] = node.children.as_slice() else {
            return None;
        };
        use super::templates::Num;
        // The type the term is said to be in, and the type its parts are
        // said to be in: ℕ₀ is said of an integer, its parts integers.
        let (claimed, ty) = match super::expr::system_of(set)? {
            super::expr::System::Type(t @ (Num::Int | Num::Rat | Num::Real)) => (t, t),
            super::expr::System::NonNegative => (Num::Nat, Num::Int),
            _ => return None,
        };
        let wide = self.writer.carrier(term).built()?;
        if node.notation() != crate::notations::MEMBERSHIP || wide <= ty {
            return None;
        }
        let mut writer = self.writer.with_letters(self.writer.letters.clone());
        let mut lines = Vec::new();
        // The parts within the term: the term itself is what the step
        // claims, and a letter of the type said is in it already; a letter
        // of a wider type, A ∈ ℝ, may be said an integer.
        let whole = writer.grammar.print(term);
        for part in term.walk() {
            let typed = part.is_name()
                && writer.carrier(&part).built().is_some_and(|c| c <= ty);
            if typed
                || part.notation() == crate::notations::NUMERAL
                || writer.grammar.print(&part) == whole
            {
                continue;
            }
            if let Some(said) = self.integer_line(&part, ty) {
                let line = said.proof;
                if lines.contains(&line) {
                    continue;
                }
                writer.integers.push(super::expr::SaidInteger {
                    term: writer.grammar.print(&part),
                    proof: line.clone(),
                    ty,
                    value: None,
                    slot_only: false,
                });
                lines.push(line);
            }
        }
        if lines.is_empty() {
            return None;
        }
        use super::tactics as t;
        let witness = writer.number_fixed(term, ty).built()?;
        let rules = lines
            .iter()
            .map(|line| {
                t::forwards(Printed::applied(
                    "Classical.choose_spec",
                    super::doc::Source::Core,
                    vec![line.clone()],
                    super::doc::LeanType::Prop,
                ))
            })
            .collect();
        // The named numbers' equations put in leave the claim closed, or
        // arithmetic for `parley_ring`.
        let equal = super::tactics::by_term(super::doc::Proof::By(Tactic::Seq(vec![
            t::push_cast(None),
            t::try_(t::simp_only(false, None, rules, None)),
            Tactic::AllGoals(Box::new(t::bridge(BridgeTactic::Ring, vec![]))),
        ])));
        let parts = match claimed {
            // In ℕ₀: the integer, beside its being at least 0.
            Num::Nat => vec![witness, side_term(&[]), equal],
            _ => vec![witness, equal],
        };
        let shown = Tactic::Exact(super::expr::anonymous(parts));
        Some(super::doc::Proof::By(Tactic::Group(Box::new(shown))))
    }

    fn proof_by_reason(
        &self,
        reason: Reason,
        k: usize,
        node: &Node,
    ) -> Route<super::doc::Proof> {
        use super::doc::Proof;
        use super::tactics as t;
        // A restate step, or a requires line of lines alone, whose claim the
        // checker found a line states (`restated`): that line, met as a
        // whole before any "for all" of the claim is taken apart.
        if matches!(
            reason.just.head,
            Head::Method(Method::Restate) | Head::Lines
        ) {
            if let Some(proof) = self.restated_proof(reason.just.line, node) {
                return Route::Built(proof);
            }
        }
        match &reason.just.head {
            Head::Item { .. } => self.citation(reason, k, node),
            Head::Method(m) => {
                // A claim said of every member of a set is proved of one,
                // taken as the method's letter. Substitute rows each say
                // the whole claim, "for all" and all, and end on it; so does
                // a substitution the checker found into a line's "for all"
                // as a whole, its places counted from the top of it
                // (`substituted`).
                let whole = self
                    .substitution_record(reason.just.line, Some(k), false)
                    .is_some_and(|r| r.start.notation() == crate::notations::FOR_ALL);
                let rows =
                    *m == Method::Substitute && (!reason.just.rows.is_empty() || whole);
                let (intros, body, writer) = match rows {
                    true => (
                        Vec::new(),
                        node,
                        self.writer.with_letters(self.writer.letters.clone()),
                    ),
                    false => self.peel(node),
                };
                let proof = match self.method_proof(reason, *m, k, body, &writer) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let proof = match self.count_conversion(*m, body, reason.just) {
                    CountConversion::None => proof,
                    CountConversion::Before => Proof::By(Tactic::Seq(vec![
                        t::bridge(BridgeTactic::CountInt, vec![]),
                        tactic_of(&proof),
                    ])),
                    CountConversion::After => Proof::By(t::bridge(
                        BridgeTactic::CountAfter,
                        vec![TacticArg::Term(t::bracket(super::tactics::by_term(
                            proof,
                        )))],
                    )),
                };
                Route::Built(with_intros(&intros, proof))
            }
            // A step citing a define claims its equation, which Lean's `set`
            // put in scope under the define's label.
            Head::Define => match self.recursion_cited(reason.just) {
                // A rule said for every n, F(n + 1) = 2F(n): said of one n.
                Some(r) => {
                    let (intros, body, writer) = self.peel(node);
                    let cases = self.cited_parts(&reason.just.from);
                    self.recursion_clause(&r, &cases, body, &writer)
                        .map(|clause| match intros.is_empty() {
                            true => clause,
                            false => Proof::By(Tactic::Seq(vec![
                                Tactic::Intro(intros.clone()),
                                tactic_of(&clause),
                            ])),
                        })
                }
                // A function the header lets by its value: its equation
                // put in, f(a) its value at a, and the claim closed, as it
                // stands where the checker met the claim's sides with the
                // value written out (`define_links`), and once worked out
                // where it recorded arithmetic left. Not of a value by cases,
                // whose case the record does not say, nor of a claim "for
                // all", where the equation's condition, its argument in the
                // function's domain, is to be shown of the claim's letter
                // and `omega` does not show it.
                None => match self.header_function_cited(reason.just) {
                    // A function the header lets by cases on a domain: its
                    // equation at the argument the cited line puts in the
                    // domain (`define_domains`), `hD1 _ h`, and the case the
                    // checker took (`define_cases`).
                    Some(hyp)
                        if reason
                            .just
                            .defined
                            .as_deref()
                            .is_some_and(|l| self.define_by_cases(l))
                            && self
                                .rec
                                .define_cases
                                .contains_key(&reason.just.line)
                            && self
                                .rec
                                .define_domains
                                .contains_key(&reason.just.line) =>
                    {
                        let taken = &self.rec.define_cases[&reason.just.line];
                        let domain = self.domain_proof(
                            &self.rec.define_domains[&reason.just.line],
                            None,
                        );
                        match (domain, self.conditions_put(taken, node)) {
                            (Route::Built(domain), Route::Built(conditions)) => {
                                let equation =
                                    hyp_applied(&hyp, vec![elided_term(), domain]);
                                let mut rules = vec![t::forwards(equation)];
                                rules.extend(conditions);
                                let alone =
                                    taken.meeting.as_ref().is_some_and(unfolds_alone);
                                Route::Built(Proof::By(simp_unfolded(
                                    rules,
                                    alone,
                                    node.notation() == crate::notations::FOR_ALL,
                                )))
                            }
                            _ => Route::Built(header_ways(&hyp)),
                        }
                    }
                    Some(hyp)
                        if self.rec.define_links.contains_key(&reason.just.line)
                            && !reason
                                .just
                                .defined
                                .as_deref()
                                .is_some_and(|l| self.define_by_cases(l))
                            && node.notation() != crate::notations::FOR_ALL =>
                    {
                        let met = &self.rec.define_links[&reason.just.line];
                        let alone = met.as_ref().is_some_and(unfolds_alone);
                        Route::Built(Proof::By(unfolded_by(&[hyp], alone, false)))
                    }
                    // A claim "for all" of a header's function: its equation
                    // at the member, where the record says what puts the
                    // member in the domain (`define_domains`).
                    Some(hyp)
                        if node.notation() == crate::notations::FOR_ALL
                            && !reason
                                .just
                                .defined
                                .as_deref()
                                .is_some_and(|l| self.define_by_cases(l)) =>
                    {
                        match self.for_all_by_header(&hyp, node, reason.just.line) {
                            Route::Built(p) => Route::Built(p),
                            Route::Declined(_) => Route::Built(header_ways(&hyp)),
                        }
                    }
                    Some(hyp) => Route::Built(header_ways(&hyp)),
                    // A define of the proof's, its equation under the
                    // define's label: unfolded, as a calculation row
                    // citing it is, L(k) = N(k)/10^k of L's `set`.
                    None => {
                        let unfold: Vec<String> = reason
                            .just
                            .refs
                            .iter()
                            .filter(|r| self.thm.defines.iter().any(|d| d.label == **r))
                            .filter_map(|r| self.named.get(r).and_then(|n| n.first()))
                            .cloned()
                            .collect();
                        // The claim's sides as the checker met them with the
                        // defines written out (`define_links`).
                        let met = self.rec.define_links.get(&reason.just.line);
                        // A define by cases, `h(i) = g(i) if i ≤ j, else p`,
                        // whose case the cited lines show: what the record
                        // says of its sides does not say which case holds.
                        let by_cases = reason.just.refs.iter().any(|r| {
                            self.thm.defines.iter().any(|d| d.label == *r)
                                && self.define_by_cases(r)
                        });
                        if let (Some(met), false, false) =
                            (met, unfold.is_empty(), by_cases)
                        {
                            let cast = match self.writer.formula(node) {
                                Route::Built(claim) => match &claim.kind {
                                    super::doc::TermKind::Infix {
                                        lhs, rhs, ..
                                    } => self.unfolds_to_casts(lhs, rhs),
                                    _ => false,
                                },
                                Route::Declined(_) => false,
                            };
                            let alone = met.as_ref().is_some_and(unfolds_alone);
                            return Route::Built(Proof::By(unfolded_by(
                                &unfold,
                                alone && !cast,
                                node.notation() == crate::notations::FOR_ALL,
                            )));
                        }
                        // A define by cases at the case the checker took
                        // (`define_cases`): each condition it passed put by
                        // the line that says it, `if_pos` where it holds and
                        // `if_neg` where it fails, and the case's value met
                        // with the other side as the record met them.
                        if let (Some(taken), false, true) = (
                            self.rec.define_cases.get(&reason.just.line),
                            unfold.is_empty(),
                            by_cases,
                        ) {
                            if let Route::Built(conditions) =
                                self.conditions_put(taken, node)
                            {
                                let alone =
                                    taken.meeting.as_ref().is_some_and(unfolds_alone);
                                let mut rules: Vec<super::doc::Rule> = unfold
                                    .iter()
                                    .map(|d| t::forwards(t::hyp(d)))
                                    .collect();
                                rules.extend(conditions);
                                return Route::Built(Proof::By(simp_unfolded(
                                    rules,
                                    alone,
                                    node.notation() == crate::notations::FOR_ALL,
                                )));
                            }
                        }
                        let mut ways = match unfold.is_empty() {
                            true => Vec::new(),
                            false => unfolded(&unfold),
                        };
                        ways.push(t::bridge(BridgeTactic::Side, vec![]));
                        let why = match by_cases {
                            true => ListReason::DefineByCases,
                            false => ListReason::DefineSides,
                        };
                        Route::Built(ways_proof(why, ways))
                    }
                },
            },
            // One manipulation of a line: linear arithmetic on the line the
            // checker found it made from (`orders`).
            Head::Manipulation(_) => {
                self.order_proof(reason.just.line, k, node).or_try(|| {
                    Route::Built(Proof::By(t::bridge(BridgeTactic::Side, vec![])))
                })
            }
            // A requires line's lines: the fact is what they say, or
            // follows from it by arithmetic.
            Head::Lines => {
                Route::Built(Proof::By(t::bridge(BridgeTactic::Side, vec![])))
            }
        }
    }

    /// Where a step takes the counts its claim or the lines it cites say
    /// in ℕ∞, |X| = |Y| + 1 (`Writer::said_in_extended`), to the integers
    /// they are, `parley_count_int`. A step that computes by a ring or an
    /// order does so first, wherever a count is in ℕ∞, which is neither.
    /// One that rewrites or reasons does so first only where its lines say
    /// counts both ways, as a rewrite in ℕ∞ meets ℕ∞ lines as they are. A
    /// calculation, and substitute rows, build their lines inside the step
    /// as they are written, so the step takes what they build and the goal
    /// to integers together, after; each row is taken as a step of its own
    /// (`substitute_rows`).
    fn count_conversion(
        &self,
        m: Method,
        claim: &Node,
        just: &Justification,
    ) -> CountConversion {
        let cited = self.cited_parts(&just.refs);
        let lines: Vec<&Node> = std::iter::once(claim)
            .chain(cited.iter().map(|c| &c.node))
            .collect();
        let forms = self.count_forms(&lines);
        match m {
            Method::Calculation if forms.extended => CountConversion::After,
            Method::Substitute if !just.rows.is_empty() && forms.extended => {
                CountConversion::After
            }
            Method::Algebra | Method::Arithmetic | Method::Inequalities
                if forms.extended =>
            {
                CountConversion::Before
            }
            Method::Substitute
            | Method::Transitivity
            | Method::Antisymmetry
            | Method::Restate
                if forms.mixed =>
            {
                CountConversion::Before
            }
            _ => CountConversion::None,
        }
    }

    /// How these lines say their counts: whether one says a count in ℕ∞,
    /// and whether one set's count is said both in ℕ∞ and as an integer,
    /// |A| = 0 beside |A| ∈ ℕ of a finite A.
    fn count_forms(&self, lines: &[&Node]) -> CountForms {
        let mut forms: std::collections::BTreeMap<String, CountSaid> =
            std::collections::BTreeMap::new();
        for line in lines {
            self.note_counts(line, None, &mut forms);
        }
        CountForms {
            extended: forms.values().any(|f| f.extended),
            mixed: forms.values().any(|f| f.extended && f.integer),
        }
    }

    /// Each set this node counts, with how the relation the count stands in
    /// says it: in ℕ∞ (`Writer::said_in_extended`) or as an integer.
    /// `extended` is that of the relation nearest above, if any.
    fn note_counts(
        &self,
        node: &Node,
        extended: Option<bool>,
        forms: &mut std::collections::BTreeMap<String, CountSaid>,
    ) {
        let counting = |n: &Node| {
            n.walk()
                .iter()
                .any(|c| &*c.notation_name() == "cardinality")
        };
        let relation = matches!(
            node.notation(),
            crate::notations::EQUALITY
                | crate::notations::ORDER
                | crate::notations::MEMBERSHIP
        );
        let extended = match relation && counting(node) {
            true => {
                Some(self.writer.said_in_extended(node) || self.writer.counts(node))
            }
            false => extended,
        };
        if let (Some(e), "cardinality", [set]) =
            (extended, &*node.notation_name(), node.children.as_slice())
        {
            let said = forms
                .entry(self.sources.checked.grammar.print(set))
                .or_default();
            match e {
                true => said.extended = true,
                false => said.integer = true,
            }
        }
        for c in &node.children {
            self.note_counts(c, extended, forms);
        }
    }

    /// A claim's leading "for all" taken off: the names its letters and
    /// their guards are introduced by, the body, and the letters in scope
    /// with the claim's own added.
    fn peel<'n>(&self, node: &'n Node) -> (Vec<String>, &'n Node, Writer<'a>) {
        let mut writer = self.writer.with_letters(self.writer.letters.clone());
        let mut intros = Vec::new();
        let mut body = node;
        while body.notation() == crate::notations::FOR_ALL {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let name = super::names::letter(&letter.text);
            // Over a range, a number system or another set of numbers, [0,
            // 1]: the letter of the numbers' type, and where the type does
            // not say it, the fact that it is in the set. Over a set of
            // things, sets or a group's elements, a member of their type,
            // and the fact.
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
                writer.introduce(&letter.text, super::expr::range_letter_system(set));
                (None, true)
            } else {
                match (super::expr::system_of(set), self.writer.set_members(set)) {
                    (Some(s), _) => {
                        writer.introduce(&letter.text, s);
                        (None, !matches!(s, super::expr::System::Type(_)))
                    }
                    (None, Some(super::expr::Members::Numbers(n))) => {
                        (Some(LetterType::Number(n)), true)
                    }
                    (None, Some(m)) => (Some(LetterType::Member(m)), true),
                    (None, None) => break,
                }
            };
            if let Some(ty) = ty {
                writer.letters.insert(letter.text.to_string(), ty);
                writer.wholes.shift_remove(&*letter.text);
            }
            intros.push(name.clone());
            if guarded {
                intros.push(format!("h_{name}"));
            }
            body = inner;
        }
        (intros, body, writer)
    }

    /// The proof of a claim by a method that closes it, with the letters
    /// `writer` holds.
    fn method_proof(
        &self,
        reason: Reason,
        m: Method,
        k: usize,
        node: &Node,
        writer: &Writer,
    ) -> Route<super::doc::Proof> {
        use super::doc::Proof;
        let just = reason.just;
        Route::Built(match m {
            Method::Algebra => {
                // A cited equation of a narrower type is combined as the
                // claim's type has it.
                let mut cited = self.cited_parts(&just.refs);
                for c in &mut cited {
                    if let Some(read) = self.at_recorded_letter(c, &node.names()) {
                        *c = read;
                    }
                }
                // A define the step cites is written out, in the claim and
                // in each line it cites, as the checker reads the step: in
                // Lean, its equation rewrites them all, and the casts it
                // leaves are pushed in. Lines are widened after, as they
                // then read.
                // A define's value may name another the step cites, v's of
                // ω₁, so they are written out until none is left.
                let defines = self.cited_defines(&just.refs);
                let mut claim = node.clone();
                for d in &defines {
                    cited.retain(|c| c.proof != super::tactics::hyp(&d.proof));
                }
                let grammar = &self.sources.checked.grammar;
                let printed =
                    |claim: &Node, cited: &[super::algebra::Cited]| -> Vec<String> {
                        std::iter::once(claim)
                            .chain(cited.iter().map(|c| &c.node))
                            .map(|n| grammar.print(n))
                            .collect()
                    };
                for _ in 0..=defines.len() {
                    let before = printed(&claim, &cited);
                    for d in &defines {
                        claim = self.put_define(&claim, d);
                        for c in &mut cited {
                            c.node = self.put_define(&c.node, d);
                        }
                    }
                    if printed(&claim, &cited) == before {
                        break;
                    }
                }
                let mut haves = Vec::new();
                for c in &mut cited {
                    match self.widened(&c.node, &c.proof, &claim, writer) {
                        Route::Built(w) => {
                            haves.extend(w.have);
                            c.proof = w.name;
                        }
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // Each read with its identity elements dropped, as the
                // checker decides it: F(0 + 1) and F(1) are one term.
                let ctx = self.sources.ctx;
                let claim = crate::matching::bare(&claim, ctx);
                for c in &mut cited {
                    c.node = crate::matching::bare(&c.node, ctx);
                }
                let proof = match super::algebra::algebra(
                    writer,
                    self.sources.targets,
                    &claim,
                    &cited,
                ) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let mut lines: Vec<Tactic> =
                    written_out(&defines, &self.rewritten_at());
                lines.extend(haves);
                return Route::Built(haves_then(lines, proof));
            }
            Method::Arithmetic => {
                Proof::By(super::tactics::bridge(BridgeTactic::Arith, vec![]))
            }
            // Arithmetic of real numbers, √8 = 2√2 or ln(2) ≠ 0: its own
            // tactic, which tries `parley_arith` first (`RealTactics`).
            Method::RealArithmetic => {
                Proof::By(super::tactics::bridge(BridgeTactic::Real, vec![]))
            }
            // Rows are linear moves on the line the first row cites, so the
            // claim follows from that line by linear arithmetic, as a step
            // with no rows does from the lines it cites.
            // An order is left to the ways of orders alone; a chain of
            // equations, A = B = C, to `parley_side`.
            Method::Inequalities | Method::Transitivity | Method::Antisymmetry => {
                // A chain whose links the checker placed, all in one type:
                // composed link by link (`chain_composed`).
                if just.head.is(Method::Transitivity) {
                    if let Some(composed) = self.chain_composed(just, node) {
                        return Route::Built(composed);
                    }
                }
                // What the checker recorded the step rests on (`orders`,
                // `antisymmetric`).
                let recorded = match m {
                    Method::Inequalities => self.order_proof(just.line, k, node),
                    Method::Antisymmetry => self.antisymmetry_proof(just.line, node),
                    _ => Route::no("a transitivity chain is composed from its links"),
                };
                if let Route::Built(proof) = recorded {
                    return Route::Built(proof);
                }
                // A cited "for all", a(n) = 1 − 1/2ⁿ for every n, is read
                // at the claim's letter, which linear arithmetic can use.
                let mut steps: Vec<Tactic> = self
                    .cited_parts(&just.refs)
                    .iter()
                    .filter_map(|c| self.at_recorded_letter(c, &node.names()))
                    .map(|at| Tactic::Fact(at.proof))
                    .collect();
                let close = match node.notation() == ORDER {
                    true => BridgeTactic::Order,
                    false => BridgeTactic::Side,
                };
                steps.push(super::tactics::bridge(close, vec![]));
                super::doc::Proof::By(Tactic::Seq(steps))
            }
            Method::Substitute => return self.substitute(just, k, node, writer),
            Method::Calculation => return self.calculation(just, writer),
            Method::Exhibit => return self.exhibit(just, node),
            Method::Instantiate => return self.instantiate(just, node, writer),
            Method::Membership => return self.membership(just, node, writer),
            Method::Inspection | Method::Restate | Method::Join => {
                Proof::By(super::tactics::bridge(BridgeTactic::Side, vec![]))
            }
            other => {
                return Route::no(format!(
                    "the method {} is not written in Lean yet",
                    other.as_str()
                ))
            }
        })
    }

    /// A recursion a proof lets, `let N(0) = 0, N(k + 1) = 10·N(k) + d(k +
    /// 1), for k ∈ ℕ₀`: its function, of ℤ into the type its rules compute
    /// in, obtained from `recursion_exists`, and its rules one hypothesis
    /// named by its label, as a recursion the header lets is written
    /// (`header_recursions`), which a step cites alike. A recursion of
    /// several functions, over other than ℕ₀, or whose step applies its
    /// function at other than k, is declined.
    fn define_recursion(
        &mut self,
        d: usize,
        r: &crate::corpus::Recursion,
        depth: usize,
    ) -> Route<()> {
        use super::templates::Num;
        let line = self.thm.defines[d].clone();
        if r.domain.trim() != "ℕ₀" {
            return Route::no("a recursion over other than ℕ₀");
        }
        let rules = match recursion_rules(r, &line, self.rec) {
            Route::Built(rules) => rules,
            Route::Declined(why) => return Route::Declined(why),
        };
        let [rule] = rules.as_slice() else {
            return Route::no("a recursion of several functions a proof lets");
        };
        let saved = self.writer.letters.clone();
        self.writer
            .letters
            .insert(r.index.clone(), LetterType::Number(Num::Int));
        let mut to = Num::Int;
        for n in [&rule.start, &rule.step] {
            self.writer.letters.insert(
                rule.name.clone(),
                LetterType::Function { from: Num::Int, to },
            );
            match self.writer.carrier(n) {
                Route::Built(c) => to = to.max(c),
                Route::Declined(why) => {
                    self.writer.letters = saved;
                    return Route::Declined(why);
                }
            }
        }
        let ty = LetterType::Function { from: Num::Int, to };
        self.writer.letters.insert(rule.name.clone(), ty.clone());
        // The step as `recursion_exists` takes it: of k and the value at k,
        // N(k) in it a letter for that value.
        let previous = fresh_letter(&self.writer, &r.index);
        let at_index = rule
            .step
            .walk()
            .into_iter()
            .find(|n| applied_at(n, rule.name, &r.index));
        let stepped = match &at_index {
            Some(at) => super::expr::put_for(
                &rule.step,
                at,
                &Node::name(crate::formula::Sort::none(), &previous),
            ),
            None => rule.step.clone(),
        };
        let still_applied = stepped
            .walk()
            .iter()
            .any(|n| n.is_name() && &*n.text == rule.name.as_str());
        self.writer
            .letters
            .insert(previous.clone(), LetterType::Number(to));
        let written = (
            self.writer.number_fixed(&rule.start, to),
            self.writer.number_fixed(&rule.step, to),
            self.writer.number_fixed(&stepped, to),
        );
        self.writer.letters = saved;
        self.writer.letters.insert(rule.name.clone(), ty);
        if still_applied {
            return Route::no(
                "a recursion whose step applies its function at other than k",
            );
        }
        let (start, step, by_previous) = match written {
            (Route::Built(s), Route::Built(t), Route::Built(g)) => (s, t, g),
            (Route::Declined(why), _, _)
            | (_, Route::Declined(why), _)
            | (_, _, Route::Declined(why)) => return Route::Declined(why),
        };
        let f = super::names::letter(rule.name);
        let k = super::names::letter(&r.index);
        let v = super::names::letter(&previous);
        let label = line_name(&line.label);
        // ∃ f : ℤ → T, f 0 = start ∧ ∀ k : ℤ, 0 ≤ k → f (k + 1) = step.
        use super::doc::{LeanType, Op, Quant, TermKind};
        let int = LeanType::Num(super::templates::Num::Int);
        let value = LeanType::Num(to);
        let function = LeanType::Fun {
            from: Box::new(int.clone()),
            to: Box::new(value.clone()),
        };
        let k_letter = || Printed::letter(k.clone(), int.clone());
        let f_at = |at: Printed| {
            Printed::of(
                TermKind::App {
                    head: Box::new(Printed::letter(f.clone(), function.clone())),
                    args: vec![super::doc::Arg::Explicit(at)],
                    explicit: false,
                },
                value.clone(),
            )
        };
        let equal =
            |a: Printed, b: Printed| Printed::infix(Op::EQUALS, a, b, LeanType::Prop);
        let Some(and) = Op::of("∧") else {
            return Route::no("no ∧ among the writer's operators");
        };
        let Some(le) = Op::of("≤") else {
            return Route::no("no ≤ among the writer's operators");
        };
        let Some(plus) = Op::of("+") else {
            return Route::no("no + among the writer's operators");
        };
        let next = Printed::infix(
            plus,
            k_letter(),
            Printed::numeral("1", int.clone()),
            int.clone(),
        );
        let every = Printed::of(
            TermKind::Quantified {
                quant: Quant::ForAll,
                letter: k.clone(),
                letter_ty: int.clone(),
                guard: Some(Box::new(Printed::infix(
                    le,
                    Printed::numeral("0", int.clone()),
                    k_letter(),
                    LeanType::Prop,
                ))),
                body: Box::new(equal(f_at(next), step)),
                bounded: false,
            },
            LeanType::Prop,
        );
        let both = Printed::infix(
            and,
            equal(f_at(Printed::numeral("0", int.clone())), start),
            every,
            LeanType::Prop,
        );
        let rules = Printed::of(
            TermKind::Quantified {
                quant: Quant::Exists,
                letter: f.clone(),
                letter_ty: function,
                guard: None,
                body: Box::new(both),
                bounded: false,
            },
            LeanType::Prop,
        );
        let exists = Printed::of(
            TermKind::App {
                head: Box::new(super::tactics::bridge_lemma(
                    "LeanBridges.Functions.recursion_exists",
                    BridgeModule::Functions,
                )),
                args: vec![
                    super::doc::Arg::Explicit(Printed::of(
                        TermKind::Elided,
                        LeanType::Prop,
                    )),
                    super::doc::Arg::Explicit(untyped_lambda(
                        &[k.as_str(), v.as_str()],
                        by_previous,
                    )),
                ],
                explicit: false,
            },
            LeanType::Prop,
        );
        self.push_at(
            depth,
            Tactic::Obtain {
                names: vec![f, label.clone()],
                says: Some(rules),
                from: exists,
            },
            line.line,
            Spot::Statement,
        );
        self.named.insert(line.label.clone(), vec![label]);
        Route::Built(())
    }

    /// A define in a proof, `let t = 1/j, a real number`: Lean's `set`, of
    /// the type the line names, or else of the least that holds its value,
    /// whose hypothesis is the define's equation, named by its label.
    fn define(&mut self, d: usize, depth: usize) -> Route<()> {
        self.defined.insert(d);
        let line = &self.thm.defines[d];
        let def = match crate::corpus::define_parts(&line.text) {
            Route::Built(crate::corpus::DefineParts::One(def)) => def,
            Route::Built(crate::corpus::DefineParts::Recursion(r)) => {
                return self.define_recursion(d, &r, depth)
            }
            _ => return Route::no("a define of a phrase"),
        };
        if !def.params.is_empty() {
            return self.define_function(d, &def, depth);
        }
        let bodies: Vec<&Node> = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == line.line)
            .map(|(_, node)| node)
            .collect();
        let [body] = bodies.as_slice() else {
            return Route::no(
                "a define whose value the checker did not read as one term",
            );
        };
        let body = (*body).clone();
        // A name for an element or a set, `let b = a⁻¹`: of the type its
        // value has, written as the writer writes such terms.
        let set_like = self
            .writer
            .member_kind(&body)
            .map(|m| m.letter())
            .or_else(|| self.writer.members_of(&body).map(LetterType::Set));
        if let Some(ty) = set_like.filter(|_| def.kind.is_none()) {
            let value = match self.writer.set_term(&body) {
                Route::Built(v) => v,
                Route::Declined(why) => return Route::Declined(why),
            };
            self.name_value(d, &def.name, ty, value, body, depth);
            return Route::Built(());
        }
        use super::templates::Num;
        // A positive or nonnegative whole number is a natural number named
        // from its kind's fact, whatever its value's type, as `let m ∈ ℕ`
        // names one and as the elaborator puts the name among ℕ's members
        // once the kind is shown (`GOALS.md` decision 20).
        if matches!(
            def.kind.as_deref(),
            Some("a positive integer" | "a natural number" | "a nonnegative integer")
        ) {
            return self.kinded_witness(d, &def.name, body, depth);
        }
        let ty = match def.kind.as_deref() {
            Some("a real number") => Num::Real,
            Some("a rational number") => Num::Rat,
            Some("an integer") => Num::Int,
            Some("a complex number") => Num::Complex,
            Some(other) => return Route::no(format!("a define of {other}")),
            None => match self.writer.carrier(&body) {
                Route::Built(n) => n,
                Route::Declined(why) => return Route::Declined(why),
            },
        };
        // An integer whose value is wider, `let e = p/d, an integer`: Lean's
        // ℤ division would round, so the name is the number its reason
        // shows the value to be.
        let wider = match self.writer.carrier(&body) {
            Route::Built(n) => n > ty,
            Route::Declined(why) => return Route::Declined(why),
        };
        if def.kind.is_some() && wider {
            return self.kinded_witness(d, &def.name, body, depth);
        }
        let value = match self.writer.number_fixed(&body, ty) {
            Route::Built(v) => v,
            Route::Declined(why) => return Route::Declined(why),
        };
        self.name_value(d, &def.name, LetterType::Number(ty), value, body, depth);
        // A define of a kind whose value is already of the type, `let n =
        // a·b, an integer`: the kind's fact is still a line, proved by the
        // define's reason.
        if def.kind.is_some() {
            let KindShown { says, proof, .. } = match self.kind_shown(d) {
                Route::Built(s) => s,
                Route::Declined(why) => return Route::Declined(why),
            };
            let line = &self.thm.defines[d];
            let label = line_name(&line.label);
            self.push_at(
                depth,
                Tactic::Have {
                    name: format!("{label}_kind"),
                    says,
                    proof: Box::new(proof),
                },
                line.line,
                Spot::Statement,
            );
        }
        Route::Built(())
    }

    /// What closes a block, a part of one or a theorem once its steps are
    /// written, its last step being `last` and what it owes `owed`, the
    /// goal with the block's lines taken off (`Owed::written`): nothing
    /// after a step shown impossible, which closed it; the two lines a step
    /// written `contradicting N` opposes; and otherwise each part of the
    /// last step's "and" proving the part it owes, as the checker met them
    /// (`CheckedTheorem::ends_met`).
    fn closing(&self, last: Option<usize>, owed: Owing) -> Route<Closing> {
        let Some(at) = last else {
            return Route::no("a block with no steps");
        };
        let step = &self.thm.steps[at];
        if step.impossible {
            return Route::Built(Closing::Closed);
        }
        let (owes, owed_nodes) = match owed {
            Owing::Written(Some(owed)) => {
                let mut owes = Vec::new();
                for o in owed {
                    match self.writer.formula(o) {
                        Route::Built(p) => owes.push(p),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                (owes, owed.to_vec())
            }
            Owing::Written(None) => (Vec::new(), Vec::new()),
            Owing::Lean { nodes, goal } => (goal, nodes.unwrap_or_default().to_vec()),
        };
        // Two lines that oppose close a contradiction, whose goal is False;
        // a case or a proof block whose assumption cannot hold they close by
        // `absurd`, whatever it owes.
        if let Some(c) = self.rec.contradicted.get(&step.just.line) {
            return self
                .contradiction_closed(step, c, owes.is_empty())
                .map(|t| Closing::Tactic(Box::new(Tactic::Exact(t))));
        }
        if owes.is_empty() {
            return Route::no(format!(
                "step {} ends a block that owes nothing it says, and contradicts no line",
                step.number
            ));
        }
        // How the step meets what it owes, one meeting to each part of its
        // "and", as the checker paired them.
        let Some(meetings) = self.rec.ends_met.get(&step.just.line) else {
            return Route::no(format!(
                "step {} ends its block, and the checker recorded no meeting of it with what it owes",
                step.number
            ));
        };
        let all = match self.claimed_all(step) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let named = all.iter().filter(|(_, _, says)| !says.is_truth()).count();
        let names = Self::names_of(step, named);
        let mut name_of = names.iter();
        // Each side taken apart at the page's "and", as the checker paired
        // them, not at an "and" Lean's statement alone writes.
        let mut parts = Vec::new();
        for (_, node, says) in &all {
            let proof = match says.is_truth() {
                true => None,
                false => name_of.next().map(|n| super::tactics::hyp(n)),
            };
            and_leaves(node, says, proof, &mut parts);
        }
        if owed_nodes.len() != owes.len() {
            return Route::no(format!(
                "step {} ends a block whose goal the record says in {} sentences and Lean in {}",
                step.number,
                owed_nodes.len(),
                owes.len()
            ));
        }
        let mut owed_parts = Vec::new();
        for (node, owe) in owed_nodes.iter().zip(&owes) {
            and_leaves(node, owe, None, &mut owed_parts);
        }
        // A sentence the checker met whole that the record writes out as an
        // "and", a phrase as its meaning, is met whole here too.
        let mut whole = false;
        if let ([(_, _, says)], [owe], [_]) =
            (all.as_slice(), owes.as_slice(), meetings.as_slice())
        {
            if parts.len() != 1 {
                parts =
                    vec![(says.clone(), names.first().map(|n| super::tactics::hyp(n)))];
                owed_parts = vec![(owe.clone(), None)];
                whole = true;
            }
        }
        if parts.len() != owed_parts.len() || parts.len() != meetings.len() {
            return Route::no(format!(
                "step {} ends its block in {} parts, and it owes {}, of which the checker met {}",
                step.number,
                parts.len(),
                owed_parts.len(),
                meetings.len()
            ));
        }
        let values = self.set_values();
        // The last step that says what is owed as written proves it by its
        // `have`, the goal's own proof.
        if let ([(_, _, says)], [owe], [met], [name]) = (
            all.as_slice(),
            owes.as_slice(),
            meetings.as_slice(),
            names.as_slice(),
        ) {
            if met.as_written()
                && super::doc::forms::casts_differ(says, owe, &values).is_none()
            {
                return Route::Built(Closing::Last(name.clone()));
            }
        }
        let mut proofs = Vec::new();
        for (((says, proof), (owe, _)), met) in
            parts.iter().zip(&owed_parts).zip(meetings)
        {
            let proved = match (owe.is_truth(), proof) {
                (true, _) => Some(Proved::Term(trivial())),
                (false, Some(proof)) => self.met_proof(proof.clone(), says, owe, met),
                (false, None) => None,
            };
            match proved {
                Some(p) => proofs.push(p),
                None => {
                    return Route::no(format!(
                        "step {} ends its block on {}, met with {} as {met:?}, which no one tactic takes to the other",
                        step.number,
                        says.text(),
                        owe.text()
                    ))
                }
            }
        }
        let mut assembled = Vec::new();
        match whole {
            true => assembled = proofs,
            false => {
                let mut proofs = proofs.into_iter();
                for (node, owe) in owed_nodes.iter().zip(&owes) {
                    match assembled_as(node, owe, &mut proofs) {
                        Some(p) => assembled.push(p),
                        None => {
                            return Route::no(
                                "an ending whose parts do not make what it owes",
                            )
                        }
                    }
                }
            }
        }
        Route::Built(Closing::Tactic(Box::new(match assembled.len() {
            1 => assembled.remove(0).closer(),
            _ => Tactic::Exact(super::expr::anonymous(
                assembled.into_iter().map(Proved::term).collect(),
            )),
        })))
    }

    /// How `proof`, a line that says `says`, proves `wanted`, the two met as
    /// the checker recorded (`Meeting`): turned round by `.symm`, its
    /// identity elements dropped by `simpa only`, and otherwise as it is,
    /// its casts moved where the writer placed them otherwise on the two.
    /// None for parts paired out of order, which no one tactic takes.
    fn met_proof(
        &self,
        proof: Printed,
        says: &Printed,
        wanted: &Printed,
        met: &crate::matching::Meeting,
    ) -> Option<Proved> {
        use super::doc::forms;
        if met.permuted {
            return None;
        }
        let (proof, says) = match met.turned {
            true => (turned_proof(proof, says), forms::turned_statement(says)),
            false => (proof, says.clone()),
        };
        // A numeral the writer takes to ℕ on one side, `2 ^ (1 : ℤ).toNat`
        // beside 2 ^ 1, is worked out as identity elements are dropped.
        let to_nat: Vec<&'static str> = match forms::written_alike(&says, wanted) {
            true => Vec::new(),
            false => forms::to_nat_rules(&says)
                .into_iter()
                .chain(forms::to_nat_rules(wanted))
                .collect(),
        };
        // A numeral's `toNat` is worked out by its simprocs (`to_nat_rules`),
        // and the cast of a numeral it leaves, ↑0 beside 0, from ℕ or from
        // ℤ, is that numeral (`casts::NUMERAL_CASTS`).
        if met.identities.is_empty() && !to_nat.is_empty() {
            use super::templates::Num;
            let mut rules = to_nat;
            rules.extend(
                super::casts::NUMERAL_CASTS
                    .iter()
                    .filter(|(from, _, _)| matches!(from, Num::Nat | Num::Int))
                    .map(|(_, _, lemma)| *lemma),
            );
            return Some(Proved::Simplified { rules, line: proof });
        }
        if !met.identities.is_empty() {
            let mut rules: Vec<&'static str> = Vec::new();
            for d in &met.identities {
                let rule = identity_lemma(d)?;
                if !rules.contains(&rule) {
                    rules.push(rule);
                }
            }
            for rule in to_nat {
                if !rules.contains(&rule) {
                    rules.push(rule);
                }
            }
            return Some(Proved::Simplified { rules, line: proof });
        }
        match forms::casts_differ(&says, wanted, &self.set_values()) {
            Some(apart) => cast_proved(apart, proof, &says, wanted),
            None => Some(Proved::Term(proof)),
        }
    }

    /// Keeps a line's sentences under its label. A sentence the writer
    /// states, a step's `have`, keeps what that states (`LineSentence::says`),
    /// which every later reading reads; one Lean states for it, a part an
    /// `obtain` takes from an item, is read as the writer writes its tree.
    fn store(&mut self, label: String, said: Vec<LineSentence>) {
        self.trees.insert(label, said);
    }

    /// What a line says in Lean: as it was stated (`store`), or, of a line
    /// not stated so, as the writer writes its tree now.
    fn line_statement(&self, line: &super::algebra::Cited) -> Route<Printed> {
        match &line.says {
            Some(says) => Route::Built(says.clone()),
            None => self.writer.formula(&line.node),
        }
    }

    /// The letters the proof so far names by `set`, with their values.
    fn set_values(&self) -> super::doc::forms::Values {
        self.lines
            .iter()
            .filter_map(|l| match &l.tactic {
                Tactic::Set {
                    name, value, with, ..
                } => Some((
                    name.clone(),
                    super::doc::forms::Value {
                        value: value.clone(),
                        equation: with.clone(),
                    },
                )),
                _ => None,
            })
            .collect()
    }

    /// What closes a block on a step written `contradicting N`: the line that
    /// says the other negated, applied to the other, `h₁ h₂`, where the goal
    /// is False, and otherwise `absurd h₂ h₁`; the other turned round where
    /// Lean writes its equation the other way.
    fn contradiction_closed(
        &self,
        step: &Step,
        c: &Contradicted,
        to_false: bool,
    ) -> Route<Printed> {
        use super::doc::forms;
        let own = match self.claim(step) {
            Route::Built(said) => match said.as_slice() {
                [(_, says)] => (
                    super::tactics::hyp(&Self::names_of(step, 1)[0]),
                    says.clone(),
                ),
                _ => {
                    return Route::no(format!(
                        "step {} contradicts a line and claims several sentences",
                        step.number
                    ))
                }
            },
            Route::Declined(d) => return Route::Declined(d),
        };
        let other = match self.line_says(&c.at) {
            Route::Built(o) => o,
            Route::Declined(d) => return Route::Declined(d),
        };
        let ((negation, says_not), (positive, says)) = match c.negated {
            Negating::Step => (own, other),
            Negating::Line => (other, own),
        };
        let Some(denied) = forms::denied(&says_not) else {
            return Route::no(format!(
                "step {} contradicts {}, and Lean writes neither as a negation",
                step.number, c.at.line
            ));
        };
        // The one met with what the other denies as the checker met them
        // (`Contradicted::meeting`).
        let positive = match self.met_proof(positive, &says, &denied, &c.meeting) {
            Some(Proved::Term(t)) => t,
            Some(other) => other.term(),
            None => {
                return Route::no(format!(
                    "step {} contradicts {}: Lean writes the one as {} and the other denies {}, met as {:?}",
                    step.number,
                    c.at.line,
                    says.text(),
                    denied.text(),
                    c.meeting
                ))
            }
        };
        Route::Built(match to_false {
            true => applied_to(negation, positive),
            false => Printed::applied(
                "absurd",
                super::doc::Source::Core,
                vec![positive, negation],
                super::doc::LeanType::Prop,
            ),
        })
    }

    /// What stands where the checker found a fact in a line (`FirstAt`), as
    /// a term that proves it and the statement Lean writes for it: the
    /// sentence at that place, a "for all" of the line read at the block's
    /// letter the step names, `hH1 y`, or one part of either joined by
    /// "and", `hH1.2`.
    fn line_says(&self, at: &FirstAt) -> Route<(Printed, Printed)> {
        let found = match self.line_part(at) {
            Route::Built(f) => f,
            Route::Declined(d) => return Route::Declined(d),
        };
        let Some(rule) = at.implied else {
            return self.line_statement(&found).map(|says| (found.proof, says));
        };
        let says = match self.writer.formula(&at.written) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        self.implied_proof(&found, rule, &says)
            .map(|proof| (proof, says))
    }

    /// The proof of a substitution's own equation where no line says it
    /// (`Substituted::from` None), by the source the step names: worked out
    /// by arithmetic, a `have` proved by `parley_arith`; or a define of a
    /// name, its hypothesis, turned where the step writes the name on the
    /// right. None of any other source.
    fn equation_given(
        &self,
        just: &Justification,
    ) -> Option<(Option<Tactic>, GivenEquation)> {
        use super::tactics as t;
        use crate::corpus::skeleton::Source;
        let rec = self.rec.substituted.get(&just.line)?;
        if rec.from.is_some() {
            return None;
        }
        match just.source.as_ref()? {
            Source::Arithmetic => {
                let says = self.writer.formula(&rec.equation).built()?;
                let have = Tactic::Have {
                    name: "e_arith".to_string(),
                    says: says.clone(),
                    proof: Box::new(super::doc::Proof::By(t::bridge(
                        BridgeTactic::Arith,
                        vec![],
                    ))),
                };
                Some((
                    Some(have),
                    GivenEquation {
                        change: super::algebra::Cited {
                            node: rec.equation.clone(),
                            proof: t::hyp("e_arith"),
                            says: Some(says),
                        },
                        above: None,
                    },
                ))
            }
            Source::At(place) => {
                let label = place.named();
                let d = self.thm.defines.iter().find(|d| d.label == label)?;
                let Route::Built(crate::corpus::DefineParts::One(one)) =
                    crate::corpus::define_parts(&d.text)
                else {
                    return None;
                };
                // A define of a name, its equation under the define's label;
                // a function the header lets, of one argument, its equation at
                // the argument the record puts in its domain
                // (`define_domains`), `hD1 _ h`.
                let equation = match one.params.len() {
                    0 => t::hyp(self.named.get(label)?.first()?),
                    1 => {
                        let hyp = self.header_function_named(label)?;
                        let domain = self
                            .domain_proof(
                                self.rec.define_domains.get(&just.line)?,
                                None,
                            )
                            .built()?;
                        hyp_applied(&hyp, vec![elided_term(), domain])
                    }
                    _ => return None,
                };
                // Turned where the step writes it the other way round from
                // the define, as the checker found (`define_facing`).
                let proof = faced(equation, rec.define_facing?);
                Some((
                    None,
                    GivenEquation {
                        change: super::algebra::Cited {
                            node: rec.equation.clone(),
                            proof,
                            says: None,
                        },
                        above: None,
                    },
                ))
            }
            Source::RealArithmetic => None,
        }
    }

    /// The rewrites that take a define by cases to the case the checker
    /// took (`define_cases`): `if_pos h` of each condition passed that
    /// holds and `if_neg h` of each that fails, h the line that says so.
    fn conditions_put(
        &self,
        taken: &crate::checker::record::TakenCase,
        claim: &Node,
    ) -> Route<Vec<super::doc::Rule>> {
        use super::doc::forms::relation_type;
        let claim_type = match self.writer.formula(claim) {
            Route::Built(c) => relation_type(&c),
            Route::Declined(d) => return Route::Declined(d),
        };
        let mut out = Vec::new();
        for condition in &taken.passed {
            let Some(at) = &condition.said_by else {
                return Route::no("a case's condition said by no line the step cites");
            };
            let found = match self.line_part(at) {
                Route::Built(f) => f,
                Route::Declined(d) => return Route::Declined(d),
            };
            if at.implied.is_some() {
                return Route::no(
                    "a case's condition a line implies without saying it",
                );
            }
            // A line Lean states in a narrower type than the claim's is the
            // condition stated in the claim's type: cast up, `(by
            // exact_mod_cast h : …)`, or, a fact of numerals alone, `¬ (1/2 :
            // ℚ) < 1/2` beside a define over ℝ, which holds no cast to move,
            // worked out there, `(by norm_num : ¬ (1/2 : ℝ) < 1/2)`.
            let says = match self.line_statement(&found) {
                Route::Built(s) => s,
                Route::Declined(d) => return Route::Declined(d),
            };
            let proof = match (relation_type(&says), &claim_type) {
                (Some(line), Some(claim)) if line != *claim => {
                    let (super::doc::LeanType::Num(l), super::doc::LeanType::Num(c)) =
                        (&line, claim)
                    else {
                        return Route::no(
                            "a case's condition said by a line in another type than the claim's",
                        );
                    };
                    if l > c {
                        return Route::no(
                            "a case's condition said by a line in a wider type than the claim's",
                        );
                    }
                    let restated = match self.writer.closed_formula(&at.written, *c) {
                        Route::Built(r) => r,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    let up = match restated.lettered() {
                        false => norm_num_term(),
                        true => super::tactics::by_term(super::doc::Proof::By(
                            super::tactics::exact_mod_cast(found.proof),
                        )),
                    };
                    ascribed(up, restated)
                }
                _ => found.proof,
            };
            let lemma = match condition.holds {
                true => "if_pos",
                false => "if_neg",
            };
            out.push(super::tactics::forwards(Printed::applied(
                lemma,
                super::doc::Source::Core,
                vec![proof],
                super::doc::LeanType::Prop,
            )));
        }
        Route::Built(out)
    }

    /// A claim "for all j ∈ S" proved by a header function's equation at
    /// the member, `intro j h_j; simp only [hD1 j h]`, worked out after as
    /// the checker met the sides (`define_links`). `h` puts the member in
    /// the function's domain as the record says (`define_domains`): a line,
    /// or the member's own fact, which is the domain's fact itself where S
    /// is the domain, and the range's lower bound where S is a range inside
    /// it, `1 ≤ j` being `0 < j` in ℤ.
    fn for_all_by_header(
        &self,
        hyp: &str,
        node: &Node,
        line: usize,
    ) -> Route<super::doc::Proof> {
        use super::tactics as t;
        let (Some(said), Some(met)) = (
            self.rec.define_domains.get(&line),
            self.rec.define_links.get(&line),
        ) else {
            return Route::no("a claim \"for all\" with no domain or meeting recorded");
        };
        let Some((member, _)) =
            crate::citing::claimed_member(node, self.writer.grammar)
        else {
            return Route::no("a claim \"for all\" over no set");
        };
        let (intros, body, writer) = self.peel(node);
        let ([letter, h], false) = (
            intros.as_slice(),
            body.notation() == crate::notations::FOR_ALL,
        ) else {
            return Route::no("a claim \"for all\" of more than one letter");
        };
        // The member's own fact as the domain's: the domain's fact itself
        // where the set is the domain, the range's lower bound where it is a
        // range inside it.
        let member_fact = match member.children[1].notation() {
            crate::notations::INTEGER_RANGE => {
                let says = match writer.formula(&member) {
                    Route::Built(s) => s,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match range_bounds(&says, &t::hyp(h)).into_iter().next() {
                    Some((proof, _)) => proof,
                    None => return Route::no("a range member Lean writes otherwise"),
                }
            }
            _ => t::hyp(h),
        };
        let domain = match self.domain_proof(said, Some(member_fact)) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let equation = hyp_applied(hyp, vec![t::hyp(letter), domain]);
        let alone = met.as_ref().is_some_and(unfolds_alone);
        Route::Built(super::doc::Proof::By(Tactic::Seq(vec![
            Tactic::Intro(intros.clone()),
            simp_unfolded(vec![t::forwards(equation)], alone, false),
        ])))
    }

    /// The proof of a claim the checker found a line states
    /// (`CheckedTheorem::restated`): the line, its sentence or part, read at
    /// a block's letter where the line says it for all, or what it implies
    /// (`line_says`), met with the claim as Lean states it (`proof_meeting`).
    /// None where the record has no place, or Lean states the two apart.
    fn restated_proof(&self, line: usize, node: &Node) -> Option<super::doc::Proof> {
        let at = self.rec.restated.get(&line)?;
        let (proof, says) = self.line_says(at).built()?;
        let claim = self.claim_as_stated(line, node)?;
        if !super::doc::forms::relation_types_agree(&says, &claim) {
            return None;
        }
        self.proof_meeting(proof, &says, &claim)
            .map(|p| super::doc::Proof::By(p.closer()))
    }

    /// The proof that a define's argument is in its domain, as the record
    /// says (`define_domains`): the line's sentence or part that says it, or,
    /// of a claim said of every member, the member's own fact, `member`,
    /// where the claim's step has one. Declined of a fact a line implies
    /// without writing it.
    fn domain_proof(
        &self,
        said: &crate::checker::record::DomainSaid,
        member: Option<Printed>,
    ) -> Route<Printed> {
        use crate::checker::record::DomainSaid;
        match (said, member) {
            (DomainSaid::Line(at), _) if at.implied.is_none() => {
                self.line_part(at).map(|found| found.proof)
            }
            (DomainSaid::Line(_), _) => Route::no("a domain a line implies"),
            (DomainSaid::Member, Some(fact)) => Route::Built(fact),
            (DomainSaid::Member, None) => {
                Route::no("a domain the claim's member says, of a claim not peeled")
            }
        }
    }

    /// The sentence or part of a line `at` names, as the page writes it, with
    /// the term that proves it; of an implied fact, what implies it.
    fn line_part(&self, at: &FirstAt) -> Route<super::algebra::Cited> {
        let line = &at.line;
        let Some(sentences) = self.trees.get(line) else {
            return Route::no(format!("line {line}, which no name in Lean holds"));
        };
        let own = self.written_sentences(line);
        let found = match (at.sentence, sentences.as_slice()) {
            (None, [one]) => Some(one.cited()),
            (None, _) => {
                return Route::no(format!(
                    "the sentences of line {line} together, which Lean names apart"
                ))
            }
            (Some(k), _) if k < own => sentences
                .iter()
                .find(|s| s.at == k)
                .map(LineSentence::cited),
            (Some(k), _) => {
                let letters: std::collections::BTreeSet<String> =
                    at.written.names().into_iter().collect();
                sentences
                    .iter()
                    .filter_map(|s| self.at_recorded_letter(&s.cited(), &letters))
                    .nth(k - own)
            }
        };
        let Some(found) = found else {
            return Route::no(format!(
                "sentence {:?} of line {line}, which Lean has no line for",
                at.sentence
            ));
        };
        match at.part {
            None => Route::Built(found),
            Some(j) => {
                let mut parts = Vec::new();
                conjuncts(&found.node, found.proof, found.says, &mut parts);
                match parts.into_iter().nth(j) {
                    Some(part) => Route::Built(part),
                    None => Route::no(format!(
                        "part {j} of what line {line} says, which Lean does not join by \"and\""
                    )),
                }
            }
        }
    }

    /// Whether Lean writes the membership `node` as a bound, `0 < x` or
    /// `0 ≤ x`.
    fn written_as_bound(&self, node: &Node) -> bool {
        match self.writer.formula(node) {
            Route::Built(says) => matches!(
                &says.kind,
                super::doc::TermKind::Infix { op, .. } if op.symbol == "<" || op.symbol == "≤"
            ),
            Route::Declined(_) => false,
        }
    }

    /// The proof of what `found`, a sentence or part of a line, implies by
    /// `rule` (`FirstAt::implied`), from how Lean writes `found`: a range
    /// membership is `x ∈ Finset.Icc a b`, whose bounds `Finset.mem_Icc`
    /// gives; a membership of ℕ or ℕ₀ is the bound `0 < x` or `0 ≤ x`
    /// itself, which is also `x ≥ 1` in ℤ. `target` is what it implies as
    /// Lean writes it.
    fn implied_proof(
        &self,
        found: &super::algebra::Cited,
        rule: crate::citing::Implication,
        target: &Printed,
    ) -> Route<Printed> {
        use crate::citing::Implication;
        match rule {
            // A membership of a wider number system: of one Lean's type
            // already holds, `True`; of ℕ₀ from ℕ, `le_of_lt` of the bound
            // `0 < x`, which Lean writes `0 ≤ x`.
            Implication::WiderSystem if target.is_truth() => Route::Built(Printed::constant(
                "True.intro",
                super::doc::Source::Core,
                super::doc::LeanType::Prop,
            )),
            Implication::WiderSystem => {
                let at_most = matches!(
                    &target.kind,
                    super::doc::TermKind::Infix { op, .. } if op.symbol == "≤"
                );
                let positive = matches!(
                    membership_of_whole(&found.node),
                    Some((_, crate::rules::System::N))
                );
                match (at_most, positive && self.written_as_bound(&found.node)) {
                    (true, true) => Route::Built(nonneg_of(
                        crate::rules::System::N,
                        found.proof.clone(),
                    )),
                    _ => Route::no(format!(
                        "a membership of a wider system, {}, which Lean writes otherwise",
                        target.text()
                    )),
                }
            }
            Implication::RangeBound { lemma } => {
                let says = match self.line_statement(found) {
                    Route::Built(s) => s,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let side = crate::rules::RANGE_BOUNDS
                    .iter()
                    .position(|(_, l)| *l == lemma);
                match side.and_then(|k| range_bounds(&says, &found.proof).into_iter().nth(k)) {
                    Some((proof, _)) => Route::Built(proof),
                    None => Route::no(format!(
                        "the bound {lemma} of {}, which Lean does not write as a range",
                        says.text()
                    )),
                }
            }
            // Lean writes a letter's membership as its bound, and a term's
            // as a whole number equal to it, `∃ m₀, 0 < m₀ ∧ ↑m₀ = 3 ^ m`.
            Implication::SystemFact { lemma } if !self.written_as_bound(&found.node) => {
                Route::no(format!(
                    "what {lemma} gives of a membership Lean writes as a whole number"
                ))
            }
            Implication::SystemFact { lemma } => match system_fact_field(lemma) {
                Some(None) => Route::Built(found.proof.clone()),
                Some(Some(field)) => Route::Built(fields(found.proof.clone(), &[field])),
                None => Route::no(format!(
                    "what {lemma} gives of a membership, which Lean's bound does not"
                )),
            },
            // `X ∈ 𝒫S` is `X ∈ Set.powerset S`, which is `X ⊆ S` by
            // definition: the line's proof is a proof of either.
            Implication::OtherForm {
                lemma: "gsspw" | "elpwi",
            } => Route::Built(found.proof.clone()),
            other => Route::no(format!(
                "a fact a line implies by {other:?}, which the Lean build does not prove yet"
            )),
        }
    }

    /// Whether the two sides of an equation, as Lean writes them, are left
    /// apart in casts once the defines' equations are put in, which
    /// `push_cast` then moves in. `simp only [hD]` puts each `set` letter's
    /// value where the letter stood, and closes a goal that is then `x = x`
    /// itself: where the two sides are alike with each such letter read as
    /// its value (`forms::alike_once_set`), nothing is left. Where Lean
    /// casts such a letter to a type its value is not in, `(S 1 : ℚ)` of an
    /// S in ℤ, the cast stands around the value once it is put in, to be
    /// pushed into it. A define no `set` names, a header's function, is put
    /// in by its own equation, `(f a : ℝ) = …`, which states the claim's
    /// side as the claim casts it, and leaves no cast.
    fn unfolds_to_casts(&self, one: &Printed, other: &Printed) -> bool {
        use super::doc::forms;
        let values = self.set_values();
        !forms::alike_once_set(one, other, &values)
            && (forms::casts_set_letter(one, &values)
                || forms::casts_set_letter(other, &values))
    }

    /// How many sentences the line `line` writes, by the reference that
    /// cites it: a step's claim, a hypothesis, a block's opening line; one
    /// for any other line the writer names, a define or a requires line.
    fn written_sentences(&self, line: &str) -> usize {
        let thm = self.thm;
        let count = |w: Written| w.sentences().len();
        if let Some(step) = thm
            .steps
            .iter()
            .find(|s| s.number.number().is_some_and(|n| n.to_string() == line))
        {
            return step.claim.sentences().len();
        }
        for (i, h) in thm.hypotheses.iter().enumerate() {
            let label = h.label.clone().unwrap_or_else(|| format!("H{}", i + 1));
            if label == line {
                return count(h.body(&thm.path));
            }
        }
        for o in thm.steps.iter().flat_map(|s| &s.openers) {
            if o.label == line {
                return count(o.body(&thm.path));
            }
        }
        1
    }

    /// How `proof`, a line that says `says`, proves `wanted` as Lean has it
    /// (`forms::meets`): as it is, turned round, or by a tactic that moves
    /// the one to the other; None where the two differ in more.
    fn proof_meeting(
        &self,
        proof: Printed,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<Proved> {
        use super::doc::forms::{self, Meets};
        use super::doc::CountForm::{Extended, Natural};
        let meets = forms::meets(says, wanted, &self.set_values())?;
        // A count is taken from ℕ to ℕ∞ or ℤ only as `forms_converted`
        // takes it: a line counting one way meets one counting another not
        // by its casts. The other meetings compare the two read alike, so
        // their counts are in one form.
        let counts = |t: &Printed| t.has_count(Natural) || t.has_count(Extended);
        if (counts(says) || counts(wanted)) && matches!(meets, Meets::Casts { .. }) {
            return None;
        }
        Some(match meets {
            Meets::Same | Meets::Unfolded => Proved::Term(proof),
            Meets::Turned { negated: false } => {
                Proved::Term(super::tactics::symm(proof))
            }
            Meets::Turned { negated: true } => Proved::Term(Printed::applied(
                "Ne.symm",
                super::doc::Source::Core,
                vec![proof],
                super::doc::LeanType::Prop,
            )),
            Meets::Identities(rules) => Proved::Simplified { rules, line: proof },
            Meets::Ranges => Proved::Simplified {
                rules: vec!["Finset.mem_Icc", "Set.mem_Icc"],
                line: proof,
            },
            Meets::Casts { .. } => {
                match forms::casts_differ(says, wanted, &self.set_values()) {
                    Some(apart) => cast_proved(apart, proof, says, wanted)?,
                    None => Proved::Term(proof),
                }
            }
        })
    }

    /// The proof that closes the claim `node`, which Lean writes as `claim`,
    /// from `term`, which says `says` where that is known: one tactic where
    /// the two meet as Lean has them (`proof_meeting`); the alternatives of
    /// `closers` where they do not.
    /// A part of a cited item's sentence at the citation's values, as a
    /// tree: the values put into it, a function or property given as a value
    /// applied where the sentence applies it.
    fn at_values(&self, part: &Node, binding: &crate::matching::Binding) -> Node {
        let read =
            read_at_values(part, binding, &self.sources.checked.grammar.binders());
        crate::matching::standard(
            &crate::matching::substitute_apart(&read, binding, self.sources.ctx),
            self.sources.ctx,
        )
    }

    /// A part of a cited item's sentence at the citation's values, written as
    /// the step's lines are: the values put into its tree, a function or
    /// property given as a value applied where the sentence applies it, by
    /// the theorem's writer, in the calculation's type where it is a row of
    /// one. None where the writer cannot write it.
    fn written_at_values(
        &self,
        part: &Node,
        binding: &crate::matching::Binding,
    ) -> Option<Printed> {
        let at_values = self.at_values(part, binding);
        match self.worked_in.get() {
            Some(at)
                if at_values.notation() == EQUALITY
                    || at_values.notation() == ORDER =>
            {
                self.writer.closed_formula(&at_values, at).built()
            }
            _ => self.writer.formula(&at_values).built(),
        }
    }

    /// The claim from a cited item, or an instance of a line, read in the
    /// step's spelling (`docs/LEAN.md`, a citation): `term` proves Lean's
    /// statement of the item's part, `said`, which the step's lines write as
    /// `written`; `cited` is the citation, None for a line's instance; the
    /// item is read as `written` (`parley_instance`), or is it where the two
    /// are one statement, and the claim follows as the two meet: as written,
    /// turned round, or by the identities the meeting names. None where the
    /// bridge has no fact to read the item by, or the meeting gives no one
    /// way.
    fn read_in_spelling(
        &self,
        cited: Option<&crate::checker::record::Cited>,
        term: &Printed,
        said: &Printed,
        written: &Printed,
        claim: StepClaim<'_>,
    ) -> Option<super::doc::Proof> {
        let StepClaim {
            printed: claim,
            stated: claim_stated,
        } = claim;
        use super::doc::Proof;
        use super::tactics as t;
        // Not of a fact Lean's types make true, which says nothing to read;
        // nor in a step that works through numbers lines or the step name,
        // whose goal those numbers' equations rewrite before the step's
        // proof (`specs_in`), so that it is not the claim as written; nor a
        // claim that counts a set printed afresh, whose line may count in
        // ℕ∞, which the claim so printed does not show (as `closer` holds).
        // A claim as the step's `have` states it (`claim_stated`) shows the
        // form its counts are in.
        let through_named =
            !self.named_specs.is_empty() || !self.said_used.borrow().is_empty();
        // An integer power under a binder is read across only where the two
        // write it alike: taken to `toNat` on one side alone, its exponent's
        // fact holds only under the binder, where `omega` is not asked.
        let binder_powers_apart =
            integer_powers_under_binders(written) != integer_powers_under_binders(said);
        if written.is_truth()
            || through_named
            || (item_counts(claim) && !claim_stated)
            || binder_powers_apart
        {
            return None;
        }
        // Of an item in a wider type: not a value given it that is a numeral
        // alone, `Complex.cos 0`, which stands at the wider type with no cast
        // to move; nor a complex exponent; nor a fact of numerals alone,
        // `(abs 0 : ℤ) = 0` for a row in ℝ, which `norm_cast` works out to
        // `True` and takes nothing across, so it is worked out where it is
        // asked (as `forms::meets` holds). `parley_instance_real` lifts the
        // step instead and leaves the item as it is.
        let letters = cited.map(|c| c.item_letters.as_slice()).unwrap_or_default();
        // Only where the item applies a function to a numeral: in
        // arithmetic, `(2 : ℚ) ^ n`, `norm_cast` reads the numeral as the
        // cast of the claim's.
        let bare_widened = function_of_numeral(said)
            && letters.iter().any(|l| {
                matches!(
                    (l.item_system, l.value_system),
                    (Some(crate::rules::System::C | crate::rules::System::R), Some(v))
                        if Some(v) != l.item_system
                ) && cited
                    .and_then(|c| c.binding.get(&l.letter))
                    .is_some_and(|v| v.names().is_empty())
            });
        let lettered = said
            .walk()
            .iter()
            .any(|n| matches!(n.kind, super::doc::TermKind::Letter(_)));
        let bridge = instance_bridge(said, written);
        if bridge == BridgeTactic::InstanceCast
            && (bare_widened || complex_exponent(said) || !lettered)
        {
            return None;
        }
        let met = self.proof_meeting(
            match one_statement(written, said) {
                true => term.clone(),
                false => t::hyp("hI"),
            },
            written,
            claim,
        )?;
        Some(match one_statement(written, said) {
            true => Proof::By(met.closer()),
            false => Proof::Block(vec![
                Tactic::Have {
                    name: "hI".to_string(),
                    says: written.clone(),
                    proof: Box::new(Proof::By(t::bridge(
                        bridge,
                        vec![TacticArg::Term(t::bracket(term.clone()))],
                    ))),
                },
                met.closer(),
            ]),
        })
    }

    fn closer(
        &self,
        node: &Node,
        claim: Option<StepClaim<'_>>,
        term: Printed,
        says: Option<&Printed>,
        met: HowMet<'_>,
        bridge: Option<CitedBridge>,
    ) -> super::doc::Proof {
        let HowMet { facing, meeting } = met;
        let claim_stated = claim.is_some_and(|c| c.stated);
        let claim = claim.map(|c| c.printed);
        // A claim Lean's types make true says nothing a term is met with; one
        // in another type than the term's is not known to be its; and one
        // that counts a set, printed afresh, stands where a calculation of
        // counts may take its rows in ℕ∞, which the claim so printed does not
        // show. One as the step's `have` states it (`claim_stated`) shows
        // the form its counts are in.
        let counts_unknown = |c: &Printed| item_counts(c) && !claim_stated;
        let unstated = match claim {
            Some(c) if c.is_truth() => ListReason::CitedClaimTruth,
            Some(c) if counts_unknown(c) => ListReason::CitedClaimCounts,
            _ => ListReason::CitedUnstated,
        };
        let claim = claim.filter(|c| !c.is_truth() && !counts_unknown(c));
        if let (Some(claim), Some(says)) = (claim, says) {
            let agree = super::doc::forms::relation_types_agree(says, claim);
            // Where the two are alike but for the types of their terms, or
            // apart only in casts, and `norm_cast` moves every cast in both
            // to the letters and numerals (`casts::norm_cast_moves_all`), it
            // brings the two to one form, and `exact_mod_cast` closes the one
            // by the other. It relates them only through the casts they hold:
            // two stated in different types, an item in ℝ for a claim in ℚ,
            // with no cast from the one to the other, have no form in common.
            let one_type = !super::doc::forms::relation_types_apart(says, claim);
            let by_norm_cast = one_type
                && super::casts::norm_cast_moves_all(says)
                && super::casts::norm_cast_moves_all(claim);
            match self.proof_meeting(term.clone(), says, claim) {
                Some(Proved::Term(t)) if agree => return super::doc::Proof::Term(t),
                Some(Proved::Term(_) | Proved::Cast { .. }) if by_norm_cast => {
                    return super::doc::Proof::By(super::tactics::exact_mod_cast(term))
                }
                // Identity elements dropped, or a cast `norm_cast` does not
                // move, are no fact a tactic is known to take the one to the
                // other by.
                Some(
                    Proved::Term(_)
                    | Proved::Cast { .. }
                    | Proved::Simplified { .. }
                    | Proved::Unsettled { .. },
                )
                | None => {}
            }
            // Statements the writer's comparison does not meet, `0 ≤ ‖(C : ℂ)‖`
            // beside `|C| ≥ 0`, whose forms as `norm_cast` leaves them are
            // alike (`casts::norm_cast_form`): `exact_mod_cast`.
            let values = self.set_values();
            let formed = super::doc::forms::alike_once_set(
                &super::casts::norm_cast_form(says),
                &super::casts::norm_cast_form(claim),
                &values,
            );
            if by_norm_cast && formed {
                return super::doc::Proof::By(super::tactics::exact_mod_cast(term));
            }
            // Two stated in different types that the checker met as they
            // stand (`Cited::meetings`: no identity dropped, nothing spelt
            // otherwise), Lean's statements of them apart in no form the
            // writer chose (`forms::differences`), where `norm_cast` moves
            // every cast of both: `exact_mod_cast` takes the one up to the
            // other. Not a fact of numerals alone, with no letter or
            // function, which `norm_cast` does not take across every order;
            // nor one alike only by a library function read at another type,
            // `Real.exp` as `Complex.exp` of the cast, which `norm_cast` does
            // not take either: no function is widened here.
            let widen = |_: &str, _| None;
            let met_as_written =
                meeting.is_some_and(|m| m.identities.is_empty() && !m.respelled);
            let lifted = met_as_written
                && super::doc::forms::differences(says, claim, &widen).is_empty()
                && (says.lettered() || claim.lettered());
            if !one_type
                && lifted
                && super::casts::norm_cast_moves_all(says)
                && super::casts::norm_cast_moves_all(claim)
            {
                return super::doc::Proof::By(super::tactics::exact_mod_cast(term));
            }
            // The checker paired the parts of a notation whose parts stand in
            // any order out of their places, and took nothing else to meet
            // the two (`Cited::meetings`, `permuted`): where the claim lists a
            // set's members, Lean's `{w, u}` beside the item's `{u, w}`, the
            // item taken in the claim's order.
            let listed = claim.walk().iter().any(|n| {
                matches!(
                    n.kind,
                    super::doc::TermKind::Listed {
                        brackets: super::doc::Brackets::Brace,
                        ..
                    }
                )
            });
            let only_permuted = meeting.is_some_and(|m| {
                m.permuted && m.identities.is_empty() && !m.respelled && !m.turned
            });
            if listed && only_permuted {
                return super::doc::Proof::By(reordered(
                    &term,
                    node.notation() == EQUALITY,
                ));
            }
            // An item worked in a wider field than the claim's, ℂ for a claim
            // in ℝ, taken down to it by the writer's own conversion, as an
            // instance is (`instance_closed`).
            if let Some(down) = read_down(says, claim) {
                use super::tactics as t;
                return super::doc::Proof::By(t::on_h(
                    &term,
                    vec![t::bridge(down, vec![TacticArg::Term(t::hyp("h"))])],
                ));
            }
            // The checker met the item's conclusion at its values with the
            // claim, so in one type the two differ only in spelling and
            // casts: an equation of numbers whose casts `push_cast` all moves
            // is the item's once pushed in and put by the ring's laws,
            // `linear_combination`, whose `parley_norm` checks
            // `push_cast; ring1`; an order with the item's casts is it over
            // the same atoms, `linarith`. `linear_combination e` checks that
            // the claim's left side less its right, less e's, is 0, so an e
            // Lean states turned round is given as `e.symm`. A `toNat` the
            // writer put on one side only, `2 ^ (n.toNat - 1)` beside
            // `2 ^ (n - 1)`, is another atom to `ring1` and to `linarith`,
            // and no cast moves it.
            // The item's statement as `simp` reads it, its functions given
            // as rules applied, `(fun k => 1 / k) 1` as `1 / 1`
            // (`forms::beta_reduced`): `push_cast` and the `norm_num` of
            // `parley_norm` both read it so.
            let reduced = super::doc::forms::beta_reduced(says);
            let of_numbers = node.children.iter().all(|c| c.sort.is("number"));
            let pushed = super::casts::push_cast_moves_all_in_sides(&reduced)
                && super::casts::push_cast_moves_all_in_sides(claim);
            let same_to_nat = to_nat_texts(&reduced) == to_nat_texts(claim);
            let atoms = same_ring_atoms(&reduced, claim, &values);
            match node.notation() {
                EQUALITY
                    if one_type && of_numbers && pushed && same_to_nat && atoms =>
                {
                    // Which way the item faces the claim, as the checker met
                    // them (`Cited::facings`); where it records none, the
                    // step keeps its ways.
                    let facing = match facing {
                        Some(facing) => faced(term, facing),
                        None => {
                            return close(
                                ListReason::CitedFacingUnknown,
                                &self.writer,
                                node,
                                term,
                            )
                        }
                    };
                    return super::doc::Proof::By(super::tactics::linear_combination(
                        facing,
                    ));
                }
                ORDER
                    if one_type
                        && same_to_nat
                        && atoms
                        && cast_texts(&reduced) == cast_texts(claim) =>
                {
                    return super::doc::Proof::By(super::tactics::call(
                        "linarith",
                        vec![super::tactics::rules(vec![term])],
                    ))
                }
                _ => {}
            }
            // An item stated over more than its values are in, as the record
            // says (`cited_bridge`): the Lean facts that read it as the claim.
            let turned_term = || match facing {
                Some(facing) => faced(term.clone(), facing),
                None => term.clone(),
            };
            match bridge {
                Some(CitedBridge::Rules(rules)) => {
                    return super::doc::Proof::By(super::tactics::simpa_only(
                        rules,
                        turned_term(),
                    ))
                }
                Some(CitedBridge::Cast) => {
                    return super::doc::Proof::By(super::tactics::exact_mod_cast(
                        turned_term(),
                    ))
                }
                None => {}
            }
            // The checker met the item with the claim as written
            // (`Cited::meetings`), and the step's proof first puts each term
            // the citation gave as a named number as the cast of that number
            // (`specs_in`, `proof_of`): what is left is the item's relation
            // with each side cast up, which `norm_cast` takes back to the
            // item where the cast table says it moves a cast through the
            // relation (`casts::norm_cast_lifts_relation`).
            let as_written = meeting.is_some_and(|m| {
                m.identities.is_empty() && !m.respelled && !m.turned && !m.permuted
            });
            let through_named =
                !self.specs_in(node, &self.said_used.borrow()).is_empty();
            if as_written && through_named {
                match node.notation() {
                    // An equation the way the checker found it faces, or an
                    // order: `exact_mod_cast` of the item.
                    EQUALITY | ORDER
                        if super::doc::forms::relation_type(claim).is_some_and(
                            |to| super::casts::norm_cast_lifts_relation(says, &to),
                        ) =>
                    {
                        let faced_term = match (node.notation(), facing) {
                            (ORDER, _) => Some(term.clone()),
                            (_, Some(f)) => Some(faced(term.clone(), f)),
                            (_, None) => None,
                        };
                        if let Some(t) = faced_term {
                            return super::doc::Proof::By(
                                super::tactics::exact_mod_cast(t),
                            );
                        }
                    }
                    // A range member Lean writes as the integer that is it
                    // (`wide_range_member`): that integer, the named number,
                    // its equation `rfl`, and the item's membership.
                    _ if wide_range_member(&self.writer, node) => {
                        let rfl = Printed::constant(
                            "rfl",
                            super::doc::Source::Core,
                            super::doc::LeanType::Prop,
                        );
                        return super::doc::Proof::By(Tactic::Exact(
                            range_member_made(rfl, term.clone()),
                        ));
                    }
                    // A claim joined by "and": part by part (`parts_closed`).
                    _ => {
                        if let Some(proof) = parts_closed(node, claim, says, &term) {
                            return proof;
                        }
                    }
                }
            }
            let why = apart(node, &reduced, claim, &values, facing);
            return close(why, &self.writer, node, term);
        }
        // A claim Lean's types make true, `True`, is closed as it stands.
        if unstated == ListReason::CitedClaimTruth {
            return super::doc::Proof::By(super::tactics::call("trivial", vec![]));
        }
        close(unstated, &self.writer, node, term)
    }

    /// The proof of the side a forward reading of `statement`, an item's
    /// sentence at the citation's values, starts from: the line the checker
    /// read it from (`Cited::firsts`), met with that side as Lean has it;
    /// `parley_side` where no line the citation names says it.
    fn premise(&self, cited: &Cited, statement: &Printed) -> Printed {
        left_side(statement)
            .and_then(|wanted| self.first_proof(cited, &wanted))
            .unwrap_or_else(|| side_term(&[]))
    }

    /// What proves a fact a definition's right side asks, `wanted` as Lean
    /// has it where it is known: the line the checker read it from, or,
    /// where none says it or a witness's facts must be put in scope first
    /// (`known`), `parley_side`.
    fn shown_by_line(
        &self,
        cited: &Cited,
        wanted: Option<&Printed>,
        known: &[Tactic],
    ) -> Printed {
        match (known.is_empty(), wanted) {
            (true, Some(w)) => self
                .first_proof(cited, w)
                .unwrap_or_else(|| side_term(known)),
            _ => side_term(known),
        }
    }

    /// The proof of `wanted` from a line the checker read the citation's
    /// reading from (`Cited::firsts`), met as Lean has it; None where none
    /// says it.
    fn first_proof(&self, cited: &Cited, wanted: &Printed) -> Option<Printed> {
        if item_counts(wanted) {
            return None;
        }
        cited.firsts.iter().find_map(|at| {
            let (proof, says) = self.line_says(at).built()?;
            if !super::doc::forms::relation_types_agree(&says, wanted) {
                return None;
            }
            self.proof_meeting(proof, &says, wanted).map(Proved::term)
        })
    }

    /// The proof of a hypothesis of a cited item from where the checker
    /// found it supplied (`Cited::supplied`): the line, the sentence or
    /// the part of one the citation names or the `let` line that says it
    /// once, or the step's requires line, or what one of those implies,
    /// meeting `wanted`, the hypothesis as Lean asks it at the citation's
    /// values. None where no line supplies it, or the line says it
    /// otherwise than Lean asks.
    fn supplied_proof(&self, by: &SuppliedBy, wanted: &Printed) -> Option<Printed> {
        if item_counts(wanted) {
            return None;
        }
        let (proof, says) = match by {
            SuppliedBy::Line(at) | SuppliedBy::SaidOnce(at) => {
                self.line_says(at).built()?
            }
            SuppliedBy::Requires { line, implied } => {
                let step = &self.thm.steps[self.step_now.get()?];
                let name = format!("r{}_{}", step.line, line + 1);
                let [said] = self.trees.get(&name)?.as_slice() else {
                    return None;
                };
                match implied {
                    None => (
                        super::tactics::hyp(&name),
                        self.line_statement(&said.cited()).built()?,
                    ),
                    // What the line implies is what the checker found
                    // `wanted` to be.
                    Some(rule) => (
                        self.implied_proof(&said.cited(), *rule, wanted).built()?,
                        wanted.clone(),
                    ),
                }
            }
            SuppliedBy::Unstated => return None,
        };
        use super::doc::forms;
        // A line in another type than Lean asks, `(10^(k + 1) : ℤ) > 0` for
        // `0 < (10^(k + 1) : ℚ)`, is taken across by `exact_mod_cast`, where
        // the cast table says `norm_cast` moves a cast of the two types
        // through the relation, every cast of what Lean asks moves, and the
        // two are alike but for their casts. `exact_mod_cast` compares the
        // relations as written, so a line saying `>` where Lean asks `<` is
        // turned first (`gt_iff_lt`). ℚ's order is not taken to ℝ's:
        // `norm_cast` does not take a fact of numerals across there, `(0 :
        // ℚ) ≤ 3^m` for `(0 : ℝ) ≤ 3^m`; an equation it takes.
        if forms::relation_types_apart(&says, wanted) {
            use super::{doc::LeanType, templates::Num};
            let rational_to_real = forms::relation_type(&says)
                == Some(LeanType::Num(Num::Rat))
                && forms::relation_type(wanted) == Some(LeanType::Num(Num::Real))
                && !matches!(relation_symbol(wanted), Some("=" | "≠"));
            let lifts = !rational_to_real
                && forms::relation_type(wanted).is_some_and(|to| {
                    super::casts::norm_cast_lifts_relation(&says, &to)
                })
                && super::casts::norm_cast_moves_all(wanted);
            forms::meets(&says, wanted, &self.set_values()).filter(|_| lifts)?;
            let proof = match (relation_symbol(&says), relation_symbol(wanted)) {
                (Some(">"), Some("<")) => turned_order("gt_iff_lt.mp", proof),
                (Some("≥"), Some("≤")) => turned_order("ge_iff_le.mp", proof),
                (Some("<"), Some(">")) => turned_order("gt_iff_lt.mpr", proof),
                (Some("≤"), Some("≥")) => turned_order("ge_iff_le.mpr", proof),
                _ => proof,
            };
            return Some(super::tactics::by_term(super::doc::Proof::By(
                super::tactics::exact_mod_cast(proof),
            )));
        }
        // One whose type is known on one side alone is not known to meet it.
        if !forms::relation_types_agree(&says, wanted) {
            return None;
        }
        self.proof_meeting(proof, &says, wanted).map(Proved::term)
    }

    /// The proof that the value an instantiation gives `letter` is in its
    /// domain, from where the checker found that supplied
    /// (`Instantiated::guards`), the membership as Lean writes it; by
    /// `parley_side` where no line supplies it, or the line says it
    /// otherwise than Lean asks.
    fn value_guard(
        &self,
        recorded: &crate::checker::record::Instantiated,
        letter: &str,
    ) -> Printed {
        recorded
            .guards
            .iter()
            .find(|g| g.letter == letter)
            .and_then(|g| {
                let wanted = self.writer.formula(&g.written).built()?;
                self.supplied_proof(&g.by, &wanted)
            })
            .unwrap_or_else(|| side_term(&[]))
    }

    /// Puts what ends a block, a part or a theorem at `depth`: its last
    /// step's proof in place of the step's `have`, where the step says what
    /// is owed as written and its `have` is the last line there; else the
    /// closing tactic, `exact` of that step's name among them.
    fn close(&mut self, depth: usize, closing: Closing, page_line: usize, spot: Spot) {
        match closing {
            Closing::Closed => {}
            Closing::Last(name) => {
                if !self.last_proves_goal(depth, &name) {
                    self.push_at(
                        depth,
                        Tactic::Exact(super::tactics::hyp(&name)),
                        page_line,
                        spot,
                    );
                }
            }
            Closing::Tactic(t) => self.push_at(depth, *t, page_line, spot),
        }
    }

    /// Where the last line at `depth` is the `have` naming `name`, its proof
    /// put in its place as what proves the goal: a term by `exact`, a
    /// tactic as it is, and the lines of a block one level out. False where
    /// that line is anything else.
    fn last_proves_goal(&mut self, depth: usize, name: &str) -> bool {
        let Some(k) = self.lines.iter().rposition(|l| l.depth <= depth) else {
            return false;
        };
        if self.lines[k].depth != depth {
            return false;
        }
        let Tactic::Have {
            name: had, proof, ..
        } = &self.lines[k].tactic
        else {
            return false;
        };
        if had != name {
            return false;
        }
        let origin = self.lines[k].origin.clone();
        let proof = (**proof).clone();
        match proof {
            super::doc::Proof::Term(t) => self.lines[k].tactic = Tactic::Exact(t),
            super::doc::Proof::By(t) => self.lines[k].tactic = t,
            super::doc::Proof::Block(ts) => {
                for l in &mut self.lines[k + 1..] {
                    l.depth -= 1;
                }
                let inline = ts.into_iter().map(|tactic| ProofLine {
                    depth,
                    tactic,
                    origin: origin.clone(),
                });
                self.lines.splice(k..=k, inline);
            }
        }
        true
    }

    /// A define's name given its value, `set b : G := a⁻¹ with hD1`: the
    /// letter of its type, and the line's equation, b = a⁻¹, by its label.
    fn name_value(
        &mut self,
        d: usize,
        name: &str,
        ty: LetterType,
        value: Printed,
        body: Node,
        depth: usize,
    ) {
        let line = &self.thm.defines[d];
        let label = line_name(&line.label);
        let (at, page_label) = (line.line, line.label.clone());
        let letter_name = super::names::letter(name);
        let is_set = matches!(ty.lean_type(), super::doc::LeanType::Set(_));
        self.push_at(
            depth,
            Tactic::Set {
                name: letter_name.clone(),
                ty: ty.lean_type(),
                value,
                with: label.clone(),
            },
            at,
            Spot::Statement,
        );
        // A set the define names that is finite, U of a set-builder within
        // 𝒫{1, …, n}, is said finite at once, with the proof why it is gives
        // (`finite_proof`): Lean's tactics see the letter and not its value.
        let made_finite = match is_set {
            true => self.finite_proof(&body),
            false => None,
        };
        if let Some(made_finite) = made_finite {
            use super::tactics as t;
            let says = Printed {
                kind: super::doc::TermKind::Field {
                    inner: Box::new(t::hyp(&letter_name)),
                    field: "Finite".to_string(),
                },
                ty: Some(super::doc::LeanType::Prop),
            };
            let proof = super::doc::Proof::By(Tactic::Seq(vec![
                t::call("rw", vec![t::rules(vec![t::hyp(&label)])]),
                Tactic::Exact(made_finite),
            ]));
            self.push_at(
                depth,
                Tactic::Have {
                    name: format!("{label}_finite"),
                    says,
                    proof: Box::new(proof),
                },
                at,
                Spot::Statement,
            );
        }
        self.writer.letters.insert(name.to_string(), ty);
        let letter = Node::name(body.sort.clone(), name);
        let equation = Node::of(
            crate::notations::EQUALS,
            crate::formula::node::Sort::of("formula"),
            vec![letter, body],
        );
        self.named.insert(page_label.clone(), vec![label.clone()]);
        self.trees
            .insert(page_label, vec![LineSentence::only(equation, label)]);
    }

    /// The fact a define of a kind says of its value, `gcd(t, w) ∈ ℕ` of
    /// `let n = gcd(t, w), a positive integer`, as Lean writes it, and its
    /// proof by the define's reason.
    fn kind_shown(&self, d: usize) -> Route<KindShown> {
        let line = &self.thm.defines[d];
        let members = &self.sources.checked.grammar.members;
        let kinded = match line.kinded(&self.thm.path, members) {
            Ok(Some(k)) => k,
            Ok(None) => return Route::no("a define of a kind with no reason"),
            Err(p) => return Route::no(p.to_string()),
        };
        let fact = match self.tree(&kinded.shown.fact) {
            Route::Built(n) => n,
            Route::Declined(why) => return Route::Declined(why),
        };
        let says = match self.writer.formula(&fact) {
            Route::Built(f) => f,
            Route::Declined(why) => return Route::Declined(why),
        };
        let Ok(just) = &kinded.shown.by else {
            return Route::no("a define whose reason does not read");
        };
        let reason = Reason {
            just,
            cited: self.rec.cited_requires.get(&kinded.shown.line),
        };
        let proof = match self.proof_of(reason, 0, &fact) {
            Route::Built(p) => p,
            Route::Declined(why) => return Route::Declined(why),
        };
        Route::Built(KindShown { fact, says, proof })
    }

    /// A define naming a whole number its value is shown to be, `let e =
    /// p/d, a positive integer` with `p/d ∈ ℕ` its reason's fact: that
    /// fact proved by the reason, as a requires line is, and the name taken
    /// from it, `obtain ⟨e, hD1_pos, hD1⟩`, so that the define's equation
    /// e = p/d is said in the value's type.
    fn kinded_witness(
        &mut self,
        d: usize,
        name: &str,
        body: Node,
        depth: usize,
    ) -> Route<()> {
        let line = &self.thm.defines[d];
        let shown = match self.kind_shown(d) {
            Route::Built(s) => s,
            Route::Declined(why) => return Route::Declined(why),
        };
        let KindShown { fact, says, proof } = shown;
        let kind_line = Tactic::Have {
            name: format!("{}_kind", line_name(&line.label)),
            says,
            proof: Box::new(proof),
        };
        let [_, set] = fact.children.as_slice() else {
            return Route::no("a kind's fact that is no membership");
        };
        // The letter is an integer whatever its kind; ℕ and ℕ₀ say its order
        // beside it, 0 < e or 0 ≤ e, as `let e ∈ ℕ` does.
        let system = match super::expr::system_of(set) {
            Some(
                s @ (super::expr::System::Positive | super::expr::System::NonNegative),
            ) => s,
            Some(s @ super::expr::System::Type(super::templates::Num::Int)) => s,
            _ => return Route::no("a define of a kind other than ℕ, ℕ₀ or ℤ"),
        };
        let ordered = !matches!(system, super::expr::System::Type(_));
        let ty = super::templates::Num::Int;
        let label = line_name(&line.label);
        let (at, page_label) = (line.line, line.label.clone());
        let letter = super::names::letter(name);
        // Its kind as a line of the letter, `A ∈ ℕ`, proved by the order
        // named beside it, `0 < A`: a step finds the letter's fact there.
        if ordered {
            let member = fact
                .with_children(vec![Node::name(body.sort.clone(), name), set.clone()]);
            self.store(
                format!("{page_label} kind"),
                vec![LineSentence {
                    at: 0,
                    node: member,
                    name: None,
                    proof: super::tactics::hyp(&format!("{label}_pos")),
                    says: None,
                }],
            );
        }
        // A value of integers, k + 1, is the letter as any define's value
        // is: Lean's `set` of it, which a step citing the define unfolds
        // (`cited_defines`); its kind said as an order of the value, 0 < k +
        // 1, which the `set` makes an order of the letter.
        let integer = self
            .writer
            .carrier(&body)
            .built()
            .is_some_and(|n| n <= super::templates::Num::Int);
        if integer {
            let value = match self.writer.number_fixed(&body, ty) {
                Route::Built(v) => v,
                Route::Declined(why) => return Route::Declined(why),
            };
            self.push_at(depth, kind_line, at, Spot::Statement);
            self.name_value(d, name, LetterType::Number(ty), value, body, depth);
            self.writer.introduce(name, system);
            if ordered {
                self.push_at(
                    depth,
                    Tactic::Name {
                        name: format!("{label}_pos"),
                        term: super::tactics::hyp(&format!("{label}_kind")),
                    },
                    at,
                    Spot::Statement,
                );
            }
            return Route::Built(());
        }
        // A value of a wider type, p/d: its kind's fact is a witness, `∃ m :
        // ℤ, 0 < m ∧ (m : ℚ) = p/d`, and the letter is that m.
        let names = match ordered {
            true => vec![letter.clone(), format!("{label}_pos"), label.clone()],
            false => vec![letter.clone(), label.clone()],
        };
        self.push_at(depth, kind_line, at, Spot::Statement);
        self.push_at(
            depth,
            Tactic::Obtain {
                names,
                says: None,
                from: super::tactics::hyp(&format!("{label}_kind")),
            },
            at,
            Spot::Statement,
        );
        self.writer.introduce(name, system);
        self.witness_letters.push(WitnessLetter {
            value: body.clone(),
            letter: Node::name(body.sort.clone(), name),
        });
        let equation = Node::of(
            crate::notations::EQUALS,
            crate::formula::node::Sort::of("formula"),
            vec![Node::name(body.sort.clone(), name), body],
        );
        self.named.insert(page_label.clone(), vec![label.clone()]);
        self.witnessed.insert(page_label.clone());
        self.trees
            .insert(page_label, vec![LineSentence::only(equation, label)]);
        Route::Built(())
    }

    /// A define of a function whose kind says its values are whole, `let
    /// f(a) = (a^(p − 2)) mod p, an integer, for a ∈ {2, …, p − 2}`, of a
    /// value Lean computes wider: the kind's fact proved by its reason, a
    /// witness at every member, `∀ a ∈ X, ∃ m : ℤ, ↑m = v`, and the function
    /// the choice of each, `obtain ⟨f, hD1⟩ : ∃ g : ℤ → ℤ, ∀ a ∈ X, ↑(g a)
    /// = v`. Its values are then integers, as the kind says and as the
    /// elaborator types the function (`kind_of_values`), and the define's
    /// equation is said at each member, in the value's type, as a line a
    /// step reads at its letter.
    fn kinded_function(
        &mut self,
        d: usize,
        def: &crate::corpus::Define,
        from: super::templates::Num,
        domain: Node,
        body: Node,
        depth: usize,
    ) -> Route<()> {
        use super::doc::{Proof, Quant, TermKind};
        use super::tactics as t;
        let Some(param) = def.params.first() else {
            return Route::no("a kinded function of no argument");
        };
        let KindShown { fact, says, proof } = match self.kind_shown(d) {
            Route::Built(s) => s,
            Route::Declined(why) => return Route::Declined(why),
        };
        let proof = match self.kind_by_witness(d, param, &fact) {
            Some(p) => p,
            None => proof,
        };
        // ∀ a ∈ X, ∃ m : ℤ, ↑m = v: the guard, and the value in its type.
        let TermKind::Quantified {
            quant: Quant::ForAll,
            letter,
            letter_ty,
            guard,
            body: each,
            ..
        } = &says.kind
        else {
            return Route::no("a kinded function whose fact Lean states as no for all");
        };
        let TermKind::Quantified {
            quant: Quant::Exists,
            body: witness,
            ..
        } = &each.kind
        else {
            return Route::no(
                "a kinded function whose values Lean states as no witness",
            );
        };
        let TermKind::Infix { rhs: value, .. } = &witness.kind else {
            return Route::no("a kinded function whose witness is no equation");
        };
        let Some(guard) = guard else {
            return Route::no("a kinded function whose fact has no domain");
        };
        let line = &self.thm.defines[d];
        let (at, page_label) = (line.line, line.label.clone());
        let label = line_name(&line.label);
        let kind = format!("{label}_kind");
        let int = super::templates::Num::Int;
        let function = LetterType::Function { from, to: int }.lean_type();
        let a = || t::hyp(letter);
        let h = || t::hyp("h");
        // ∃ g : ℤ → ℤ, ∀ a ∈ X, ↑(g a) = v.
        let g_a = applied_to(t::hyp("g"), a());
        let equal = Printed::infix(
            super::doc::Op::EQUALS,
            Printed::cast(g_a, value.ty.clone().unwrap_or(super::doc::LeanType::Prop)),
            (**value).clone(),
            super::doc::LeanType::Prop,
        );
        let every = Printed::of(
            TermKind::Quantified {
                quant: Quant::ForAll,
                letter: letter.clone(),
                letter_ty: letter_ty.clone(),
                guard: Some(guard.clone()),
                body: Box::new(equal),
                bounded: false,
            },
            super::doc::LeanType::Prop,
        );
        let chosen = super::expr::witnessed("g".to_string(), function, None, every);
        // ⟨fun a => if h : a ∈ X then (hD1_kind a h).choose else 0, fun a h
        // => by simp only [h, ↓reduceDIte]; exact (hD1_kind a h).choose_spec⟩.
        let at_member = || applied_to(applied_to(t::hyp(&kind), a()), h());
        let pick = Printed::of(
            TermKind::DependentIf {
                proof: "h".to_string(),
                cond: guard.clone(),
                yes: Box::new(projected(at_member(), &["choose"])),
                no: Box::new(Printed::numeral("0", super::doc::LeanType::Num(int))),
            },
            super::doc::LeanType::Num(int),
        );
        // The function applied is reduced and its `if` taken by h together,
        // as `rw` does not reach under the application.
        let spec = t::by_term(Proof::By(Tactic::Seq(vec![
            t::simp_only(
                false,
                None,
                vec![t::forwards(h()), t::forwards(t::lemma("↓reduceDIte"))],
                None,
            ),
            Tactic::Exact(projected(at_member(), &["choose_spec"])),
        ])));
        let made = super::expr::anonymous(vec![
            untyped_lambda(&[letter.as_str()], pick),
            untyped_lambda(&[letter.as_str(), "h"], spec),
        ]);
        self.push_at(
            depth,
            Tactic::Have {
                name: kind.clone(),
                says,
                proof: Box::new(proof),
            },
            at,
            Spot::Statement,
        );
        let f = super::names::letter(&def.name);
        self.push_at(
            depth,
            Tactic::Obtain {
                names: vec![f, label.clone()],
                says: Some(chosen),
                from: made,
            },
            at,
            Spot::Statement,
        );
        self.writer
            .letters
            .insert(def.name.clone(), LetterType::Function { from, to: int });
        // The define says its equation at every member: ∀ a ∈ X, f(a) = v.
        let g = &self.sources.checked.grammar;
        let a_node = Node::name(
            domain
                .sort
                .held()
                .unwrap_or_else(crate::formula::Sort::none),
            &param.name,
        );
        let f_node = Node::name(crate::formula::Sort::of("function"), &def.name);
        let Some(f_a) =
            crate::formula::page::made_as(g, "_(_)", vec![f_node, a_node.clone()])
        else {
            return Route::no("the database declares no _(_)");
        };
        let equation = Node::of(
            crate::notations::EQUALS,
            crate::formula::Sort::of("formula"),
            vec![f_a, body],
        );
        let Some(said) = crate::formula::page::made_as(
            g,
            "for all _ ∈ _, _",
            vec![a_node, domain, equation],
        ) else {
            return Route::no("the database declares no for all _ ∈ _, _");
        };
        self.named.insert(page_label.clone(), vec![label.clone()]);
        self.witnessed.insert(page_label.clone());
        self.trees
            .insert(page_label, vec![LineSentence::only(said, label)]);
        Route::Built(())
    }

    /// The proof of a function's kind, `∀ a ∈ X, ∃ m : ℤ, ↑m = v`, as a
    /// step proves a wide term whole: at a member, `intro a h_a`, the whole
    /// number v is named from the lines its reason cites, read with the
    /// letters the checker read the reason with (`kind_letters`). None
    /// where those lines name no such number.
    fn kind_by_witness(
        &mut self,
        d: usize,
        param: &crate::corpus::define::Param,
        fact: &Node,
    ) -> Option<super::doc::Proof> {
        use super::doc::Proof;
        let line = &self.thm.defines[d];
        let letters = self.rec.kind_letters.get(&line.label)?.clone();
        let members = &self.sources.checked.grammar.members;
        let kinded = line.kinded(&self.thm.path, members).ok()??;
        let just = kinded.shown.by.as_ref().ok()?;
        let facts = self.cited_parts(&just.refs);
        *self.held_now.borrow_mut() = self.held_at(just.line);
        let [_, _, member] = fact.children.as_slice() else {
            return None;
        };
        let [term, _] = member.children.as_slice() else {
            return None;
        };
        let int = super::templates::Num::Int;
        let before = self
            .writer
            .letters
            .insert(param.name.clone(), LetterType::Number(int));
        let shown = self.whole_witness(term, &letters, &facts);
        match before {
            Some(ty) => self.writer.letters.insert(param.name.clone(), ty),
            None => self.writer.letters.shift_remove(&param.name),
        };
        let letter = super::names::letter(&param.name);
        let intro = Tactic::Intro(vec![letter.clone(), format!("h_{letter}")]);
        Some(Proof::By(Tactic::Seq(vec![
            intro,
            tactic_of(&shown.built()?),
        ])))
    }

    /// A define of a function of one number in a proof, `let S(m) =
    /// Σ(j = 1 to m) 3^j, for m ∈ ℕ`: Lean's `set` of a function from the
    /// type of the set its argument runs over to the least type holding its
    /// value, whose hypothesis, named by the label, a step citing the define
    /// unfolds it by (`written_out`).
    fn define_function(
        &mut self,
        d: usize,
        def: &crate::corpus::Define,
        depth: usize,
    ) -> Route<()> {
        let line = &self.thm.defines[d];
        let [param] = def.params.as_slice() else {
            return Route::no("a define of a function of more than one argument");
        };
        if set_valued(self.rec, &def.name) {
            return Route::left_out(SET_VALUED);
        }
        // The checker reads the line's argument, the set it runs over and
        // the value apart.
        let read: Vec<&Node> = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == line.line)
            .map(|(_, node)| node)
            .collect();
        let over = |n: &&&Node| {
            matches!(
                n.notation(),
                crate::notations::NUMBER_SYSTEMS | crate::notations::INTEGER_RANGE
            )
        };
        // Over a number system, a range, or a set of numbers, X of X ⊆ ℤ.
        let of_numbers = |n: &&&Node| {
            !(n.is_name() && *n.text == *param.name)
                && matches!(
                    self.writer.set_members(n),
                    Some(super::expr::Members::Numbers(_))
                )
        };
        let Some(domain) = read
            .iter()
            .find(over)
            .or_else(|| read.iter().find(of_numbers))
        else {
            return Route::left_out(
                "a define of a function on other than a number system",
            );
        };
        // The value is what the line reads besides the domain and the
        // argument; a value that is itself a set of numbers, {|x| : x ∈
        // 𝒫{1, …, k}}, is not the domain.
        let bodies: Vec<&&Node> = read
            .iter()
            .filter(|n| !std::ptr::eq(**n, *domain))
            .filter(|n| !(n.is_name() && *n.text == *param.name))
            .collect();
        let [body] = bodies.as_slice() else {
            return Route::left_out(
                "a define whose value the checker did not read as one term",
            );
        };
        // A function on ℕ, ℕ₀ or a range {0, …, m} takes integers, as the
        // writer's sequences do, so that q(j) of a sum's index is written
        // as it stands; its values off the range are none of the page's.
        let from = match (
            super::expr::system_of(domain),
            self.writer.set_members(domain),
        ) {
            (Some(system), _) => {
                super::expr::letter_type(system).max(super::templates::Num::Int)
            }
            (None, _) if domain.notation() == crate::notations::INTEGER_RANGE => {
                super::templates::Num::Int
            }
            (None, Some(super::expr::Members::Numbers(n))) => {
                n.max(super::templates::Num::Int)
            }
            (None, _) => {
                return Route::no(
                    "a define of a function on a set Lean has no type for",
                )
            }
        };
        // The value is read with the argument a number of that type, in ℕ
        // or ℕ₀ where the domain or range puts it, 10^k of k ∈ ℕ₀ written as
        // the steps write it; the argument is no letter of the proof's
        // after it.
        let system = match super::expr::system_of(domain) {
            Some(s) => Some(s),
            None if domain.notation() == crate::notations::INTEGER_RANGE => {
                Some(super::expr::range_letter_system(domain))
            }
            None => None,
        };
        let whole_before = self.writer.wholes.get(&param.name).copied();
        let before = self
            .writer
            .letters
            .insert(param.name.clone(), LetterType::Number(from));
        if let Some(s) = system {
            self.writer.introduce(&param.name, s);
        }
        // Of a real or complex argument, values of that type at least, as a
        // header function's are (`header_function`).
        let value = match self.writer.carrier(body) {
            Route::Built(to) => {
                let to = match from >= super::templates::Num::Real {
                    true => to.max(from),
                    false => to,
                };
                self.writer.number_fixed(body, to).map(|v| (to, v))
            }
            Route::Declined(why) => Route::Declined(why),
        };
        match before {
            Some(ty) => self.writer.letters.insert(param.name.clone(), ty),
            None => self.writer.letters.shift_remove(&param.name),
        };
        match whole_before {
            Some(s) => self.writer.wholes.insert(param.name.clone(), s),
            None => self.writer.wholes.shift_remove(&param.name),
        };
        let (to, value) = match value {
            Route::Built(v) => v,
            Route::Declined(why) => return Route::Declined(why),
        };
        // A function whose kind says its values are whole, which Lean
        // computes wider: its values are the kind's witnesses.
        if def.kind.is_some() && to > super::templates::Num::Int {
            let (domain, body) = ((*domain).clone(), (**body).clone());
            return self.kinded_function(d, def, from, domain, body, depth);
        }
        let name = super::names::letter(&def.name);
        let label = line_name(&line.label);
        let function = LetterType::Function { from, to }.lean_type();
        // A lambda term, which the writer's comparisons apply where the
        // letter stands applied, as `simp only [hD]` does
        // (`forms::alike_once_set`).
        let lambda = Printed {
            kind: super::doc::TermKind::Quantified {
                quant: super::doc::term::Quant::Fun,
                letter: super::names::letter(&param.name),
                letter_ty: LetterType::Number(from).lean_type(),
                guard: None,
                body: Box::new(value),
                bounded: false,
            },
            ty: Some(function.clone()),
        };
        self.push_at(
            depth,
            Tactic::Set {
                name: name.clone(),
                ty: function,
                value: lambda,
                with: label.clone(),
            },
            line.line,
            Spot::Statement,
        );
        self.writer
            .letters
            .insert(def.name.clone(), LetterType::Function { from, to });
        // Of real or complex numbers on a set, [0, 1]: its domain, within
        // which its limits and derivatives are taken (`domain_of`), as a
        // header function's is.
        let whole = matches!(
            super::expr::system_of(domain),
            Some(super::expr::System::Type(_))
        );
        if !whole && from >= super::templates::Num::Real {
            match self.writer.numbers_at(domain, from) {
                Route::Built(p) => {
                    self.writer.domains.insert(def.name.clone(), p);
                }
                Route::Declined(why) => return Route::Declined(why),
            }
        }
        self.named.insert(line.label.clone(), vec![label]);
        Route::Built(())
    }

    /// A define of the theorem's file, outside the theorem, that its
    /// statement is read with: Lean's `set`, of the least type holding the
    /// term it names, its equation named by the name.
    fn define_outside(&mut self, name: &str, body: &Node) -> Route<()> {
        // A set it names, B = {1, 2}: the set, of the type its members give.
        if let Some(members) = self.writer.members_of(body) {
            let value = match self.writer.set_term(body) {
                Route::Built(v) => v,
                Route::Declined(d) => return Route::Declined(d),
            };
            let lean = super::names::letter(name);
            let ty = LetterType::Set(members);
            self.push_at(
                1,
                Tactic::Set {
                    name: lean.clone(),
                    ty: ty.lean_type(),
                    value,
                    with: format!("h_{lean}"),
                },
                self.thm.line,
                Spot::Statement,
            );
            self.writer.letters.insert(name.to_string(), ty);
            return Route::Built(());
        }
        let ty = match self.writer.carrier(body) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        };
        let value = match self.writer.number_fixed(body, ty) {
            Route::Built(v) => v,
            Route::Declined(d) => return Route::Declined(d),
        };
        let lean = super::names::letter(name);
        let line = self.thm.line;
        self.push_at(
            1,
            Tactic::Set {
                name: lean.clone(),
                ty: self.writer.num_type(ty),
                value,
                with: format!("h_{lean}"),
            },
            line,
            Spot::Statement,
        );
        self.writer
            .letters
            .insert(name.to_string(), LetterType::Number(ty));
        Route::Built(())
    }

    /// `exhibit`: the claim's "there is", with the values the checker read
    /// for its letters, and what it says of them by the lines the checker
    /// found to state it (`Exhibit::shown`), `parley_side` where none does.
    fn exhibit(&self, just: &Justification, node: &Node) -> Route<super::doc::Proof> {
        let Some(exhibit) = self
            .rec
            .exhibited
            .get(&just.line)
            .and_then(|all| all.iter().flatten().next())
        else {
            return Route::no("an exhibit the checker read no values for");
        };
        let binding = &exhibit.values;
        // The facts asked of the values, in the checker's order: each
        // letter's membership, then the body's parts.
        let mut shown = exhibit.shown.iter();
        // there is a ∈ X with nothing said of a, `∃ a ∈ X, True`: the
        // member, that it is in X, and nothing.
        if let ("there-is-some", [letter, set]) =
            (&*node.notation_name(), node.children.as_slice())
        {
            let Some(value) = binding.get(&letter.text) else {
                return Route::no(format!("no value for {}", letter.text));
            };
            let Some(members) = self.writer.set_members(set) else {
                return Route::no("there is some member of a set with no Lean type");
            };
            return self.writer.element_term(value, &members).map(|v| {
                let in_set = super::tactics::by_term(super::doc::Proof::By(
                    super::tactics::bridge(BridgeTactic::SetSide, vec![]),
                ));
                let nothing = Printed::constant(
                    "trivial",
                    super::doc::Source::Core,
                    super::doc::LeanType::Prop,
                );
                super::doc::Proof::Term(super::expr::anonymous(vec![
                    v, in_set, nothing,
                ]))
            });
        }
        let mut parts = Vec::new();
        let mut known = Vec::new();
        let mut body = node;
        // The claim as Lean has it, each "there is" given its value in turn:
        // what each fact about the values says there.
        let mut lean_body = self.writer.formula(node).built();
        while body.notation() == crate::notations::THERE_IS {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let Some(value) = binding.get(&letter.text) else {
                return Route::no(format!("no value for {}", letter.text));
            };
            let membership = shown.next();
            // A member of a set: the value as the writer writes a member,
            // and its membership by the line that says it.
            if let Some(members) = self.writer.members_of(set) {
                let term = match self.writer.element_term(value, &members) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let (guard, next) = exists_at(lean_body.as_ref(), &term);
                parts.push(term);
                parts.push(self.fact_shown(guard.as_ref(), &known, membership));
                lean_body = next;
                body = inner;
                continue;
            }
            // A polynomial: the function, and that it is one.
            if &*set.notation_name() == "polynomials" {
                match self.writer.set_term(value) {
                    Route::Built(p) => parts.push(p),
                    Route::Declined(d) => return Route::Declined(d),
                }
                parts.push(side_term(&known));
                body = inner;
                continue;
            }
            // A function between sets of numbers: the function, of the
            // types the quantifier gives it, and that it maps the one set
            // into the other.
            if let ("functions-from", [from, to]) =
                (&*set.notation_name(), set.children.as_slice())
            {
                match self.function_given(&self.writer, value, from, to) {
                    Route::Built(p) => parts.push(p),
                    Route::Declined(d) => return Route::Declined(d),
                }
                parts.push(side_term(&known));
                body = inner;
                continue;
            }
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
                (super::templates::Num::Int, true)
            } else {
                match super::expr::system_of(set) {
                    Some(s) => (
                        super::expr::letter_type(s),
                        !matches!(s, super::expr::System::Type(_)),
                    ),
                    None => {
                        return Route::no("a value of a letter of no number system")
                    }
                }
            };
            let (guard, next) = match self.witness(value, ty) {
                Route::Built(w) => {
                    let at = exists_at(lean_body.as_ref(), &w.term);
                    parts.push(w.term);
                    known.extend(w.known);
                    at
                }
                Route::Declined(d) => return Route::Declined(d),
            };
            if guarded {
                parts.push(self.fact_shown(guard.as_ref(), &known, membership));
            }
            lean_body = next;
            body = inner;
        }
        if parts.is_empty() {
            return Route::no("an exhibit of no \"there is\"");
        }
        parts.push(self.facts_shown(body, lean_body.as_ref(), &known, &mut shown));
        Route::Built(super::doc::Proof::Term(super::expr::anonymous(parts)))
    }

    /// What proves a fact an exhibit says of its values, `wanted` as Lean
    /// has it where it is known, from where the checker found it stated
    /// (`shown`); `parley_side` where no line states it, or a witness's
    /// facts must be put in scope first (`known`).
    fn fact_shown(
        &self,
        wanted: Option<&Printed>,
        known: &[Tactic],
        shown: Option<&Supplied>,
    ) -> Printed {
        let (true, Some(wanted), Some(shown)) = (known.is_empty(), wanted, shown)
        else {
            return side_term(known);
        };
        self.supplied_proof(&shown.by, wanted)
            .unwrap_or_else(|| side_term(&[]))
    }

    /// The facts an exhibit says of its values, `said`, taken apart as Lean
    /// nests its "and", each proved as `fact_shown` proves it: `wanted` is
    /// the same as Lean has it, where it is known, and `shown` gives where
    /// each part stands, in order.
    fn facts_shown<'s>(
        &self,
        said: &Node,
        wanted: Option<&Printed>,
        known: &[Tactic],
        shown: &mut impl Iterator<Item = &'s Supplied>,
    ) -> Printed {
        match (said.notation(), said.children.as_slice()) {
            (
                crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
                [l, r],
            ) => {
                let (wl, wr) = match wanted.and_then(and_sides) {
                    Some((a, b)) => (Some(a), Some(b)),
                    None => (None, None),
                };
                let left = self.facts_shown(l, wl.as_ref(), known, shown);
                let right = self.facts_shown(r, wr.as_ref(), known, shown);
                super::expr::anonymous(vec![left, right])
            }
            _ => self.fact_shown(wanted, known, shown.next()),
        }
    }

    /// The claim sentence `node` of the step whose reason is on `line`, as
    /// the step's `have` states it (`claimed_all`): what Lean's goal for it
    /// is, a claim of numerals alone in the type of the lines it is reached
    /// from, a claim of counts in the form the step writes its counts in.
    /// None for a sentence no step's `have` states, a calculation's row.
    /// The claim as a line of the proof states it, where one does: a
    /// calculation's row as the calculation states it (`row_stated`), its
    /// counts in the form the rows take them; outside a calculation and a
    /// witness, the step's `have` (`stated_claim`), its counts in the form
    /// the step writes them. Inside a witness's `refine` the goal is what
    /// the claim says of the witness, which no line states (`in_witness`).
    fn stated_form(&self, line: usize, node: &Node) -> Option<Printed> {
        let relation = node.notation() == EQUALITY || node.notation() == ORDER;
        if let Some(row) = self.row_stated.borrow().clone().filter(|_| relation) {
            return Some(row);
        }
        if self.worked_in.get().is_some() || self.in_witness.get() {
            return None;
        }
        self.stated_claim(line, node)
    }

    /// The claim a step's proof is met with, as Lean states it: as a line
    /// states it (`stated_form`); else a relation of numbers in a
    /// calculation's type, told that type (`Writer::closed_formula`); else as
    /// the writer writes it.
    fn claim_as_stated(&self, line: usize, node: &Node) -> Option<Printed> {
        if let Some(stated) = self.stated_form(line, node) {
            return Some(stated);
        }
        let relation = node.notation() == EQUALITY || node.notation() == ORDER;
        let of_numbers = node.children.iter().all(|c| self.writer.is_number(c));
        match self.worked_in.get() {
            Some(at) if relation && of_numbers => {
                self.writer.closed_formula(node, at).built()
            }
            _ => self.writer.formula(node).built(),
        }
    }

    fn stated_claim(&self, line: usize, node: &Node) -> Option<Printed> {
        self.thm
            .steps
            .iter()
            .find(|s| s.just.line == line)
            .and_then(|step| self.claimed_all(step).built())
            .and_then(|all| all.into_iter().find(|(_, n, _)| n.same(node)))
            .map(|(_, _, printed)| printed)
    }

    /// Every set the claim counts, and the item at the citation's values
    /// counts, written from its page formula with why it is finite
    /// (`finite_proof`); a set not shown finite is left out.
    fn finite_counted(
        &self,
        cited: &Cited,
        sentence: &Sentence,
        claim: &Node,
    ) -> Vec<ShownFinite> {
        let item = self.at_values(&sentence.says, &cited.binding);
        let mut out = Vec::new();
        let mut seen: Vec<Node> = Vec::new();
        for set in [claim, &item]
            .into_iter()
            .flat_map(|n| n.walk())
            .filter(|c| &*c.notation_name() == "cardinality")
            .filter_map(|c| c.children.first().cloned())
        {
            if seen
                .iter()
                .any(|s| crate::matching::alike_top(s, &set, self.sources.ctx))
            {
                continue;
            }
            seen.push(set.clone());
            let (Route::Built(written), Some(proof)) =
                (self.writer.set_term(&set), self.finite_proof(&set))
            else {
                continue;
            };
            out.push(ShownFinite {
                set: written,
                proof,
            });
        }
        out
    }

    /// Each exponent of a power in the claim, or in the cited item at the
    /// citation's values, that the record shows at least 0, as Lean writes
    /// it with the proof (`nonneg_proof`).
    fn exponents_shown_whole(
        &self,
        cited: &Cited,
        sentence: &Sentence,
        claim: &Node,
    ) -> Vec<NonNegative> {
        let known = self.supplied_whole(cited);
        let item = self.at_values(&sentence.says, &cited.binding);
        self.exponents_whole_in(&[claim, &item], &known)
    }

    /// A line read, `says`, met with the claim, `wanted`: alike in every form
    /// the writer chose (`forms::differences`); or apart only in a power one
    /// writes as an integer power and the other to its exponent's `toNat`,
    /// each converted as a citation's is (`forms_converted`), its exponent's
    /// fact from the record, read from the page formulas of the two,
    /// `pages`; or apart otherwise, or at an exponent with no fact.
    fn powers_met(
        &self,
        pages: &[&Node],
        says: &Printed,
        wanted: &Printed,
        proof: &Printed,
        turned: bool,
    ) -> PowersMet {
        use super::doc::forms;
        let templates = self.writer.templates;
        let widen = |head: &str, at| templates.same_function_at(head, at);
        let facing = match turned {
            true => forms::turned_statement(says),
            false => says.clone(),
        };
        if forms::differences(&facing, wanted, &widen).is_empty() {
            return PowersMet::Alike;
        }
        match self.powers_converted_at(pages, says, wanted, proof, turned) {
            Some(proof) => PowersMet::Converted(Box::new(proof)),
            None => PowersMet::Apart,
        }
    }

    /// `powers_met`'s conversion: None where the two are alike already, or
    /// apart otherwise than in such powers.
    fn powers_converted_at(
        &self,
        pages: &[&Node],
        says: &Printed,
        wanted: &Printed,
        proof: &Printed,
        turned: bool,
    ) -> Option<super::doc::Proof> {
        use super::doc::forms;
        let templates = self.writer.templates;
        let widen = |head: &str, at| templates.same_function_at(head, at);
        let facing = match turned {
            true => forms::turned_statement(says),
            false => says.clone(),
        };
        let found = forms::differences(&facing, wanted, &widen);
        let to_nat = |d: &forms::FormDifference| {
            matches!(d, forms::FormDifference::ToNat { .. })
        };
        if found.is_empty() || !found.iter().all(to_nat) {
            return None;
        }
        let mut zpow = forms::integer_exponents(&facing);
        zpow.extend(forms::integer_exponents(wanted));
        let whole: Vec<NonNegative> = self
            .exponents_whole_in(pages, &[])
            .into_iter()
            .filter(|w| zpow.iter().any(|e| forms::alike(e, &w.exponent)))
            .collect();
        let exponents: Vec<Printed> =
            whole.iter().map(|w| w.exponent.clone()).collect();
        let left = forms::differences(
            &forms::with_natural_powers(&facing, &exponents),
            &forms::with_natural_powers(wanted, &exponents),
            &widen,
        );
        let conversion = Conversion {
            finite: &[],
            whole: &whole,
            bound: &[],
            cast_powers: false,
            identities: &[],
            numeral_to_nat: leaves_numeral_to_nat(&facing)
                || leaves_numeral_to_nat(wanted),
        };
        (!whole.is_empty() && left.is_empty())
            .then(|| forms_converted(proof, &conversion, turned))
    }

    /// Each exponent of a power in the page formulas `pages` that the
    /// record shows at least 0, as Lean writes it, with the proof
    /// (`nonneg_proof`), `known` among the facts it is shown from.
    fn exponents_whole_in(
        &self,
        pages: &[&Node],
        known: &[ShownWhole],
    ) -> Vec<NonNegative> {
        let ctx = self.sources.ctx;
        let mut out = Vec::new();
        let mut seen: Vec<Node> = Vec::new();
        for e in pages
            .iter()
            .flat_map(|n| n.walk())
            .filter(|n| n.notation() == crate::notations::POWER)
            .filter_map(|n| n.children.get(1).cloned())
        {
            if seen.iter().any(|s| crate::matching::alike_top(s, &e, ctx)) {
                continue;
            }
            seen.push(e.clone());
            let (Route::Built(exponent), Some(proof)) = (
                self.writer.number_fixed(&e, super::templates::Num::Int),
                self.nonneg_proof(&e, known),
            ) else {
                continue;
            };
            out.push(NonNegative { exponent, proof });
        }
        out
    }

    /// The values a citation gives the cited item's letters in ℕ or ℕ₀,
    /// each with the proof of `0 ≤ v` from where the checker found the
    /// item's hypothesis `m ∈ ℕ₀` supplied (`Cited::supplied`).
    fn supplied_whole(&self, cited: &Cited) -> Vec<ShownWhole> {
        cited
            .supplied
            .iter()
            .filter_map(|s| {
                let at = self.at_values(&s.want, &cited.binding);
                let (value, system) = membership_of_whole(&at)?;
                let wanted = self.writer.formula(&at).built()?;
                let proof = self.supplied_proof(&s.by, &wanted)?;
                Some(ShownWhole {
                    term: value.clone(),
                    proof: nonneg_of(system, proof),
                })
            })
            .collect()
    }

    /// The proof that the integer `e` is at least 0, `0 ≤ e`, from why the
    /// said-once walk puts it in ℕ₀ (`citing::reason_within`), the walk the
    /// Metamath build proves memberships from. A part the walk does not take
    /// apart is in ℕ₀ where `known` gives it, a hypothesis of a cited item
    /// the checker found supplied, or where a line the step names says so,
    /// `i − n ∈ ℕ₀` of an `instantiate … from 2.1`. None where the walk does
    /// not put e in ℕ₀, or gives a reason `nonneg_by` writes no proof for.
    fn nonneg_proof(&self, e: &Node, known: &[ShownWhole]) -> Option<Printed> {
        use crate::citing::OnceReason;
        use crate::rules::System;
        let ctx = self.sources.ctx;
        let mut known = known.to_vec();
        // What the lines in scope bound below at 0 or above, each from the
        // line that says it (`Bound::said_by`): 4.3's `0 < e`.
        for b in self.writer.bounds.terms.iter().filter(|b| b.least >= 0) {
            if let Some(proof) = self.bound_nonneg(b) {
                known.push(ShownWhole {
                    term: b.term.clone(),
                    proof,
                });
            }
        }
        if let Some(i) = self.step_now.get() {
            for f in self.step_facts(i) {
                let Some((term, system)) = membership_of_whole(&f.node) else {
                    continue;
                };
                if self.written_as_bound(&f.node) {
                    known.push(ShownWhole {
                        term: term.clone(),
                        proof: nonneg_of(system, f.proof.clone()),
                    });
                }
            }
        }
        let known = known.as_slice();
        let letters = self.writer.page_systems();
        let nonzero = |d: &Node| crate::citing::nonzero_said_once(d, &letters);
        let said = |t: &Node, s: System| {
            (System::N0.within(s)
                && known
                    .iter()
                    .any(|k| crate::matching::alike_top(&k.term, t, ctx)))
            .then_some(OnceReason::Stated)
        };
        let reason =
            crate::citing::reason_within(e, System::N0, &letters, &nonzero, &said)?;
        self.nonneg_by(e, &reason, known)
    }

    /// `0 ≤ t` of a term a line in scope bounds below at 0 or above
    /// (`Bound`), from that line as Lean states it: `t ∈ ℕ₀` itself, `t ∈ ℕ`
    /// by `le_of_lt`, `a ≤ t` by `le_trans` of `0 ≤ a`, `a < t` by `le_of_lt`
    /// of `lt_of_le_of_lt` of `0 ≤ a`, the numeral's fact by `norm_num`.
    /// None where no line in scope says it, or says it of a bound that is no
    /// numeral.
    fn bound_nonneg(&self, b: &crate::citing::bounds::Bound) -> Option<Printed> {
        use crate::notations::{
            AT_LEAST, AT_MOST, GREATER, LESS, MEMBERSHIP, NUMERAL, ORDER,
        };
        let ctx = self.sources.ctx;
        let said = b.said_by.as_ref()?;
        let line = self
            .trees
            .values()
            .flatten()
            .find(|s| crate::matching::alike_top(&s.node, said, ctx))?;
        let proof = line.proof.clone();
        if said.notation() == MEMBERSHIP {
            let (_, system) = membership_of_whole(said)?;
            return Some(nonneg_of(system, proof));
        }
        let [l, r] = said.children.as_slice() else {
            return None;
        };
        let s = said.spelling();
        let (bound, strict) = match () {
            _ if said.notation() != ORDER => return None,
            _ if s == LESS => (l, true),
            _ if s == GREATER => (r, true),
            _ if s == AT_MOST => (l, false),
            _ if s == AT_LEAST => (r, false),
            _ => return None,
        };
        if bound.notation() != NUMERAL {
            return None;
        }
        let applied = |name: &str, args: Vec<Printed>| {
            Printed::applied(
                name,
                super::doc::Source::Mathlib,
                args,
                super::doc::LeanType::Prop,
            )
        };
        Some(match strict {
            true => applied(
                "le_of_lt",
                vec![super::tactics::bracket(applied(
                    "lt_of_le_of_lt",
                    vec![norm_num_term(), proof],
                ))],
            ),
            false => applied("le_trans", vec![norm_num_term(), proof]),
        })
    }

    /// `nonneg_proof` of `e` for the reason the walk gives: a part `known`
    /// gives, by its proof; a numeral, by `norm_num`; a letter, from the line
    /// that introduces it (`letter_nonneg`); a factorial, a natural number
    /// cast, `Nat.cast_nonneg`; a sum or a product of parts the
    /// walk puts in ℕ₀, `add_nonneg` or `mul_nonneg` of theirs. None for any
    /// other reason.
    fn nonneg_by(
        &self,
        e: &Node,
        reason: &crate::citing::OnceReason,
        known: &[ShownWhole],
    ) -> Option<Printed> {
        use crate::citing::OnceReason;
        use crate::notations::{ADDITIVE, MULTIPLICATIVE, PLUS, TIMES};
        let ctx = self.sources.ctx;
        let both = |lemma: &str, parts: &[Node], reasons: &[OnceReason]| {
            let ([a, b], [ra, rb]) = (parts, reasons) else {
                return None;
            };
            Some(Printed::applied(
                lemma,
                super::doc::Source::Mathlib,
                vec![
                    super::tactics::bracket(self.nonneg_by(a, ra, known)?),
                    super::tactics::bracket(self.nonneg_by(b, rb, known)?),
                ],
                super::doc::LeanType::Prop,
            ))
        };
        match (reason, e.notation()) {
            (OnceReason::Stated, _) => known
                .iter()
                .find(|k| crate::matching::alike_top(&k.term, e, ctx))
                .map(|k| k.proof.clone()),
            (OnceReason::Numeral, _) => Some(norm_num_term()),
            (OnceReason::Letter, _) => self.letter_nonneg(e),
            // n! is a natural number, which Lean casts to ℤ.
            (OnceReason::Factorial(_), _) => Some(Printed::applied(
                "Nat.cast_nonneg",
                super::doc::Source::Mathlib,
                vec![Printed::of(
                    super::doc::TermKind::Elided,
                    super::doc::LeanType::Prop,
                )],
                super::doc::LeanType::Prop,
            )),
            (OnceReason::Built(reasons), ADDITIVE) if e.spelling() == PLUS => {
                both("add_nonneg", &e.children, reasons)
            }
            (OnceReason::Built(reasons), MULTIPLICATIVE) if e.spelling() == TIMES => {
                both("mul_nonneg", &e.children, reasons)
            }
            _ => None,
        }
    }

    /// `0 ≤ n` of a letter the said-once walk puts in ℕ₀, from the line in
    /// scope that introduces it: `n ∈ ℕ₀`, which Lean states `0 ≤ n`; `n ∈
    /// ℕ`, `le_of_lt` of its `0 < n`; `n ∈ {a, …, b}` of a numeral a,
    /// `le_trans` of `0 ≤ a` and the range's lower bound. None where no line
    /// in scope introduces it so.
    fn letter_nonneg(&self, e: &Node) -> Option<Printed> {
        use super::expr::System;
        if !e.is_name() {
            return None;
        }
        self.trees.values().flatten().find_map(|s| {
            if let Some((letter, system)) = super::statement::introduces(&s.node) {
                if letter.as_str() != &*e.text {
                    return None;
                }
                return match system {
                    System::Positive => {
                        Some(nonneg_of(crate::rules::System::N, s.proof.clone()))
                    }
                    System::NonNegative => Some(s.proof.clone()),
                    System::Type(_) => None,
                };
            }
            let letter = super::statement::range_letter(&s.node)?;
            let from = s.node.children.get(1)?.children.first()?;
            if letter.as_str() != &*e.text
                || from.notation() != crate::notations::NUMERAL
            {
                return None;
            }
            let lower = Printed {
                kind: super::doc::TermKind::Field {
                    inner: Box::new(super::tactics::bracket(Printed::applied(
                        "Finset.mem_Icc.mp",
                        super::doc::Source::Mathlib,
                        vec![s.proof.clone()],
                        super::doc::LeanType::Prop,
                    ))),
                    field: "1".to_string(),
                },
                ty: Some(super::doc::LeanType::Prop),
            };
            Some(Printed::applied(
                "le_trans",
                super::doc::Source::Mathlib,
                vec![super::tactics::bracket(norm_num_term()), lower],
                super::doc::LeanType::Prop,
            ))
        })
    }

    /// The proof that `set` is finite, from why the checker says it is
    /// (`citing::finite::finite_by` over the facts the writer is given): a
    /// line's name where a line says so; `(whole).subset h` of a part of a
    /// finite set by the line `h`; and how the set is made, by Mathlib's
    /// lemmas for ∅, a listed set, a range, 𝒫, ∪, an image, and `.subset`
    /// of A ∖ B, A ∩ B and a set-builder within A. None where the set is not
    /// shown finite, or the reason names nothing a proof is written from: a
    /// define's function, or a letter bound over a set.
    fn finite_proof(&self, set: &Node) -> Option<Printed> {
        let why = crate::citing::finite::finite_by(
            self.writer.grammar,
            &self.writer.finite,
            set,
        )?;
        self.proof_of_finite(&why, set)
    }

    /// `finite_proof` of `set` for the reason `why`.
    fn proof_of_finite(
        &self,
        why: &crate::citing::finite::FiniteBy,
        set: &Node,
    ) -> Option<Printed> {
        use super::doc::TermKind;
        use crate::citing::finite::{FiniteBy, Making};
        let field = |inner: Printed, name: &str| projected(inner, &[name]);
        let hole = || Printed::of(TermKind::Elided, super::doc::LeanType::Prop);
        let constant = |name: &str| {
            Printed::constant(
                name,
                super::doc::Source::Mathlib,
                super::doc::LeanType::Prop,
            )
        };
        // A part of A, by the membership of each member: `fun _ h => h.1` of
        // a set-builder, A ∖ B or A ∩ B within A, `h.2` of A ∩ B within B.
        let part_of = |whole: Printed, side: &str| {
            let member = untyped_lambda(
                &["_", "h"],
                Printed {
                    kind: TermKind::Field {
                        inner: Box::new(super::tactics::hyp("h")),
                        field: side.to_string(),
                    },
                    ty: Some(super::doc::LeanType::Prop),
                },
            );
            applied_to(field(whole, "subset"), super::tactics::bracket(member))
        };
        let child = |k: usize| set.children.get(k);
        let of = |k: usize| {
            let part = child(k)?;
            self.finite_proof(part)
        };
        match why {
            FiniteBy::Said(line) => self.line_saying(line),
            // A count given as a number at least 1, written in ℕ,
            // `(X.ncard : ℤ) = 2`: its count is not 0, by the line and the
            // bounds in scope.
            FiniteBy::Counted {
                at_least_one: true, ..
            } => Some(Printed::applied(
                "Set.finite_of_ncard_ne_zero",
                super::doc::Source::Mathlib,
                vec![super::tactics::by_term(super::doc::Proof::By(
                    super::tactics::call("omega", vec![]),
                ))],
                super::doc::LeanType::Prop,
            )),
            // A count that may be 0, written in ℕ∞, `X.encard = ↑m`.
            FiniteBy::Counted {
                line,
                at_least_one: false,
            } => Some(Printed::applied(
                "Set.finite_of_encard_eq_coe",
                super::doc::Source::Mathlib,
                vec![self.line_saying(line)?],
                super::doc::LeanType::Prop,
            )),
            FiniteBy::Part { line, whole } => {
                let said = self.line_node(line)?;
                let whole_set = match (said.notation(), said.children.as_slice()) {
                    (crate::notations::MEMBERSHIP, [_, powerset]) => {
                        powerset.children.first()?
                    }
                    (_, [_, whole]) => whole,
                    _ => return None,
                };
                let whole_proof = self.proof_of_finite(whole, whole_set)?;
                Some(applied_to(
                    field(whole_proof, "subset"),
                    self.line_saying(line)?,
                ))
            }
            FiniteBy::Made(made) => match made {
                Making::Empty => Some(constant("Set.finite_empty")),
                Making::Listed => Some(applied_to(constant("Set.toFinite"), hole())),
                Making::Range => Some(applied_to(
                    applied_to(constant("Set.finite_Icc"), hole()),
                    hole(),
                )),
                Making::Powerset(_) => Some(field(of(0)?, "powerset")),
                Making::Builder(_) => Some(part_of(of(1)?, "1")),
                Making::Minus(_) => Some(part_of(of(0)?, "1")),
                Making::Inter(_) => match of(0) {
                    Some(left) => Some(part_of(left, "1")),
                    None => Some(part_of(of(1)?, "2")),
                },
                Making::Union(_, _) => Some(applied_to(
                    field(of(0)?, "union"),
                    super::tactics::bracket(of(1)?),
                )),
                Making::Image(_) => Some(applied_to(field(of(2)?, "image"), hole())),
                Making::Applied(_) => None,
            },
            FiniteBy::Define(_) | FiniteBy::Bound(_) | FiniteBy::MemberOf(_) => None,
        }
    }

    /// The sentence of a line in scope the page prints as `printed`.
    fn line_node(&self, printed: &str) -> Option<&Node> {
        self.trees
            .values()
            .flatten()
            .map(|s| &s.node)
            .find(|n| self.writer.grammar.print(n) == printed)
    }

    /// The proof of the sentence of a line in scope the page prints as
    /// `printed`: its name, or the projection that takes it.
    fn line_saying(&self, printed: &str) -> Option<Printed> {
        self.trees
            .values()
            .flatten()
            .find(|s| self.writer.grammar.print(&s.node) == printed)
            .map(|s| s.proof.clone())
    }

    /// A `transitivity` step's chain composed link by link
    /// (`CheckedTheorem::links`): each link the line the checker placed it
    /// in, read the way the chain goes, an equation read from its right side
    /// by `.symm` and an order by its converse, which Lean takes as the same
    /// statement; a chain going down taken as its links going up from the
    /// last; and the links joined by the lemma for each pair of relations,
    /// `lt_of_le_of_lt` of `≤` then `<`. Closed by `exact`, or by
    /// `exact_mod_cast` where the claim is in another type than the links.
    /// None where a link stands in no line, or the links are not all in one
    /// type, or the chain is of equations alone, which the claim may write
    /// either way round.
    fn chain_composed(
        &self,
        just: &Justification,
        node: &Node,
    ) -> Option<super::doc::Proof> {
        use super::doc::forms;
        let converse = |s: &str| -> Option<&'static str> {
            match s {
                "=" => Some("="),
                "<" => Some(">"),
                ">" => Some("<"),
                "≤" => Some("≥"),
                "≥" => Some("≤"),
                _ => None,
            }
        };
        let mut read: Vec<(Printed, &'static str)> = Vec::new();
        let mut ty = None;
        for link in self.rec.links.get(&just.line)? {
            let (proof, says) = self.line_says(link.at.as_ref()?).built()?;
            let symbol = relation_symbol(&says)?;
            let t = forms::relation_type(&says)?;
            if *ty.get_or_insert(t.clone()) != t {
                return None;
            }
            // Only a relation of the five makes a link.
            let turned = converse(symbol)?;
            read.push(match (link.turned, symbol) {
                (true, "=") => (super::tactics::symm(proof), "="),
                (true, _) => (proof, turned),
                (false, s) => (proof, s),
            });
        }
        if read.iter().any(|(_, s)| matches!(*s, ">" | "≥")) {
            read = read
                .into_iter()
                .rev()
                .map(|(p, s)| match s {
                    "=" => Some((super::tactics::symm(p), "=")),
                    s => Some((p, converse(s)?)),
                })
                .collect::<Option<_>>()?;
        }
        let mut links = read.into_iter();
        let (mut proof, mut rel) = links.next()?;
        for (next, s) in links {
            let (lemma, joined) = match (rel, s) {
                ("=", "=") => ("Eq.trans", "="),
                ("=", "≤") => ("Eq.trans_le", "≤"),
                ("=", "<") => ("Eq.trans_lt", "<"),
                ("≤", "=") => ("LE.le.trans_eq", "≤"),
                ("≤", "≤") => ("le_trans", "≤"),
                ("≤", "<") => ("lt_of_le_of_lt", "<"),
                ("<", "=") => ("LT.lt.trans_eq", "<"),
                ("<", "≤") => ("lt_of_lt_of_le", "<"),
                ("<", "<") => ("lt_trans", "<"),
                _ => return None,
            };
            proof = Printed::applied(
                lemma,
                super::doc::Source::Mathlib,
                vec![proof, next],
                super::doc::LeanType::Prop,
            );
            rel = joined;
        }
        if rel == "=" {
            return None;
        }
        let claim = self.claim_as_stated(just.line, node)?;
        let tactic = match forms::relation_type(&claim) == ty {
            true => Tactic::Exact(proof),
            false => super::tactics::exact_mod_cast(proof),
        };
        Some(super::doc::Proof::By(tactic))
    }

    /// A sentence of an order step's claim from what the checker recorded
    /// it rests on (`CheckedTheorem::orders`): each part joined by "and" by
    /// `order_part`, the parts in `⟨…⟩` as the sentence joins them. `line`
    /// is the justification's, `k` the sentence's place, `node` the
    /// sentence as Lean states it.
    fn order_proof(
        &self,
        line: usize,
        k: usize,
        node: &Node,
    ) -> Route<super::doc::Proof> {
        let Some(parts) = self.rec.orders.get(&line).and_then(|o| o.sentences.get(k))
        else {
            return Route::no("an order step the checker recorded no facts for");
        };
        let mut left = parts.iter();
        let proof = match self.order_joined(node, &mut left) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        match left.next() {
            None => Route::Built(proof),
            Some(_) => {
                Route::no("an order step recorded with more parts than its claim")
            }
        }
    }

    /// The proof of `node`, a sentence or a part of one, taking its parts
    /// joined by "and" from `parts` left to right, as the checker counts
    /// them.
    fn order_joined<'p>(
        &self,
        node: &Node,
        parts: &mut impl Iterator<Item = &'p crate::checker::record::OrderPart>,
    ) -> Route<super::doc::Proof> {
        use super::doc::Proof;
        if node.notation() != crate::notations::CONJUNCTION {
            let Some(part) = parts.next() else {
                return Route::no(
                    "an order step recorded with fewer parts than its claim",
                );
            };
            return self.order_part(part, node);
        }
        let mut items = Vec::new();
        for child in &node.children {
            match self.order_joined(child, parts) {
                Route::Built(Proof::Term(t)) => items.push(t),
                Route::Built(p) => items.push(super::tactics::by_term(p)),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        Route::Built(Proof::Term(super::expr::anonymous(items)))
    }

    /// One part of an order step's claim, `node`, from what it rests on:
    /// the fact that says a disequality, `Ne.symm` of it where it says it
    /// turned; `ne_of_lt` or `ne_of_gt` of the order a `weakening` makes
    /// one of; otherwise `linarith only` over the facts it adds, each
    /// disequality it takes both ways split first by `Ne.lt_or_gt`.
    ///
    /// Linear arithmetic adds facts of one type. Where Lean states the
    /// claim and the facts in different number types, it works in the
    /// widest of them: a fact in a narrower one is taken up to it by
    /// `exact_mod_cast`, and a claim in a narrower one is proved there and
    /// taken down by `exact_mod_cast`.
    fn order_part(
        &self,
        part: &crate::checker::record::OrderPart,
        node: &Node,
    ) -> Route<super::doc::Proof> {
        use super::doc::{LeanType, Proof, Source, TermKind};
        use crate::checker::record::Weakened;
        let wanted = match self.writer.formula(node) {
            Route::Built(w) => w,
            Route::Declined(d) => return Route::Declined(d),
        };
        if let Some(r) = &part.restates {
            let fact = match self.order_fact(&r.by) {
                Route::Built(f) => f,
                Route::Declined(d) => return Route::Declined(d),
            };
            if super::doc::forms::relation_types_apart(&fact.says, &wanted) {
                return Route::no(
                    "a disequality an order step restates, in another type",
                );
            }
            // The checker found the two the same up to moving terms across,
            // `a − b ≠ 0` of `a ≠ b`: where Lean writes them alike the fact
            // is the claim; otherwise an equation denying the claim gives
            // one denying the fact by linear arithmetic.
            if fact.says.text() == wanted.text() {
                return Route::Built(Proof::Term(fact.proof));
            }
            if r.turned {
                let turned = Printed::applied(
                    "Ne.symm",
                    Source::Mathlib,
                    vec![fact.proof.clone()],
                    LeanType::Prop,
                );
                if turned_relation_text(&fact.says).as_deref() == Some(&wanted.text()) {
                    return Route::Built(Proof::Term(turned));
                }
            }
            let mut with = vec![super::tactics::hyp("h")];
            for f in &part.uses {
                match self.order_fact(f) {
                    Route::Built(t)
                        if !super::doc::forms::relation_types_apart(
                            &t.says, &wanted,
                        ) =>
                    {
                        with.push(t.proof)
                    }
                    Route::Built(_) => {
                        return Route::no(
                            "a define an order step adds, in another type",
                        );
                    }
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            let equal = split_linarith(&[], with);
            let body = Printed::of(
                TermKind::App {
                    head: Box::new(fact.proof),
                    args: vec![super::doc::Arg::Explicit(equal)],
                    explicit: false,
                },
                LeanType::Prop,
            );
            return Route::Built(Proof::Term(Printed::of(
                TermKind::Lambda {
                    letters: vec!["h".to_string()],
                    body: Box::new(body),
                },
                LeanType::Prop,
            )));
        }
        let mut facts = Vec::new();
        let mut split = Vec::new();
        let read = part
            .uses
            .iter()
            .map(|f| (f, false))
            .chain(part.split.iter().map(|f| (f, true)));
        for (f, apart) in read {
            match self.order_fact(f) {
                Route::Built(t) if apart => split.push(t),
                Route::Built(t) => facts.push(t),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // The widest type among the claim and the facts.
        let claim_in = number_type(&wanted);
        let mut widest = claim_in;
        for f in facts.iter().chain(&split) {
            match (number_type(&f.says), widest) {
                (Some(t), Some(w)) => widest = Some(t.max(w)),
                (None, None) => {}
                _ => {
                    return Route::no(
                        "an order step's facts in types other than numbers",
                    )
                }
            }
        }
        // `(show T by exact_mod_cast f)`: `linarith` reads a fact `show`
        // states before it runs, where an ascription's proof is left to
        // after.
        let widened = |f: OrderFactTerm| -> Route<Printed> {
            let Some(to) = widest.filter(|w| number_type(&f.says) != Some(*w)) else {
                return Route::Built(f.proof);
            };
            if !f.widens {
                return Route::no("a define's kind an order step adds in a wider type");
            }
            let says = match self.writer.closed_formula(&f.node, to) {
                Route::Built(s) => s,
                Route::Declined(d) => return Route::Declined(d),
            };
            if !(cast_crosses(&f.says, &says)
                && super::casts::norm_cast_moves_all(&says)
                && super::casts::norm_cast_moves_all(&f.says))
            {
                return Route::no(
                    "an order step's fact in a narrower type than norm_cast takes up",
                );
            }
            Route::Built(super::tactics::bracket(shown(
                says,
                Proof::By(super::tactics::exact_mod_cast(f.proof)),
            )))
        };
        let stated: Vec<&Printed> = std::iter::once(&wanted)
            .chain(facts.iter().chain(&split).map(|f| &f.says))
            .collect();
        let ties = reciprocals(&stated);
        let mut added = Vec::new();
        for f in facts {
            match widened(f) {
                Route::Built(t) => added.push(t),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        added.extend(ties);
        let mut apart = Vec::new();
        for f in split {
            match widened(f) {
                Route::Built(t) => apart.push(t),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        let linear = split_linarith(&apart, added);
        let narrower = match (claim_in, widest) {
            (Some(c), Some(w)) if c != w => Some(w),
            _ => None,
        };
        if let Some(to) = narrower {
            if part.weakened.is_some() {
                return Route::no(
                    "a disequality weakened from an order in a wider type",
                );
            }
            let says = match self.writer.closed_formula(node, to) {
                Route::Built(s) => s,
                Route::Declined(d) => return Route::Declined(d),
            };
            // `exact_mod_cast` takes the claim back where `norm_cast` moves
            // every cast of both statements (the cast table).
            if !(cast_crosses(&wanted, &says)
                && super::casts::norm_cast_moves_all(&says)
                && super::casts::norm_cast_moves_all(&wanted))
            {
                return Route::no("an order step's claim in a narrower type than norm_cast takes it to");
            }
            let proof = match linear.kind {
                TermKind::By(proof) => *proof,
                _ => Proof::By(Tactic::Exact(linear)),
            };
            return Route::Built(Proof::By(super::tactics::exact_mod_cast(
                super::tactics::bracket(shown(says, proof)),
            )));
        }
        let weak = |lemma: &str| {
            Printed::applied(
                lemma,
                Source::Mathlib,
                vec![linear.clone()],
                LeanType::Prop,
            )
        };
        Route::Built(match part.weakened {
            Some(Weakened::Below) => Proof::Term(weak("ne_of_lt")),
            Some(Weakened::Above) => Proof::Term(weak("ne_of_gt")),
            None => match linear.kind {
                TermKind::By(proof) => *proof,
                _ => Proof::Term(linear),
            },
        })
    }

    /// A fact an order step adds, from where the checker found it
    /// (`OrderFact`): the term that proves it, and what Lean states it as.
    fn order_fact(
        &self,
        fact: &crate::checker::record::OrderFact,
    ) -> Route<OrderFactTerm> {
        use crate::checker::record::OrderFact;
        let (proof, says, node) = match fact {
            OrderFact::Line(at) => match self.line_says(at) {
                Route::Built((proof, says)) => (proof, says, at.written.clone()),
                Route::Declined(d) => return Route::Declined(d),
            },
            OrderFact::Define(label) => {
                let lines =
                    self.trees.get(label).map(Vec::as_slice).unwrap_or_default();
                let [line] = lines else {
                    return Route::no("a define an order step adds, not one equation");
                };
                let Some(name) = &line.name else {
                    return Route::no(
                        "a define an order step adds, with no name in Lean",
                    );
                };
                let says = match self.line_statement(&line.cited()) {
                    Route::Built(s) => s,
                    Route::Declined(d) => return Route::Declined(d),
                };
                (super::tactics::hyp(name), says, line.node.clone())
            }
            // A define's kind is a line of its letter, `n ∈ ℕ`, proved by
            // the order Lean names beside it (`kinded_witness`).
            OrderFact::Kind {
                define,
                implied,
                written,
            } => {
                let Some([kind]) =
                    self.trees.get(&format!("{define} kind")).map(Vec::as_slice)
                else {
                    return Route::no("a define's kind Lean names no line of");
                };
                let implies = match self.writer.formula(written) {
                    Route::Built(s) => s,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let proof = match self.implied_proof(&kind.cited(), *implied, &implies)
                {
                    Route::Built(proof) => proof,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // Lean states the kind of the letter, as its line does, `0 <
                // n`, where the page's fact is of the define's value.
                match self.line_statement(&kind.cited()) {
                    Route::Built(says) => (proof, says, kind.node.clone()),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            OrderFact::Requires {
                line,
                implied: None,
            } => {
                let Some(step) = self.step_now.get().map(|i| &self.thm.steps[i]) else {
                    return Route::no("a requires line outside a step");
                };
                let name = format!("r{}_{}", step.line, line + 1);
                let Some([said]) = self.trees.get(&name).map(Vec::as_slice) else {
                    return Route::no(
                        "a requires line above, not one sentence in Lean",
                    );
                };
                let says = match self.line_statement(&said.cited()) {
                    Route::Built(s) => s,
                    Route::Declined(d) => return Route::Declined(d),
                };
                (super::tactics::hyp(&name), says, said.node.clone())
            }
            OrderFact::Requires {
                implied: Some(_), ..
            } => {
                return Route::no(
                    "what a requires line above implies, in an order step",
                );
            }
            OrderFact::Member(_) => {
                return Route::no("what the member an order step is read at implies");
            }
        };
        // Linear arithmetic adds relations, not a "for all" of them.
        if matches!(says.kind, super::doc::TermKind::Quantified { .. }) {
            return Route::no("a \"for all\" an order step adds as a whole");
        }
        Route::Built(OrderFactTerm {
            proof,
            says,
            node,
            widens: !matches!(fact, OrderFact::Kind { .. }),
        })
    }

    /// `antisymmetry`: `le_antisymm` of the line that says the claim's left
    /// side is at most its right and the line that says the converse, as
    /// the checker paired them (`CheckedTheorem::antisymmetric`).
    fn antisymmetry_proof(&self, line: usize, node: &Node) -> Route<super::doc::Proof> {
        use super::doc::{LeanType, Proof, Source};
        let Some(rec) = self.rec.antisymmetric.get(&line) else {
            return Route::no("an antisymmetry step the checker paired no lines for");
        };
        let wanted = match self.writer.formula(node) {
            Route::Built(w) => w,
            Route::Declined(d) => return Route::Declined(d),
        };
        let mut proofs = Vec::new();
        for at in [&rec.below, &rec.above] {
            let (proof, says) = match self.line_says(at) {
                Route::Built(found) => found,
                Route::Declined(d) => return Route::Declined(d),
            };
            if super::doc::forms::relation_types_apart(&says, &wanted) {
                return Route::no(
                    "an antisymmetry step's line in another type than its claim",
                );
            }
            proofs.push(proof);
        }
        Route::Built(Proof::Term(Printed::applied(
            "le_antisymm",
            Source::Mathlib,
            proofs,
            LeanType::Prop,
        )))
    }

    /// `instantiate`: the "for all" line at the values given, each guard
    /// proved from where the checker found it supplied (`value_guard`), and
    /// an "if" in it applied where the claim is what it gives.
    fn instantiate(
        &self,
        just: &Justification,
        node: &Node,
        writer: &Writer,
    ) -> Route<super::doc::Proof> {
        let Some(target) = just
            .target
            .as_deref()
            .or(just.refs.first().map(String::as_str))
        else {
            return Route::no("an instantiate of no line");
        };
        let stated = self.stated_claim(just.line, node);
        let claim = match stated {
            Some(printed) => Route::Built(printed),
            None => writer.formula(node),
        };
        // The sentence, or the part of one, of the line the checker found
        // the instance in (`CheckedTheorem::instantiated`).
        let Some(recorded) = self.rec.instantiated.get(&just.line) else {
            return Route::no(format!(
                "an instantiate of {target} the checker read no instance of"
            ));
        };
        let part = match self.line_part(&recorded.at) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A "for all" read at the block's letter, with no values given, is
        // the instance itself; with values, they are given to the reading.
        let at_letter = recorded
            .at
            .sentence
            .is_some_and(|k| k >= self.written_sentences(&recorded.at.line));
        if at_letter && just.values.is_empty() {
            let instance = self.line_statement(&part);
            let page = part.node.clone();
            return Route::Built(self.instance_closed(
                node,
                claim,
                part.proof,
                instance,
                None,
                Some(&page),
                recorded,
            ));
        }
        let part = &part;
        let (line, name) = (&part.node, &part.proof);
        // The values as Lean gives them to the line's letters, each with
        // whether a guard's proof follows it.
        let mut given: Vec<(Printed, bool)> = Vec::new();
        let mut args: Vec<Printed> = Vec::new();
        // The values as the page gives them, each to its letter.
        let mut binding = crate::matching::Binding::new();
        let mut body = line;
        while body.notation() == crate::notations::FOR_ALL {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            // A letter given no value is read at the block's letter of its
            // type the claim writes and the line does not, as the checker
            // reads it.
            let value = match just.values.pairs().find(|(n, _)| *n == &*letter.text) {
                Some((_, given)) => match self.tree(given) {
                    Route::Built(v) => v,
                    Route::Declined(d) => return Route::Declined(d),
                },
                None => {
                    // The names the line writes free: a letter it binds
                    // itself, as the block's may be named, is not one.
                    let own = crate::matching::free_names(
                        line,
                        &self.sources.checked.grammar.binders(),
                    );
                    // A range's letter is an integer.
                    let ty = if set.notation() == crate::notations::INTEGER_RANGE {
                        Some(super::templates::Num::Int)
                    } else {
                        super::expr::system_of(set).map(super::expr::letter_type)
                    };
                    // A set's letter is a member of its kind.
                    let member = writer.members_of(set).map(|m| m.letter());
                    // Where several fit, a letter given to another of the
                    // line's letters, the N of `m := N`, is that one's value
                    // and not this one's.
                    let given: Vec<String> = just
                        .values
                        .pairs()
                        .filter_map(|(_, v)| self.tree(v).built())
                        .flat_map(|v| v.names())
                        .collect();
                    let fits = |n: &String| {
                        let has = writer.letters.get(n.as_str());
                        !own.contains(n)
                            && (ty.is_some_and(|t| has == Some(&LetterType::Number(t)))
                                || (member.is_some() && has == member.as_ref()))
                    };
                    let mut at: Vec<String> =
                        node.names().into_iter().filter(|n| fits(n)).collect();
                    if at.len() > 1 {
                        at.retain(|n| !given.contains(n));
                    }
                    // A claim that is itself a "for all" keeps the letters
                    // given no value: the line is read at those given.
                    let [at] = at.as_slice() else {
                        if node.notation() == crate::notations::FOR_ALL {
                            break;
                        }
                        return Route::no(format!("no value for {}", letter.text));
                    };
                    Node::name(letter.sort.clone(), at)
                }
            };
            binding.insert(
                crate::formula::symbol::Symbol::of(&letter.text),
                value.clone(),
            );
            // A member of a set: the value, and that it is in the set.
            if let Some(members) = writer.members_of(set) {
                match writer.element_term(&value, &members) {
                    Route::Built(p) => {
                        given.push((p.clone(), true));
                        args.push(p);
                    }
                    Route::Declined(d) => return Route::Declined(d),
                }
                args.push(self.value_guard(recorded, &letter.text));
                body = inner;
                continue;
            }
            // A function or map between sets: it, and that it maps the one
            // into the other.
            if let ("functions-from", [from, to]) =
                (&*set.notation_name(), set.children.as_slice())
            {
                match self.function_given(writer, &value, from, to) {
                    Route::Built(p) => {
                        given.push((p.clone(), true));
                        args.push(p);
                    }
                    Route::Declined(d) => return Route::Declined(d),
                }
                args.push(self.value_guard(recorded, &letter.text));
                body = inner;
                continue;
            }
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
                (super::templates::Num::Int, true)
            } else {
                match super::expr::system_of(set) {
                    Some(s) => (
                        super::expr::letter_type(s),
                        !matches!(s, super::expr::System::Type(_)),
                    ),
                    None => {
                        return Route::no("a value of a letter of no number system")
                    }
                }
            };
            match writer.number_fixed(&value, ty) {
                Route::Built(p) => {
                    given.push((p.clone(), guarded));
                    args.push(p);
                    if guarded {
                        args.push(self.value_guard(recorded, &letter.text));
                    }
                }
                Route::Declined(d) => return Route::Declined(d),
            }
            body = inner;
        }
        let taken_off = recorded.conditions.len();
        let instance = match self.writer.formula(line) {
            Route::Built(l) => lean_instance(&l, &given, taken_off),
            Route::Declined(d) => Route::Declined(d),
        };
        // Each condition the checker took off on the way to the claim, from
        // where it found it supplied, as Lean states it at the values.
        for (k, condition) in recorded.conditions.iter().enumerate() {
            let proof = match &instance {
                Route::Built(i) => self.supplied_proof(&condition.by, &i.conditions[k]),
                Route::Declined(_) => None,
            };
            args.push(proof.unwrap_or_else(|| side_term(&[])));
        }
        let instance = instance.map(|i| i.left);
        // What is left of the line once its letters are given and its
        // conditions taken off, at the values, as the step's lines write it.
        let left = (0..taken_off).try_fold(body, |at, _| {
            node_consequent(at).filter(|_| at.notation() != BICONDITIONAL)
        });
        let written = left.and_then(|at| self.written_at_values(at, &binding));
        let page = left.map(|at| self.at_values(at, &binding));
        let applied = Printed {
            kind: super::doc::TermKind::App {
                head: Box::new(name.clone()),
                args: args.into_iter().map(super::doc::Arg::Explicit).collect(),
                explicit: false,
            },
            ty: Some(super::doc::LeanType::Prop),
        };
        Route::Built(self.instance_closed(
            node,
            claim,
            super::tactics::bracket(applied),
            instance,
            written,
            page.as_ref(),
            recorded,
        ))
    }

    /// The proof of the claim `node`, which Lean states as `claim`, from
    /// `proof`, an instance of a line that
    /// Lean states as `instance`, by how the checker met the instance with
    /// the claim (`Instantiated::meeting`). Where Lean's statements of the
    /// two differ otherwise, the instance, turned where the checker turned
    /// it, is taken down to the claim's field where it is in a wider one,
    /// `parley_rat_of_real` of ℝ for a claim in ℚ and `parley_of_complex` of
    /// ℂ; and otherwise reaches the claim by the closer
    /// whose Lean fact holds of the two, the ways tried in order where none
    /// does (`close`). Before those rows, the instance as the step's lines
    /// write it at the values, `written`, read from the line and met with
    /// the claim, as a citation's is (`read_in_spelling`). Before that, a
    /// power the one writes as an integer power and the other to its
    /// exponent's `toNat` is converted as a citation's is (`forms_converted`),
    /// each exponent's fact from the record, `page` being the instance as a
    /// page formula at its values.
    #[allow(clippy::too_many_arguments)]
    fn instance_closed(
        &self,
        node: &Node,
        claim: Route<Printed>,
        proof: Printed,
        instance: Route<Printed>,
        written: Option<Printed>,
        page: Option<&Node>,
        recorded: &crate::checker::record::Instantiated,
    ) -> super::doc::Proof {
        use super::doc::forms;
        let lean = match (&instance, claim.clone()) {
            (Route::Built(says), Route::Built(wanted)) => Some((says.clone(), wanted)),
            _ => None,
        };
        // An instance Lean takes as the claim, once turned where the checker
        // turned it: a function applied worked out, a bound letter renamed, a
        // `set` letter read as its value, the types the same
        // (`forms::one_term_once_set`). `exact` checks just that.
        if let Some((says, wanted)) = &lean {
            let turned = recorded.meeting.turned;
            let facing = match turned {
                true => forms::turned_statement(says),
                false => says.clone(),
            };
            if forms::one_term_once_set(&facing, wanted, &self.set_values()) {
                return super::doc::Proof::By(Tactic::Exact(faced(
                    proof,
                    facing_of_turned(turned),
                )));
            }
        }
        // The field the instance is worked in beyond the claim's, ℝ for a
        // claim in ℚ, taken down by the writer's conversion (`read_down`).
        let down = lean
            .as_ref()
            .and_then(|(says, wanted)| read_down(says, wanted));
        let met = match (instance, claim) {
            // Lean's statement of the instance is the claim's as Lean
            // writes both, once turned where the checker turned it, or
            // apart only in casts the writer placed; or the checker dropped
            // identity elements, which `simpa only` takes. Any other
            // difference is in the types Lean gives the line's letters, ℝ
            // for a claim in ℚ, which the writer does not name.
            (Route::Built(says), Route::Built(wanted)) => {
                let met = &recorded.meeting;
                let lean_says = match met.turned {
                    true => forms::turned_statement(&says),
                    false => says.clone(),
                };
                let values = self.set_values();
                // Alike as written is alike in one type: `1 ≤ 1/2` in ℝ and
                // in ℚ are written alike and are two statements.
                let two_types = forms::relation_types_apart(&lean_says, &wanted);
                let lean_alike = (forms::written_alike(&lean_says, &wanted)
                    && !two_types)
                    || forms::casts_differ(&lean_says, &wanted, &values).is_some();
                match lean_alike || !met.identities.is_empty() {
                    true => self.met_proof(proof.clone(), &says, &wanted, met),
                    false => None,
                }
            }
            _ => None,
        };
        if let Some(proved) = met {
            return super::doc::Proof::By(proved.closer());
        }
        if let (Some((says, wanted)), Some(page)) = (&lean, page) {
            if let Some(converted) = self.powers_converted_at(
                &[node, page],
                says,
                wanted,
                &proof,
                recorded.meeting.turned,
            ) {
                return converted;
            }
        }
        let read = match (&written, &lean) {
            (Some(written), Some((says, wanted))) => {
                let said = match one_statement(written, says) {
                    true => written,
                    false => says,
                };
                let claim = StepClaim {
                    printed: wanted,
                    stated: false,
                };
                self.read_in_spelling(None, &proof, said, written, claim)
            }
            _ => None,
        };
        if let Some(read) = read {
            return read;
        }
        use super::tactics as t;
        // The instance turned round where the checker turned it.
        let proof = faced(proof, facing_of_turned(recorded.meeting.turned));
        // An instance in a wider field than the claim's, taken down to it by
        // the writer's own conversion.
        if let Some(bridge) = down {
            return super::doc::Proof::By(t::on_h(
                &proof,
                vec![t::bridge(bridge, vec![TacticArg::Term(t::hyp("h"))])],
            ));
        }
        // The two in one type, met by the checker: each closer where its
        // Lean fact holds of Lean's statements of them. An equation of
        // numbers whose casts `push_cast` all moves (the cast table) is the
        // instance once pushed in and put by the ring's laws,
        // `linear_combination`, whose `parley_norm` checks
        // `push_cast; ring1`; an order with the same casts as the instance
        // is it over the same atoms, `linarith`. Any other keeps the ways it
        // tries.
        let Some((says, wanted)) = lean else {
            return close(ListReason::CitedUnstated, &self.writer, node, proof);
        };
        let says = match recorded.meeting.turned {
            true => super::doc::forms::turned_statement(&says),
            false => says,
        };
        let of_numbers = node.children.iter().all(|c| c.sort.is("number"));
        let pushed = super::casts::push_cast_moves_all_in_sides(&says)
            && super::casts::push_cast_moves_all_in_sides(&wanted);
        let same_casts = cast_texts(&says) == cast_texts(&wanted);
        let atoms = same_ring_atoms(&says, &wanted, &self.set_values());
        super::doc::Proof::By(match node.notation() {
            EQUALITY if of_numbers && pushed && atoms => t::linear_combination(proof),
            ORDER if same_casts && atoms => {
                t::call("linarith", vec![t::rules(vec![proof])])
            }
            _ => {
                let why = apart(
                    node,
                    &says,
                    &wanted,
                    &self.set_values(),
                    Some(Facing::Straight),
                );
                return close(why, &self.writer, node, proof);
            }
        })
    }

    /// The defines among the lines a step cites, each as its equation says
    /// it: the checker reads such a step with them written out.
    fn cited_defines(&self, refs: &[String]) -> Vec<CitedDefine> {
        let mut out: Vec<CitedDefine> = refs
            .iter()
            .filter(|r| self.thm.defines.iter().any(|d| d.label == **r))
            .filter(|r| !self.witnessed.contains(*r))
            .flat_map(|r| self.trees.get(r).into_iter().flatten())
            .filter_map(|line| match line.node.children.as_slice() {
                [name, value] if line.node.notation() == EQUALITY && name.is_name() => {
                    Some(CitedDefine {
                        name: name.clone(),
                        value: value.clone(),
                        proof: line.name.clone()?,
                        param: None,
                    })
                }
                _ => None,
            })
            .collect();
        out.extend(refs.iter().filter_map(|r| self.cited_function_define(r)));
        out
    }

    /// A define of a function of one argument a step cites by its label,
    /// q(j) = F(j)²: its name, its body, its argument and the name of the
    /// line Lean's `set` gives it; None for any other reference.
    fn cited_function_define(&self, label: &str) -> Option<CitedDefine> {
        let line = self
            .thm
            .defines
            .iter()
            .find(|d| d.label == label && d.line > self.thm.conclusion_line)?;
        let Route::Built(crate::corpus::DefineParts::One(def)) =
            crate::corpus::define_parts(&line.text)
        else {
            return None;
        };
        let [param] = def.params.as_slice() else {
            return None;
        };
        let bodies: Vec<&Node> = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == line.line)
            .map(|(_, node)| node)
            .filter(|n| n.notation() != crate::notations::NUMBER_SYSTEMS)
            .filter(|n| !(n.is_name() && *n.text == *param.name))
            .collect();
        let [body] = bodies.as_slice() else {
            return None;
        };
        let proof = self.named.get(label)?.first()?.clone();
        Some(CitedDefine {
            name: Node::name(crate::formula::Sort::none(), &def.name),
            value: (*body).clone(),
            proof,
            param: Some(param.name.clone()),
        })
    }

    /// A line with a cited define put in: its name for its value, or each
    /// application q(a) of a function's for its body at a.
    fn put_define(&self, node: &Node, d: &CitedDefine) -> Node {
        let Some(param) = &d.param else {
            return put_for(node, &d.name, &d.value);
        };
        if let (crate::notations::APPLICATION, [f, a]) =
            (node.notation(), node.children.as_slice())
        {
            if f.is_name() && f.text == d.name.text {
                let a = self.put_define(a, d);
                let put = crate::matching::Binding::from([(
                    crate::formula::symbol::Symbol::of(param),
                    a,
                )]);
                return crate::matching::substitute_apart_by(
                    &d.value,
                    &put,
                    &self.sources.checked.grammar.binders(),
                );
            }
        }
        if node.children.is_empty() {
            return node.clone();
        }
        node.with_children(
            node.children
                .iter()
                .map(|c| self.put_define(c, d))
                .collect(),
        )
    }

    /// `substitute`: the claim is a line, or the left side of a calculation's
    /// link, with a term put for another by an equation, which a line says
    /// or arithmetic works out.
    /// A substitution as the checker recorded it (`CheckedTheorem::
    /// substituted`): what the equation is put into, written with each place
    /// it is put at as one fresh letter of the type the term put for has
    /// there, the motive; and the equation's proof, turned where the record
    /// puts its left side for its right. Put into a line, `Eq.subst` along
    /// the motive takes the line to the claim; put into a side of the claim
    /// `t = t′`, `congrArg` of the motive is the claim, turned where the side
    /// is its right. Either is closed by `exact_mod_cast`, as a numeral put
    /// where the claim writes it in a wider type is written with its cast.
    /// Declined where the record has none, or a place of no number type.
    /// A row of a `substitute` step (`SubstitutedInto::RowAbove`) is put
    /// into the row above as into a line, its change proved by its reason;
    /// a step's own equation from no line, by its proof (`GivenEquation`).
    fn substituted_by_record(
        &self,
        line: usize,
        sentence: Option<usize>,
        claim: &Node,
        row: Option<&GivenEquation>,
    ) -> Route<super::doc::Proof> {
        use super::doc::{LeanType, Proof};
        use super::tactics as t;
        use crate::checker::record::SubstitutedInto;
        let found = self.substitution_record(
            line,
            sentence,
            row.is_some_and(|r| r.above.is_some()),
        );
        let Some(rec) = found else {
            return Route::no("a substitution the checker recorded no way of");
        };
        // Put at no place: the line is the claim once the theorem's outside
        // defines are written out, as Lean has both (`Substituted::put`).
        if rec.put.places.is_empty() {
            let SubstitutedInto::Line(at) = &rec.into else {
                return Route::no("a putting at no place into no line");
            };
            let (proof, says) = match self.line_says(at) {
                Route::Built(both) => both,
                Route::Declined(d) => return Route::Declined(d),
            };
            let Some(wanted) = self.claim_as_stated(line, claim) else {
                return Route::no("a claim Lean states no form of");
            };
            return match self.proof_meeting(proof, &says, &wanted) {
                Some(proved) => Route::Built(Proof::By(Tactic::Exact(proved.term()))),
                None => Route::no(
                    "a line put at no place that Lean states otherwise than the claim",
                ),
            };
        }
        let [left, right] = rec.equation.children.as_slice() else {
            return Route::no("a recorded equation of no two sides");
        };
        let (was, now) = match rec.put.turned {
            false => (left, right),
            true => (right, left),
        };
        // Which way the equation's proof is used: as the record puts it, the
        // side put for on the left.
        let put_facing = |as_said: bool| match as_said != rec.put.turned {
            true => Facing::Straight,
            false => Facing::Turned,
        };
        // The equation's proof: the line's part the record names, turned
        // where the line says it the other way round; a row's change, which
        // its reason proves as the record writes it.
        let (part, equation) = match (&rec.from, row) {
            (Some(from), _) => {
                let part = match self.line_part(from) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // Which way round the line says the recorded equation
                // (`Substituted::line_facing`).
                let as_said = rec.line_facing != Some(Facing::Turned);
                let equation = faced(part.proof.clone(), put_facing(as_said));
                (part, equation)
            }
            (None, Some(row)) => {
                let equation = faced(row.change.proof.clone(), put_facing(true));
                (row.change.clone(), equation)
            }
            (None, None) => {
                return Route::no("an equation the record takes from no line")
            }
        };
        // A side holding a cast of a `toNat`, `((2^p − 1).toNat : ℤ)`, which
        // `push_cast` moves only knowing the term is not negative. A `toNat`
        // with no cast over it, an exponent's `2 ^ m.toNat`, is a term like
        // any other.
        let cast_to_nat = [left, right].iter().any(|side| {
            self.writer
                .formula(side)
                .built()
                .or_else(|| {
                    self.writer.number(side, super::templates::Num::Int).built()
                })
                .is_some_and(|p| casts_a_to_nat(&p))
        });
        if cast_to_nat {
            return Route::no("an equation with a side holding a cast of a toNat");
        }
        // A place that is an exponent is written by what the page says of
        // its term, `(−1)^m.toNat` of m said a whole number. Where the page
        // says so of the term put for and of the term put, and neither is a
        // natural-number letter written as it stands, the motive's letter is
        // said whole as well (`Writer::wholes`), and its exponent is written
        // as theirs are; any other exponent declines.
        let exponent = rec
            .put
            .places
            .iter()
            .any(|p| place_is_exponent(&rec.start, p));
        use super::expr::NaturalForm;
        let form = |n: &Node| self.writer.natural_form(n);
        // An equation of natural numbers put at exponents, φ(n) = |S| put in
        // a^φ(n): Lean's exponent is of ℕ, so the equation is put there in
        // ℕ, stated so first (`e_nat`), and the motive's letter is of ℕ.
        let natural_exponent = exponent
            && rec
                .put
                .places
                .iter()
                .all(|p| place_is_exponent(&rec.start, p))
            && form(was) == NaturalForm::AsItIs
            && form(now) == NaturalForm::AsItIs;
        // Else the motive's letter is written as Lean writes the exponents
        // at both its values (`Writer::natural_form`): as its `toNat` where
        // both are, a numeral put counting so, since its `toNat` works out
        // (`Int.reduceToNat`); else an integer, its power an integer one,
        // converted to the claim's after (`int_exponent`,
        // `powers_converted_at`), each exponent's fact from the record. A
        // difference put for a whole letter, p − 1 for k, leaves it an
        // integer.
        let now_to_nat = form(now) == NaturalForm::ToNat
            || now.notation() == crate::notations::NUMERAL;
        let whole_was = exponent
            && !natural_exponent
            && form(was) == NaturalForm::ToNat
            && now_to_nat;
        let int_exponent = exponent && !natural_exponent && !whole_was;
        let whole_letter = |w: &mut Writer, letter: &str| {
            if whole_was {
                w.wholes
                    .insert(letter.to_string(), super::expr::System::NonNegative);
            }
        };
        // The motive's letter, of the type the equation's proof states it
        // in, the claim's where the line is widened to it, else the type
        // the term put for has where it stands; and fresh to what it is put
        // into.
        let stated = self
            .line_statement(&part)
            .built()
            .as_ref()
            .and_then(super::doc::forms::relation_type)
            .and_then(|t| match t {
                LeanType::Num(n) => Some(n),
                _ => None,
            });
        let ty = match (stated, self.writer.carrier(was)) {
            (Some(n), _) => n,
            (None, Route::Built(n)) => n,
            (None, Route::Declined(d)) => return Route::Declined(d),
        };
        let (ty, equation, in_nat) = match natural_exponent {
            false => (ty, equation, None),
            true => match self.nat_equation(was, now, &equation) {
                Route::Built(have) => {
                    (super::templates::Num::Nat, t::hyp("e_nat"), Some(have))
                }
                Route::Declined(d) => return Route::Declined(d),
            },
        };
        // What every way out states before its proof: `e_nat`, and `e_w`
        // where the equation is widened (`haves_then`).
        let mut haves: Vec<Tactic> = in_nat.into_iter().collect();
        let taken = rec.start.names();
        let Some(letter) = ["t", "u", "w", "s", "r"].into_iter().find(|l| {
            !taken.iter().any(|n| n == l) && !self.writer.letters.contains_key(*l)
        }) else {
            return Route::no("no fresh letter for a substitution's motive");
        };
        let marked = mark_places(
            &rec.start,
            &rec.put.places,
            &Node::name(was.sort.clone(), letter),
        );
        let mut letters = self.writer.letters.clone();
        letters.insert(letter.to_string(), LetterType::Number(ty));
        let mut inner = self.writer.with_letters(letters);
        whole_letter(&mut inner, letter);
        // The motive's letter standing in a slot of whole numbers in a wider
        // type, a range's member, is written as the whole number it is
        // (`Writer::wide_in_slot`), `∃ m : ℤ, (m : ℚ) = t ∧ P m`: put into a
        // line Lean writes so too, the slot's whole numbers, else declined.
        let slot = self.writer.wide_in_slot(&rec.start).map(|(_, whole)| whole);
        if inner.wide_in_slot(&marked).is_some() && slot.is_none() {
            return Route::no("a motive whose letter stands for a whole number");
        }
        // Stated by a `have` first: `exact_mod_cast` elaborates its term
        // with no type for a numeral exponent to default to, `t ^ 3` as an
        // integer power. The casts of both are pushed down to the letters
        // first, where the motive's `(a : ℚ) * (t : ℚ)` and the line's
        // `↑(a * b)` meet; lifted instead, a division of casts is read one
        // way on one side and another on the other. A claim that pushing
        // alone works out, `True`, is closed on the way.
        // A putting that makes the claim only turned round, or with a listed
        // set's members in another order (`Substituted::meeting`), is no
        // motive's: the claim is not the line with the equation put in.
        let m = &rec.meeting;
        if m.turned || m.permuted || m.renamed || m.respelled {
            return Route::no("a putting that meets the claim other than as written");
        }
        // The identity elements the putting leaves and the claim drops, as
        // the record names them, `1·x` as `x` by `one_mul`.
        let dropped: Option<Vec<&'static str>> =
            m.identities.iter().map(identity_lemma).collect();
        let Some(dropped) = dropped else {
            return Route::no("an identity element dropped that no lemma names");
        };
        // Dropped with the casts pushed, as rewrites `push_cast` takes beside
        // its own: a numeral put where the claim has it in a wider type is
        // cast, `((1 : ℤ) : ℝ) * x`, which `one_mul` meets only as `1 * x`,
        // and `push_cast` may drop the identity itself.
        let close = |term: Printed| {
            let pushed = match dropped.is_empty() {
                true => t::push_cast(Some(t::at_h(true))),
                false => t::call(
                    "push_cast",
                    vec![
                        t::rules(dropped.iter().map(|l| t::lemma(l)).collect()),
                        t::at_h(true),
                    ],
                ),
            };
            Proof::By(t::on_h(
                &term,
                vec![
                    pushed,
                    Tactic::AllGoals(Box::new(t::exact_mod_cast(t::hyp("h")))),
                ],
            ))
        };
        let in_arithmetic =
            |path: &Vec<usize>| self.place_in_formula_type(&rec.start, path);
        match &rec.into {
            SubstitutedInto::Line(_) | SubstitutedInto::RowAbove => {
                // A fact the line implies, `k ≤ n` of `k ∈ {1, …, n}`, has
                // no name of its own: the line's proves what it writes.
                if let SubstitutedInto::Line(at) = &rec.into {
                    if at.implied.is_some() {
                        return Route::no("a substitution into a fact a line implies");
                    }
                }
                let into = match (&rec.into, row) {
                    (SubstitutedInto::Line(at), _) => match self.line_part(at) {
                        Route::Built(p) => p,
                        Route::Declined(d) => return Route::Declined(d),
                    },
                    (
                        _,
                        Some(GivenEquation {
                            above: Some(above), ..
                        }),
                    ) => above.clone(),
                    _ => return Route::no("a row's substitution with no row above"),
                };
                // The type the line writes the term put for in. A term of
                // the line's arithmetic, a side or a part of a sum, product or
                // power's base, is written in the line's type, `2^k · 2` in a
                // line of ℚ; any other, a function's argument, in its own,
                // `factorial (4 − 2)` in ℤ, which is the equation's.
                let line_type = match self
                    .line_statement(&into)
                    .built()
                    .as_ref()
                    .and_then(super::doc::forms::relation_type)
                {
                    Some(LeanType::Num(n)) => Some(n),
                    _ => None,
                };
                // Each place's type: the line's for one in its arithmetic,
                // its own for any other; places of one type take one motive.
                let types: std::collections::BTreeSet<super::templates::Num> = rec
                    .put
                    .places
                    .iter()
                    .map(|p| match in_arithmetic(p) {
                        true => line_type.unwrap_or(ty),
                        false => ty,
                    })
                    .collect();
                let place_type = match types.into_iter().collect::<Vec<_>>().as_slice()
                {
                    [one] => *one,
                    // Places of two types, a function's argument in the
                    // equation's own and a term of the line's arithmetic in its
                    // wider one: the equation put in twice, at the argument as
                    // it is, then widened (`e_w`) at the arithmetic of what
                    // that makes.
                    [own_type, wide] if *own_type == ty && Some(*wide) == line_type => {
                        if int_exponent || slot.is_some() {
                            return Route::no(
                                "a substitution at places written in different types",
                            );
                        }
                        let wide = *wide;
                        let (own, arith): (Vec<Vec<usize>>, Vec<Vec<usize>>) = rec
                            .put
                            .places
                            .iter()
                            .cloned()
                            .partition(|p| !in_arithmetic(p));
                        let named = Node::name(was.sort.clone(), letter);
                        let stage =
                            |start: &Node,
                             places: &[Vec<usize>],
                             at: super::templates::Num| {
                                let mut letters = self.writer.letters.clone();
                                letters
                                    .insert(letter.to_string(), LetterType::Number(at));
                                self.writer
                                    .with_letters(letters)
                                    .formula(&mark_places(start, places, &named))
                                    .map(|body| lambda(letter, LeanType::Num(at), body))
                            };
                        let first_motive = match stage(&rec.start, &own, ty) {
                            Route::Built(m) => m,
                            Route::Declined(d) => return Route::Declined(d),
                        };
                        let between =
                            crate::matching::put_at_places(&rec.start, &own, now);
                        let second_motive = match stage(&between, &arith, wide) {
                            Route::Built(m) => m,
                            Route::Declined(d) => return Route::Declined(d),
                        };
                        match self.equation_widened(rec, was, now, ty, wide, &equation)
                        {
                            Route::Built(have) => haves.push(have),
                            Route::Declined(d) => return Route::Declined(d),
                        }
                        let subst = |motive: Printed, eq: Printed, line: Printed| {
                            applied(
                                "Eq.subst",
                                vec![
                                    super::doc::Arg::Named {
                                        name: "motive".to_string(),
                                        value: motive,
                                    },
                                    super::doc::Arg::Explicit(eq),
                                    super::doc::Arg::Explicit(line),
                                ],
                            )
                        };
                        let first = subst(first_motive, equation, into.proof);
                        let second = subst(second_motive, t::hyp("e_w"), first);
                        return Route::Built(haves_then(haves, close(second)));
                    }
                    _ => {
                        return Route::no(
                            "a substitution at places written in different types",
                        )
                    }
                };
                // A line in a narrower type than the equation, `F (j + 1) =
                // G j` of ℤ for an equation of ℝ, holds the term in no type
                // the equation has; in a wider, the equation is stated in the
                // line's type first, as `widened` states it.
                if place_type < ty {
                    return Route::no(
                        "a line in a narrower type than the equation put into it",
                    );
                }
                let equation = match place_type > ty {
                    false => equation,
                    true => {
                        match self
                            .equation_widened(rec, was, now, ty, place_type, &equation)
                        {
                            Route::Built(have) => haves.push(have),
                            Route::Declined(d) => return Route::Declined(d),
                        }
                        t::hyp("e_w")
                    }
                };
                let mut letters = self.writer.letters.clone();
                letters.insert(letter.to_string(), LetterType::Number(place_type));
                let mut inner = self.writer.with_letters(letters);
                whole_letter(&mut inner, letter);
                let body = match inner.formula(&marked) {
                    Route::Built(b) => b,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // The claim is the motive at the new value only where the two
                // are written in one form: a line of a real term written as
                // the whole number it is, `∃ m : ℤ, (m : ℝ) = t ∧ …`, is not
                // the claim of an integer, `f k ∈ …`.
                // Nor the line it is put into: the motive at the old value
                // is that line.
                // A range member Lean computes wider, said as the integer that
                // is it (`wide_range_member`), made from a line that the
                // integer the equation puts for is in the range, at that
                // member alone: that integer, the equation and the line.
                if wide_range_member(&self.writer, claim) && rec.put.places == [vec![0]]
                {
                    return Route::Built(haves_then(
                        haves,
                        Proof::By(Tactic::Exact(range_member_made(
                            equation, into.proof,
                        ))),
                    ));
                }
                let claimed = self.claim_as_stated(line, claim);
                let line_said = self.line_statement(&into).built();
                let in_form = |said: &Option<Printed>| {
                    said.as_ref().is_some_and(|c| {
                        std::mem::discriminant(&c.kind)
                            == std::mem::discriminant(&body.kind)
                    })
                };
                // A line of the whole number a term is, `∃ m : ℤ, (m : ℚ) =
                // 2 ^ p ∧ Even m`, put into, where the claim says it of the
                // whole number the new term is, `Even (3 ^ q.toNat)`: what
                // the motive gives is said of that number,
                // `parley_witness_at`.
                let witnessed = match (slot, in_form(&line_said), in_form(&claimed)) {
                    (_, true, true) => None,
                    (Some(whole), true, false) => Some(whole),
                    _ => return Route::no(
                        "a motive written in another form than the claim or the line",
                    ),
                };
                let motive = lambda(letter, LeanType::Num(place_type), body.clone());
                let put_in = applied(
                    "Eq.subst",
                    vec![
                        super::doc::Arg::Named {
                            name: "motive".to_string(),
                            value: motive,
                        },
                        super::doc::Arg::Explicit(equation),
                        super::doc::Arg::Explicit(into.proof),
                    ],
                );
                if let Some(whole) = witnessed {
                    if int_exponent {
                        return Route::no(
                            "a substitution into an exponent of a whole number's line",
                        );
                    }
                    let w = match inner.number_fixed(now, whole) {
                        Route::Built(w) => w,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    let lemma = match whole {
                        super::templates::Num::Nat => "parley_witness_at_nat",
                        _ => "parley_witness_at",
                    };
                    // That the witness is the new term: by its casts, or, a
                    // whole number the step names (`named_specs`), by the
                    // equation that names it.
                    let shows = match w.names("Classical.choose")
                        && !self.named_specs.is_empty()
                    {
                        false => t::call("norm_cast", vec![]),
                        true => Tactic::Seq(vec![
                            t::push_cast(None),
                            t::simp_only(
                                false,
                                None,
                                self.named_specs
                                    .iter()
                                    .cloned()
                                    .map(t::forwards)
                                    .collect(),
                                None,
                            ),
                        ]),
                    };
                    let said = Printed {
                        kind: super::doc::TermKind::App {
                            head: Box::new(t::bridge_lemma(
                                lemma,
                                BridgeModule::PowerTactics,
                            )),
                            args: vec![
                                super::doc::Arg::Explicit(put_in),
                                super::doc::Arg::Explicit(w),
                                super::doc::Arg::Explicit(t::by_term(Proof::By(shows))),
                            ],
                            explicit: false,
                        },
                        ty: Some(LeanType::Prop),
                    };
                    return Route::Built(haves_then(
                        haves,
                        Proof::By(Tactic::Exact(said)),
                    ));
                }
                let closed = match int_exponent {
                    false => close(put_in),
                    // The motive at the new term, its power an integer one,
                    // converted to the claim's natural power, the exponent's
                    // fact from the record.
                    true => {
                        let now_written = match inner.number_fixed(now, place_type) {
                            Route::Built(p) => p,
                            Route::Declined(d) => return Route::Declined(d),
                        };
                        let given = std::collections::BTreeMap::from([(
                            super::names::letter(letter),
                            now_written,
                        )]);
                        let result = body.substituted(&given);
                        let met = claimed.as_ref().map(|c| {
                            self.powers_met(
                                &[claim, &rec.start, was, now],
                                &result,
                                c,
                                &put_in,
                                false,
                            )
                        });
                        match met {
                            Some(PowersMet::Converted(proof)) => *proof,
                            // Nothing left to convert: closed as any other.
                            Some(PowersMet::Alike) => close(put_in),
                            _ => return Route::no(
                                "a substitution into an exponent of no term said whole",
                            ),
                        }
                    }
                };
                Route::Built(haves_then(haves, closed))
            }
            // Into an exponent of a side whose term put for is not said whole:
            // the motive's letter an integer, its power an integer one, in
            // the calculation's field, and what `congrArg` gives converted
            // to the claim's natural powers, each exponent's fact from the
            // record (`powers_converted_at`).
            SubstitutedInto::ClaimSide(side) if int_exponent => {
                use super::doc::Op;
                use super::templates::Num;
                let at = match self.writer.carrier(&rec.start) {
                    Route::Built(n) => {
                        n.max(ty).max(self.worked_in.get().unwrap_or(Num::Int))
                    }
                    Route::Declined(d) => return Route::Declined(d),
                };
                // An integer power is a field's.
                if !whole_was && at < Num::Rat {
                    return Route::no(
                        "a substitution into an exponent of no term said whole",
                    );
                }
                let body = match inner.number(&marked, at) {
                    Route::Built(b) => b,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // Told its type where nothing in it fixes one, numerals and
                // the motive's letter alone, as a calculation's first term is.
                let body = match inner.pinned(&marked) {
                    true => body,
                    false => Printed::cast(t::bracket(body), inner.num_type(at)),
                };
                let (Route::Built(was_written), Route::Built(now_written)) =
                    (inner.number_fixed(was, ty), inner.number_fixed(now, ty))
                else {
                    return Route::no(
                        "a substitution into an exponent of no term said whole",
                    );
                };
                let at_value = |v: Printed| {
                    body.substituted(&std::collections::BTreeMap::from([(
                        super::names::letter(letter),
                        v,
                    )]))
                };
                let (before, after) = (at_value(was_written), at_value(now_written));
                let motive = lambda(letter, LeanType::Num(ty), body.clone());
                let made = applied(
                    "congrArg",
                    vec![
                        super::doc::Arg::Explicit(motive),
                        super::doc::Arg::Explicit(equation),
                    ],
                );
                let (made, result) = match side {
                    0 => (
                        made,
                        Printed::infix(Op::EQUALS, before, after, LeanType::Prop),
                    ),
                    _ => (
                        t::symm(t::bracket(made)),
                        Printed::infix(Op::EQUALS, after, before, LeanType::Prop),
                    ),
                };
                let met = self.claim_as_stated(line, claim).map(|c| {
                    self.powers_met(
                        &[claim, &rec.start, was, now],
                        &result,
                        &c,
                        &made,
                        false,
                    )
                });
                match met {
                    Some(PowersMet::Converted(proof)) => {
                        Route::Built(haves_then(haves, *proof))
                    }
                    // Nothing left to convert: closed as any other.
                    Some(PowersMet::Alike) => {
                        Route::Built(haves_then(haves, close(made)))
                    }
                    _ => Route::no(
                        "a substitution into an exponent of no term said whole",
                    ),
                }
            }
            SubstitutedInto::ClaimSide(side) => {
                // Written in the wider of the claim side's type and the
                // equation's. An equation in a narrower type put only at
                // places of the side's arithmetic is stated in the wider
                // first, as `widened` states it, and the motive's letter is of
                // the wider: cast inside the motive, it would be pushed onto
                // each division, which `push_cast` spells as `Rat.divInt` on
                // one side and not the other. At a place written in its own
                // type, an index or an exponent, the letter keeps the
                // equation's, and an equation of rationals is not put into a
                // wider field so.
                let at = match self.writer.carrier(&rec.start) {
                    Route::Built(n) => n.max(ty),
                    Route::Declined(d) => return Route::Declined(d),
                };
                let arithmetic = rec.put.places.iter().all(in_arithmetic);
                if !arithmetic && ty == super::templates::Num::Rat && at > ty {
                    return Route::no(
                        "an equation of rationals put into a wider field",
                    );
                }
                let letter_ty = match arithmetic {
                    true => at,
                    false => ty,
                };
                let equation = match at > ty && arithmetic {
                    false => equation,
                    true => {
                        match self.equation_widened(rec, was, now, ty, at, &equation) {
                            Route::Built(have) => haves.push(have),
                            Route::Declined(d) => return Route::Declined(d),
                        }
                        t::hyp("e_w")
                    }
                };
                let mut letters = self.writer.letters.clone();
                letters.insert(letter.to_string(), LetterType::Number(letter_ty));
                let mut wide = self.writer.with_letters(letters);
                whole_letter(&mut wide, letter);
                let body = match wide.number(&marked, at) {
                    Route::Built(b) => b,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let motive = lambda(letter, LeanType::Num(letter_ty), body);
                let made = applied(
                    "congrArg",
                    vec![
                        super::doc::Arg::Explicit(motive),
                        super::doc::Arg::Explicit(equation),
                    ],
                );
                let closed = close(match side {
                    0 => made,
                    _ => t::symm(t::bracket(made)),
                });
                Route::Built(haves_then(haves, closed))
            }
        }
    }

    fn substitute(
        &self,
        just: &Justification,
        k: usize,
        claim: &Node,
        writer: &Writer,
    ) -> Route<super::doc::Proof> {
        use super::doc::Proof;
        use super::tactics as t;
        // As the checker recorded it, where it did; an equation from no line
        // by its own proof (`equation_given`).
        let given = self.equation_given(just);
        if let Route::Built(proof) = self.substituted_by_record(
            just.line,
            Some(k),
            claim,
            given.as_ref().map(|(_, g)| g),
        ) {
            return Route::Built(match given.and_then(|(have, _)| have) {
                Some(have) => haves_then(vec![have], proof),
                None => proof,
            });
        }
        if !just.rows.is_empty() {
            return self.substitute_rows(just, writer);
        }
        // Substituting from a function the header lets by its value: its
        // equation for every x, put in where f is applied.
        if let Some(crate::corpus::skeleton::Source::At(place)) = &just.source {
            if let Some(hyp) = self.header_function_named(place.named()) {
                let everywhere = TacticArg::At(vec![super::doc::Location::Everywhere]);
                return Route::Built(Proof::By(Tactic::Seq(vec![
                    t::try_(t::simp_only(
                        false,
                        None,
                        vec![t::forwards(t::hyp(&hyp))],
                        Some(everywhere),
                    )),
                    t::first(
                        ListReason::HeaderFunction,
                        vec![
                            t::call("done", vec![]),
                            t::bridge(BridgeTactic::Side, vec![]),
                        ],
                    ),
                ])));
            }
        }
        let mut haves = Vec::new();
        // The equation's own name, where it is widened to the claim's type.
        let mut stated: Option<Printed> = None;
        // The equation put in, as a tree.
        let mut put: Option<Node> = None;
        let equation = match (&just.source, &just.equation) {
            (Some(crate::corpus::skeleton::Source::At(place)), written) => {
                // Of a line saying several things, the equation the step
                // writes, as Lean writes both; else the one that turns the
                // claim's left side into its right, as a calculation's row
                // "= 0² + 0²  substitute D1" puts B = 0 of "A = 0 and B = 0";
                // else its first equation.
                let wanted = written
                    .as_ref()
                    .and_then(|w| self.tree(w).built())
                    .and_then(|n| self.writer.formula(&n).built())
                    .map(|p| p.untyped());
                let parts = self.cited_parts(&[place.named().to_string()]);
                let grammar = &self.sources.checked.grammar;
                // Where the checker recorded the substitution, the
                // equation is the part of the line it found
                // (`Substituted::from`).
                let recorded = self
                    .rec
                    .substituted
                    .get(&just.line)
                    .and_then(|r| r.from.as_ref())
                    .and_then(|at| self.line_part(at).built());
                let chosen = recorded
                    .as_ref()
                    .or_else(|| {
                        parts
                            .iter()
                            .find(|c| {
                                wanted.is_some()
                                    && self
                                        .line_statement(c)
                                        .built()
                                        .map(|p| p.untyped())
                                        == wanted
                            })
                            .or_else(|| {
                                (claim.notation() == crate::notations::EQUALITY)
                                    .then(|| {
                                        parts.iter().find(|c| {
                                            c.node.notation()
                                                == crate::notations::EQUALITY
                                                && makes_claim(&c.node, claim, grammar)
                                        })
                                    })
                                    .flatten()
                            })
                            .or_else(|| {
                                parts.iter().find(|c| {
                                    c.node.notation() == crate::notations::EQUALITY
                                })
                            })
                            .or(parts.first())
                    })
                    .map(|c| (c.node.clone(), c.proof.clone()));
                // Put into a line Lean's types give, `⌊A⌋ ∈ ℤ`, the claim is
                // a membership the equation shows.
                if let Some((line, name)) = &chosen {
                    if let Some(proof) = member_by_equation(
                        &self.writer,
                        line,
                        name,
                        claim,
                        self.sources.ctx,
                    ) {
                        return Route::Built(proof);
                    }
                }
                match chosen.as_ref().map(|(n, p)| (n, p)) {
                    Some((line, name)) => match self.widened(line, name, claim, writer)
                    {
                        Route::Built(w) => {
                            haves.extend(w.have);
                            stated = Some(name.clone());
                            put = Some(line.clone());
                            w.name
                        }
                        Route::Declined(d) => return Route::Declined(d),
                    },
                    None => {
                        return Route::no(format!(
                            "substitute from {}, which has no Lean name",
                            place.named()
                        ))
                    }
                }
            }
            (_, Some(written)) => {
                let node = match self.tree(written) {
                    Route::Built(n) => n,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // An equation shown by real arithmetic where it is put, ln(8)
                // = 3·ln(2) (real arithmetic), is the real arithmetic's.
                let real = matches!(
                    just.source,
                    Some(crate::corpus::skeleton::Source::RealArithmetic)
                );
                let tactic = match real {
                    true => BridgeTactic::Real,
                    false => BridgeTactic::Side,
                };
                // Of numerals alone, cos(0) = 1, it is said in the type the
                // claim is computed in, where it is put: `Complex.cos 0` in
                // a line of complex numbers.
                let at = claim
                    .children
                    .iter()
                    .filter_map(|c| self.writer.carrier(c).built())
                    .fold(super::templates::Num::Int, |a, b| a.max(b));
                // Of no letter of the proof's, cos(0) = 1, whose names are
                // the library's functions only.
                let lettered = node
                    .names()
                    .iter()
                    .any(|n| self.writer.letters.contains_key(n.as_str()));
                let said = match !lettered {
                    true => self.writer.closed_formula(&node, at),
                    false => self.writer.formula(&node),
                };
                match said {
                    Route::Built(p) => {
                        t::bracket(shown(p, Proof::By(t::bridge(tactic, vec![]))))
                    }
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            _ => return Route::Built(Proof::By(t::bridge(BridgeTactic::Side, vec![]))),
        };
        // The line put into, cast up to the claim's type where it is
        // narrower. Of a line saying several things, the one the equation
        // turns into the claim; else the one that says what the claim does,
        // divides where the claim divides; else the first.
        let grammar = &self.sources.checked.grammar;
        let turns = |part: &Node| -> bool {
            let Some([left, right]) = put.as_ref().map(|e| e.children.as_slice())
            else {
                return false;
            };
            let want = grammar.print(claim);
            [(left, right), (right, left)].iter().any(|(from, to)| {
                grammar.print(&put_term(part, from, to, grammar)) == want
            })
        };
        // Where no part turns into the claim with the equation put for every
        // place, the equation is put for some places only, gcd(a, b) ∣ b
        // from b ∣ b, and each part that says what the claim does is offered.
        // A "for all" of the line is judged by what it says at the block's
        // letter, p(x) = (x − a)·q(x) + p(a) of "… for all x ∈ ℂ" at x, and
        // put into by its own name, which the tactic rewrites under the
        // quantifier.
        let at_claim = |node: &Node| -> Node {
            // Only what the line says at the claim's letter is wanted, so
            // its proof is left out.
            let cited = super::algebra::Cited {
                node: node.clone(),
                proof: Printed::of(
                    super::doc::TermKind::Elided,
                    super::doc::LeanType::Prop,
                ),
                says: None,
            };
            self.at_recorded_letter(&cited, &claim.names())
                .map_or_else(|| node.clone(), |at| at.node)
        };
        // Where the checker recorded the substitution into a line, the part
        // of the line it found (`Substituted::into`).
        let recorded_into = self.rec.substituted.get(&just.line).and_then(|r| match &r
            .into
        {
            crate::checker::record::SubstitutedInto::Line(at) => {
                self.line_part(at).built()
            }
            _ => None,
        });
        let unrecorded = || {
            just.into
                .as_ref()
                .and_then(|place| self.trees.get(place.named()))
                .map(|t| {
                    let t: Vec<(&Node, &Printed)> =
                        t.iter().map(|s| (&s.node, &s.proof)).collect();
                    let turned: Vec<_> = t
                        .iter()
                        .copied()
                        .filter(|(n, _)| turns(&at_claim(n)))
                        .take(1)
                        .collect();
                    if !turned.is_empty() {
                        return turned;
                    }
                    let alike: Vec<_> = t
                        .iter()
                        .copied()
                        .filter(|(n, _)| at_claim(n).notation() == claim.notation())
                        .collect();
                    if !alike.is_empty() {
                        return alike;
                    }
                    t.into_iter().take(1).collect()
                })
                .unwrap_or_default()
        };
        let candidates: Vec<(&Node, &Printed)> = match &recorded_into {
            Some(part) => vec![(&part.node, &part.proof)],
            None => unrecorded(),
        };
        let mut into = Vec::new();
        // A line put into that says something of the whole number a term
        // is, `∃ m : ℤ, (m : ℚ) = 2 ^ (p − 1) * 2 ∧ 2 ^ p − 1 ∣ m`, whose
        // term the equation turns into the claim's whole number, 2^p: the
        // line said of that number, the equation showing it is the term.
        let mut witnessed: Vec<Tactic> = Vec::new();
        for (line, name) in &candidates {
            let Some((term, whole)) = self.writer.wide_in_slot(line) else {
                continue;
            };
            let Some(at) = path_to(line, &term).and_then(|p| at_path(claim, &p)) else {
                continue;
            };
            let Route::Built(w) = self.writer.number_fixed(at, whole) else {
                continue;
            };
            let lemma = match whole {
                super::templates::Num::Nat => "parley_witness_at_nat",
                _ => "parley_witness_at",
            };
            // The named number is its term by its own equation, which the
            // step names beside the one it puts in (`named_specs`).
            let specs: Vec<super::doc::Rule> =
                self.named_specs.iter().cloned().map(t::forwards).collect();
            for by in [equation.clone(), negated(equation.clone())] {
                let mut steps = vec![t::push_cast(None)];
                if !specs.is_empty() {
                    steps.push(t::try_(t::simp_only(false, None, specs.clone(), None)));
                }
                steps.push(t::linear_combination(by));
                let shows = Proof::By(Tactic::Seq(steps));
                let applied = Printed {
                    kind: super::doc::TermKind::App {
                        head: Box::new(t::bridge_lemma(
                            lemma,
                            BridgeModule::PowerTactics,
                        )),
                        args: [
                            (*name).clone(),
                            t::bracket(w.clone()),
                            super::tactics::by_term(shows),
                        ]
                        .into_iter()
                        .map(super::doc::Arg::Explicit)
                        .collect(),
                        explicit: false,
                    },
                    ty: Some(super::doc::LeanType::Prop),
                };
                witnessed.push(Tactic::Exact(applied));
            }
        }
        for (i, (line, name)) in candidates.into_iter().enumerate() {
            // A "for all" line read at the block's letter, the part of it
            // the equation turns into the claim: line 2's "e(n) ≠ D(f(n),
            // n)" at the block's n, the equation being of that n, which no
            // rewriting under the line's own binder reaches.
            let read = self.at_recorded_letter(
                &super::algebra::Cited {
                    node: line.clone(),
                    proof: name.clone(),
                    says: None,
                },
                &claim.names(),
            );
            let mut parts = Vec::new();
            let read = read.filter(|_| line.notation() == crate::notations::FOR_ALL);
            if let Some(at) = &read {
                conjuncts(&at.node, at.proof.clone(), at.says.clone(), &mut parts);
            }
            // Of no part the equation turns into the claim, the whole line at
            // the letter, as a "for all" line cited inside a block is read:
            // 5.7's a·f(a) ≡ 1 at the block's a, which f(a) = 1 then turns
            // into a·1 ≡ 1, the claim a ≡ 1 with its 1 written.
            let whole = read.filter(|_| !parts.iter().any(|p| turns(&p.node)));
            if let Some(part) = parts.iter().find(|p| turns(&p.node)).or(whole.as_ref())
            {
                let at_name = format!("at{i}");
                haves.push(Tactic::Name {
                    name: at_name.clone(),
                    term: part.proof.clone(),
                });
                match self.widened(&part.node, &t::hyp(&at_name), claim, writer) {
                    Route::Built(w) => {
                        haves.extend(w.have);
                        into.push(w.name);
                    }
                    Route::Declined(d) => return Route::Declined(d),
                }
                continue;
            }
            match self.widened(line, name, claim, writer) {
                Route::Built(w) => {
                    haves.extend(w.have);
                    into.push(w.name);
                }
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // The equation is put in at the type its term has where it stands:
        // widened to the claim's, or as stated, where the term sits in a
        // part of a fixed type, (4 − 2)! of a claim in ℚ.
        // Of several lines, each is rewritten into before any is simplified,
        // since a simplification that loops ends the search (`parley_put_at`).
        let own = stated.clone().filter(|s| *s != equation);
        // An equation of natural numbers, A = (n + 1)!, put where its term
        // stands as a natural number, the exponent of 2^A: Lean's exponent
        // is of ℕ, so the equation is put there in ℕ.
        let in_nat = match (&put, &stated) {
            (Some(e), Some(name)) if e.notation() == EQUALITY => {
                match e.children.as_slice() {
                    [l, r] => self.nat_equation(l, r, name).built(),
                    _ => None,
                }
            }
            _ => None,
        };
        let mut ways: Vec<Tactic> = Vec::new();
        let tactics: &[BridgeTactic] = if into.len() > 1 {
            &[BridgeTactic::PutAt, BridgeTactic::SubstAt]
        } else {
            &[BridgeTactic::SubstAt]
        };
        for tactic in tactics {
            for line in &into {
                ways.push(put_into(*tactic, &equation, line));
                if let Some(own) = &own {
                    ways.push(put_into(*tactic, own, line));
                }
                if let Some(in_nat) = &in_nat {
                    ways.push(super::tactics::steps(vec![
                        in_nat.clone(),
                        put_into(*tactic, &t::hyp("e_nat"), line),
                    ]));
                }
            }
        }
        if into.is_empty() {
            ways.push(subst_by(&equation));
            if let Some(own) = &own {
                ways.push(subst_by(own));
            }
        }
        // A range member Lean computes wider is said as the integer that is
        // it (`wide_range_member`): an equation ↑(f k) = v put into f k ∈
        // {0, …, n − 1} is that integer, its equation and the line.
        if wide_range_member(&self.writer, claim) {
            for line in &into {
                ways.push(Tactic::Exact(range_member_made(
                    equation.clone(),
                    line.clone(),
                )));
            }
        }
        ways.extend(witnessed);
        Route::Built(haves_then(haves, ways_proof(ListReason::Substituted, ways)))
    }

    /// A cited "for all" of one letter written at the block's letter the
    /// check read it at (`CheckedTheorem::read_at`): its body with the
    /// letter put in, proved by the line applied to it, `hH2 y`. None where
    /// the line says no such "for all", the check read it at no letter, or
    /// that letter is not among `names`, the letters the claim writes.
    fn at_recorded_letter(
        &self,
        cited: &super::algebra::Cited,
        names: &std::collections::BTreeSet<String>,
    ) -> Option<super::algebra::Cited> {
        let [letter, set, body] = cited.node.children.as_slice() else {
            return None;
        };
        if cited.node.notation() != crate::notations::FOR_ALL || !letter.is_name() {
            return None;
        }
        // A guarded "for all", over ℕ or ℕ₀, asks a proof besides the
        // letter, that it is above 0 or at least 0, which the lines in scope
        // give; one over any other set, ℝ ∖ {5} or B, that the letter is in
        // it.
        let guard_by =
            |tactic| Some(super::tactics::by_term(super::doc::Proof::By(tactic)));
        let (ty, guard) = match super::expr::system_of(set) {
            Some(system) => (
                LetterType::Number(super::expr::letter_type(system)),
                match system {
                    super::expr::System::Type(_) => None,
                    _ => guard_by(super::tactics::bridge(BridgeTactic::Side, vec![])),
                },
            ),
            None => (
                self.writer.set_members(set)?.letter(),
                guard_by(super::tactics::bridge(BridgeTactic::SetSide, vec![])),
            ),
        };
        // The block's letter the check read the line at (`read_at`), where
        // the claim names it.
        let ctx = self.sources.ctx;
        let standard = |n: &Node| crate::matching::standard(n, ctx);
        let said = standard(&cited.node);
        let i = self.step_now.get()?;
        let read_at = self
            .rec
            .read_at
            .get(i)?
            .iter()
            .find(|r| crate::matching::alike_top(&standard(&r.said), &said, ctx))?;
        let at = read_at.letter.text.to_string();
        if !names.contains(&at) || self.writer.letters.get(at.as_str()) != Some(&ty) {
            return None;
        }
        let at = &at;
        let put = crate::matching::Binding::from([(
            letter.text,
            Node::name(letter.sort.clone(), at),
        )]);
        let read = crate::matching::substitute_apart_by(
            body,
            &put,
            &self.sources.checked.grammar.binders(),
        );
        // The guard is the block's `let` line that puts the letter in the
        // set (`ReadAt::opened_by`), `hK7`, where Lean names that line.
        let guard = match (guard, self.line_part(&read_at.opened_by)) {
            (Some(_), Route::Built(line)) => Some(line.proof),
            (guard, _) => guard,
        };
        let mut args = vec![super::tactics::hyp(&super::names::letter(at))];
        args.extend(guard);
        let at_letter = args.into_iter().fold(cited.proof.clone(), applied_to);
        Some(super::algebra::Cited {
            node: read,
            proof: super::tactics::bracket(at_letter),
            says: None,
        })
    }

    /// A `membership` claim `t ∈ S` the checker found shown by a cited
    /// equation putting t beside a term in S (`members_shown`,
    /// `ShownBy::Beside`), where Lean writes t in a wider type than S's:
    /// that other side as S's witness, and the equation faced so the
    /// witness is its left side, by `exact_mod_cast`. None where the record
    /// has no such equation, or Lean writes t in S's type already.
    fn member_from_record(
        &self,
        just: &Justification,
        node: &Node,
        writer: &Writer,
    ) -> Option<super::doc::Proof> {
        use crate::checker::record::ShownBy;
        let ShownBy::Beside(beside) = &self.rec.members_shown.get(&just.line)?.by
        else {
            return None;
        };
        let [term, set] = node.children.as_slice() else {
            return None;
        };
        let super::expr::System::Type(n) = super::expr::system_of(set)? else {
            return None;
        };
        if writer.carrier(term).built()? <= n {
            return None;
        }
        let other = &beside.other;
        if !writer.carrier(other).built().is_some_and(|c| c <= n) {
            return None;
        }
        let w = writer.number_fixed(other, n).built()?;
        let equation = self.cited_parts(&just.refs).into_iter().find(|c| {
            crate::matching::alike_top(&c.node, &beside.equation, self.sources.ctx)
        })?;
        // The witness is the side that is not the term: the equation as it
        // stands where the term is its right side, turned where its left.
        let faced = match beside.facing {
            Facing::Turned => equation.proof,
            Facing::Straight => {
                super::tactics::symm(super::tactics::bracket(equation.proof))
            }
        };
        let proof = super::tactics::by_term(super::doc::Proof::By(
            super::tactics::exact_mod_cast(faced),
        ));
        Some(super::doc::Proof::Term(super::expr::anonymous(vec![
            w, proof,
        ])))
    }

    /// `membership`. A term of a wider type said to be in a number system,
    /// an integer or a real, is one by a cited equation (`member_by_equation`).
    /// Any other membership is what the lines and the letters' types give.
    fn membership(
        &self,
        just: &Justification,
        node: &Node,
        writer: &Writer,
    ) -> Route<super::doc::Proof> {
        if let Some(proof) = self.member_from_record(just, node, writer) {
            return Route::Built(proof);
        }
        Route::Built(super::doc::Proof::By(super::tactics::bridge(
            BridgeTactic::Side,
            vec![],
        )))
    }

    /// `substitute` in rows: each row the row above with the change its
    /// reason proves put in, the first row the line it cites, and the last
    /// the claim.
    fn substitute_rows(
        &self,
        just: &Justification,
        writer: &Writer,
    ) -> Route<super::doc::Proof> {
        let Some(Ok(rows)) =
            crate::corpus::proof::substitute_rows(just, &self.thm.path)
        else {
            return Route::no("substitute rows that do not cut");
        };
        let Some(first) = rows.first() else {
            return Route::no("substitute rows with no row");
        };
        let Some(mut above) = self
            .named
            .get(first.cite.trim())
            .and_then(|n| n.first())
            .cloned()
        else {
            return Route::no(format!(
                "a first row citing {}, which has no Lean name",
                first.cite
            ));
        };
        let mut above_node: Option<Node> = self
            .trees
            .get(first.cite.trim())
            .and_then(|t| t.first())
            .map(|s| s.node.clone());
        // The row above as Lean has it, its name and statement: the cited
        // line's one sentence, then each row as it is written.
        let mut above_cited: Option<super::algebra::Cited> =
            match self.trees.get(first.cite.trim()).map(Vec::as_slice) {
                Some([one]) => Some(one.cited()),
                _ => None,
            };
        let mut haves = Vec::new();
        for (k, row) in rows.iter().enumerate().skip(1) {
            let row_node = match self.tree(&row.formula) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            let row_says = match writer.formula(&row_node) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            let Some(reason) = &row.reason else {
                return Route::no("a row after the first with no reason");
            };
            let Ok(by) = &reason.by else {
                return Route::no("a row whose reason does not read");
            };
            let change = match self.tree(&reason.fact) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            let change_says = match writer.formula(&change) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            // The change is stated by the `have` below, its counts in the
            // form it writes them (`row_stated`), as a calculation's row is.
            *self.row_stated.borrow_mut() = Some(change_says.clone());
            let proof = self.proof_of(
                Reason {
                    just: by,
                    cited: self.rec.cited_requires.get(&reason.line),
                },
                0,
                &change,
            );
            *self.row_stated.borrow_mut() = None;
            let proof = match proof {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            let change_name = format!("c{k}");
            haves.push(Tactic::Have {
                name: change_name.clone(),
                says: change_says.clone(),
                proof: Box::new(proof),
            });
            let change_h = super::tactics::hyp(&change_name);
            let row_name = format!("row{k}");
            // The change put into the row above at the places the checker
            // recorded (`SubstitutedInto::RowAbove`), as a line's equation
            // is put into a line; not where the row's lines say counts both
            // ways, which are taken to integers first (`count_conversion`).
            let counted_both_ways = {
                let lines: Vec<&Node> = std::iter::once(&change)
                    .chain(above_node.as_ref())
                    .chain(std::iter::once(&row_node))
                    .collect();
                self.count_forms(&lines).mixed
            };
            let recorded =
                above_cited
                    .clone()
                    .filter(|_| !counted_both_ways)
                    .and_then(|above| {
                        let put = GivenEquation {
                            change: super::algebra::Cited {
                                node: change.clone(),
                                proof: change_h.clone(),
                                says: Some(change_says.clone()),
                            },
                            above: Some(above),
                        };
                        self.substituted_by_record(
                            reason.line,
                            None,
                            &row_node,
                            Some(&put),
                        )
                        .built()
                    });
            let proof = match recorded {
                Some(proof) => proof,
                None => {
                    // Where the checker recorded the places the change goes in
                    // (`substituted_rows`) and none is a term of the row's arithmetic,
                    // a count in an exponent, each is written in its own type, and the
                    // change goes in as it is stated (`place_in_formula_type`); else
                    // widened to the row's type.
                    let in_own_type =
                        self.rec.substituted_rows.get(&reason.line).is_some_and(
                            |rec| {
                                !rec.put.places.is_empty()
                                    && rec.put.places.iter().all(|p| {
                                        !self.place_in_formula_type(&rec.start, p)
                                    })
                            },
                        );
                    let used = match in_own_type {
                        true => change_h.clone(),
                        false => {
                            match self.widened(&change, &change_h, &row_node, writer) {
                                Route::Built(w) => {
                                    haves.extend(w.have);
                                    w.name
                                }
                                Route::Declined(d) => return Route::Declined(d),
                            }
                        }
                    };
                    // At the type the term has where it stands, as `substitute`
                    // puts its equation in; each equation put by rewriting before
                    // either by `simp`, which loops where one side stands in the
                    // other, k in k + 1 − 1, and `first` goes on past no loop.
                    let above_h = super::tactics::hyp(&above);
                    let put = if used == change_h {
                        put_into(BridgeTactic::SubstAt, &used, &above_h)
                    } else {
                        super::tactics::first(
                            ListReason::RowPut,
                            vec![
                                put_into(BridgeTactic::PutAt, &used, &above_h),
                                put_into(BridgeTactic::PutAt, &change_h, &above_h),
                                put_into(BridgeTactic::SubstAt, &used, &above_h),
                                put_into(BridgeTactic::SubstAt, &change_h, &above_h),
                            ],
                        )
                    };
                    // A row whose lines say counts both ways takes them to
                    // integers first, as a step does (`count_conversion`).
                    let lines: Vec<&Node> = std::iter::once(&change)
                        .chain(above_node.as_ref())
                        .chain(std::iter::once(&row_node))
                        .collect();
                    let forms = self.count_forms(&lines);
                    let put = match forms.mixed {
                        true => Tactic::Seq(vec![
                            super::tactics::bridge(BridgeTactic::CountInt, vec![]),
                            put,
                        ]),
                        false => put,
                    };
                    super::doc::Proof::By(put)
                }
            };
            haves.push(Tactic::Have {
                name: row_name.clone(),
                says: row_says.clone(),
                proof: Box::new(proof),
            });
            above_cited = Some(super::algebra::Cited {
                node: row_node.clone(),
                proof: super::tactics::hyp(&row_name),
                says: Some(row_says),
            });
            above = row_name;
            above_node = Some(row_node);
        }
        let last = super::doc::Proof::By(Tactic::Exact(super::tactics::hyp(&above)));
        Route::Built(haves_then(haves, last))
    }

    /// An equation a line says, as a term to rewrite the claim with: the
    /// line itself, or, where the line is computed in a narrower type than
    /// the claim, the line cast up to the claim's type, since Lean rewrites
    /// a term only with an equation of its own type.
    fn widened(
        &self,
        line: &Node,
        name: &Printed,
        claim: &Node,
        writer: &Writer,
    ) -> Route<Widened> {
        let same = || {
            Route::Built(Widened {
                have: None,
                name: name.clone(),
            })
        };
        let numbers = |n: &Node| -> Vec<Node> {
            n.children
                .iter()
                .filter(|c| writer.is_number(c))
                .cloned()
                .collect()
        };
        let sides = numbers(line);
        if line.notation() != crate::notations::EQUALITY || sides.len() != 2 {
            return same();
        }
        // The line's type as it was written: the least that holds its sides.
        let mut own = super::templates::Num::Int;
        for s in &sides {
            match writer.carrier(s) {
                Route::Built(n) => own = own.max(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // The claim's type, or the calculation's where the claim is a row.
        let mut wanted = self.worked_in.get().map_or(own, |w| w.max(own));
        for s in numbers(claim) {
            match writer.carrier(&s) {
                Route::Built(n) => wanted = wanted.max(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        if wanted == own {
            return same();
        }
        let mut printed = Vec::new();
        for s in &sides {
            match writer.number(s, wanted) {
                Route::Built(p) => printed.push(p),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // Numerals alone are told their type.
        if !sides.iter().any(|s| writer.pinned(s)) {
            printed[0] = Printed::cast(printed[0].clone(), writer.num_type(wanted));
        }
        let [left, right]: [Printed; 2] = match printed.try_into() {
            Ok(both) => both,
            Err(_) => return Route::no("an equation of other than two sides"),
        };
        // The equation mapped into the wider type, its casts pushed in, and
        // compared with what is wanted up to the ring's laws.
        let wide = format!("{}_w", name.text().replace('.', "_"));
        let said = Printed::infix(
            super::doc::Op::EQUALS,
            left,
            right,
            super::doc::LeanType::Prop,
        );
        Route::Built(Widened {
            have: Some(widening_have(
                writer,
                &wide,
                said,
                own,
                wanted,
                name.clone(),
            )),
            name: super::tactics::hyp(&wide),
        })
    }

    /// The checker's record of how a substitution makes its claim: a row's,
    /// put into the row above, from the rows (`substituted_rows`); a claim
    /// sentence's own, where the record takes the substitution sentence by
    /// sentence (`substituted_sentences`); else the step's (`substituted`).
    fn substitution_record(
        &self,
        line: usize,
        sentence: Option<usize>,
        row_above: bool,
    ) -> Option<&crate::checker::record::Substituted> {
        match (row_above, sentence) {
            (true, _) => self.rec.substituted_rows.get(&line),
            (false, Some(k)) => self
                .rec
                .substituted_sentences
                .get(&(line, k))
                .or_else(|| self.rec.substituted.get(&line)),
            (false, None) => self.rec.substituted.get(&line),
        }
    }

    /// Where a step's defines are written out (`written_out`): each line the
    /// step names, by the hypothesis that proves it, and the goal. Not every
    /// line in scope, which would rewrite lines the step does not use, a
    /// define's own equation among them, to `True`.
    fn rewritten_at(&self) -> Vec<super::doc::Location> {
        use super::doc::{Location, TermKind};
        // The hypothesis a line's proof is, or projects from, `s1` of `s1.2`.
        fn root(p: &Printed) -> Option<&str> {
            match &p.kind {
                TermKind::Letter(name) => Some(name),
                TermKind::Paren(inner) | TermKind::Field { inner, .. } => root(inner),
                _ => None,
            }
        }
        let named = self.named_now.borrow();
        let mut out: Vec<Location> = Vec::new();
        for r in named.iter().flatten() {
            if self.thm.defines.iter().any(|d| d.label == *r) {
                continue;
            }
            for s in self.trees.get(r).into_iter().flatten() {
                if let Some(name) = root(&s.proof) {
                    let at = Location::Hypothesis(name.to_string());
                    if !out.contains(&at) {
                        out.push(at);
                    }
                }
            }
        }
        out.push(Location::Goal);
        out
    }

    /// Whether a substitution's place in `start` is written in the type of
    /// what it is put into, a term of its arithmetic (`Writer::in_formula_type`
    /// of its parent); the whole of `start` is. Any other, a function's
    /// argument or an exponent, is written in its own type.
    fn place_in_formula_type(&self, start: &Node, path: &[usize]) -> bool {
        let Some((&last, up)) = path.split_last() else {
            return true;
        };
        at_path(start, up)
            .is_some_and(|parent| self.writer.in_formula_type(parent, last))
    }

    /// `have e_nat : was = now` in ℕ, from the equation's proof `equation` by
    /// `exact_mod_cast`: an equation of natural numbers put where Lean's
    /// term is of ℕ, a power's exponent. Declined where either side is no
    /// natural number Lean writes in ℕ.
    fn nat_equation(
        &self,
        was: &Node,
        now: &Node,
        equation: &Printed,
    ) -> Route<Tactic> {
        use super::templates::Num;
        if !(self.writer.natural(was) && self.writer.natural(now)) {
            return Route::no("an equation not of natural numbers");
        }
        let (Route::Built(l), Route::Built(r)) = (
            self.writer.number(was, Num::Nat),
            self.writer.number(now, Num::Nat),
        ) else {
            return Route::no("an equation of natural numbers not written in ℕ");
        };
        Route::Built(Tactic::Have {
            name: "e_nat".to_string(),
            says: Printed::infix(
                super::doc::Op::EQUALS,
                l,
                r,
                super::doc::LeanType::Prop,
            ),
            proof: Box::new(super::doc::Proof::By(super::tactics::exact_mod_cast(
                equation.clone(),
            ))),
        })
    }

    /// `have e_w : was = now`, the recorded equation as the substitution puts
    /// it, stated in the wider type `to` (`Writer::closed_formula`) from its
    /// proof `equation` in `from` (`widening_have`).
    fn equation_widened(
        &self,
        rec: &crate::checker::record::Substituted,
        was: &Node,
        now: &Node,
        from: super::templates::Num,
        to: super::templates::Num,
        equation: &Printed,
    ) -> Route<Tactic> {
        let put = rec.equation.with_children(vec![was.clone(), now.clone()]);
        let Route::Built(says) = self.writer.closed_formula(&put, to) else {
            return Route::no("an equation the writer cannot state widened");
        };
        Route::Built(widening_have(
            &self.writer,
            "e_w",
            says,
            from,
            to,
            equation.clone(),
        ))
    }

    /// `calculation`: the chain as Lean's `calc`, every term in one type,
    /// each link proved by its reason.
    fn calculation(
        &self,
        just: &Justification,
        writer: &Writer,
    ) -> Route<super::doc::Proof> {
        let Some(Ok(chain)) = crate::corpus::proof::chain(just, &self.thm.path) else {
            return Route::no("a calculation whose lines do not cut");
        };
        let mut terms = vec![match self.tree(&chain.start) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        }];
        for line in &chain.lines {
            match self.tree(&line.term) {
                Route::Built(n) => terms.push(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // A chain that counts ∅ beside a set, |S| = |∅|: ∅ is a set of what
        // S holds (`expr::counted_beside_empty`).
        let hinted;
        let writer = match terms
            .iter()
            .find_map(|a| terms.iter().find_map(|b| writer.counted_beside_empty(a, b)))
        {
            Some(m) if writer.empty_of.is_none() => {
                let mut w = writer.with_letters(writer.letters.clone());
                w.empty_of = Some(m);
                hinted = w;
                &hinted
            }
            _ => writer,
        };
        // A chain of sets or of their members, A ∩ B = B ∩ A = ∅ or
        // F(F⁻¹(C)) = F(x), is written as sets are, and has no number type
        // to work in.
        let of_sets = terms
            .iter()
            .any(|t| writer.members_of(t).is_some() || writer.member_kind(t).is_some());
        // A chain of counts, |A| = |∅| = 0, is in ℕ∞ (`sets::count_term`).
        let of_counts = terms.iter().any(|t| writer.counts(t));
        // From ℤ, as the claim it proves is written.
        let mut at = super::templates::Num::Int;
        let mut printed = Vec::new();
        if of_counts {
            for t in &terms {
                match writer.count_term(t) {
                    Route::Built(p) => printed.push(p),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        } else if of_sets {
            for t in &terms {
                match writer.set_term(t) {
                    Route::Built(p) => printed.push(p),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        } else {
            for t in &terms {
                match writer.carrier(t) {
                    Route::Built(n) => at = at.max(n),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            for t in &terms {
                match writer.number(t, at) {
                    Route::Built(p) => printed.push(p),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            // A first term whose type nothing in it fixes, numerals alone or
            // a power whose letters are only in its exponent, is told its
            // type, bracketed inside as it stands in the chain.
            if !writer.pinned(&terms[0]) {
                let first = printed[0].clone();
                let first = match first.prec() < 51 {
                    true => super::tactics::bracket(first),
                    false => first,
                };
                printed[0] = Printed::cast(first, writer.num_type(at));
            }
        }
        // The claim, the first term and the last, is stated in its own
        // least type; a chain worked out in a wider one moves the goal there
        // first, as `qify` or `rify` does.
        let of_numbers = !of_sets && !of_counts;
        let mut own = super::templates::Num::Int;
        for t in [terms.first(), terms.last()].into_iter().flatten() {
            if !of_numbers {
                break;
            }
            if let Route::Built(n) = writer.carrier(t) {
                own = own.max(n);
            }
        }
        // The chain is worked in `at`, its first term told the type where
        // nothing in it fixes one; a claim in a narrower type, 3^q = 2^p in
        // ℤ beside ln and exp in ℝ, is moved up to it first.
        // A claim of numerals alone may be written in the chain's type
        // already, from the line it is reached from (`claimed`), and then
        // has nowhere to move.
        let mut block: Vec<Tactic> = match (of_numbers && own < at, at) {
            (true, super::templates::Num::Rat) => {
                vec![Tactic::Try(Box::new(super::tactics::call("qify", vec![])))]
            }
            (true, super::templates::Num::Real) => {
                vec![Tactic::Try(Box::new(super::tactics::call("rify", vec![])))]
            }
            _ => Vec::new(),
        };
        let mut links: Vec<super::doc::tactic::CalcLink> = Vec::new();
        let single = chain.lines.len() == 1;
        for (k, line) in chain.lines.iter().enumerate() {
            let (relation, modulus) = match line.relation.as_str() {
                r @ ("=" | "<" | ">" | "≤" | "≥") => (r.to_string(), None),
                "≡" => {
                    let Some(modulus) = &line.modulus else {
                        return Route::no("a congruence with no modulus");
                    };
                    let modulus = match self.tree(modulus) {
                        Route::Built(m) => m,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    match writer.number_fixed(&modulus, super::templates::Num::Int) {
                        Route::Built(m) => ("≡".to_string(), Some(m)),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                other => return Route::no(format!("a calculation joined by {other}")),
            };
            let proof = match &line.reason {
                Some(r) => {
                    let Ok(by) = &r.by else {
                        return Route::no(
                            "a calculation line whose reason does not read",
                        );
                    };
                    let fact = match self.tree(&r.fact) {
                        Route::Built(n) => n,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    let reason = Reason {
                        just: by,
                        cited: self.rec.cited_requires.get(&r.line),
                    };
                    self.worked_in.set(Some(at));
                    *self.row_stated.borrow_mut() =
                        super::doc::Op::of(relation.as_str()).map(|op| {
                            Printed::infix(
                                op,
                                printed[k].clone(),
                                printed[k + 1].clone(),
                                super::doc::LeanType::Prop,
                            )
                        });
                    let proof = self.proof_of(reason, 0, &fact);
                    self.worked_in.set(None);
                    *self.row_stated.borrow_mut() = None;
                    match proof {
                        Route::Built(p) => p,
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // A row citing a define, S(1) = Σ(j = 1 to 1) j(j + 1) by
                // D1, unfolds it and pushes in the casts that leaves; a
                // header's function, its equation guarded by its domain, at
                // an argument linear arithmetic shows is in it.
                None if let Some(cite) = line.cited() => {
                    let define = self
                        .thm
                        .defines
                        .iter()
                        .any(|d| d.label == cite)
                        .then(|| self.named.get(cite).and_then(|n| n.first()))
                        .flatten();
                    // A row of a step that names whole numbers, citing a line
                    // in the page's forms: both taken to ℚ, each named number
                    // put as its term, and the line used.
                    let named = self.named.get(cite).and_then(|n| n.first());
                    let in_named = match (named, self.named_specs.is_empty()) {
                        (Some(name), false) => Some(in_named_forms(
                            &self.named_specs,
                            name,
                            self.rec.link_facings.get(&line.line).copied(),
                            relation == "≡",
                        )),
                        _ => None,
                    };
                    // Whether the row, or the line it cites, takes an integer
                    // to ℕ, an item's 2^(d·e).toNat: a define is then not put
                    // in alone (`by_define`).
                    let line_to_nat = self
                        .trees
                        .get(cite)
                        .and_then(|t| t.first())
                        .and_then(|s| self.line_statement(&s.cited()).built())
                        .is_some_and(|p| p.has_to_nat());
                    let to_nat = [&printed[k], &printed[k + 1]]
                        .iter()
                        .any(|p| p.has_to_nat())
                        || line_to_nat;
                    // A row the define makes true, as the checker met its two
                    // sides with the define written out (`define_links`): the
                    // define's equation, and then the work its meeting leaves,
                    // or the casts Lean writes on the row.
                    let met = self.rec.define_links.get(&line.line);
                    // Two sides Lean writes alike once each `set` letter is
                    // read as its value: `simp only [hD]` puts the values in
                    // and closes the `x = x` left, whatever `toNat` or names
                    // the row writes.
                    let values = self.set_values();
                    let alike_set = super::doc::forms::alike_once_set(
                        &printed[k],
                        &printed[k + 1],
                        &values,
                    );
                    let by_define =
                        match (define, met, self.named_specs.is_empty(), to_nat) {
                            (Some(h), _, _, _) if alike_set => {
                                Some(super::doc::Proof::By(unfolded_by(
                                    std::slice::from_ref(h),
                                    true,
                                    false,
                                )))
                            }
                            // A row writing `toNat`, or citing a line that
                            // does, whose sides differ only in casts once the
                            // `set` letters are read as their values: Lean's
                            // casts, which `push_cast` moves once the
                            // define is put in.
                            (Some(h), Some(met), true, to_nat)
                                if !to_nat
                                    || super::doc::forms::casts_differ(
                                        &printed[k],
                                        &printed[k + 1],
                                        &values,
                                    )
                                    .is_some() =>
                            {
                                let cast =
                                    self.unfolds_to_casts(&printed[k], &printed[k + 1]);
                                Some(super::doc::Proof::By(unfolded_by(
                                    std::slice::from_ref(h),
                                    met.as_ref().is_some_and(unfolds_alone) && !cast,
                                    false,
                                )))
                            }
                            _ => None,
                        };
                    let mut ways: Vec<Tactic> = match define {
                        Some(h) => unfolded(std::slice::from_ref(h)),
                        None => Vec::new(),
                    };
                    // A "for all" line read at the row's letter, as a line
                    // cited inside a block is: 5.7's a·f(a) ≡ 1 at the
                    // block's a, as it stands or turned round.
                    let names: std::collections::BTreeSet<String> = terms[k]
                        .names()
                        .into_iter()
                        .chain(terms[k + 1].names())
                        .collect();
                    let read: Vec<super::algebra::Cited> = self
                        .trees
                        .get(cite)
                        .into_iter()
                        .flatten()
                        .filter(|s| s.node.notation() == crate::notations::FOR_ALL)
                        .filter_map(|s| self.at_recorded_letter(&s.cited(), &names))
                        .collect();
                    // The one such line, the way the checker found the row
                    // faces it (`link_facings`).
                    let at_letter = match (
                        read.as_slice(),
                        self.rec.link_facings.get(&line.line),
                    ) {
                        ([at], Some(facing)) => Some(super::doc::Proof::By(
                            Tactic::Exact(faced(at.proof.clone(), *facing)),
                        )),
                        _ => None,
                    };
                    for at in read {
                        for facing in [Facing::Straight, Facing::Turned] {
                            ways.push(Tactic::Exact(faced(at.proof.clone(), facing)));
                        }
                    }
                    ways.push(super::tactics::bridge(BridgeTactic::Side, vec![]));
                    // In the named numbers' forms, the line used the way the
                    // record says the row faces it: the row's proof.
                    let named_decided = in_named
                        .clone()
                        .filter(|_| self.rec.link_facings.contains_key(&line.line))
                        .map(super::doc::Proof::By);
                    ways.extend(in_named);
                    // The row is what the cited line says where the checker
                    // found it (`link_places`), that sentence or part as the
                    // line states it, met with the row as Lean writes it:
                    // as it stands, turned round, or apart in casts the cast
                    // table moves, a line in ℤ read in the chain's ℚ.
                    let placed = self
                        .rec
                        .link_places
                        .get(&line.line)
                        // A line whose statement the writer wrote (`store`):
                        // what Lean states for an obtained part is not known
                        // here.
                        .filter(|at| {
                            self.line_part(at)
                                .built()
                                .is_some_and(|found| found.says.is_some())
                        })
                        .and_then(|at| self.line_says(at).built())
                        .and_then(|(proof, says)| {
                            let op = super::doc::Op::of(relation.as_str())?;
                            let row = Printed::infix(
                                op,
                                printed[k].clone(),
                                printed[k + 1].clone(),
                                super::doc::LeanType::Prop,
                            );
                            // As the closer takes a meeting: of statements in
                            // one type, and no count, whose ℕ∞ a chain of
                            // counts may take its rows in.
                            let agree =
                                super::doc::forms::relation_types_agree(&says, &row)
                                    && fields_of(&says) == fields_of(&row);
                            if !agree || item_counts(&says) || item_counts(&row) {
                                return None;
                            }
                            self.proof_meeting(proof, &says, &row)
                        });
                    // A row that writes a power as the integer power where
                    // the line has it to its exponent's `toNat`, or the other
                    // way: converted as a citation's is, from the sentence the
                    // checker found the row in (`link_places`).
                    let converted = || {
                        let at = self.rec.link_places.get(&line.line)?;
                        let found = self.line_part(at).built()?;
                        let (proof, says) = self.line_says(at).built()?;
                        let op = super::doc::Op::of(relation.as_str())?;
                        let row = Printed::infix(
                            op,
                            printed[k].clone(),
                            printed[k + 1].clone(),
                            super::doc::LeanType::Prop,
                        );
                        self.powers_converted_at(
                            &[&terms[k], &terms[k + 1], &found.node],
                            &says,
                            &row,
                            &proof,
                            false,
                        )
                    };
                    match (by_define, placed) {
                        (Some(proof), _) => proof,
                        (None, Some(proved)) => super::doc::Proof::By(proved.closer()),
                        (None, None) => match (converted(), at_letter, named_decided) {
                            (Some(proof), _, _)
                            | (None, Some(proof), _)
                            | (None, None, Some(proof)) => proof,
                            (None, None, None) => ways_proof(ListReason::RowRead, ways),
                        },
                    }
                }
                // A row the page works out by real arithmetic, = 3·ln(2).
                None if line.cite == crate::corpus::Method::RealArithmetic.as_str() => {
                    super::doc::Proof::By(super::tactics::bridge(
                        BridgeTactic::Real,
                        vec![],
                    ))
                }
                None => super::doc::Proof::By(super::tactics::call("norm_num", vec![])),
            };
            // A chain of one link is that link, and its proof the step's:
            // Lean's calc would read the line after a lone link as another.
            if single {
                return Route::Built(proof);
            }
            links.push(super::doc::tactic::CalcLink {
                relation,
                term: printed[k + 1].clone(),
                modulus,
                proof,
            });
        }
        block.push(Tactic::Calc {
            first: printed[0].clone(),
            links,
        });
        Route::Built(super::doc::Proof::Block(block))
    }

    /// Each sentence of the lines `refs` names, each conjunction taken apart
    /// into its parts, with the Lean term that proves each part.
    fn cited_parts(&self, refs: &[String]) -> Vec<super::algebra::Cited> {
        let mut out = Vec::new();
        for r in refs {
            for s in self.trees.get(r).into_iter().flatten() {
                conjuncts(&s.node, s.proof.clone(), s.says.clone(), &mut out);
            }
        }
        out
    }

    /// Where the item's set letter `name` is the domain of one of its maps,
    /// the domain of the map the citation gives for it, as Lean writes it;
    /// None where the letter is no map's domain.
    fn given_domain(
        &self,
        sentence: &Sentence,
        name: &str,
        binding: &crate::matching::Binding,
    ) -> Option<Route<super::expr::Printed>> {
        let (map, _) = sentence.domains.iter().find(|(_, d)| {
            matches!(&d.kind, super::doc::TermKind::Letter(l) if *l == super::names::letter(name))
        })?;
        let given = binding.get(&crate::formula::symbol::Symbol::of(map));
        Some(match given {
            // The domain stands bracketed as an argument does.
            Some(g) if g.is_name() => match self.writer.domain_of(&g.text) {
                Some(d) if d.prec() < super::expr::MAX => {
                    let ty = d.ty.clone();
                    Route::Built(super::expr::Printed {
                        kind: super::doc::TermKind::Paren(Box::new(d)),
                        ty,
                    })
                }
                Some(d) => Route::Built(d),
                None => Route::no(format!("{}, whose domain no line gives", g.text)),
            },
            // A map given by its values, x ↦ c, is given on all its type.
            Some(g) if &*g.notation_name() == "property-of" => Route::Built(
                super::expr::Printed::head("Set.univ", super::doc::Source::Mathlib),
            ),
            _ => Route::left_out(format!(
                "a map's domain where its map {map} is given no letter"
            )),
        })
    }

    /// Whether a citation gives one of the letters an item's hypothesis
    /// uses, as Lean states it, all of a number system or a range, D := ℝ:
    /// the item asks `∀ x ∈ Set.univ, …` or `i ∈ Set.Icc a b` where the
    /// citing proof's line says `∀ x : ℝ, …` or `i ∈ Finset.Icc a b`, which
    /// `parley_whole_side` takes the one to the other. The Lean statement
    /// shows the letters a function's domain adds to the page's, D of
    /// `D ∈ nhds x`.
    fn given_whole(&self, asked: &Printed, binding: &crate::matching::Binding) -> bool {
        let used: Vec<&str> = asked
            .walk()
            .into_iter()
            .filter_map(|t| match &t.kind {
                super::doc::TermKind::Letter(name) => Some(name.as_str()),
                _ => None,
            })
            .collect();
        binding.iter().any(|(letter, v)| {
            matches!(
                v.notation(),
                crate::notations::NUMBER_SYSTEMS | crate::notations::INTEGER_RANGE
            ) && used.contains(&super::names::letter(letter.as_ref()).as_str())
        })
    }

    /// The type each of an item's type variables is taken at where a
    /// citation gives its things numbers, x ∈ {u, w} cited of 1 and 2: the
    /// least that holds every number given them. From ℕ: a set of naturals
    /// given for a set of things, S ⊆ ℕ, is of naturals, and a number given
    /// raises it to ℤ at least.
    fn things_given(
        &self,
        binders: &[Binder],
        binding: &crate::matching::Binding,
    ) -> ThingsGiven {
        use super::expr::Members;
        let mut given = ThingsGiven::default();
        for b in binders {
            let Binder::Letter { page, ty, .. } = b else {
                continue;
            };
            let Some(value) = binding.get(&crate::formula::symbol::Symbol::of(page))
            else {
                continue;
            };
            match ty {
                // A term of natural letters, b·d, is a natural; any other
                // number is an integer at least.
                LetterType::Member(Members::Things(var))
                    if self.writer.is_number(value) =>
                {
                    let of_letters = value.walk().iter().any(|m| m.is_name());
                    if of_letters && self.writer.natural(value) {
                        continue;
                    }
                    if let Route::Built(c) = self.writer.carrier(value) {
                        given.raise(*var, c);
                    }
                }
                // A set of things given a set of numbers, X := ℝ, sets the
                // things' type at least to that set's.
                LetterType::Set(Members::Things(var)) => {
                    match self.writer.set_members(value) {
                        Some(Members::Numbers(n)) => {
                            given.raise(*var, n);
                            given.numbers.insert(*var);
                        }
                        Some(m @ Members::Sets(_)) => {
                            given.others.insert(*var, m);
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        // A map given by its values, n ↦ 9ⁿ, gives what its body is with
        // n of the type its domain's things are taken at, ℚ of n in ℤ.
        for b in binders {
            let Binder::Letter {
                page,
                ty:
                    LetterType::Map {
                        from: Members::Things(from),
                        to: Members::Things(to),
                    },
                ..
            } = b
            else {
                continue;
            };
            let value = binding.get(&crate::formula::symbol::Symbol::of(page));
            let Some(value) = value.filter(|v| &*v.notation_name() == "property-of")
            else {
                continue;
            };
            let [body] = value.children.as_slice() else {
                continue;
            };
            let takes = given
                .at
                .get(from)
                .copied()
                .unwrap_or(super::templates::Num::Nat);
            let mut letters = self.writer.letters.clone();
            letters.insert(value.text.to_string(), LetterType::Number(takes));
            if let Route::Built(c) = self.writer.with_letters(letters).carrier(body) {
                given.raise(*to, c);
            }
        }
        // Things the citation gives nothing are what ∅ holds where the
        // lines say: the integers of ∏(x ∈ ∅) x in the base of an induction
        // on the parts of a set of integers.
        if let Some(held) = &self.writer.empty_of {
            let vars: std::collections::BTreeSet<usize> = binders
                .iter()
                .filter_map(|b| match b {
                    Binder::Letter { ty, .. } => Some(ty.lean_type()),
                    _ => None,
                })
                .flat_map(|ty| things_of_type(&ty))
                .collect();
            for var in vars {
                let told = given.numbers.contains(&var)
                    || given.others.contains_key(&var)
                    || given.at.contains_key(&var);
                match held {
                    _ if told => {}
                    Members::Numbers(n) => {
                        given.numbers.insert(var);
                        given.raise(var, *n);
                    }
                    other => {
                        given.others.insert(var, other.clone());
                    }
                }
            }
        }
        given
    }

    /// The item applied to what the citation gives it, and what it then
    /// says: the theorem with each letter given its value, and each
    /// hypothesis given by the line cited that says it as Lean writes both,
    /// or else left to `parley_side`.
    fn instance_of(
        &self,
        sentence: &Sentence,
        binding: &crate::matching::Binding,
        claim: Option<&Node>,
        supplied: &[Supplied],
    ) -> Route<Instance> {
        let mut given: std::collections::BTreeMap<String, super::expr::Printed> =
            std::collections::BTreeMap::new();
        let things = self.things_given(&sentence.binders, binding);
        // The type an item's general letters take: the least that holds the
        // claim and every value given them, a field's at least where the
        // item divides.
        let general = match sentence.general {
            Some(g) => {
                let least = if g.field {
                    super::templates::Num::Rat
                } else {
                    super::templates::Num::Int
                };
                let mut at = self.worked_in.get().map_or(least, |w| w.max(least));
                let numbers: Vec<&Node> = claim
                    .into_iter()
                    .flat_map(|c| c.children.iter())
                    .filter(|c| self.writer.is_number(c))
                    .collect();
                for n in numbers {
                    match self.writer.carrier(n) {
                        Route::Built(c) => at = at.max(c),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // A term the claim puts in a hole of a fixed type, ⌊A/B⌋ in
                // ℝ's, is of that type.
                if let Some(c) = claim {
                    at = at.max(self.held_in(c));
                }
                for b in &sentence.binders {
                    let Binder::Letter {
                        page,
                        ty,
                        general: true,
                        ..
                    } = b
                    else {
                        continue;
                    };
                    let Some(value) =
                        binding.get(&crate::formula::symbol::Symbol::of(page))
                    else {
                        continue;
                    };
                    match self.given_type(value, ty, &things) {
                        Route::Built(c) => at = at.max(c),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                Some(at)
            }
            None => None,
        };
        let things_at = |var: &usize| {
            let least = self.worked_in.get().unwrap_or(super::templates::Num::Nat);
            things.at.get(var).map_or(least, |n| least.max(*n))
        };
        let mut args = Vec::new();
        for b in &sentence.binders {
            match b {
                Binder::Letter {
                    name,
                    page,
                    ty,
                    general: in_general,
                } => {
                    let Some(value) =
                        binding.get(&crate::formula::symbol::Symbol::of(page))
                    else {
                        // A set the citation gives no value: a map's domain,
                        // the X of `f : X → W`, is the domain of what f is
                        // given, within which its images are taken; the Z a
                        // map goes into is all of its type, which every map
                        // goes into; anything else is left to Lean.
                        let fill =
                            match (ty, self.given_domain(sentence, name, binding)) {
                                (LetterType::Set(_), Some(Route::Built(d))) => d,
                                (LetterType::Set(_), Some(Route::Declined(d))) => {
                                    return Route::Declined(d)
                                }
                                (LetterType::Set(_), None) => {
                                    super::expr::Printed::head(
                                        "Set.univ",
                                        super::doc::Source::Mathlib,
                                    )
                                }
                                // A function of a recursion the file lets, F of
                                // D1, is the citing theorem's F, which the same
                                // define lets.
                                (LetterType::Function { .. }, _)
                                    if self.writer.letters.get(page.as_str())
                                        == Some(ty) =>
                                {
                                    super::expr::Printed::letter(
                                        super::names::letter(page),
                                        ty.lean_type(),
                                    )
                                }
                                _ => super::expr::Printed::of(
                                    super::doc::TermKind::Elided,
                                    ty.lean_type(),
                                ),
                            };
                        given.insert(name.clone(), fill.clone());
                        args.push(super::doc::Arg::Named {
                            name: name.clone(),
                            value: fill,
                        });
                        continue;
                    };
                    // The value of a define that names its number, m/p of
                    // `let r = m/p, a positive integer`, is that number, r.
                    let value = self
                        .witness_letters
                        .iter()
                        .find(|w| {
                            crate::matching::alike_top(
                                &w.value,
                                value,
                                self.sources.ctx,
                            )
                        })
                        .map_or(value, |w| &w.letter);
                    let printed = match (ty, general.filter(|_| *in_general)) {
                        (LetterType::Number(_), Some(at)) => {
                            self.writer.number_fixed(value, at)
                        }
                        // A value of a wider type that a line says is in the
                        // letter's, A + B ∈ ℚ of reals: the number that line
                        // gives.
                        (LetterType::Number(n), None) => {
                            match self.writer.number_fixed(value, *n) {
                                Route::Declined(d) => {
                                    match self.integer_line(value, *n) {
                                        Some(line) => {
                                            let printed = super::tactics::bracket(
                                                line.chosen(*n),
                                            );
                                            self.said_used.borrow_mut().push(
                                                SaidUsed {
                                                    line,
                                                    term: self
                                                        .writer
                                                        .grammar
                                                        .print(value),
                                                },
                                            );
                                            Route::Built(printed)
                                        }
                                        None => Route::Declined(d),
                                    }
                                }
                                built => built,
                            }
                        }
                        // A property given by what it says of t, `fun t : α
                        // => …`, t a member of what the property is of.
                        (LetterType::Property(members), _) => {
                            // Of things the citation gives numbers, the
                            // numbers at the type the things are taken at.
                            // Of things given sets, a set of them; of sets of
                            // things, sets of what is given for those.
                            let put = things.put(members, &things_at);
                            let (of, of_type) = (put.letter(), put.member_type());
                            match (&*value.notation_name(), value.children.as_slice()) {
                                ("property-of", [body]) => {
                                    let mut letters = self.writer.letters.clone();
                                    letters.insert(value.text.to_string(), of);
                                    let inner = self.writer.with_letters(letters);
                                    inner.formula(body).map(|b| {
                                        lambda(
                                            &super::names::letter(&value.text),
                                            of_type,
                                            b,
                                        )
                                    })
                                }
                                _ if value.is_name() => {
                                    Route::Built(super::tactics::hyp(
                                        &super::names::letter(&value.text),
                                    ))
                                }
                                _ => Route::no(
                                    "a property given by other than what it says",
                                ),
                            }
                        }
                        // A function given for a function letter, of the
                        // same types.
                        // A function given by its values, k ↦ t, a sum's
                        // term: `fun k : ℤ => t`, t in what it gives.
                        (LetterType::Function { from, to }, given)
                            if &*value.notation_name() == "property-of" =>
                        {
                            // A function into the general type gives the
                            // type chosen for it.
                            let gives = given.unwrap_or(*to);
                            match value.children.as_slice() {
                                [body] => {
                                    let mut letters = self.writer.letters.clone();
                                    letters.insert(
                                        value.text.to_string(),
                                        LetterType::Number(*from),
                                    );
                                    let mut inner = self.writer.with_letters(letters);
                                    inner.wholes.shift_remove(&*value.text);
                                    // k ↦ 2^k given for a sum's term stands for
                                    // the sum's index the claim runs it over,
                                    // in ℕ₀ from 0, so 2^k is written as the
                                    // claim's sum writes it.
                                    let index = claim.and_then(|c| {
                                        super::expr::index_letter_system(c, &value.text)
                                    });
                                    if let (super::templates::Num::Int, Some(system)) =
                                        (*from, index)
                                    {
                                        inner.introduce(&value.text, system);
                                    }
                                    inner.number_fixed(body, gives).map(|b| {
                                        lambda(
                                            &super::names::letter(&value.text),
                                            super::doc::LeanType::Num(*from),
                                            b,
                                        )
                                    })
                                }
                                _ => Route::no(
                                    "a function by its values of other than one body",
                                ),
                            }
                        }
                        (LetterType::Function { from, to }, given) => {
                            match self.writer.function_type(value) {
                                Route::Built(t)
                                    if t == (*from, given.unwrap_or(*to)) =>
                                {
                                    Route::Built(self.writer.function_printed(value))
                                }
                                // A function that takes the letter's numbers
                                // and gives numbers within its type, t of ℤ
                                // into ℤ for f of ℕ into ℝ: t between casts.
                                Route::Built((takes, gives))
                                    if *from <= takes
                                        && gives <= given.unwrap_or(*to) =>
                                {
                                    let wanted = given.unwrap_or(*to);
                                    Route::Built(mapped_through(
                                        self.writer.function_printed(value),
                                        super::doc::LeanType::Num(*from),
                                        takes,
                                        gives,
                                        wanted,
                                    ))
                                }
                                Route::Built(_) => Route::no(
                                    "a function given for a letter of other types",
                                ),
                                Route::Declined(d) => Route::Declined(d),
                            }
                        }
                        (LetterType::Statement, _) => self.writer.formula(value),
                        // A thing given a number: the number, at the type
                        // the things are taken at here.
                        (LetterType::Member(super::expr::Members::Things(var)), _)
                            if self.writer.is_number(value) =>
                        {
                            self.writer.number_fixed(value, things_at(var))
                        }
                        // A set of things given a set of numbers: the set at
                        // the type the things are taken at here.
                        (LetterType::Set(super::expr::Members::Things(var)), _)
                            if matches!(
                                self.writer.set_members(value),
                                Some(super::expr::Members::Numbers(_))
                            ) =>
                        {
                            self.writer.numbers_at(value, things_at(var))
                        }
                        // A map of things given by its values on numbers,
                        // n ↦ 9ⁿ: `fun n : ℤ => 9 ^ n`, taking and giving
                        // numbers at the types its two sides' things are
                        // taken at here.
                        (
                            LetterType::Map {
                                from: super::expr::Members::Things(from),
                                to: super::expr::Members::Things(to),
                            },
                            _,
                        ) if &*value.notation_name() == "property-of" => {
                            match value.children.as_slice() {
                                [body] => {
                                    let mut letters = self.writer.letters.clone();
                                    letters.insert(
                                        value.text.to_string(),
                                        LetterType::Number(things_at(from)),
                                    );
                                    let inner = self.writer.with_letters(letters);
                                    inner.number_fixed(body, things_at(to)).map(|b| {
                                        lambda(
                                            &super::names::letter(&value.text),
                                            super::doc::LeanType::Num(things_at(from)),
                                            b,
                                        )
                                    })
                                }
                                _ => Route::no(
                                    "a map by its values of other than one body",
                                ),
                            }
                        }
                        // A map from things into numbers given by its
                        // values, x ↦ x·c for t : X → ℤ: `fun x : ℤ => x *
                        // c`, x a member of what the things are taken at
                        // here, its value a number of t's type.
                        (
                            LetterType::Map {
                                from: from @ super::expr::Members::Things(_),
                                to: super::expr::Members::Numbers(to),
                            },
                            given,
                        ) if &*value.notation_name() == "property-of" => {
                            let put = things.put(from, &things_at);
                            let gives = given.unwrap_or(*to);
                            match value.children.as_slice() {
                                [body] => {
                                    let mut letters = self.writer.letters.clone();
                                    letters
                                        .insert(value.text.to_string(), put.letter());
                                    let inner = self.writer.with_letters(letters);
                                    inner.number_fixed(body, gives).map(|b| {
                                        lambda(
                                            &super::names::letter(&value.text),
                                            put.member_type(),
                                            b,
                                        )
                                    })
                                }
                                _ => Route::no(
                                    "a map by its values of other than one body",
                                ),
                            }
                        }
                        // A function of numbers given for a map of things
                        // into numbers, f for u : X → K: f itself where it
                        // gives the numbers asked, else f's value cast up.
                        (
                            LetterType::Map {
                                from: from @ super::expr::Members::Things(_),
                                to: super::expr::Members::Numbers(to),
                            },
                            given,
                        ) if self.writer.function_type(value).built().is_some() => {
                            let wanted = given.unwrap_or(*to);
                            let put = things.put(from, &things_at);
                            match self.writer.function_type(value) {
                                Route::Built((_, gives)) if gives == wanted => {
                                    Route::Built(self.writer.function_printed(value))
                                }
                                Route::Built((takes, gives)) if gives < wanted => {
                                    Route::Built(mapped_through(
                                        self.writer.function_printed(value),
                                        put.member_type(),
                                        takes,
                                        gives,
                                        wanted,
                                    ))
                                }
                                Route::Built(_) => Route::no(
                                    "a function given for a map into a narrower type",
                                ),
                                Route::Declined(d) => Route::Declined(d),
                            }
                        }
                        // A listed set whose members give no type, {∅},
                        // given for a set of things that another letter
                        // gives sets: a set of those.
                        (LetterType::Set(super::expr::Members::Things(var)), _)
                            if things.others.contains_key(var)
                                && self.writer.members_of(value).is_none() =>
                        {
                            self.writer.listed_as(value, &things.others[var])
                        }
                        // ∅ given for a member, the x := ∅ of |{x}| = 1 for
                        // |{∅}|: with the type the writer gives ∅ inside
                        // {∅} (`Writer::sets_of_nothing`), which ∅ alone
                        // does not give Lean.
                        (LetterType::Member(super::expr::Members::Things(_)), _)
                            if &*value.notation_name() == "empty-set" =>
                        {
                            match self
                                .writer
                                .sets_of_nothing(std::slice::from_ref(value))
                            {
                                Some(set) => Route::Built(Printed::cast(
                                    Printed::constant(
                                        "∅",
                                        super::doc::Source::Core,
                                        set.member_type(),
                                    ),
                                    set.member_type(),
                                )),
                                None => self.writer.set_term(value),
                            }
                        }
                        // A set, a member or a map given for one: the term
                        // as the writer writes a set's.
                        (
                            LetterType::Set(_)
                            | LetterType::Member(_)
                            | LetterType::Map { .. },
                            _,
                        ) => self.writer.set_term(value),
                        // A group given for a group, or a subgroup for a
                        // subgroup: its Lean name, the type or the
                        // `Subgroup G` itself, not the set it stands for.
                        (LetterType::Group | LetterType::Subgroup(_), _) => {
                            Route::Built(super::tactics::hyp(&super::names::letter(
                                &value.text,
                            )))
                        }
                        // The identity is no binder: `1` of the group.
                        (LetterType::Identity(_), _) => {
                            Route::no("an identity given as a letter of an item")
                        }
                    };
                    match printed {
                        Route::Built(p) => {
                            given.insert(name.clone(), p.clone());
                            args.push(super::doc::Arg::Named {
                                name: name.clone(),
                                value: p,
                            });
                        }
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // A hypothesis the checker found a line or a requires line
                // supplies (`Cited::supplied`), a letter's number system
                // among them: that line by its name, met with the
                // hypothesis as Lean asks it at the values given, as it
                // stands or by its casts (`supplied_proof`). Where none
                // does, and the citation gives the hypothesis's set all of
                // ℝ or a range, what the lines say read as the item asks
                // it (`parley_whole_side`); else `parley_side`.
                Binder::Fact { line, says, .. } => {
                    let wanted = super::doc::forms::substituted_all(says, &given);
                    let proof = line.as_ref().and_then(|line| {
                        supplied
                            .iter()
                            .find(|s| {
                                crate::matching::alike_top(
                                    &s.want,
                                    line,
                                    self.sources.ctx,
                                )
                            })
                            .and_then(|s| self.supplied_proof(&s.by, &wanted))
                    });
                    let search = || match self.given_whole(says, binding) {
                        true => super::tactics::by_term(super::doc::Proof::By(
                            super::tactics::bridge(BridgeTactic::WholeSide, vec![]),
                        )),
                        false => side_term(&[]),
                    };
                    args.push(proof_arg(proof.unwrap_or_else(search)));
                }
            }
        }
        // A type variable the item's sentence holds and none of its letters
        // does, the α of |(∅ : Set α)| = 0, is given by name: no argument
        // tells Lean what it is. It is what ∅ holds where the lines say.
        let lettered: std::collections::BTreeSet<usize> = sentence
            .binders
            .iter()
            .filter_map(|b| match b {
                Binder::Letter { ty, .. } => Some(ty.lean_type()),
                _ => None,
            })
            .flat_map(|ty| things_of_type(&ty))
            .collect();
        if let Some(held) = &self.writer.empty_of {
            for var in things_in(&sentence.prop) {
                if !lettered.contains(&var) {
                    args.insert(
                        0,
                        super::doc::Arg::Named {
                            name: super::expr::things_name(var),
                            value: super::expr::Printed::of(
                                super::doc::TermKind::Letter(
                                    held.letter().lean_type().text(),
                                ),
                                super::doc::LeanType::Universe,
                            ),
                        },
                    );
                }
            }
        }
        let decl = super::expr::Printed::head(
            &sentence.decl,
            super::doc::Source::Item(module_of_decl(&sentence.decl)),
        );
        let head = if args.is_empty() {
            decl
        } else {
            super::expr::Printed {
                kind: super::doc::TermKind::Paren(Box::new(super::expr::Printed {
                    kind: super::doc::TermKind::App {
                        head: Box::new(decl),
                        args,
                        explicit: false,
                    },
                    ty: Some(super::doc::LeanType::Prop),
                })),
                ty: Some(super::doc::LeanType::Prop),
            }
        };
        let term = fields(head, &sentence.part);
        let statement = sentence.prop.substituted(&given);
        let statement = match general {
            Some(at) => statement.with_general(super::doc::LeanType::Num(at)),
            None => statement,
        };
        Route::Built(Instance { term, statement })
    }

    /// The type a value given a general letter is in: a number's own, a
    /// function by its values k ↦ t the type of t with k of the type the
    /// function takes, and a function letter's what it gives.
    fn given_type(
        &self,
        value: &Node,
        ty: &LetterType,
        things: &ThingsGiven,
    ) -> Route<super::templates::Num> {
        match (ty, value.children.as_slice()) {
            (LetterType::Function { from, .. }, [body])
                if &*value.notation_name() == "property-of" =>
            {
                let mut letters = self.writer.letters.clone();
                letters.insert(value.text.to_string(), LetterType::Number(*from));
                self.writer.with_letters(letters).carrier(body)
            }
            (LetterType::Function { .. }, _) => {
                self.writer.function_type(value).map(|(_, to)| to)
            }
            // A map of things into numbers given by its values, x ↦ x·c: the
            // type of x·c with x a number of the type the things are given;
            // given a function, what the function gives.
            (
                LetterType::Map {
                    from: super::expr::Members::Things(var),
                    ..
                },
                [body],
            ) if &*value.notation_name() == "property-of" => {
                // Things given things, x ↦ c of a set of the theorem's
                // things: x one of them.
                let x = match things.at.get(var) {
                    Some(takes) => LetterType::Number(*takes),
                    None => LetterType::Member(super::expr::Members::Things(*var)),
                };
                let mut letters = self.writer.letters.clone();
                letters.insert(value.text.to_string(), x);
                self.writer.with_letters(letters).carrier(body)
            }
            // Given a map letter into numbers, t : X → ℤ, what it gives.
            (LetterType::Map { .. }, _) => {
                match self.writer.letters.get(&*value.text) {
                    Some(LetterType::Map {
                        to: super::expr::Members::Numbers(n),
                        ..
                    }) if value.is_name() => Route::Built(*n),
                    _ => self.writer.function_type(value).map(|(_, to)| to),
                }
            }
            // A set given for a `Set K` letter: the type of its numbers.
            (LetterType::Set(_), _) => match self.writer.set_members(value) {
                Some(super::expr::Members::Numbers(n)) => Route::Built(n),
                _ => Route::no(format!(
                    "{} is no set of numbers",
                    self.writer.grammar.print(value)
                )),
            },
            _ => self.writer.carrier(value),
        }
    }

    /// The item a reason cites, in Lean.
    fn cited_item<'r>(&self, reason: Reason<'r>) -> Route<(&Item, &'r Cited)>
    where
        'a: 'r,
    {
        let Some(cited) = reason.cited else {
            return Route::no("a citation the checker did not read");
        };
        match self.sources.items.get(&cited.item) {
            Some(item) => Route::Built((item, cited)),
            None => Route::no(format!("{} has no Lean form", cited.item)),
        }
    }

    /// Sentence `k` of a claim, by the item its reason cites.
    fn citation(
        &self,
        reason: Reason,
        k: usize,
        node: &Node,
    ) -> Route<super::doc::Proof> {
        use super::doc::Proof;
        use super::tactics as t;
        let (item, cited) = match self.cited_item(reason) {
            Route::Built(x) => x,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A phrase's define cited, `D1 n := 6, from 2`: the phrase is
        // written out as its meaning in the claim and in the lines alike, so
        // the claim is what the lines it cites say, in the claim's own
        // words, and the definition, whose two sides are one, adds nothing.
        let phrase = super::items::record_of(self.sources.checked, &cited.item)
            .is_some_and(|r| {
                r.phrase.is_some() && r.kind == crate::corpus::RecordKind::Definition
            });
        if phrase {
            return Route::Built(Proof::By(t::bridge(BridgeTactic::Side, vec![])));
        }
        let Some(concluded) = cited.concluded.get(k) else {
            return Route::no("a claim sentence no conclusion of the item gives");
        };
        let Some(sentence) = item.sentences.get(concluded.sentence) else {
            return Route::no("a conclusion the item does not have in Lean");
        };
        let instance = match self.instance_of(
            sentence,
            &cited.binding,
            Some(node),
            &cited.supplied,
        ) {
            Route::Built(i) => i,
            Route::Declined(d) => return Route::Declined(d),
        };
        // An item read as written says what the claim says: where the two
        // write one term in different forms, the build reports it. The
        // sets whose counts differ only in form are converted.
        let mut counted: Vec<Printed> = Vec::new();
        // The sets the two count, each with why it is finite.
        let mut finite: Vec<ShownFinite> = Vec::new();
        // The exponents whose powers differ only in form, each with why it is
        // at least 0, converted alike.
        let mut powered: Vec<NonNegative> = Vec::new();
        // Whether an integer power of a natural number cast up is converted
        // to the natural power alike.
        let mut cast_powers = false;
        // The powers under a sum whose exponent names its letter, converted
        // for each letter in its range.
        let mut bound: Vec<super::doc::forms::BoundPower> = Vec::new();
        // The rewrites of the identity elements the checker dropped meeting
        // the reading with the claim (`Cited::meetings`).
        let mut identities: Vec<&'static str> = Vec::new();
        // Whether a numeral's `toNat` is left once a reading is worked out.
        let mut numeral_to_nat = false;
        // A line that is the item's equation turned round, compared turned
        // back and closed by the equation's `symm`.
        let mut turned = false;
        // An item whose statement, its letters given, Lean writes as it
        // writes the line, up to what Lean takes as one term (a function
        // applied worked out, a bound letter renamed, a `set` letter read
        // as its value, `forms::alike_once_set`), closes the line by
        // `exact` alone. Two that are alike but for casts are not enough:
        // an item over any ring given ℤ writes `n ^ (2 : ℤ)`, which ℤ has
        // no power for, and the comparison keeps casts.
        let mut agrees = false;
        // An item that is the line once the identity elements the checker
        // dropped are dropped from both (`Cited::meetings`), with nothing else
        // apart: closed by those rewrites, as a conversion of them alone.
        let mut by_identities = false;
        // What the reading gives, as Lean states it at the citation's values:
        // the sentence as written, or the side a forward reading reaches.
        let compared = match concluded.way {
            Way::AsWritten => Some(instance.statement.clone()),
            Way::Forward => consequent(&instance.statement),
            Way::Backward => None,
        };
        if let Some(compared) = compared {
            if let Some(claim) = self.claim_as_stated(reason.just.line, node) {
                let templates = self.writer.templates;
                let widen = |head: &str, at| templates.same_function_at(head, at);
                use super::doc::forms;
                // Which way the item's equation faces the claim, as the
                // checker met them (`Cited::facings`).
                turned = matches!(
                    cited.facings.get(k).copied().flatten(),
                    Some(Facing::Turned)
                );
                let claim = match turned {
                    true => forms::turned(&claim),
                    false => claim,
                };
                // The identity elements the checker dropped meeting the two,
                // x − 0 read as x (`Cited::meetings`), dropped from both as
                // the conversion's rewrites drop them, and compared so.
                identities = cited
                    .meetings
                    .get(k)
                    .cloned()
                    .flatten()
                    .map(|m| m.identities.iter().filter_map(identity_lemma).collect())
                    .unwrap_or_default();
                identities.sort_unstable();
                identities.dedup();
                // With functions given as values applied first, as `simp`
                // reads them: (fun k => x ^ (m + 1 - k)) 0 is x ^ (m + 1 - 0).
                let (compared, claim_read) = match identities.is_empty() {
                    true => (compared, claim.clone()),
                    false => (
                        forms::with_identities_dropped(
                            &forms::beta_reduced(&compared),
                            &identities,
                        ),
                        forms::with_identities_dropped(
                            &forms::beta_reduced(&claim),
                            &identities,
                        ),
                    ),
                };
                numeral_to_nat = leaves_numeral_to_nat(&compared)
                    || leaves_numeral_to_nat(&claim_read);
                let mut found = forms::differences(&compared, &claim_read, &widen);
                for d in &found {
                    if let forms::FormDifference::Count {
                        item_set, line_set, ..
                    } = d
                    {
                        for set in [item_set, line_set] {
                            if !counted.contains(set) {
                                counted.push(set.clone());
                            }
                        }
                    }
                }
                // A count is converted only of a set shown finite
                // (`finite_counted`): one not shown so has no count in ℕ to
                // be taken to, and its difference stays. Both rewritten as
                // `forms_converted` rewrites them, what is left is what the
                // conversion leaves.
                if !counted.is_empty() {
                    finite = self.finite_counted(cited, sentence, node);
                    counted.retain(|s| finite.iter().any(|f| forms::alike(&f.set, s)));
                }
                if !counted.is_empty() {
                    found = forms::differences(
                        &forms::with_natural_counts(&compared, &counted),
                        &forms::with_natural_counts(&claim_read, &counted),
                        &widen,
                    );
                }
                // An integer power on one side and the natural power to its
                // exponent's `toNat` on the other: each integer power whose
                // exponent the record shows at least 0 (`nonneg_proof`)
                // rewritten as the natural one, as `forms_converted`
                // rewrites it, and what is left compared. An integer power
                // of a natural number cast up, `a ^ (k : ℤ)`, is the natural
                // power `a ^ k` with no fact asked (`zpow_natCast`).
                let natural_casts = forms::casts_natural_exponent(&compared)
                    || forms::casts_natural_exponent(&claim_read);
                let apart = |d: &forms::FormDifference| match d {
                    forms::FormDifference::ToNat { .. } => true,
                    forms::FormDifference::Cast { .. } => natural_casts,
                    _ => false,
                };
                if found.iter().any(apart) {
                    cast_powers = natural_casts;
                    let mut zpow = forms::integer_exponents(&compared);
                    zpow.extend(forms::integer_exponents(&claim_read));
                    powered = self
                        .exponents_shown_whole(cited, sentence, node)
                        .into_iter()
                        .filter(|w| zpow.iter().any(|e| forms::alike(e, &w.exponent)))
                        .collect();
                    // A power under a sum whose exponent names its letter,
                    // at least 0 only for each letter in the sum's range
                    // (`bound_rewrite`), where the other side takes that
                    // exponent to ℕ.
                    let apart_at: Vec<&Printed> = found
                        .iter()
                        .filter_map(|d| match d {
                            forms::FormDifference::ToNat { term, .. } => Some(term),
                            _ => None,
                        })
                        .collect();
                    bound = forms::bound_integer_powers(&compared)
                        .into_iter()
                        .chain(forms::bound_integer_powers(&claim_read))
                        .filter(|b| range_lower(&b.over).is_some())
                        .filter(|b| {
                            apart_at.iter().any(|t| forms::alike(t, &b.exponent))
                        })
                        .collect();
                    if !powered.is_empty() || cast_powers || !bound.is_empty() {
                        let exponents: Vec<Printed> = powered
                            .iter()
                            .map(|w| w.exponent.clone())
                            .chain(bound.iter().map(|b| b.exponent.clone()))
                            .collect();
                        let read = |t: &Printed| {
                            forms::with_natural_powers(
                                &forms::with_natural_counts(t, &counted),
                                &exponents,
                            )
                        };
                        found = forms::differences(
                            &read(&compared),
                            &read(&claim_read),
                            &widen,
                        );
                    }
                }
                // `exact` takes the two as written: not stated in two known
                // types, which the comparison, reading a count's relation in
                // ℕ, does not ask. An item's type variable is Lean's to fill.
                let known = |t: &Printed| {
                    forms::relation_type(t).filter(|ty| things_of_type(ty).is_empty())
                };
                let two_types = matches!(
                    (known(&compared), known(&claim)),
                    (Some(a), Some(b)) if a != b
                );
                agrees = found.is_empty()
                    && !two_types
                    && !turned
                    && counted.is_empty()
                    && powered.is_empty()
                    && !cast_powers
                    && bound.is_empty()
                    && identities.is_empty()
                    && !claim.is_truth()
                    && forms::one_term_once_set(&compared, &claim, &self.set_values());
                by_identities = found.is_empty()
                    && !two_types
                    && counted.is_empty()
                    && powered.is_empty()
                    && !cast_powers
                    && bound.is_empty()
                    && !identities.is_empty()
                    && !claim.is_truth();
                // An identity element Lean writes cast up, `((1 : ℤ) : ℚ)`,
                // taken to the numeral first, so its rewrite meets it.
                if by_identities {
                    identities.extend(forms::cast_unit_lemmas(&compared));
                    identities.extend(forms::cast_unit_lemmas(&claim_read));
                    identities.sort_unstable();
                    identities.dedup();
                }
                for d in found {
                    self.forms.borrow_mut().push(FormNote {
                        page_line: reason.just.line,
                        item: cited.item.clone(),
                        difference: d,
                    });
                }
            }
        }
        let statement = instance.statement.clone();
        let inst = instance.term;
        let iff = sentence.says.notation() == BICONDITIONAL;
        let implication = matches!(sentence.says.notation(), CONDITIONAL | IMPLICATION);
        // What the term the reading gives says, as Lean has it: the sentence,
        // or the side a forward reading reaches.
        let mut says = match concluded.way {
            Way::AsWritten => Some(statement.clone()),
            Way::Forward => consequent(&statement),
            Way::Backward => None,
        };
        // The claim as Lean states it (`claim_as_stated`), and whether a line
        // states it so (`stated_form`).
        let stated = self.stated_form(reason.just.line, node);
        let claim_lean = self.claim_as_stated(reason.just.line, node);
        let term = match concluded.way {
            Way::AsWritten => inst,
            Way::Forward if iff => forwards_of(inst, self.premise(cited, &statement)),
            Way::Forward if implication => {
                applied_to(inst, self.premise(cited, &statement))
            }
            Way::Forward => {
                return Route::no("a forward reading of a sentence that is no ↔ or if")
            }
            Way::Backward => {
                let witness =
                    match self.witnesses(&statement, cited, k, &reason.just.refs) {
                        Route::Built(w) => w,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                // What the definition's left side says, read in the claim's
                // own words where the two say one thing otherwise: an item
                // over any ring says "∈ ℕ₀" `∃ m : ℕ, ↑m = x`, a claim of
                // integers `0 ≤ x` (`parley_side`).
                // A claim a requires line above already states, "0 ≤ b − c"
                // for "b − c ∈ ℕ₀", is that line: tried first, as it is
                // quick and the others may search long.
                // A natural given as an integer's `toNat`, put back by `▸`,
                // which the goal guides in an `exact`; where the claim is in
                // a wider type than the item, the term stated by a `have`
                // and cast to it.
                let by_to_nat = inst.names("Int.toNat_of_nonneg");
                let mpr = Printed {
                    kind: super::doc::TermKind::App {
                        head: Box::new(Printed {
                            kind: super::doc::TermKind::Field {
                                inner: Box::new(t::bracket(inst)),
                                field: "mpr".to_string(),
                            },
                            ty: None,
                        }),
                        args: vec![super::doc::Arg::Explicit(witness)],
                        explicit: false,
                    },
                    ty: None,
                };
                // The definition's left side as Lean states it at the
                // citation's values, where it is the claim up to what Lean
                // takes as the same term: a function applied worked out,
                // `(fun n => x n + C) n` as `x n + C`, a bound letter
                // renamed, a `set` letter read as its value
                // (`forms::alike_once_set`), the `toNat` of a natural number
                // cast up that number (`forms::one_term_once_set`). The
                // reading proves the claim as it stands, which the term's
                // type checks by definitional equality.
                let left = left_side(&statement);
                let values = self.set_values();
                let as_claimed = match (&left, &claim_lean) {
                    (Some(left), Some(claim)) => {
                        super::doc::forms::one_term_once_set(left, claim, &values)
                    }
                    _ => false,
                };
                if as_claimed && !by_to_nat {
                    return Route::Built(Proof::Term(mpr));
                }
                // The definition's left side at the citation's values, as the
                // step's lines write it, read from the reading and met with
                // the claim, as a sentence read forwards is.
                let written = node_antecedent(&sentence.says)
                    .and_then(|part| self.written_at_values(part, &cited.binding));
                let read = match (&written, &left, &claim_lean) {
                    (Some(written), Some(left), Some(claim)) if !by_to_nat => {
                        let said = match one_statement(written, left) {
                            true => written,
                            false => left,
                        };
                        let claim = StepClaim {
                            printed: claim,
                            stated: stated.is_some(),
                        };
                        self.read_in_spelling(Some(cited), &mpr, said, written, claim)
                    }
                    _ => None,
                };
                if let Some(read) = read {
                    return Route::Built(read);
                }
                // An item over any ring or any set, taken at ℤ or ℕ, states
                // a membership in its general terms, where the claim of an
                // integer states its own fact: the Lean facts the record
                // gives (`cited_bridge`).
                let at = Cites::of(node, left.as_ref(), claim_lean.as_ref(), &values);
                match (cited_bridge(cited, sentence, &at), by_to_nat) {
                    (Some(CitedBridge::Rules(rules)), false) => {
                        return Route::Built(Proof::By(t::simpa_only(rules, mpr)))
                    }
                    (Some(CitedBridge::Cast), false) => {
                        return Route::Built(Proof::By(t::exact_mod_cast(mpr)))
                    }
                    _ => {}
                }
                let mut ways = vec![
                    t::steps(vec![
                        t::call("assumption", vec![]),
                        t::call("done", vec![]),
                    ]),
                    Tactic::Exact(mpr.clone()),
                ];
                if by_to_nat {
                    ways.push(t::on_h(&mpr, vec![t::exact_mod_cast(t::hyp("h"))]));
                    ways.push(t::on_h(
                        &mpr,
                        vec![
                            cast_to_nat_at_h(),
                            t::try_(t::push_cast(Some(t::at_h(true)))),
                            t::exact_mod_cast(t::hyp("h")),
                        ],
                    ));
                }
                ways.push(t::on_h(&mpr, vec![t::bridge(BridgeTactic::Side, vec![])]));
                return Route::Built(ways_proof(ListReason::DefinitionBackwards, ways));
            }
        };
        // A claim that is itself the "and", read as its parts, is the whole.
        let whole = matches!(
            node.notation(),
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION
        );
        // What the reading gives: a definition's right side, a theorem's
        // sentence; its "and" is taken apart as its tree nests it.
        let read = match (iff, sentence.says.children.as_slice()) {
            (true, [_, right]) => right,
            _ => &sentence.says,
        };
        // A sentence of the claim that one part of the "and" the reading
        // gives met, "for all d …" of "p > 1 and for all d …": that part, as
        // the checker's matcher met it (`Concluded::part`), its projection.
        let path = match (whole, concluded.part) {
            (false, Some(at)) => match leaf_path(read, at) {
                Some(path) => Some(path),
                None => {
                    return Route::no(
                        "a reading whose \"and\" has fewer parts than the part the claim met",
                    )
                }
            },
            _ => None,
        };
        let term = match &path {
            Some(path) => {
                says = says.and_then(|s| along(&s, path));
                projected(term, path)
            }
            None => term,
        };
        // A claim that is one part of what that part gives read at the
        // values, a property applied taken as its body (`Cited::within`):
        // the part of the "and" its body is, its projection.
        let term = match (cited.within.get(k).copied().flatten(), &says) {
            (Some(j), Some(s)) => {
                // The part read at the values, its property applied as its
                // body (`at_values`), and the path to its part j there.
                let part = match &path {
                    Some(path) => node_along(read, path),
                    None => Some(read),
                };
                let inner = part
                    .map(|p| self.at_values(p, &cited.binding))
                    .and_then(|at| leaf_path(&at, j));
                let Some(inner) = inner else {
                    return Route::no(
                        "a property's body whose \"and\" has fewer parts than the part the claim met",
                    );
                };
                says = along(&super::doc::forms::beta_reduced(s), &inner);
                projected(term, &inner)
            }
            _ => term,
        };
        // A define the step cites is written out first, as for algebra.
        let defines = self.cited_defines(&reason.just.refs);
        // An item that says a natural power of an integer is one gives the
        // claim nothing to read where the claim's exponent is an integer
        // the page shows not negative, 2^(n − 1); the writer gives the
        // witness.
        // The part of the item's sentence the reading gives, the sentence as
        // written or the side a forward reading reaches, and of it the part
        // of an "and" the step takes, at the citation's values, written as
        // the step's lines are (`docs/LEAN.md`, a citation). Kept where it is
        // spelt otherwise than Lean's statement of that part, which
        // `parley_instance` then reads as it.
        let given = match concluded.way {
            Way::AsWritten => Some(&sentence.says),
            Way::Forward => node_consequent(&sentence.says),
            Way::Backward => None,
        };
        let as_written = match (given, &path) {
            (Some(given), Some(path)) => node_along(given, path),
            (given, None) => given,
            (None, Some(_)) => None,
        }
        .and_then(|part| self.written_at_values(part, &cited.binding));
        // Where the two are one statement (`one_statement`), the writer's
        // copy, whose terms carry the types Lean's statement of an item over
        // any ring leaves to Lean, is what the closer compares with the
        // claim.
        let alike = match (&as_written, &says) {
            (Some(w), Some(s)) => one_statement(w, s),
            _ => false,
        };
        let says = match (&as_written, says) {
            (Some(w), Some(_)) if alike => Some(w.clone()),
            (_, s) => s,
        };
        let read_as_written = match (&as_written, &says, &claim_lean) {
            (Some(written), Some(said), Some(claim))
                if counted.is_empty()
                    && powered.is_empty()
                    && !cast_powers
                    && bound.is_empty()
                    && !agrees =>
            {
                let claim = StepClaim {
                    printed: claim,
                    stated: stated.is_some(),
                };
                self.read_in_spelling(Some(cited), &term, said, written, claim)
            }
            _ => None,
        };
        let conversion = Conversion {
            finite: &finite,
            whole: &powered,
            bound: &bound,
            cast_powers,
            identities: &identities,
            numeral_to_nat,
        };
        let closed = match (self.writer.integer_power_witness(node), read_as_written) {
            _ if !counted.is_empty()
                || !powered.is_empty()
                || cast_powers
                || !bound.is_empty() =>
            {
                forms_converted(&term, &conversion, turned)
            }
            _ if agrees => Proof::By(Tactic::Exact(term)),
            (Some(witness), _) => Proof::By(Tactic::Exact(witness)),
            // The item read in the step's spelling and met with the claim
            // (`docs/LEAN.md`, a citation); the recorded identities where
            // they are all that stands apart; the closer's rules where
            // neither holds.
            (None, Some(read)) => read,
            (None, None) if by_identities => {
                forms_converted(&term, &conversion, turned)
            }
            (None, None) => self.closer(
                node,
                claim_lean.as_ref().map(|printed| StepClaim {
                    printed,
                    stated: stated.is_some(),
                }),
                term,
                says.as_ref(),
                HowMet {
                    facing: cited.facings.get(k).copied().flatten(),
                    meeting: cited.meetings.get(k).and_then(Option::as_ref),
                },
                cited_bridge(
                    cited,
                    sentence,
                    &Cites::of(
                        node,
                        says.as_ref(),
                        claim_lean.as_ref(),
                        &self.set_values(),
                    ),
                ),
            ),
        };
        // The goal alone: each line the item is given puts the defines in
        // itself, where it is passed (`supplied_proof`).
        Route::Built(haves_then(
            written_out(&defines, &[super::doc::Location::Goal]),
            closed,
        ))
    }

    /// The proof of the right side of a definition a step folds, the `k`th
    /// sentence the citation concludes: its parts as the checker took them
    /// apart at the citation's values (`Cited::unfolded`), each proved where
    /// the checker found it supplied (`unfolded_proofs`); or the side whole,
    /// by the line the checker read it from (`Cited::firsts`), as Lean has
    /// it in `statement`, the definition at the citation's values, where a
    /// witness is a letter the line cited binds. Left to `parley_side`
    /// where no line says it.
    fn witnesses(
        &self,
        statement: &Printed,
        cited: &crate::checker::record::Cited,
        k: usize,
        refs: &[String],
    ) -> Route<Printed> {
        let lean_body = right_side(statement);
        // A witness that is a letter bound by the line cited, the k of its
        // "there is k", is no value in scope: the line says the right side
        // whole.
        let bound_here: std::collections::BTreeSet<String> = self
            .cited_parts(refs)
            .iter()
            .filter(|c| c.node.notation() == crate::notations::THERE_IS)
            .filter_map(|c| c.node.children.first())
            .filter(|l| l.is_name())
            .map(|l| l.text.to_string())
            .collect();
        let bound_by_line = cited
            .bound
            .values()
            .any(|v| v.is_name() && bound_here.contains(v.text.as_str()));
        let whole = || Route::Built(self.shown_by_line(cited, lean_body.as_ref(), &[]));
        if bound_by_line {
            return whole();
        }
        let (Some(Some(parts)), Some(lean)) = (cited.unfolded.get(k), &lean_body)
        else {
            return whole();
        };
        // What a line said of a witness the page wrote as a fraction that
        // is an integer, put in scope where the witness's facts are proved.
        let mut known = Vec::new();
        match self.unfolded_proof(lean, parts.iter().collect(), &mut known) {
            Some(proof) => Route::Built(proof),
            None => whole(),
        }
    }

    /// The proof of `lean`, Lean's statement of a definition's right side or
    /// of a "there is"'s body at its witness, from `parts`, the checker's
    /// parts of the same (`Cited::unfolded`), taken in order, one to each
    /// statement Lean joins by "and". Where the page asks more parts than
    /// Lean states, a membership of a number system that is a Lean type, x
    /// ∈ ℝ, is one Lean does not state, and is left out. None where the two
    /// do not then take the same number of parts, or a "there is" meets no
    /// "there is" of Lean's.
    fn unfolded_proof(
        &self,
        lean: &Printed,
        mut parts: Vec<&Unfolded>,
        known: &mut Vec<Tactic>,
    ) -> Option<Printed> {
        let wanted = lean_conjuncts(lean);
        while parts.len() > wanted {
            let at = parts.iter().position(|p| type_membership(p))?;
            parts.remove(at);
        }
        if parts.len() != wanted {
            return None;
        }
        let mut parts = parts.into_iter();
        let proof = self.unfolded_tree(lean, &mut parts, known)?;
        parts.next().is_none().then_some(proof)
    }

    /// The proof of `lean`, its statements joined by "and" each proved by the
    /// next of `parts`: a fact from where the checker found it supplied, as
    /// Lean states it; a "there is" by its witness, its guard where Lean
    /// writes one, an integer's of ℕ or ℕ₀ or a member's of a set, and its
    /// body at the witness (`unfolded_proof`), the membership the first of
    /// the body's parts where Lean writes it there.
    fn unfolded_tree<'u>(
        &self,
        lean: &Printed,
        parts: &mut impl Iterator<Item = &'u Unfolded>,
        known: &mut Vec<Tactic>,
    ) -> Option<Printed> {
        let lean = super::doc::forms::beta_reduced(&unparenthesized(lean));
        if let super::doc::TermKind::Infix { op, lhs, rhs } = &lean.kind {
            if op.symbol == "∧" {
                let left = self.unfolded_tree(lhs, parts, known)?;
                let right = self.unfolded_tree(rhs, parts, known)?;
                return Some(joined(vec![left], right));
            }
        }
        match parts.next()? {
            Unfolded::Fact { by, .. } => Some(self.unfolded_fact(&lean, by, known)),
            Unfolded::Witness {
                value,
                member,
                body,
            } => {
                let Unfolded::Fact { fact, by } = member.as_ref() else {
                    return None;
                };
                let [_, set] = fact.children.as_slice() else {
                    return None;
                };
                let system = super::expr::system_of(set);
                let term = match system {
                    Some(s) => {
                        let w =
                            self.witness(value, super::expr::letter_type(s)).built()?;
                        known.extend(w.known);
                        w.term
                    }
                    // A witness in a set: a number at its own type or a
                    // member as the writer writes one.
                    None => match self.writer.carrier(value) {
                        Route::Built(at) if self.writer.is_number(value) => {
                            self.writer.number_fixed(value, at).built()?
                        }
                        _ => self.writer.set_term(value).built()?,
                    },
                };
                let (guard, at) = exists_at(Some(&lean), &term);
                let at = at?;
                let mut proofs = vec![term];
                let mut inner: Vec<&Unfolded> = body.iter().collect();
                match guard {
                    Some(guard) => proofs.push(self.unfolded_fact(&guard, by, known)),
                    None => inner.insert(0, member),
                }
                let body = self.unfolded_proof(&at, inner, known)?;
                Some(joined(proofs, body))
            }
        }
    }

    /// The proof of one fact of a definition's right side, `wanted` as Lean
    /// states it at the citation's values: from where the checker found it
    /// supplied; by `parley_side` where no line supplies it, the line says
    /// it otherwise than Lean asks, or a witness's facts are put in scope
    /// first.
    fn unfolded_fact(
        &self,
        wanted: &Printed,
        by: &SuppliedBy,
        known: &[Tactic],
    ) -> Printed {
        if !known.is_empty() {
            return side_term(known);
        }
        self.supplied_proof(by, wanted)
            .unwrap_or_else(|| side_term(&[]))
    }

    /// A witness of a "there is" over `ty`: the value as Lean computes it
    /// there, or, for a value the page writes as a fraction that a line
    /// says is an integer, the integer that line gives, with what it says
    /// of it put in scope where the witness's facts are proved.
    fn witness(&self, value: &Node, ty: super::templates::Num) -> Route<Witness> {
        match self.writer.number_fixed(value, ty) {
            Route::Built(p) => Route::Built(Witness {
                term: p,
                known: None,
            }),
            Route::Declined(d) => match self.integer_line(value, ty) {
                Some(line) => Route::Built(Witness {
                    term: line.chosen(ty),
                    known: Some(Tactic::Fact(Printed::applied(
                        "Classical.choose_spec",
                        super::doc::Source::Core,
                        vec![line.proof],
                        super::doc::LeanType::Prop,
                    ))),
                }),
                None if ty == super::templates::Num::Int => {
                    match self.named_witness(value) {
                        Route::Built(w) => Route::Built(w),
                        Route::Declined(_) => Route::Declined(d),
                    }
                }
                None => Route::Declined(d),
            },
        }
    }

    /// A witness in ℤ of a term Lean computes wider, m² of an m a line the
    /// step names puts in ℕ: the whole number the step's lines name
    /// (`whole_witness`), chosen from the proof that there is one, and that
    /// proof's spec put in scope where the witness's facts are proved.
    fn named_witness(&self, value: &Node) -> Route<Witness> {
        use super::doc::{LeanType, Op, Proof};
        use super::tactics as t;
        let Some(i) = self.step_now.get() else {
            return Route::no("a witness outside a step");
        };
        let Some(letters) = self.rec.introduced.get(i) else {
            return Route::no("a step the checker's record has no letters for");
        };
        let facts = self.step_facts(i);
        // The witness stands inside a term, so its proof is one line.
        let proof = match self.whole_witness(value, letters, &facts) {
            Route::Built(p) => on_one_line(p),
            Route::Declined(d) => return Route::Declined(d),
        };
        let at = match self.writer.carrier(value) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        };
        let written = match self.writer.number_fixed(value, at) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let ty = self.writer.num_type(at);
        let letter = super::expr::witness_letter(value);
        let says = Printed::of(
            super::doc::TermKind::Quantified {
                quant: super::doc::Quant::Exists,
                letter: letter.clone(),
                letter_ty: LeanType::Num(super::templates::Num::Int),
                guard: None,
                body: Box::new(Printed::infix(
                    Op::EQUALS,
                    Printed::cast(t::hyp(&letter), ty),
                    written,
                    LeanType::Prop,
                )),
                bounded: false,
            },
            LeanType::Prop,
        );
        let name = "named_witness".to_string();
        let have = have_bracketed(Tactic::Have {
            name: name.clone(),
            says,
            proof: Box::new(proof),
        });
        let chosen = Printed::applied(
            "Classical.choose",
            super::doc::Source::Core,
            vec![t::hyp(&name)],
            LeanType::Num(super::templates::Num::Int),
        );
        let spec = Printed::applied(
            "Classical.choose_spec",
            super::doc::Source::Core,
            vec![t::hyp(&name)],
            LeanType::Prop,
        );
        let term = t::bracket(t::by_term(Proof::By(Tactic::Seq(vec![
            have.clone(),
            Tactic::Exact(chosen),
        ]))));
        Route::Built(Witness {
            term,
            known: Some(Tactic::Seq(vec![have, Tactic::Fact(spec)])),
        })
    }

    /// A line the step names saying a term is an integer, `(N − 1)/2 ∈ ℤ`,
    /// or that it is in a range, where `value` is that term as Lean writes
    /// it, with its Lean name and what it says beside the equation; None
    /// where no line says so. Lean states that line as `∃ m : ℤ, (m : ℚ) =
    /// …`, so the integer is the witness it gives.
    fn integer_line(
        &self,
        value: &Node,
        ty: super::templates::Num,
    ) -> Option<SaidLine> {
        // Lean states each as `∃ m : T, ↑m = x` of a term wider than T, of ℤ,
        // ℚ and ℝ, and of ℕ and ℕ₀ as `∃ m : ℤ, 0 ≤ m ∧ ↑m = x`, whose
        // witness is an integer too.
        let at = self.writer.carrier(value).built()?;
        let systems: Vec<super::expr::System> = match ty {
            super::templates::Num::Int => vec![
                super::expr::System::Type(ty),
                super::expr::System::NonNegative,
                super::expr::System::Positive,
            ],
            super::templates::Num::Rat | super::templates::Num::Real => {
                vec![super::expr::System::Type(ty)]
            }
            _ => return None,
        };
        let wanted = self.writer.number(value, at).built()?.untyped();
        // Whether the check found a line the reason names stating the term
        // in that system (`held`): such a line is the one taken. A range is
        // no statement of a system, and its integer is Lean's way of
        // writing the line.
        let asked = match ty {
            super::templates::Num::Int => crate::rules::System::Z,
            super::templates::Num::Rat => crate::rules::System::Q,
            _ => crate::rules::System::R,
        };
        let stated = matches!(
            self.held(value, asked),
            Some(crate::checker::record::LinesHold::Stated { .. })
        );
        // The latest such line the step names, or part of an "and".
        let named = self.named_now.borrow();
        let mut parts = Vec::new();
        for (key, lines) in &self.trees {
            if !named.as_ref().is_some_and(|n| n.contains(key)) {
                continue;
            }
            for s in lines {
                conjuncts(&s.node, s.proof.clone(), s.says.clone(), &mut parts);
            }
        }
        parts.iter().rev().find_map(|c| {
            let [term, set] = c.node.children.as_slice() else {
                return None;
            };
            if c.node.notation() != crate::notations::MEMBERSHIP {
                return None;
            }
            // A range of a wider term, k ∈ {1, …, n} of a real k, is its
            // integer with the range, `∃ m : ℤ, ↑m = k ∧ m ∈ …`
            // (`wide_range_member`).
            let beside = match super::expr::system_of(set) {
                Some(s) if stated && systems.contains(&s) => match s {
                    super::expr::System::Type(_) => Beside::Nothing,
                    _ => Beside::Order,
                },
                None if ty == super::templates::Num::Int
                    && wide_range_member(&self.writer, &c.node) =>
                {
                    Beside::Range
                }
                _ => return None,
            };
            let same = self.writer.number(term, at).built().map(|p| p.untyped())
                == Some(wanted.clone());
            same.then(|| SaidLine {
                proof: c.proof.clone(),
                beside,
            })
        })
    }

    /// `obtain`: the witnesses of a "there is" an item gives, named as the
    /// claim names them.
    /// The "there is" an `obtain` takes its witnesses from: a line of the
    /// page it names, or a sentence of the item it cites.
    fn obtained_from(&self, i: usize) -> Route<Obtained> {
        let step = &self.thm.steps[i];
        if self.rec.cited[i].is_none() && step.just.obtained_from.is_none() {
            // The sentence, or the part of one, of the lines named that
            // says "there is".
            // A "for all" line is read at the block's letter, as the checker
            // reads it.
            let mut names = std::collections::BTreeSet::new();
            for s in step.claim.sentences() {
                if let Some(n) = self.rec.page.get(&s) {
                    names.extend(n.names());
                }
            }
            names.retain(|n| !step.just.obtained.contains(n));
            return match self
                .cited_parts(&step.just.from)
                .into_iter()
                .map(|c| self.at_recorded_letter(&c, &names).unwrap_or(c))
                .find(|c| {
                    c.node.notation() == crate::notations::THERE_IS
                        || &*c.node.notation_name() == "there-is-some"
                }) {
                Some(c) => Route::Built(Obtained {
                    term: c.proof,
                    says: c.node,
                    binding: crate::matching::Binding::new(),
                    lean: None,
                }),
                None => Route::no("an obtain from no line that says \"there is\""),
            };
        }
        let reason = Reason {
            just: &step.just,
            cited: self.rec.cited[i].as_ref(),
        };
        let (item, cited) = match self.cited_item(reason) {
            Route::Built(x) => x,
            Route::Declined(d) => return Route::Declined(d),
        };
        let Some(at) = cited.obtained else {
            return Route::no("an obtain that takes no sentence of its item");
        };
        let before: usize = match self.sources.checked.library.groups.get(&cited.item) {
            Some(Some(groups)) => {
                groups[..cited.group].iter().map(|g| g.gives.len()).sum()
            }
            _ => 0,
        };
        let Some(sentence) = item.sentences.get(before + at) else {
            return Route::no("an obtain of a sentence the item does not have in Lean");
        };
        let mut binding = cited.binding.clone();
        for (k, v) in &cited.written {
            binding.entry(*k).or_insert_with(|| v.clone());
        }
        let (inst, premise, statement) =
            match self.instance_of(sentence, &binding, None, &cited.supplied) {
                Route::Built(i) => {
                    let premise = self.premise(cited, &i.statement);
                    (i.term, premise, i.statement)
                }
                Route::Declined(d) => return Route::Declined(d),
            };
        // A definition's right side is the "there is"; a theorem's sentence
        // is one.
        let iff = sentence.says.notation() == BICONDITIONAL;
        let says = match (iff, sentence.says.children.as_slice()) {
            (true, [_, right]) => right.clone(),
            _ => sentence.says.clone(),
        };
        // At the citation's values, a property given applied where the
        // sentence applies it: P(d) of set-builder is "there are m, n with
        // d = a·m + b·n".
        let says =
            read_at_values(&says, &binding, &self.sources.checked.grammar.binders());
        // The "there is" as Lean states it: the sentence, or the side of a
        // definition the forward reading reaches.
        let lean = match iff {
            true => consequent(&statement),
            false => Some(statement),
        };
        Route::Built(Obtained {
            term: if iff {
                forwards_of(inst, premise)
            } else {
                inst
            },
            says,
            binding,
            lean,
        })
    }

    fn obtain(&mut self, i: usize, depth: usize) -> Route<()> {
        self.said_used.borrow_mut().clear();
        let source = match self.obtained_from(i) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        let used = std::mem::take(&mut *self.said_used.borrow_mut());
        let step = &self.thm.steps[i];
        self.introduce(step);
        let claimed = match self.claimed(step) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let claim = Self::without_places(&claimed);
        let names = Self::names_of(step, claim.len());
        if let Some(n) = step.number.number() {
            self.named.insert(n.to_string(), names.clone());
            // Lean states each part as it takes it from the item, not as the
            // writer writes the page's claim: a part's statement is kept
            // below, where it is the item's (`lean_body_parts`).
            let said = Self::claim_sentences(&claimed, &names)
                .into_iter()
                .map(|s| LineSentence { says: None, ..s })
                .collect();
            self.store(n.to_string(), said);
        }
        // Lean nests a "there is" as the page does: each letter, then the
        // fact its range gives where Lean's type does not, then what is said
        // of them all. The claim's sentence about each letter's range is
        // that fact; its other sentences are what is said.
        let mut guards: IndexMap<String, String> = IndexMap::new();
        let mut body: Vec<String> = Vec::new();
        for ((node, _), name) in claim.iter().zip(&names) {
            // A letter's fact of being in a set, x ∈ A, as of a range, or
            // of being a part of one, W ⊆ X.
            let in_set = match node.children.as_slice() {
                [x, set]
                    if (node.notation() == crate::notations::MEMBERSHIP
                        || &*node.notation_name() == "subset")
                        && x.is_name()
                        && self.writer.members_of(set).is_some() =>
                {
                    Some(x.text.to_string())
                }
                _ => None,
            };
            // A function's fact of mapping one set into another, g : A → B,
            // the `Set.MapsTo` a "there is g : A → B" gives beside g.
            let maps = match node.children.as_slice() {
                [g, _, _]
                    if node.notation() == crate::notations::FUNCTION_TYPE
                        && g.is_name() =>
                {
                    Some(g.text.to_string())
                }
                _ => None,
            };
            let letter = introduces(node)
                .map(|(l, _)| l)
                .or_else(|| super::statement::range_letter(node))
                .or(in_set)
                .or(maps)
                .or_else(|| super::statement::introduces_polynomial(node));
            match letter.filter(|l| step.just.obtained.contains(l)) {
                Some(l) => {
                    guards.insert(l, name.clone());
                }
                None => body.push(name.clone()),
            }
        }
        // there is a ∈ X with nothing said, `∃ a ∈ X, True`: the letter, the
        // fact that it is in X, and nothing.
        if let ("there-is-some", [obtained]) =
            (&*source.says.notation_name(), step.just.obtained.as_slice())
        {
            let guard = guards
                .get(obtained)
                .cloned()
                .unwrap_or_else(|| "_".to_string());
            self.push_at(
                depth,
                Tactic::Obtain {
                    names: vec![super::names::letter(obtained), guard, "_".to_string()],
                    says: None,
                    from: source.term.clone(),
                },
                step.line,
                Self::step_spot(step),
            );
            return Route::Built(());
        }
        let mut pattern = Vec::new();
        let mut said = &source.says;
        // A "there is" the sentence says after an "and", u ∈ X and (there
        // are m, n with …): what comes before it, unnamed, and then it.
        while let (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [_, right],
        ) = (said.notation(), said.children.as_slice())
        {
            if right.notation() != crate::notations::THERE_IS {
                break;
            }
            pattern.push("_".to_string());
            said = right;
        }
        // Each letter the item's "there is" binds, as the step names it.
        let mut renamed = crate::matching::Binding::new();
        for obtained in &step.just.obtained {
            let [bound, set, inner] = said.children.as_slice() else {
                return Route::no(
                    "an obtain of more letters than its \"there is\" binds",
                );
            };
            if said.notation() != crate::notations::THERE_IS {
                return Route::no(
                    "an obtain of more letters than its \"there is\" binds",
                );
            }
            pattern.push(super::names::letter(obtained));
            renamed.insert(
                crate::formula::symbol::Symbol::of(&bound.text),
                Node::name(bound.sort.clone(), obtained),
            );
            // Lean writes "there is s ∈ S" with the membership beside s
            // for every S but a number system its type gives, ℤ, ℚ, ℝ or
            // ℂ; the page's ℕ and ℕ₀ add that the integer s is above 0 or
            // at least 0. The set as the citation gives it, Y := ℕ.
            let given = match set.is_name() {
                true => source.binding.get(&set.text).unwrap_or(set),
                false => set,
            };
            let whole = matches!(
                super::expr::system_of(given),
                Some(super::expr::System::Positive | super::expr::System::NonNegative)
            );
            let guarded = set.notation() == crate::notations::INTEGER_RANGE
                || whole
                || super::expr::system_of(set).is_none();
            if guarded {
                // A member of the page's ℕ or ℕ₀ keeps its fact named.
                let unnamed = match whole {
                    true => format!("{}_pos", super::names::letter(obtained)),
                    false => "_".to_string(),
                };
                let guard = guards.get(obtained).cloned().unwrap_or(unnamed);
                pattern.push(guard);
            }
            said = inner;
        }
        // What is said of the letters, taken apart as Lean nests its "and":
        // ((d > 1 ∧ d ∣ p) ∧ d ∣ q) is ⟨⟨a, b⟩, c⟩.
        // A part Lean states otherwise than the page's sentence, q·N + 0 = A
        // for q·N = A, is obtained under a name of its own, and the sentence
        // is stated from it after, so that each line's name says what the
        // page says.
        let mut restated = Vec::new();
        // The names that hold their part as Lean states it from the item,
        // with that statement: what a step citing the line reads.
        let mut as_stated: Vec<(String, Printed)> = Vec::new();
        if !body.is_empty() {
            if body.len() > conjunct_count(said) {
                return Route::no(
                    "an obtain whose sentences are not the parts of its \"there is\"",
                );
            }
            let said = crate::matching::substitute_apart_by(
                said,
                &renamed,
                &self.sources.checked.grammar.binders(),
            );
            let parts = shaped_parts(&said, body.len());
            // The parts as Lean states them, from the item's statement of
            // the "there is" (`Obtained::lean`), where it takes apart into
            // as many parts as the page's.
            let stated: Vec<Printed> = source
                .lean
                .as_ref()
                .map(|s| lean_body_parts(s, &step.just.obtained))
                .filter(|p| p.len() == conjunct_count(&said))
                .unwrap_or_default();
            let values = self.set_values();
            let mut lean_names = Vec::new();
            for (name, part) in body.iter().zip(&parts) {
                let at = claimed.iter().zip(&names).find(|(_, n)| *n == name);
                let page = at.map(|((_, _, p), _)| p.clone());
                // The part of the "there is" the checker found the sentence
                // to be (`ObtainedPart::owed`), as Lean states it.
                let owed = at.and_then(|((place, _, _), _)| {
                    let found: Vec<&crate::checker::record::ObtainedPart> = self
                        .rec
                        .obtained_parts
                        .get(&step.just.line)
                        .into_iter()
                        .flatten()
                        .filter(|p| p.sentence == *place)
                        .collect();
                    match found.as_slice() {
                        [one] if one.part == 0 => stated.get(one.owed).cloned(),
                        _ => None,
                    }
                });
                // How the checker met the sentence's parts with those of
                // the "there is" (`CheckedTheorem::obtained_parts`), and
                // where the writer placed casts on the one and not the
                // other.
                let met = at.map(|((place, _, _), _)| {
                    self.rec
                        .obtained_parts
                        .get(&step.just.line)
                        .into_iter()
                        .flatten()
                        .filter(|p| p.sentence == *place)
                        .any(|p| {
                            p.meeting.turned
                                || p.meeting.permuted
                                || !p.meeting.identities.is_empty()
                        })
                });
                let lean = match &owed {
                    Some(stated) => Some(stated.clone()),
                    None => self.writer.formula(part).built(),
                };
                let differs = match (&page, &lean, met) {
                    (Some(says), Some(lean), Some(met)) => {
                        met || super::doc::forms::casts_differ(lean, says, &values)
                            .is_some()
                    }
                    _ => false,
                };
                match (differs, page, lean) {
                    (true, Some(says), Some(lean)) => {
                        let as_obtained = format!("{name}_obtained");
                        lean_names.push(as_obtained.clone());
                        restated.push(Restated {
                            name: name.clone(),
                            says,
                            from: as_obtained,
                            lean,
                        });
                    }
                    _ => {
                        lean_names.push(name.clone());
                        if let Some(stated) = owed {
                            as_stated.push((name.clone(), stated));
                        }
                    }
                }
            }
            pattern.push(shaped_pattern(&said, &lean_names));
        }
        self.push_at(
            depth,
            Tactic::Obtain {
                names: pattern,
                says: None,
                from: source.term.clone(),
            },
            step.line,
            Self::step_spot(step),
        );
        for r in restated {
            let Some(proved) =
                self.proof_meeting(super::tactics::hyp(&r.from), &r.lean, &r.says)
            else {
                return Route::no(format!(
                    "an obtain whose part Lean states as {}, and the page as {}",
                    r.lean.text(),
                    r.says.text()
                ));
            };
            self.push_at(
                depth,
                Tactic::Have {
                    name: r.name,
                    says: r.says,
                    proof: Box::new(super::doc::Proof::Term(proved.term())),
                },
                step.line,
                Self::step_spot(step),
            );
        }
        // An item given a line's number, x := the rational of `√2 ∈ ℚ`,
        // gives its facts of that number; a sentence the page says of the
        // line's term, √2 = p/q, is that fact with the goal put in terms of
        // the number.
        for ((node, prop), name) in claim.iter().zip(&names) {
            let specs = self.specs_in(node, &used);
            if specs.is_empty() {
                continue;
            }
            as_stated.retain(|(n, _)| n != name);
            self.push_at(
                depth,
                Tactic::Have {
                    name: name.clone(),
                    says: prop.clone(),
                    proof: Box::new(super::doc::Proof::By(Tactic::Seq(vec![
                        super::tactics::call("rw", vec![TacticArg::Rules(specs)]),
                        super::tactics::exact_mod_cast(super::tactics::hyp(name)),
                    ]))),
                },
                step.line,
                Self::step_spot(step),
            );
        }
        if let Some(line) = step
            .number
            .number()
            .and_then(|n| self.trees.get_mut(&n.to_string()))
        {
            for (name, stated) in as_stated {
                for s in line
                    .iter_mut()
                    .filter(|s| s.name.as_deref() == Some(name.as_str()))
                {
                    s.says = Some(stated.clone());
                }
            }
        }
        Route::Built(())
    }

    /// The rewrites that put a claim in terms of the numbers lines give,
    /// `← Classical.choose_spec hS` for each line used whose term the claim
    /// has, to rewrite by; none where it has none.
    fn specs_in(&self, claim: &Node, used: &[SaidUsed]) -> Vec<super::doc::Rule> {
        let parts: Vec<String> = claim
            .walk()
            .iter()
            .map(|n| self.writer.grammar.print(n))
            .collect();
        // A term standing where the Lean form of its notation reads it at ℝ,
        // the a^(p − 2) of (a^(p − 2)) mod p, is there at ℝ whatever type
        // the line naming its number says it in.
        let mut real: Vec<(String, Node)> = Vec::new();
        for n in claim.walk() {
            let mut at_real: Vec<&Node> = self.writer.always_real_args(&n);
            if let Route::Built(t) = self.writer.template(&n) {
                let fixed = super::templates::Slot::Fixed(super::templates::Num::Real);
                at_real.extend(
                    n.children
                        .iter()
                        .zip(&t.holes)
                        .filter(|(_, hole)| **hole == fixed)
                        .map(|(child, _)| child),
                );
            }
            for arg in at_real {
                real.push((self.writer.grammar.print(arg), arg.clone()));
            }
        }
        let mut lines: Vec<&Printed> = Vec::new();
        let mut out = Vec::new();
        for u in used {
            if !parts.contains(&u.term) || lines.contains(&&u.line.proof) {
                continue;
            }
            lines.push(&u.line.proof);
            let spec = u.line.equation();
            let at_real = real
                .iter()
                .find(|(printed, _)| *printed == u.term)
                .and_then(|(_, node)| self.spec_at_real(&u.line, spec.clone(), node));
            out.push(super::tactics::backwards(at_real.unwrap_or(spec)));
        }
        out
    }

    /// The equation a line naming a whole number gives, `Classical.choose_spec
    /// h`, restated at ℝ, where its term stands at ℝ: `(by exact_mod_cast
    /// Classical.choose_spec h : ((Classical.choose h : ℤ) : ℝ) = t)`. None
    /// where the term is not written at ℝ.
    fn spec_at_real(
        &self,
        line: &SaidLine,
        spec: Printed,
        term: &Node,
    ) -> Option<Printed> {
        use super::doc::LeanType;
        use super::templates::Num;
        let value = self.writer.number_fixed(term, Num::Real).built()?;
        let chosen = line.chosen(Num::Int);
        let says = Printed::infix(
            super::doc::Op::EQUALS,
            Printed::cast(
                Printed::cast(chosen, LeanType::Num(Num::Int)),
                LeanType::Num(Num::Real),
            ),
            value,
            LeanType::Prop,
        );
        // The line states its equation in the term's own type.
        let own = self.writer.carrier(term).built()?;
        let proof = super::tactics::by_term(cast_carried(spec, own, Num::Real));
        Some(ascribed(proof, says))
    }

    /// A step that owns a block: its claim proved by the block's steps,
    /// opened by its lines.
    fn block(
        &mut self,
        i: usize,
        method: Method,
        claim: &[(Node, Printed)],
        names: &[String],
        depth: usize,
    ) -> Route<()> {
        let step = &self.thm.steps[i];
        let spot = Self::step_spot(step);
        // A claim Lean's types already make true needs no proof, and what
        // the block shows inside it is cited nowhere outside it.
        if claim.is_empty() {
            self.push_at(
                depth,
                Tactic::Comment("what this block shows, Lean's types give".to_string()),
                step.line,
                spot,
            );
            return Route::Built(());
        }
        // A claim of several sentences is proved as their "and", and taken
        // apart after into each sentence's name.
        let Some((claimed, _)) = claim.first() else {
            return Route::no("a block with no claim");
        };
        if claim.len() > 1 && method == Method::Induction {
            return Route::no("an induction whose claim is several sentences");
        }
        let (whole, prop) = match claim {
            [(_, prop)] => (names[0].clone(), prop.clone()),
            _ => {
                let parts = claim.iter().map(|(_, p)| p.clone()).collect();
                let Some(all) = super::expr::joined(super::doc::Op::AND, parts, 36)
                else {
                    return Route::no("a claim of no sentences");
                };
                (format!("{}_all", names[0]), all)
            }
        };
        let Some(block_at) = self.rec.blocks.iter().position(|b| b.owner == i) else {
            return Route::no("a block the checker did not record");
        };
        let block = self.rec.blocks[block_at].clone();
        self.push_at(
            depth,
            Tactic::Have {
                name: whole.clone(),
                says: prop,
                proof: Box::new(super::doc::Proof::Block(Vec::new())),
            },
            step.line,
            spot.clone(),
        );
        let kept = self.writer.letters.clone();
        let kept_wholes = self.writer.wholes.clone();
        // The lines in scope as the block opens: a line one case or
        // direction says is no line of the next.
        let kept_lines = self.trees.clone();
        let parts: Vec<Option<usize>> = if step.parts.is_empty() {
            vec![None]
        } else {
            (0..step.parts.len()).map(Some).collect()
        };
        match method {
            Method::Proof | Method::Contradiction => {
                if let Route::Declined(d) = self.open(step, None, depth + 1) {
                    return Route::Declined(d);
                }
                let children: Vec<usize> = block.children.clone();
                if let Route::Declined(d) = self.steps(&children, depth + 1) {
                    return Route::Declined(d);
                }
                let closing = match self.closing(
                    children.last().copied(),
                    Owing::Written(block.ends_written(None)),
                ) {
                    Route::Built(c) => c,
                    Route::Declined(d) => return Route::Declined(d),
                };
                self.close(depth + 1, closing, step.line, spot.clone());
            }
            Method::Cases => {
                // The sentence, or the part of one, of the lines named that
                // says "or".
                // A "for all" line is read at the letters the cases assume,
                // as the checker reads it.
                let mut letters = std::collections::BTreeSet::new();
                for o in &step.openers {
                    for s in o.body(&self.thm.path).sentences() {
                        if let Some(n) = self.rec.page.get(&s) {
                            letters.extend(n.names());
                        }
                    }
                }
                let Some(said) = self
                    .cited_parts(&step.just.from)
                    .into_iter()
                    .map(|c| self.at_recorded_letter(&c, &letters).unwrap_or(c))
                    .find(|c| c.node.notation() == crate::notations::DISJUNCTION)
                else {
                    return Route::no("cases from no line that says \"or\"");
                };
                let source = said.proof.clone();
                let labels: Vec<String> = parts
                    .iter()
                    .map(|part| {
                        step.openers
                            .iter()
                            .find(|o| o.part == *part)
                            .map(|o| line_name(&o.label))
                            .unwrap_or_else(|| "_".to_string())
                    })
                    .collect();
                // The pattern follows the "or" as the page groups it: a ∨ b
                // ∨ c read from the left is (a ∨ b) ∨ c.
                // Cases that group the "or" otherwise, a ∨ b as one case of
                // a ∨ b ∨ c ∨ d, take it restated as the cases say it, each
                // case a part of an "or" read from the right.
                let mut names = labels.iter();
                let pattern = or_pattern(&said.node, &mut names);
                let line = if disjuncts(&said.node) == labels.len() {
                    Tactic::Rcases {
                        from: source.clone(),
                        pattern,
                    }
                } else {
                    let mut says = Vec::new();
                    for part in &parts {
                        let node =
                            step.openers.iter().find(|o| o.part == *part).and_then(
                                |o| {
                                    o.body(&self.thm.path)
                                        .sentences()
                                        .first()
                                        .and_then(|s| self.rec.page.get(s))
                                        .cloned()
                                },
                            );
                        let Some(node) = node else {
                            return Route::no("a case that assumes nothing");
                        };
                        match self.writer.formula(&node) {
                            Route::Built(p) => says.push(p),
                            Route::Declined(d) => return Route::Declined(d),
                        }
                    }
                    let restated = Tactic::Seq(vec![
                        Tactic::Fact(source.clone()),
                        super::tactics::call("tauto", vec![]),
                    ]);
                    Tactic::Rcases {
                        from: super::tactics::bracket(shown(
                            cases_said(says),
                            super::doc::Proof::By(restated),
                        )),
                        pattern: cases_pattern(&labels),
                    }
                };
                self.push_at(depth + 1, line, step.line, spot.clone());
                for (part, label) in parts.iter().zip(&labels) {
                    // Each case starts from the letters as the block found
                    // them: a letter one case lets is none of the next's.
                    self.writer.letters = kept.clone();
                    self.writer.wholes = kept_wholes.clone();
                    self.trees = kept_lines.clone();
                    self.named.insert(label.clone(), vec![label.clone()]);
                    // What the case assumes, for a step that cites it.
                    if let Some(o) = step.openers.iter().find(|o| o.part == *part) {
                        let nodes: Vec<Node> = o
                            .body(&self.thm.path)
                            .sentences()
                            .iter()
                            .filter_map(|s| self.rec.page.get(s).cloned())
                            .collect();
                        if let [node] = nodes.as_slice() {
                            self.store(
                                o.label.clone(),
                                vec![LineSentence::only(node.clone(), label.clone())],
                            );
                        }
                    }
                    let children: Vec<usize> = block
                        .children
                        .iter()
                        .copied()
                        .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                        .collect();
                    self.push_at(
                        depth + 1,
                        Tactic::Bullet(Box::new(super::tactics::call("skip", vec![]))),
                        step.line,
                        spot.clone(),
                    );
                    // The lines after the case's `by` line open its method's
                    // block: a supposition, or a proof block's lets.
                    let inner: Vec<crate::corpus::Opener> =
                        step.opening(*part).inner.into_iter().cloned().collect();
                    if let Route::Declined(d) = self.open_lines(step, &inner, depth + 2)
                    {
                        return Route::Declined(d);
                    }
                    if let Route::Declined(d) = self.steps(&children, depth + 2) {
                        return Route::Declined(d);
                    }
                    // A case that says it is the claim assumes what is owed,
                    // and has no steps.
                    let claimed =
                        step.openers.iter().any(|o| o.part == *part && o.is_claim);
                    let closing = match children.is_empty() && claimed {
                        true => Closing::Tactic(Box::new(Tactic::Exact(
                            super::tactics::hyp(label),
                        ))),
                        false => match self.closing(
                            children.last().copied(),
                            Owing::Written(block.ends_written(*part)),
                        ) {
                            Route::Built(c) => c,
                            Route::Declined(d) => return Route::Declined(d),
                        },
                    };
                    self.close(depth + 2, closing, step.line, spot.clone());
                }
            }
            Method::Induction => {
                if let Route::Declined(d) =
                    self.induction(step, &block, claimed, &parts, depth + 1)
                {
                    return Route::Declined(d);
                }
            }
            Method::BothDirections => {
                self.push_at(
                    depth + 1,
                    super::tactics::call("constructor", vec![]),
                    step.line,
                    spot.clone(),
                );
                for part in &parts {
                    self.trees = kept_lines.clone();
                    self.push_at(
                        depth + 1,
                        Tactic::Bullet(Box::new(super::tactics::call("skip", vec![]))),
                        step.line,
                        spot.clone(),
                    );
                    if let Route::Declined(d) = self.open(step, *part, depth + 2) {
                        return Route::Declined(d);
                    }
                    let children: Vec<usize> = block
                        .children
                        .iter()
                        .copied()
                        .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                        .collect();
                    if let Route::Declined(d) = self.steps(&children, depth + 2) {
                        return Route::Declined(d);
                    }
                    let closing = match self.closing(
                        children.last().copied(),
                        Owing::Written(block.ends_written(*part)),
                    ) {
                        Route::Built(c) => c,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    self.close(depth + 2, closing, step.line, spot.clone());
                }
            }
            other => {
                return Route::no(format!(
                    "the method {} is not written in Lean yet",
                    other.as_str()
                ))
            }
        }
        self.writer.letters = kept;
        self.writer.wholes = kept_wholes;
        if claim.len() > 1 {
            self.push_at(
                depth,
                Tactic::Obtain {
                    names: names.to_vec(),
                    says: None,
                    from: super::tactics::hyp(&whole),
                },
                step.line,
                spot,
            );
        }
        Route::Built(())
    }

    /// `induction`: "for all k ∈ ℕ₀" from 0 and "for all k ∈ ℕ" from 1 are
    /// `LeanBridges.Functions.le_induction` from 0 or 1 of the integer k; the step part's
    /// induction hypothesis keeps the page's label.
    fn induction(
        &mut self,
        step: &Step,
        block: &crate::checker::record::Block,
        claimed: &Node,
        parts: &[Option<usize>],
        depth: usize,
    ) -> Route<()> {
        let spot = Self::step_spot(step);
        let [letter, set, body] = claimed.children.as_slice() else {
            return Route::no("an induction whose claim says no \"for all\"");
        };
        if claimed.notation() != crate::notations::FOR_ALL || !letter.is_name() {
            return Route::no("an induction whose claim says no \"for all\"");
        }
        let name = super::names::letter(&letter.text);
        let start = step.just.start.as_deref().unwrap_or("");
        if start == "∅" {
            return self.subset_induction(step, block, claimed, parts, depth);
        }
        let from_one = match (super::expr::system_of(set), start) {
            (Some(super::expr::System::NonNegative), "0") => false,
            (Some(super::expr::System::Positive), "1") => true,
            _ => return Route::no("an induction from other than the start of ℕ or ℕ₀"),
        };
        let system = match from_one {
            true => super::expr::System::Positive,
            false => super::expr::System::NonNegative,
        };
        self.writer.introduce(&letter.text, system);
        // The letter is an integer and its guard 0 < k or 0 ≤ k; the guard
        // put as `le_induction` reads it, 1 ≤ k or 0 ≤ k, in its place, so
        // that the induction hypothesis does not ask it again.
        let start = if from_one { 1 } else { 0 };
        let guard = format!("h_{name}");
        let int = super::doc::LeanType::Num(super::templates::Num::Int);
        let from = match super::expr::relation_of(
            "≤",
            Printed::numeral(start.to_string(), int.clone()),
            Printed::letter(name.clone(), int),
        ) {
            Route::Built(r) => r,
            Route::Declined(d) => return Route::Declined(d),
        };
        let lines = [
            Tactic::Intro(vec![name.clone(), guard.clone()]),
            Tactic::Replace {
                name: guard.clone(),
                says: from,
                proof: Box::new(super::doc::Proof::By(super::tactics::call(
                    "omega",
                    vec![],
                ))),
            },
            Tactic::Induction {
                on: vec![name.clone(), guard],
                using: super::tactics::bridge_lemma(
                    "LeanBridges.Functions.le_induction",
                    BridgeModule::Functions,
                ),
            },
        ];
        for line in lines {
            self.push_at(depth, line, step.line, spot.clone());
        }
        // Each part starts from the lines in scope as the induction found
        // them: a line one part opens is no line of the next.
        let kept_lines = self.trees.clone();
        for part in parts {
            self.trees = kept_lines.clone();
            let marker = part
                .and_then(|k| step.parts.get(k))
                .map(|(m, _)| m.as_str())
                .unwrap_or("");
            let openers: Vec<&crate::corpus::Opener> =
                step.openers.iter().filter(|o| o.part == *part).collect();
            match marker {
                "base" => {
                    self.push_at(
                        depth,
                        Tactic::Alternative("base".to_string()),
                        step.line,
                        spot.clone(),
                    );
                }
                "step" => {
                    let hypothesis = openers
                        .iter()
                        .find(|o| o.is_hypothesis)
                        .map(|o| line_name(&o.label))
                        .unwrap_or_else(|| "IH".to_string());
                    if let Some(o) = openers.iter().find(|o| o.is_hypothesis) {
                        self.named.insert(o.label.clone(), vec![hypothesis.clone()]);
                        self.store(
                            o.label.clone(),
                            vec![LineSentence::only(body.clone(), hypothesis.clone())],
                        );
                    }
                    let letter_line = openers
                        .iter()
                        .find(|o| !o.is_hypothesis && o.kind == Intro::Let);
                    let guard = letter_line
                        .map(|o| line_name(&o.label))
                        .unwrap_or_else(|| format!("h_{name}"));
                    // The letter's line, `j ∈ ℕ` or `j ∈ ℕ₀`, which Lean
                    // writes `0 < j` or `0 ≤ j`, from the case's guard,
                    // `1 ≤ j` or `0 ≤ j`.
                    if let Some(o) = letter_line {
                        if let Some(node) = self.opener_node(o) {
                            let h = super::tactics::hyp(&guard);
                            let proof = match from_one {
                                true => Printed::applied(
                                    "lt_of_lt_of_le",
                                    super::doc::Source::Mathlib,
                                    vec![
                                        Printed::constant(
                                            "zero_lt_one",
                                            super::doc::Source::Mathlib,
                                            super::doc::LeanType::Prop,
                                        ),
                                        h,
                                    ],
                                    super::doc::LeanType::Prop,
                                ),
                                false => h,
                            };
                            self.store(
                                o.label.clone(),
                                vec![LineSentence {
                                    at: 0,
                                    node,
                                    name: None,
                                    proof,
                                    says: None,
                                }],
                            );
                        }
                    }
                    let case = format!("succ {name} {guard} {hypothesis}");
                    self.push_at(
                        depth,
                        Tactic::Alternative(case),
                        step.line,
                        spot.clone(),
                    );
                }
                other => return Route::no(format!("an induction part {other:?}")),
            }
            // A case proved by its own `proof` block: its lines, other than
            // the induction's letter and hypothesis, are opened as a
            // `proof` block's are.
            let own: Vec<crate::corpus::Opener> = openers
                .iter()
                .filter(|o| !o.is_hypothesis)
                .filter(|o| !self.introduces_letter(o, &letter.text))
                .map(|o| (*o).clone())
                .collect();
            let opened_from = self.lines.len();
            if let Route::Declined(d) = self.open_lines(step, &own, depth + 1) {
                return Route::Declined(d);
            }
            // The binders the part's own lines took off its goal.
            let introduced: usize = self.lines[opened_from..]
                .iter()
                .filter(|l| l.depth == depth + 1)
                .map(|l| match &l.tactic {
                    Tactic::Intro(names) => names.len(),
                    _ => 0,
                })
                .sum();
            let children: Vec<usize> = block
                .children
                .iter()
                .copied()
                .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                .collect();
            if let Route::Declined(d) = self.steps(&children, depth + 1) {
                return Route::Declined(d);
            }
            // The part's goal is the motive Lean makes at the start or at
            // k + 1, the cast of the letter a cast of that value, `↑(k + 1)`,
            // with what the part's own lines took off it by their intros.
            let motive = match self.writer.formula(body) {
                Route::Built(m) => m,
                Route::Declined(d) => return Route::Declined(d),
            };
            let int = super::doc::LeanType::Num(super::templates::Num::Int);
            let at = match marker {
                "base" => Printed::numeral(start.to_string(), int),
                _ => Printed::infix(
                    super::doc::Op::PLUS,
                    Printed::letter(name.clone(), int.clone()),
                    Printed::numeral("1".to_string(), int.clone()),
                    int,
                ),
            };
            let goal = super::doc::forms::substituted(&motive, &name, &at);
            let Some(goal) = goal_after_intros(&goal, introduced) else {
                return Route::no(format!(
                    "an induction part whose lines take off its goal what Lean does not, {}",
                    goal.text()
                ));
            };
            let owing = Owing::Lean {
                nodes: block.ends_written(*part),
                goal: vec![goal],
            };
            let closing = match self.closing(children.last().copied(), owing) {
                Route::Built(c) => c,
                Route::Declined(d) => return Route::Declined(d),
            };
            self.close(depth + 1, closing, step.line, spot.clone());
        }
        Route::Built(())
    }

    /// `induction on Y starting at ∅` of "for all Y ⊆ X": the parts of a
    /// finite X, `LeanBridges.Sets.subset_induction`, X's finiteness from
    /// why it is (`finite_proof`). The base is ∅; the step lets Y ⊆ X,
    /// assumes the claim of Y under the page's label, and opens its own
    /// lines, a ∈ X ∖ Y, before proving it of Y ∪ {a}.
    fn subset_induction(
        &mut self,
        step: &Step,
        block: &crate::checker::record::Block,
        claimed: &Node,
        parts: &[Option<usize>],
        depth: usize,
    ) -> Route<()> {
        use super::tactics as t;
        let spot = Self::step_spot(step);
        let ([letter, set, body], crate::notations::FOR_ALL) =
            (claimed.children.as_slice(), claimed.notation())
        else {
            return Route::no("an induction on a set whose claim says no \"for all\"");
        };
        let ("powerset", [whole]) = (&*set.notation_name(), set.children.as_slice())
        else {
            return Route::no("an induction on a set of other than the parts of a set");
        };
        let Some(members) = self.writer.members_of(whole) else {
            return Route::no("an induction on the parts of a set of no Lean type");
        };
        let name = super::names::letter(&letter.text);
        self.writer
            .letters
            .insert(letter.text.to_string(), LetterType::Set(members));
        let open =
            || Printed::of(super::doc::TermKind::Open, super::doc::LeanType::Prop);
        // X's finiteness from why the checker says it is (`finite_proof`);
        // `parley_finite` where the reason names nothing to write it from.
        let finite = self.finite_proof(whole).unwrap_or_else(|| {
            t::by_term(super::doc::Proof::By(t::bridge(
                BridgeTactic::Finite,
                vec![],
            )))
        });
        let induction = Printed::applied(
            "LeanBridges.Sets.subset_induction",
            super::doc::Source::Bridge(BridgeModule::Sets),
            vec![finite, open(), open()],
            super::doc::LeanType::Prop,
        );
        self.push_at(
            depth,
            t::call("refine", vec![TacticArg::Term(induction)]),
            step.line,
            spot.clone(),
        );
        // Each part starts from the lines in scope as the induction found
        // them, as `induction`'s parts do.
        let kept_lines = self.trees.clone();
        for part in parts {
            self.trees = kept_lines.clone();
            let marker = part
                .and_then(|k| step.parts.get(k))
                .map(|(m, _)| m.as_str())
                .unwrap_or("");
            let openers: Vec<crate::corpus::Opener> = step
                .openers
                .iter()
                .filter(|o| o.part == *part)
                .cloned()
                .collect();
            let first = match marker {
                "base" => t::call("skip", vec![]),
                "step" => {
                    let guard = openers
                        .iter()
                        .find(|o| self.lets_part_letter(o, &letter.text))
                        .cloned();
                    let hypothesis = openers.iter().find(|o| o.is_hypothesis).cloned();
                    let (Some(guard), Some(hypothesis)) = (guard, hypothesis) else {
                        return Route::no(
                            "an induction step on a set with no letter or hypothesis",
                        );
                    };
                    let (guard_name, ih_name) =
                        (line_name(&guard.label), line_name(&hypothesis.label));
                    if let Some(n) = self.opener_node(&guard) {
                        self.named
                            .insert(guard.label.clone(), vec![guard_name.clone()]);
                        self.store(
                            guard.label.clone(),
                            vec![LineSentence::only(n, guard_name.clone())],
                        );
                    }
                    self.named
                        .insert(hypothesis.label.clone(), vec![ih_name.clone()]);
                    self.store(
                        hypothesis.label.clone(),
                        vec![LineSentence::only(body.clone(), ih_name.clone())],
                    );
                    Tactic::Intro(vec![name.clone(), guard_name, ih_name])
                }
                other => return Route::no(format!("an induction part {other:?}")),
            };
            self.push_at(
                depth,
                Tactic::Bullet(Box::new(first)),
                step.line,
                spot.clone(),
            );
            let own: Vec<crate::corpus::Opener> = openers
                .into_iter()
                .filter(|o| !o.is_hypothesis && !self.lets_part_letter(o, &letter.text))
                .collect();
            if let Route::Declined(d) = self.open_lines(step, &own, depth + 1) {
                return Route::Declined(d);
            }
            let children: Vec<usize> = block
                .children
                .iter()
                .copied()
                .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                .collect();
            // The base's ∅ is the part of X the letter was: a set of what
            // X holds, ∏(x ∈ ∅) c of members of X.
            let empty_was = self.writer.empty_of.clone();
            if marker == "base" {
                self.writer.empty_of = self.writer.members_of(whole);
            }
            let written = self.steps(&children, depth + 1);
            self.writer.empty_of = empty_was;
            if let Route::Declined(d) = written {
                return Route::Declined(d);
            }
            let closing = match self.closing(
                children.last().copied(),
                Owing::Written(block.ends_written(*part)),
            ) {
                Route::Built(c) => c,
                Route::Declined(d) => return Route::Declined(d),
            };
            self.close(depth + 1, closing, step.line, spot.clone());
        }
        Route::Built(())
    }

    /// Whether an opening line lets the letter of an induction on parts,
    /// `Y ⊆ X`.
    fn lets_part_letter(&self, o: &crate::corpus::Opener, letter: &str) -> bool {
        !o.is_hypothesis
            && self.opener_node(o).is_some_and(|n| {
                &*n.notation_name() == "subset"
                    && n.children.first().is_some_and(|y| &*y.text == letter)
            })
    }

    /// A function or map given a letter of "for all f : X → Y": the value
    /// as Lean writes it, where it is of the type the quantifier gives f.
    fn function_given(
        &self,
        writer: &Writer,
        value: &Node,
        from: &Node,
        to: &Node,
    ) -> Route<Printed> {
        match writer.function_between(from, to) {
            Some(LetterType::Function { from, to }) => {
                match writer.function_type(value) {
                    Route::Built(t) if t == (from, to) => {
                        Route::Built(writer.function_printed(value))
                    }
                    Route::Built(_) => {
                        Route::no("a function given for one of other types")
                    }
                    Route::Declined(d) => Route::Declined(d),
                }
            }
            Some(wanted @ LetterType::Map { .. }) => {
                match writer.letters.get(&*value.text) {
                    Some(ty) if value.is_name() && *ty == wanted => {
                        Route::Built(Printed::letter(
                            super::names::letter(&value.text),
                            ty.lean_type(),
                        ))
                    }
                    _ => Route::no("a map given for one of other types"),
                }
            }
            _ => Route::no("a function given between sets of no Lean type"),
        }
    }

    /// What an opening line says, as the checker read it.
    fn opener_node(&self, o: &crate::corpus::Opener) -> Option<Node> {
        o.body(&self.thm.path)
            .sentences()
            .first()
            .and_then(|s| self.rec.page.get(s))
            .cloned()
    }

    /// Whether an opening line is the `let` of a letter, the induction's.
    fn introduces_letter(&self, o: &crate::corpus::Opener, letter: &str) -> bool {
        o.kind == Intro::Let
            && o.body(&self.thm.path)
                .sentences()
                .iter()
                .filter_map(|s| self.rec.page.get(s))
                .any(|n| introduces(n).is_some_and(|(l, _)| l == letter))
    }

    /// The lines that open a `proof` or `contradiction` block: each `let`
    /// introduces its letter, each `assume` its fact, and a `suppose` the
    /// opposite of the claim.
    fn open(&mut self, step: &Step, part: Option<usize>, depth: usize) -> Route<()> {
        let openers: Vec<crate::corpus::Opener> = step
            .openers
            .iter()
            .filter(|o| o.part == part)
            .cloned()
            .collect();
        self.open_lines(step, &openers, depth)
    }

    /// The opening lines given, each introduced as `open` introduces it.
    fn open_lines(
        &mut self,
        step: &Step,
        openers: &[crate::corpus::Opener],
        depth: usize,
    ) -> Route<()> {
        let spot = Self::step_spot(step);
        for o in openers {
            let label = line_name(&o.label);
            self.named.insert(o.label.clone(), vec![label.clone()]);
            let body = o.body(&self.thm.path);
            let mut nodes: Vec<Node> = body
                .sentences()
                .iter()
                .filter_map(|s| self.rec.page.get(s).cloned())
                .collect();
            // A `let` the page does not read as a formula, `let X ⊆ A`, says
            // what the checker reads it to assert.
            if nodes.is_empty() {
                nodes = self
                    .rec
                    .opener_asserted
                    .get(&o.line)
                    .cloned()
                    .unwrap_or_default();
            }
            match o.kind {
                Intro::Let => {
                    for node in &nodes {
                        if let Some(letter) = super::statement::range_letter(node) {
                            // In ℕ or ℕ₀ where the range starts at 1 or 0.
                            let system = match node.children.get(1) {
                                Some(range) => super::expr::range_letter_system(range),
                                None => super::expr::System::Type(
                                    super::templates::Num::Int,
                                ),
                            };
                            self.writer.introduce(&letter, system);
                            let letter = super::names::letter(&letter);
                            self.store(
                                o.label.clone(),
                                vec![LineSentence::only(node.clone(), label.clone())],
                            );
                            self.intro(
                                depth,
                                vec![letter.clone(), label.clone()],
                                o.line,
                                &spot,
                            );
                            // The range as the page writes it: an
                            // induction's step leaves its end `↑(N + 1)`,
                            // which the page writes N + 1 and an item is
                            // given so, and Lean matching the one with the
                            // other unfolds the range past its limit.
                            self.push_at(
                                depth,
                                Tactic::Try(Box::new(super::tactics::push_cast(Some(
                                    TacticArg::At(vec![
                                        super::doc::Location::Hypothesis(label.clone()),
                                    ]),
                                )))),
                                o.line,
                                spot.clone(),
                            );
                            // The range's bounds beside it, which linear
                            // arithmetic reads, the membership kept for the
                            // items given it; a claim may state the bounds
                            // already.
                            let bounds = Printed::applied(
                                "Finset.mem_Icc.mp",
                                super::doc::Source::Mathlib,
                                vec![super::tactics::hyp(&label)],
                                super::doc::LeanType::Prop,
                            );
                            self.push_at(
                                depth,
                                Tactic::Try(Box::new(Tactic::Name {
                                    name: format!("{label}_bounds"),
                                    term: bounds,
                                })),
                                o.line,
                                spot.clone(),
                            );
                            continue;
                        }
                        if let Some((letter, ty)) =
                            super::statement::introduces_function(node)
                        {
                            self.writer.letters.insert(letter.clone(), ty);
                            self.intro(
                                depth,
                                vec![super::names::letter(&letter)],
                                o.line,
                                &spot,
                            );
                            continue;
                        }
                        // `let f : X → Y` between sets: the map and the fact
                        // that it maps X into Y, as "for all f : X → Y" gives
                        // them (`quantified_over_functions`).
                        if let (crate::notations::FUNCTION_TYPE, [f, from, to]) =
                            (node.notation(), node.children.as_slice())
                        {
                            if let (true, Some(ty)) =
                                (f.is_name(), self.writer.function_between(from, to))
                            {
                                self.writer.letters.insert(f.text.to_string(), ty);
                                self.store(
                                    o.label.clone(),
                                    vec![LineSentence::only(
                                        node.clone(),
                                        label.clone(),
                                    )],
                                );
                                self.intro(
                                    depth,
                                    vec![super::names::letter(&f.text), label.clone()],
                                    o.line,
                                    &spot,
                                );
                                continue;
                            }
                        }
                        // `let t ∈ S` of a set S: the member and the fact
                        // that it is one, as "for all t ∈ S" gives them.
                        // `let X ⊆ A` likewise gives a set and the fact.
                        if let [t, set] = node.children.as_slice() {
                            let member = node.notation()
                                == crate::notations::MEMBERSHIP
                                && t.is_name();
                            let part =
                                &*node.notation_name() == "subset" && t.is_name();
                            let ty = match (member, part) {
                                (true, _) => {
                                    self.writer.members_of(set).map(|m| m.letter())
                                }
                                (_, true) => {
                                    self.writer.set_members(set).map(LetterType::Set)
                                }
                                _ => None,
                            };
                            if let Some(ty) = ty {
                                self.writer.letters.insert(t.text.to_string(), ty);
                                self.store(
                                    o.label.clone(),
                                    vec![LineSentence::only(
                                        node.clone(),
                                        label.clone(),
                                    )],
                                );
                                self.intro(
                                    depth,
                                    vec![super::names::letter(&t.text), label.clone()],
                                    o.line,
                                    &spot,
                                );
                                continue;
                            }
                        }
                        let Some((letter, system)) = introduces(node) else {
                            return Route::no(
                                "a let that introduces no letter of a number system",
                            );
                        };
                        self.writer.introduce(&letter, system);
                        let letter = super::names::letter(&letter);
                        if !matches!(system, super::expr::System::Type(_)) {
                            self.store(
                                o.label.clone(),
                                vec![LineSentence::only(node.clone(), label.clone())],
                            );
                            self.intro(
                                depth,
                                vec![letter.clone(), label.clone()],
                                o.line,
                                &spot,
                            );
                        } else {
                            self.intro(depth, vec![letter.clone()], o.line, &spot);
                        }
                    }
                }
                Intro::Assume => {
                    // A line of several sentences is the "and" of them,
                    // each sentence taken by its projection.
                    let n = nodes.len();
                    let said = nodes
                        .iter()
                        .enumerate()
                        .map(|(k, node)| LineSentence {
                            at: k,
                            node: node.clone(),
                            name: None,
                            proof: fields(
                                super::tactics::hyp(&label),
                                &projection_path(k, n),
                            ),
                            says: None,
                        })
                        .collect();
                    self.store(o.label.clone(), said);
                    self.intro(depth, vec![label.clone()], o.line, &spot);
                }
                Intro::Suppose => {
                    let Some(node) = nodes.first() else {
                        return Route::no("a suppose the checker did not read");
                    };
                    let says = match self.writer.formula(node) {
                        Route::Built(s) => s,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    self.store(
                        o.label.clone(),
                        vec![LineSentence::only(node.clone(), label.clone())],
                    );
                    if let Route::Declined(d) =
                        self.suppose(&label, says, o.line, &spot, depth)
                    {
                        return Route::Declined(d);
                    }
                }
            }
        }
        Route::Built(())
    }

    /// A contradiction's `suppose` line, named `label`: the claim denied,
    /// `by_contra`, where the supposition is the claim negated, and the
    /// negation's body taken, `intro`, where the claim is the supposition
    /// negated. The hypothesis is the supposition as the page writes it:
    /// named as it comes where Lean writes the two alike, ascribed where
    /// they differ by a `≠` read as `¬ =`, and turned round where the page
    /// writes its equation the other way.
    fn suppose(
        &mut self,
        label: &str,
        says: Printed,
        line: usize,
        spot: &Spot,
        depth: usize,
    ) -> Route<()> {
        use super::doc::forms::{self, Meets};
        use super::doc::LeanType;
        let Some(supposition) = self.rec.supposed.get(&line) else {
            return Route::no("a supposition the checker relates to no claim");
        };
        let shown = match self.writer.formula(&supposition.against) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let (open, given) = match supposition.shape {
            Supposed::ClaimDenied => ("by_contra", Some(forms::negation(&shown))),
            Supposed::Denial => ("intro", forms::denied(&shown)),
        };
        let Some(given) = given else {
            return Route::no(format!(
                "a claim that denies its supposition, which Lean writes as no negation, {}",
                shown.text()
            ));
        };
        let opening =
            |name: Printed| super::tactics::call(open, vec![TacticArg::Term(name)]);
        // How the supposition meets what the block denies is the checker's
        // (`Supposition::meeting`); Lean's own writing of the two decides
        // only whether the hypothesis is ascribed the page's words.
        let met = &supposition.meeting;
        if met.permuted || !met.identities.is_empty() {
            return Route::no(format!(
                "the supposition {}, met with what `{open}` gives, {}, as {met:?}",
                says.text(),
                given.text()
            ));
        }
        let shape = match (met.turned, forms::written_alike(&given, &says)) {
            (true, _) => Some(Meets::Turned {
                negated: forms::denies_equation(&given),
            }),
            (false, true) => Some(Meets::Same),
            (false, false) => Some(Meets::Unfolded),
        };
        match shape {
            Some(Meets::Same) => {
                self.push_at(
                    depth,
                    opening(super::tactics::hyp(label)),
                    line,
                    spot.clone(),
                );
            }
            Some(Meets::Unfolded) => {
                let given = ascribed(super::tactics::hyp(label), says);
                self.push_at(depth, opening(given), line, spot.clone());
            }
            Some(Meets::Turned { negated }) => {
                let given_name = format!("h_{label}");
                let given = super::tactics::hyp(&given_name);
                let turned = match negated {
                    false => super::tactics::symm(given),
                    true => Printed::applied(
                        "Ne.symm",
                        super::doc::Source::Core,
                        vec![given],
                        LeanType::Prop,
                    ),
                };
                self.push_at(
                    depth,
                    opening(super::tactics::hyp(&given_name)),
                    line,
                    spot.clone(),
                );
                self.push_at(
                    depth,
                    Tactic::Have {
                        name: label.to_string(),
                        says,
                        proof: Box::new(super::doc::Proof::Term(turned)),
                    },
                    line,
                    spot.clone(),
                );
            }
            Some(Meets::Identities(_) | Meets::Ranges | Meets::Casts { .. }) | None => {
                return Route::no(format!(
                    "the supposition {}, which is not what `{open}` gives, {}",
                    says.text(),
                    given.text()
                ))
            }
        }
        Route::Built(())
    }
}

/// What an `obtain` takes its witnesses from: the Lean term that proves the
/// "there is", and the "there is" itself.
struct Obtained {
    term: Printed,
    says: Node,
    /// What the cited item's letters stand for, the Y of "there is s ∈ Y"
    /// given ℕ; empty for a line of the proof, which writes its own sets.
    binding: crate::matching::Binding,
    /// The "there is" as Lean states it at the item's values, which the
    /// `obtain` takes apart; None of a line of the proof, which the writer
    /// states itself.
    lean: Option<Printed>,
}

/// A cited line as a step uses it: the name to use, and the `have` that
/// casts it up to the claim's type where it is narrower.
struct Widened {
    have: Option<Tactic>,
    /// The line as the claim's type has it: the line itself, or the name
    /// of its widened copy.
    name: Printed,
}

/// `congrArg (fun x : A => (x : B)) e`: the equation e of A mapped into B.
fn cast_up(
    writer: &Writer,
    own: super::templates::Num,
    wanted: super::templates::Num,
    equation: Printed,
) -> Printed {
    let x = Printed::cast(super::tactics::hyp("x"), writer.num_type(wanted));
    Printed::applied(
        "congrArg",
        super::doc::Source::Core,
        vec![lambda("x", writer.num_type(own), x), equation],
        super::doc::LeanType::Prop,
    )
}

/// How a statement Lean derives meets the claim (`Proof::powers_met`).
enum PowersMet {
    /// Apart only in powers, converted by this proof.
    Converted(Box<super::doc::Proof>),
    /// Alike in every form the writer chose.
    Alike,
    /// Apart otherwise.
    Apart,
}

/// Whether the place at `path` in `start` is a power's exponent, the second
/// child of a `POWER`.
fn place_is_exponent(start: &Node, path: &[usize]) -> bool {
    let Some((&last, up)) = path.split_last() else {
        return false;
    };
    last == 1
        && at_path(start, up).is_some_and(|n| n.notation() == crate::notations::POWER)
}

/// `have name : says := by have h := ↑proof; push_cast at h; linear_combination
/// h`: an equation proved in `from` stated in the wider `to`, cast up and its
/// casts pushed in. `norm_cast` does not take a sum of rationals to the
/// reals, which this does.
fn widening_have(
    writer: &Writer,
    name: &str,
    says: Printed,
    from: super::templates::Num,
    to: super::templates::Num,
    proof: Printed,
) -> Tactic {
    use super::tactics as t;
    Tactic::Have {
        name: name.to_string(),
        says,
        proof: Box::new(super::doc::Proof::By(Tactic::Seq(vec![
            t::name_h(&cast_up(writer, from, to, proof)),
            t::push_cast(Some(t::at_h(false))),
            t::linear_combination(t::hyp("h")),
        ]))),
    }
}

/// A proof with these tactics before it, inside its `by`: a block of them
/// and then the proof's own tactic, each line indented under the `by`.
fn haves_then(haves: Vec<Tactic>, proof: super::doc::Proof) -> super::doc::Proof {
    use super::doc::Proof;
    if haves.is_empty() {
        return proof;
    }
    let mut lines = haves;
    match proof {
        Proof::By(t) => lines.push(t),
        Proof::Term(t) => lines.push(Tactic::Exact(t)),
        Proof::Block(ts) => lines.extend(ts),
    }
    Proof::Block(lines)
}

/// A claim `s ∈ S`, S ℤ, ℚ or ℝ and s of a wider type, shown by an
/// equation, `name`, one side of which is in S already: that side is the
/// witness, and the equation, with the casts pushed in, its proof. None
/// where the claim or the equation is not so.
fn member_by_equation(
    writer: &Writer,
    equation: &Node,
    name: &Printed,
    claim: &Node,
    ctx: &crate::matching::Context,
) -> Option<super::doc::Proof> {
    let [term, set] = claim.children.as_slice() else {
        return None;
    };
    if claim.notation() != crate::notations::MEMBERSHIP
        || set.notation() != crate::notations::NUMBER_SYSTEMS
        || equation.notation() != EQUALITY
    {
        return None;
    }
    let super::expr::System::Type(n) = super::expr::system_of(set)? else {
        return None;
    };
    if writer.carrier(term).built()? <= n {
        return None;
    }
    // The equation is of the claim's term: a = 1 shows nothing of √b + 1.
    if !equation
        .children
        .iter()
        .any(|side| crate::matching::alike_top(side, term, ctx))
    {
        return None;
    }
    equation.children.iter().enumerate().find_map(|(at, side)| {
        let fits = writer.carrier(side).built().is_some_and(|c| c <= n);
        if !fits || side.names().is_empty() && !writer.is_number(side) {
            return None;
        }
        let w = writer.number_fixed(side, n).built()?;
        // The witness `w` is the equation's side at `at`: the equation is
        // `↑w = s` as it stands where it is the left, turned where the
        // right; `exact_mod_cast` reads both with their casts moved alike.
        let faced = match at {
            0 => name.clone(),
            _ => super::tactics::symm(super::tactics::bracket(name.clone())),
        };
        let proof = super::tactics::by_term(super::doc::Proof::By(
            super::tactics::exact_mod_cast(faced),
        ));
        Some(super::doc::Proof::Term(super::expr::anonymous(vec![
            w, proof,
        ])))
    })
}

/// A witness as Lean writes it, and the tactic that puts what a line says
/// of it in scope, where it is an integer a line gives.
struct Witness {
    term: Printed,
    known: Option<Tactic>,
}

/// `by parley_side` as a term, after the tactics that put what lines say
/// of the witnesses before it in scope.
fn side_term(known: &[Tactic]) -> Printed {
    let mut tactics = known.to_vec();
    tactics.push(super::tactics::bridge(BridgeTactic::Side, vec![]));
    let tactic = match <[Tactic; 1]>::try_from(tactics) {
        Ok([one]) => one,
        Err(all) => Tactic::Seq(all),
    };
    super::tactics::by_term(super::doc::Proof::By(tactic))
}

/// A define a step cites: its letter, the term it names, and the Lean name
/// of its equation.
struct CitedDefine {
    name: Node,
    value: Node,
    proof: String,
    /// The argument of a function's define, the j of q(j) = F(j)², which
    /// each application q(a) puts a for; None for a define of a term.
    param: Option<String>,
}

/// The tactic lines that write the defines out at `at`, the lines the step
/// uses and the goal (`Proof::rewritten_at`), and push in the casts that
/// leaves; none where no define is cited.
fn written_out(defines: &[CitedDefine], at: &[super::doc::Location]) -> Vec<Tactic> {
    use super::tactics as t;
    if defines.is_empty() {
        return Vec::new();
    }
    let there = || TacticArg::At(at.to_vec());
    let rewrites = defines
        .iter()
        .map(|d| t::forwards(t::hyp(&d.proof)))
        .collect();
    vec![
        Tactic::Try(Box::new(t::simp_only(false, None, rewrites, Some(there())))),
        Tactic::Try(Box::new(t::push_cast(Some(there())))),
    ]
}

/// `node` with `to` put for each part that is `from`, the two compared as
/// the grammar prints them.
/// Whether putting one side of `equation` for the other in the left side of
/// `claim`, an equation, gives its right side.
fn makes_claim(
    equation: &Node,
    claim: &Node,
    grammar: &crate::formula::Grammar,
) -> bool {
    let (Some([from, to]), Some([left, right])) = (
        equation.children.as_slice().first_chunk::<2>(),
        claim.children.as_slice().first_chunk::<2>(),
    ) else {
        return false;
    };
    let want = grammar.print(right);
    [(from, to), (to, from)]
        .iter()
        .any(|(a, b)| grammar.print(&put_term(left, a, b, grammar)) == want)
}

fn put_term(
    node: &Node,
    from: &Node,
    to: &Node,
    grammar: &crate::formula::Grammar,
) -> Node {
    if grammar.print(node) == grammar.print(from) {
        return to.clone();
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| put_term(c, from, to, grammar))
            .collect(),
    )
}

/// `node` with `value` put for each place the letter `name` stands.
fn put_for(node: &Node, name: &Node, value: &Node) -> Node {
    if node.is_name() && node.text == name.text {
        return value.clone();
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| put_for(c, name, value))
            .collect(),
    )
}

/// How many statements an "or" joins, however it groups them.
fn disjuncts(node: &Node) -> usize {
    if node.notation() == crate::notations::DISJUNCTION {
        node.children.iter().map(disjuncts).sum()
    } else {
        1
    }
}

/// An `rcases` pattern for an "or" as its tree groups it, each disjunct
/// named in turn from `names`: `(C1 | C2) | C3` for (a ∨ b) ∨ c.
fn or_pattern(
    node: &Node,
    names: &mut std::slice::Iter<'_, String>,
) -> super::doc::Pattern {
    use super::doc::Pattern;
    if let ([left, right], crate::notations::DISJUNCTION) =
        (node.children.as_slice(), node.notation())
    {
        let l = or_pattern(left, names);
        let r = or_pattern(right, names);
        return Pattern::Or(Box::new(l), Box::new(r));
    }
    Pattern::Name(names.next().cloned().unwrap_or_else(|| "_".to_string()))
}

/// The cases as one "or", each bracketed: `(a) ∨ (b) ∨ (c)`.
fn cases_said(cases: Vec<Printed>) -> Printed {
    let bracketed = cases.into_iter().map(super::tactics::bracket).collect();
    match super::doc::Op::of("∨").and_then(|or| super::expr::joined(or, bracketed, 0))
    {
        Some(all) => all,
        None => Printed::truth(),
    }
}

/// The cases named in turn, read from the right: `a | b | c`.
fn cases_pattern(names: &[String]) -> super::doc::Pattern {
    use super::doc::Pattern;
    match names {
        [] => Pattern::Name("_".to_string()),
        [one] => Pattern::Name(one.clone()),
        [first, rest @ ..] => Pattern::Or(
            Box::new(Pattern::Name(first.clone())),
            Box::new(cases_pattern(rest)),
        ),
    }
}

/// The lines a step cites anywhere in its reason: its own references, the
/// line it substitutes into, and those its calculation's rows cite, by a
/// reason of their own or alone.
fn step_cited_refs(step: &crate::corpus::Step, path: &str) -> Vec<String> {
    let mut out: Vec<String> = step.just.refs.clone();
    let into = |j: &Justification| j.into.as_ref().map(|p| p.named().to_string());
    out.extend(into(&step.just));
    if let Some(Ok(chain)) = crate::corpus::proof::chain(&step.just, path) {
        for line in &chain.lines {
            match &line.reason {
                Some(r) => {
                    if let Ok(by) = &r.by {
                        out.extend(by.refs.iter().cloned());
                        out.extend(into(by));
                    }
                }
                None => {
                    if let Some(cited) = crate::corpus::proof::chain_cited(&line.cite) {
                        out.push(cited);
                    }
                }
            }
        }
    }
    let mut seen = std::collections::BTreeSet::new();
    out.retain(|r| seen.insert(r.clone()));
    out
}

/// The child indices that lead from `node` to a part of the shape of `part`,
/// the first in the tree's order; None where there is none.
fn path_to(node: &Node, part: &Node) -> Option<Vec<usize>> {
    if node.spelt_alike(part) {
        return Some(Vec::new());
    }
    node.children.iter().enumerate().find_map(|(i, c)| {
        let mut rest = path_to(c, part)?;
        rest.insert(0, i);
        Some(rest)
    })
}

/// The part of `node` the child indices lead to; None where they lead off
/// the tree.
fn at_path<'n>(node: &'n Node, path: &[usize]) -> Option<&'n Node> {
    match path.split_first() {
        None => Some(node),
        Some((i, rest)) => at_path(node.children.get(*i)?, rest),
    }
}

/// Whether the node is the function `f` applied at the letter `k`, N(k).
fn applied_at(node: &Node, f: &str, k: &str) -> bool {
    match node.children.as_slice() {
        [head, arg] => {
            node.notation() == crate::notations::APPLICATION
                && head.is_name()
                && &*head.text == f
                && arg.is_name()
                && &*arg.text == k
        }
        _ => false,
    }
}

/// A letter for a value no letter of the writer's or `taken` is: v, or w,
/// u, or v with a number.
fn fresh_letter(writer: &Writer, taken: &str) -> String {
    let free = |l: &str| l != taken && !writer.letters.contains_key(l);
    if let Some(l) = ["v", "w", "u"].into_iter().find(|l| free(l)) {
        return l.to_string();
    }
    let mut i = 1;
    loop {
        let l = format!("v{i}");
        if free(&l) {
            return l;
        }
        i += 1;
    }
}

/// A sentence's parts, a conjunction taken apart by Lean's projections,
/// `H3.1` and `H3.2`, as the tree joins them.
fn conjuncts(
    node: &Node,
    proof: Printed,
    says: Option<Printed>,
    out: &mut Vec<super::algebra::Cited>,
) {
    let joined = matches!(
        node.notation(),
        crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION
    );
    if let ([left, right], true) = (node.children.as_slice(), joined) {
        // The statement as stated, taken apart as the tree is; None where it
        // is no "and".
        let (said_left, said_right) = match says.as_ref().and_then(and_sides) {
            Some((l, r)) => (Some(l), Some(r)),
            None => (None, None),
        };
        conjuncts(left, fields(proof.clone(), &["1"]), said_left, out);
        conjuncts(right, fields(proof, &["2"]), said_right, out);
        return;
    }
    out.push(super::algebra::Cited {
        node: node.clone(),
        proof,
        says,
    });
}

/// A claim proved from a term that gives it, as the claim's shape asks:
/// an equation by the ring identity between the two, an order by linear
/// arithmetic, anything else as it stands.
/// A sentence of an item with each property the citation gives by what it
/// says, P := t ↦ …, applied where the sentence applies it: P(u) its body
/// with u's value for t. The item's other letters stay as its statement
/// has them, as Lean's statement of it does.
fn read_at_values(
    node: &Node,
    binding: &crate::matching::Binding,
    binders: &crate::matching::FxIndexMap<
        crate::formula::notation_id::NotationId,
        crate::formula::notation::Binds,
    >,
) -> Node {
    // A property holds of a term, P(x), and a function letter applied to
    // one, t(k): each read as the rule the citation gives the letter,
    // `property-of`, with the term for its letter.
    if let ("holds-of" | "application", [p, arg]) =
        (&*node.notation_name(), node.children.as_slice())
    {
        if let Some(stands) = binding.get(&p.text).filter(|_| p.is_name()) {
            if let ("property-of", [body]) =
                (&*stands.notation_name(), stands.children.as_slice())
            {
                let arg = crate::matching::substitute_apart_by(arg, binding, binders);
                let put = crate::matching::Binding::from([(stands.text, arg)]);
                return crate::matching::substitute_apart_by(body, &put, binders);
            }
        }
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| read_at_values(c, binding, binders))
            .collect(),
    )
}

/// Whether a fact speaks of a letter the claim's leading "for all" binds.
fn bound_in(claim: &Node, fact: &Node) -> bool {
    let mut body = claim;
    let mut bound = Vec::new();
    while let (crate::notations::FOR_ALL, [letter, _, inner]) =
        (body.notation(), body.children.as_slice())
    {
        bound.push(letter.text.to_string());
        body = inner;
    }
    let names = fact.names();
    bound.iter().any(|b| names.iter().any(|n| **n == **b))
}

/// The fact under the claim's leading "for all" binders, x² ≥ 0 as "for
/// all x ∈ [0, 1], x² ≥ 0".
fn under_binders(claim: &Node, fact: &Node) -> Node {
    match (claim.notation(), claim.children.as_slice()) {
        (crate::notations::FOR_ALL, [letter, set, inner]) => claim.with_children(vec![
            letter.clone(),
            set.clone(),
            under_binders(inner, fact),
        ]),
        _ => fact.clone(),
    }
}

/// An `obtain` pattern for a sentence, one name to each part of its "and"
/// as it nests, the names taken in order; a part left with no name is `_`.
fn shaped_pattern(said: &Node, names: &[String]) -> String {
    let and_sides = |n: &Node| match (n.notation(), n.children.as_slice()) {
        (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [l, r],
        ) => Some((l.clone(), r.clone())),
        _ => None,
    };
    match (names, and_sides(said)) {
        ([], _) => "_".to_string(),
        ([one], _) => one.clone(),
        // Each side takes as many names as it has parts, the left as many
        // as it can while the right keeps one: an "and" that is one
        // sentence of the page stays whole.
        (_, Some((l, r))) => {
            let take = conjunct_count(&l).min(names.len() - 1);
            let take = take.max(names.len().saturating_sub(conjunct_count(&r)));
            let (left, right) = names.split_at(take.min(names.len()));
            format!(
                "⟨{}, {}⟩",
                shaped_pattern(&l, left),
                shaped_pattern(&r, right)
            )
        }
        (_, None) => names[0].clone(),
    }
}

/// The parts of `said` an obtain pattern of `count` names takes, in order,
/// split as `shaped_pattern` splits it.
fn shaped_parts(said: &Node, count: usize) -> Vec<Node> {
    match (count, said.notation(), said.children.as_slice()) {
        (0, _, _) => Vec::new(),
        (1, _, _) => vec![said.clone()],
        (
            _,
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [l, r],
        ) => {
            let take = conjunct_count(l).min(count - 1);
            let take = take.max(count.saturating_sub(conjunct_count(r)));
            let take = take.min(count);
            let mut out = shaped_parts(l, take);
            out.extend(shaped_parts(r, count - take));
            out
        }
        _ => vec![said.clone()],
    }
}

/// A sentence an obtain takes under a name of its own, `from`, where Lean
/// states it as `lean` and the page as `says`, stated after as the page
/// says it under its own name.
struct Restated {
    name: String,
    says: Printed,
    from: String,
    lean: Printed,
}

/// How many parts an "and" holds, each "and" in it taken apart.
fn conjunct_count(node: &Node) -> usize {
    match (node.notation(), node.children.as_slice()) {
        (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [l, r],
        ) => conjunct_count(l) + conjunct_count(r),
        _ => 1,
    }
}

/// A proof of a claim said "for all", made of a proof of its body: the
/// letters introduced, then the body's proof. A body proved by a block of
/// tactics on lines of their own, `by` and a line break, takes the `intro`
/// as its first line, at the block's indentation, since a block cannot
/// follow `intro …;` on its line.
fn after_intros(intros: &[String], proof: super::doc::Proof) -> super::doc::Proof {
    use super::doc::Proof;
    let intro = Tactic::Intro(intros.to_vec());
    match proof {
        Proof::Block(mut tactics) => {
            tactics.insert(0, intro);
            Proof::Block(tactics)
        }
        other => Proof::By(Tactic::Seq(vec![intro, tactic_of(&other)])),
    }
}

/// A proof of a claim said of every member of a set, proved of one taken
/// as these letters: `intro` first, inside the proof's `by`.
fn with_intros(intros: &[String], proof: super::doc::Proof) -> super::doc::Proof {
    use super::doc::Proof;
    if intros.is_empty() {
        return proof;
    }
    let intro = Tactic::Intro(intros.to_vec());
    match proof {
        Proof::By(t) => Proof::By(Tactic::Seq(vec![intro, t])),
        Proof::Block(mut ts) => {
            ts.insert(0, intro);
            Proof::Block(ts)
        }
        Proof::Term(t) => Proof::By(Tactic::Seq(vec![intro, Tactic::Exact(t)])),
    }
}

/// A proof as a tactic that closes the goal with it: `(t)` of `by t`,
/// `exact (t)` of a term, `exact (by …)` of a block.
/// A proof written on one line, as a term inside another needs it: a block's
/// tactics joined by `;`, and each `have`'s own tactic proof in brackets, so
/// that it does not take the tactics after it as its own.
fn on_one_line(proof: super::doc::Proof) -> super::doc::Proof {
    use super::doc::Proof;
    match proof {
        Proof::Block(tactics) => Proof::By(Tactic::Seq(
            tactics.into_iter().map(have_bracketed).collect(),
        )),
        other => other,
    }
}

/// A `have` whose proof is tactics, its proof as a bracketed `by` term; any
/// other tactic as it is.
fn have_bracketed(tactic: Tactic) -> Tactic {
    use super::doc::Proof;
    match tactic {
        Tactic::Have { name, says, proof } => {
            let proof = match *proof {
                Proof::Term(t) => Proof::Term(t),
                tactics => Proof::Term(super::tactics::bracket(
                    super::tactics::by_term(on_one_line(tactics)),
                )),
            };
            Tactic::Have {
                name,
                says,
                proof: Box::new(proof),
            }
        }
        other => other,
    }
}

fn tactic_of(proof: &super::doc::Proof) -> Tactic {
    use super::doc::Proof;
    match proof {
        Proof::By(t) => Tactic::Group(Box::new(t.clone())),
        Proof::Term(t) => Tactic::Exact(super::tactics::bracket(t.clone())),
        Proof::Block(_) => Tactic::Exact(super::tactics::bracket(
            super::tactics::by_term(proof.clone()),
        )),
    }
}

/// The proof `by t` of one way, `by first | a | b` of several: the ways a
/// step is closed, tried in order because of `why`.
fn ways_proof(why: ListReason, ways: Vec<Tactic>) -> super::doc::Proof {
    let tactic = match <[Tactic; 1]>::try_from(ways) {
        Ok([one]) => one,
        Err(ways) => super::tactics::first(why, ways),
    };
    super::doc::Proof::By(tactic)
}

/// The ways a claim is closed from `term` (`closers`), tried because of
/// `why`.
fn close(
    why: ListReason,
    writer: &Writer,
    claim: &Node,
    term: Printed,
) -> super::doc::Proof {
    super::doc::Proof::By(super::tactics::first(why, closers(writer, claim, term)))
}

/// Why a cited statement `says` and the claim, both as Lean states them,
/// keep a list: the first of the closer's checks that does not hold of
/// them, in the order the closer asks them.
fn apart(
    claim_node: &Node,
    says: &Printed,
    claim: &Printed,
    values: &super::doc::forms::Values,
    facing: Option<Facing>,
) -> ListReason {
    let types_apart = super::doc::forms::relation_types_apart(says, claim);
    let shaped = matches!(claim_node.notation(), EQUALITY | ORDER);
    if types_apart {
        ListReason::CitedTypesApart
    } else if !shaped {
        ListReason::CitedOtherShape
    } else if to_nat_texts(says) != to_nat_texts(claim) {
        ListReason::CitedToNatApart
    } else if !(super::casts::push_cast_moves_all_in_sides(says)
        && super::casts::push_cast_moves_all_in_sides(claim))
        || (claim_node.notation() == ORDER && cast_texts(says) != cast_texts(claim))
    {
        ListReason::CitedCastsUnmoved
    } else if !same_ring_atoms(says, claim, values) {
        ListReason::CitedAtomsApart
    } else if claim_node.notation() == EQUALITY && facing.is_none() {
        ListReason::CitedFacingUnknown
    } else {
        ListReason::CitedOtherShape
    }
}

/// The cited statement taken with its listed sets in the claim's order: an
/// equation of sets member by member, which takes a listed set in any order
/// and of any size; another relation, a membership or subset of a listed
/// set, read in both as the members' equations it says, which `tauto` takes
/// in any order. Where the claim reads as nothing left to show,
/// `all_goals` runs `tauto` on no goal.
fn reordered(cited: &Printed, equation: bool) -> Tactic {
    use super::tactics as t;
    let h = || t::hyp("h");
    if !equation {
        return t::on_h(
            cited,
            vec![
                t::simp_only(
                    false,
                    None,
                    vec![
                        t::forwards(t::lemma("Set.mem_insert_iff")),
                        t::forwards(t::lemma("Set.mem_singleton_iff")),
                        t::forwards(t::lemma("Set.insert_subset_iff")),
                        t::forwards(t::lemma("Set.singleton_subset_iff")),
                    ],
                    Some(t::at_h(true)),
                ),
                Tactic::AllGoals(Box::new(t::call("tauto", vec![]))),
            ],
        );
    }
    let x = t::hyp("x");
    let applied = Printed {
        kind: super::doc::TermKind::App {
            head: Box::new(h()),
            args: vec![super::doc::Arg::Explicit(x.clone())],
            explicit: false,
        },
        ty: None,
    };
    t::on_h(
        cited,
        vec![
            t::call("ext", vec![TacticArg::Term(x)]),
            t::call(
                "rw",
                vec![t::rules(vec![t::lemma("Set.ext_iff")]), t::at_h(false)],
            ),
            t::call("specialize", vec![TacticArg::Term(applied)]),
            t::simp_only(
                false,
                None,
                vec![
                    t::forwards(t::lemma("Set.mem_insert_iff")),
                    t::forwards(t::lemma("Set.mem_singleton_iff")),
                ],
                Some(t::at_h(true)),
            ),
            t::call("tauto", vec![]),
        ],
    )
}

/// `parley_subst e`: the equation e put into the goal.
fn subst_by(equation: &Printed) -> Tactic {
    use super::tactics as t;
    t::bridge(BridgeTactic::Subst, vec![TacticArg::Term(equation.clone())])
}

/// `parley_put_at e h` or `parley_subst_at e h`: the equation e put into
/// the line h.
fn put_into(tactic: BridgeTactic, equation: &Printed, into: &Printed) -> Tactic {
    super::tactics::bridge(
        tactic,
        vec![
            TacticArg::Term(equation.clone()),
            TacticArg::Term(into.clone()),
        ],
    )
}

/// An exponent the record shows at least 0, as Lean writes it, and the proof
/// of `0 ≤ e` (`nonneg_proof`).
#[derive(Clone, Debug)]
struct NonNegative {
    exponent: Printed,
    proof: Printed,
}

/// The parts of what a "there is" says of its letters, as Lean states the
/// "there is", `statement`: each letter it binds taken off with its guard,
/// in order, and given the name the obtain gives it, `obtained`, and what is
/// said of them taken apart at `∧`. Empty where `statement` binds no letter.
fn lean_body_parts(statement: &Printed, obtained: &[String]) -> Vec<Printed> {
    use super::doc::{Quant, TermKind};
    fn unbracketed(t: &Printed) -> &Printed {
        match &t.kind {
            TermKind::Paren(inner) => unbracketed(inner),
            _ => t,
        }
    }
    fn and_parts(t: &Printed, out: &mut Vec<Printed>) {
        match and_sides(t) {
            Some((lhs, rhs)) => {
                and_parts(&lhs, out);
                and_parts(&rhs, out);
            }
            None => out.push(unbracketed(t).clone()),
        }
    }
    let mut given = std::collections::BTreeMap::new();
    let mut at = statement;
    while let TermKind::Quantified {
        quant: Quant::Exists,
        letter,
        letter_ty,
        body,
        ..
    } = &unbracketed(at).kind
    {
        let Some(name) = obtained.get(given.len()) else {
            return Vec::new();
        };
        given.insert(
            letter.clone(),
            Printed::letter(super::names::letter(name), letter_ty.clone()),
        );
        at = body;
    }
    if given.is_empty() {
        return Vec::new();
    }
    let mut parts = Vec::new();
    and_parts(at, &mut parts);
    parts.iter().map(|p| p.substituted(&given)).collect()
}

/// A set as Lean writes it, with the proof that it is finite
/// (`finite_proof`).
#[derive(Clone, Debug)]
struct ShownFinite {
    set: Printed,
    proof: Printed,
}

/// A page term with the proof that it is at least 0, from a hypothesis of a
/// cited item the checker found supplied.
#[derive(Clone, Debug)]
struct ShownWhole {
    term: Node,
    proof: Printed,
}

/// The term and the system of a membership of ℕ or ℕ₀, `t ∈ ℕ₀`; None of
/// any other sentence.
fn membership_of_whole(sentence: &Node) -> Option<(&Node, crate::rules::System)> {
    use crate::rules::System;
    let [term, set] = sentence.children.as_slice() else {
        return None;
    };
    if sentence.notation() != crate::notations::MEMBERSHIP
        || set.notation() != crate::notations::NUMBER_SYSTEMS
    {
        return None;
    }
    let system = System::of_sign(&set.text)?;
    matches!(system, System::N | System::N0).then_some((term, system))
}

/// Whether a statement, its functions applied (`forms::beta_reduced`), takes
/// a numeral to ℕ, `(0 : ℤ).toNat` of `fun k => y ^ k.toNat` at 0.
fn leaves_numeral_to_nat(term: &Printed) -> bool {
    use super::doc::TermKind;
    super::doc::forms::beta_reduced(term).walk().iter().any(|t| {
        matches!(&t.kind, TermKind::ToNat(inner)
            if super::casts::as_natural(inner).is_some()
                && matches!(&super::doc::forms::ascriptions_dropped(inner).kind, TermKind::Numeral(_)))
    })
}

/// What a citation's conversion rewrites (`forms_converted`).
struct Conversion<'a> {
    /// Each finite set the two count, with why it is finite: its count in
    /// ℕ∞ written as its count in ℕ.
    finite: &'a [ShownFinite],
    /// Each exponent at least 0, with why: the integer power written as the
    /// natural power to its `toNat`.
    whole: &'a [NonNegative],
    /// Each power under a sum whose exponent names its letter, converted for
    /// each letter in the sum's range.
    bound: &'a [super::doc::forms::BoundPower],
    /// An integer power of a natural number cast up, `a ^ (k : ℤ)`, written
    /// as the natural power `a ^ k` (`zpow_natCast`).
    cast_powers: bool,
    /// The rewrites of the identity elements the checker dropped meeting the
    /// two (`Cited::meetings`), `sub_zero` of x − 0.
    identities: &'a [&'static str],
    /// A numeral's `toNat` the reading leaves, `(0 : ℤ).toNat`, worked out
    /// (`Int.reduceToNat`).
    numeral_to_nat: bool,
}

/// A citation whose item writes a term in one form and the claim in the
/// other, each form one the writer chose under a fact the record gives:
/// `(have h := t; simp only [← Set.Finite.cast_ncard_eq (p : S.Finite),
/// parley_zpow_toNat (n := e) (h := q)] at h ⊢; exact_mod_cast h)`. Each
/// count in ℕ∞ of a finite S is written as its count in ℕ, and each integer
/// power `a ^ e` of an e at least 0 as the natural power `a ^ e.toNat`,
/// after which the two differ only by casts; `h.symm` where the claim is
/// the item's equation turned round (`Conversion` says what is converted).
fn forms_converted(cited: &Printed, c: &Conversion, turned: bool) -> super::doc::Proof {
    use super::tactics as t;
    let Conversion {
        finite,
        whole,
        bound,
        cast_powers,
        identities,
        numeral_to_nat,
    } = c;
    let powers = whole.iter().map(|w| {
        t::forwards(Printed {
            kind: super::doc::TermKind::App {
                head: Box::new(t::bridge_lemma(
                    "parley_zpow_toNat",
                    BridgeModule::PowerTactics,
                )),
                args: vec![
                    super::doc::Arg::Named {
                        name: "n".to_string(),
                        value: w.exponent.clone(),
                    },
                    super::doc::Arg::Named {
                        name: "h".to_string(),
                        value: w.proof.clone(),
                    },
                ],
                explicit: false,
            },
            ty: Some(super::doc::LeanType::Prop),
        })
    });
    let rules = finite
        .iter()
        .map(|ShownFinite { set, proof }| {
            // Told its type, `({a} : Set α)`, as the count writes it.
            let typed = match &set.ty {
                Some(ty) => Printed::cast(set.clone(), ty.clone()),
                None => t::bracket(set.clone()),
            };
            let says = Printed::of(
                super::doc::TermKind::Field {
                    inner: Box::new(typed),
                    field: "Finite".to_string(),
                },
                super::doc::LeanType::Prop,
            );
            let proof = ascribed(proof.clone(), says);
            t::backwards(Printed::applied(
                "Set.Finite.cast_ncard_eq",
                super::doc::Source::Mathlib,
                vec![t::bracket(proof)],
                super::doc::LeanType::Prop,
            ))
        })
        .chain(powers)
        .chain(cast_powers.then(|| t::forwards(t::lemma("zpow_natCast"))))
        .chain((0..bound.len()).map(|k| t::forwards(t::hyp(&format!("hb{}", k + 1)))))
        .chain(identities.iter().map(|l| t::forwards(t::lemma(l))))
        .chain(numeral_to_nat.then(|| t::forwards(t::lemma("Int.reduceToNat"))))
        .collect();
    let mut steps: Vec<Tactic> = bound
        .iter()
        .enumerate()
        .filter_map(|(k, b)| bound_rewrite(b, &format!("hb{}", k + 1)))
        .collect();
    // A rewrite stated for each letter in a sum's range is taken under the
    // sum, where the letter's membership is in scope: `+contextual`.
    steps.push(t::simp_only(
        !bound.is_empty(),
        None,
        rules,
        Some(t::at_h(true)),
    ));
    steps.push(t::exact_mod_cast(match turned {
        true => t::symm(t::hyp("h")),
        false => t::hyp("h"),
    }));
    super::doc::Proof::By(t::on_h(cited, steps))
}

/// The lower end `a` of a range a sum runs over, `Finset.Icc a b`; None of
/// any other set.
fn range_lower(over: &Printed) -> Option<&Printed> {
    let super::doc::TermKind::App { head, args, .. } = &over.kind else {
        return None;
    };
    let (super::doc::TermKind::Const(c), [super::doc::Arg::Explicit(a), _]) =
        (&head.kind, args.as_slice())
    else {
        return None;
    };
    (c.name == "Finset.Icc").then_some(a)
}

/// `have name : ∀ k ∈ Finset.Icc a b, x ^ e = x ^ e.toNat := fun k hk =>
/// parley_zpow_toNat x e (by linarith [(Finset.mem_Icc.mp hk).1])`: a power
/// under a sum whose exponent names its letter, as the natural power, for
/// each letter in the sum's range, the exponent at least 0 by the range's
/// lower bound. None where the sum runs over no range.
fn bound_rewrite(b: &super::doc::forms::BoundPower, name: &str) -> Option<Tactic> {
    use super::doc::{LeanType, Op, Quant, Source, TermKind};
    use super::tactics as t;
    range_lower(&b.over)?;
    let k = || Printed::letter(&b.letter, b.letter_ty.clone());
    let natural = Printed::infix(
        Op::POWER,
        b.base.clone(),
        Printed::of(
            TermKind::ToNat(Box::new(t::bracket(b.exponent.clone()))),
            LeanType::Num(super::templates::Num::Nat),
        ),
        b.power.ty.clone().unwrap_or(LeanType::Prop),
    );
    let says = Printed::of(
        TermKind::Quantified {
            quant: Quant::ForAll,
            letter: b.letter.clone(),
            letter_ty: b.letter_ty.clone(),
            guard: Some(Box::new(Printed::infix(
                Op::of("∈")?,
                k(),
                b.over.clone(),
                LeanType::Prop,
            ))),
            body: Box::new(Printed::infix(
                Op::EQUALS,
                b.power.clone(),
                natural,
                LeanType::Prop,
            )),
            bounded: true,
        },
        LeanType::Prop,
    );
    let lower = Printed {
        kind: TermKind::Field {
            inner: Box::new(t::bracket(Printed::applied(
                "Finset.mem_Icc.mp",
                Source::Mathlib,
                vec![t::hyp("hk")],
                LeanType::Prop,
            ))),
            field: "1".to_string(),
        },
        ty: Some(LeanType::Prop),
    };
    let nonneg = t::by_term(super::doc::Proof::By(t::call(
        "linarith",
        vec![t::rules(vec![lower])],
    )));
    let each = Printed::applied(
        "parley_zpow_toNat",
        Source::Bridge(BridgeModule::PowerTactics),
        vec![
            t::bracket(b.base.clone()),
            t::bracket(b.exponent.clone()),
            nonneg,
        ],
        LeanType::Prop,
    );
    Some(Tactic::Have {
        name: name.to_string(),
        says,
        proof: Box::new(super::doc::Proof::Term(Printed::of(
            TermKind::Lambda {
                letters: vec![b.letter.clone(), "hk".to_string()],
                body: Box::new(each),
            },
            LeanType::Prop,
        ))),
    })
}

/// The type variables a term's parts are of, or are sets or maps of.
fn things_in(term: &Printed) -> std::collections::BTreeSet<usize> {
    let mut out: std::collections::BTreeSet<usize> =
        term.ty.iter().flat_map(things_of_type).collect();
    for child in term.children() {
        out.extend(things_in(child));
    }
    out
}

/// The type variables a type is made of.
fn things_of_type(ty: &super::doc::LeanType) -> Vec<usize> {
    use super::doc::LeanType;
    match ty {
        LeanType::Things(n) => vec![*n],
        LeanType::Set(inner) => things_of_type(inner),
        LeanType::Fun { from, to } => {
            let mut out = things_of_type(from);
            out.extend(things_of_type(to));
            out
        }
        _ => Vec::new(),
    }
}

/// `show s by t`: a term saying s, proved by t.
fn shown(says: Printed, proof: super::doc::Proof) -> Printed {
    Printed::of(
        super::doc::TermKind::Show {
            says: Box::new(says),
            proof: Box::new(super::tactics::by_term(proof)),
        },
        super::doc::LeanType::Prop,
    )
}

/// `(proof : says)`: a proof given the statement it is taken as.
fn ascribed(proof: Printed, says: Printed) -> Printed {
    Printed::of(
        super::doc::TermKind::Ascribed {
            proof: Box::new(proof),
            says: Box::new(says),
        },
        super::doc::LeanType::Prop,
    )
}

/// Whether the two sides of an equation a define makes true, met as the
/// checker met them with the define written out, are then the same term,
/// which `simp only [hD]` closes by reflexivity: bound letters may be
/// renamed, which are the same term to Lean, and nothing else taken. An
/// identity element dropped or a respelling is arithmetic left for
/// `norm_num`.
fn unfolds_alone(met: &crate::matching::Meeting) -> bool {
    met.identities.is_empty() && !met.respelled && !met.turned && !met.permuted
}

/// The equations of the defines `defines` applied, `simp (disch := omega)
/// only [h]`, which closes a claim they make true as it stands; and where
/// `alone` is false, the claim then worked out, `push_cast; norm_num`. Of a
/// claim "for all x ∈ S, A = B", `implies_true` takes the `∀ x ∈ S, True`
/// its body leaves.
fn unfolded_by(defines: &[String], alone: bool, for_all: bool) -> Tactic {
    use super::tactics as t;
    let rules: Vec<super::doc::Rule> =
        defines.iter().map(|d| t::forwards(t::hyp(d))).collect();
    simp_unfolded(rules, alone, for_all)
}

/// The ways a step citing a function the header lets keeps where the record
/// does not decide it: the function's equation put in, then the claim as it
/// stands or worked out.
fn header_ways(hyp: &str) -> super::doc::Proof {
    use super::tactics as t;
    super::doc::Proof::By(Tactic::Seq(vec![
        t::try_(t::simp_only(
            false,
            None,
            vec![t::forwards(t::hyp(hyp))],
            None,
        )),
        t::first(
            ListReason::HeaderFunction,
            vec![
                t::call("done", vec![]),
                t::bridge(BridgeTactic::Side, vec![]),
            ],
        ),
    ]))
}

/// `unfolded_by` with the rules given: the defines' equations and any
/// rewrite that goes with them, a case's `if_pos h`.
fn simp_unfolded(
    mut rules: Vec<super::doc::Rule>,
    alone: bool,
    for_all: bool,
) -> Tactic {
    use super::tactics as t;
    if for_all {
        rules.push(t::forwards(t::lemma("implies_true")));
    }
    let simp = t::simp_only(false, Some(t::call("omega", vec![])), rules, None);
    match alone {
        true => simp,
        false => {
            Tactic::Seq(vec![simp, t::push_cast(None), t::call("norm_num", vec![])])
        }
    }
}

/// `(simp (disch := omega) only [h]; done)` and `(simp (disch := omega)
/// only [h]; push_cast; norm_num; done)`: a claim made true by the
/// equations of the defines cited, as they stand or once worked out.
fn unfolded(defines: &[String]) -> Vec<Tactic> {
    use super::tactics as t;
    let rules: Vec<super::doc::Rule> =
        defines.iter().map(|d| t::forwards(t::hyp(d))).collect();
    let simp =
        || t::simp_only(false, Some(t::call("omega", vec![])), rules.clone(), None);
    vec![
        t::steps(vec![simp(), t::call("done", vec![])]),
        t::steps(vec![
            simp(),
            t::push_cast(None),
            t::call("norm_num", vec![]),
            t::call("done", vec![]),
        ]),
    ]
}

/// `qify; push_cast; simp only [specs]; linear_combination line`: a row and
/// the line it cites taken to ℚ, each named number put as its term, and the
/// line used the way the row faces it (`link_facings`), `-line` where
/// turned; both ways where the record has no facing. A congruence row is
/// the line itself, which states it in the named numbers' forms already:
/// `exact line`, or `line.symm` where turned.
fn in_named_forms(
    specs: &[Printed],
    line: &str,
    facing: Option<Facing>,
    congruence: bool,
) -> Tactic {
    use super::tactics as t;
    if let (true, Some(facing)) = (congruence, facing) {
        return Tactic::Exact(faced(t::hyp(line), facing));
    }
    let rules = specs.iter().cloned().map(t::forwards).collect();
    let by_line = |by: Printed| {
        t::steps(vec![t::linear_combination(by), t::call("done", vec![])])
    };
    let used = match facing {
        Some(Facing::Straight) => t::linear_combination(t::hyp(line)),
        Some(Facing::Turned) => t::linear_combination(negated(t::hyp(line))),
        None => t::first(
            ListReason::NamedNumbers,
            vec![by_line(t::hyp(line)), by_line(negated(t::hyp(line)))],
        ),
    };
    t::steps(vec![
        t::call("qify", vec![]),
        t::push_cast(None),
        t::simp_only(false, None, rules, None),
        used,
    ])
}

/// That a term is at least 0, from the line that puts it in ℕ₀, `h`, or
/// in ℕ, `(le_of_lt h)`.
fn nonneg_of(system: crate::rules::System, line: Printed) -> Printed {
    match system {
        crate::rules::System::N => Printed::applied(
            "le_of_lt",
            super::doc::Source::Mathlib,
            vec![line],
            super::doc::LeanType::Prop,
        ),
        _ => line,
    }
}

/// `by norm_num`, as a term: a fact of numerals alone.
fn norm_num_term() -> Printed {
    super::tactics::by_term(super::doc::Proof::By(super::tactics::call(
        "norm_num",
        vec![],
    )))
}

/// `Int.toNat_of_nonneg h`: an integer at least 0 is its `toNat`.
fn to_nat_of(nonneg: Printed) -> Printed {
    Printed::applied(
        "Int.toNat_of_nonneg",
        super::doc::Source::Core,
        vec![nonneg],
        super::doc::LeanType::Prop,
    )
}

/// `-t`.
fn negated(term: Printed) -> Printed {
    Printed {
        ty: term.ty.clone(),
        kind: super::doc::TermKind::Neg(Box::new(term)),
    }
}

/// A named number's equation with its term: the one a step proves, by its
/// name, or the line's witness's, `Classical.choose_spec h`.
fn spec_of(said: &super::expr::SaidInteger) -> Printed {
    let proof = said.proof.clone();
    match said.value {
        Some(_) => proof,
        None => Printed {
            kind: super::doc::TermKind::App {
                head: Box::new(Printed::head(
                    "Classical.choose_spec",
                    super::doc::Source::Core,
                )),
                args: vec![super::doc::Arg::Explicit(proof)],
                explicit: false,
            },
            ty: None,
        },
    }
}

/// `by push_cast; simp only [specs]; all_goals ring`: a claim made true by
/// the named numbers' equations. Put in, they leave the claim closed where
/// its terms are theirs as written, or arithmetic, which is `ring`'s.
fn specs_equal(specs: &[Printed]) -> Printed {
    use super::tactics as t;
    let rules: Vec<super::doc::Rule> = specs.iter().cloned().map(t::forwards).collect();
    super::tactics::by_term(super::doc::Proof::By(specs_then(&rules, ring_left())))
}

/// `all_goals ring`: the arithmetic a rewriting leaves, where it leaves any.
fn ring_left() -> Tactic {
    Tactic::AllGoals(Box::new(super::tactics::call("ring", vec![])))
}

/// `specs_equal` of a named number for `term`. Where the term takes a
/// remainder, `(a^(p − 2)) mod p`, the number is Lean's `%` of integers and
/// the term the bridge's `mod` of real numbers, which are one where the
/// divisor is not negative (`LeanBridges.Divisibility.mod_intCast`): each
/// way first puts the one for the other, the divisor's sign by `omega`
/// from the lines in scope.
fn specs_equal_of(term: &Node, specs: &[Printed]) -> Printed {
    use super::tactics as t;
    if !takes_remainder(term) {
        return specs_equal(specs);
    }
    let rules: Vec<super::doc::Rule> = specs.iter().cloned().map(t::forwards).collect();
    t::by_term(super::doc::Proof::By(unmod_then(&rules, ring_left())))
}

/// One way of `specs_equal_of`: the integers' `%` put as the bridge's
/// `mod` of their casts, then the named numbers' equations and `last`.
fn unmod_then(rules: &[super::doc::Rule], last: Tactic) -> Tactic {
    use super::tactics as t;
    let unmod = t::call(
        "rw",
        vec![TacticArg::Rules(vec![t::backwards(mod_int_cast())])],
    );
    Tactic::Group(Box::new(Tactic::Seq(vec![unmod, specs_then(rules, last)])))
}

/// A term where it stands as one whole, bracketed unless it already is:
/// a witness inside `⟨…⟩`, as an argument is.
fn whole_term(term: Printed) -> Printed {
    match term.prec() >= super::expr::MAX {
        true => term,
        false => super::tactics::bracket(term),
    }
}

/// A claim joined by "and" that the checker met with the item's "and" as
/// written, closed part by part: "and" stands in no other order, so part j
/// of the item is part j of the claim. The item named once, `have h :=
/// term`, each part from its projection `h.j`:
/// - a membership of ℕ or ℕ₀ Lean writes as an integer of a wider term,
///   `∃ m : ℤ, 0 < m ∧ ↑m = t` (`Writer::in_system`), beside the item's
///   order `0 < v` of the same order: `⟨_, h.j, rfl⟩`, t being the named
///   number's cast once the proof has put it;
/// - an equation or order whose casts `norm_cast` all moves on both sides:
///   `by exact_mod_cast h.j`.
///
/// None where the two split into different numbers of parts, or a part has
/// neither form.
fn parts_closed(
    node: &Node,
    claim: &Printed,
    says: &Printed,
    term: &Printed,
) -> Option<super::doc::Proof> {
    use super::doc::TermKind;
    use super::tactics as t;
    let parts = and_parts(node);
    if parts.len() < 2 {
        return None;
    }
    // The order of `0 < m` or `0 ≤ m`, a bound of the numeral 0.
    let zero_bound = |p: &Printed| match &p.kind {
        TermKind::Infix { op, lhs, .. }
            if matches!(op.symbol, "<" | "≤")
                && matches!(&lhs.kind, TermKind::Numeral(d) if d == "0") =>
        {
            Some(op.symbol)
        }
        _ => None,
    };
    let mut proofs = Vec::new();
    for (j, part) in parts.iter().enumerate() {
        let path = leaf_path(node, j)?;
        let (wanted, given) = (along(claim, &path)?, along(says, &path)?);
        if and_sides(&given).is_some() || and_sides(&wanted).is_some() {
            return None;
        }
        let h = projected(t::hyp("h"), &path);
        let witnessed = match &wanted.kind {
            TermKind::Quantified {
                quant: super::doc::Quant::Exists,
                guard: Some(guard),
                ..
            } if part.notation() == crate::notations::MEMBERSHIP => {
                zero_bound(guard).filter(|order| zero_bound(&given) == Some(*order))
            }
            _ => None,
        };
        let proof = match witnessed {
            Some(_) => {
                let rfl = Printed::constant(
                    "rfl",
                    super::doc::Source::Core,
                    super::doc::LeanType::Prop,
                );
                super::expr::anonymous(vec![elided_term(), h, rfl])
            }
            None if matches!(part.notation(), EQUALITY | ORDER)
                && super::casts::norm_cast_moves_all(&given)
                && super::casts::norm_cast_moves_all(&wanted) =>
            {
                t::by_term(super::doc::Proof::By(t::exact_mod_cast(h)))
            }
            None => return None,
        };
        proofs.push(proof);
    }
    Some(super::doc::Proof::By(t::on_h(
        term,
        vec![Tactic::Exact(super::expr::anonymous(proofs))],
    )))
}

/// `⟨_, equation, member⟩`: a claim of a range member Lean computes wider
/// (`wide_range_member`), made of the integer that is it, its equation with
/// the term, and that integer's membership.
fn range_member_made(equation: Printed, member: Printed) -> Printed {
    let elided = Printed::of(super::doc::TermKind::Elided, super::doc::LeanType::Prop);
    super::expr::anonymous(vec![elided, equation, member])
}

/// Whether a claim says a term Lean computes wider than ℤ is in a range,
/// `f(a) ∈ {0, …, p − 1}` of a real f, which Lean says of the integer that
/// is the term (`Writer::formula`).
fn wide_range_member(writer: &Writer, claim: &Node) -> bool {
    let (crate::notations::MEMBERSHIP, [term, set]) =
        (claim.notation(), claim.children.as_slice())
    else {
        return false;
    };
    set.notation() == crate::notations::INTEGER_RANGE
        && writer
            .carrier(term)
            .built()
            .is_some_and(|c| c > super::templates::Num::Int)
}

/// Whether a term takes a remainder, x mod n, which Lean writes as the
/// bridge's `mod` of real numbers where its parts are, and as `%` of
/// integers where a step names them whole.
fn takes_remainder(term: &Node) -> bool {
    term.walk().iter().any(|n| &*n.notation_name() == "mod")
}

/// `LeanBridges.Divisibility.mod_intCast _ _ (by omega)`: the bridge's `mod`
/// of two integers cast to ℝ is their `%`, where the divisor is not
/// negative, which `omega` reads off the lines in scope.
fn mod_int_cast() -> Printed {
    use super::doc::bridges::BridgeModule;
    use super::doc::{Arg, Proof, TermKind};
    use super::tactics as t;
    let elided = || Printed::of(TermKind::Elided, super::doc::LeanType::Prop);
    let sign = t::bracket(t::by_term(Proof::By(t::call("omega", vec![]))));
    Printed {
        kind: TermKind::App {
            head: Box::new(t::bridge_lemma(
                "LeanBridges.Divisibility.mod_intCast",
                BridgeModule::Divisibility,
            )),
            args: vec![
                Arg::Explicit(elided()),
                Arg::Explicit(elided()),
                Arg::Explicit(sign),
            ],
            explicit: false,
        },
        ty: None,
    }
}

/// An equation of a whole number's line, stated in `from`, carried to the
/// type `to` the goal writes it in: by its casts, or, from ℚ to ℝ, where
/// `exact_mod_cast` does not carry a power to an integer, by casting the
/// equation to ℝ and pushing the cast in, `have h := congrArg (fun x => ((x
/// : ℚ) : ℝ)) e; push_cast at h; exact h`.
fn cast_carried(
    equation: Printed,
    from: super::templates::Num,
    to: super::templates::Num,
) -> super::doc::Proof {
    use super::doc::{Arg, LeanType, TermKind};
    use super::tactics as t;
    use super::templates::Num;
    if (from, to) != (Num::Rat, Num::Real) {
        return super::doc::Proof::By(t::exact_mod_cast(equation));
    }
    let to_real = untyped_lambda(
        &["x"],
        Printed::cast(
            Printed::cast(t::hyp("x"), LeanType::Num(Num::Rat)),
            LeanType::Num(Num::Real),
        ),
    );
    let carried = Printed {
        kind: TermKind::App {
            head: Box::new(t::lemma("congrArg")),
            args: vec![Arg::Explicit(to_real), Arg::Explicit(equation.clone())],
            explicit: false,
        },
        ty: None,
    };
    let pushed = Tactic::Seq(vec![
        Tactic::Name {
            name: "h".to_string(),
            term: carried,
        },
        t::push_cast(Some(t::at_h(false))),
        Tactic::Exact(t::hyp("h")),
    ]);
    super::doc::Proof::By(pushed)
}

/// `fun a h => body`: a function of these letters, whose types Lean finds
/// from where it stands, as the proof part of `⟨…⟩` takes them.
fn untyped_lambda(letters: &[&str], body: Printed) -> Printed {
    let ty = body.ty.clone().unwrap_or(super::doc::LeanType::Prop);
    Printed::of(
        super::doc::TermKind::Lambda {
            letters: letters.iter().map(|l| l.to_string()).collect(),
            body: Box::new(body),
        },
        ty,
    )
}

/// `refine ⟨parts⟩`: the goal's parts, the ones left open proved after.
fn refine(parts: Vec<Printed>) -> Tactic {
    super::tactics::call(
        "refine",
        vec![TacticArg::Term(super::expr::anonymous(parts))],
    )
}

/// `(push_cast; simp only [specs]; last)`.
fn specs_then(rules: &[super::doc::Rule], last: Tactic) -> Tactic {
    use super::tactics as t;
    t::steps(vec![
        t::push_cast(None),
        t::simp_only(false, None, rules.to_vec(), None),
        last,
    ])
}

/// `(have h := t; (try push_cast at h); (try push_cast); linear_combination
/// (norm := parley_norm) e)`: the citation with its casts pushed in on both
/// sides, then the claim as a combination of it.
fn pushed_then(cited: &Printed, by: Printed) -> Tactic {
    use super::tactics as t;
    t::on_h(
        cited,
        vec![
            t::try_(t::push_cast(Some(t::at_h(false)))),
            t::try_(t::push_cast(None)),
            t::linear_combination(by),
        ],
    )
}

/// `simp (disch := parley_side) only [parley_cast_toNat] at h`: a natural
/// given as an integer's `toNat` put back as the integer, cast to ℚ or ℝ.
fn cast_to_nat_at_h() -> Tactic {
    use super::tactics as t;
    t::simp_only(
        false,
        Some(t::bridge(BridgeTactic::Side, vec![])),
        vec![t::forwards(t::bridge_lemma(
            "parley_cast_toNat",
            BridgeModule::PowerTactics,
        ))],
        Some(t::at_h(false)),
    )
}

/// The ways a claim is closed from a term that proves it, or something
/// near it, tried in order (`close`).
fn closers(writer: &Writer, claim: &Node, cited: Printed) -> Vec<Tactic> {
    use super::tactics as t;
    let complex = super::doc::LeanType::Num(super::templates::Num::Complex);
    let real = super::doc::LeanType::Num(super::templates::Num::Real);
    let to_nat_put_back = cited.names("Int.toNat_of_nonneg");
    let h = || t::hyp("h");
    // An equation or order between sets, members or counts is closed as
    // any other claim: the closers for numbers work in a field or a ring.
    let of_numbers = claim
        .children
        .iter()
        .all(|c| c.sort.is("number") && !writer.counts(c));
    match claim.notation() {
        // An instance whose casts sit otherwise than the claim's, ↑(0 : ℕ)
        // for 0, is taken with them pushed in, and one whose equation the
        // claim turns round, as a cited rule written a + b = c claimed as
        // c = a + b, is taken negated. A corpus theorem stated in a
        // wider type than the claim, ℝ for a claim in ℚ, has the claim moved
        // up to it.
        EQUALITY if of_numbers => {
            // A remainder of integers written with `%`, beside an item of
            // set.mm's mod of real numbers: the item's put as `%` first.
            let of_mod = claim.walk().iter().any(|n| &*n.notation_name() == "mod");
            let as_remainder = of_mod.then(|| {
                let mod_lemma = |name| {
                    t::forwards(t::bridge_lemma(name, BridgeModule::Divisibility))
                };
                t::steps(vec![
                    t::name_h(&cited),
                    t::simp_only(
                        false,
                        Some(t::call("positivity", vec![])),
                        vec![
                            mod_lemma("LeanBridges.Divisibility.mod_natCast"),
                            mod_lemma("LeanBridges.Divisibility.mod_intCast"),
                        ],
                        Some(t::at_h(true)),
                    ),
                    t::exact_mod_cast(t::hyp("h")),
                ])
            });
            // A term given a natural as an integer's `toNat`, rewritten back
            // by `▸` (`instance`): an error elaborating it against the goal,
            // as `exact_mod_cast` does, is logged and does not fail the
            // alternative, so it is cast from a `have`, which fails.
            // An item stated over ℂ, given the claim's real numbers cast up,
            // `(P : ℂ)`, where the claim is in ℝ: the item read back in ℝ.
            let below_complex = claim
                .children
                .iter()
                .filter_map(|c| writer.carrier(c).built())
                .all(|n| n < super::templates::Num::Complex);
            let of_complex =
                (cited.has_cast_to(&complex) && below_complex).then(|| {
                    t::on_h(
                        &cited,
                        vec![t::bridge(
                            BridgeTactic::OfComplex,
                            vec![TacticArg::Term(h())],
                        )],
                    )
                });
            // An item over ℝ given rationals, the geometric sum at a := 2,
            // where the claim is written in its own type, ℚ: cast down.
            let of_real: Vec<Tactic> = cited
                .has_cast_to(&real)
                .then(|| {
                    t::on_h(
                        &cited,
                        vec![t::bridge(
                            BridgeTactic::RatOfReal,
                            vec![TacticArg::Term(h())],
                        )],
                    )
                })
                .into_iter()
                .collect();
            // An item that counts in ℕ∞, |∅| = 0, met in ℤ: the goal's
            // counts of finite sets said in ℕ∞ (`parley_count_ext`), where
            // the item meets it as it stands, before the `exact_mod_cast`
            // below, whose error is logged as above.
            let counted = claim
                .walk()
                .iter()
                .any(|n| &*n.notation_name() == "cardinality");
            let counted = counted.then(|| {
                t::steps(vec![
                    t::bridge(BridgeTactic::CountExt, vec![]),
                    t::exact_mod_cast(cited.clone()),
                ])
            });
            let by_to_nat = to_nat_put_back;
            // The `▸` of a `toNat` rewrites its cast to ℤ only; one cast to
            // ℚ or ℝ, (1 − 2y).toNat in ℚ, is put back as the integer by
            // `parley_cast_toNat`.
            // The term itself, given to `linear_combination`: not one with a
            // `toNat` put back by `▸`, whose error is logged as above; the
            // `have` after it takes that one.
            let direct = (!by_to_nat).then(|| t::linear_combination(cited.clone()));
            let cast = match by_to_nat {
                true => vec![
                    t::on_h(&cited, vec![t::exact_mod_cast(h())]),
                    t::on_h(&cited, vec![t::exact_mod_cast(t::symm(h()))]),
                    t::on_h(
                        &cited,
                        vec![
                            cast_to_nat_at_h(),
                            t::try_(t::push_cast(Some(t::at_h(true)))),
                            t::linear_combination(h()),
                        ],
                    ),
                ],
                false => vec![
                    t::exact_mod_cast(cited.clone()),
                    t::exact_mod_cast(t::symm(t::bracket(cited.clone()))),
                ],
            };
            let negated = Printed {
                kind: super::doc::TermKind::Neg(Box::new(h())),
                ty: None,
            };
            let mut out: Vec<Tactic> = direct.into_iter().collect();
            out.push(pushed_then(&cited, h()));
            out.push(pushed_then(&cited, negated));
            out.extend(counted);
            out.extend(cast);
            out.push(t::on_h(
                &cited,
                vec![t::call("rify", vec![]), t::linear_combination(h())],
            ));
            out.push(t::on_h(
                &cited,
                vec![t::call("qify", vec![]), t::linear_combination(h())],
            ));
            out.extend(as_remainder);
            out.extend(of_complex);
            out.extend(of_real);
            out.push(t::on_h(&cited, vec![t::bridge(BridgeTactic::Side, vec![])]));
            out
        }
        // A numeral given to a letter of ℕ arrives cast, ((3 : ℕ) : ℤ),
        // which linarith reads only once the cast is pushed in.
        // An item over ℝ cited for a claim the page computes in ℚ gives
        // the claim cast up, which exact_mod_cast brings down.
        ORDER if of_numbers => {
            vec![
                t::call("linarith", vec![t::rules(vec![cited.clone()])]),
                t::on_h(
                    &cited,
                    vec![
                        t::push_cast(Some(t::at_h(false))),
                        t::call("linarith", vec![]),
                    ],
                ),
                t::exact_mod_cast(cited.clone()),
                t::on_h(&cited, vec![t::bridge(BridgeTactic::Side, vec![])]),
            ]
        }
        // A relation said either way round, a congruence or a ↔, as the
        // claim writes it. Here and above, the last way takes the
        // citation's "and" apart: a definition unfolded to "p > 1 and for
        // all d …" gives either half. A claim with a listed set in it, which
        // may be in another order than the item's, {w, u} for {u, w}, is put
        // in one order on both sides.
        _ => {
            let listed = claim.walk().iter().any(|n| {
                matches!(
                    &*n.notation_name(),
                    "listed-two" | "listed-three" | "listed-four"
                )
            });
            let reorder =
                listed.then(|| reordered(&cited, claim.notation() == EQUALITY));
            // A natural given as an integer's `toNat`, put back by `▸`: an
            // error elaborating that against the goal is logged and does not
            // fail the alternative, so the term is stated by a `have`, which
            // fails. `▸` puts it back only where it is cast to ℤ; cast to ℚ
            // or ℝ, m/(2^p − 1).toNat inside a "there is", it is put back by
            // `parley_cast_toNat`.
            match to_nat_put_back {
                true => {
                    let mut out = vec![
                        t::on_h(&cited, vec![Tactic::Exact(h())]),
                        t::on_h(&cited, vec![Tactic::Exact(t::symm(h()))]),
                        t::on_h(
                            &cited,
                            vec![t::call("simpa", vec![TacticArg::Using(h())])],
                        ),
                        t::on_h(&cited, vec![t::exact_mod_cast(h())]),
                    ];
                    out.extend(reorder);
                    out.push(t::on_h(
                        &cited,
                        vec![
                            cast_to_nat_at_h(),
                            t::try_(t::push_cast(Some(t::at_h(true)))),
                            Tactic::Exact(h()),
                        ],
                    ));
                    out.push(t::on_h(
                        &cited,
                        vec![t::bridge(BridgeTactic::Side, vec![])],
                    ));
                    out
                }
                false => {
                    // A line in ℝ taken at a value, ε := 1/2, whose claim of
                    // rationals is written in its own type, ℚ: cast down.
                    let of_real = cited.has_cast_to(&real).then(|| {
                        t::on_h(
                            &cited,
                            vec![t::bridge(
                                BridgeTactic::RatOfReal,
                                vec![TacticArg::Term(h())],
                            )],
                        )
                    });
                    let mut out = vec![
                        Tactic::Exact(cited.clone()),
                        Tactic::Exact(t::symm(t::bracket(cited.clone()))),
                        t::call("simpa", vec![TacticArg::Using(cited.clone())]),
                        t::exact_mod_cast(cited.clone()),
                    ];
                    // A range member Lean computes wider is said as the
                    // integer that is it, `∃ m : ℤ, ↑m = t ∧ m ∈ Finset.Icc a
                    // b` (`Writer::formula`), and the claim's t is the
                    // integer the item puts in the range once the step
                    // rewrites it so: that integer, its own equation, and the
                    // item.
                    // A product or sum over a range, which the claim writes
                    // over `Finset.Icc`, of an item over a set of numbers
                    // that writes `∏ᶠ x ∈ Set.Icc a b`: the item's put over
                    // the finset the set is.
                    let ranged = super::expr::RangedOperators::of(claim);
                    for (on, lemma) in [
                        (ranged.product, "finprod_mem_coe_finset"),
                        (ranged.sum, "finsum_mem_coe_finset"),
                    ] {
                        if on {
                            out.push(t::on_h(
                                &cited,
                                vec![
                                    t::call(
                                        "rw",
                                        vec![
                                            TacticArg::Rules(vec![
                                                t::backwards(t::lemma(
                                                    "Finset.coe_Icc",
                                                )),
                                                t::forwards(t::lemma(lemma)),
                                            ]),
                                            t::at_h(false),
                                        ],
                                    ),
                                    Tactic::Exact(h()),
                                ],
                            ));
                        }
                    }
                    if wide_range_member(writer, claim) {
                        let rfl = Printed::constant(
                            "rfl",
                            super::doc::Source::Core,
                            super::doc::LeanType::Prop,
                        );
                        out.push(Tactic::Exact(range_member_made(rfl, cited.clone())));
                    }
                    out.extend(reorder);
                    out.extend(of_real);
                    out.push(t::on_h(
                        &cited,
                        vec![t::bridge(BridgeTactic::Side, vec![])],
                    ));
                    out
                }
            }
        }
    }
}
