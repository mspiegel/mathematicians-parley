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

use super::doc::bridges::BridgeModule;
use super::doc::{ListReason, Tactic, TacticArg};
use super::expr::{LetterType, Printed, Writer};
use super::items::{Item, Sentence};
use super::names::{line_name, snake};
use super::spelling::{fields_of, number_types};
use super::statement::{binders, introduces, Asked, Binder, StatedAt};
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

mod blocks;
mod cited_lines;
mod citing;
mod conversions;
mod headers;
mod helpers;
mod kinds;
mod orders;
mod proved;
mod reading;
mod reasons;
mod substitution;
mod terms;

use self::conversions::*;
use self::headers::*;
use self::helpers::*;
use self::proved::*;
use self::terms::*;
pub use self::terms::{
    as_item, as_written, set_valued, Origin, Sources, Spot, SET_VALUED,
};

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
    let mut written_above: Vec<StatedHypothesis> = Vec::new();
    let mut written_below: Vec<StatedHypothesis> = Vec::new();
    for (line, (label, s)) in said.iter().enumerate() {
        let into = match above(label) {
            true => &mut written_above,
            false => &mut written_below,
        };
        for s in s {
            if let Some(name) = &s.name {
                into.push(StatedHypothesis {
                    node: defined_out(&s.node, rec, writer),
                    name: name.clone(),
                    at: crate::citing::HypothesisAt {
                        line,
                        sentence: s.at,
                    },
                });
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
    let props: Vec<&Printed> = conclusion.iter().map(|c| &c.prop).collect();
    let lets = super::statement::let_letters(&thm.hypotheses, &thm.path);
    let binders = super::statement::with_sethoods(binders, &lets, &props);
    Route::Built(Statement {
        binders,
        conclusion,
    })
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
    /// Each name a define gives a finite set, U of `let U = {c ∈ G(m, n) :
    /// …}`, with the `have` that says it is (`hD3_finite`), which proves it
    /// finite for the reason the record gives a define's name
    /// (`FiniteBy::Define`).
    finite_defined: IndexMap<String, String>,
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
    /// The names a claim's leading "for all" is opened under while its
    /// proof is written, `x h_x` of `intro x h_x` (`peel`): a line Lean
    /// states under the same binders is read at them, and a member's fact
    /// is the guard's name.
    intros_now: std::cell::RefCell<Vec<String>>,
    /// The sentence of a claim whose proof is being written (`proof_of`),
    /// by which the step's proof puts its cited lines in terms of the
    /// numbers lines name (`specs_in`).
    claim_now: std::cell::RefCell<Option<Node>>,
    /// While a citation's closing is written, the equations of the defines
    /// the citation has already put into the goal (`written_out`), `hD1`:
    /// the closing does not put them in again.
    defines_in_goal: std::cell::RefCell<Vec<String>>,
    /// While a block's part is opened, the goal it opens, as Lean states it
    /// (`OpeningGoal`): an `assume` takes its statement from it, as `intro`
    /// does, `V.encard = 2` of a direction of `V.encard = 2 ↔ …`.
    opening_goal: Option<OpeningGoal>,
    /// The statement's facts that a thing is one of ZF's sets, by name with
    /// what each says as Lean states it, the page's `assume X exists` and
    /// those its `let` lines give (`statement::with_sethoods`): what meets
    /// a cited item's own (`StatedAt::Sethood`).
    sethoods: Vec<Sethood>,
}

/// A statement's fact that a thing is one of ZF's sets.
struct Sethood {
    name: String,
    /// What it says, as Lean states it.
    says: String,
}

/// The goal a part of a block opens, and where its own lines start.
struct OpeningGoal {
    /// The goal before the part's `intro`s, as Lean states it.
    goal: Printed,
    /// The proof's line count when the part began opening.
    from: usize,
    /// The depth the part's lines are at.
    depth: usize,
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

/// A whole number a line or the step names for a term (`number_named`).
struct NumberNamed {
    /// The term, as a line writes it.
    term: Printed,
    /// The number's equation with it, `↑(Classical.choose h) = t`.
    equation: Printed,
}

/// A line taken to the numbers lines name for the terms it gives as whole
/// numbers (`at_named_numbers`).
struct LineAtNumbers {
    /// Its proof at those numbers.
    proof: Printed,
    /// What it then says.
    says: Printed,
}

/// The `t` of `↑m = t`, the equation a "there is" of the letter `m` gives
/// its number; None of any other formula.
fn witness_equation(p: &Printed, letter: &str) -> Option<Printed> {
    use super::doc::{Op, TermKind};
    fn bare_letter(p: &Printed) -> Option<&str> {
        match &p.kind {
            TermKind::Letter(l) => Some(l),
            TermKind::Paren(inner) | TermKind::Cast { inner, .. } => bare_letter(inner),
            _ => None,
        }
    }
    let TermKind::Infix { op, lhs, rhs } = &p.kind else {
        return None;
    };
    (*op == Op::EQUALS && bare_letter(lhs) == Some(letter)).then(|| (**rhs).clone())
}

/// A cited line's sentence a step restates of the numbers it names, within
/// that step's proof: where it is kept, and what it said before.
struct RestatedInStep {
    /// The label the line is kept under.
    line: String,
    /// The sentence's place among the line's.
    place: usize,
    /// What the sentence said before the step restated it.
    before: Option<Printed>,
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

/// A term a formula puts in a whole-number slot that Lean does not compute
/// as one, which Lean states of the whole number it is
/// (`Writer::slot_witness`).
struct WideTerm {
    /// The term, a/k of gcd(a/k, b/k) = 1.
    term: Node,
    /// The type of its witness, ℤ or ℕ.
    whole: super::templates::Num,
}

/// A line a step cites in the witness form, `∃ m : ℤ, ↑m = t ∧ P m`, or its
/// negation, which the step restates of the numbers it names for its terms.
struct CitedWitness {
    /// The line's Lean name.
    name: String,
    /// The terms the witnesses stand for, the outermost first.
    terms: Vec<WideTerm>,
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

/// A rewrite that puts a named number for its term, `← Classical.choose_spec
/// h`, with the term as the page prints it and as Lean writes it where the
/// rewrite finds it.
struct NumberRule {
    term: String,
    /// None where the writer cannot write the term, and the rewrite is put
    /// in the goal alone.
    lean: Option<Printed>,
    rule: super::doc::Rule,
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
        writer: Writer::new(
            &sources.checked.grammar,
            sources.templates,
            &sources.ctx.conjunctions,
        ),
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
        finite_defined: IndexMap::new(),
        named_now: std::cell::RefCell::new(None),
        held_now: std::cell::RefCell::new(Vec::new()),
        step_now: std::cell::Cell::new(None),
        intros_now: std::cell::RefCell::new(Vec::new()),
        claim_now: std::cell::RefCell::new(None),
        defines_in_goal: std::cell::RefCell::new(Vec::new()),
        opening_goal: None,
        sethoods: Vec::new(),
    };
    proof.writer.reals = held_real(rec, &proof.writer);
    proof.writer.finite_from(&rec.said_finite);
    proof.writer.finite_under = std::rc::Rc::new(rec.finite_under.clone());
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
    // Each says what its binder states, which a later reading reads: a
    // count the hypothesis alone makes finite stays in ℕ∞ there, where the
    // proof's writer counts it in ℕ.
    let stated: std::collections::BTreeMap<&str, &Printed> = binders
        .iter()
        .filter_map(|b| match b {
            Binder::Fact { name, says, .. } => Some((name.as_str(), says)),
            Binder::Letter { .. } => None,
        })
        .collect();
    let bound: std::collections::BTreeSet<&str> =
        binders.iter().map(Binder::name).collect();
    for (label, said) in hypothesis_sentences(thm, rec) {
        let said: Vec<LineSentence> = said
            .into_iter()
            .filter(|s| s.name.as_deref().is_some_and(|n| bound.contains(n)))
            .map(|s| LineSentence {
                says: s
                    .name
                    .as_deref()
                    .and_then(|n| stated.get(n))
                    .map(|p| (*p).clone()),
                ..s
            })
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
    proof.sethoods = binders
        .iter()
        .filter_map(|b| match b {
            Binder::Fact { name, says, .. }
                if says
                    .constants()
                    .iter()
                    .any(|c| c.name == super::expr::IS_SET) =>
            {
                Some(Sethood {
                    name: name.clone(),
                    says: says.text(),
                })
            }
            _ => None,
        })
        .collect();
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
