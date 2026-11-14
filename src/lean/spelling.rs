//! A cited item's Lean statement read as the step writes it (`docs/LEAN.md`,
//! a citation).
//!
//! An item's Lean statement is written once, over any ring `K` or any set
//! `X`; the step's lines are written from the page. At a citation the two
//! can spell one fact differently: `∀ x ∈ Set.univ` beside `∀ x`, `(2 * m :
//! ℚ)` beside `2 * (m : ℚ)`, an item in ℂ beside a line in ℝ. The step
//! proves its own spelling from the item by what Lean knows of the two
//! forms, and by nothing Lean finds at proof time:
//! - where Lean takes the two as one term, the item itself (`exact`);
//! - where the item, its functions applied, casts a term that is no letter
//!   to another type, those casts pushed down (`push_cast`);
//! - for each form the item writes and the step does not, the library's
//!   fact that joins the two (`Spelling`);
//! - where the item is in a wider type, ℂ at reals or ℝ at rationals, its
//!   casts moved to meet the step's (`exact_mod_cast`).

use super::doc::{forms, Arg, BoundForm, LeanType, Quant, Tactic, TermKind};
use super::expr::Printed;
use super::tactics as t;
use super::templates::Num;

/// The fields an item's Lean statement and the step's spelling of it are
/// worked in, the widest each names (`fields_of`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InstanceFields {
    /// One field; a side whose field the writer does not know is no
    /// difference.
    One,
    /// The item in ℝ and the step in ℚ alone.
    RealAtRationals,
    /// The item in another wider type, ℂ at reals or ℝ at integers.
    Wider,
}

impl InstanceFields {
    /// The fields of the item's statement, `item`, and the step's,
    /// `written`.
    pub fn of(item: &Printed, written: &Printed) -> InstanceFields {
        let (of_item, of_step) = (fields_of(item), fields_of(written));
        let real_at_rationals = of_step == std::collections::BTreeSet::from([Num::Rat])
            && of_item.contains(&Num::Real)
            && !of_item.contains(&Num::Complex);
        match (of_item.last() == of_step.last(), real_at_rationals) {
            (true, _) => InstanceFields::One,
            (false, true) => InstanceFields::RealAtRationals,
            (false, false) => InstanceFields::Wider,
        }
    }
}

/// The fields a statement as Lean writes it is worked in, ℚ, ℝ or ℂ, of
/// its number types: an exponent's ℕ or an index's ℤ beside them says
/// nothing of the field.
pub fn fields_of(term: &Printed) -> std::collections::BTreeSet<Num> {
    number_types(term)
        .into_iter()
        .filter(|n| matches!(n, Num::Rat | Num::Real | Num::Complex))
        .collect()
}

/// The number types a statement as Lean writes it names: those of its
/// terms, and those it casts to.
pub fn number_types(term: &Printed) -> std::collections::BTreeSet<Num> {
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

/// The library's facts that take an item's statement to the step's
/// spelling of it, each of one form the item writes and the step does not.
#[derive(Debug, Default, PartialEq, Eq)]
struct Spelling {
    /// Facts rewriting the item's statement.
    at_item: Vec<Printed>,
    /// Facts rewriting the step's.
    at_step: Vec<Printed>,
    /// Whether a fact holds under a side condition of integers, a divisor
    /// not below 0, which `omega` proves from the lines in scope.
    side_by_omega: bool,
    /// Whether the item's casts are first lifted out of a sum or product of
    /// casts, `↑A + ↑M * ↑1` as `↑(A + M * 1)` (`norm_cast`), for a fact
    /// stated of one cast integer, `mod ↑a ↑b`.
    lifted_first: bool,
}

impl Spelling {
    fn is_empty(&self) -> bool {
        self.at_item.is_empty() && self.at_step.is_empty()
    }
}

/// The facts that join the forms the item, `said`, writes and the step,
/// `written`, does not:
/// - a quantifier over the whole type written over `Set.univ`, `∀ x ∈
///   Set.univ` or `∃ x ∈ Set.univ`, read over the type (`Set.mem_univ`,
///   then `true_implies` or `true_and`);
/// - a set built from `Set.univ`, `{t ∈ Set.univ | P t}`, read as `{t | P
///   t}` (`Set.mem_univ`, `true_and`);
/// - an integer said as some `(m : K)` at K := ℤ, `∃ m, P m ∧ (m : ℤ) = t`,
///   read as `P t` (`Int.cast_id`, `exists_eq_right`);
/// - a product or sum over a range as a set, which the step takes over the
///   range as a finite set (`parley_finprod_Icc`, `parley_finsum_Icc`);
/// - a membership of a range as a set beside the step's of a range as a
///   finite set, the step's read as its two bounds (`Finset.mem_Icc`);
/// - the reals' `mod` of integers cast up, read as their `%`
///   (`LeanBridges.Divisibility.mod_intCast`).
///
/// A form Lean defines as the other, `a > b` as `b < a` or a member of `{t
/// | P t}` as `P`, needs no fact: `exact` takes the one as the other.
fn spelling(said: &Printed, written: &Printed) -> Spelling {
    let mut at_item: Vec<&'static str> = Vec::new();
    let mut bridged: Vec<&'static str> = Vec::new();
    let mut at_step: Vec<&'static str> = Vec::new();
    let mut divided: Vec<&'static str> = Vec::new();
    let mut lifted_first = false;
    let item = said.walk();
    let step = written.walk();
    let step_remainders = step
        .iter()
        .any(|n| matches!(&n.kind, TermKind::Infix { op, .. } if op.symbol == "%"));
    for node in &item {
        match &node.kind {
            TermKind::Quantified {
                quant,
                guard: Some(guard),
                ..
            } if over_universe(guard) => match quant {
                Quant::ForAll => {
                    add_facts(&mut at_item, &["Set.mem_univ", "true_implies"])
                }
                Quant::Exists => add_facts(&mut at_item, &["Set.mem_univ", "true_and"]),
                Quant::Fun => {}
            },
            TermKind::Bound {
                form: BoundForm::SetOfMember { set },
                ..
            } if is_universe(set) => {
                add_facts(&mut at_item, &["Set.mem_univ", "true_and"])
            }
            TermKind::Quantified {
                quant: Quant::Exists,
                letter,
                letter_ty,
                guard: Some(_),
                body,
                bounded: false,
            } if equals_its_letter(letter, letter_ty, body) => {
                add_facts(&mut at_item, &["Int.cast_id", "exists_eq_right"])
            }
            TermKind::Bound {
                form:
                    BoundForm::BigOp {
                        product,
                        finite: true,
                        set,
                        ..
                    },
                ..
            } if is_range(set, "Set.Icc")
                && step.iter().any(|n| over_finite_range(n, *product)) =>
            {
                add_facts(
                    &mut bridged,
                    &[match product {
                        true => "parley_finprod_Icc",
                        false => "parley_finsum_Icc",
                    }],
                )
            }
            TermKind::App { head, args, .. }
                if is_const(head, "LeanBridges.Divisibility.mod")
                    && step_remainders =>
            {
                add_facts(&mut divided, &["LeanBridges.Divisibility.mod_intCast"]);
                lifted_first |= args.iter().any(|a| match a {
                    Arg::Explicit(x) => !cast_letter(x),
                    Arg::Named { .. } => false,
                });
            }
            _ => {}
        }
    }
    // `push_cast` works out an integer sum of numerals it casts up,
    // `((1 + 1 : ℤ) : ℚ)` as `2`, which the step writes in the field as
    // `1 + 1`: Lean's library names that one sum (`one_add_one_eq_two`).
    let numerals_cast = forms::beta_reduced(said).walk().iter().any(|n| {
        matches!(&n.kind, TermKind::Cast { inner, to: LeanType::Num(to) }
            if is_field(*to) && numeral_sum(inner, false))
    });
    if numerals_cast && step.iter().any(|n| numeral_sum(n, true)) {
        add_facts(&mut at_step, &["one_add_one_eq_two"]);
    }
    let item_ranges = item.iter().any(|n| member_of_range(n, "Set.Icc"));
    if item_ranges && step.iter().any(|n| member_of_range(n, "Finset.Icc")) {
        add_facts(&mut at_step, &["Finset.mem_Icc"]);
    }
    use super::doc::bridges::BridgeModule;
    let side_by_omega = !divided.is_empty();
    let mut item_facts: Vec<Printed> = bridged
        .into_iter()
        .map(|l| t::bridge_lemma(l, BridgeModule::InstanceTactics))
        .collect();
    item_facts.extend(
        divided
            .into_iter()
            .map(|l| t::bridge_lemma(l, BridgeModule::Divisibility)),
    );
    item_facts.extend(at_item.into_iter().map(t::lemma));
    Spelling {
        at_item: item_facts,
        at_step: at_step.into_iter().map(t::lemma).collect(),
        side_by_omega,
        lifted_first,
    }
}

/// Whether the number type is a field, ℚ, ℝ or ℂ.
fn is_field(n: Num) -> bool {
    matches!(n, Num::Rat | Num::Real | Num::Complex)
}

/// Whether the term is `1 + 1`, in a field where `in_field`, or of whole
/// numbers otherwise.
fn numeral_sum(term: &Printed, in_field: bool) -> bool {
    let term = unbracketed(term);
    let one =
        |x: &Printed| matches!(&innermost(x).kind, TermKind::Numeral(d) if d == "1");
    let typed = match &term.ty {
        Some(LeanType::Num(n)) => is_field(*n) == in_field,
        _ => false,
    };
    matches!(&term.kind, TermKind::Infix { op, lhs, rhs }
        if op.symbol == "+" && one(lhs) && one(rhs))
        && typed
}

/// Whether the term is a letter cast to some type, `(A : ℝ)`.
fn cast_letter(term: &Printed) -> bool {
    match &unbracketed(term).kind {
        TermKind::Cast { inner, .. } => {
            matches!(unbracketed(inner).kind, TermKind::Letter(_))
        }
        _ => false,
    }
}

/// Each of `facts` added to `into` where it is not there yet.
fn add_facts(into: &mut Vec<&'static str>, facts: &[&'static str]) {
    for f in facts {
        if !into.contains(f) {
            into.push(f);
        }
    }
}

/// The term within its brackets and ascriptions.
fn innermost(term: &Printed) -> &Printed {
    match &term.kind {
        TermKind::Paren(inner) | TermKind::Cast { inner, .. } => innermost(inner),
        _ => term,
    }
}

/// Whether the term is the constant `name`.
fn is_const(term: &Printed, name: &str) -> bool {
    matches!(&innermost(term).kind, TermKind::Const(c) if c.name == name)
}

/// Whether the term is the whole type as a set, `(Set.univ : Set ℝ)`.
fn is_universe(term: &Printed) -> bool {
    is_const(term, "Set.univ")
}

/// Whether a guard says its letter is in the whole type, `x ∈ Set.univ`.
fn over_universe(guard: &Printed) -> bool {
    matches!(&innermost(guard).kind,
        TermKind::Infix { op, rhs, .. } if op.symbol == "∈" && is_universe(rhs))
}

/// Whether the term is a range `head a b`, `Set.Icc` or `Finset.Icc`.
fn is_range(term: &Printed, head: &str) -> bool {
    matches!(&innermost(term).kind,
        TermKind::App { head: h, .. } if is_const(h, head))
}

/// Whether the node says something is a member of a range `head a b`.
fn member_of_range(node: &Printed, head: &str) -> bool {
    matches!(&node.kind,
        TermKind::Infix { op, rhs, .. } if op.symbol == "∈" && is_range(rhs, head))
}

/// Whether the node is a product (or a sum) over a range as a finite set.
fn over_finite_range(node: &Printed, product: bool) -> bool {
    matches!(&node.kind, TermKind::Bound {
        form: BoundForm::BigOp { product: p, finite: false, set, .. },
        ..
    } if *p == product && is_range(set, "Finset.Icc"))
}

/// Whether `body`, under a condition on the letter, says the letter at its
/// own type is some term, `(m : ℤ) = t` of `∃ m, P m ∧ (m : ℤ) = t`: what
/// an integer said as some `(m : K)` reads at K := ℤ.
fn equals_its_letter(letter: &str, letter_ty: &LeanType, body: &Printed) -> bool {
    let TermKind::Infix { op, lhs, .. } = &innermost(body).kind else {
        return false;
    };
    let own_cast = match &unbracketed(lhs).kind {
        TermKind::Cast { inner, to } => {
            matches!(&unbracketed(inner).kind, TermKind::Letter(l) if l == letter)
                && to == letter_ty
        }
        _ => false,
    };
    op.symbol == "=" && own_cast
}

/// The term within its brackets.
fn unbracketed(term: &Printed) -> &Printed {
    match &term.kind {
        TermKind::Paren(inner) => unbracketed(inner),
        _ => term,
    }
}

/// Whether the item's statement, its functions applied, casts a numeral or
/// a sum, difference, product, quotient, power or negation to another type:
/// `((fun j => (j : ℚ)) (k + 1))` is `((k + 1 : ℤ) : ℚ)`, which `push_cast`
/// takes to `(k : ℚ) + 1`. The value of a function, `(choose n k : ℝ)`, is
/// a term `push_cast` moves no cast into, and a term of a type Lean fills
/// in where the item is cited, its α, is not cast.
fn casts_pushed(said: &Printed) -> bool {
    forms::beta_reduced(said)
        .walk()
        .iter()
        .any(|c| match &c.kind {
            TermKind::Cast { inner, to } => {
                let inner = innermost(inner);
                let arithmetic = match &inner.kind {
                    TermKind::Numeral(_) | TermKind::Neg(_) => true,
                    TermKind::Infix { op, .. } => {
                        matches!(op.symbol, "+" | "-" | "*" | "/" | "^")
                    }
                    _ => false,
                };
                arithmetic && inner.ty.as_ref().is_some_and(|t| t.fixed() && t != to)
            }
            _ => false,
        })
}

/// The proof of the step's spelling, `written`, from the item's proof
/// `term`, whose Lean statement is `said`, in `fields`.
pub fn read_as_written(
    term: &Printed,
    said: &Printed,
    written: &Printed,
    fields: InstanceFields,
    values: &forms::Values,
) -> Tactic {
    let spelt = spelling(said, written);
    let mut steps = Vec::new();
    if spelt.lifted_first {
        steps.push(t::call(
            "norm_cast",
            vec![super::doc::TacticArg::At(vec![
                super::doc::Location::Hypothesis("h".to_string()),
            ])],
        ));
    }
    if !spelt.at_item.is_empty() {
        steps.push(t::simp_only(
            false,
            spelt.side_by_omega.then(|| t::call("omega", vec![])),
            spelt.at_item.iter().cloned().map(t::forwards).collect(),
            Some(t::at_h(false)),
        ));
    }
    if !spelt.at_step.is_empty() {
        steps.push(t::simp_only(
            false,
            None,
            spelt.at_step.iter().cloned().map(t::forwards).collect(),
            None,
        ));
    }
    match fields {
        InstanceFields::One => {
            if spelt.is_empty() && forms::one_term_once_set(said, written, values) {
                return Tactic::Exact(term.clone());
            }
            if casts_pushed(said) {
                steps.insert(0, t::push_cast(Some(t::at_h(true))));
            }
            if steps.is_empty() {
                return Tactic::Exact(term.clone());
            }
            steps.push(Tactic::Exact(t::hyp("h")));
        }
        InstanceFields::Wider => {
            if steps.is_empty() {
                return t::exact_mod_cast(term.clone());
            }
            steps.push(t::exact_mod_cast(t::hyp("h")));
        }
        // A rational statement is not found inside a real one, `norm_cast`
        // lifting only to casts of integers: the step is lifted to ℝ
        // instead (`rify`), the item's compound casts pushed down as the
        // step's are there, and the two meet by moving their casts alike.
        InstanceFields::RealAtRationals => {
            steps.insert(0, t::call("rify", vec![]));
            if casts_pushed(said) {
                steps.insert(1, t::push_cast(Some(t::at_h(true))));
            }
            steps.push(t::exact_mod_cast(t::hyp("h")));
        }
    }
    t::on_h(term, steps)
}

/// The proof of a claim of real numbers from `term`, an item over ℂ given
/// real numbers cast up, whose Lean statement is `said`: each operation the
/// item applies in ℂ to casts of reals read as the cast of the real one,
/// right to left by Mathlib's `Complex.ofReal_*` (`exp (↑a + 1)` as `↑(exp
/// (a + 1))`), and the two then met by moving their casts alike. A complex
/// power of a real is the cast of its real power only at a base not below
/// 0 (`Complex.ofReal_cpow`), which `positivity` shows of the base.
pub fn read_from_complex(term: &Printed, said: &Printed) -> Tactic {
    let facts = complex_operations(said);
    let powers = facts.contains(&"Complex.ofReal_cpow");
    t::on_h(
        term,
        vec![
            t::simp_only(
                false,
                powers.then(|| t::call("positivity", vec![])),
                facts
                    .into_iter()
                    .map(|f| t::backwards(t::lemma(f)))
                    .collect(),
                Some(t::at_h(false)),
            ),
            t::exact_mod_cast(t::hyp("h")),
        ],
    )
}

/// The `Complex.ofReal_*` fact of each operation the statement applies in
/// ℂ, in the order first met.
fn complex_operations(said: &Printed) -> Vec<&'static str> {
    let mut out = Vec::new();
    for node in said.walk() {
        if let Some(fact) = complex_operation(node) {
            if !out.contains(&fact) {
                out.push(fact);
            }
        }
    }
    out
}

/// The `Complex.ofReal_*` fact that reads the node, an operation in ℂ, as
/// the cast of the real one; None of any other node.
fn complex_operation(node: &Printed) -> Option<&'static str> {
    let complex = Some(LeanType::Num(Num::Complex));
    match &node.kind {
        TermKind::Numeral(d) if node.ty == complex => Some(match d.as_str() {
            "0" => "Complex.ofReal_zero",
            "1" => "Complex.ofReal_one",
            _ => "Complex.ofReal_ofNat",
        }),
        TermKind::Cast {
            inner,
            to: LeanType::Num(Num::Complex),
        } => match innermost(inner).ty {
            Some(LeanType::Num(Num::Int)) => Some("Complex.ofReal_intCast"),
            Some(LeanType::Num(Num::Nat)) => Some("Complex.ofReal_natCast"),
            _ => None,
        },
        TermKind::Infix { op, rhs, .. } if node.ty == complex => match op.symbol {
            "+" => Some("Complex.ofReal_add"),
            "-" => Some("Complex.ofReal_sub"),
            "*" => Some("Complex.ofReal_mul"),
            "/" => Some("Complex.ofReal_div"),
            "^" if rhs.ty == complex => Some("Complex.ofReal_cpow"),
            "^" => Some("Complex.ofReal_pow"),
            _ => None,
        },
        TermKind::Neg(_) if node.ty == complex => Some("Complex.ofReal_neg"),
        TermKind::App { head, .. } => match &innermost(head).kind {
            TermKind::Const(c) => match c.name.as_str() {
                "Complex.exp" => Some("Complex.ofReal_exp"),
                "Complex.sin" => Some("Complex.ofReal_sin"),
                "Complex.cos" => Some("Complex.ofReal_cos"),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}
