//! Whether two statements write one term in one form: what a citation's
//! item says once its letters are given, and the line it proves.
//!
//! The two are compared node by node. Where they part, the place is
//! reported if it is one of the forms the writer chooses: a count taken in
//! ℕ or in ℕ∞, a whole number taken to ℕ or not, a term cast to one type or
//! another. Any other parting, a sentence the item says otherwise than the
//! line, is no question of form and is not reported.

use super::term::{Arg, CountForm, LeanType, Piece, Term, TermKind};
use crate::lean::templates::Num;

/// One place two statements write a term in different forms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FormDifference {
    /// A count, `ncard` in one and `encard` in the other, of one set as each
    /// writes it, which may differ inside in form.
    Count {
        item: CountForm,
        line: CountForm,
        item_set: Term,
        line_set: Term,
    },
    /// A whole number taken to ℕ, `n.toNat`, in one and not the other.
    ToNat { in_item: bool },
    /// A term cast to a type in one and not, or to another, in the other.
    Cast {
        item: Option<LeanType>,
        line: Option<LeanType>,
    },
}

impl FormDifference {
    /// What differs, in words.
    pub fn describe(&self) -> String {
        let count = |f: &CountForm| match f {
            CountForm::Natural => "a natural number (ncard)",
            CountForm::Extended => "in ℕ∞ (encard)",
        };
        let cast = |t: &Option<LeanType>| match t {
            Some(t) => format!("cast to {}", t.text()),
            None => "not cast".to_string(),
        };
        match self {
            FormDifference::Count { item, line, .. } => format!(
                "a count the item writes {} and the line {}",
                count(item),
                count(line)
            ),
            FormDifference::ToNat { in_item: true } => {
                "a whole number the item takes to ℕ (.toNat) and the line does not"
                    .to_string()
            }
            FormDifference::ToNat { in_item: false } => {
                "a whole number the line takes to ℕ (.toNat) and the item does not"
                    .to_string()
            }
            FormDifference::Cast { item, line } => format!(
                "a term the item writes {} and the line {}",
                cast(item),
                cast(line)
            ),
        }
    }
}

/// Every place the item's statement and the line write one term in
/// different forms; none where they agree. A cast is first taken down onto
/// the parts of what it casts on both sides, as `push_cast` takes it:
/// `((a - b : ℤ) : ℚ)` and `(a : ℚ) - (b : ℚ)` are one form, which Lean
/// moves between by that one tactic, and only a difference it leaves is a
/// form the writer chose. A relation one side states in a narrower type
/// than the other, sin(a + b) = … over ℂ cited by a line in ℝ, or an item
/// in ℤ cited by a row of a calculation in ℚ, is compared cast up to the
/// wider, as `exact_mod_cast` takes the one to the other.
///
/// `widen` gives the constant that is a library function at another type,
/// `Complex.cos` of `Real.cos` at ℂ (`Templates::same_function_at`): a
/// cast of the function's value is the function of the cast argument.
pub fn differences(item: &Term, line: &Term, widen: &Widen) -> Vec<FormDifference> {
    let mut out = Vec::new();
    let (item, line) = (pushed(item, widen), pushed(line, widen));
    let (item, line) = (in_naturals(&item), in_naturals(&line));
    let line = lifted(&line, &item, widen).unwrap_or(line);
    let item = lifted(&item, &line, widen).unwrap_or(item);
    compare(&item, &line, &mut out);
    out
}

/// A relation between natural numbers cast to one type, `(a : ℤ) ≤ (b :
/// ℤ)` or `(a : ℕ∞) = (1 : ℕ∞)`, as the relation in ℕ itself, `a ≤ b`,
/// which `norm_cast` takes it to (`Nat.cast_le`, `Nat.cast_inj`); any
/// other term as it is.
fn in_naturals(term: &Term) -> Term {
    let natural = |t: &Term| -> Option<Term> {
        match &bare(t).kind {
            TermKind::Cast { inner, .. }
                if inner.ty == Some(LeanType::Num(Num::Nat)) =>
            {
                Some((**inner).clone())
            }
            TermKind::Numeral(d) => Some(Term::of(
                TermKind::Numeral(d.clone()),
                LeanType::Num(Num::Nat),
            )),
            _ => None,
        }
    };
    if let TermKind::Infix { op, lhs, rhs } = &bare(term).kind {
        if term.ty == Some(LeanType::Prop) {
            if let (Some(l), Some(r)) = (natural(lhs), natural(rhs)) {
                return Term::of(
                    TermKind::Infix {
                        op: *op,
                        lhs: Box::new(l),
                        rhs: Box::new(r),
                    },
                    LeanType::Prop,
                );
            }
        }
    }
    term.clone()
}

/// Whether the line is the item's equation turned round: its left side
/// alike the item's right and not its left, but for forms.
pub fn turned_round(item: &Term, line: &Term) -> bool {
    use super::term::Op;
    match (&bare(item).kind, &bare(line).kind) {
        (
            TermKind::Infix {
                op: a,
                lhs: il,
                rhs: ir,
            },
            TermKind::Infix {
                op: b,
                lhs: ll,
                rhs: lr,
            },
        ) => {
            *a == Op::EQUALS
                && a == b
                && alike(il, lr)
                && alike(ir, ll)
                && !alike(il, ll)
        }
        _ => false,
    }
}

/// An equation with its sides swapped; any other term as it is.
pub fn turned(term: &Term) -> Term {
    match &bare(term).kind {
        TermKind::Infix { op, lhs, rhs } => Term {
            kind: TermKind::Infix {
                op: *op,
                lhs: rhs.clone(),
                rhs: lhs.clone(),
            },
            ty: term.ty.clone(),
        },
        _ => term.clone(),
    }
}

/// The term with each count in ℕ∞ of one of the sets, `S.encard`, written
/// as its count in ℕ cast up, `(S.ncard : ℕ∞)`: what rewriting by
/// `Set.Finite.cast_ncard_eq` backwards makes of it.
pub fn with_natural_counts(term: &Term, sets: &[Term]) -> Term {
    let mut out = term.clone();
    if let TermKind::Count {
        set,
        form: CountForm::Extended,
    } = &term.kind
    {
        if sets.iter().any(|s| alike(s, set)) {
            let natural = Term::of(
                TermKind::Count {
                    set: set.clone(),
                    form: CountForm::Natural,
                },
                LeanType::Num(Num::Nat),
            );
            return Term::of(
                TermKind::Cast {
                    inner: Box::new(natural),
                    to: LeanType::ENat,
                },
                LeanType::ENat,
            );
        }
    }
    for child in out.children_mut() {
        *child = with_natural_counts(child, sets);
    }
    out
}

/// The constant that is a library function at another type.
pub type Widen<'a> = dyn Fn(&str, Num) -> Option<super::term::ConstRef> + 'a;

/// The relation with its sides cast up to the type the other's are in,
/// where both are one relation and the other's is wider; None where they
/// are not.
fn lifted(narrow: &Term, other: &Term, widen: &Widen) -> Option<Term> {
    let (
        TermKind::Infix { op: b, lhs, rhs },
        TermKind::Infix {
            op: a,
            lhs: other_lhs,
            ..
        },
    ) = (&bare(narrow).kind, &bare(other).kind)
    else {
        return None;
    };
    let (Some(LeanType::Num(wide)), Some(LeanType::Num(own))) =
        (&other_lhs.ty, &lhs.ty)
    else {
        return None;
    };
    if a != b || own >= wide {
        return None;
    }
    let to = LeanType::Num(*wide);
    Some(Term {
        kind: TermKind::Infix {
            op: *b,
            lhs: Box::new(pushed(&cast_down(lhs, &to, widen), widen)),
            rhs: Box::new(pushed(&cast_down(rhs, &to, widen), widen)),
        },
        ty: narrow.ty.clone(),
    })
}

/// The term with every cast taken down as far as `push_cast` takes it.
fn pushed(term: &Term, widen: &Widen) -> Term {
    let mut out = match &term.kind {
        TermKind::Cast { inner, to } => cast_down(inner, to, widen),
        // A map given by its values applied, `(fun x => t) a`, is t at a,
        // as Lean reads it.
        TermKind::App { head, args, .. } => match (&bare(head).kind, args.as_slice()) {
            (
                TermKind::Quantified {
                    quant: super::term::Quant::Fun,
                    letter,
                    body,
                    ..
                },
                [Arg::Explicit(a)],
            ) => {
                let given =
                    std::collections::BTreeMap::from([(letter.clone(), a.clone())]);
                return pushed(&body.substituted(&given), widen);
            }
            _ => term.clone(),
        },
        // A numeral taken to ℕ is the numeral, `(3 : ℤ).toNat` 3, and a
        // natural number cast to ℤ and taken back is itself.
        TermKind::ToNat(inner) => match &bare(inner).kind {
            TermKind::Numeral(digits) => Term {
                kind: TermKind::Numeral(digits.clone()),
                ty: Some(LeanType::Num(Num::Nat)),
            },
            TermKind::Cast { inner: x, .. }
                if x.ty == Some(LeanType::Num(Num::Nat)) =>
            {
                (**x).clone()
            }
            _ => term.clone(),
        },
        _ => term.clone(),
    };
    for child in out.children_mut() {
        *child = pushed(child, widen);
    }
    out
}

/// `(x : to)` with the cast taken onto x's parts: a numeral is written at
/// `to`; a cast of a cast is one cast; through + · and ^ (onto the base),
/// through − and negation outside ℕ, whose subtraction stops at 0, through
/// / in a field, whose division is exact, and through a library function
/// that has a form at `to`.
fn cast_down(inner: &Term, to: &LeanType, widen: &Widen) -> Term {
    use super::term::Op;
    let at = |kind: TermKind| Term {
        kind,
        ty: Some(to.clone()),
    };
    let cast = |x: &Term| match x.ty.as_ref() == Some(to) {
        true => x.clone(),
        false => at(TermKind::Cast {
            inner: Box::new(x.clone()),
            to: to.clone(),
        }),
    };
    let from = inner.ty.as_ref();
    let natural = matches!(from, Some(LeanType::Num(Num::Nat)));
    let field = matches!(
        from,
        Some(LeanType::Num(Num::Rat | Num::Real | Num::Complex))
    );
    match &inner.kind {
        TermKind::Paren(x) | TermKind::Cast { inner: x, .. } => cast_down(x, to, widen),
        // A sum or product over a Finset, onto its body (`Nat.cast_sum`,
        // `Int.cast_prod`): the last of its terms.
        // An integer power, `x ^ m` with m in ℤ, onto its base
        // (`Rat.cast_zpow`).
        TermKind::Notation { pieces, prec } if matches!(pieces.as_slice(), [Piece::Term { .. }, Piece::Text(t), Piece::Term { .. }] if t == " ^ ") =>
        {
            let mut pieces = pieces.clone();
            if let Some(Piece::Term { term, .. }) = pieces.first_mut() {
                **term = cast(term);
            }
            at(TermKind::Notation {
                pieces,
                prec: *prec,
            })
        }
        TermKind::Notation { pieces, prec } if over_finset(pieces) => {
            let mut pieces = pieces.clone();
            if let Some(Piece::Term { term, .. }) = pieces.last_mut() {
                **term = cast(term);
            }
            at(TermKind::Notation {
                pieces,
                prec: *prec,
            })
        }
        TermKind::App {
            head,
            args,
            explicit,
        } => {
            // `abs` is one function at every ordered type, ↑|a| = |↑a|
            // (`Int.cast_abs`, `Rat.cast_abs`).
            let wider = match (&head.kind, to) {
                (TermKind::Const(c), LeanType::Num(_)) if c.name == "abs" => {
                    Some(c.clone())
                }
                (TermKind::Const(c), LeanType::Num(n)) => widen(&c.name, *n),
                _ => None,
            };
            match wider {
                Some(c) => at(TermKind::App {
                    head: Box::new(Term {
                        kind: TermKind::Const(c),
                        ty: head.ty.clone(),
                    }),
                    args: args
                        .iter()
                        .map(|a| match a {
                            Arg::Explicit(t) => Arg::Explicit(cast(t)),
                            named => named.clone(),
                        })
                        .collect(),
                    explicit: *explicit,
                }),
                None => cast(inner),
            }
        }
        TermKind::Numeral(digits) => at(TermKind::Numeral(digits.clone())),
        TermKind::Infix { op, lhs, rhs }
            if *op == Op::PLUS
                || *op == Op::TIMES
                || (*op == Op::MINUS && !natural)
                || (*op == Op::DIVIDE && field) =>
        {
            at(TermKind::Infix {
                op: *op,
                lhs: Box::new(cast(lhs)),
                rhs: Box::new(cast(rhs)),
            })
        }
        // A real power, x ^ y of a real y, which the writer writes only of
        // an x the lines show at least 0, onto both (`Complex.ofReal_cpow`);
        // any other power onto its base.
        TermKind::Infix { op, lhs, rhs } if *op == Op::POWER => {
            let real_exponent = rhs.ty == Some(LeanType::Num(Num::Real));
            at(TermKind::Infix {
                op: *op,
                lhs: Box::new(cast(lhs)),
                rhs: Box::new(match real_exponent {
                    true => cast(rhs),
                    false => (**rhs).clone(),
                }),
            })
        }
        TermKind::Neg(x) if !natural => at(TermKind::Neg(Box::new(cast(x)))),
        _ => cast(inner),
    }
}

/// Whether a notation is a sum or product over a Finset, `∑ k ∈ s, t`,
/// which a cast passes into; `∑ᶠ` over a set is not.
fn over_finset(pieces: &[Piece]) -> bool {
    matches!(pieces.first(), Some(Piece::Text(t)) if t.starts_with("∑ ") || t.starts_with("∏ "))
}

/// The term with brackets no precedence asks for taken off, and a type
/// given a term that has it already, `(2 : ℤ)` of an integer 2, which is
/// that term at its own type and no cast.
fn bare(term: &Term) -> &Term {
    match &term.kind {
        TermKind::Paren(inner) => bare(inner),
        TermKind::Cast { inner, to } if inner.ty.as_ref() == Some(to) => bare(inner),
        _ => term,
    }
}

/// Whether a natural number is the integer `x` taken to ℕ, written as it
/// stands: `natural` cast to ℤ, with the cast pushed down, is `x` in one
/// form.
fn is_to_nat_of(x: &Term, natural: &Term) -> bool {
    if natural.ty != Some(LeanType::Num(Num::Nat)) {
        return false;
    }
    let none = |_: &str, _: Num| None;
    let up = pushed(&cast_down(natural, &LeanType::Num(Num::Int), &none), &none);
    let mut parts = Vec::new();
    compare(&pushed(x, &none), &up, &mut parts);
    parts.is_empty() && alike(x, &up)
}

fn compare(item: &Term, line: &Term, out: &mut Vec<FormDifference>) {
    let (item, line) = (bare(item), bare(line));
    match (&item.kind, &line.kind) {
        (TermKind::Count { set: a, form: f }, TermKind::Count { set: b, form: g }) => {
            if f != g {
                out.push(FormDifference::Count {
                    item: *f,
                    line: *g,
                    item_set: (**a).clone(),
                    line_set: (**b).clone(),
                });
            }
            compare(a, b, out);
        }
        (TermKind::ToNat(a), TermKind::ToNat(b)) => compare(a, b, out),
        // A cast or `toNat` on one side only is a form where taking it off
        // leaves one term on both; where it leaves two, the item says
        // something else there, which is no question of form.
        (TermKind::ToNat(a) | TermKind::Cast { inner: a, .. }, _)
            if !alike(a, line) => {}
        (_, TermKind::ToNat(b) | TermKind::Cast { inner: b, .. })
            if !alike(item, b) => {}
        // x.toNat beside a natural number y that cast to ℤ is x, as
        // `push_cast` writes it: ((2 : ℤ) ^ n).toNat beside 2 ^ n.
        (TermKind::ToNat(a), _) if is_to_nat_of(a, line) => {}
        (_, TermKind::ToNat(b)) if is_to_nat_of(b, item) => {}
        (TermKind::ToNat(a), _) => {
            out.push(FormDifference::ToNat { in_item: true });
            compare(a, line, out);
        }
        (_, TermKind::ToNat(b)) => {
            out.push(FormDifference::ToNat { in_item: false });
            compare(item, b, out);
        }
        (TermKind::Cast { inner: a, to: s }, TermKind::Cast { inner: b, to: t }) => {
            if s != t {
                out.push(FormDifference::Cast {
                    item: Some(s.clone()),
                    line: Some(t.clone()),
                });
            }
            compare(a, b, out);
        }
        (TermKind::Cast { inner: a, to }, _) => {
            out.push(FormDifference::Cast {
                item: Some(to.clone()),
                line: None,
            });
            compare(a, line, out);
        }
        (_, TermKind::Cast { inner: b, to }) => {
            out.push(FormDifference::Cast {
                item: None,
                line: Some(to.clone()),
            });
            compare(item, b, out);
        }
        _ => {
            if std::mem::discriminant(&item.kind) != std::mem::discriminant(&line.kind)
            {
                return;
            }
            let (a, b) = (children(item), children(line));
            if a.len() == b.len() {
                for (x, y) in a.into_iter().zip(b) {
                    compare(x, y, out);
                }
            }
        }
    }
}

/// Whether two terms are one term but for their forms: alike once every
/// cast, `toNat` and spare bracket is taken off, with a count alike in
/// either form.
fn alike(a: &Term, b: &Term) -> bool {
    let strip = |t: &Term| -> Term {
        let mut t = t.clone();
        while let TermKind::Paren(x)
        | TermKind::Cast { inner: x, .. }
        | TermKind::ToNat(x) = t.kind
        {
            t = *x;
        }
        t
    };
    let (a, b) = (strip(a), strip(b));
    let leaves_agree = match (&a.kind, &b.kind) {
        (TermKind::Letter(x), TermKind::Letter(y)) => x == y,
        (TermKind::Numeral(x), TermKind::Numeral(y)) => x == y,
        (TermKind::Const(x), TermKind::Const(y)) => x == y,
        (TermKind::Infix { op: x, .. }, TermKind::Infix { op: y, .. }) => x == y,
        (TermKind::Count { .. }, TermKind::Count { .. }) => true,
        (x, y) => std::mem::discriminant(x) == std::mem::discriminant(y),
    };
    let (xs, ys) = (children(&a), children(&b));
    leaves_agree
        && xs.len() == ys.len()
        && xs.into_iter().zip(ys).all(|(x, y)| alike(x, y))
}

/// The terms directly inside a node, in order, as both sides are walked.
fn children(term: &Term) -> Vec<&Term> {
    match &term.kind {
        TermKind::App { args, .. } => args
            .iter()
            .map(|a| match a {
                Arg::Explicit(t) => t,
                Arg::Named { value, .. } => value,
            })
            .collect(),
        TermKind::Notation { pieces, .. } => pieces
            .iter()
            .filter_map(|p| match p {
                Piece::Term { term, .. } => Some(&**term),
                Piece::Text(_) => None,
            })
            .collect(),
        _ => term.children(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn count(form: CountForm) -> Term {
        let set = Term::letter("d", LeanType::Set(Box::new(LeanType::Num(Num::Int))));
        Term::of(
            TermKind::Count {
                set: Box::new(set),
                form,
            },
            LeanType::ENat,
        )
    }

    #[test]
    fn one_count_in_two_forms_is_reported() {
        let found = differences(
            &count(CountForm::Extended),
            &count(CountForm::Natural),
            &none,
        );
        assert_eq!(
            found,
            [FormDifference::Count {
                item: CountForm::Extended,
                line: CountForm::Natural,
                item_set: Term::letter(
                    "d",
                    LeanType::Set(Box::new(LeanType::Num(Num::Int)))
                ),
                line_set: Term::letter(
                    "d",
                    LeanType::Set(Box::new(LeanType::Num(Num::Int)))
                ),
            }]
        );
    }

    /// No library functions.
    fn none(_: &str, _: Num) -> Option<super::super::term::ConstRef> {
        None
    }

    fn int_letter(name: &str) -> Term {
        Term::letter(name, LeanType::Num(Num::Int))
    }

    fn infix(op: super::super::term::Op, lhs: Term, rhs: Term, ty: Num) -> Term {
        Term::of(
            TermKind::Infix {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            LeanType::Num(ty),
        )
    }

    fn to_rat(x: Term) -> Term {
        Term::of(
            TermKind::Cast {
                inner: Box::new(x),
                to: LeanType::Num(Num::Rat),
            },
            LeanType::Num(Num::Rat),
        )
    }

    #[test]
    fn a_cast_over_a_difference_is_the_difference_of_casts() {
        use super::super::term::Op;
        let whole =
            to_rat(infix(Op::MINUS, int_letter("a"), int_letter("b"), Num::Int));
        let parts = infix(
            Op::MINUS,
            to_rat(int_letter("a")),
            to_rat(int_letter("b")),
            Num::Rat,
        );
        assert!(differences(&whole, &parts, &none).is_empty());
    }

    #[test]
    fn a_cast_over_a_natural_difference_stays() {
        use super::super::term::Op;
        let nat = |n: &str| Term::letter(n, LeanType::Num(Num::Nat));
        let whole = to_rat(infix(Op::MINUS, nat("a"), nat("b"), Num::Nat));
        let parts = infix(Op::MINUS, to_rat(nat("a")), to_rat(nat("b")), Num::Rat);
        assert!(!differences(&whole, &parts, &none).is_empty());
    }

    #[test]
    fn a_term_in_one_form_on_both_sides_is_not() {
        assert!(differences(
            &count(CountForm::Natural),
            &count(CountForm::Natural),
            &none
        )
        .is_empty());
    }
}
