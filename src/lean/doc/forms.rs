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
    /// A count, `ncard` in one and `encard` in the other.
    Count { item: CountForm, line: CountForm },
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
            FormDifference::Count { item, line } => format!(
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
/// form the writer chose.
pub fn differences(item: &Term, line: &Term) -> Vec<FormDifference> {
    let mut out = Vec::new();
    compare(&pushed(item), &pushed(line), &mut out);
    out
}

/// The term with every cast taken down as far as `push_cast` takes it.
fn pushed(term: &Term) -> Term {
    let mut out = match &term.kind {
        TermKind::Cast { inner, to } => cast_down(inner, to),
        _ => term.clone(),
    };
    for child in out.children_mut() {
        *child = pushed(child);
    }
    out
}

/// `(x : to)` with the cast taken onto x's parts: a numeral is written at
/// `to`; a cast of a cast is one cast; through + · and ^ (onto the base),
/// through − and negation outside ℕ, whose subtraction stops at 0, and
/// through / in a field, whose division is exact.
fn cast_down(inner: &Term, to: &LeanType) -> Term {
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
        TermKind::Paren(x) | TermKind::Cast { inner: x, .. } => cast_down(x, to),
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
        TermKind::Infix { op, lhs, rhs } if *op == Op::POWER => at(TermKind::Infix {
            op: *op,
            lhs: Box::new(cast(lhs)),
            rhs: rhs.clone(),
        }),
        TermKind::Neg(x) if !natural => at(TermKind::Neg(Box::new(cast(x)))),
        _ => cast(inner),
    }
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

fn compare(item: &Term, line: &Term, out: &mut Vec<FormDifference>) {
    let (item, line) = (bare(item), bare(line));
    match (&item.kind, &line.kind) {
        (TermKind::Count { set: a, form: f }, TermKind::Count { set: b, form: g }) => {
            if f != g {
                out.push(FormDifference::Count { item: *f, line: *g });
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
        let found =
            differences(&count(CountForm::Extended), &count(CountForm::Natural));
        assert_eq!(
            found,
            [FormDifference::Count {
                item: CountForm::Extended,
                line: CountForm::Natural
            }]
        );
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
        assert!(differences(&whole, &parts).is_empty());
    }

    #[test]
    fn a_cast_over_a_natural_difference_stays() {
        use super::super::term::Op;
        let nat = |n: &str| Term::letter(n, LeanType::Num(Num::Nat));
        let whole = to_rat(infix(Op::MINUS, nat("a"), nat("b"), Num::Nat));
        let parts = infix(Op::MINUS, to_rat(nat("a")), to_rat(nat("b")), Num::Rat);
        assert!(!differences(&whole, &parts).is_empty());
    }

    #[test]
    fn a_term_in_one_form_on_both_sides_is_not() {
        assert!(
            differences(&count(CountForm::Natural), &count(CountForm::Natural))
                .is_empty()
        );
    }
}
