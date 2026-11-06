//! Whether two statements write one term in one form: what a citation's
//! item says once its letters are given, and the line it proves.
//!
//! The two are compared node by node. Where they part, the place is
//! reported if it is one of the forms the writer chooses: a count taken in
//! ℕ or in ℕ∞, a whole number taken to ℕ or not, a term cast to one type or
//! another. Any other parting, a sentence the item says otherwise than the
//! line, is no question of form and is not reported.

use super::term::{Arg, CountForm, LeanType, Piece, Term, TermKind};

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
/// different forms; none where they agree.
pub fn differences(item: &Term, line: &Term) -> Vec<FormDifference> {
    let mut out = Vec::new();
    compare(item, line, &mut out);
    out
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
    use crate::lean::templates::Num;

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

    #[test]
    fn a_term_in_one_form_on_both_sides_is_not() {
        assert!(
            differences(&count(CountForm::Natural), &count(CountForm::Natural))
                .is_empty()
        );
    }
}
