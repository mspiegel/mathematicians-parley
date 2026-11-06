//! The one place Lean text is made from the document model.
//!
//! A term is bracketed only where Lean would read it otherwise: each kind
//! has a precedence, and each place a term stands needs one at least
//! (`Term::at`), as `Printed::at` brackets the writer's text.

use super::tactic::{Proof, Tactic};
use super::term::{Arg, CountForm, LeanType, Quant, Term, TermKind};
use crate::lean::expr::{bracketed, things_name, APP, GENERAL, MAX};

impl LeanType {
    /// How Lean writes the type.
    pub fn text(&self) -> String {
        match self {
            LeanType::Num(n) => n.lean().to_string(),
            LeanType::General => GENERAL.to_string(),
            LeanType::ENat => "ℕ∞".to_string(),
            LeanType::Prop => "Prop".to_string(),
            LeanType::Set(m) => format!("Set {}", bracketed(&m.text())),
            LeanType::Things(var) => things_name(*var),
            LeanType::Elements(g) => crate::lean::names::letter(g),
            LeanType::Fun { from, to } => format!("{} → {}", from.text(), to.text()),
        }
    }
}

impl Term {
    /// The precedence of the term's outermost operator.
    pub fn prec(&self) -> u32 {
        match &self.kind {
            TermKind::Raw { prec, .. } => *prec,
            TermKind::App { .. } => APP,
            TermKind::Infix { op, .. } => op.prec,
            TermKind::ModEq { .. } => 50,
            TermKind::Neg(_) => 75,
            TermKind::Quantified { .. } => 0,
            TermKind::Letter(_)
            | TermKind::Const(_)
            | TermKind::Numeral(_)
            | TermKind::Hole(_)
            | TermKind::Elided
            | TermKind::Enclosed { .. }
            | TermKind::Not(_)
            | TermKind::Cast { .. }
            | TermKind::Count { .. }
            | TermKind::ToNat(_)
            | TermKind::Field { .. }
            | TermKind::Paren(_) => MAX,
        }
    }

    /// The text, bracketed unless it binds at least as tightly as `need`.
    pub fn at(&self, need: u32) -> String {
        if self.prec() >= need {
            self.text()
        } else {
            format!("({})", self.text())
        }
    }

    /// The term as Lean text.
    pub fn text(&self) -> String {
        match &self.kind {
            TermKind::Raw { text, .. } => text.clone(),
            TermKind::Letter(name) => name.clone(),
            TermKind::Const(c) => c.name.clone(),
            TermKind::Numeral(digits) => digits.clone(),
            TermKind::Hole(i) => format!("_{i}"),
            TermKind::Elided => "_".to_string(),
            TermKind::Enclosed { open, close, inner } => {
                format!("{open}{}{close}", inner.text())
            }
            TermKind::ModEq { a, b, n } => {
                format!("{} ≡ {} [ZMOD {}]", a.at(51), b.at(51), n.at(MAX))
            }
            TermKind::App {
                head,
                args,
                explicit,
            } => {
                let mut out = match explicit {
                    true => format!("@{}", head.at(MAX)),
                    false => head.at(MAX),
                };
                for a in args {
                    out.push(' ');
                    out.push_str(&arg_text(a));
                }
                out
            }
            TermKind::Infix { op, lhs, rhs } => {
                let (left, right) = op.needs();
                format!("{} {} {}", lhs.at(left), op.symbol, rhs.at(right))
            }
            TermKind::Not(p) => format!("¬ {}", p.at(40)),
            TermKind::Neg(x) => format!("-{}", x.at(76)),
            TermKind::Cast { inner, to } => {
                format!("({} : {})", inner.text(), to.text())
            }
            TermKind::Count { set, form } => {
                let field = match form {
                    CountForm::Natural => "ncard",
                    CountForm::Extended => "encard",
                };
                format!("{}.{field}", set.at(MAX))
            }
            TermKind::ToNat(x) => format!("{}.toNat", x.at(MAX)),
            TermKind::Field { inner, field } => format!("{}.{field}", inner.at(MAX)),
            TermKind::Quantified {
                quant,
                letter,
                letter_ty,
                guard,
                body,
            } => {
                let ty = letter_ty.text();
                match (quant, guard) {
                    (Quant::Exists, None) => {
                        format!("∃ {letter} : {ty}, {}", body.text())
                    }
                    (Quant::Exists, Some(g)) => {
                        format!("∃ {letter} : {ty}, {} ∧ {}", g.text(), body.at(36))
                    }
                    (Quant::ForAll, None) => {
                        format!("∀ {letter} : {ty}, {}", body.text())
                    }
                    (Quant::ForAll, Some(g)) => {
                        format!("∀ {letter} : {ty}, {} → {}", g.text(), body.at(25))
                    }
                }
            }
            TermKind::Paren(inner) => format!("({})", inner.text()),
        }
    }
}

/// An argument as it stands after what is applied: by place, bracketed as
/// an argument, or by name.
fn arg_text(arg: &Arg) -> String {
    match arg {
        Arg::Explicit(t) => t.at(MAX),
        Arg::Named { name, value } => format!("({name} := {})", value.text()),
    }
}

impl Tactic {
    /// The tactic as Lean text, on one line.
    pub fn text(&self) -> String {
        match self {
            Tactic::Raw(text) => text.clone(),
            Tactic::Exact(t) => format!("exact {}", t.text()),
            Tactic::Call { tactic, args } => {
                let mut out = tactic.name.to_string();
                for a in args {
                    out.push(' ');
                    out.push_str(&a.at(MAX));
                }
                out
            }
            Tactic::First(ts) => {
                let alternatives: Vec<String> = ts.iter().map(Tactic::text).collect();
                format!("first | {}", alternatives.join(" | "))
            }
            Tactic::Seq(ts) => {
                let steps: Vec<String> = ts.iter().map(Tactic::text).collect();
                steps.join("; ")
            }
            Tactic::Group(t) => format!("({})", t.text()),
            Tactic::Try(t) => format!("try {}", t.text()),
            Tactic::AllGoals(t) => format!("all_goals {}", t.text()),
        }
    }
}

impl Proof {
    /// The proof as Lean text, on one line.
    pub fn text(&self) -> String {
        match self {
            Proof::Term(t) => t.text(),
            Proof::By(t) => format!("by {}", t.text()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::tactic::TacticRef;
    use super::super::term::{ConstRef, Op, Source};
    use super::*;
    use crate::lean::templates::Num;

    fn letter(name: &str, n: Num) -> Term {
        Term::of(TermKind::Letter(name.to_string()), LeanType::Num(n))
    }

    fn infix(symbol: &str, lhs: Term, rhs: Term, ty: LeanType) -> Term {
        let op = Op::of(symbol).expect("an operator");
        Term::of(
            TermKind::Infix {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            ty,
        )
    }

    #[test]
    fn a_sum_under_a_product_is_bracketed_and_a_product_under_a_sum_is_not() {
        let int = LeanType::Num(Num::Int);
        let sum = infix(
            "+",
            letter("a", Num::Int),
            letter("b", Num::Int),
            int.clone(),
        );
        let product = infix("*", sum.clone(), letter("c", Num::Int), int.clone());
        assert_eq!(product.text(), "(a + b) * c");
        let other = infix(
            "*",
            letter("a", Num::Int),
            letter("b", Num::Int),
            int.clone(),
        );
        assert_eq!(
            infix("+", other, letter("c", Num::Int), int).text(),
            "a * b + c"
        );
    }

    #[test]
    fn subtraction_brackets_a_difference_on_its_right_only() {
        let int = LeanType::Num(Num::Int);
        let ab = infix(
            "-",
            letter("a", Num::Int),
            letter("b", Num::Int),
            int.clone(),
        );
        let left = infix("-", ab.clone(), letter("c", Num::Int), int.clone());
        let right = infix("-", letter("c", Num::Int), ab, int);
        assert_eq!(left.text(), "a - b - c");
        assert_eq!(right.text(), "c - (a - b)");
    }

    #[test]
    fn a_count_a_cast_and_a_quantifier_print_as_the_writer_writes_them() {
        let set = Term::of(
            TermKind::Letter("d".to_string()),
            LeanType::Set(Box::new(LeanType::Num(Num::Int))),
        );
        let count = Term::of(
            TermKind::Count {
                set: Box::new(set),
                form: CountForm::Natural,
            },
            LeanType::Num(Num::Nat),
        );
        let cast = Term::cast(count, LeanType::Num(Num::Int));
        let m = letter("m", Num::Int);
        let one = Term::of(TermKind::Numeral("1".to_string()), LeanType::Num(Num::Int));
        let claim = infix(
            "=",
            cast,
            infix("-", m, one, LeanType::Num(Num::Int)),
            LeanType::Prop,
        );
        assert_eq!(claim.text(), "(d.ncard : ℤ) = m - 1");
        let quantified = Term::of(
            TermKind::Quantified {
                quant: Quant::Exists,
                letter: "m₀".to_string(),
                letter_ty: LeanType::Num(Num::Nat),
                guard: None,
                body: Box::new(claim),
            },
            LeanType::Prop,
        );
        assert_eq!(quantified.text(), "∃ m₀ : ℕ, (d.ncard : ℤ) = m - 1");
    }

    #[test]
    fn named_arguments_and_alternatives_print_on_one_line() {
        let item = Term::of(
            TermKind::Const(ConstRef {
                name: "Parley.Items.Stdlib.Counting.mun_card_singleton".to_string(),
                source: Source::Item("Parley.Items.Stdlib.Counting".to_string()),
            }),
            LeanType::Prop,
        );
        let applied = Term::of(
            TermKind::App {
                head: Box::new(item),
                args: vec![Arg::Named {
                    name: "x".to_string(),
                    value: Term::raw("(∅ : Set α)", MAX),
                }],
                explicit: false,
            },
            LeanType::Prop,
        );
        let side = Tactic::Call {
            tactic: TacticRef {
                name: "parley_side",
                source: Source::Bridge("Tactics".to_string()),
            },
            args: Vec::new(),
        };
        let proof = Proof::By(Tactic::First(vec![
            Tactic::Exact(applied.clone()),
            Tactic::Group(Box::new(Tactic::Seq(vec![
                Tactic::Raw("have h := (x)".to_string()),
                side,
            ]))),
        ]));
        assert_eq!(
            proof.text(),
            "by first | exact Parley.Items.Stdlib.Counting.mun_card_singleton (x := (∅ : Set α)) | (have h := (x); parley_side)"
        );
        assert_eq!(applied.constants().len(), 1);
    }
}
