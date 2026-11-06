//! A notation's Lean template, `_1 + _2` or `Real.sqrt _1`, read once
//! into a tree whose holes `Term::instantiate` fills.
//!
//! The templates a record's `lean-builds` field writes use a small part of
//! Lean: names applied to arguments, infix operators, `¬` and `-` before a
//! term, `⌊x⌋` and `‖x‖`, `x.toNat`, a cast `(x : ℂ)`, `[ZMOD n]` after a
//! congruence, `@` before a name given every argument, and `_`.

use super::term::{Arg, ConstRef, LeanType, Op, Source, Term, TermKind};
use crate::lean::templates::Num;

/// The tree of a template's text; None where the text is not of the part
/// of Lean templates use, or leaves something unread.
pub fn read(text: &str) -> Option<Term> {
    let tokens = tokens(text);
    let mut reader = Reader { tokens, at: 0 };
    let term = reader.expr(0)?;
    (reader.at == reader.tokens.len()).then_some(term)
}

/// A template's text cut into marks and words.
fn tokens(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut word = String::new();
    for c in text.chars() {
        let mark = matches!(c, '(' | ')' | '⌊' | '⌋' | '‖' | '[' | ']' | ':');
        if c.is_whitespace() || mark {
            if !word.is_empty() {
                out.push(std::mem::take(&mut word));
            }
            if mark {
                out.push(c.to_string());
            }
        } else {
            word.push(c);
        }
    }
    if !word.is_empty() {
        out.push(word);
    }
    out
}

/// The template's tokens and how far they are read.
struct Reader {
    tokens: Vec<String>,
    at: usize,
}

impl Reader {
    fn peek(&self) -> Option<&str> {
        self.tokens.get(self.at).map(String::as_str)
    }

    fn take(&mut self) -> Option<String> {
        let t = self.tokens.get(self.at)?.clone();
        self.at += 1;
        Some(t)
    }

    fn expect(&mut self, token: &str) -> Option<()> {
        (self.take()? == token).then_some(())
    }

    /// Terms joined by infix operators binding at least `min` tightly.
    fn expr(&mut self, min: u32) -> Option<Term> {
        let mut lhs = self.prefix()?;
        while let Some(op) = self.peek().and_then(Op::of) {
            if op.prec < min {
                break;
            }
            self.at += 1;
            let (_, right) = op.needs();
            let rhs = self.expr(right)?;
            lhs = match (op.symbol, self.peek()) {
                ("≡", Some("[")) => {
                    self.at += 1;
                    self.expect("ZMOD")?;
                    let n = self.expr(0)?;
                    self.expect("]")?;
                    skeleton(TermKind::ModEq {
                        a: Box::new(lhs),
                        b: Box::new(rhs),
                        n: Box::new(n),
                    })
                }
                _ => skeleton(TermKind::Infix {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }),
            };
        }
        Some(lhs)
    }

    /// `¬ p`, `-x`, or an application.
    fn prefix(&mut self) -> Option<Term> {
        match self.peek()? {
            "¬" => {
                self.at += 1;
                Some(skeleton(TermKind::Not(Box::new(self.expr(40)?))))
            }
            word if word.len() > 1 && word.starts_with('-') => {
                let rest = word['-'.len_utf8()..].to_string();
                self.at += 1;
                Some(skeleton(TermKind::Neg(Box::new(atom_word(&rest)?))))
            }
            _ => self.application(),
        }
    }

    /// An atom applied to the atoms after it, if any.
    fn application(&mut self) -> Option<Term> {
        let explicit = self.peek().is_some_and(|w| w.starts_with('@'));
        let head = self.atom()?;
        let mut args = Vec::new();
        while self.starts_atom() {
            args.push(Arg::Explicit(self.atom()?));
        }
        if args.is_empty() && !explicit {
            return Some(head);
        }
        Some(skeleton(TermKind::App {
            head: Box::new(head),
            args,
            explicit,
        }))
    }

    /// Whether the next token begins an argument. `‖` closes a norm as
    /// well as opening one, so after a term it is the close.
    fn starts_atom(&self) -> bool {
        match self.peek() {
            Some("(" | "⌊") => true,
            Some(")" | "⌋" | "‖" | "]" | "[" | ":" | "¬") | None => false,
            Some(word) => Op::of(word).is_none(),
        }
    }

    /// A word, or a bracketed term, a cast, `⌊x⌋` or `‖x‖`.
    fn atom(&mut self) -> Option<Term> {
        match self.take()?.as_str() {
            "(" => {
                let inner = self.expr(0)?;
                if self.peek() == Some(":") {
                    self.at += 1;
                    let to = Num::read(&self.take()?)?;
                    self.expect(")")?;
                    return Some(Term {
                        kind: TermKind::Cast {
                            inner: Box::new(inner),
                            to: LeanType::Num(to),
                        },
                        ty: Some(LeanType::Num(to)),
                    });
                }
                self.expect(")")?;
                Some(inner)
            }
            "⌊" => self.enclosed("⌊", "⌋"),
            "‖" => self.enclosed("‖", "‖"),
            word => atom_word(word.strip_prefix('@').unwrap_or(word)),
        }
    }

    /// A term between two marks, the first read already.
    fn enclosed(&mut self, open: &'static str, close: &'static str) -> Option<Term> {
        let inner = self.expr(0)?;
        self.expect(close)?;
        Some(skeleton(TermKind::Enclosed {
            open,
            close,
            inner: Box::new(inner),
        }))
    }
}

/// A word as a term: `_`, a hole `_1` with `.toNat` after it or not, a
/// numeral, or a name.
fn atom_word(word: &str) -> Option<Term> {
    if word == "_" {
        return Some(skeleton(TermKind::Elided));
    }
    if let Some(rest) = word.strip_prefix('_') {
        let (number, field) = match rest.split_once('.') {
            Some((n, f)) => (n, Some(f)),
            None => (rest, None),
        };
        let hole = skeleton(TermKind::Hole(number.parse().ok()?));
        return match field {
            None => Some(hole),
            Some("toNat") => Some(skeleton(TermKind::ToNat(Box::new(hole)))),
            Some(_) => None,
        };
    }
    if word.chars().all(|c| c.is_ascii_digit()) {
        return Some(skeleton(TermKind::Numeral(word.to_string())));
    }
    Some(skeleton(TermKind::Const(ConstRef {
        name: word.to_string(),
        source: source_of(word),
    })))
}

/// Where a name a template writes comes from: a bridge module for
/// `LeanBridges.M.x`, Mathlib for any other.
fn source_of(name: &str) -> Source {
    match name
        .strip_prefix("LeanBridges.")
        .and_then(|r| r.split_once('.'))
    {
        Some((module, _)) => Source::Bridge(module.to_string()),
        None => Source::Mathlib,
    }
}

/// A node of a template, whose type its holes settle when it is filled.
fn skeleton(kind: TermKind) -> Term {
    Term { kind, ty: None }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_kind_a_template_writes_reads_and_prints_back() {
        for text in [
            "_1 + _2",
            "_1 - _2",
            "_1 * _2",
            "_1 / _2",
            "_1 ^ _2",
            "-_1",
            "¬ _1",
            "_1 ∧ _2",
            "⌊_1⌋",
            "‖_1‖",
            "abs _1",
            "Real.exp 1",
            "Complex.I",
            "Nat.Prime _1.toNat",
            "ArithmeticFunction.sigma 1 _1 = 2 * _1",
            "_1 ^ (1 / 2 : ℂ)",
            "_1 ≡ _2 [ZMOD _3]",
            "@ite _ _2 (Classical.propDecidable _2) _1 _3",
            "Polynomial.aeval _2 (Polynomial.bernoulli _1)",
            "IsAlgebraic ℤ _1",
            "LeanBridges.Divisibility.mod _1 _2",
        ] {
            let tree = read(text).unwrap_or_else(|| panic!("{text} reads"));
            assert_eq!(tree.text(), text);
        }
    }

    #[test]
    fn a_bridge_name_comes_from_its_module() {
        let tree = read("LeanBridges.Counting.choose _1 _2").expect("it reads");
        let sources: Vec<&Source> =
            tree.constants().iter().map(|c| &c.source).collect();
        assert_eq!(sources, [&Source::Bridge("Counting".to_string())]);
    }
}
