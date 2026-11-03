//! The gate's read-back: whether each statement Lean proved does the
//! page's arithmetic.
//!
//! The page computes every number as a number: its subtraction never stops
//! at 0 and its division never rounds. Lean computes in a type, and a
//! subtraction in ℕ or a division in ℤ is another operation. So each
//! statement Lean elaborated, as lean4export writes it, is read for the
//! arithmetic it does and the type of each operation, and compared with the
//! page's tree: every operation the page writes is in Lean's statement, as
//! many of each kind, and none is done in a type that computes otherwise
//! (`export::unfaithful`). A membership the letter's type already gives is
//! no statement in Lean, and its arithmetic is not counted.

use std::collections::BTreeMap;

use super::expr::Writer;
use crate::formula::Node;
use crate::notations::{
    DIVIDED, FOR_ALL, MEMBERSHIP, MINUS, PLUS, POWER, SUPERSCRIPT, THERE_IS, TIMES,
    UNARY_MINUS,
};

/// The arithmetic the page writes in these sentences, by the name
/// `export::operation` gives each kind.
pub fn page_arithmetic(writer: &Writer, sentences: &[Node]) -> BTreeMap<String, usize> {
    let mut out = BTreeMap::new();
    for s in sentences {
        count(writer, s, &mut out);
    }
    out
}

fn count(writer: &Writer, node: &Node, out: &mut BTreeMap<String, usize>) {
    // A function on a range, t : {1, …, n + 1} → ℝ, is a Lean function on
    // ℤ, so its statement writes no arithmetic of the range's ends.
    if node.notation() == crate::notations::FUNCTION_TYPE {
        return;
    }
    // A membership or a quantifier Lean states as nothing says nothing.
    if matches!(node.notation(), MEMBERSHIP | FOR_ALL | THERE_IS) {
        if let crate::outcome::Route::Built(p) = writer.formula(node) {
            if p.text == "True" {
                return;
            }
            // A quantifier the writer states with its body `True`, ∀ x ∈
            // [0, 1], True of "1/(1 + x²) ∈ ℝ", says only its set.
            if let ([_, set, _], true) =
                (node.children.as_slice(), p.text.ends_with(", True"))
            {
                count(writer, set, out);
                return;
            }
        }
    }
    // f tends to L at c is written with c twice, the point and the point
    // left out of the domain: `nhdsWithin c (D \ {c})`.
    if let ("function-limit", [_, _, at]) =
        (&*node.notation_name(), node.children.as_slice())
    {
        count(writer, at, out);
    }
    let spelling = node.spelling();
    let op = if spelling == PLUS {
        Some("addition")
    } else if spelling == MINUS {
        Some("subtraction")
    } else if spelling == TIMES
        || matches!(&*node.notation_name(), "group-operation" | "coset")
    {
        // A group's operation a·b is its multiplication, Lean's `*` on G;
        // a coset gH is g times each element of H, `(g * ·) '' H`.
        Some("multiplication")
    } else if spelling == DIVIDED {
        Some("division")
    } else if matches!(node.notation(), POWER | SUPERSCRIPT) {
        Some("power")
    } else if node.notation() == UNARY_MINUS {
        Some("negation")
    } else {
        None
    };
    if let Some(op) = op {
        *out.entry(op.to_string()).or_insert(0) += 1;
    }
    for c in &node.children {
        count(writer, c, out);
    }
}

/// What differs between the page's arithmetic and Lean's, each said once;
/// none where they agree.
pub fn differences(
    page: &BTreeMap<String, usize>,
    lean: &BTreeMap<(String, String), usize>,
) -> Vec<String> {
    let mut out = Vec::new();
    let mut lean_counts: BTreeMap<&str, usize> = BTreeMap::new();
    for ((op, ty), n) in lean {
        *lean_counts.entry(op.as_str()).or_insert(0) += n;
        if let Some(why) = super::export::unfaithful(op, ty) {
            out.push(why);
        }
    }
    let ops: std::collections::BTreeSet<&str> = page
        .keys()
        .map(String::as_str)
        .chain(lean_counts.keys().copied())
        .collect();
    for op in ops {
        let p = page.get(op).copied().unwrap_or(0);
        let l = lean_counts.get(op).copied().unwrap_or(0);
        if p != l {
            out.push(format!("the page writes {p} {op} and Lean's statement {l}"));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_subtraction_in_the_naturals_is_not_the_pages() {
        let page = BTreeMap::from([("subtraction".to_string(), 1)]);
        let lean =
            BTreeMap::from([(("subtraction".to_string(), "Nat".to_string()), 1)]);
        assert_eq!(
            differences(&page, &lean),
            vec!["subtraction in ℕ, where it stops at 0".to_string()]
        );
        let rational =
            BTreeMap::from([(("subtraction".to_string(), "Rat".to_string()), 1)]);
        assert!(differences(&page, &rational).is_empty());
    }

    #[test]
    fn an_operation_lean_lost_is_reported() {
        let page = BTreeMap::from([("addition".to_string(), 2)]);
        let lean = BTreeMap::from([(("addition".to_string(), "Int".to_string()), 1)]);
        assert_eq!(
            differences(&page, &lean),
            vec!["the page writes 2 addition and Lean's statement 1".to_string()]
        );
    }
}
