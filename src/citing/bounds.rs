//! What the page's lines say a term is at least, and whether a term is at
//! least 0: x ≥ 0 of `x > 0`, p ≥ 1 of `p ∈ ℕ`, |x| and x² by their form.
//! A square root or a real power whose base this says is at least 0 is
//! real, as Metamath proves `√x ∈ ℝ` from the line `0 ≤ x` (`resqrtcld`).
//!
//! The rule is written once, here, over a view of the terms a tool writes
//! (`BoundsAsk`): which lines are in scope, which letters are natural
//! numbers, and how a sum's term is read inside it. A tool says only those;
//! what follows from them is decided here.

use crate::formula::Node;
use crate::notations::{
    ABSOLUTE_VALUE, ADDITIVE, AT_LEAST, AT_MOST, CLOSED_INTERVAL, COMMA_CONJUNCTION,
    CONJUNCTION, EQUALITY, EULER, FACTORIAL, FOR_ALL, GREATER, IN, INTEGER_RANGE,
    JUXTAPOSITION, LESS, MEMBERSHIP, MINUS, MULTIPLICATIVE, NAME, NATURALS, NATURALS0,
    NUMBER_SYSTEMS, NUMERAL, OPEN_INTERVAL, ORDER, PI, PLUS, POWER, REAL_POWER,
    SET_BUILDER, SQUARE_ROOT, SUPERSCRIPT, TIMES,
};

/// What lines say a term is at least: x ≥ 0 of `x > 0`, p ≥ 1 of `p ∈ ℕ`.
#[derive(Clone, Debug, Default)]
pub struct SaidBounds {
    /// Each term a line bounds below, and the bound.
    pub terms: Vec<Bound>,
    /// The lines that bound a term at each integer of a range, `for all k ∈
    /// {1, …, n}, a(k) ≥ 0`: in a sum or a product over that range by the
    /// same letter, the term is so bounded.
    pub over_ranges: Vec<Node>,
}

/// A term a line says is at least a whole number.
#[derive(Clone, Debug)]
pub struct Bound {
    pub term: Node,
    pub least: i64,
    /// The sentence that says it, as the page writes it, `0 < e` or `e ∈
    /// ℕ`, from which a backend proves the bound; None of a bound the rule
    /// reads from the set a quantifier runs over, which no line says.
    pub said_by: Option<Node>,
}

impl SaidBounds {
    /// What is said of terms the letter is not in: inside a sum by a letter
    /// k, a line about another k says nothing of it.
    pub fn without_letter(&self, letter: &str) -> SaidBounds {
        SaidBounds {
            terms: self
                .terms
                .iter()
                .filter(|b| !mentions(&b.term, letter))
                .cloned()
                .collect(),
            over_ranges: self.over_ranges.clone(),
        }
    }
}

/// Whether the letter stands anywhere in the term.
fn mentions(term: &Node, letter: &str) -> bool {
    term.walk()
        .iter()
        .any(|m| m.is_name() && &*m.text == letter)
}

/// What the bounds rule asks of the tool whose terms it reads.
pub trait BoundsAsk {
    /// What the lines in scope bound below.
    fn bounds(&self) -> &SaidBounds;
    /// Whether two terms are the same term as the page writes them.
    fn same(&self, a: &Node, b: &Node) -> bool;
    /// Whether a letter is a natural number, in ℕ or ℕ₀, by its introducing
    /// line.
    fn natural_letter(&self, letter: &str) -> bool;
    /// Of a sum or product, whether its term is at least 0 as the sum reads
    /// it, with what the lines say inside it (`inside_sum`); false of any
    /// other term.
    fn summed_nonnegative(&self, node: &Node) -> bool;
    /// Whether a term is the library's exponential of an argument.
    fn exponential(&self, node: &Node) -> bool;
}

/// What these lines bound below, each read beside the others.
pub fn from_lines<A: BoundsAsk>(ask: &A, lines: &[&Node], out: &mut SaidBounds) {
    for line in lines {
        said_bounds(ask, line, lines, out);
    }
}

/// What a line bounds below: x ≥ 0 of x ≥ 0, x > 0 or 0 < x, p ≥ 1 of
/// 1 < p or p ∈ ℕ, x of x ∈ D for a set D whose members are bounded,
/// what each part of an "and" says, and a term bounded at each k of a
/// range. `lines` are the lines beside it, which may say what D is. A
/// strict order bounds as the other does, x > 0 saying x ≥ 0 of a real
/// x.
pub fn said_bounds<A: BoundsAsk>(
    ask: &A,
    line: &Node,
    lines: &[&Node],
    out: &mut SaidBounds,
) {
    match (line.notation(), line.children.as_slice()) {
        (CONJUNCTION | COMMA_CONJUNCTION, parts) => {
            for part in parts {
                said_bounds(ask, part, lines, out);
            }
        }
        (ORDER, [a, b]) => {
            let s = line.spelling();
            let said = if s == GREATER || s == AT_LEAST {
                lower(ask, b).map(|least| (a, least))
            } else if s == LESS || s == AT_MOST {
                lower(ask, a).map(|least| (b, least))
            } else {
                None
            };
            if let Some((t, least)) = said {
                out.terms.push(Bound {
                    term: t.clone(),
                    least,
                    said_by: Some(line.clone()),
                });
            }
        }
        (MEMBERSHIP, [t, set]) if line.spelling() == IN => {
            if let Some(least) = set_least(ask, set, lines) {
                out.terms.push(Bound {
                    term: t.clone(),
                    least,
                    said_by: Some(line.clone()),
                });
            }
        }
        (FOR_ALL, [_, set, _]) if set.notation() == INTEGER_RANGE => {
            out.over_ranges.push(line.clone());
        }
        _ => {}
    }
}

/// A whole number every member of the set is at least: 1 of ℕ, 0 of
/// ℕ₀, a's of a range or interval from a, y's of {y ∈ X : y > 0}, and of
/// a letter a line beside it says is such a set, D of D = {y ∈ ℝ : y >
/// 0}. None where nothing bounds them.
pub fn set_least<A: BoundsAsk>(ask: &A, set: &Node, lines: &[&Node]) -> Option<i64> {
    match (set.notation(), set.children.as_slice()) {
        (NUMBER_SYSTEMS, _) if set.spelling() == NATURALS => Some(1),
        (NUMBER_SYSTEMS, _) if set.spelling() == NATURALS0 => Some(0),
        (INTEGER_RANGE | CLOSED_INTERVAL | OPEN_INTERVAL, [from, _]) => {
            lower(ask, from)
        }
        (SET_BUILDER, [y, within, condition]) => {
            let mut said = SaidBounds::default();
            said_bounds(ask, condition, &[], &mut said);
            let by_condition = said
                .terms
                .iter()
                .filter(|b| b.term.is_name() && b.term.text == y.text)
                .map(|b| b.least);
            set_least(ask, within, &[])
                .into_iter()
                .chain(by_condition)
                .max()
        }
        (NAME, _) => lines
            .iter()
            .filter_map(|l| defined_as(l, set))
            .filter_map(|value| set_least(ask, value, &[]))
            .max(),
        _ => None,
    }
}

/// The value a line `S = value` gives the letter, where it is that line.
fn defined_as<'n>(line: &'n Node, letter: &Node) -> Option<&'n Node> {
    match (line.notation(), line.children.as_slice()) {
        (EQUALITY, [s, value]) if s.is_name() && s.text == letter.text => Some(value),
        _ => None,
    }
}

/// A whole number the term is at least, where it is a number at least
/// 0, √2 or π, though no whole number but 0 bounds it.
fn lower<A: BoundsAsk>(ask: &A, node: &Node) -> Option<i64> {
    least(ask, node).or_else(|| nonnegative(ask, node).then_some(0))
}

/// The greatest whole number the term is shown to be at least: by a
/// line in scope, or by its form, a whole numeral, a natural number
/// letter at 0, n! at 1, a sum of bounded terms at the sum of their
/// bounds, a − c at a's bound less the numeral c, a product of terms at
/// least 0 at the product, a power of a base at least 1 at 1. None where
/// nothing bounds it.
pub fn least<A: BoundsAsk>(ask: &A, node: &Node) -> Option<i64> {
    let said = ask
        .bounds()
        .terms
        .iter()
        .filter(|b| ask.same(&b.term, node))
        .map(|b| b.least)
        .max();
    said.into_iter().chain(least_by_form(ask, node)).max()
}

/// `least`, by the term's form alone.
fn least_by_form<A: BoundsAsk>(ask: &A, node: &Node) -> Option<i64> {
    match (node.notation(), node.children.as_slice()) {
        (NUMERAL, _) => node.text.parse::<i64>().ok(),
        (NAME, _) => ask.natural_letter(&node.text).then_some(0),
        (FACTORIAL, _) => Some(1),
        (ABSOLUTE_VALUE, _) => Some(0),
        (ADDITIVE, [a, b]) if node.spelling() == PLUS => {
            least(ask, a)?.checked_add(least(ask, b)?)
        }
        (ADDITIVE, [a, c]) if node.spelling() == MINUS && c.notation() == NUMERAL => {
            least(ask, a)?.checked_sub(c.text.parse::<i64>().ok()?)
        }
        (MULTIPLICATIVE, [a, b]) if node.spelling() == TIMES => {
            let (a, b) = (least(ask, a)?, least(ask, b)?);
            (a >= 0 && b >= 0).then(|| a.checked_mul(b)).flatten()
        }
        (JUXTAPOSITION, [a, b]) => {
            let (a, b) = (least(ask, a)?, least(ask, b)?);
            (a >= 0 && b >= 0).then(|| a.checked_mul(b)).flatten()
        }
        (POWER | SUPERSCRIPT, [base, exponent]) => {
            let whole = least(ask, exponent).is_some_and(|e| e >= 0);
            match least(ask, base) {
                Some(b) if b >= 1 && whole => Some(1),
                Some(b) if b >= 0 && whole => Some(0),
                _ => is_even_numeral(exponent).then_some(0),
            }
        }
        _ => (&*node.notation_name() == "cardinality").then_some(0),
    }
}

/// Whether a term is an even whole numeral, the 2 of x².
fn is_even_numeral(node: &Node) -> bool {
    node.notation() == NUMERAL && node.text.parse::<u64>().is_ok_and(|n| n % 2 == 0)
}

/// Whether a term is a sum or a product, over a range or a set.
fn is_big_operator(node: &Node) -> bool {
    matches!(
        node.notation(),
        crate::notations::SUM | crate::notations::PRODUCT
    ) || matches!(&*node.notation_name(), "sum-over" | "product-over")
}

/// What lines bound inside a sum by `index` over the range from `from` to
/// `to`: nothing of another k than the index, and of the index what a line
/// says at each k of that same range, a(k) of `for all k ∈ {1, …, n},
/// a(k) ≥ 0` in Σ(k = 1 to n) a(k). Over a set, not a range, `range` is
/// None and only the first holds.
pub fn inside_sum<A: BoundsAsk>(
    ask: &A,
    index: &Node,
    range: Option<(&Node, &Node)>,
) -> SaidBounds {
    let mut said = ask.bounds().without_letter(&index.text);
    let Some((from, to)) = range else {
        return said;
    };
    for line in &ask.bounds().over_ranges {
        let [k, set, body] = line.children.as_slice() else {
            continue;
        };
        let [a, b] = set.children.as_slice() else {
            continue;
        };
        if k.text == index.text && ask.same(a, from) && ask.same(b, to) {
            said_bounds(ask, body, &[], &mut said);
        }
    }
    said
}

/// What lines bound inside "for all x ∈ S" or "there is x ∈ S": nothing of
/// another x, and of x the least of S, x ≥ 0 of "for all x ∈ ℕ₀", as of a
/// letter the header lets.
pub fn inside_quantifier<A: BoundsAsk>(
    ask: &A,
    letter: &Node,
    set: &Node,
) -> SaidBounds {
    let mut said = ask.bounds().without_letter(&letter.text);
    if let Some(least) = set_least(ask, set, &[]) {
        said.terms.push(Bound {
            term: letter.clone(),
            least,
            said_by: None,
        });
    }
    said
}

/// Whether the term is at least 0: a line in scope says so, or its form
/// does, a numeral, π, e, a natural number letter, |x|, a count, n!,
/// exp(x), or a sum, product, quotient, power or square root of such; a
/// sum or product over a range of a term a line says is at least 0 at
/// each k of it.
pub fn nonnegative<A: BoundsAsk>(ask: &A, node: &Node) -> bool {
    if least(ask, node).is_some_and(|l| l >= 0) {
        return true;
    }
    if is_big_operator(node) {
        return ask.summed_nonnegative(node);
    }
    let all = |parts: &[Node]| parts.iter().all(|p| nonnegative(ask, p));
    match node.notation() {
        NUMERAL | PI | EULER => true,
        ABSOLUTE_VALUE | FACTORIAL => true,
        ADDITIVE => node.spelling() == PLUS && all(&node.children),
        MULTIPLICATIVE | JUXTAPOSITION => all(&node.children),
        POWER | SUPERSCRIPT if node.children.get(1).is_some_and(is_even_numeral) => {
            true
        }
        POWER | SUPERSCRIPT | REAL_POWER | SQUARE_ROOT => {
            node.children.first().is_some_and(|b| nonnegative(ask, b))
        }
        crate::notations::APPLICATION => ask.exponential(node),
        _ => &*node.notation_name() == "cardinality",
    }
}

/// Whether a real power or square root takes its base at at least 0, so
/// that its principal value is real (`resqrtcld`); true of every other
/// term.
pub fn principal_is_real<A: BoundsAsk>(ask: &A, node: &Node) -> bool {
    if !matches!(node.notation(), REAL_POWER | SQUARE_ROOT) {
        return true;
    }
    node.children.first().is_some_and(|b| nonnegative(ask, b))
}
