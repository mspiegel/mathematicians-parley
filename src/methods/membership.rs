//! Whether a `membership` step holds (`METHODS.md`, membership): a term is
//! in a number system because its parts are. The term is walked as the
//! page says a membership once (`citing::within`: numerals, letters, and
//! what +, −, ·, unary −, a power to a numeral and / build from them), with
//! a quotient's divisor not zero by a line saying so or by being a numeral.
//! What that walk does not take apart is in a system where a fact says so,
//! where a cited equation puts it beside a term that is, or by the closure
//! table: an operation `rules::WHOLE` names by its target, and a sum over a
//! range by its term at every index.

use indexmap::IndexMap;

use super::terms::Targets;
use crate::citing::{numeral_nonzero, within, Introduced};
use crate::formula::Node;
use crate::matching::{alike, substitute_apart, Binding, Context};
use crate::rules;

/// What a membership is decided from: the facts the step cites and its
/// requires lines above it say, each part of them and what each membership
/// among them implies; the letters the page puts in a number system once;
/// the function types in scope; and the targets that say what operation a
/// term applies.
pub struct Facts<'a> {
    pub facts: &'a [Node],
    pub letters: Introduced,
    /// The letters that run over a range {a, …, b}, a sum's index among
    /// them, with the range they run over.
    pub ranged: IndexMap<String, Range>,
    /// The function types in scope, `f : D → E`, which say a value of f is
    /// in E at a point of D.
    pub typed: &'a [Node],
    /// The notations' and library functions' targets, which say what
    /// operation a term applies (`Targets::operation`).
    pub targets: &'a Targets,
    pub ctx: &'a Context,
}

/// The ends of a range {a, …, b} a letter runs over.
#[derive(Clone)]
pub struct Range {
    pub start: Node,
    pub end: Node,
}

/// How deep a cited equation may carry a term to another, so that two lines
/// saying t = u and u = t end.
const CARRIED: usize = 3;

/// Whether `term` is in `system` by what `facts` give.
pub fn holds(term: &Node, system: &str, facts: &Facts) -> bool {
    member(term, system, facts, CARRIED)
}

fn member(term: &Node, system: &str, facts: &Facts, depth: usize) -> bool {
    let nonzero = |d: &Node| nonzero(d, facts);
    let said = |t: &Node, s: &str| said_otherwise(t, s, facts, depth);
    within(term, system, &facts.letters, &nonzero, &said)
}

fn same(a: &Node, b: &Node, ctx: &Context) -> bool {
    alike(a, b, ctx, &IndexMap::new(), &IndexMap::new())
}

/// Whether a divisor is not zero: a numeral other than zero, or a fact
/// saying it, as `d ≠ 0` either way round or as a sign, `0 < d` or `d < 0`.
pub fn nonzero(divisor: &Node, facts: &Facts) -> bool {
    if numeral_nonzero(divisor) {
        return true;
    }
    let by_parts = match (divisor.notation.as_str(), divisor.children.as_slice()) {
        ("multiplicative" | "juxtaposition", [a, b]) => {
            nonzero(a, facts) && nonzero(b, facts)
        }
        ("power" | "superscript", [a, e]) => {
            e.notation == "numeral" && nonzero(a, facts)
        }
        _ => false,
    };
    if by_parts {
        return true;
    }
    let zero = |n: &Node| n.notation == "numeral" && n.text == "0";
    let is = |n: &Node| same(n, divisor, facts.ctx);
    facts
        .facts
        .iter()
        .any(|f| match (f.notation.as_str(), f.children.as_slice()) {
            ("logical-not", [inner]) => {
                match (inner.notation.as_str(), inner.children.as_slice()) {
                    ("equality", [a, b]) => (is(a) && zero(b)) || (zero(a) && is(b)),
                    _ => false,
                }
            }
            ("order", [a, b]) => match f.text.as_str() {
                "<" => (zero(a) && is(b)) || (is(a) && zero(b)),
                ">" => (is(a) && zero(b)) || (zero(a) && is(b)),
                _ => false,
            },
            _ => false,
        })
}

/// The part of a divisor `nonzero` finds nothing saying is not zero: the
/// divisor itself, or where it is a product, a quotient or a power to a
/// numeral, the first of its parts that is not. None where it is not zero.
pub fn unsaid_part(divisor: &Node, facts: &Facts) -> Option<Node> {
    if nonzero(divisor, facts) {
        return None;
    }
    let parts: Vec<&Node> =
        match (divisor.notation.as_str(), divisor.children.as_slice()) {
            ("multiplicative" | "juxtaposition", [a, b]) => vec![a, b],
            ("power" | "superscript", [a, e]) if e.notation == "numeral" => vec![a],
            _ => Vec::new(),
        };
    parts
        .iter()
        .find_map(|p| unsaid_part(p, facts))
        .or_else(|| Some(divisor.clone()))
}

/// Whether a part the walk does not take apart is in `system`: a fact
/// says so, of a system inside it; a cited equation puts it beside a term
/// that is; or the closure table puts it there, by its operation, as a sum
/// over a range, a power, a function's value or a term by cases.
fn said_otherwise(term: &Node, system: &str, facts: &Facts, depth: usize) -> bool {
    let stated = facts.facts.iter().any(|f| {
        f.notation == "membership"
            && matches!(f.children.as_slice(), [t, set]
                if set.notation == "number-systems"
                    && same(t, term, facts.ctx)
                    && rules::within_path(rules::system_of(&set.text), Some(system)).is_some())
    });
    if stated {
        return true;
    }
    if depth > 0 {
        let carried = facts.facts.iter().any(|f| {
            f.notation == "equality"
                && matches!(f.children.as_slice(), [a, b]
                    if (same(a, term, facts.ctx) && member(b, system, facts, depth - 1))
                        || (same(b, term, facts.ctx) && member(a, system, facts, depth - 1)))
        });
        if carried {
            return true;
        }
    }
    whole(term, system, facts, depth)
        || summed(term, system, facts, depth)
        || powered(term, system, facts, depth)
        || valued(term, system, facts, depth)
        || cased(term, system, facts, depth)
}

/// A term by cases, what a define by cases writes out to, in a system
/// where each of its values is: s(x) ∈ ℕ₀ where s is 0 or 1.
fn cased(term: &Node, system: &str, facts: &Facts, depth: usize) -> bool {
    let ("by-cases", [value, _, otherwise]) =
        (term.notation.as_str(), term.children.as_slice())
    else {
        return false;
    };
    member(value, system, facts, depth) && member(otherwise, system, facts, depth)
}

/// A power a^e in a system the closure table closes under powers, a in it
/// and e in ℕ₀: 2^j ∈ ℤ where j ∈ ℕ₀. A power to a numeral is the walk's.
fn powered(term: &Node, system: &str, facts: &Facts, depth: usize) -> bool {
    let ("power" | "superscript", [base, exponent]) =
        (term.notation.as_str(), term.children.as_slice())
    else {
        return false;
    };
    rules::closed("cexp", system).is_some()
        && member(exponent, "cn0", facts, depth)
        && member(base, system, facts, depth)
}

/// A function's value f(x) in a system holding E, where a type in scope
/// says `f : D → E` and x is in D: by a number system D holds, by a range
/// D x runs over, or by a fact putting x in D.
fn valued(term: &Node, system: &str, facts: &Facts, depth: usize) -> bool {
    let ("application", [f, at]) = (term.notation.as_str(), term.children.as_slice())
    else {
        return false;
    };
    facts.typed.iter().any(|t| {
        let [g, domain, codomain] = t.children.as_slice() else {
            return false;
        };
        same(g, f, facts.ctx)
            && codomain.notation == "number-systems"
            && rules::within_path(rules::system_of(&codomain.text), Some(system))
                .is_some()
            && in_domain(at, domain, facts, depth)
    })
}

/// Whether `x` is in the set `domain` a function is typed over.
fn in_domain(x: &Node, domain: &Node, facts: &Facts, depth: usize) -> bool {
    if domain.notation == "number-systems" {
        return rules::system_of(&domain.text)
            .is_some_and(|s| member(x, s, facts, depth));
    }
    let runs_over = x.is_name()
        && facts.ranged.get(&x.text).is_some_and(|r| {
            matches!(domain.children.as_slice(), [a, b]
                if domain.notation == "integer-range"
                    && same(a, &r.start, facts.ctx)
                    && same(b, &r.end, facts.ctx))
        });
    runs_over
        || facts.facts.iter().any(|f| {
            f.notation == "membership"
                && matches!(f.children.as_slice(), [y, set]
                    if same(y, x, facts.ctx) && same(set, domain, facts.ctx))
        })
}

/// A term whose operation the closure table says gives a whole number
/// (`rules::WHOLE`), in a system holding ℕ₀, its parts in what the table
/// asks. The operation is read off the term's target, a notation's or a
/// library function's (`Targets::operation`).
fn whole(term: &Node, system: &str, facts: &Facts, depth: usize) -> bool {
    let Some(op) = facts.targets.operation(term) else {
        return false;
    };
    let Some(w) = rules::WHOLE.iter().find(|w| w.op == op.label) else {
        return false;
    };
    let [left, right] = op.parts.as_slice() else {
        return false;
    };
    rules::within_path(Some("cn0"), Some(system)).is_some()
        && member(left, w.left.1, facts, depth)
        && member(right, w.right.1, facts, depth)
}

/// A sum over a range in ℝ or ℂ, its term in that system at every index:
/// the index is in the system its range lies in (`rules::RANGE_WITHIN`), and
/// a term dividing by something that holds the index is one a fact says at
/// every point of a set holding the range (`SYNTAX.md`).
fn summed(term: &Node, system: &str, facts: &Facts, depth: usize) -> bool {
    let ("sum", [index, start, end, body]) =
        (term.notation.as_str(), term.children.as_slice())
    else {
        return false;
    };
    if !matches!(system, "cr" | "cc") || !index.is_name() {
        return false;
    }
    let inside = index_system(start);
    if divides_by(body, &index.text) {
        let sum = Summed {
            index: &index.text,
            body,
            start,
            end,
        };
        return facts
            .facts
            .iter()
            .any(|f| said_pointwise(f, &sum, system, facts.ctx));
    }
    let mut letters = facts.letters.clone();
    if let Some(inside) = inside {
        letters.insert(index.text.clone(), inside);
    }
    let mut ranged = facts.ranged.clone();
    ranged.insert(
        index.text.clone(),
        Range {
            start: start.clone(),
            end: end.clone(),
        },
    );
    let at = Facts {
        facts: facts.facts,
        letters,
        ranged,
        typed: facts.typed,
        targets: facts.targets,
        ctx: facts.ctx,
    };
    member(body, system, &at, depth)
}

/// The number system a range from `start` puts its members in: ℕ from 1,
/// ℕ₀ from 0, ℤ from anywhere.
fn index_system(start: &Node) -> Option<&'static str> {
    let begins = (start.notation == "numeral")
        .then(|| {
            start
                .text
                .parse::<u32>()
                .ok()
                .and_then(rules::numeral_label)
        })
        .flatten();
    rules::RANGE_WITHIN
        .iter()
        .find(|(_, first, _)| first.is_none() || *first == begins)
        .map(|(system, _, _)| *system)
}

/// The atoms of a term and the divisors it writes, as `algebra` reads it
/// (`METHODS.md`): it is taken apart where it is built by +, −, ·, unary −,
/// / and a power to a numeral, and every other part, a letter included, is
/// an atom. A numeral is neither.
pub struct Parts {
    pub atoms: Vec<Node>,
    pub divisors: Vec<Node>,
}

impl Parts {
    pub fn of(term: &Node) -> Parts {
        let mut out = Parts {
            atoms: Vec::new(),
            divisors: Vec::new(),
        };
        out.take(term);
        out
    }

    fn take(&mut self, term: &Node) {
        let numeral_exponent = |e: &Node| e.notation == "numeral";
        match (
            term.notation.as_str(),
            term.text.as_str(),
            term.children.as_slice(),
        ) {
            ("numeral", _, _) => {}
            ("additive", _, [a, b]) | ("juxtaposition", _, [a, b]) => {
                self.take(a);
                self.take(b);
            }
            ("multiplicative", "/", [a, b]) => {
                self.take(a);
                self.take(b);
                if b.notation != "numeral" {
                    self.divisors.push(b.clone());
                }
            }
            ("multiplicative", _, [a, b]) => {
                self.take(a);
                self.take(b);
            }
            ("unary-minus", _, [a]) => self.take(a),
            ("power" | "superscript", _, [a, e]) if numeral_exponent(e) => self.take(a),
            _ => self.atoms.push(term.clone()),
        }
    }
}

/// Whether `term` divides by something other than a numeral that holds
/// the letter `index`.
pub fn divides_by(term: &Node, index: &str) -> bool {
    term.walk().iter().any(|part| {
        part.notation == "multiplicative"
            && part.text == "/"
            && part
                .children
                .get(1)
                .is_some_and(|d| d.notation != "numeral" && d.names().contains(index))
    })
}

/// A sum over a range, its parts by name.
pub struct Summed<'n> {
    pub index: &'n str,
    pub body: &'n Node,
    pub start: &'n Node,
    pub end: &'n Node,
}

impl<'n> Summed<'n> {
    /// `term` as a sum over a range, where it is one.
    pub fn of(term: &'n Node) -> Option<Summed<'n>> {
        let ("sum", [index, start, end, body]) =
            (term.notation.as_str(), term.children.as_slice())
        else {
            return None;
        };
        index.is_name().then_some(Summed {
            index: &index.text,
            body,
            start,
            end,
        })
    }
}

/// Whether `fact` says, at every point of a set holding the sum's range,
/// that its term is in a system inside `system`: `for all k ∈ ℕ, 1/k ∈ ℝ`
/// for Σ(k = 1 to n) 1/k.
pub fn said_pointwise(fact: &Node, sum: &Summed, system: &str, ctx: &Context) -> bool {
    let ("for-all", [bound, set, body]) =
        (fact.notation.as_str(), fact.children.as_slice())
    else {
        return false;
    };
    let ("membership", [value, into]) =
        (body.notation.as_str(), body.children.as_slice())
    else {
        return false;
    };
    let holds_range = match set.notation.as_str() {
        "number-systems" => {
            rules::within_path(index_system(sum.start), rules::system_of(&set.text))
                .is_some()
        }
        "integer-range" => matches!(set.children.as_slice(), [a, b]
            if same(a, sum.start, ctx) && same(b, sum.end, ctx)),
        _ => false,
    };
    let lands = into.notation == "number-systems"
        && rules::within_path(rules::system_of(&into.text), Some(system)).is_some();
    let at = Binding::from([(sum.index.to_string(), bound.clone())]);
    holds_range && lands && same(&substitute_apart(sum.body, &at, ctx), value, ctx)
}
