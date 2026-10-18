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
use crate::citing::{
    index_system, nonzero_said_once, sum_said_once, within, Introduced,
};
use crate::formula::Node;
use crate::matching::{alike, substitute_apart, Binding, Context};
use crate::notations::{
    EQUALITY, INTEGER_RANGE, MEMBERSHIP, MULTIPLICATIVE, NUMBER_SYSTEMS, NUMERAL,
};
use crate::rules::{self, System};

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
    /// The function types the claim rests on, `f : D → E`, which say a
    /// value of f is in E at a point of D: a type is cited for its values
    /// (`READERS.md`).
    pub typed: &'a [Node],
    /// The function types in scope, which a sum's terms may use as well:
    /// what a type says of a sum's term at each index is no value the page
    /// writes, and the build reads it from the scope there (`in_family`).
    pub in_sums: &'a [Node],
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
pub fn holds(term: &Node, system: System, facts: &Facts) -> bool {
    member(term, system, facts, CARRIED)
}

/// Whether the page says `term` is in `system`, which a method's atoms ask
/// of it (`READERS.md`, membership is said once): by the walk, or by a fact
/// stating the membership of what the walk does not take apart. A power to
/// an exponent other than a numeral or a letter in ℕ or ℕ₀, a function's
/// value or a sum is not reached from its parts, as `holds` reaches it; a
/// line says it. The term is read with
/// its identity elements dropped (`SYNTAX.md`, an identity element goes
/// without saying), so 2^(d·1) is the power to the letter d.
pub fn said(term: &Node, system: System, facts: &Facts) -> bool {
    let term = &crate::matching::bare(term, facts.ctx);
    let nonzero = |d: &Node| nonzero(d, facts);
    let stated = |t: &Node, s: System| {
        sum_said_once(t, s, &facts.letters, facts.in_sums, facts.ctx)
            || facts.facts.iter().any(|f| {
                f.notation() == MEMBERSHIP
                    && matches!(f.children.as_slice(), [held, set]
                        if set.notation() == NUMBER_SYSTEMS
                            && same(held, t, facts.ctx)
                            && System::of_sign(&set.text).is_some_and(|k| k.within(s)))
            })
    };
    within(term, system, &facts.letters, &nonzero, &stated)
}

/// Whether an atom of an `algebra` or `inequalities` step is in `system`
/// (`METHODS.md`, membership, Facts in: the test every method's side
/// conditions are asked by): said, or given by a cited equation that puts it
/// beside a term in `system`, as citing a(0) = 0 says a(0) is a number.
pub fn atom_held(term: &Node, system: System, facts: &Facts) -> bool {
    said(term, system, facts)
        || facts.facts.iter().any(|f| {
            f.notation() == EQUALITY
                && f.text == "="
                && matches!(f.children.as_slice(), [a, b]
                    if (same(a, term, facts.ctx) && holds(b, system, facts))
                        || (same(b, term, facts.ctx) && holds(a, system, facts)))
        })
}

/// Whether a bare `from` line reads `term ∈ system` off its facts
/// (`SYNTAX.md`): said, as a method's atoms are, or a function's value at a
/// point of its domain by a type among them. It builds nothing from parts
/// beyond what is said once, which is the `membership` method's to do.
pub fn read_off(term: &Node, system: System, facts: &Facts) -> bool {
    said(term, system, facts) || valued(term, system, facts, 0)
}

fn member(term: &Node, system: System, facts: &Facts, depth: usize) -> bool {
    let nonzero = |d: &Node| nonzero(d, facts);
    let said = |t: &Node, s: System| said_otherwise(t, s, facts, depth);
    within(term, system, &facts.letters, &nonzero, &said)
}

fn same(a: &Node, b: &Node, ctx: &Context) -> bool {
    alike(a, b, ctx, &IndexMap::new(), &IndexMap::new())
}

/// Whether a divisor is not zero: a numeral other than zero or a term the
/// page says once is a positive integer (`nonzero_said_once`), or a fact
/// saying it, as `d ≠ 0` either way round or as a sign, `0 < d` or `d < 0`.
pub fn nonzero(divisor: &Node, facts: &Facts) -> bool {
    if nonzero_said_once(divisor, &facts.letters) {
        return true;
    }
    let by_parts = match (divisor.notation.as_str(), divisor.children.as_slice()) {
        ("multiplicative" | "juxtaposition", [a, b]) => {
            nonzero(a, facts) && nonzero(b, facts)
        }
        ("power" | "superscript", [a, e]) => {
            e.notation() == NUMERAL && nonzero(a, facts)
        }
        _ => false,
    };
    if by_parts {
        return true;
    }
    let zero = |n: &Node| n.notation() == NUMERAL && n.text == "0";
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
            ("power" | "superscript", [a, e]) if e.notation() == NUMERAL => vec![a],
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
fn said_otherwise(term: &Node, system: System, facts: &Facts, depth: usize) -> bool {
    let stated = facts.facts.iter().any(|f| {
        f.notation() == MEMBERSHIP
            && matches!(f.children.as_slice(), [t, set]
                if set.notation() == NUMBER_SYSTEMS
                    && same(t, term, facts.ctx)
                    && System::of_sign(&set.text).is_some_and(|s| s.within(system)))
    });
    if stated {
        return true;
    }
    if depth > 0 {
        let carried = facts.facts.iter().any(|f| {
            f.notation() == EQUALITY
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
fn cased(term: &Node, system: System, facts: &Facts, depth: usize) -> bool {
    let ("by-cases", [value, _, otherwise]) =
        (term.notation.as_str(), term.children.as_slice())
    else {
        return false;
    };
    member(value, system, facts, depth) && member(otherwise, system, facts, depth)
}

/// A power a^e in a system the closure table closes under powers, a in it
/// and e in ℕ₀: 2^j ∈ ℤ where j ∈ ℕ₀. A power to a numeral is the walk's.
fn powered(term: &Node, system: System, facts: &Facts, depth: usize) -> bool {
    let ("power" | "superscript", [base, exponent]) =
        (term.notation.as_str(), term.children.as_slice())
    else {
        return false;
    };
    rules::closed("cexp", system.label()).is_some()
        && member(exponent, System::N0, facts, depth)
        && member(base, system, facts, depth)
}

/// A function's value f(x) in a system holding E, where a type in scope
/// says `f : D → E` and x is in D: by a number system D holds, by a range
/// D x runs over, or by a fact putting x in D.
fn valued(term: &Node, system: System, facts: &Facts, depth: usize) -> bool {
    let ("application", [f, at]) = (term.notation.as_str(), term.children.as_slice())
    else {
        return false;
    };
    facts.typed.iter().any(|t| {
        let [g, domain, codomain] = t.children.as_slice() else {
            return false;
        };
        same(g, f, facts.ctx)
            && codomain.notation() == NUMBER_SYSTEMS
            && System::of_sign(&codomain.text).is_some_and(|s| s.within(system))
            && in_domain(at, domain, facts, depth)
    })
}

/// Whether `x` is in the set `domain` a function is typed over.
fn in_domain(x: &Node, domain: &Node, facts: &Facts, depth: usize) -> bool {
    if domain.notation() == NUMBER_SYSTEMS {
        return System::of_sign(&domain.text)
            .is_some_and(|s| member(x, s, facts, depth));
    }
    let runs_over = x.is_name()
        && facts.ranged.get(&x.text).is_some_and(|r| {
            matches!(domain.children.as_slice(), [a, b]
                if domain.notation() == INTEGER_RANGE
                    && same(a, &r.start, facts.ctx)
                    && same(b, &r.end, facts.ctx))
        });
    runs_over
        || facts.facts.iter().any(|f| {
            f.notation() == MEMBERSHIP
                && matches!(f.children.as_slice(), [y, set]
                    if same(y, x, facts.ctx) && same(set, domain, facts.ctx))
        })
}

/// A term whose operation the closure table says gives a whole number
/// (`rules::WHOLE`), in a system holding ℕ₀, its parts in what the table
/// asks. The operation is read off the term's target, a notation's or a
/// library function's (`Targets::operation`).
fn whole(term: &Node, system: System, facts: &Facts, depth: usize) -> bool {
    let Some(op) = facts.targets.operation(term) else {
        return false;
    };
    let Some(w) = rules::WHOLE.iter().find(|w| w.op == op.label) else {
        return false;
    };
    let ([left, right], Some(left_in), Some(right_in)) = (
        op.parts.as_slice(),
        System::of_label(w.left.1),
        System::of_label(w.right.1),
    ) else {
        return false;
    };
    System::N0.within(system)
        && member(left, left_in, facts, depth)
        && member(right, right_in, facts, depth)
}

/// A sum over a range in ℝ or ℂ, its term in that system at every index:
/// the index is in the system its range lies in (`rules::RANGE_WITHIN`), and
/// a term dividing by something that holds the index is one a fact says at
/// every point of a set holding the range (`SYNTAX.md`).
fn summed(term: &Node, system: System, facts: &Facts, depth: usize) -> bool {
    let ("sum", [index, start, end, body]) =
        (term.notation.as_str(), term.children.as_slice())
    else {
        return false;
    };
    if !matches!(system, System::R | System::C) || !index.is_name() {
        return false;
    }
    let mut letters = facts.letters.clone();
    if let Some(inside) = index_system(start) {
        letters.insert(index.text.clone(), inside);
    }
    if divides_by(body, &index.text, &letters) {
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
    let mut ranged = facts.ranged.clone();
    ranged.insert(
        index.text.clone(),
        Range {
            start: start.clone(),
            end: end.clone(),
        },
    );
    let typed: Vec<Node> = facts.typed.iter().chain(facts.in_sums).cloned().collect();
    let at = Facts {
        facts: facts.facts,
        letters,
        ranged,
        typed: &typed,
        in_sums: facts.in_sums,
        targets: facts.targets,
        ctx: facts.ctx,
    };
    member(body, system, &at, depth)
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
        let numeral_exponent = |e: &Node| e.notation() == NUMERAL;
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
                if b.notation() != NUMERAL {
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

/// Whether `term` divides by something holding the letter `index` that the
/// page does not say once is a positive integer, `letters` holding the
/// index's own system (`citing::nonzero_said_once`).
pub fn divides_by(term: &Node, index: &str, letters: &Introduced) -> bool {
    term.walk().iter().any(|part| {
        part.notation() == MULTIPLICATIVE
            && part.text == "/"
            && part.children.get(1).is_some_and(|d| {
                d.names().contains(index) && !nonzero_said_once(d, letters)
            })
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
pub fn said_pointwise(
    fact: &Node,
    sum: &Summed,
    system: System,
    ctx: &Context,
) -> bool {
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
            System::maybe_within(index_system(sum.start), System::of_sign(&set.text))
        }
        "integer-range" => matches!(set.children.as_slice(), [a, b]
            if same(a, sum.start, ctx) && same(b, sum.end, ctx)),
        _ => false,
    };
    let lands = into.notation() == NUMBER_SYSTEMS
        && System::of_sign(&into.text).is_some_and(|s| s.within(system));
    let at = Binding::from([(sum.index.to_string(), bound.clone())]);
    holds_range && lands && same(&substitute_apart(sum.body, &at, ctx), value, ctx)
}
