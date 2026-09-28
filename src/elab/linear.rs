//! Linear arithmetic over an ordered field, as `METHODS.md` specifies it.
//!
//! `inequalities` is the one closure method that needs a decision procedure
//! rather than a table of named laws. Deciding it is done here; emitting the
//! Metamath proof of what was decided is done in [`super::normal`], because
//! the two are different jobs and only the second needs the kernel.
//!
//! Everything rests on reading a term as a linear combination of **atoms**.
//! An atom is a maximal subterm not built from numerals by `+`, `−`, unary
//! minus, `·` by a numeral and `/` by a numeral, and a numeral over anything
//! else is that numeral times the reciprocal, which is the atom. The method
//! never looks inside one and knows nothing about what it means: `|y|` is an
//! atom, and that it is at least `y` reaches a step as a cited line rather
//! than as arithmetic.
//!
//! A fact is a linear expression against zero. The five shapes `METHODS.md`
//! lists reduce to four by moving everything to one side and turning one
//! negation round, since `not (e <_ 0)` is `0 < e`. What is carried here is
//! `=`, `<_`, `<` and `=/=`, and the last is the one that splits: using it
//! means solving twice, once each side of the equation, and both must fail.

use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};
use num_traits::{Signed, Zero};

use super::field::{q, ADD, DIV, MUL, NEG, Q, SUB};
use crate::mm::kernel::{FloatLabels, Term};
use crate::rules::{digit_of, numeral_label};

/// A rational combination of atoms, plus a constant.
#[derive(Clone, Debug, Default)]
pub struct Linear {
    pub weight: IndexMap<Rc<str>, Q>,
    pub constant: Q,
}

impl Linear {
    pub fn constant(value: Q) -> Linear {
        Linear {
            weight: IndexMap::new(),
            constant: value,
        }
    }

    pub fn atom(said: Rc<str>, weight: Q) -> Linear {
        let mut out = Linear::constant(Q::zero());
        out.weight.insert(said, weight);
        out
    }

    pub fn scaled(&self, by: &Q) -> Linear {
        Linear {
            weight: self
                .weight
                .iter()
                .map(|(k, v)| (k.clone(), v * by))
                .collect(),
            constant: &self.constant * by,
        }
    }

    pub fn plus(&self, other: &Linear) -> Linear {
        let mut out = self.weight.clone();
        for (atom, weight) in &other.weight {
            *out.entry(atom.clone()).or_insert_with(Q::zero) += weight;
        }
        Linear {
            weight: out.into_iter().filter(|(_, v)| !v.is_zero()).collect(),
            constant: &self.constant + &other.constant,
        }
    }

    pub fn minus(&self, other: &Linear) -> Linear {
        self.plus(&other.scaled(&q(-1)))
    }

    pub fn atoms(&self) -> BTreeSet<Rc<str>> {
        self.weight
            .iter()
            .filter(|(_, v)| !v.is_zero())
            .map(|(k, _)| k.clone())
            .collect()
    }

    pub fn constant_only(&self) -> bool {
        self.atoms().is_empty()
    }
}

/// The relation a fact stands in to zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum How {
    Eq,
    Le,
    Lt,
    Ne,
}

/// Which of the facts the caller supplied a fact was built from, and in what
/// multiple, in the order they were met.
pub type Weights = IndexMap<usize, Q>;

/// A linear expression standing in a relation to zero: `side how 0`.
///
/// `weights` says which of the facts the caller supplied this one was built
/// from, and in what multiple. A fact straight from the caller is one times
/// itself; one that elimination produced is the combination that produced
/// it. Carrying it is what lets a refutation be turned into a proof rather
/// than only a verdict.
#[derive(Clone, Debug)]
pub struct Fact {
    pub side: Linear,
    pub how: How,
    pub weights: Weights,
}

impl Fact {
    pub fn new(side: Linear, how: How) -> Fact {
        Fact {
            side,
            how,
            weights: Weights::new(),
        }
    }

    /// This scaled by `mine` plus `other` scaled by `theirs`.
    fn combined(&self, other: &Fact, mine: &Q, theirs: &Q) -> Weights {
        let mut out: Weights =
            self.weights.iter().map(|(k, v)| (*k, v * mine)).collect();
        for (k, v) in &other.weights {
            *out.entry(*k).or_insert_with(Q::zero) += v * theirs;
        }
        out.into_iter().filter(|(_, v)| !v.is_zero()).collect()
    }
}

/// The relation a set.mm label states, among the two a fact may carry.
pub fn relation(label: &str) -> Option<How> {
    match label {
        "clt" => Some(How::Lt),
        "cle" => Some(How::Le),
        _ => None,
    }
}

/// The value a term denotes, if it is built only from numerals.
pub fn numeral(term: &Term, labels: &FloatLabels) -> Option<Q> {
    if term.variable().is_some() {
        return None;
    }
    let label = term.label()?;
    if let Some(d) = digit_of(label) {
        return Some(q(d as i64));
    }
    if label == NEG && term.children().len() == 1 {
        return numeral(&term.children()[0], labels).map(|v| -v);
    }
    if label != "co" || term.children().len() != 3 {
        return None;
    }
    let operation = term.children()[2].rpn(labels);
    let left = numeral(&term.children()[0], labels)?;
    let right = numeral(&term.children()[1], labels)?;
    match &*operation {
        ADD => Some(left + right),
        SUB => Some(left - right),
        MUL => Some(left * right),
        DIV if !right.is_zero() => Some(left / right),
        _ => None,
    }
}

/// A term as a linear combination of atoms.
///
/// What is not built from numerals by the operations above is an atom, and
/// is keyed by the term it spells so that two occurrences of one subterm are
/// one atom.
pub fn read(term: &Term, labels: &FloatLabels) -> Linear {
    if let Some(value) = numeral(term, labels) {
        return Linear::constant(value);
    }
    if term.variable().is_none()
        && term.label() == Some(NEG)
        && term.children().len() == 1
    {
        return read(&term.children()[0], labels).scaled(&q(-1));
    }
    if term.variable().is_none()
        && term.label() == Some("co")
        && term.children().len() == 3
    {
        let operation = term.children()[2].rpn(labels);
        let (left, right) = (&term.children()[0], &term.children()[1]);
        match &*operation {
            ADD => return read(left, labels).plus(&read(right, labels)),
            SUB => return read(left, labels).minus(&read(right, labels)),
            MUL => {
                if let Some(by) = numeral(right, labels) {
                    return read(left, labels).scaled(&by);
                }
                if let Some(by) = numeral(left, labels) {
                    return read(right, labels).scaled(&by);
                }
            }
            DIV => {
                let by = numeral(right, labels);
                if let Some(by) = &by {
                    if !by.is_zero() {
                        return read(left, labels).scaled(&(q(1) / by));
                    }
                }
                // A numeral over a term is the numeral times the term's
                // reciprocal, and the reciprocal is the atom (`METHODS.md`).
                if by.is_none() {
                    if let Some(top) = numeral(left, labels) {
                        if !top.is_zero() {
                            let one = numeral_label(1).expect("a digit");
                            let reciprocal =
                                format!("{one} {} {DIV} co", right.rpn(labels));
                            return Linear::atom(Rc::from(reciprocal), top);
                        }
                    }
                }
            }
            _ => {}
        }
    }
    Linear::atom(term.rpn(labels), q(1))
}

/// A claim as a fact about zero, or None if it states no relation.
///
/// The claim is moved to one side, so `a <_ b` becomes `a - b <_ 0`, and a
/// negated relation is turned rather than carried: not (a <_ b) is b < a. A
/// disequality is carried as one fact and split where it is used.
pub fn fact(term: &Term, labels: &FloatLabels) -> Option<Fact> {
    let mut term = term;
    let mut negated = false;
    if term.variable().is_none()
        && term.label() == Some("wn")
        && term.children().len() == 1
    {
        negated = true;
        term = &term.children()[0];
    }
    if term.variable().is_some() {
        return None;
    }
    if term.label() == Some("wceq") && term.children().len() == 2 {
        let side =
            read(&term.children()[0], labels).minus(&read(&term.children()[1], labels));
        return Some(Fact::new(side, if negated { How::Ne } else { How::Eq }));
    }
    if term.label() != Some("wbr") || term.children().len() != 3 {
        return None;
    }
    let how = relation(&term.children()[2].rpn(labels))?;
    let left = read(&term.children()[0], labels);
    let right = read(&term.children()[1], labels);
    if !negated {
        return Some(Fact::new(left.minus(&right), how));
    }
    // not (a < b) is b <_ a, and not (a <_ b) is b < a.
    let turned = if how == How::Lt { How::Le } else { How::Lt };
    Some(Fact::new(right.minus(&left), turned))
}

/// The fact that denies this one, for the refutation to start from.
pub fn opposite(one: &Fact) -> Fact {
    match one.how {
        How::Eq => Fact::new(one.side.clone(), How::Ne),
        How::Ne => Fact::new(one.side.clone(), How::Eq),
        How::Lt => Fact::new(one.side.scaled(&q(-1)), How::Le),
        How::Le => Fact::new(one.side.scaled(&q(-1)), How::Lt),
    }
}

/// The multipliers that make a set of facts contradict.
#[derive(Clone, Debug)]
pub enum Certificate {
    /// Farkas's combination: each given fact and the multiple of it that
    /// goes into the contradiction.
    Farkas(Weights),
    /// A disequality, the one fact with two readings, taken both ways: the
    /// set fails only when both do, and there is no single combination.
    Either {
        at: usize,
        below: Box<Certificate>,
        above: Box<Certificate>,
    },
}

/// Whether these facts have no solution over an ordered field.
pub fn refutes(facts: &[Fact]) -> bool {
    certificate(facts, &vec![None; facts.len()]).is_some()
}

/// How many of the page's lines a combination rests on: the distinct lines
/// among the facts it gives a weight.
fn lines_used(weights: &Weights, line_of: &[Option<usize>]) -> usize {
    weights
        .iter()
        .filter(|(_, w)| !w.is_zero())
        .filter_map(|(i, _)| line_of.get(*i).copied().flatten())
        .collect::<BTreeSet<usize>>()
        .len()
}

/// The multipliers that make these facts contradict, or None.
///
/// Fourier–Motzkin: an equation is two inequalities, then one atom at a time
/// is eliminated by adding every lower bound to every upper bound. What is
/// left is constants, and the set fails when one of them is a constant
/// standing in a relation no number satisfies.
///
/// An inequality may only be multiplied by something positive; an equation
/// by anything, which is why its two halves carry opposite signs. A proof of
/// the step is built from the combination, so it is kept rather than
/// discarded.
///
/// `line_of` says which of the page's lines each fact came from, None for
/// one the method adds, as the claim denied. Every step's cited line must do
/// work (`ELABORATION.md`, R3), so of the combinations that contradict, the
/// one resting on the most lines is taken, and of those the first. Atoms
/// are eliminated in the order the facts first name them, which is the
/// order the page writes them, so which combination is first is the page's.
pub fn certificate(facts: &[Fact], line_of: &[Option<usize>]) -> Option<Certificate> {
    for (i, one) in facts.iter().enumerate() {
        if one.how == How::Ne {
            let mut rest: Vec<Fact> = facts[..i].to_vec();
            rest.extend(facts[i + 1..].iter().cloned());
            let mut lines: Vec<Option<usize>> = line_of[..i].to_vec();
            lines.extend(line_of[i + 1..].iter().copied());
            lines.push(line_of[i]);
            let mut first = rest.clone();
            first.push(Fact::new(one.side.clone(), How::Lt));
            let below = certificate(&first, &lines)?;
            let mut second = rest;
            second.push(Fact::new(one.side.scaled(&q(-1)), How::Lt));
            let above = certificate(&second, &lines)?;
            return Some(Certificate::Either {
                at: i,
                below: Box::new(below),
                above: Box::new(above),
            });
        }
    }
    let mut open: Vec<Fact> = Vec::new();
    for (i, one) in facts.iter().enumerate() {
        let alone = |weight: i64| {
            let mut w = Weights::new();
            w.insert(i, q(weight));
            w
        };
        if one.how == How::Eq {
            open.push(Fact {
                side: one.side.clone(),
                how: How::Le,
                weights: alone(1),
            });
            open.push(Fact {
                side: one.side.scaled(&q(-1)),
                how: How::Le,
                weights: alone(-1),
            });
        } else {
            open.push(Fact {
                side: one.side.clone(),
                how: one.how,
                weights: alone(1),
            });
        }
    }
    let mut atoms: IndexSet<Rc<str>> = IndexSet::new();
    for one in &open {
        for (atom, weight) in &one.side.weight {
            if !weight.is_zero() {
                atoms.insert(atom.clone());
            }
        }
    }
    for atom in &atoms {
        let (mut under, mut over, mut rest) = (Vec::new(), Vec::new(), Vec::new());
        for one in open {
            let weight = one.side.weight.get(atom).cloned().unwrap_or_else(Q::zero);
            if weight.is_positive() {
                over.push(one);
            } else if weight.is_negative() {
                under.push(one);
            } else {
                rest.push(one);
            }
        }
        let mut joined = Vec::new();
        for high in &over {
            for low in &under {
                let a = high.side.weight[atom].clone();
                let b = -low.side.weight[atom].clone();
                let made = high.side.scaled(&b).plus(&low.side.scaled(&a));
                let how = if high.how == How::Lt || low.how == How::Lt {
                    How::Lt
                } else {
                    How::Le
                };
                joined.push(Fact {
                    side: made,
                    how,
                    weights: high.combined(low, &b, &a),
                });
            }
        }
        rest.extend(joined);
        open = rest;
        if open.len() > 400 {
            return None; // past anything the corpus has
        }
    }
    let mut best: Option<(usize, Weights)> = None;
    for one in open {
        if !one.side.constant_only() {
            continue;
        }
        let c = &one.side.constant;
        if (one.how == How::Lt && !c.is_negative())
            || (one.how == How::Le && c.is_positive())
        {
            let used = lines_used(&one.weights, line_of);
            if best.as_ref().is_none_or(|(most, _)| used > *most) {
                best = Some((used, one.weights));
            }
        }
    }
    best.map(|(_, weights)| Certificate::Farkas(weights))
}

/// Whether the claim follows from the given facts.
///
/// The claim is denied and the set shown to have no solution. Denying an
/// equation gives a disequality, which is the one fact that splits, so an
/// equation concluded and a disequality cited cost the same.
pub fn follows(given: &[Fact], claim: &Fact) -> bool {
    let mut all = given.to_vec();
    all.push(opposite(claim));
    refutes(&all)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atom(name: &str) -> Linear {
        Linear::atom(Rc::from(name), q(1))
    }

    #[test]
    fn a_bound_carried_through_a_sum_follows() {
        // x <= 1 and y <= 2 give x + y <= 3.
        let x = atom("vx");
        let y = atom("vy");
        let given = [
            Fact::new(x.minus(&Linear::constant(q(1))), How::Le),
            Fact::new(y.minus(&Linear::constant(q(2))), How::Le),
        ];
        let claim = Fact::new(x.plus(&y).minus(&Linear::constant(q(3))), How::Le);
        assert!(follows(&given, &claim));
        let wrong = Fact::new(x.plus(&y).minus(&Linear::constant(q(2))), How::Le);
        assert!(!follows(&given, &wrong));
    }

    #[test]
    fn an_equation_concluded_splits_into_two_readings() {
        let x = atom("vx");
        let given = [
            Fact::new(x.clone(), How::Le),
            Fact::new(x.scaled(&q(-1)), How::Le),
        ];
        let claim = Fact::new(x, How::Eq);
        let mut all = given.to_vec();
        all.push(opposite(&claim));
        assert!(matches!(
            certificate(&all, &vec![None; all.len()]),
            Some(Certificate::Either { .. })
        ));
    }
}
