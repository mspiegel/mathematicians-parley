//! Which sets a theorem knows are finite: those its lines say are, and
//! those made from such sets in ways that keep a set finite.
//!
//! The checker records what a theorem's hypotheses, defines and bound
//! letters make finite (`said_finite`, kept as
//! `CheckedTheorem::said_finite`), and a backend asks of a set it writes
//! with `is_finite` over that record. Lean needs the answer where it writes
//! a count, `A.ncard` of a finite A and `A.encard` otherwise, which may be
//! before the step that shows the set finite: |A ∩ B| in a statement
//! whose proof says `A ∩ B is finite` at step 4. Metamath's ♯ is one form
//! of every set, so it proves finiteness from the page's lines alone.

use std::collections::{BTreeMap, BTreeSet};

use crate::formula::{Grammar, Node};

/// Why a set is finite: what a backend proves it finite from, a line's name
/// or how the set is made, in one form for every backend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FiniteBy {
    /// A line says so, `A is finite`: the line, as the page prints it.
    Said(String),
    /// A line gives its count as a number, |Y| = 2 or |Y| = m.
    Counted {
        /// The line, as the page prints it.
        line: String,
        /// Whether the number is at least 1, as `positive` says
        /// (`finite_sets`): such a line vouches for itself and is written in
        /// ℕ, `Y.ncard = 2`; one that may be 0 in ℕ∞, `Y.encard = m`.
        at_least_one: bool,
    },
    /// A part of a finite set, B of `B ⊆ A` or of `B ∈ 𝒫A`: that line, as
    /// the page prints it, and why the whole is finite.
    Part { line: String, whole: Box<FiniteBy> },
    /// The name a define gives a finite set.
    Define(String),
    /// A letter the theorem binds only over sets of finite sets.
    Bound(String),
    /// A letter bound over 𝒫A, a part of A, of a finite A (`bound_over`).
    MemberOf(Box<FiniteBy>),
    /// How the set is made.
    Made(Making),
}

/// How a set is made that keeps it finite (`finite_by`), with why each part
/// it is made from is finite.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Making {
    /// ∅.
    Empty,
    /// A set listed, {a, b}.
    Listed,
    /// A range of integers, {a, …, b}.
    Range,
    /// A ∖ B, of a finite A.
    Minus(Box<FiniteBy>),
    /// A ∩ B, of whichever part is finite, the first where both are.
    Inter(Box<FiniteBy>),
    /// A ∪ B, of both parts.
    Union(Box<FiniteBy>, Box<FiniteBy>),
    /// 𝒫A, of a finite A.
    Powerset(Box<FiniteBy>),
    /// {x ∈ A : …}, of a finite A.
    Builder(Box<FiniteBy>),
    /// {E(s) : s ∈ A}, of a finite A.
    Image(Box<FiniteBy>),
    /// G(m, n) of a function a define names finite sets with
    /// (`finite_names`).
    Applied(String),
}

/// The sets known finite, each as the page prints it, with why.
pub type FiniteSets = BTreeMap<String, FiniteBy>;

/// What a theorem makes finite, as the page prints each set or name.
#[derive(Clone, Debug, Default)]
pub struct SaidFinite {
    /// The sets its hypotheses make finite, the names its defines give
    /// finite sets, and the letters it binds only over sets of finite sets
    /// (`finite_names`), each with why.
    pub sets: FiniteSets,
    /// For each hypothesis that makes a set finite, as printed, the sets
    /// only it does and it may not vouch for itself (`finite_sets_vouched`):
    /// it is written knowing only the rest, since `|X| = 0` written with
    /// `X.ncard` would hold of every infinite X too.
    pub only_by: BTreeMap<String, BTreeSet<String>>,
}

/// What a theorem's hypotheses, defines and lines make finite. Of its
/// lines only the hypotheses say a set is finite: a step's line holds only
/// from that step on, V ⊆ {a, b} late in a proof, and the conclusion only
/// where the hypotheses do. The other lines are read for the letters they
/// bind (`finite_names`). `positive` says which numbers a count given in a
/// hypothesis is at least 1 as, so that it vouches for itself.
pub fn said_finite(
    grammar: &Grammar,
    hypotheses: &[Node],
    defines: &[Named],
    lines: &[&Node],
    positive: &dyn Fn(&Node) -> bool,
) -> SaidFinite {
    let by_all = finite_sets(grammar, hypotheses, positive);
    let mut only_by = BTreeMap::new();
    for line in hypotheses {
        let printed = grammar.print(line);
        let by_others = finite_sets(
            grammar,
            hypotheses.iter().filter(|l| grammar.print(l) != printed),
            positive,
        );
        let by_itself = finite_sets_vouched(grammar, std::iter::once(line), positive);
        let only: BTreeSet<String> = by_all
            .keys()
            .filter(|s| !by_others.contains_key(*s) && !by_itself.contains_key(*s))
            .cloned()
            .collect();
        if !only.is_empty() {
            only_by.insert(printed, only);
        }
    }
    let mut sets = by_all;
    finite_names(grammar, &mut sets, defines, lines);
    SaidFinite { sets, only_by }
}

/// The sets these lines make finite, as the page prints them, each with
/// why: one a line says is, `A is finite`; one whose count a line gives as
/// a whole number, |Y| = 2 or |Y| = m, since `Y.encard = m` says Y has m
/// elements; and one a line puts inside such a set, B of `B ⊆ A`. Each count
/// records whether `positive` says its number is at least 1, which says how
/// its line is written (`FiniteBy::Counted`). A count that may be 0 is taken
/// only for a set nothing else here makes finite, since its line is written
/// in ℕ where something else does. A line counts where it is the whole line
/// or one part of an "and"; under an "if" or a "not" it says nothing of the
/// set.
pub fn finite_sets<'n>(
    grammar: &Grammar,
    lines: impl IntoIterator<Item = &'n Node>,
    positive: &dyn Fn(&Node) -> bool,
) -> FiniteSets {
    sets_read(grammar, lines, positive, true)
}

/// `finite_sets` of what the lines may say of themselves: a count given as
/// a number only where `positive` says the number is at least 1, |Y| = 2,
/// which `Y.ncard = 2` holds of no infinite set. A count that may be 0 is
/// written in ℕ∞ in its own line, since `Y.ncard = 0` holds of every
/// infinite set too.
pub fn finite_sets_vouched<'n>(
    grammar: &Grammar,
    lines: impl IntoIterator<Item = &'n Node>,
    positive: &dyn Fn(&Node) -> bool,
) -> FiniteSets {
    sets_read(grammar, lines, positive, false)
}

/// `finite_sets`, a count that may be 0 taken where `maybe_zero`.
fn sets_read<'n>(
    grammar: &Grammar,
    lines: impl IntoIterator<Item = &'n Node>,
    positive: &dyn Fn(&Node) -> bool,
    maybe_zero: bool,
) -> FiniteSets {
    let mut said = SaidOfSets {
        finite: Vec::new(),
        subsets: Vec::new(),
        positive,
    };
    for line in lines {
        said.read(line, line);
    }
    let mut out = FiniteSets::new();
    for s in &said.finite {
        let why = match s.counted {
            None => FiniteBy::Said(grammar.print(s.line)),
            Some(true) => FiniteBy::Counted {
                line: grammar.print(s.line),
                at_least_one: true,
            },
            Some(false) => continue,
        };
        out.entry(grammar.print(s.set)).or_insert(why);
    }
    with_parts(grammar, &said.subsets, &mut out);
    if maybe_zero {
        for s in said.finite.iter().filter(|s| s.counted == Some(false)) {
            out.entry(grammar.print(s.set))
                .or_insert_with(|| FiniteBy::Counted {
                    line: grammar.print(s.line),
                    at_least_one: false,
                });
        }
        with_parts(grammar, &said.subsets, &mut out);
    }
    out
}

/// Adds to `out` each part of a finite set by the lines `subsets`, and each
/// part of those, until no more are.
fn with_parts(grammar: &Grammar, subsets: &[Subset<'_>], out: &mut FiniteSets) {
    loop {
        let more: Vec<(String, FiniteBy)> = subsets
            .iter()
            .filter(|s| !out.contains_key(&grammar.print(s.part)))
            .filter_map(|s| {
                let whole = finite_by(grammar, out, s.whole)?;
                Some((
                    grammar.print(s.part),
                    FiniteBy::Part {
                        line: grammar.print(s.line),
                        whole: Box::new(whole),
                    },
                ))
            })
            .collect();
        if more.is_empty() {
            return;
        }
        for (set, why) in more {
            out.entry(set).or_insert(why);
        }
    }
}

/// What lines say of sets that makes one finite, each with the line that
/// says it.
struct SaidOfSets<'n, 'p> {
    /// A of `A is finite`, or X of |X| = e.
    finite: Vec<SaidSet<'n>>,
    /// `B ⊆ A`, each.
    subsets: Vec<Subset<'n>>,
    /// Whether the number a count is given as is at least 1.
    positive: &'p dyn Fn(&Node) -> bool,
}

/// A set a line says is finite, or gives the count of as a number.
struct SaidSet<'n> {
    set: &'n Node,
    line: &'n Node,
    /// None where the line says the set is finite; where it gives the
    /// count, whether the number is at least 1.
    counted: Option<bool>,
}

/// A line `part ⊆ whole`.
struct Subset<'n> {
    part: &'n Node,
    whole: &'n Node,
    line: &'n Node,
}

impl<'n> SaidOfSets<'n, '_> {
    /// What `node`, a part of `line`, says.
    fn read(&mut self, line: &'n Node, node: &'n Node) {
        use crate::notations::{COMMA_CONJUNCTION, CONJUNCTION};
        match (
            &*node.notation_name(),
            node.notation(),
            node.children.as_slice(),
        ) {
            ("finite", _, [set]) => self.finite.push(SaidSet {
                set,
                line,
                counted: None,
            }),
            ("subset", _, [part, whole]) => {
                self.subsets.push(Subset { part, whole, line })
            }
            // A member of 𝒫A is a part of A: `let Y ⊆ X` read as Y ∈ 𝒫X.
            (_, crate::notations::MEMBERSHIP, [part, set])
                if &*set.notation_name() == "powerset" =>
            {
                if let [whole] = set.children.as_slice() {
                    self.subsets.push(Subset { part, whole, line });
                }
            }
            // |X| = e, a count given as a number, says X is finite.
            (_, crate::notations::EQUALITY, [a, b]) => {
                for (count, value) in [(a, b), (b, a)] {
                    let counted = &*count.notation_name() == "cardinality";
                    let a_number = !value
                        .walk()
                        .iter()
                        .any(|n| &*n.notation_name() == "cardinality");
                    if let ([set], true, true) =
                        (count.children.as_slice(), counted, a_number)
                    {
                        self.finite.push(SaidSet {
                            set,
                            line,
                            counted: Some((self.positive)(value)),
                        });
                    }
                }
            }
            (_, CONJUNCTION | COMMA_CONJUNCTION, parts) => {
                for p in parts {
                    self.read(line, p);
                }
            }
            _ => {}
        }
    }
}

/// Why a letter bound over `set` is finite, a set of its own whatever a set
/// of its name outside is: where `set` is 𝒫A of a finite A, a part of A.
/// None for any other binder.
pub fn bound_over(
    grammar: &Grammar,
    finite: &FiniteSets,
    set: &Node,
) -> Option<FiniteBy> {
    match (&*set.notation_name(), set.children.as_slice()) {
        ("powerset", [whole]) => {
            finite_by(grammar, finite, whole).map(|w| FiniteBy::MemberOf(Box::new(w)))
        }
        _ => None,
    }
}

/// Whether a relation that counts a set is one ℕ∞ says as the page does:
/// each side made of counts, whole numerals and letters `natural` says the
/// page puts in ℕ or ℕ₀, by + and ·, k ≤ |W| or |X| = |Y| + 1. Such a
/// relation counts in ℕ∞ whatever the theorem knows of the sets, as
/// set.mm's ♯ does. A relation that computes with a count, |A| − |B| = 1 or
/// |S| = j of an integer j, counts a finite set as a natural number: the
/// page has shown the count is one (`card-nat0`) before computing with it.
pub fn said_in_extended(relation: &Node, natural: &dyn Fn(&str) -> bool) -> bool {
    let counted = relation
        .walk()
        .iter()
        .any(|m| &*m.notation_name() == "cardinality");
    counted
        && relation
            .children
            .iter()
            .all(|c| natural_beside_count(c, natural))
}

/// Whether a term is a natural number as ℕ∞ holds one: counts, whole
/// numerals, letters `natural` says the page puts in ℕ or ℕ₀, and their
/// sums and products.
pub fn natural_beside_count(node: &Node, natural: &dyn Fn(&str) -> bool) -> bool {
    if &*node.notation_name() == "cardinality" {
        return true;
    }
    match node.notation() {
        crate::notations::NUMERAL => !node.text.contains('.'),
        crate::notations::NAME => natural(&node.text),
        _ => {
            matches!(&*node.notation_name(), "additive" | "multiplicative")
                && matches!(&*node.spelling().text(), "+" | "·")
                && node
                    .children
                    .iter()
                    .all(|c| natural_beside_count(c, natural))
        }
    }
}

/// Whether a set is finite (`finite_by`).
pub fn is_finite(grammar: &Grammar, finite: &FiniteSets, set: &Node) -> bool {
    finite_by(grammar, finite, set).is_some()
}

/// Why a set is finite, by what lines say (`finite_sets`) and how it is
/// made: ∅, a listed set {a, b} and a range {a, …, b}; A ∖ B where A is,
/// A ∩ B where either is, A ∪ B where both are; 𝒫A, {x ∈ A : …} and
/// {E(s) : s ∈ A} where A is. None where it is not shown finite.
pub fn finite_by(
    grammar: &Grammar,
    finite: &FiniteSets,
    set: &Node,
) -> Option<FiniteBy> {
    if let Some(why) = finite.get(&grammar.print(set)) {
        return Some(why.clone());
    }
    let of = |s: &Node| finite_by(grammar, finite, s).map(Box::new);
    let made = match (
        &*set.notation_name(),
        &*set.spelling().text(),
        set.children.as_slice(),
    ) {
        ("empty-set", _, _) => Making::Empty,
        ("singleton" | "listed-two" | "listed-three" | "listed-four", _, _) => {
            Making::Listed
        }
        ("integer-range", _, _) => Making::Range,
        ("set-operations", "∖", [a, _]) => Making::Minus(of(a)?),
        ("set-operations", "∩", [a, b]) => Making::Inter(of(a).or_else(|| of(b))?),
        ("set-operations", "∪", [a, b]) => Making::Union(of(a)?, of(b)?),
        ("powerset", _, [a]) => Making::Powerset(of(a)?),
        ("set-builder", _, [_, a, _]) => Making::Builder(of(a)?),
        ("set-image", _, [_, _, a]) => Making::Image(of(a)?),
        // A function a define names finite sets with, G(m, n) of a G whose
        // body is finite whatever its arguments (`finite_names`).
        (_, _, [f, ..])
            if matches!(
                set.notation(),
                crate::notations::APPLICATION | crate::notations::APPLICATION_TO_TWO
            ) && f.is_name()
                && finite.contains_key(&grammar.print(f)) =>
        {
            Making::Applied(grammar.print(f))
        }
        _ => return None,
    };
    Some(FiniteBy::Made(made))
}

/// Whether every member of a set is a finite set: 𝒫A where A is finite,
/// and what is made from such a set by {x ∈ _ : …}, ∖, ∩ and ∪, or named
/// for one (`members`).
fn holds_finite(
    grammar: &Grammar,
    finite: &FiniteSets,
    members: &BTreeSet<String>,
    set: &Node,
) -> bool {
    if members.contains(&grammar.print(set)) {
        return true;
    }
    let of = |s: &Node| holds_finite(grammar, finite, members, s);
    match (
        &*set.notation_name(),
        &*set.spelling().text(),
        set.children.as_slice(),
    ) {
        ("powerset", _, [a]) => is_finite(grammar, finite, a),
        ("set-builder", _, [_, a, _]) => of(a),
        ("set-operations", "∖", [a, _]) => of(a),
        ("set-operations", "∩", [a, b]) => of(a) || of(b),
        ("set-operations", "∪", [a, b]) => of(a) && of(b),
        _ => false,
    }
}

/// A define of a proof: the name, and the term it names.
pub struct Named<'n> {
    pub name: String,
    pub value: &'n Node,
}

/// What a theorem's defines and bound letters add to the finite sets its
/// hypotheses give: a name for a finite set, F = {S ⊆ X : |S| = j} of a
/// finite X, is one; and a letter bound over sets that hold only finite
/// sets, the S of {S ∈ 𝒫X : |S| = j}, is one where every place the
/// theorem binds it is such a set, so that a property given for it, "|S|
/// = j", counts it as the set-builder does.
fn finite_names(
    grammar: &Grammar,
    finite: &mut FiniteSets,
    defines: &[Named],
    lines: &[&Node],
) {
    let mut members = BTreeSet::new();
    for d in defines {
        if is_finite(grammar, finite, d.value) {
            finite
                .entry(d.name.clone())
                .or_insert_with(|| FiniteBy::Define(d.name.clone()));
        }
        if holds_finite(grammar, finite, &members, d.value) {
            members.insert(d.name.clone());
        }
    }
    let mut bound: BTreeMap<String, bool> = BTreeMap::new();
    for n in lines.iter().flat_map(|l| l.walk()) {
        let over = match (n.notation(), &*n.notation_name(), n.children.as_slice()) {
            (_, "set-builder", [x, set, _]) => Some((x, set)),
            (_, "set-image", [_, x, set]) => Some((x, set)),
            (
                crate::notations::FOR_ALL | crate::notations::THERE_IS,
                _,
                [x, set, _],
            ) => Some((x, set)),
            _ => None,
        };
        if let Some((x, set)) = over.filter(|(x, _)| x.is_name()) {
            let holds = holds_finite(grammar, finite, &members, set);
            let all = bound.entry(x.text.to_string()).or_insert(true);
            *all = *all && holds;
        }
    }
    for (x, _) in bound.into_iter().filter(|(_, all)| *all) {
        finite
            .entry(x.clone())
            .or_insert_with(|| FiniteBy::Bound(x));
    }
}
