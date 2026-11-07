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

/// What a theorem makes finite, as the page prints each set or name.
#[derive(Clone, Debug, Default)]
pub struct SaidFinite {
    /// The sets its hypotheses make finite, the names its defines give
    /// finite sets, and the letters it binds only over sets of finite sets
    /// (`finite_names`).
    pub sets: BTreeSet<String>,
    /// For each hypothesis that makes a set finite, as printed, the sets
    /// only it does. A hypothesis is written knowing only what the others
    /// make finite, since a line cannot vouch for itself: `|X| = 0` written
    /// with `X.ncard` would hold of every infinite X too.
    pub only_by: BTreeMap<String, BTreeSet<String>>,
}

/// What a theorem's hypotheses, defines and lines make finite. Of its
/// lines only the hypotheses say a set is finite: a step's line holds only
/// from that step on, V ⊆ {a, b} late in a proof, and the conclusion only
/// where the hypotheses do. The other lines are read for the letters they
/// bind (`finite_names`).
pub fn said_finite(
    grammar: &Grammar,
    hypotheses: &[Node],
    defines: &[Named],
    lines: &[&Node],
) -> SaidFinite {
    let by_all = finite_sets(grammar, hypotheses);
    let mut only_by = BTreeMap::new();
    for line in hypotheses {
        if finite_sets(grammar, std::iter::once(line)).is_empty() {
            continue;
        }
        let printed = grammar.print(line);
        let others = hypotheses.iter().filter(|l| grammar.print(l) != printed);
        let by_others = finite_sets(grammar, others);
        let only: BTreeSet<String> = by_all.difference(&by_others).cloned().collect();
        only_by.insert(printed, only);
    }
    let mut sets = by_all;
    finite_names(grammar, &mut sets, defines, lines);
    SaidFinite { sets, only_by }
}

/// The sets these lines make finite, as the page prints them: one a line
/// says is, `A is finite`, and one a line puts inside such a set, B of
/// `B ⊆ A` (`is_finite`). A line counts where it is the whole line or one
/// part of an "and"; under an "if" or a "not" it says nothing of the set.
pub fn finite_sets<'n>(
    grammar: &Grammar,
    lines: impl IntoIterator<Item = &'n Node>,
) -> BTreeSet<String> {
    sets_said_finite(grammar, lines, true)
}

/// `finite_sets` of what the lines say in words, `A is finite` and `B ⊆
/// A`, and not of a count given as a number, |Y| = 2: what a step's lines
/// in scope make finite for the Lean writer, which writes a line such as
/// |Y| = 2 in ℕ∞, a line not vouching for itself, so that its set is
/// counted alike in that line and those after it.
pub fn finite_sets_in_words<'n>(
    grammar: &Grammar,
    lines: impl IntoIterator<Item = &'n Node>,
) -> BTreeSet<String> {
    sets_said_finite(grammar, lines, false)
}

/// `finite_sets`, a count given as a number read as making its set finite
/// where `by_counts`.
fn sets_said_finite<'n>(
    grammar: &Grammar,
    lines: impl IntoIterator<Item = &'n Node>,
    by_counts: bool,
) -> BTreeSet<String> {
    let mut said = SaidOfSets {
        by_counts,
        ..SaidOfSets::default()
    };
    for line in lines {
        said.read(line);
    }
    let mut out: BTreeSet<String> =
        said.finite.iter().map(|s| grammar.print(s)).collect();
    // A part of a part of a finite set is finite too: until no more are.
    loop {
        let more: Vec<String> = said
            .subsets
            .iter()
            .filter(|s| is_finite(grammar, &out, s.whole))
            .map(|s| grammar.print(s.part))
            .filter(|p| !out.contains(p))
            .collect();
        if more.is_empty() {
            return out;
        }
        out.extend(more);
    }
}

/// What lines say of sets that makes one finite.
#[derive(Default)]
struct SaidOfSets<'n> {
    /// A of `A is finite`.
    finite: Vec<&'n Node>,
    /// `B ⊆ A`, each.
    subsets: Vec<Subset<'n>>,
    /// Whether |X| = e, a count given as a number, says X is finite.
    by_counts: bool,
}

/// A line `part ⊆ whole`.
struct Subset<'n> {
    part: &'n Node,
    whole: &'n Node,
}

impl<'n> SaidOfSets<'n> {
    fn read(&mut self, node: &'n Node) {
        use crate::notations::{COMMA_CONJUNCTION, CONJUNCTION};
        match (
            &*node.notation_name(),
            node.notation(),
            node.children.as_slice(),
        ) {
            ("finite", _, [set]) => self.finite.push(set),
            ("subset", _, [part, whole]) => self.subsets.push(Subset { part, whole }),
            // |X| = e, a count given as a number, says X is finite.
            (_, crate::notations::EQUALITY, [a, b]) if self.by_counts => {
                for (count, value) in [(a, b), (b, a)] {
                    let counted = &*count.notation_name() == "cardinality";
                    let a_number = !value
                        .walk()
                        .iter()
                        .any(|n| &*n.notation_name() == "cardinality");
                    if let ([set], true, true) =
                        (count.children.as_slice(), counted, a_number)
                    {
                        self.finite.push(set);
                    }
                }
            }
            (_, CONJUNCTION | COMMA_CONJUNCTION, parts) => {
                for p in parts {
                    self.read(p);
                }
            }
            _ => {}
        }
    }
}

/// Whether a set is finite by what lines say (`finite_sets`) and how it
/// is made: ∅, a listed set {a, b} and a range {a, …, b}; A ∖ B where A
/// is, A ∩ B where either is, A ∪ B where both are; 𝒫A, {x ∈ A : …} and
/// {E(s) : s ∈ A} where A is.
pub fn is_finite(grammar: &Grammar, finite: &BTreeSet<String>, set: &Node) -> bool {
    if finite.contains(&grammar.print(set)) {
        return true;
    }
    let of = |s: &Node| is_finite(grammar, finite, s);
    match (
        &*set.notation_name(),
        &*set.spelling().text(),
        set.children.as_slice(),
    ) {
        (
            "empty-set" | "singleton" | "listed-two" | "listed-three" | "listed-four"
            | "integer-range",
            _,
            _,
        ) => true,
        ("set-operations", "∖", [a, _]) => of(a),
        ("set-operations", "∩", [a, b]) => of(a) || of(b),
        ("set-operations", "∪", [a, b]) => of(a) && of(b),
        ("powerset", _, [a]) => of(a),
        ("set-builder", _, [_, a, _]) => of(a),
        ("set-image", _, [_, _, a]) => of(a),
        // A function a define names finite sets with, G(m, n) of a G whose
        // body is finite whatever its arguments (`finite_names`).
        (_, _, [f, ..])
            if matches!(
                set.notation(),
                crate::notations::APPLICATION | crate::notations::APPLICATION_TO_TWO
            ) =>
        {
            f.is_name() && finite.contains(&grammar.print(f))
        }
        _ => false,
    }
}

/// Whether every member of a set is a finite set: 𝒫A where A is finite,
/// and what is made from such a set by {x ∈ _ : …}, ∖, ∩ and ∪, or named
/// for one (`members`).
fn holds_finite(
    grammar: &Grammar,
    finite: &BTreeSet<String>,
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
    finite: &mut BTreeSet<String>,
    defines: &[Named],
    lines: &[&Node],
) {
    let mut members = BTreeSet::new();
    for d in defines {
        if is_finite(grammar, finite, d.value) {
            finite.insert(d.name.clone());
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
    finite.extend(bound.into_iter().filter(|(_, all)| *all).map(|(x, _)| x));
}
