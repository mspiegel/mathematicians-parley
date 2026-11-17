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

use indexmap::{IndexMap, IndexSet};

use crate::formula::node::ByShape;
use crate::formula::Node;

/// Why a set is finite: what a backend proves it finite from, a line or how
/// the set is made, in one form for every backend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FiniteBy {
    /// A line says so, `A is finite`: the line's sentence.
    Said(ByShape),
    /// A line gives its count as a number, |Y| = 2 or |Y| = m.
    Counted {
        /// The line's sentence.
        line: ByShape,
        /// Whether the number is at least 1, as `positive` says
        /// (`finite_sets`): such a line vouches for itself and is written in
        /// ℕ, `Y.ncard = 2`; one that may be 0 in ℕ∞, `Y.encard = m`.
        at_least_one: bool,
    },
    /// A part of a finite set, B of `B ⊆ A` or of `B ∈ 𝒫A`: that line's
    /// sentence, and why the whole is finite.
    Part { line: ByShape, whole: Box<FiniteBy> },
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
    /// gH, of a finite H: the image of H under multiplying by g.
    Coset(Box<FiniteBy>),
    /// G(m, n) of a function a define names finite sets with
    /// (`finite_names`).
    Applied(String),
    /// The functions from X to Y, of a finite X and a finite Y.
    Functions(Box<FiniteBy>, Box<FiniteBy>),
    /// X × Y, of a finite X and a finite Y.
    Product(Box<FiniteBy>, Box<FiniteBy>),
}

/// The sets known finite, each by its tree, with why: a define's or a bound
/// letter's name by its name (`name_key`).
pub type FiniteSets = IndexMap<ByShape, FiniteBy>;

/// The key of a set in `FiniteSets`: its tree.
pub fn key(set: &Node) -> ByShape {
    ByShape(set.clone())
}

/// The key of a name, a define's or a bound letter's, in `FiniteSets`: the
/// name as a tree, which is that name wherever the page writes it.
pub fn name_key(name: &str) -> ByShape {
    ByShape(Node::name(crate::formula::Sort::unknown(), name))
}

/// What a theorem makes finite, each set or name by its tree.
#[derive(Clone, Debug, Default)]
pub struct SaidFinite {
    /// The sets its hypotheses make finite, the names its defines give
    /// finite sets, and the letters it binds only over sets of finite sets
    /// (`finite_names`), each with why.
    pub sets: FiniteSets,
    /// For each hypothesis that makes a set finite, the sets only it does
    /// and it may not vouch for itself (`finite_sets_vouched`): it is
    /// written knowing only the rest, since `|X| = 0` written with `X.ncard`
    /// would hold of every infinite X too.
    pub only_by: IndexMap<ByShape, IndexSet<ByShape>>,
}

/// What a theorem's hypotheses, defines and lines make finite. Of its
/// lines only the hypotheses say a set is finite: a step's line holds only
/// from that step on, V ⊆ {a, b} late in a proof, and the conclusion only
/// where the hypotheses do. The other lines are read for the letters they
/// bind (`finite_names`). `positive` says which numbers a count given in a
/// hypothesis is at least 1 as, so that it vouches for itself.
pub fn said_finite(
    hypotheses: &[Node],
    defines: &[Named],
    lines: &[&Node],
    positive: &dyn Fn(&Node) -> bool,
) -> SaidFinite {
    let by_all = finite_sets(hypotheses, positive);
    let mut only_by = IndexMap::new();
    for line in hypotheses {
        let by_others =
            finite_sets(hypotheses.iter().filter(|l| !l.spelt_alike(line)), positive);
        let by_itself = finite_sets_vouched(std::iter::once(line), positive);
        let only: IndexSet<ByShape> = by_all
            .keys()
            .filter(|s| !by_others.contains_key(*s) && !by_itself.contains_key(*s))
            .cloned()
            .collect();
        if !only.is_empty() {
            only_by.insert(key(line), only);
        }
    }
    let mut sets = by_all;
    finite_names(&mut sets, defines, lines);
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
    lines: impl IntoIterator<Item = &'n Node>,
    positive: &dyn Fn(&Node) -> bool,
) -> FiniteSets {
    sets_read(lines, positive, true)
}

/// Of each "if P then Q" the sentences write, anywhere in them, the sets P
/// makes finite within Q, by the whole "if" as a tree (`ByShape`): X of
/// "for all sets X, if |X| = m then |{S ⊆ X : |S| = j}| = C(m, j)", where X
/// has m elements. A count P gives that may be 0 counts too, as a line
/// `assume |X| = m` makes X finite from there on (`finite_sets`). An "if"
/// whose P makes nothing finite is left out.
pub fn finite_under<'n>(
    sentences: impl IntoIterator<Item = &'n Node>,
) -> indexmap::IndexMap<crate::formula::node::ByShape, FiniteSets> {
    use crate::notations::{CONDITIONAL, IMPLICATION};
    let mut out = indexmap::IndexMap::new();
    for sentence in sentences {
        for node in sentence.walk() {
            let ([condition, _], CONDITIONAL | IMPLICATION) =
                (node.children.as_slice(), node.notation())
            else {
                continue;
            };
            let sets = finite_sets([condition], &|_| false);
            if !sets.is_empty() {
                out.insert(crate::formula::node::ByShape(node.clone()), sets);
            }
        }
    }
    out
}

/// `finite_sets` of what the lines may say of themselves: a count given as
/// a number only where `positive` says the number is at least 1, |Y| = 2,
/// which `Y.ncard = 2` holds of no infinite set. A count that may be 0 is
/// written in ℕ∞ in its own line, since `Y.ncard = 0` holds of every
/// infinite set too.
pub fn finite_sets_vouched<'n>(
    lines: impl IntoIterator<Item = &'n Node>,
    positive: &dyn Fn(&Node) -> bool,
) -> FiniteSets {
    sets_read(lines, positive, false)
}

/// `finite_sets`, a count that may be 0 taken where `maybe_zero`.
fn sets_read<'n>(
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
            None => FiniteBy::Said(key(s.line)),
            Some(true) => FiniteBy::Counted {
                line: key(s.line),
                at_least_one: true,
            },
            Some(false) => continue,
        };
        out.entry(key(s.set)).or_insert(why);
    }
    with_parts(&said.subsets, &mut out);
    if maybe_zero {
        for s in said.finite.iter().filter(|s| s.counted == Some(false)) {
            out.entry(key(s.set)).or_insert_with(|| FiniteBy::Counted {
                line: key(s.line),
                at_least_one: false,
            });
        }
        with_parts(&said.subsets, &mut out);
    }
    out
}

/// Adds to `out` each part of a finite set by the lines `subsets`, and each
/// part of those, until no more are.
fn with_parts(subsets: &[Subset<'_>], out: &mut FiniteSets) {
    loop {
        let more: Vec<(ByShape, FiniteBy)> = subsets
            .iter()
            .filter(|s| !out.contains_key(&key(s.part)))
            .filter_map(|s| {
                let whole = finite_by(out, s.whole)?;
                Some((
                    key(s.part),
                    FiniteBy::Part {
                        line: key(s.line),
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
pub fn bound_over(finite: &FiniteSets, set: &Node) -> Option<FiniteBy> {
    match (&*set.notation_name(), set.children.as_slice()) {
        ("powerset", [whole]) => {
            finite_by(finite, whole).map(|w| FiniteBy::MemberOf(Box::new(w)))
        }
        _ => None,
    }
}

/// Why a letter bound over `set` is finite where it is bound: as a part of
/// a finite A where `set` is 𝒫A (`bound_over`), or as the record has it
/// where every place the theorem binds it holds only finite sets, S of S ∈
/// U(k) (`FiniteBy::Bound`, `finite_names`). None otherwise, whatever a set
/// of its name outside is.
pub fn bound_letter(
    finite: &FiniteSets,
    letter: &Node,
    set: &Node,
) -> Option<FiniteBy> {
    bound_over(finite, set).or_else(|| match finite.get(&name_key(&letter.text)) {
        Some(why @ FiniteBy::Bound(_)) => Some(why.clone()),
        _ => None,
    })
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
pub fn is_finite(finite: &FiniteSets, set: &Node) -> bool {
    finite_by(finite, set).is_some()
}

/// Why a set is finite, by what lines say (`finite_sets`) and how it is
/// made: ∅, a listed set {a, b} and a range {a, …, b}; A ∖ B where A is,
/// A ∩ B where either is, A ∪ B where both are; 𝒫A, {x ∈ A : …} and
/// {E(s) : s ∈ A} where A is; the functions from X to Y where both are.
/// None where it is not shown finite.
pub fn finite_by(finite: &FiniteSets, set: &Node) -> Option<FiniteBy> {
    if let Some(why) = finite.get(&key(set)) {
        return Some(why.clone());
    }
    let of = |s: &Node| finite_by(finite, s).map(Box::new);
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
        ("coset", _, [_, h]) => Making::Coset(of(h)?),
        ("functions-from", _, [x, y]) => Making::Functions(of(x)?, of(y)?),
        ("product-set", _, [x, y]) => Making::Product(of(x)?, of(y)?),
        // A function a define names finite sets with, G(m, n) of a G whose
        // body is finite whatever its arguments (`finite_names`).
        (_, _, [f, ..])
            if matches!(
                set.notation(),
                crate::notations::APPLICATION | crate::notations::APPLICATION_TO_TWO
            ) && f.is_name()
                && finite.contains_key(&key(f)) =>
        {
            Making::Applied(f.text.to_string())
        }
        _ => return None,
    };
    Some(FiniteBy::Made(made))
}

/// Whether every member of a set is a finite set: 𝒫A where A is finite,
/// and what is made from such a set by {x ∈ _ : …}, ∖, ∩ and ∪, or named
/// for one (`members`), a function's define among them applied, U(k) of
/// U(k) = {S ⊆ {1, …, k} : …}, whose body holds finite sets whatever k is.
fn holds_finite(finite: &FiniteSets, members: &BTreeSet<String>, set: &Node) -> bool {
    if set.is_name() && members.contains(&*set.text) {
        return true;
    }
    if let (crate::notations::APPLICATION, [f, ..]) =
        (set.notation(), set.children.as_slice())
    {
        if f.is_name() && members.contains(&*f.text) {
            return true;
        }
    }
    let of = |s: &Node| holds_finite(finite, members, s);
    match (
        &*set.notation_name(),
        &*set.spelling().text(),
        set.children.as_slice(),
    ) {
        ("powerset", _, [a]) => is_finite(finite, a),
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

/// Each define whose term is a finite set by `finite`, its name added as
/// one, in the order defined, so that a define made from an earlier one is
/// finite where that one is: F = {S ⊆ X : |S| = j} of a finite X.
pub fn finite_defines(finite: &mut FiniteSets, defines: &[Named]) {
    for d in defines {
        if is_finite(finite, d.value) {
            finite
                .entry(name_key(&d.name))
                .or_insert_with(|| FiniteBy::Define(d.name.clone()));
        }
    }
}

/// What a theorem's defines and bound letters add to the finite sets its
/// hypotheses give: a name for a finite set, F = {S ⊆ X : |S| = j} of a
/// finite X, is one; and a letter bound over sets that hold only finite
/// sets, the S of {S ∈ 𝒫X : |S| = j}, is one where every place the
/// theorem binds it is such a set, so that a property given for it, "|S|
/// = j", counts it as the set-builder does.
pub fn finite_names(finite: &mut FiniteSets, defines: &[Named], lines: &[&Node]) {
    let mut members = BTreeSet::new();
    finite_defines(finite, defines);
    for d in defines {
        if holds_finite(finite, &members, d.value) {
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
            let holds = holds_finite(finite, &members, set);
            let all = bound.entry(x.text.to_string()).or_insert(true);
            *all = *all && holds;
        }
    }
    for (x, _) in bound.into_iter().filter(|(_, all)| *all) {
        finite
            .entry(name_key(&x))
            .or_insert_with(|| FiniteBy::Bound(x));
    }
}
