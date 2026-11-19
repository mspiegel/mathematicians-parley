//! The lemma stages' types and the free functions of fitting.

use std::collections::VecDeque;
use std::iter;

use super::*;
use crate::mm::kernel;

/// The token a join is written with in a statement.
pub(super) fn join_token(join: Join) -> &'static str {
    match join {
        Join::Implies => "wi",
        Join::Iff | Join::Turned => "wb",
    }
}

/// The two lemmas that carry a claim about three points in no order from
/// one order of them to another (`held_reordered`). Each is ( the points are
/// numbers -> ( the claim of A, B, C -> the claim of the new order ) ).
/// Where a stage of applying a lemma leaves it: carried on, or the claim
/// reached some other way and nothing left to do.
pub(super) enum Staged<T> {
    /// The next stage is given this.
    Onward(T),
    /// The claim is reached.
    Settled(Route<Proof>),
}

/// What a lemma is used with, for fitting its variables
/// (`Elaborator::fit_variables`).
pub(super) struct VariablesAsked<'l> {
    /// The lemma.
    pub(super) label: &'l str,
    /// The lemma's signature.
    pub(super) sig: &'l Signature,
    /// The claim the lemma reaches.
    pub(super) goal: &'l Term,
    /// The scope the step sits in.
    pub(super) scope: &'l Rpn,
    /// What the step's lines say.
    pub(super) facts: &'l Facts,
    /// The step, where the claim is a step's.
    pub(super) step: Option<&'l Step>,
    /// Whether the lemma may be reached across what it says another way.
    pub(super) crossing: bool,
    /// What a `with` target said the lemma's variables stand for.
    pub(super) seed: Option<&'l Binding>,
    /// The lemma's variables.
    pub(super) variables: &'l Vars,
    /// What each of the lemma's variables stands for so far.
    pub(super) binding: Binding,
}

/// What a lemma's variables stand for once fitted
/// (`Elaborator::fit_variables`).
pub(super) struct Fitted {
    /// What each of the lemma's variables stands for.
    pub(super) binding: Binding,
    /// What the binding gained since the claim was fitted.
    pub(super) fresh: Binding,
}

/// What a lemma is used with, for choosing the scope it is used in
/// (`Elaborator::scope_of`).
pub(super) struct ScopeAsked<'l> {
    /// The lemma.
    pub(super) label: &'l str,
    /// The lemma's signature.
    pub(super) sig: &'l Signature,
    /// The claim the lemma reaches.
    pub(super) goal: &'l Term,
    /// The scope the step sits in.
    pub(super) scope: &'l Rpn,
    /// What the step's lines say.
    pub(super) facts: &'l Facts,
    /// The step, where the claim is a step's.
    pub(super) step: Option<&'l Step>,
    /// Whether the lemma may be reached across what it says another way.
    pub(super) crossing: bool,
    /// What a `with` target said the lemma's variables stand for.
    pub(super) seed: Option<&'l Binding>,
    /// What the lemma states before the claim, outermost first.
    pub(super) antecedents: &'l [Term],
    /// The lemma's variables.
    pub(super) variables: &'l Vars,
    /// What the binding gained since the claim was fitted.
    pub(super) fresh: &'l Binding,
    /// What each of the lemma's variables stands for so far.
    pub(super) binding: Binding,
}

/// The scope a lemma is used in (`Elaborator::scope_of`).
pub(super) struct Scope {
    /// What each of the lemma's variables stands for, the facts of the scope
    /// having filled what the claim left open.
    pub(super) binding: Binding,
    /// The scope.
    pub(super) where_: Rpn,
    /// The frame that scope is the scope of.
    pub(super) frame: usize,
    /// What the proof being built may rest on there.
    pub(super) known: Facts,
}

/// How a lemma's scope is chosen (`Elaborator::scope_of`).
pub(super) enum Scoped {
    /// The lemma is used in this scope.
    In(Scope),
    /// The claim is reached some other way, over another letter.
    Settled(Route<Proof>),
}

/// The antecedents of a lemma, and what is known when they are matched
/// (`Elaborator::fit_open_antecedents`).
pub(super) struct OpenAntecedents<'l> {
    /// What the lemma states before the claim, outermost first.
    pub(super) antecedents: &'l [Term],
    /// What each of the lemma's variables stands for so far.
    pub(super) binding: Binding,
    /// The lemma's variables.
    pub(super) variables: &'l Vars,
    /// What the binding gained since the claim was fitted.
    pub(super) fresh: &'l Binding,
    /// The scope the lemma is used in.
    pub(super) where_: &'l Rpn,
    /// What the proof being built may rest on at that scope.
    pub(super) known: &'l Facts,
}

/// A lemma fitted to a claim, with what its antecedents ask
/// (`Elaborator::apply_lemma`).
pub(super) struct Reached<'l> {
    /// The lemma.
    pub(super) label: &'l str,
    /// The lemma's signature.
    pub(super) sig: &'l Signature,
    /// The claim the lemma reaches.
    pub(super) goal: &'l Term,
    /// What each of the lemma's variables stands for.
    pub(super) binding: Binding,
    /// What the lemma states before the claim, outermost first.
    pub(super) antecedents: Vec<Term>,
    /// How each antecedent is joined to what follows it.
    pub(super) joins: Vec<Join>,
    /// The scope the lemma is used in.
    pub(super) where_: Rpn,
    /// The frame that scope is the scope of.
    pub(super) frame: usize,
    /// What the proof being built may rest on at that scope.
    pub(super) known: Facts,
    /// The scope the step sits in.
    pub(super) scope: &'l Rpn,
    /// The step, where the claim is a step's.
    pub(super) step: Option<&'l Step>,
    /// What the step's lines say.
    pub(super) facts: &'l Facts,
}

pub(super) struct Reorder {
    /// A, C, B from A, B, C.
    pub(super) swap: &'static str,
    /// B, C, A from A, B, C.
    pub(super) rotate: &'static str,
}

/// A claim about three points as a pair of `REORDERS` reads it.
pub(super) struct ThreePoints {
    /// The claim of A, B, C, as the pair's swap lemma takes it.
    pub(super) shape: Term,
    /// The shape's three letters, in the order it names them.
    pub(super) letters: Vec<Symbol>,
    /// The points the claim puts at those letters, in the same order.
    pub(super) points: Vec<Term>,
}

/// The claims about three points that `commutes any order` says are one in any
/// order, by the lemmas that reorder them: a triangle (`forms-a-triangle`)
/// and collinearity (`collinear`).
pub(super) const REORDERS: [Reorder; 2] = [
    Reorder {
        swap: "gtriswap",
        rotate: "gtrirotate",
    },
    Reorder {
        swap: "gcolswap",
        rotate: "gcolrotate",
    },
];

/// A listed set of three or more elements taken apart at its last element
/// (`listing_step`).
pub(super) struct ListingEnd {
    /// What stands before the last element.
    pub(super) rest: ListingRest,
    /// The last element listed.
    pub(super) last: Term,
}

/// What stands before a listing's last element.
pub(super) enum ListingRest {
    /// The first two of a triple, {a, b, c} with c the last.
    Triple(Term, Term),
    /// A listing of three or more, joined with the last element's
    /// singleton: ( {a, b, c} ∪ {d} ) with d the last.
    Union(Term),
}

/// The element of a singleton, {a}; None for any other term.
pub(super) fn singleton_element(term: &Term) -> Option<&Term> {
    match term.label() {
        Some("csn") if term.children().len() == 1 => Some(&term.children()[0]),
        _ => None,
    }
}

/// A listed set of three or more taken apart at its last element: a
/// triple, or a listing joined with a singleton (`listing_step`); None for
/// any other term.
pub(super) fn listing_end(term: &Term) -> Option<ListingEnd> {
    let kids = term.children();
    match term.label() {
        Some("ctp") if kids.len() == 3 => Some(ListingEnd {
            rest: ListingRest::Triple(kids[0].clone(), kids[1].clone()),
            last: kids[2].clone(),
        }),
        Some("cun") if kids.len() == 2 => {
            let last = singleton_element(&kids[1])?;
            listing_end(&kids[0])?;
            Some(ListingEnd {
                rest: ListingRest::Union(kids[0].clone()),
                last: last.clone(),
            })
        }
        _ => None,
    }
}

/// How many constructors a pattern fixes: the nodes that are not variables.
pub(super) fn constructors(pattern: &Term) -> usize {
    if pattern.variable().is_some() {
        return 0;
    }
    1 + pattern.children().iter().map(constructors).sum::<usize>()
}

/// A disequality in the page's spelling: set.mm's `A =/= B` as `-. A = B`.
/// Anything else is itself.
pub(super) fn page_spelling(term: &Term) -> Term {
    if term.label() != Some("wne") {
        return term.clone();
    }
    Term::apply("wn", vec![Term::apply("wceq", term.children().to_vec())])
}

/// The antecedent of `pending` whose letters `binding` fixes the largest
/// share of, taken out of it; the first of those tied. None where none is
/// left.
pub(super) fn most_fixed<'t>(
    pending: &mut Vec<&'t Term>,
    binding: &Binding,
) -> Option<&'t Term> {
    let share = |t: &Term| {
        let names = t.names();
        let fixed = names.iter().filter(|n| binding.contains_key(*n)).count();
        (fixed, names.len().max(1))
    };
    let mut best = 0;
    for i in 1..pending.len() {
        let (a, a_all) = share(pending[i]);
        let (b, b_all) = share(pending[best]);
        if a * b_all > b * a_all {
            best = i;
        }
    }
    (!pending.is_empty()).then(|| pending.remove(best))
}

/// Whether a shape holds the hole numbered `wanted`.
pub(super) fn holds(tree: &Shape, wanted: usize) -> bool {
    match tree {
        Shape::Hole(i) => *i == wanted,
        Shape::Const(_) => false,
        Shape::App(_, _, kids) => kids.iter().any(|k| holds(k, wanted)),
    }
}

/// A shape spelt with its holes filled.
pub(super) fn spell(tree: &Shape, holes: &[Rpn]) -> Rpn {
    match tree {
        Shape::Hole(i) => holes[*i].clone(),
        Shape::Const(c) => t!(c),
        Shape::App(label, wrap, kids) => {
            let parts: Vec<Rpn> = kids.iter().map(|k| spell(k, holes)).collect();
            applied(&parts, label, wrap.as_deref())
        }
    }
}

/// The parts one after another, then the constructor, then the operation it
/// wraps where it wraps one.
pub(super) fn applied(parts: &[Rpn], label: &str, wrap: Option<&str>) -> Rpn {
    let mut out: Vec<Symbol> = Vec::new();
    for part in parts {
        out.extend_from_slice(part.tokens());
    }
    out.push(Symbol::of(label));
    if let Some(w) = wrap {
        out.push(Symbol::of(w));
    }
    Rpn::from(out)
}

/// Whether the tokens of `part` stand together somewhere in `whole`.
pub(super) fn holds_run(whole: &Rpn, part: &Rpn) -> bool {
    part.is_empty()
        || whole
            .tokens()
            .windows(part.len())
            .any(|w| w == part.tokens())
}

/// The same equation with its sides the other way round; None for anything
/// that is not an equation, whose sides are not interchangeable.
pub(super) fn turned_equation(term: &Term) -> Option<Term> {
    if term.label() != Some("wceq") || term.children().len() != 2 {
        return None;
    }
    Some(Term::apply(
        "wceq",
        vec![term.children()[1].clone(), term.children()[0].clone()],
    ))
}

/// Whether `piece` says what a function the binding fixes maps between: `F
/// : A --> B`, F bound.
pub(super) fn function_fixed(piece: &Term, binding: &Binding) -> bool {
    if piece.variable().is_some()
        || !matches!(
            piece.label(),
            Some("wf") | Some("wf1") | Some("wfo") | Some("wf1o")
        )
        || piece.children().len() != 3
    {
        return false;
    }
    piece.children()[2]
        .variable()
        .is_some_and(|v| binding.contains_key(v))
}

/// The things a lemma's antecedent asks, one conjunct at a time.
/// Whether `binding` gives every letter of `slot` a value.
pub(super) fn decides(slot: &Term, binding: &Binding) -> bool {
    slot.names().iter().all(|n| binding.contains_key(&**n))
}

/// Whether a term is a conjunction, of two parts or of three.
pub(super) fn is_conjunction(term: &Term) -> bool {
    matches!(term.label(), Some("wa") | Some("w3a"))
}

pub fn conjuncts_of(slot: &Term) -> Vec<Term> {
    let mut pieces = Vec::new();
    let mut parts = VecDeque::from([slot.clone()]);
    while let Some(part) = parts.pop_front() {
        if matches!(part.label(), Some("wa") | Some("w3a")) {
            for c in part.children().iter().rev() {
                parts.push_front(c.clone());
            }
        } else {
            pieces.push(part);
        }
    }
    pieces
}

/// The classes an antecedent asks about and nothing decides: set.mm leaves
/// such a class free so that a citation may name any class holding the
/// thing, and what it is asking is that the thing be a set.
pub fn sethood(slot: &Term, binding: &Binding) -> Vec<Symbol> {
    let mut out = Vec::new();
    let mut rest = vec![slot.clone()];
    while let Some(node) = rest.pop() {
        if matches!(node.label(), Some("wa") | Some("w3a")) {
            rest.extend(node.children().iter().cloned());
            continue;
        }
        if matches!(node.label(), Some("wral") | Some("wal")) {
            rest.push(node.children()[0].clone());
            continue;
        }
        let Some(at) = node.label().and_then(|l| lookup(rules::HELD_IN, l)) else {
            continue;
        };
        if let Some(name) = node.children()[at].variable_symbol() {
            if !binding.contains_key(&name) {
                out.push(name);
            }
        }
    }
    out
}

/// A pattern whose binders stand for whatever class fills them: a binder is
/// written `cv` over a setvar, and a claim may answer it with a term.
pub fn as_class(node: &Term, marks: &BTreeSet<String>) -> Term {
    if node.variable().is_some() {
        return node.clone();
    }
    if node.label() == Some("cv")
        && node.children()[0]
            .variable()
            .is_some_and(|v| marks.contains(v))
    {
        return node.children()[0].clone();
    }
    node.with_children(node.children().iter().map(|c| as_class(c, marks)).collect())
}

/// Every part of a term, the whole first.
pub(super) fn subterms(term: &Term) -> Vec<Term> {
    let mut out = Vec::new();
    let mut rest = VecDeque::from([term.clone()]);
    while let Some(node) = rest.pop_front() {
        if node.variable().is_none() {
            rest.extend(node.children().iter().cloned());
        }
        out.push(node);
    }
    out
}

/// `fit` where an equation of the pattern may meet one of the term either
/// way round: what the lemma says in other words is the instance fitted,
/// and its caller carries that to the claim by `Matcher::same`, which reads
/// an equation either way round as the page does. A notation's two holes in
/// no order meet the term's either way round too, as `same` exchanges them
/// (`pair_exchanged`): |AO| meets |QA| at O := Q. Every other fit is the
/// kernel's, which a proof takes symbol for symbol.
pub(super) fn fit_either_way(
    pattern: &Term,
    ground: &Term,
    seed: &Binding,
    fitting: &Fitting,
) -> Option<Binding> {
    let first = ToFit {
        pattern: pattern.clone(),
        ground: ground.clone(),
    };
    either_way(vec![first], seed.clone(), fitting)
}

/// What `either_way` fits by: the lemma's variables a fit may bind, and the
/// term with its two holes in no order exchanged, where a notation puts
/// two in no order at its head (`Elaborator::pair_turned`).
pub(super) struct Fitting<'f> {
    pub(super) variables: &'f Vars,
    pub(super) turned: &'f dyn Fn(&Term) -> Option<Term>,
    /// Whether only those two holes meet either way round, and an equation
    /// and a listing are fitted as written: a fit of what a lemma asks to
    /// what a line says as the page writes it (`fit_respelt_in_no_order`).
    pub(super) pairs_only: bool,
}

/// A part of a pattern and the part of the term it is fitted to.
#[derive(Clone)]
pub(super) struct ToFit {
    pub(super) pattern: Term,
    pub(super) ground: Term,
}

/// The parts still to fit, the last fitted now: a variable bound or
/// checked against what it is bound to, an equation tried with its sides
/// as written and then turned, a node whose notation puts two holes in no
/// order tried as written and then with the two exchanged, any other node
/// part by part. A choice that a later part does not fit is undone.
pub(super) fn either_way(
    mut left: Vec<ToFit>,
    mut binding: Binding,
    fitting: &Fitting,
) -> Option<Binding> {
    let Some(ToFit { pattern, ground }) = left.pop() else {
        return Some(binding);
    };
    if let Some(v) = pattern
        .variable()
        .filter(|v| fitting.variables.contains(*v))
    {
        match binding.get(v) {
            Some(seen) if !kernel::same(seen, &ground) => return None,
            Some(_) => {}
            None => {
                binding.insert(Symbol::of(v), ground.clone());
            }
        }
        return either_way(left, binding, fitting);
    }
    if pattern.variable().is_some() || ground.variable().is_some() {
        if pattern.variable() != ground.variable() {
            return None;
        }
        return either_way(left, binding, fitting);
    }
    if pattern.label() != ground.label()
        || pattern.children().len() != ground.children().len()
    {
        return None;
    }
    if !fitting.pairs_only {
        if let (Some(ours), Some(theirs)) = (listed(&pattern), listed(&ground)) {
            return listed_either_way(&left, &ours, &theirs, &binding, fitting);
        }
    }
    let exchanged = (fitting.turned)(&ground);
    for one in iter::once(&ground).chain(exchanged.as_ref()) {
        let more = parts_paired(&left, &pattern, one, false);
        if let Some(done) = either_way(more, binding.clone(), fitting) {
            return Some(done);
        }
    }
    let equation = pattern.label() == Some("wceq") && pattern.children().len() == 2;
    if !equation || fitting.pairs_only {
        return None;
    }
    either_way(
        parts_paired(&left, &pattern, &ground, true),
        binding,
        fitting,
    )
}

/// `left` with the pattern's parts each to be fitted to the term's at the
/// same place, or, where `turn`, to the term's in the reverse order.
pub(super) fn parts_paired(
    left: &[ToFit],
    pattern: &Term,
    ground: &Term,
    turn: bool,
) -> Vec<ToFit> {
    let mut more = left.to_vec();
    let theirs: Vec<Term> = if turn {
        ground.children().iter().rev().cloned().collect()
    } else {
        ground.children().to_vec()
    };
    more.extend(
        pattern
            .children()
            .iter()
            .cloned()
            .zip(theirs)
            .map(|(pattern, ground)| ToFit { pattern, ground })
            .rev(),
    );
    more
}

/// `either_way` at a listed set of the pattern's and one of the term's: the
/// pattern's elements fitted to the term's in any order, since `same`
/// carries a listing to any order of it (`listing_step`). The orders tried
/// are those of the pattern's own listing, which the lemma writes, and
/// each is cut off at the first element that does not fit.
pub(super) fn listed_either_way(
    left: &[ToFit],
    ours: &[Term],
    theirs: &[Term],
    binding: &Binding,
    fitting: &Fitting,
) -> Option<Binding> {
    if ours.len() != theirs.len() {
        return None;
    }
    let Some((first, rest)) = ours.split_first() else {
        return either_way(left.to_vec(), binding.clone(), fitting);
    };
    for (at, ground) in theirs.iter().enumerate() {
        let one = ToFit {
            pattern: first.clone(),
            ground: ground.clone(),
        };
        let Some(fitted) = either_way(vec![one], binding.clone(), fitting) else {
            continue;
        };
        let mut others = theirs.to_vec();
        others.remove(at);
        if let Some(done) = listed_either_way(left, rest, &others, &fitted, fitting) {
            return Some(done);
        }
    }
    None
}

/// The elements of a listed set of two or more, in the order listed: a
/// pair, a triple, or a listing of four or more (`listing_end`); None for
/// any other term.
pub(super) fn listed(term: &Term) -> Option<Vec<Term>> {
    if term.label() == Some("cpr") && term.children().len() == 2 {
        return Some(term.children().to_vec());
    }
    let ListingEnd { rest, last } = listing_end(term)?;
    let mut elements = match rest {
        ListingRest::Triple(first, second) => vec![first, second],
        ListingRest::Union(before) => listed(&before)?,
    };
    elements.push(last);
    Some(elements)
}

/// The lemma carrying a class's equality up through one place of a term.
/// `term` with each class or formula inside it that binds `letter` moved to
/// bind `spare`, its own occurrences with it; the term's own binder, where
/// it binds `letter`, is left as it is (`renamed_past_inner`).
pub(super) fn inner_moved(term: &Term, letter: &str, spare: &Term) -> Term {
    fn moved(term: &Term, letter: &str, spare: &Term) -> Term {
        if term.variable().is_some() {
            return term.clone();
        }
        let binds_it = term.label() != Some("cv")
            && term.children().iter().any(|c| c.variable() == Some(letter));
        if binds_it {
            let mut put = Binding::new();
            put.insert(Symbol::of(letter), spare.clone());
            return term.substitute(&put);
        }
        term.with_children(
            term.children()
                .iter()
                .map(|c| moved(c, letter, spare))
                .collect(),
        )
    }
    if term.variable().is_some() {
        return term.clone();
    }
    term.with_children(
        term.children()
            .iter()
            .map(|c| {
                if c.variable() == Some(letter) {
                    c.clone()
                } else {
                    moved(c, letter, spare)
                }
            })
            .collect(),
    )
}

pub(super) fn class_lift(label: &str, place: usize) -> Option<&'static str> {
    rules::CLASS_LIFT
        .iter()
        .find(|(l, p, _)| *l == label && *p == place)
        .map(|(_, _, lemma)| *lemma)
}
