//! What supplies an item's hypotheses, and the hypotheses and conclusion checks.

use std::sync::Arc;

use super::*;
use crate::matching::{expand, Meeting};
use crate::notations::FUNCTIONS_FROM;
use crate::{citing, matching};

/// Where a fact a citation needs stands, searched in one order for an
/// item's hypothesis (`Cited::supplied`) and for the side a definition is
/// read from (`Cited::firsts`): a line `refs` names; one of the step's
/// requires lines the citation reads, all of them for the step's own and
/// those above it for a citation on the line `below`
/// (`Step::requires_above`), that writes the fact or else implies it; the
/// `let` line in scope that says it once; the said-once walk.
pub(super) struct Suppliers<'a> {
    pub(super) step: &'a Step,
    pub(super) refs: &'a [String],
    pub(super) item: Option<&'a str>,
    /// The requires lines the citation reads, each as its sentences.
    pub(super) required: Vec<Vec<Node>>,
    pub(super) parts: Rc<Parts>,
    pub(super) known: &'a Known<'a>,
    pub(super) library: &'a Library<'a>,
}

impl<'a> Suppliers<'a> {
    pub(super) fn new(
        step: &'a Step,
        refs: &'a [String],
        item: Option<&'a str>,
        below: Option<usize>,
        known: &'a Known<'a>,
        library: &'a Library<'a>,
    ) -> Suppliers<'a> {
        // The lines read with the defines the citation cites written out:
        // the step's own, or a requires line's (`unfolded_parts`).
        let defined = known.citing_item(refs, item);
        let read = |r: &Requires| -> Vec<Node> {
            r.fact
                .sentences()
                .iter()
                .filter_map(|s| known.read_citing(s, &defined))
                .collect()
        };
        let required: Vec<Vec<Node>> = match below {
            None => step.requires.iter().map(read).collect(),
            Some(line) => step.requires_above(line).map(read).collect(),
        };
        // A citation on a requires line reads that line's parts, the member
        // a claim's "for all" gives among them (`requires_parts`); one on
        // the step, the step's.
        let parts = below
            .and_then(|line| step.requires.iter().find(|r| r.line == line))
            .and_then(|req| requires_parts(step, req, &[], known, library))
            .map(Rc::new)
            .unwrap_or_else(|| known.parts(step, library));
        Suppliers {
            step,
            refs,
            item,
            required,
            parts,
            known,
            library,
        }
    }

    /// How the line `by` names, as it writes `fact`, met `asked`, the
    /// hypothesis at the citation's values (`Known::alike_how`); of a fact a
    /// line implies, how that fact met it, `H ≠ Q` of a triangle met with the
    /// asked `Q ≠ H`; None where no line writes or implies it.
    pub(super) fn meeting(
        &self,
        asked: &Node,
        fact: &Node,
        by: &SuppliedBy,
        narrowed: Option<&Narrowed>,
    ) -> Option<Meeting> {
        let ctx = &self.library.ctx;
        let none = IndexMap::new();
        let written = match by {
            SuppliedBy::Line(at) | SuppliedBy::SaidOnce(at) if at.implied.is_none() => {
                at.written.clone()
            }
            // The fact the line implies by the recorded rule that is alike
            // what is asked.
            SuppliedBy::Line(at) | SuppliedBy::SaidOnce(at) => {
                let rule = at.implied?;
                implied_by(&at.written, self.known.env, &self.known.sorts)
                    .into_iter()
                    .filter(|(_, r)| *r == rule)
                    .map(|(implied, _)| implied)
                    .find(|implied| {
                        alike(&standard(implied, ctx), fact, ctx, &none, &none)
                    })?
            }
            // So of a fact one of the step's requires lines implies.
            SuppliedBy::Requires {
                line,
                implied: Some(rule),
            } => self
                .required
                .get(*line)?
                .iter()
                .flat_map(|s| implied_by(s, self.known.env, &self.known.sorts))
                .filter(|(_, r)| r == rule)
                .map(|(implied, _)| implied)
                .find(|implied| {
                    alike(&standard(implied, ctx), fact, ctx, &none, &none)
                })?,
            SuppliedBy::Requires {
                line,
                implied: None,
            } => self
                .required
                .get(*line)?
                .iter()
                .find(|s| alike(&standard(s, ctx), fact, ctx, &none, &none))?
                .clone(),
            _ => return None,
        };
        // A line narrowed to the set asked is met over that set.
        let written = match (narrowed, written.children.as_slice()) {
            (Some(n), [letter, _, body]) if written.notation() == FOR_ALL => {
                written.with_children(vec![letter.clone(), n.to.clone(), body.clone()])
            }
            _ => written,
        };
        if let Some(met) = self.known.alike_how(asked, &written) {
            return Some(met);
        }
        // A line found through the defines the citation cites, as the
        // search reads the step's lines (`Known::read_citing`), met with
        // them read out.
        let defined = self.known.citing_item(self.refs, self.item);
        let read = expand(&written, &defined);
        let met = self.known.alike_how(asked, &read)?;
        Some(Meeting {
            defines_read: true,
            ..met
        })
    }

    /// Where `fact`, in its standard form, stands: on a line (`said`), else
    /// as what lines give together or what needs no line (`derived`);
    /// `Unstated` where none of those supplies it.
    pub(super) fn by(&self, fact: &Node) -> SuppliedBy {
        self.said(fact)
            .or_else(|| self.derived(fact))
            .unwrap_or(SuppliedBy::Unstated)
    }

    /// What no one line says but the step gives all the same: the membership
    /// its claim's "for all" gives (`Bound`); a membership a function's type
    /// or a subset carries, each of the two on its line (`Through`); an
    /// equation the same on both sides (`Identity`); an "and" whose parts
    /// stand apart (`Parts`). None where it is none of these.
    pub(super) fn derived(&self, fact: &Node) -> Option<SuppliedBy> {
        let (known, library, ctx) = (self.known, self.library, &self.library.ctx);
        let none = IndexMap::new();
        let alike_fact = |n: &Node| alike(n, fact, ctx, &none, &none);
        // A function's membership of the functions from X to Y, which a line
        // says as its type, `g : X → Y` (`supply::typed_into`).
        if let (MEMBERSHIP, [f, set]) = (fact.notation(), fact.children.as_slice()) {
            if let (FUNCTIONS_FROM, [from, to]) =
                (set.notation(), set.children.as_slice())
            {
                let typed = page::made_as(
                    library.env.g,
                    "_ : _ → _",
                    vec![f.clone(), from.clone(), to.clone()],
                );
                if let Some(by) = typed.and_then(|t| self.said(&standard(&t, ctx))) {
                    return Some(by);
                }
            }
        }
        // The claim's own "for all".
        if let Some(bound) = self.claimed(fact) {
            return Some(bound);
        }
        // Two facts of the step that give it together. A subset's member is
        // also sought where it stands though the step's facts leave it out,
        // `k ∈ {1, …, m}` a block's `let` says, for `k ∈ {1, …, n}` through
        // `{1, …, m} ⊆ {1, …, n}`.
        let facts = &self.parts.facts;
        for carrier in facts {
            let sought = subset_member(carrier, fact);
            for member in facts.iter().chain(sought.as_ref()) {
                let pair = [carrier.clone(), member.clone()];
                let carried = function_values(&pair, known.env, &known.sorts)
                    .iter()
                    .any(|v| alike_fact(&standard(v, ctx)))
                    || subset_carries(carrier, member, fact, ctx)
                    || for_all_carries(carrier, member, fact, ctx);
                if !carried {
                    continue;
                }
                // The member said by a line, or by the claim's own "for all".
                let member = self.said(member).or_else(|| self.claimed(member));
                if let (Some(c), Some(m)) = (self.said(carrier), member) {
                    return Some(SuppliedBy::Through {
                        carrier: Box::new(c),
                        member: Box::new(m),
                    });
                }
            }
        }
        // An equation whose two sides meet.
        if ctx.equations.contains(&fact.notation()) {
            if let [lhs, rhs] = fact.children.as_slice() {
                if let Some(met) = known.alike_how(lhs, rhs) {
                    return Some(SuppliedBy::Identity(met));
                }
            }
        }
        // An "and", part by part.
        let parts = conjuncts(fact, library);
        if parts.len() > 1 {
            let placed: Vec<SuppliedBy> = parts.iter().map(|p| self.by(p)).collect();
            if !placed.iter().any(|p| matches!(p, SuppliedBy::Unstated)) {
                return Some(SuppliedBy::Parts(placed));
            }
        }
        None
    }

    /// `Bound` where `fact` is the membership the step's claim, a "for all"
    /// proved in one line, gives its letter (`Known::step_member`); None
    /// otherwise.
    pub(super) fn claimed(&self, fact: &Node) -> Option<SuppliedBy> {
        let ctx = &self.library.ctx;
        let member = self.known.step_member(self.step)?;
        let letter = member.children.first().filter(|l| l.is_name())?;
        alike(
            &standard(&member, ctx),
            fact,
            ctx,
            &IndexMap::new(),
            &IndexMap::new(),
        )
        .then(|| SuppliedBy::Bound {
            letter: letter.text.to_string(),
        })
    }

    /// Where `fact`, in its standard form, stands on a line: one the step
    /// names, a requires line, a `let` line that says it once, or the
    /// said-once walk's reason. None where no line says it.
    pub(super) fn said(&self, fact: &Node) -> Option<SuppliedBy> {
        let (known, library, ctx) = (self.known, self.library, &self.library.ctx);
        let none = IndexMap::new();
        let states = |s: &Node| alike(&standard(s, ctx), fact, ctx, &none, &none);
        // A line that states the fact, or, of a "there is", its body at a
        // witness.
        let line = fact_at(self.step, self.refs, self.item, fact, known, library)
            .or_else(|| {
                witnessed_at(
                    self.step,
                    self.refs,
                    self.item,
                    fact,
                    &self.parts.facts,
                    known,
                    library,
                )
            });
        if let Some(at) = line {
            return Some(SuppliedBy::Line(at));
        }
        // A requires line that writes the fact, or else one that implies
        // it, `[0, 1] ⊆ ℝ` of `[0, 1] ∈ 𝒫ℝ`.
        let written = self
            .required
            .iter()
            .position(|said| said.iter().any(states))
            .map(|line| SuppliedBy::Requires {
                line,
                implied: None,
            });
        let implied = || {
            self.required.iter().enumerate().find_map(|(line, said)| {
                said.iter()
                    .flat_map(|s| implied_by(s, known.env, &known.sorts))
                    .find(|(i, _)| states(i))
                    .map(|(_, rule)| SuppliedBy::Requires {
                        line,
                        implied: Some(rule),
                    })
            })
        };
        if let Some(by) = written.or_else(implied) {
            return Some(by);
        }
        if let Some(line) = said_once_at(self.step, self.item, fact, known, library) {
            return Some(SuppliedBy::SaidOnce(line));
        }
        // A membership the said-once walk gives, for its reason. Of those
        // alike, the one spelt as the fact is: `m + 1 ∈ ℕ₀` itself, not
        // `1·(m + 1) ∈ ℕ₀`, which `alike` reads the same but whose reason is
        // another term's.
        self.parts
            .said_once
            .iter()
            .filter(|s| alike(&s.fact, fact, ctx, &none, &none))
            .min_by_key(|s| !s.fact.spelt_alike(fact))
            .map(|s| SuppliedBy::Walked(s.clone()))
    }
}

/// Whether `carrier`, a "for all x ∈ A, P(x)", and `member`, `t ∈ A`, give
/// `fact`, `P(t)`.
pub(super) fn for_all_carries(
    carrier: &Node,
    member: &Node,
    fact: &Node,
    ctx: &Context,
) -> bool {
    let none = IndexMap::new();
    let same = |a: &Node, b: &Node| alike(a, b, ctx, &none, &none);
    let ([x, domain, body], [t, within]) =
        (carrier.children.as_slice(), member.children.as_slice())
    else {
        return false;
    };
    if carrier.notation() != FOR_ALL
        || member.notation() != MEMBERSHIP
        || !same(domain, within)
    {
        return false;
    }
    let mut at = Binding::new();
    at.insert(Symbol::of(&x.text), t.clone());
    same(&standard(&substitute_apart(body, &at, ctx), ctx), fact)
}

/// Whether `subset`, `A ⊆ B` or `A ∈ 𝒫B` (`library::part_pair`), and
/// `member`, `k ∈ A`, give `fact`, `k ∈ B`.
/// The membership `subset`, `A ⊆ B`, carries to `fact`, `t ∈ B`: `t ∈ A`.
/// None where `subset` is no subset or `fact` no membership.
pub(super) fn subset_member(subset: &Node, fact: &Node) -> Option<Node> {
    let (small, _) = super::super::library::part_pair(subset)?;
    match (fact.notation(), fact.children.as_slice()) {
        (MEMBERSHIP, [point, _]) => {
            Some(fact.with_children(vec![point.clone(), small]))
        }
        _ => None,
    }
}

pub(super) fn subset_carries(
    subset: &Node,
    member: &Node,
    fact: &Node,
    ctx: &Context,
) -> bool {
    let none = IndexMap::new();
    let same = |a: &Node, b: &Node| alike(a, b, ctx, &none, &none);
    let Some((small, big)) = super::super::library::part_pair(subset) else {
        return false;
    };
    match (member.children.as_slice(), fact.children.as_slice()) {
        ([point, within], [value, wider]) => {
            member.notation() == MEMBERSHIP
                && fact.notation() == MEMBERSHIP
                && same(within, &small)
                && same(wider, &big)
                && same(point, value)
        }
        _ => false,
    }
}

/// What `taken` concludes, each sentence counted across the item's groups,
/// `before` being the sentences of the groups ahead of the one it takes.
pub(super) fn across_groups(taken: &Taken, before: usize) -> Vec<Concluded> {
    taken
        .concluded
        .iter()
        .map(|c| Concluded {
            sentence: before + c.sentence,
            ..*c
        })
        .collect()
}

/// What a step citing an item, other than to obtain, makes each of its
/// letters, as the matcher reads the citation (`taken`): the values it
/// writes and what its claim and lines fix. None where the step cites no
/// item, or no group of it concludes the claim.
pub fn bound_there(step: &Step, library: &Library, known: &Known) -> Option<Binding> {
    if step.just.head.is(Method::Obtain) {
        return None;
    }
    step.just.cited_item()?;
    let read = searched(step, Search::Takes, known, library)?;
    let Built(taken) = &*read else {
        return None;
    };
    Some(taken.binding.clone())
}

/// The hypotheses of the item a step cites that nothing it names supplies,
/// or None where they are supplied or the step cites no item.
pub(super) fn unsupplied(
    step: &Step,
    known: &Known,
    library: &Library,
) -> Option<Vec<String>> {
    let item = step.just.cited_item()?;
    // A pointer that resolves to nothing is `check_citations`'s.
    let groups = library.groups(&step.just.item(&item))?;
    let parts = known.parts(step, library);
    let takes = !searched(step, Search::Takes, known, library)?.is_declined();
    let alone = || searched(step, Search::Alone, known, library);
    missing_hypotheses(&groups, &parts, takes, &alone, library)
}

/// The hypotheses of an item that a citation's facts do not supply, as the
/// item writes them; None where every one is supplied, or where a group of
/// the item asks for nothing. A step's citation and a requires line's are
/// asked the same way. `takes` is whether a group covers the claim
/// (`Search::Takes`), and `alone` the group whose conclusions alone do
/// (`Search::Alone`), asked only where it is wanted.
pub(super) fn missing_hypotheses(
    groups: &[Group],
    parts: &Parts,
    takes: bool,
    alone: &dyn Fn() -> Option<Rc<Route<Taken>>>,
    library: &Library,
) -> Option<Vec<String>> {
    // The hypotheses are supplied under the binding the claim fixes as well,
    // where a property is fixed only by what it is said of in the claim:
    // count-step's P(k + 1) is `a(k + 1) = 0` because the claim counts the i
    // with a(i) = 0. A group the citation takes has them supplied.
    if !parts.claims.is_empty() && takes {
        return None;
    }
    // Where the claim is what a group concludes, the hypotheses missing are
    // those of that group nothing supplies under what the claim fixes, and
    // not every hypothesis it has: floor-between's x ∈ ℝ at x := A + N is
    // said once, and only k ∈ ℤ at k := ⌊A⌋ + N is not supplied.
    let alone = (!parts.claims.is_empty()).then(alone).flatten();
    if let Some(Built(alone)) = alone.as_deref() {
        // Each is said at what the claim fixes, in the page's notation, so
        // that `P or Q` with P := 2 = P reads `2 = P or Q` and does not
        // seem to name the proof's own P; and at what the citation writes,
        // which fixes a letter the conclusion does not hold: c := m.
        let mut fixed = parts.seed.clone();
        for (name, value) in &alone.binding {
            fixed.insert(*name, value.clone());
        }
        let group = &groups[alone.group];
        let unmet: Vec<String> = group
            .asked()
            .filter(|tree| !supplied_alone(tree, group, parts, &alone.binding, library))
            .map(|tree| library.env.g.print(&filled(tree, &fixed, &library.ctx)))
            .collect();
        if !unmet.is_empty() {
            return Some(unmet);
        }
    }
    let mut missing = None;
    for group in groups.iter() {
        if group.wants.is_empty() {
            return None;
        }
        let trees: Vec<Node> = group.asked().cloned().collect();
        let variables = group.letters(&trees);
        // Where a binder applies a function or a property to what it binds,
        // that is what decides it, here as in the conclusion.
        let mut sites = Sites::new();
        for t in &trees {
            binding_sites(t, &library.ctx, &[], &mut sites);
        }
        if supply(
            &trees,
            &parts.facts,
            &parts.seed,
            &variables,
            library,
            &sites,
            false,
        )
        .is_some()
        {
            return None;
        }
        // Each under what the citation writes for its letters: `c := m`
        // shows gcd(m, 3), not the item's gcd(c, 3). Those the facts supply
        // one at a time are left out, as 2 ∈ ℤ at d := 2 is, which is said
        // once; where every one is supplied alone and not all together, all
        // are named.
        let print = |tree: &Node| {
            library
                .env
                .g
                .print(&filled(tree, &parts.seed, &library.ctx))
        };
        let unmet: Vec<String> = trees
            .iter()
            .filter(|tree| !supplied_alone(tree, group, parts, &parts.seed, library))
            .map(print)
            .collect();
        missing = Some(if unmet.is_empty() {
            trees.iter().map(print).collect()
        } else {
            unmet
        });
    }
    missing
}

/// The search `how` of the item a step cites, over the step's parts, made
/// once however many checks ask it (`Known::searches`). None where the step
/// cites no item or the item has no groups, which `check_citations`
/// reports.
pub fn searched(
    step: &Step,
    how: Search,
    known: &Known,
    library: &Library,
) -> Option<Rc<Route<Taken>>> {
    let item = step.just.item(&step.just.cited_item()?);
    let groups = library.groups(&item)?;
    let parts = known.parts(step, library);
    let key = (
        Rc::as_ptr(&parts) as usize,
        Arc::as_ptr(&groups) as usize,
        how,
    );
    if let Some(found) = known.searches.borrow().get(&key) {
        return Some(found.clone());
    }
    let made = Rc::new(match how {
        Search::Takes => {
            taken(&groups, &parts.claims, &parts.facts, &parts.seed, library)
        }
        Search::Obtains => obtained(
            &groups,
            &parts.facts,
            &parts.claims,
            &step.just.obtained,
            &parts.seed,
            library,
        ),
        Search::Alone => concluded_alone(&groups, &parts, library),
    });
    known.searches.borrow_mut().insert(key, made.clone());
    Some(made)
}

/// `searched` for what the step's method reads: an obtain obtains, and
/// every other citation takes.
pub(super) fn search_of(step: &Step) -> Search {
    if step.just.head.is(Method::Obtain) {
        Search::Obtains
    } else {
        Search::Takes
    }
}

/// The group whose conclusion the claim is, read from the claim and the
/// values the citation gives, with what that fixes; its hypotheses are not
/// asked. Declined where no conclusion of the item is the claim.
pub(super) fn concluded_alone(
    groups: &[Group],
    parts: &Parts,
    library: &Library,
) -> Route<Taken> {
    let gives_only: Vec<Group> = groups
        .iter()
        .map(|g| Group {
            wants: Vec::new(),
            gives: g.gives.clone(),
            functions: g.functions.clone(),
            identities: g.identities.clone(),
        })
        .collect();
    taken(
        &gives_only,
        &parts.claims,
        &parts.facts,
        &parts.seed,
        library,
    )
}

/// Whether the citation's facts supply one hypothesis on its own, under the
/// binding the claim fixed.
pub(super) fn supplied_alone(
    want: &Node,
    group: &Group,
    parts: &Parts,
    binding: &Binding,
    library: &Library,
) -> bool {
    let trees = [want.clone()];
    let variables = group.letters(&trees);
    let mut sites = Sites::new();
    binding_sites(want, &library.ctx, &[], &mut sites);
    supply(
        &trees,
        &parts.facts,
        binding,
        &variables,
        library,
        &sites,
        false,
    )
    .is_some()
}

/// Every way the step's facts supply the hypotheses of the item it cites, as
/// the facts each way uses; None where that cannot be said, because the step
/// cites nothing that has hypotheses to supply.
///
/// This is `unsupplied` searched to the end rather than to the first way, by
/// both of its routes: the claim taking a group of the item, and a search
/// with nothing fixed. A way is the facts it took, each once, though a fact
/// the binding has pinned may supply two hypotheses.
pub(super) fn ways_supplied(
    step: &Step,
    known: &Known,
    library: &Library,
) -> Option<Vec<Vec<Node>>> {
    let item = step.just.cited_item()?;
    let groups = library.groups(&step.just.item(&item))?;
    let parts = known.parts(step, library);
    let mut out: Vec<Vec<Node>> = Vec::new();
    let took = |path: &[usize]| -> Vec<Node> {
        let distinct: BTreeSet<usize> = path.iter().copied().collect();
        distinct
            .into_iter()
            .map(|i| parts.facts[i].clone())
            .collect()
    };
    // A step whose claim the item concludes is supplied by the ways that
    // conclude it: the item's letters are what matching its conclusion
    // against the claim fixes, and its hypotheses are supplied under that.
    // Its hypotheses searched alone would bind the letters to anything the
    // facts hold, which is not what the step does and, with few pairs
    // written, is a search over every arrangement of the facts. An `obtain`
    // claims the body of what the item concludes, not the conclusion, and
    // is supplied by its hypotheses alone.
    if !parts.claims.is_empty() && !step.just.head.is(Method::Obtain) {
        taken_ways(
            &groups,
            &parts.claims,
            &parts.facts,
            &parts.seed,
            library,
            &mut |path| out.push(took(path)),
        );
        return Some(out);
    }
    for group in groups.iter() {
        if group.wants.is_empty() {
            return None;
        }
        let trees: Vec<Node> = group.asked().cloned().collect();
        let variables = group.letters(&trees);
        let mut sites = Sites::new();
        for t in &trees {
            binding_sites(t, &library.ctx, &[], &mut sites);
        }
        let mut record = |path: &[usize], _: &Binding| out.push(took(path));
        let mut ways = Ways {
            path: Vec::new(),
            found: &mut record,
        };
        let mut used = vec![false; parts.facts.len()];
        let _ = search(
            &trees,
            &parts.facts,
            &mut used,
            &parts.seed,
            &variables,
            library,
            &sites,
            false,
            false,
            Some(&mut ways),
        );
    }
    Some(out)
}

/// The two lists say the same things in the same order, facts being the
/// same when they are spelt the same.
pub(super) fn lists_spelt_alike(one: &[Node], other: &[Node]) -> bool {
    one.len() == other.len() && one.iter().zip(other).all(|(a, b)| a.spelt_alike(b))
}

/// Every fact of `some` is among `all`, as many times as it is in `some`,
/// facts being the same when they are spelt the same.
pub(super) fn within(some: &[Node], all: &[Node]) -> bool {
    let mut left: FxIndexMap<ByShape, usize> = FxIndexMap::default();
    for f in all {
        *left.entry(f.by_shape()).or_default() += 1;
    }
    some.iter().all(|f| match left.get_mut(&f.by_shape()) {
        Some(n) if *n > 0 => {
            *n -= 1;
            true
        }
        _ => false,
    })
}

/// A citation supplies the hypotheses of what it cites.
///
/// They come from the lines named in `from` and from the `requires` lines,
/// each of which states one fact. A cited line supplies every sentence of
/// its claim, because a claim of several sentences is their conjunction.
///
/// The item is read as a pattern and the facts are ground, so a citation
/// that writes no instantiation is checked the same way as one that does.
/// Where an instantiation is written it seeds the binding, which makes it
/// checked rather than taken on trust.
pub fn check_hypotheses(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        if let Some(missing) = unsupplied(step, known, library) {
            let them = if missing.len() == 1 { "it" } else { "them" };
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} cites {}, which asks for {}, and what it cites does not supply {them}",
                    step.number,
                    step.just.cited_item().unwrap_or_default(),
                    missing.join("; ")
                ),
            );
        }
        for asked in map_domains_unsaid(step, known, library) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} reads a map at a value, which asks for {}, and nothing the step names says it; a requires line says it",
                    step.number,
                    known.print(&asked)
                ),
            );
        }
        for asked in map_types_unsaid(step, known, library) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} cites {}, which asks for {}, and nothing the step names says it; a requires line says it",
                    step.number,
                    step.just.cited_item().unwrap_or_default(),
                    known.print(&asked)
                ),
            );
        }
    }
}

/// What a map read at a value asks: that the value is in the map's domain,
/// where the step's claim or a line it cites applies a map, as the rule is
/// the map's value only there (`SYNTAX.md`, a map). A value holding a letter
/// a binder around it binds is said of every member, and asks nothing of
/// one. Each membership asked and not among the step's facts, those the
/// page says once included.
pub(super) fn map_domains_unsaid(
    step: &Step,
    known: &Known,
    library: &Library,
) -> Vec<Node> {
    // A claim said of every member is read at the member, whose letter
    // the step's own: g(x) in "for all x ∈ (a, b), g(x) = f(x)" asks that
    // x be in g's domain, as the step's block would.
    let mut member: Option<Node> = None;
    let mut written: Vec<Node> = known
        .whole_as_written(&step.claim)
        .map(|claim| match claimed_member(&claim, library.env.g) {
            Some((at, body)) => {
                member = Some(standard(&at, &library.ctx));
                body
            }
            None => claim,
        })
        .into_iter()
        .collect();
    let scope = known.scope(step);
    let defined = known.citing_step(step);
    for r in &step.just.refs {
        if let Some(stated) = scope.get(r) {
            written.extend(known.says(stated, &defined).into_iter().map(|s| s.written));
        }
    }
    // A name the step cites a define of is the map it names, g(x) with
    // g := (t ∈ [a, b] ↦ f(t)) a map read at x.
    let mut asked: Vec<Node> = Vec::new();
    for node in &written {
        let node = expand(node, &defined);
        maps_applied(&node, &mut Vec::new(), library, &mut asked);
    }
    if asked.is_empty() {
        return Vec::new();
    }
    let parts = known.parts(step, library);
    let mut seen: FxIndexSet<ByShape> = FxIndexSet::default();
    asked
        .into_iter()
        .map(|a| standard(&a, &library.ctx))
        .filter(|a| !parts.facts.iter().chain(&member).any(|f| known.alike(f, a)))
        .filter(|a| seen.insert(a.by_shape()))
        .collect()
}

/// Each `value ∈ domain` a map applied in `node` asks, where the value holds
/// no letter of `bound`, the letters the binders around it hold.
pub(super) fn maps_applied(
    node: &Node,
    bound: &mut Vec<String>,
    library: &Library,
    out: &mut Vec<Node>,
) {
    for (at, domain) in matching::map_arguments(node) {
        if at.names().iter().all(|n| !bound.iter().any(|b| b == n)) {
            out.push(page::made(library.env.g, IN, vec![at, domain]));
        }
    }
    let held: Vec<String> = library
        .ctx
        .binders
        .get(&node.notation())
        .map(|b| {
            b.held
                .iter()
                .filter_map(|&at| node.children.get(at))
                .filter(|v| v.is_name())
                .map(|v| v.text.to_string())
                .collect()
        })
        .unwrap_or_default();
    let depth = bound.len();
    bound.extend(held);
    for child in &node.children {
        maps_applied(child, bound, library, out);
    }
    bound.truncate(depth);
}

/// The types an item's `let f : X → Y` lines ask of what a citation gives
/// its function letters, where it gives a map: the map is a function on the
/// domain it writes, said once, but what it sends each member to is the
/// step's to say, as `requires (the map sending y ∈ ℝ to y + 1) : ℝ → ℝ:
/// mun:function-into, from 1` does (`SYNTAX.md`, a map). A letter given as
/// a letter has its own type in scope, which the citation reads
/// (`typed_seed`). Each type asked and not among the step's lines.
pub(super) fn map_types_unsaid(
    step: &Step,
    known: &Known,
    library: &Library,
) -> Vec<Node> {
    let Some(item) = step.just.cited_item() else {
        return Vec::new();
    };
    let name = step.just.item(&item);
    let typed = library.function_types(&name);
    if typed.is_empty() {
        return Vec::new();
    }
    let parts = known.parts(step, library);
    let stands = citing::stood_for(&parts, &name, library);
    // A map, or a derivative f′ or f^(n): a function with no type of its
    // own in scope. A rule a binder's letter fills is read otherwise.
    let typeless = |v: &Node| {
        v.notation() == MAP
            || matches!(&*v.notation_name(), "derivative" | "nth-derivative")
    };
    let given_a_map = |t: &Node| {
        t.children
            .first()
            .and_then(|f| stands.get(&f.text))
            .is_some_and(typeless)
    };
    typed
        .iter()
        .filter(|t| given_a_map(t))
        .map(|t| standard(&substitute_apart(t, &stands, &library.ctx), &library.ctx))
        .filter(|asked| !parts.facts.iter().any(|f| known.alike(f, asked)))
        .collect()
}

/// A citation's claim is what the item concludes, under the binding its
/// hypotheses fixed.
pub fn check_conclusion(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        let just = &step.just;
        if !just.head.is_item() {
            continue;
        }
        let head = just.head.to_string();
        let Some(groups) = library.groups(&just.item(&head)) else {
            continue;
        };
        let parts = known.parts(step, library);
        if parts.claims.is_empty() {
            continue;
        }
        // A claim that is what the item concludes, where only a hypothesis
        // is not supplied, is said once, by `check_hypotheses`, which names
        // the hypothesis.
        let found =
            |how| searched(step, how, known, library).is_some_and(|r| !r.is_declined());
        let hypotheses_said =
            || found(Search::Alone) && unsupplied(step, known, library).is_some();
        if !found(Search::Takes) && !hypotheses_said() {
            // A claim that is the conclusion with an identity element dropped
            // from something not said to be a number is told that, and not
            // that it is something else.
            let unsaid = identities_unsaid(
                &groups,
                &parts.claims,
                &parts.facts,
                &parts.seed,
                library,
            );
            // A claim the item concludes from a "there is" whose witness
            // nothing named puts in its set is told which membership.
            let witnesses = || {
                witnesses_unsaid(
                    &groups,
                    &parts.claims,
                    &parts.facts,
                    &parts.seed,
                    library,
                )
            };
            let said = match unsaid.first() {
                Some(left) => format!(
                    "step {} drops an identity element from what {head} concludes, and nothing says {} is a number; a requires line says it",
                    step.number,
                    known.print(left)
                ),
                None => match witnesses().first() {
                    Some(member) => format!(
                        "step {} reads what {head} concludes from a \"there is\", and nothing it names says {}",
                        step.number,
                        known.print(member)
                    ),
                    None => format!(
                        "step {} claims something that {head} does not conclude",
                        step.number
                    ),
                },
            };
            report.say(&thm.path, just.line, said);
        }
    }
}
