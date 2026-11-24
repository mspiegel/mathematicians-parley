//! What a step cites: requires, facings, meetings and restatements.

use std::ptr;

use super::*;
use crate::checker::record::{BodyPart, ChainTerms, MetTrees};
use crate::matching::{Definitions, Meeting};
use crate::methods::membership;
use crate::{citing, matching};

/// A requires line whose cited item does not give its fact.
pub(super) struct Unconcluded {
    /// The requires line.
    pub(super) line: usize,
    /// The item it cites, as it names it.
    pub(super) item: String,
    /// The item's hypotheses the line's facts do not supply, where that is
    /// why; None where they are supplied and the item concludes something
    /// else.
    pub(super) missing: Option<Vec<String>>,
}

/// The requires lines of a step whose item does not conclude them.
pub(super) fn unconcluded(
    step: &Step,
    known: &Known,
    library: &Library,
) -> Vec<Unconcluded> {
    let mut out = Vec::new();
    for req in &step.requires {
        let Some((named, _)) = req.cited_item() else {
            continue;
        };
        let Some(groups) = library.groups(&step.just.item(&named)) else {
            continue;
        };
        let Some(parts) =
            requires_parts(step, req, &[], known, library, Spelt::Written)
        else {
            continue;
        };
        // One use of the item, as a step's citation is read: a line that
        // needs the item applied again writes each use as its own line.
        let cite = parts.cite(library);
        if concludes(&groups, &parts.claims, &parts.facts, &parts.seed, &cite) {
            continue;
        }
        let alone = || Some(Rc::new(concluded_alone(&groups, &parts, library)));
        out.push(Unconcluded {
            line: req.line,
            item: named,
            missing: missing_hypotheses(&groups, &parts, false, &alone, library),
        });
    }
    out
}

/// The member a requires line said of every member, "for all n ∈ ℕ, P", is
/// read at, `n ∈ ℕ`, where the item it cites says no "for all" of its own
/// (`citing::at_a_member`), read with the defines the line cites written
/// out; None for any other requires line.
pub(super) fn requires_member(
    step: &Step,
    req: &Requires,
    known: &Known,
    library: &Library,
) -> Option<Node> {
    let item = req.cited_item().map(|(named, _)| step.just.item(&named));
    let at_member = item
        .as_deref()
        .and_then(|name| library.item(name))
        .is_some_and(|i| !i.says_for_all());
    if !at_member {
        return None;
    }
    let defined = known.citing_item(req.lines(), item.as_deref());
    let claims: Vec<Node> = req
        .fact
        .sentences()
        .iter()
        .filter_map(|s| known.read_citing(s, &defined))
        .collect();
    let [claim] = claims.as_slice() else {
        return None;
    };
    claimed_member(claim, library.env.g).map(|(member, _)| member)
}

/// What a requires line's citation supplies and claims: the line's fact is
/// its claim, and its facts are the lines its reason names, the requires
/// lines above it, and the member a claim said of every member names, each
/// read with the defines the line cites as `spelt` says, all but those
/// `without` names. None where the fact does not read, which
/// `check_formulas` reports.
pub(super) fn requires_parts(
    step: &Step,
    req: &Requires,
    without: &[&str],
    known: &Known,
    library: &Library,
    spelt: Spelt,
) -> Option<Parts> {
    let scope = known.scope(step);
    let mut refs = req.lines().to_vec();
    refs.retain(|r| !without.contains(&r.as_str()));
    // A define is one formula with its name where the line cites it
    // (`Known::citing`).
    let item = req.cited_item().map(|(named, _)| step.just.item(&named));
    let cited = known.citing_item(&refs, item.as_deref());
    let defined = match spelt {
        Spelt::Written => Rc::new(Definitions::new()),
        Spelt::ReadOut => cited.clone(),
    };
    let read_all = |written: &Written| -> Vec<Node> {
        written
            .sentences()
            .iter()
            .filter_map(|s| known.read_citing(s, &defined))
            .collect()
    };
    let mut claims = read_all(&req.fact);
    if claims.is_empty() {
        return None;
    }
    let mut read: Vec<Node> = Vec::new();
    // A requires line said of every member, "for all n ∈ ℕ, P", is read at
    // the member as a step is, where the item it cites says no "for all"
    // (`citing::at_a_member`): the membership is a fact, P the claim.
    let at_member = item
        .as_deref()
        .and_then(|name| library.item(name))
        .is_some_and(|i| !i.says_for_all());
    if at_member {
        if let [claim] = claims.as_slice() {
            if let Some((member, body)) = claimed_member(claim, library.env.g) {
                read.push(member);
                claims = vec![body];
            }
        }
    }
    for r in &refs {
        if let Some(written) = scope.get(r) {
            read.extend(known.supplied(written, &defined));
        }
    }
    // A requires line may not cite another, but the facts the lines above
    // it state are established for the same step and are what a dull fact
    // its own citation asks for is written as.
    for o in step.requires_above(req.line) {
        read.extend(read_all(&o.fact));
    }
    // A step said of every member in one line: its requires lines speak
    // of the member, whose membership the claim gives (`SYNTAX.md`), and
    // which it introduces as the step's citation has it introduced
    // (`library::citation_parts`): x of "for all x ∈ [0, 1]" is in ℝ.
    let mut in_scope = introduced(known, step);
    if step.openers.is_empty() {
        if let [claim] = read_all(&step.claim).as_slice() {
            if let Some((member, _)) = claimed_member(claim, library.env.g) {
                if let Some((letter, system)) = citing::introduction(&member, &in_scope)
                {
                    in_scope.insert(letter, system);
                }
                read.push(member);
            }
        }
    }
    let letters = req
        .cited_item()
        .and_then(|(named, _)| library.item_sorts(&step.just.item(&named)));
    let mut seed = known.seed(req.values(), &defined, letters);
    if let Some((named, _)) = req.cited_item() {
        listed_seed(
            &mut seed,
            &step.just.item(&named),
            req.line,
            known,
            library,
            &defined,
        );
    }
    // The facts a step's own citation is given, so that an item cited
    // on a requires line reaches what it reaches cited by a step, the
    // memberships the page says once among them.
    let mut parts = finished(read, claims, seed, library, &known.sorts);
    if spelt == Spelt::Written {
        parts.unfolds = Some(Rc::new(matching::Unfolds {
            defines: (*cited).clone(),
        }));
    }
    let typed = super::super::library::typed_in_scope(known, step);
    said_once(
        &mut parts,
        &in_scope,
        &super::super::library::points_introduced(known, step),
        &typed,
        library,
        &known.sorts,
    );
    if let Some((named, _)) = req.cited_item() {
        typed_seed(&mut parts, &step.just.item(&named), step, known, library);
    }
    Some(parts)
}

/// What the item an obtain cites says there is, at the step: the item's
/// statements, each letter as the step's lines fix it (`obtained`). None
/// where the step obtains from no item, or from a definition that unfolds,
/// which gives the existence the step claims, reached from the claim and
/// never asked of the item; declined where no group of the item gives a
/// "there is" from what the step names.
pub fn obtained_there(
    step: &Step,
    library: &Library,
    known: &Known,
) -> Option<Route<Vec<Node>>> {
    if !step.just.head.is(Method::Obtain) {
        return None;
    }
    let name = step.just.item(&step.just.cited_item()?);
    if library.item(&name)?.unfolds() {
        return None;
    }
    let groups = library.groups(&name)?;
    let route = searched(step, Search::Obtains, known, library)?;
    Some(route.borrowed().map(|taken| {
        // An item saying "A ↔ there is …" gives the "there is", the
        // reading whose target it is, as the build obtains from it.
        groups[taken.group]
            .gives
            .iter()
            .map(|said| {
                let there_is = readings(said, library)
                    .into_iter()
                    .map(|r| r.claimed)
                    .find(|t| library.exists.contains(&t.notation()))
                    .unwrap_or_else(|| said.clone());
                filled(&there_is, &taken.binding, &library.ctx)
            })
            .collect()
    }))
}

/// How a step's citation of an item is read: the group it takes and the
/// binding, by `taken` for a step that concludes what it claims and by
/// `obtained` for an obtain, over the parts the checks read; None where the
/// step cites no item or no group reads the citation, which the checks
/// report.
pub fn cited(step: &Step, library: &Library, known: &Known) -> Option<Cited> {
    let item = step.just.item(&step.just.cited_item()?);
    let groups = library.groups(&item)?;
    let parts = known.parts(step, library);
    let read = searched(step, search_of(step), known, library)?;
    let Built(taken) = &*read else {
        return None;
    };
    let before: usize = groups[..taken.group].iter().map(|g| g.gives.len()).sum();
    let cite = parts.cite(library);
    let stated = taken.first_pairs(&groups, &parts.facts, &cite);
    let firsts = firsts_at(step, &step.just.refs, &item, &stated, None, known, library);
    let mut supplying = taken.supplying_facts(&groups, &parts.facts, &cite);
    supplying.extend(typed_supplying(&item, library));
    let supplied = supplied_at(
        step,
        &step.just.refs,
        Some(&item),
        supplying,
        Values {
            binding: &with_seed(&taken.binding, &parts.seed),
            bound: Some(&taken.bound),
        },
        None,
        known,
        library,
    );
    let kinds = kinds_said(
        step,
        &item,
        &with_seed(&taken.binding, &parts.seed),
        known,
        library,
    );
    let item_letters = item_letters(
        &groups[taken.group],
        &taken.binding,
        step,
        &parts,
        known,
        library,
    );
    let facings = facings(&groups, taken, &parts, known, library);
    let met = meetings(&groups, taken, &parts, known, library);
    let within = parts_within(&groups, taken, &parts, known, library);
    let sought = Sought {
        refs: &step.just.refs,
        requires: None,
    };
    let unfolded = unfolded(
        step,
        sought,
        &groups[taken.group],
        taken,
        &item,
        known,
        library,
    );
    let mut out = Cited {
        item,
        group: taken.group,
        obtained: taken.obtained.map(|k| before + k),
        concluded: across_groups(taken, before),
        firsts,
        supplied,
        kinds,
        item_letters,
        facings,
        meetings: met.meetings,
        met_trees: met.trees,
        within,
        binding: taken.binding.clone(),
        bound: taken.bound.clone(),
        written: parts.seed.clone(),
        unfolded,
        recursions: IndexMap::new(),
    };
    out.recursions = recursions_met(&out, known, library);
    Some(out)
}

/// Each step and requires line read at a member of its claim's "for all"
/// (`CheckedTheorem::at_member`), by the line of its justification: what
/// `citing::at_a_member` decides of it, or an instantiation reading a letter
/// its line binds at the claim's own (`Instantiated::at_claim`), its claim
/// read as written.
pub fn at_member(
    thm: &Theorem,
    library: &Library,
    known: &Known,
    instantiated: &IndexMap<usize, Instantiated>,
) -> IndexMap<usize, AtMember> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        at_member_of(step, library, known, instantiated, &mut out);
        for req in &step.requires {
            if let Some(as_step) = requires_read_as_step(step, req) {
                at_member_of(&as_step, library, known, instantiated, &mut out);
            }
        }
    }
    out
}

/// `at_member` of one step, added to `out` where it is read at a member.
fn at_member_of(
    step: &Step,
    library: &Library,
    known: &Known,
    instantiated: &IndexMap<usize, Instantiated>,
    out: &mut IndexMap<usize, AtMember>,
) {
    let claims: Option<Vec<Node>> = step
        .claim
        .sentences()
        .iter()
        .map(|s| known.read_written(s))
        .collect();
    let Some(claims) = claims else {
        return; // `check_formulas` says it does not read
    };
    let at_claim = instantiated
        .get(&step.just.line)
        .is_some_and(|i| i.at_claim.is_some());
    let read = match (at_claim, claims.as_slice()) {
        (true, [claim]) => citing::claimed_member(claim, library.env.g),
        _ => citing::at_a_member(step, &claims, library),
    };
    let Some((member, _)) = read else {
        return;
    };
    let part = match member.notation() {
        MEMBERSHIP => false,
        SUBSET => true,
        _ => return,
    };
    if let [letter, set] = member.children.as_slice() {
        out.insert(
            step.just.line,
            AtMember {
                letter: letter.text.to_string(),
                set: set.clone(),
                part,
            },
        );
    }
}

/// For each sentence `taken` concludes read backwards, what the right side
/// of its `↔` asks at the citation's values, with where each fact stands
/// among the lines `refs` names, the step's requires lines, or the `let`
/// lines in scope (`Cited::unfolded`); None for one read otherwise.
pub(super) fn unfolded(
    step: &Step,
    sought: Sought<'_>,
    group: &Group,
    taken: &Taken,
    item: &str,
    known: &Known,
    library: &Library,
) -> Vec<Option<Vec<Unfolded>>> {
    taken
        .concluded
        .iter()
        .map(|c| {
            if c.way != Way::Backward {
                return None;
            }
            let said = group.gives.get(c.sentence)?;
            let [_, right] = said.children.as_slice() else {
                return None;
            };
            if said.notation() != BICONDITIONAL {
                return None;
            }
            let at = filled(right, &taken.binding, &library.ctx);
            let witnesses = Binding::new();
            let bound = bound_renamed(right, &at, &taken.bound);
            Some(unfolded_parts(
                step, sought, &at, &bound, &witnesses, item, known, library,
            ))
        })
        .collect()
}

/// Where a citation's facts are sought: the lines it names, the step's or
/// a requires line's, and that requires line where it is one
/// (`supplied_at`).
#[derive(Clone, Copy)]
pub(super) struct Sought<'a> {
    pub refs: &'a [String],
    pub requires: Option<usize>,
}

/// The witnesses `bound` gives the "there is" letters of `right`, given as
/// well to the letters `at`, `right` filled at the citation's values, renames
/// them to: filling renames a letter a value names apart from it, h of `there
/// is h ∈ H` as a where u := t(h). The two have one shape, so their "there
/// is" letters pair in order.
fn bound_renamed(right: &Node, at: &Node, bound: &Binding) -> Binding {
    let letters = |n: &Node| -> Vec<Symbol> {
        n.walk()
            .iter()
            .filter(|m| matches!(m.notation(), THERE_IS | THERE_IS_SOME))
            .filter_map(|m| m.children.first().map(|l| l.text))
            .collect()
    };
    let mut out = bound.clone();
    for (own, renamed) in letters(right).into_iter().zip(letters(at)) {
        if own != renamed {
            if let Some(value) = bound.get(&own) {
                out.entry(renamed).or_insert_with(|| value.clone());
            }
        }
    }
    out
}

/// The parts of `node`, a definition's right side at a citation's values,
/// joined by "and" (`conjuncts`): a "there is" whose letter the citation
/// gives a witness in `bound` taken apart into the witness's membership and
/// the parts of its body, any other part a fact; each fact placed as a
/// citation's hypothesis is (`supplied_at`). `outer` holds the witnesses of
/// the "there is"es around `node`, put in each fact as it is recorded and
/// not in `node` first, where putting a witness that names a letter of an
/// inner "there is" would rename that letter apart from its witness.
#[allow(clippy::too_many_arguments)]
pub(super) fn unfolded_parts(
    step: &Step,
    sought: Sought<'_>,
    node: &Node,
    bound: &Binding,
    outer: &Binding,
    item: &str,
    known: &Known,
    library: &Library,
) -> Vec<Unfolded> {
    // Each fact is sought as the citing lines are read, with the defines
    // the citation cites written out (`Known::read_citing`): g(s) as f(s).
    // A requires line cites its own lines, not the step's.
    let defined = known.citing_item(sought.refs, Some(item));
    let fact = |fact: Node, at: &Binding| {
        let fact = substitute_apart(&fact, at, &library.ctx);
        let read = standard(&expand(&fact, &defined), &library.ctx);
        let supplied = supplied_at(
            step,
            sought.refs,
            Some(item),
            vec![Supplying {
                want: fact.clone(),
                fact: Some(read),
                at: None,
            }],
            Values {
                binding: &Binding::new(),
                bound: None,
            },
            sought.requires,
            known,
            library,
        )
        .pop();
        let (by, meeting) = match supplied {
            Some(s) => (s.by, s.meeting),
            None => (SuppliedBy::Unstated, None),
        };
        Unfolded::Fact { fact, by, meeting }
    };
    conjuncts(node, library)
        .into_iter()
        .map(|part| {
            let (letter, domain, body) =
                match (part.notation(), part.children.as_slice()) {
                    (THERE_IS, [letter, domain, body]) => (letter, domain, Some(body)),
                    (THERE_IS_SOME, [letter, domain]) => (letter, domain, None),
                    _ => return fact(part.clone(), outer),
                };
            let Some(value) = bound.get(&letter.text) else {
                return fact(part.clone(), outer);
            };
            // A "there is" a cited line states whole, where the reading
            // gives its letter that line's own bound letter, which names
            // nothing in scope, is taken from the line, and no witness is
            // shown for it.
            if value.is_name() {
                let whole = fact(part.clone(), outer);
                if let Unfolded::Fact {
                    by: SuppliedBy::Line(at),
                    ..
                } = &whole
                {
                    let bound_there = at.written.notation() == THERE_IS
                        && at
                            .written
                            .children
                            .first()
                            .is_some_and(|l| l.text == value.text);
                    if bound_there {
                        return whole;
                    }
                }
            }
            // The witness is a term of the page, which may name a letter as
            // the item's own letters are named; the outer witnesses are put
            // in the item's terms only, its domain and body.
            let value = value.clone();
            let mut inner = outer.clone();
            inner.insert(letter.text, value.clone());
            // The domain may name the witnesses before this one.
            let member = bound_in(Bound::Member, letter, domain, library.env.g);
            let member = fact(member, &inner);
            let body = body.map_or_else(Vec::new, |b| {
                unfolded_parts(step, sought, b, bound, &inner, item, known, library)
            });
            Unfolded::Witness {
                value,
                member: Box::new(member),
                body,
            }
        })
        .collect()
}

/// For each sentence `taken` concludes, which way the item's equation read
/// at the binding faces the claim's sentence it gives, the claim's
/// sentences by their place (`record::Cited::facings`). Sides are compared
/// as `Known::alike_through` compares, bound letters renamed, spellings
/// read alike, and the citation's defines read out where a side asks.
pub(super) fn facings(
    groups: &[Group],
    taken: &Taken,
    parts: &Parts,
    known: &Known,
    library: &Library,
) -> Vec<Option<Facing>> {
    let group = &groups[taken.group];
    let claims = &citing::claims_taken(group, &parts.claims, library);
    taken
        .concluded
        .iter()
        .enumerate()
        .map(|(k, c)| {
            let said = group.gives.get(c.sentence)?;
            let read = readings(said, library)
                .into_iter()
                .find(|r| r.way == c.way)?;
            let item = filled(&read.claimed, &taken.binding, &library.ctx);
            facing_of(&item, claims.get(k)?, parts.unfolds.as_deref(), known)
        })
        .collect()
}

/// Which way a step writes the equation a define gives, `equation`, beside
/// the define's own (`Substituted::define_facing`): a define of a name by
/// its equation, `named` (`formulas::define_equation`), as `facing_of`
/// meets the two; a define of a function by the side that applies it,
/// `q(a)` of `q(a) = a + 1`. None where neither side is so.
pub(in crate::checker) fn define_facing(
    thm: &Theorem,
    label: &str,
    equation: &Node,
    named: Option<&Node>,
    known: &Known,
) -> Option<Facing> {
    if let Some(named) = named {
        return facing_of(named, equation, None, known);
    }
    let d = thm.defines.iter().find(|d| d.label == label)?;
    let rule = DefinedRule::of(d, known).ok()??;
    let applies = |side: &Node| {
        side.notation() == APPLICATION
            && side
                .children
                .first()
                .is_some_and(|f| f.is_name() && f.text == rule.name)
    };
    match equation.children.as_slice() {
        [left, _] if applies(left) => Some(Facing::Straight),
        [_, right] if applies(right) => Some(Facing::Turned),
        _ => None,
    }
}

/// Which way one equation, or one congruence, faces another: a side of the
/// one alike the same side of the other, or only the other side, as
/// `Known::alike_through` compares them with `unfolds`; None where the two
/// are not both equations, or both congruences with moduli alike, or no
/// side meets.
pub(in crate::checker) fn facing_of(
    item: &Node,
    claim: &Node,
    unfolds: Option<&Unfolds>,
    known: &Known,
) -> Option<Facing> {
    let meets = |a: &Node, b: &Node| known.alike_through(a, b, unfolds).is_some();
    let sided = match (item.notation(), claim.notation()) {
        (EQUALITY, EQUALITY) => true,
        (CONGRUENT_MOD, CONGRUENT_MOD) => meets(&item.children[2], &claim.children[2]),
        _ => false,
    };
    if !sided {
        return None;
    }
    let (il, ir) = (&item.children[0], &item.children[1]);
    let (cl, cr) = (&claim.children[0], &claim.children[1]);
    if meets(il, cl) || meets(ir, cr) {
        Some(Facing::Straight)
    } else if meets(il, cr) || meets(ir, cl) {
        Some(Facing::Turned)
    } else {
        None
    }
}

/// For each sentence `taken` concludes, how the item's sentence read at the
/// binding met the claim's sentence it gives (`record::Cited::meetings`), as
/// `Known::alike_through` meets them with the citation's defines: the
/// whole, or else the part its reading's "and" gives (`Concluded::part`);
/// and where that is an "and" of which the claim is one part
/// (`parts_within`), that part. None where nothing of it meets the claim's
/// sentence, or more than one part does.
pub(super) fn meetings(
    groups: &[Group],
    taken: &Taken,
    parts: &Parts,
    known: &Known,
    library: &Library,
) -> Meetings {
    let group = &groups[taken.group];
    let claims = &citing::claims_taken(group, &parts.claims, library);
    let unfolds = parts.unfolds.as_deref();
    let mut out = Meetings {
        meetings: Vec::new(),
        trees: Vec::new(),
    };
    for (k, c) in taken.concluded.iter().enumerate() {
        let met = group.gives.get(c.sentence).and_then(|said| {
            let read = readings(said, library)
                .into_iter()
                .find(|r| r.way == c.way)?;
            let claim = claims.get(k)?;
            let (meeting, item) = meeting_of(
                &read.claimed,
                c.part,
                taken,
                claim,
                unfolds,
                known,
                library,
            )?;
            Some((
                meeting,
                MetTrees {
                    item,
                    claim: claim.clone(),
                },
            ))
        });
        let (meeting, trees) = met.unzip();
        out.meetings.push(meeting);
        out.trees.push(trees);
    }
    out
}

/// How each concluded sentence met the claim (`Cited::meetings`), and the
/// two trees each meeting is of (`Cited::met_trees`).
pub(super) struct Meetings {
    pub(super) meetings: Vec<Option<Meeting>>,
    pub(super) trees: Vec<Option<MetTrees>>,
}

/// How `claim` meets what an item's sentence `claimed` gives at the
/// citation's values: the whole, or part `part` of it, or the one part of
/// that which meets it; with that tree.
fn meeting_of(
    claimed: &Node,
    part: Option<usize>,
    taken: &Taken,
    claim: &Node,
    unfolds: Option<&Unfolds>,
    known: &Known,
    library: &Library,
) -> Option<(Meeting, Node)> {
    let binding = &taken.binding;
    let met = |item: Node| {
        known
            .alike_through(&item, claim, unfolds)
            .map(|m| (m, item))
    };
    let whole = filled(claimed, binding, &library.ctx);
    if let Some(found) = met(whole.clone()) {
        return Some(found);
    }
    // A letter bound to a rule standing alone, function-into's f at x ↦
    // f(x) where the claim reads the define g it names as that rule (`g : L
    // → U`), is the rule there, as the claim has it.
    if let Some(found) = met(substitute_apart(claimed, binding, &library.ctx)) {
        return Some(found);
    }
    let item = match part {
        Some(j) => {
            let part = conjuncts(claimed, library).into_iter().nth(j)?;
            filled(&part, binding, &library.ctx)
        }
        None => whole,
    };
    if let Some(found) = met(item.clone()) {
        return Some(found);
    }
    let parts = conjuncts(&item, library);
    let mut each = parts.into_iter().filter_map(met);
    match (each.next(), each.next()) {
        (Some(one), None) => Some(one),
        _ => None,
    }
}

/// For each sentence `taken` concludes, where the claim's sentence it gives
/// is one part of the item's part read at the binding, which part, counted
/// from 0 with every conjunction taken apart (`record::Cited::within`). The
/// item's part is the one its reading's "and" gives (`Concluded::part`), a
/// property applied in it read as the property's body at its argument; None
/// where that meets the claim's sentence whole, as `Known::alike_through`
/// meets them with the citation's defines, or no part of it does, or more
/// than one does.
pub(super) fn parts_within(
    groups: &[Group],
    taken: &Taken,
    parts: &Parts,
    known: &Known,
    library: &Library,
) -> Vec<Option<usize>> {
    let group = &groups[taken.group];
    let claims = &citing::claims_taken(group, &parts.claims, library);
    let unfolds = parts.unfolds.as_deref();
    let meets = |a: &Node, b: &Node| known.alike_through(a, b, unfolds).is_some();
    taken
        .concluded
        .iter()
        .enumerate()
        .map(|(k, c)| {
            let said = group.gives.get(c.sentence)?;
            let read = readings(said, library)
                .into_iter()
                .find(|r| r.way == c.way)?;
            let part = match c.part {
                Some(j) => conjuncts(&read.claimed, library).into_iter().nth(j)?,
                None => read.claimed.clone(),
            };
            let item = filled(&part, &taken.binding, &library.ctx);
            let claim = claims.get(k)?;
            if meets(&item, claim) {
                return None;
            }
            let parts = conjuncts(&item, library);
            let mut meet = parts
                .iter()
                .enumerate()
                .filter(|(_, p)| meets(p, claim))
                .map(|(j, _)| j);
            match (parts.len() > 1, meet.next(), meet.next()) {
                (true, Some(j), None) => Some(j),
                _ => None,
            }
        })
        .collect()
}

/// For each letter of the group a citation takes that the binding gives a
/// value, the number system the item takes it in, by the group's own
/// hypothesis `x ∈ S`, and the narrowest the page says its value is in,
/// by the one membership rule (`membership::shown`) over the step's facts
/// (`record::ItemLetter`).
pub(super) fn item_letters(
    group: &Group,
    binding: &Binding,
    step: &Step,
    parts: &Parts,
    known: &Known,
    library: &Library,
) -> Vec<ItemLetter> {
    let letters = super::super::library::introduced(known, step);
    let item_system = |letter: Symbol| {
        group.asked().find_map(|want| {
            match (want.notation(), want.children.as_slice()) {
                (MEMBERSHIP, [x, set])
                    if x.is_name()
                        && x.text == letter
                        && set.notation() == NUMBER_SYSTEMS =>
                {
                    System::of_sign(&set.text)
                }
                _ => None,
            }
        })
    };
    let typed: Vec<Node> = parts
        .facts
        .iter()
        .filter(|f| types_a_function(f))
        .cloned()
        .collect();
    let in_sums = super::super::library::typed_in_scope(known, step);
    let given = membership::Facts {
        facts: &parts.facts,
        letters,
        ranged: IndexMap::new(),
        typed: &typed,
        in_sums: &in_sums,
        targets: &library.targets,
        ctx: known.ctx,
    };
    let narrowest = |value: &Node| {
        [
            System::N,
            System::N0,
            System::Z,
            System::Q,
            System::R,
            System::C,
        ]
        .into_iter()
        .find(|s| membership::holds(value, *s, &given))
    };
    binding
        .iter()
        .map(|(letter, value)| ItemLetter {
            letter: *letter,
            item_system: item_system(*letter),
            value_system: narrowest(value),
            value_set: (value.notation() == NUMBER_SYSTEMS)
                .then(|| System::of_sign(&value.text))
                .flatten(),
        })
        .collect()
}

/// Each requires line's citation of an item, by the line it is on
/// (`cited_requires`), and the citation of the reason under a let saying a
/// kind of number, read as a requires line of the step below the let, as
/// `check_requires` reads it.
pub fn requires_cited(
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> IndexMap<usize, Cited> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        // A chain line's own reason is read as a requires line's is
        // (`ChainLine::reason`), resting on every requires line of its step.
        let reasons = chain_reasons(&step.just, &thm.path);
        for req in step.requires.iter().chain(&reasons) {
            if let Some(read) = cited_requires(step, req, library, known) {
                out.insert(req.line, read);
            }
        }
    }
    for d in &thm.defines {
        // A let whose kind does not read is reported where the checker
        // judges the let, and the build builds nothing with a problem.
        let Ok(Some(kinded)) = d.kinded(&thm.path, &known.env.g.members) else {
            continue;
        };
        let (Some(after), Some(reason)) = (thm.step_after(d.line), d.reason.as_ref())
        else {
            continue;
        };
        // The let's requires lines are read under it as well, each resting
        // on those above it.
        let under = reason.under(&d.label, after, kinded.shown.fact.clone());
        for req in &under.requires {
            if let Some(read) = cited_requires(&under, req, library, known) {
                out.insert(req.line, read);
            }
        }
    }
    out
}

/// How a requires line's citation of an item is read, over the parts the
/// line's check reads (`requires_parts`): what its reason names, the lines
/// above it, and the member its step's claim is said of. None where the
/// line cites no item or no group concludes its fact, the item then applied
/// as often as it takes (`check_requires`).
pub fn cited_requires(
    step: &Step,
    req: &Requires,
    library: &Library,
    known: &Known,
) -> Option<Cited> {
    let (named, _) = req.cited_item()?;
    let item = step.just.item(&named);
    let groups = library.groups(&item)?;
    let parts = requires_parts(step, req, &[], known, library, Spelt::Written)?;
    let cite = parts.cite(library);
    let Built(taken) = taken(&groups, &parts.claims, &parts.facts, &parts.seed, &cite)
    else {
        return None;
    };
    let before: usize = groups[..taken.group].iter().map(|g| g.gives.len()).sum();
    let stated = taken.first_pairs(&groups, &parts.facts, &cite);
    let firsts = firsts_at(
        step,
        req.lines(),
        &item,
        &stated,
        Some(req.line),
        known,
        library,
    );
    let mut supplying = taken.supplying_facts(&groups, &parts.facts, &cite);
    supplying.extend(typed_supplying(&item, library));
    let supplied = supplied_at(
        step,
        req.lines(),
        Some(&item),
        supplying,
        Values {
            binding: &with_seed(&taken.binding, &parts.seed),
            bound: Some(&taken.bound),
        },
        Some(req.line),
        known,
        library,
    );
    let kinds = kinds_said(
        step,
        &item,
        &with_seed(&taken.binding, &parts.seed),
        known,
        library,
    );
    let item_letters = item_letters(
        &groups[taken.group],
        &taken.binding,
        step,
        &parts,
        known,
        library,
    );
    let facings = facings(&groups, &taken, &parts, known, library);
    let met = meetings(&groups, &taken, &parts, known, library);
    let within = parts_within(&groups, &taken, &parts, known, library);
    let sought = Sought {
        refs: req.lines(),
        requires: Some(req.line),
    };
    let unfolded = unfolded(
        step,
        sought,
        &groups[taken.group],
        &taken,
        &item,
        known,
        library,
    );
    let mut out = Cited {
        item,
        group: taken.group,
        obtained: taken.obtained.map(|k| before + k),
        concluded: across_groups(&taken, before),
        firsts,
        supplied,
        kinds,
        item_letters,
        facings,
        meetings: met.meetings,
        met_trees: met.trees,
        within,
        binding: taken.binding.clone(),
        bound: taken.bound,
        written: parts.seed,
        unfolded,
        recursions: IndexMap::new(),
    };
    out.recursions = recursions_met(&out, known, library);
    Some(out)
}

/// Where `fact`, a line's "for all", is over a set that holds the one
/// `asked` is over, which the search reads it over (`supply::narrowed`, by
/// `set_within`): the two sets. None where they are the same, or either is
/// no "for all".
pub(super) fn narrowed_of(
    asked: &Node,
    fact: &Node,
    ctx: &Context,
) -> Option<Narrowed> {
    let ([_, to, _], [_, from, _]) =
        (asked.children.as_slice(), fact.children.as_slice())
    else {
        return None;
    };
    let none = IndexMap::new();
    let apart = asked.notation() == FOR_ALL
        && fact.notation() == FOR_ALL
        && !alike(&standard(to, ctx), &standard(from, ctx), ctx, &none, &none);
    (apart && citing::set_within(to, from)).then(|| Narrowed {
        from: from.clone(),
        to: to.clone(),
    })
}

/// The search's binding with what the citation's seed gives the letters it
/// leaves out: the sets of an item's function type, which the search does
/// not match and `typed_seed` fixes from the citing proof's lets
/// (`typed_supplying`).
pub(super) fn with_seed(binding: &Binding, seed: &Binding) -> Binding {
    let mut out = binding.clone();
    for (letter, value) in seed {
        out.entry(*letter).or_insert_with(|| value.clone());
    }
    out
}

/// Where each part of what each reading asks first stands, by the
/// reading's place, searched as a hypothesis the citation needs is
/// (`Suppliers`): among the lines `refs` names at `step`, the sentence of
/// a line it is, or is a part of, or the line where it is the line's
/// sentences together, each read as the citation of `item` reads them;
/// else a requires line, the `let` line that says it once, or the
/// said-once walk. A part no fact states is `Unstated`. Within a reading,
/// each place once.
pub(super) fn firsts_at(
    step: &Step,
    refs: &[String],
    item: &str,
    readings: &[Vec<FirstFact>],
    below: Option<usize>,
    known: &Known,
    library: &Library,
) -> Vec<Vec<First>> {
    let suppliers = Suppliers::new(step, refs, Some(item), below, known, library);
    readings
        .iter()
        .map(|firsts| reading_firsts(&suppliers, firsts))
        .collect()
}

/// `firsts_at` of one reading.
fn reading_firsts(suppliers: &Suppliers, firsts: &[FirstFact]) -> Vec<First> {
    let mut out: Vec<First> = Vec::new();
    for first in firsts {
        let Some(fact) = &first.fact else {
            out.push(First {
                asked: first.asked.clone(),
                by: SuppliedBy::Unstated,
                meeting: None,
            });
            continue;
        };
        let by = suppliers.by(fact);
        let placed = |o: &First| match (&o.by, &by) {
            (SuppliedBy::Line(a), SuppliedBy::Line(b))
            | (SuppliedBy::SaidOnce(a), SuppliedBy::SaidOnce(b)) => a.same_place(b),
            (
                SuppliedBy::Requires { line, implied },
                SuppliedBy::Requires {
                    line: other,
                    implied: theirs,
                },
            ) => line == other && implied == theirs,
            _ => false,
        };
        if !out.iter().any(placed) {
            let meeting = suppliers.meeting(&first.asked, fact, &by, None);
            out.push(First {
                asked: first.asked.clone(),
                by,
                meeting,
            });
        }
    }
    out
}

/// Where `fact` stands among the lines `refs` names at `step`, each read as
/// the citation of `item` reads them (`firsts_at`), or as the step reads
/// them where it cites no item; None where no line names says it.
pub(in crate::checker) fn fact_at(
    step: &Step,
    refs: &[String],
    item: Option<&str>,
    fact: &Node,
    known: &Known,
    library: &Library,
) -> Option<FirstAt> {
    fact_at_through(step, refs, item, fact, None, known, library)
}

/// `fact_at`, with a define of `unfolds` read out where `fact` and a line
/// differ (`states_through`).
pub(super) fn fact_at_through(
    step: &Step,
    refs: &[String],
    item: Option<&str>,
    fact: &Node,
    unfolds: Option<&Unfolds>,
    known: &Known,
    library: &Library,
) -> Option<FirstAt> {
    let states = |said: &Node| states_through(said, fact, unfolds, library);
    line_at(step, refs, item, &states, known, library)
}

/// Where a "there is", `fact`, stands among the lines `refs` names at
/// `step` as a line states its body at a witness, `3·k·(k + 1) =
/// 6·(m·(2m + 1))` of "there is k′ ∈ ℤ with 3·k·(k + 1) = 6·k′" (`SYNTAX.md`,
/// exhibit), each read as the citation of `item` reads them: the search's
/// own reading of a "there is" (`supply::supplier`), the witness shown in
/// its domain among the step's `facts`. None for a fact of another kind,
/// or where no line states it so.
pub(super) fn witnessed_at(
    step: &Step,
    refs: &[String],
    item: Option<&str>,
    fact: &Node,
    facts: &[Node],
    known: &Known,
    library: &Library,
) -> Option<FirstAt> {
    if !library.exists.contains(&fact.notation()) {
        return None;
    }
    let none = Binding::new();
    let open = BTreeSet::new();
    let sites = Sites::new();
    // The line first, then the step's facts, among which the search finds
    // the witness in its domain (`supply::witnessed_in`); the line states it
    // where the search takes the line.
    let states = |said: &Node| {
        let mut with: Vec<Node> = vec![said.clone()];
        with.extend(facts.iter().cloned());
        citing::supplier(fact, &with, &none, &open, &Cite::plain(library), &sites)
            .is_some_and(|took| ptr::eq(took, &with[0]))
    };
    line_at(step, refs, item, &states, known, library)
}

/// Where a line `refs` names at `step` says what `states` accepts, each
/// line read as the citation of `item` reads it (`fact_at`).
pub(super) fn line_at(
    step: &Step,
    refs: &[String],
    item: Option<&str>,
    states: &dyn Fn(&Node) -> bool,
    known: &Known,
    library: &Library,
) -> Option<FirstAt> {
    let scope = known.scope(step);
    let defined = known.citing_item(refs, item);
    refs.iter().find_map(|r| {
        let stated = scope.get(r)?;
        // Counted as the page writes them: the line's sentences by their
        // place, then each "for all" of it read at a block's letter, in
        // order, past the line's own.
        let says = known.says(stated, &defined);
        let own = known.sentence_count(stated);
        let sentences = says.iter().filter_map(|s| match s.from {
            SaidFrom::Sentence(k) => Some((k, s)),
            _ => None,
        });
        let at = says
            .iter()
            .filter(|s| matches!(s.from, SaidFrom::AtLetter { part: None, .. }))
            .enumerate()
            .map(|(k, s)| (own + k, s));
        let said: Vec<(usize, &super::super::library::Said)> =
            sentences.chain(at).collect();
        line_states(states, r, &said, library)
            .or_else(|| {
                // The equation between two terms of a chain the line writes,
                // x² = 0 of x² = y = 0 (`FirstAt::pair`).
                says.iter()
                    .filter(|s| matches!(s.from, SaidFrom::Pair { .. }))
                    .find(|s| states(&s.cited))
                    .and_then(|s| placed(r, s, &says, own))
            })
            .or_else(|| {
                // What the line implies, where it writes nothing that states
                // the fact.
                says.iter()
                    .filter(|s| s.implied.is_some())
                    .find(|s| states(&s.cited))
                    .and_then(|s| placed(r, s, &says, own))
            })
    })
}

/// Where each `restate` step's claim of one sentence, and each requires line
/// reasoned from lines alone, stands in a line it names
/// (`CheckedTheorem::restated`): a sentence, a part of one, a "for all"
/// read at a block's letter, or what a line implies (`fact_at`). By the
/// line of the justification; one no line it names states, a fact only the
/// lines together give, is left out.
pub fn restatements(
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> IndexMap<usize, Restated> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        if step.just.head.is(Method::Restate) && step.claim.sentences().len() == 1 {
            if let Some(found) =
                restated_at(step, &step.just.refs, &step.claim, known, library)
            {
                out.insert(step.just.line, stated(found));
            }
        }
        // A requires line of a letter the claim says "for all" of, which no
        // line states at that letter: where a line states it under the
        // claim's "for all", g′(x) ≠ 0 of "for all x ∈ D" from H11 "for all
        // x ∈ D, g′(x) ≠ 0", that line, the fact said of every member.
        let claimed = step
            .claim
            .sentences()
            .first()
            .and_then(|s| known.read_as_written(s));
        for req in step.requires.iter().filter(|r| r.is_lines()) {
            if let Some(found) =
                restated_at(step, req.lines(), &req.fact, known, library)
            {
                out.insert(req.line, stated(found));
                continue;
            }
            let Some(fact) = known.whole_as_written(&req.fact) else {
                continue;
            };
            let under_claim = claimed
                .as_ref()
                .filter(|claim| citing::speaks_of_claim_letter(claim, &fact));
            if let Some(claim) = under_claim {
                let under =
                    standard(&citing::under_claim_binders(claim, &fact), &library.ctx);
                if let Some(at) =
                    fact_at(step, req.lines(), None, &under, known, library)
                {
                    let meeting = known
                        .alike_how(&under, &at.written)
                        .filter(|m| !m.as_written());
                    out.insert(
                        req.line,
                        Restated::UnderClaim {
                            at,
                            meeting,
                            part: None,
                        },
                    );
                    continue;
                }
                if let Some((at, part)) =
                    part_under_claim(step, req.lines(), &under, known, library)
                {
                    out.insert(
                        req.line,
                        Restated::UnderClaim {
                            at,
                            meeting: None,
                            part: Some(part),
                        },
                    );
                    continue;
                }
            }
            if let Some(found) = narrowed_at(step, req, &fact, known, library) {
                out.insert(req.line, found);
                continue;
            }
            if let Some(by) = lines_give(step, req, &fact, known, library) {
                out.insert(req.line, Restated::Lines(by));
            }
        }
    }
    // The reason under a define that says a kind, read as the requires line
    // it is checked as, under the step after the define
    // (`citations::check_kinds`, `Reason::under`), by its reason's line.
    for d in &thm.defines {
        let Ok(Some(kinded)) = d.kinded(&thm.path, &known.env.g.members) else {
            continue;
        };
        let (Some(after), Some(reason)) = (thm.step_after(d.line), d.reason.as_ref())
        else {
            continue;
        };
        let under = reason.under(&d.label, after, kinded.shown.fact.clone());
        let Some(req) = under.requires.last().filter(|r| r.is_lines()) else {
            continue;
        };
        let Ok(by) = &req.by else {
            continue;
        };
        if let Some(found) = restated_at(&under, req.lines(), &req.fact, known, library)
        {
            out.insert(by.line, stated(found));
        }
    }
    out
}

/// A line stating a restatement (`Restated::Stated`), with how it met it
/// where not as written.
fn stated((at, meeting): (FirstAt, Option<Meeting>)) -> Restated {
    Restated::Stated {
        at,
        meeting: meeting.filter(|m| !m.as_written()),
    }
}

/// Where a line a requires line names says its "for all" over a set that
/// holds the requires line's (`narrowed_of`), the body the same once read
/// over the wider set: the line's place and the two sets
/// (`Restated::Narrowed`). None where no line does.
fn narrowed_at(
    step: &Step,
    req: &Requires,
    fact: &Node,
    known: &Known,
    library: &Library,
) -> Option<Restated> {
    let ctx = &library.ctx;
    let asked = standard(fact, ctx);
    let scope = known.scope(step);
    let defined = known.citing_item(req.lines(), None);
    req.lines().iter().find_map(|r| {
        let stated = scope.get(r)?;
        let says = known.says(stated, &defined);
        let own = known.sentence_count(stated);
        says.iter().find_map(|s| {
            let narrowed = narrowed_of(&asked, &s.cited, ctx)?;
            // The asked "for all" over the line's set is the line's.
            let [letter, _, body] = asked.children.as_slice() else {
                return None;
            };
            let widened = asked.with_children(vec![
                letter.clone(),
                narrowed.from.clone(),
                body.clone(),
            ]);
            if !known.alike(&widened, &s.cited) {
                return None;
            }
            let at = placed(r, s, &says, own)?;
            Some(Restated::Narrowed { at, narrowed })
        })
    })
}

/// What supplies the fact of a requires line reasoned from lines that no one
/// of them states (`CheckedTheorem::restated_by`): what the lines it names
/// give together, a function's value in its codomain from its type and its
/// argument's membership, before the said-once walk, since the requires line
/// is reasoned from them (`Suppliers::derived`, `Suppliers::by`). None where
/// nothing supplies it.
fn lines_give(
    step: &Step,
    req: &Requires,
    fact: &Node,
    known: &Known,
    library: &Library,
) -> Option<SuppliedBy> {
    let suppliers =
        Suppliers::new(step, req.lines(), None, Some(req.line), known, library);
    let standard_fact = standard(fact, &library.ctx);
    let by = suppliers
        .derived(&standard_fact)
        .unwrap_or_else(|| suppliers.by(&standard_fact));
    (!matches!(by, SuppliedBy::Unstated)).then_some(by)
}

/// Where a line `refs` names says `under`, a fact under the claim's "for
/// all", as one part of the body of its own "for all" over the same set:
/// `for all x ∈ ℚ, s(x) ∈ ℕ₀` of line 4 "for all x ∈ ℚ, s(x) ∈ ℕ₀ and
/// numer(x) = (1 − 2·s(x))·|numer(x)|". The sentence, and the part.
fn part_under_claim(
    step: &Step,
    refs: &[String],
    under: &Node,
    known: &Known,
    library: &Library,
) -> Option<(FirstAt, BodyPart)> {
    let (FOR_ALL, [letter, set, fact]) = (under.notation(), under.children.as_slice())
    else {
        return None;
    };
    let scope = known.scope(step);
    let defined = known.citing_item(refs, None);
    refs.iter().find_map(|r| {
        let stated = scope.get(r)?;
        let says = known.says(stated, &defined);
        let own = known.sentence_count(stated);
        says.iter()
            .filter(|s| matches!(s.from, SaidFrom::Sentence(_)))
            .find_map(|s| {
                let (FOR_ALL, [bound, over, body]) =
                    (s.cited.notation(), s.cited.children.as_slice())
                else {
                    return None;
                };
                if !states(over, &standard(set, &library.ctx), library) {
                    return None;
                }
                let put = Binding::from([(bound.text, letter.clone())]);
                let body = substitute_apart(body, &put, &library.ctx);
                let parts = citing::conjuncts(&body, library);
                let fact = standard(fact, &library.ctx);
                let part = parts.iter().position(|p| states(p, &fact, library))?;
                let at = placed(r, s, &says, own)?;
                Some((
                    at,
                    BodyPart {
                        part,
                        of: parts.len(),
                    },
                ))
            })
    })
}

/// Where `said`, a restatement, stands among the lines `refs` names
/// (`fact_at`), and how the line as written met it (`Known::alike_how`).
/// The fact is read in the standard order, as the lines it is sought among
/// are (`states`): `k ≥ 1` as `1 ≤ k`.
pub(super) fn restated_at(
    step: &Step,
    refs: &[String],
    said: &Written,
    known: &Known,
    library: &Library,
) -> Option<(FirstAt, Option<Meeting>)> {
    let fact = standard(&known.whole_as_written(said)?, &library.ctx);
    let at = fact_at(step, refs, None, &fact, known, library)?;
    let meeting = known.alike_how(&fact, &at.written);
    Some((at, meeting))
}

/// Where `fact`, a membership the page says once, stands among the lines
/// in scope at `step` that introduce a letter (`SYNTAX.md`, a membership is
/// said once): a `let`, or an `obtain` above the step in a block around it,
/// as `library::introducing` reads them; the line itself, or what it
/// implies, `n > 0` of `let n ∈ ℕ`. None where no such line states it.
pub(super) fn said_once_at(
    step: &Step,
    item: Option<&str>,
    fact: &Node,
    unfolds: Option<&Unfolds>,
    known: &Known,
    library: &Library,
) -> Option<FirstAt> {
    let scope = known.scope(step);
    let mut lines: Vec<String> = scope
        .iter()
        .filter(|(_, stated)| {
            matches!(stated, super::super::library::Stated::Introduced(_))
        })
        .map(|(label, _)| label.clone())
        .collect();
    lines.extend(
        known
            .thm
            .steps
            .iter()
            .filter(|o| o.just.head.is(Method::Obtain) && o.line < step.line)
            .filter(|o| o.number.parent().contains(&step.number))
            .filter_map(|o| o.number.number().map(|n| n.to_string()))
            .filter(|n| scope.contains_key(n)),
    );
    // A line in another case of the same "cases" is in no reach of the
    // step, 3.1's m ∈ ℕ of the first case for a step of the second.
    lines.retain(|n| known.in_reach(n, step));
    fact_at_through(step, &lines, item, fact, unfolds, known, library)
}

/// Whether `said`, read in the standard order, states `fact`.
pub(super) fn states(said: &Node, fact: &Node, library: &Library) -> bool {
    states_through(said, fact, None, library)
}

/// `states`, with a define of `unfolds` read out where the two differ and
/// one asks for what it names (`matching::Reading`).
pub(super) fn states_through(
    said: &Node,
    fact: &Node,
    unfolds: Option<&Unfolds>,
    library: &Library,
) -> bool {
    let ctx = &library.ctx;
    let none = IndexMap::new();
    let reading = match unfolds {
        Some(u) => matching::Reading::with(ctx, u),
        None => matching::Reading::plain(ctx),
    };
    alike(&standard(said, ctx), fact, reading, &none, &none)
}

/// Where `s`, one of the things the line `line` says (`says`, of a line
/// writing `own` sentences), stands as `FirstAt` counts it: a sentence, a
/// part of one, the sentences together, a chain's equation between two of
/// its terms (`FirstAt::pair`), or a "for all" read at a block's letter
/// past the line's own; or what one of those implies. None for a subset's
/// members, or a part of a "for all" read at a letter.
pub(in crate::checker) fn placed(
    line: &str,
    s: &super::super::library::Said,
    says: &[super::super::library::Said],
    own: usize,
) -> Option<FirstAt> {
    let (from, implied) = match (s.from, s.implied) {
        (SaidFrom::Implied(_), Some(i)) => (i.source, Some(i.rule)),
        (SaidFrom::Implied(_), None) => return None,
        (from, _) => (from, None),
    };
    let mut pair = None;
    let (sentence, part) = match from {
        SaidFrom::Whole => (None, None),
        SaidFrom::Sentence(k) => (Some(k), None),
        SaidFrom::Part { sentence, part } => (Some(sentence), Some(part)),
        // The equation between two terms of the chain the sentence is.
        SaidFrom::Pair { sentence, from, to } => {
            pair = Some(ChainTerms { from, to });
            (Some(sentence), None)
        }
        // A "for all" read at a block's letter, numbered past the line's own
        // sentences in the order read; a part of one, that reading's part.
        SaidFrom::AtLetter { sentence, part } => {
            let whole = SaidFrom::AtLetter {
                sentence,
                part: None,
            };
            let reading = says
                .iter()
                .filter(|o| matches!(o.from, SaidFrom::AtLetter { part: None, .. }))
                .position(|o| o.from == whole)?;
            (Some(own + reading), part)
        }
        SaidFrom::Implied(_) | SaidFrom::Members(_) => return None,
    };
    Some(FirstAt {
        line: line.to_string(),
        sentence,
        part,
        written: s.written.clone(),
        implied,
        pair,
    })
}

/// Where the line `line`, whose sentences read as `said`, says what `states`
/// accepts, each sentence by its place (`FirstAt::sentence`), with what the
/// page writes there.
pub(super) fn line_states(
    states: &dyn Fn(&Node) -> bool,
    line: &str,
    said: &[(usize, &super::super::library::Said)],
    library: &Library,
) -> Option<FirstAt> {
    let at = |sentence, part, written| FirstAt {
        line: line.to_string(),
        sentence,
        part,
        written,
        implied: None,
        pair: None,
    };
    for &(i, s) in said {
        if states(&s.cited) {
            return Some(at(Some(i), None, s.written.clone()));
        }
        // Counted as written.
        if let Some(j) = conjuncts(&s.cited, library).iter().position(states) {
            let written = conjuncts(&s.written, library)
                .get(j)
                .cloned()
                .unwrap_or_else(|| s.written.clone());
            return Some(at(Some(i), Some(j), written));
        }
    }
    let whole = conjoined(
        library.env.g,
        said.iter().map(|(_, s)| s.cited.clone()).collect(),
    )?;
    let written = conjoined(
        library.env.g,
        said.iter().map(|(_, s)| s.written.clone()).collect(),
    )?;
    states(&whole).then(|| at(None, None, written))
}

/// Each function-type `let` line of the item, `f : X → Y`, and what a
/// finite group's `let` line says, `G is finite`, as a fact the citation
/// supplies, after the group's hypotheses: the group leaves them out
/// (`Library::function_types`, `Library::group_assertion_lines`), and a
/// backend that states them as hypotheses, Lean's `Set.MapsTo f X Y` and
/// `(Set.univ : Set G).Finite`, finds where each stands by its place.
pub(super) fn typed_supplying(item: &str, library: &Library) -> Vec<Supplying> {
    library
        .function_type_lines(item)
        .into_iter()
        .chain(library.group_assertion_lines(item))
        .map(|w| Supplying {
            want: w.tree,
            fact: None,
            at: Some(w.at),
        })
        .collect()
}

/// Each hypothesis of `item` that names a thing of a kind
/// (`Library::kind_lines`), with the line in scope at `step` that
/// introduces the citation's value for its letter (`KindSaid::line`): the
/// last `let` or `obtain` in reach whose names hold it, as a later
/// introduction stands over an earlier one.
pub(super) fn kinds_said(
    step: &Step,
    item: &str,
    binding: &Binding,
    known: &Known,
    library: &Library,
) -> Vec<KindSaid> {
    let scope = known.scope(step);
    library
        .kind_lines(item)
        .into_iter()
        .map(|kind| {
            let value = binding
                .get(kind.letter.as_str())
                .filter(|v| v.is_name())
                .map(|v| v.text.to_string());
            let line = value.and_then(|v| {
                let lets = scope.iter().filter_map(|(label, stated)| match stated {
                    super::super::library::Stated::Introduced(i)
                        if i.names().contains(&v) =>
                    {
                        Some(label.clone())
                    }
                    _ => None,
                });
                let obtains = known
                    .thm
                    .steps
                    .iter()
                    .filter(|o| o.just.head.is(Method::Obtain) && o.line < step.line)
                    .filter(|o| o.just.obtained.contains(&v))
                    .filter_map(|o| o.number.number().map(|n| n.to_string()));
                lets.chain(obtains)
                    .filter(|label| known.in_reach(label, step))
                    .last()
            });
            KindSaid {
                at: kind.at,
                letter: kind.letter,
                line,
            }
        })
        .collect()
}

/// What supplies each hypothesis of the group `taken` takes, in the group's
/// order (`Cited::supplied`): the fact the search took for it, placed among
/// the lines `refs` names, or among the step's requires lines the citation
/// reads: all of them for the step's own, those above it for a citation on
/// the line `below` (`Step::requires_above`). A hypothesis the search took
/// no fact for, one the citation's values make true, is placed where a line
/// states it at those values (`binding`) all the same, since a backend that
/// cannot work it out takes that line. A "there is" no line states whole is
/// supplied at the witnesses the search gave its letters (`bound`), each
/// with where its membership stands (`Supplied::witnesses`).
#[allow(clippy::too_many_arguments)]
pub(super) fn supplied_at(
    step: &Step,
    refs: &[String],
    item: Option<&str>,
    supplying: Vec<Supplying>,
    values: Values,
    below: Option<usize>,
    known: &Known,
    library: &Library,
) -> Vec<Supplied> {
    let Values { binding, bound } = values;
    let ctx = &library.ctx;
    let suppliers = Suppliers::new(step, refs, item, below, known, library);
    supplying
        .into_iter()
        .map(|Supplying { want, fact, at }| {
            // The hypothesis at the citation's values, where the fact the
            // search took is alike it: the search takes `1·(m + 1) ∈ ℕ₀` for
            // `m + 1 ∈ ℕ₀`, which `alike` reads the same, and what supplies
            // it is looked for as the citation writes it.
            let at_values = standard(&substitute_apart(&want, binding, ctx), ctx);
            let none = IndexMap::new();
            let fact = match fact {
                Some(f) if !alike(&f, &at_values, ctx, &none, &none) => f,
                _ => at_values,
            };
            let by = suppliers.by(&fact);
            // The hypothesis as the citation asks it, a property given read
            // as its body where it is applied (`filled`), as a conclusion's
            // meeting reads it, met with the line as the line writes it.
            let asked = filled(&want, binding, ctx);
            let narrowed = narrowed_of(&asked, &fact, ctx);
            let meeting = suppliers.meeting(&asked, &fact, &by, narrowed.as_ref());
            let witnesses = match (bound, &meeting) {
                (Some(bound), None) => {
                    witnesses_in(&want, &by, binding, bound, &suppliers)
                }
                _ => Vec::new(),
            };
            Supplied {
                meeting,
                narrowed,
                want,
                by,
                at,
                witnesses,
            }
        })
        .collect()
}

/// The values a citation supplies a hypothesis at, where it is a "there
/// is": what goes in `supplied_at`, the citation's values and, where a
/// "there is" was supplied, the witnesses (`Taken::bound`).
pub(super) struct Values<'b> {
    pub(super) binding: &'b Binding,
    /// The value the search gave each letter a hypothesis's "there is"
    /// binds; None where nothing supplied is a "there is" of the item's.
    pub(super) bound: Option<&'b Binding>,
}

/// Each letter of `want`'s "there is", outermost first, with its witness
/// in `bound` and where the witness's membership of the domain at the
/// values stands (`Supplied::witnesses`); empty for any other fact, or
/// where a letter has no witness. A "there is" with no body, "there is s ∈
/// S", has for its witness the member the line that supplies it, `by`,
/// says is in S, `a ∈ S`.
fn witnesses_in(
    want: &Node,
    by: &SuppliedBy,
    binding: &Binding,
    bound: &Binding,
    suppliers: &Suppliers,
) -> Vec<WitnessIn> {
    let library = suppliers.library;
    let ctx = &library.ctx;
    let mut at = binding.clone();
    let mut body = Some(want);
    let mut out = Vec::new();
    while let Some(node) = body.filter(|n| library.exists.contains(&n.notation())) {
        let (letter, domain, inner) = match node.children.as_slice() {
            [letter, domain, inner] => (letter, domain, Some(inner)),
            [letter, domain] => (letter, domain, None),
            _ => break,
        };
        let stated_member = || match by {
            SuppliedBy::Line(at) | SuppliedBy::SaidOnce(at) if inner.is_none() => {
                match (at.written.notation(), at.written.children.as_slice()) {
                    (MEMBERSHIP, [member, _]) => Some(member.clone()),
                    _ => None,
                }
            }
            _ => None,
        };
        // A bodiless "there is" takes the member its line states: the
        // search's `bound` also holds what a conclusion's own binder of the
        // same letter met, the s of "for all s ∈ S".
        let Some(value) = stated_member().or_else(|| bound.get(&letter.text).cloned())
        else {
            return Vec::new();
        };
        let domain = substitute_apart(domain, &at, ctx);
        let member = standard(
            &bound_in(Bound::Member, &value, &domain, library.env.g),
            ctx,
        );
        out.push(WitnessIn {
            letter: letter.text.to_string(),
            member: suppliers.by(&member),
            said: member,
            value: value.clone(),
        });
        at.insert(letter.text, value);
        body = inner;
    }
    out
}
