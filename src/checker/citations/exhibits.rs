//! Exhibits, instantiations and the values they write.

use std::{iter, slice};

use super::*;
use crate::matching::Meeting;

/// An exhibit's lines say every part of its body at one value.
///
/// `exhibit, from L` claims a bare "there is", and the lines L state its
/// body with some value in place of the bound letter (`SYNTAX.md`). Each
/// part is stated, the value's membership of the domain among them: "there
/// is d ∈ ℤ with d > 1, d divides p" at d = 2 asks 2 ∈ ℤ and 2 > 1 as
/// surely as 2 divides p, since `READERS.md` writes a dull fact wherever
/// what a step rests on demands it, a numeral's included.
pub fn check_exhibited(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in thm.steps.iter().filter(|s| s.just.head.is(Method::Exhibit)) {
        check_exhibit(report, thm, step, library, known);
        check_exhibit_cites_used(report, thm, step, library, known);
    }
}

/// An exhibit uses each line it cites (`DATABASE.md`, a named thing doing
/// no work is an error): with the line taken away, what the exhibit needs
/// of its value is left unsaid. An exhibit that does not hold with all its
/// lines is reported by `check_exhibit`, and asked nothing here.
pub(super) fn check_exhibit_cites_used(
    report: &mut Report,
    thm: &Theorem,
    step: &Step,
    library: &Library,
    known: &Known,
) {
    let mut whole = Report::default();
    check_exhibit(&mut whole, thm, step, library, known);
    if !whole.problems.is_empty() {
        return;
    }
    let refs = &step.just.refs;
    let mut seen = BTreeSet::new();
    for r in refs.iter().filter(|r| seen.insert(r.as_str())) {
        let mut lighter = step.clone();
        lighter.just.refs = refs.iter().filter(|x| *x != r).cloned().collect();
        let mut scratch = Report::default();
        check_exhibit(&mut scratch, thm, &lighter, library, known);
        if scratch.problems.is_empty() && !shows_value(step, r, library, known) {
            report.say(
                &thm.path,
                step.just.line,
                format!("step {} cites {r} and uses nothing it says", step.number),
            );
        }
    }
}

/// Whether the line `r` an exhibit cites states a part of its body, short
/// of a letter's membership of its domain, at some value: the line shows
/// the reader the value (`SYNTAX.md`, `exhibit`: "the reader finds the
/// value by comparing"), as `p·q = p·q` shows n := q for "there is n ∈ ℕ
/// with p·q = p·n", though the equation would name its value itself.
pub(super) fn shows_value(
    step: &Step,
    r: &str,
    library: &Library,
    known: &Known,
) -> bool {
    let scope = known.scope(step);
    let Some(written) = scope.get(r) else {
        return false;
    };
    let said = known.supplied(written, &known.citing_step(step));
    let parts = known.read_out_parts(step, library);
    parts.claims.iter().any(|claim| {
        let Some(Exhibited { wants, letters }) = exhibited(claim, library) else {
            return false;
        };
        let mut sites = Sites::new();
        for t in &wants {
            binding_sites(t, &library.ctx, &[], &mut sites);
        }
        wants
            .iter()
            .filter(|w| {
                !(w.notation() == MEMBERSHIP
                    && w.children
                        .first()
                        .is_some_and(|t| letters.contains(t.text.as_str())))
            })
            .any(|w| {
                // The line itself says the part at the value, and not only
                // an equation true of itself there, n = n of q = n.
                supply(
                    slice::from_ref(w),
                    &said,
                    &Binding::new(),
                    &letters,
                    &Cite::plain(library),
                    &sites,
                    true,
                )
                .is_some_and(|at| {
                    let there = substitute_apart(w, &at, &library.ctx);
                    said.iter().any(|s| known.alike(s, &there))
                })
            })
    })
}

/// One exhibit's claim, a "there is", each part of it said of one value by
/// what the step cites or requires.
pub(super) fn check_exhibit(
    report: &mut Report,
    thm: &Theorem,
    step: &Step,
    library: &Library,
    known: &Known,
) {
    let parts = known.read_out_parts(step, library);
    let written: Vec<Node> = step
        .claim
        .sentences()
        .iter()
        .filter_map(|s| known.read_as_written(s))
        .collect();
    let facts = exhibit_facts(&parts.facts, library);
    for (claim, as_written) in parts.claims.iter().zip(&written) {
        // An exhibit claims a "there is" and shows a value for it
        // (`SYNTAX.md`, `exhibit`).
        let Some(ex) = exhibited(claim, library) else {
            if library.ctx.existences.contains(&claim.notation()) {
                continue;
            }
            report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} is an exhibit, and {} is no \"there is\" for it to give a value of",
                        step.number,
                        known.print(as_written)
                    ),
                );
            continue;
        };
        if shown_value(&ex, &facts, library, known).is_some() {
            continue;
        }
        let Some(at) = most_said_value(&ex, &facts, library, known) else {
            report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} exhibits a value, and nothing it cites or requires says the claim's body of any one value",
                        step.number
                    ),
                );
            continue;
        };
        let Exhibited { wants, letters } = ex;
        let shown = exhibited(as_written, library)
            .map(|e| e.wants)
            .filter(|w| w.len() == wants.len())
            .unwrap_or_else(|| wants.clone());
        let values: Vec<String> = letters
            .iter()
            .filter_map(|l| {
                at.get(l.as_str())
                    .map(|v| format!("{l} := {}", known.print(v)))
            })
            .collect();
        for (want, show) in wants.iter().zip(&shown) {
            if holds_at(want, &at, &facts, library, known) {
                continue;
            }
            report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} exhibits {}, so it needs {}, and nothing it cites or requires says it",
                        step.number,
                        values.join(", "),
                        known.print(&substitute_apart(show, &at, &library.ctx))
                    ),
                );
        }
    }
}

/// What an exhibit reads its values from: what the step cites and
/// requires, with the parts of each and the types said otherwise.
pub(super) fn exhibit_facts(cited: &[Node], library: &Library) -> Vec<Node> {
    let mut facts = with_parts(cited, library);
    let typed: Vec<Node> = facts
        .iter()
        .filter_map(|f| type_said_otherwise(f, library))
        .collect();
    facts.extend(typed);
    facts
}

/// Where each property in what an exhibit asks may decide what it stands
/// for (`binding_sites`).
pub(super) fn exhibit_sites(wants: &[Node], library: &Library) -> Sites {
    let mut sites = Sites::new();
    for t in wants {
        binding_sites(t, &library.ctx, &[], &mut sites);
    }
    sites
}

/// A term equals itself, which no line need write: gH = aH at a = g is
/// stated by nothing and needs nothing.
pub(super) fn equal_to_itself(w: &Node, known: &Known) -> bool {
    w.notation() == EQUALITY
        && w.children.len() == 2
        && known.alike(&w.children[0], &w.children[1])
}

/// The value an exhibit shows, each letter bound: one under which the facts
/// state every part of what it asks, or every part but the equations, each
/// of which is then a term equal to itself. None where no value is shown,
/// which `check_exhibit` reports.
pub(super) fn exhibit_value(
    ex: &Exhibited,
    facts: &[Node],
    library: &Library,
    known: &Known,
) -> Option<Binding> {
    let sites = exhibit_sites(&ex.wants, library);
    let stated = |wants: &[Node]| {
        supply(
            wants,
            facts,
            &Binding::new(),
            &ex.letters,
            &Cite::plain(library),
            &sites,
            true,
        )
    };
    let (equations, rest): (Vec<Node>, Vec<Node>) = ex
        .wants
        .iter()
        .cloned()
        .partition(|w| w.notation() == EQUALITY && w.children.len() == 2);
    stated(&ex.wants).or_else(|| {
        if equations.is_empty() {
            return None;
        }
        stated(&rest).filter(|at| {
            equations
                .iter()
                .all(|e| equal_to_itself(&substitute_apart(e, at, &library.ctx), known))
        })
    })
}

/// Whether a part `w` of what an exhibit asks holds at the value `at`: it is
/// then an equation of a term with itself, or a fact says it, alike but for
/// what goes without saying (`Known::alike`), as x = −(b + T)/3 says
/// x = −(b + 1·T)/3.
pub(super) fn holds_at(
    w: &Node,
    at: &Binding,
    facts: &[Node],
    library: &Library,
    known: &Known,
) -> bool {
    let w = substitute_apart(w, at, &library.ctx);
    equal_to_itself(&w, known) || facts.iter().any(|f| known.alike(f, &w))
}

/// The value the most parts of what an exhibit asks are said of, each
/// part's own line suggesting one, every letter bound; None where no part
/// suggests one.
pub(super) fn most_said_value(
    ex: &Exhibited,
    facts: &[Node],
    library: &Library,
    known: &Known,
) -> Option<Binding> {
    let Exhibited { wants, letters } = ex;
    let sites = exhibit_sites(wants, library);
    // A letter's bare membership, n ∈ ℕ, fits every number in ℕ, and
    // a numeral's membership is said once (`said_once`), so the value
    // it suggests is no reading of the claim: what the body says is
    // asked first, and wins where as many parts are said of each.
    let bare = |w: &Node| {
        w.notation() == MEMBERSHIP
            && w.children
                .first()
                .is_some_and(|t| letters.contains(t.text.as_str()))
    };
    let mut best: Option<(usize, Binding)> = None;
    for w in wants
        .iter()
        .filter(|w| !bare(w))
        .chain(wants.iter().filter(|w| bare(w)))
    {
        let Some(at) = supply(
            slice::from_ref(w),
            facts,
            &Binding::new(),
            letters,
            &Cite::plain(library),
            &sites,
            true,
        ) else {
            continue;
        };
        if !letters.iter().all(|l| at.contains_key(l.as_str())) {
            continue;
        }
        let count = wants
            .iter()
            .filter(|w| holds_at(w, &at, facts, library, known))
            .count();
        if best.as_ref().is_none_or(|(most, _)| count > *most) {
            best = Some((count, at));
        }
    }
    best.map(|(_, at)| at)
}

/// The value an exhibit shows, as `check_exhibit` accepts one: the value
/// `exhibit_value` reads, where the facts state each part, and otherwise
/// the value the most parts are said of where every part holds there
/// (`holds_at`). None where the exhibit shows no value.
pub(super) fn shown_value(
    ex: &Exhibited,
    facts: &[Node],
    library: &Library,
    known: &Known,
) -> Option<Binding> {
    exhibit_value(ex, facts, library, known).or_else(|| {
        most_said_value(ex, facts, library, known).filter(|at| {
            ex.wants
                .iter()
                .all(|w| holds_at(w, at, facts, library, known))
        })
    })
}

/// What each exhibit step shows, by the line of its justification: for each
/// sentence of its claim, the value each letter of its "there is" stands
/// for, as `check_exhibit` reads it, and where each fact it asks of them
/// stands among the lines the step names, its requires lines and the `let`
/// lines in scope (`supplied_at`); None for a sentence that is no "there
/// is" the step gives a value of. The build exhibits these values.
pub fn exhibit_values(
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> IndexMap<usize, Vec<Option<Exhibit>>> {
    thm.steps
        .iter()
        .filter(|s| s.just.head.is(Method::Exhibit))
        .map(|step| {
            let parts = known.read_out_parts(step, library);
            let facts = exhibit_facts(&parts.facts, library);
            let values = parts
                .claims
                .iter()
                .map(|claim| {
                    let ex = exhibited(claim, library)?;
                    let values = shown_value(&ex, &facts, library, known)?;
                    let asked =
                        ex.wants.iter().cloned().map(Supplying::sought).collect();
                    let shown = supplied_at(
                        step,
                        &step.just.refs,
                        None,
                        asked,
                        &values,
                        None,
                        known,
                        library,
                    );
                    Some(Exhibit { values, shown })
                })
                .collect();
            (step.just.line, values)
        })
        .collect()
}

/// What a "there is" asks of the value exhibited for it: each letter in its
/// domain, then each part of the body; and the letters.
pub(super) struct Exhibited {
    pub(super) wants: Vec<Node>,
    pub(super) letters: BTreeSet<String>,
}

pub(super) fn exhibited(claim: &Node, library: &Library) -> Option<Exhibited> {
    // The letters and their domains, then the body: a "there is" whose body
    // is a "there is" again, as "there are k, m, n ∈ ℕ with …" builds, binds
    // each letter in turn. "There is s ∈ S" binds its letter over nothing,
    // and asks only that the value is in S.
    let mut bound: Vec<(&Node, &Node)> = Vec::new();
    let mut body = Some(claim);
    while let Some(at) = body {
        match (at.notation(), at.children.as_slice()) {
            (THERE_IS, [letter, domain, inner]) => {
                bound.push((letter, domain));
                body = Some(inner);
            }
            (THERE_IS_SOME, [letter, domain]) => {
                bound.push((letter, domain));
                body = None;
            }
            _ => break,
        }
    }
    if bound.is_empty() {
        return None;
    }
    let mut wants: Vec<Node> = bound
        .iter()
        .map(|(letter, domain)| bound_in(Bound::Member, letter, domain, library.env.g))
        .collect();
    if let Some(body) = body {
        wants.extend(conjuncts(body, library));
    }
    let letters = bound.iter().map(|(l, _)| l.text.to_string()).collect();
    Some(Exhibited { wants, letters })
}

/// An instantiation's values are in the domains they are put in.
///
/// `instantiate v := t in line L, from L2`: line L says "for all v ∈ X, B",
/// and L2 supplies t ∈ X (`SYNTAX.md`), or a requires line does. A numeral
/// is no exception: `y := 1` in "for all x, y ∈ ℤ" asks 1 ∈ ℤ, written
/// `requires 1 ∈ ℤ: arithmetic`, as a cited item's hypothesis does.
pub fn check_instantiated(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        if !step.just.head.is(Method::Instantiate) {
            continue;
        }
        let Some(target) = step.just.target.clone() else {
            continue;
        };
        let Some(line) = known.scope(step).get(&target).cloned() else {
            continue;
        };
        let parts = known.read_out_parts(step, library);
        let written = values_written(step, known);
        let defined = known.citing_step(step);
        let mut said: Vec<(Option<Node>, Option<Node>)> = known
            .says(&line, &defined)
            .into_iter()
            .map(|s| (Some(s.cited), Some(s.written)))
            .collect();
        if !known.reads(&line) {
            said.push((None, None));
        }
        // What the values put in the domains need, each found among the
        // step's facts; unjudged where a domain is one `bound_in` does not
        // read, or a membership is missing and reported.
        let mut wants: Vec<Node> = Vec::new();
        let mut judged = true;
        for (read, as_written) in said {
            let (Some(read), Some(as_written)) = (read, as_written) else {
                judged = false;
                continue;
            };
            // The part instantiated is one the values fit, as
            // `check_instance_claimed` takes it: inside a block, a line
            // "for all a, for all x" also says "for all x" at the block's
            // letter, which the values for a and x do not fit.
            if fit_of(&read, &parts.seed) != Fit::Fits {
                continue;
            }
            // A cited line may meet a condition of the line as well, "if ε
            // > 0 then" in "for all ε > 0", which the elaborator judges.
            if read
                .walk()
                .iter()
                .any(|n| matches!(n.notation(), IMPLICATION | CONDITIONAL))
            {
                judged = false;
            }
            let binders = binders_of(&read);
            if !binders
                .iter()
                .any(|b| parts.seed.contains_key(&b.letter.text))
            {
                continue;
            }
            for m in
                value_memberships(&read, &as_written, &parts.seed, &written, library)
            {
                // A function's type is its membership of the functions
                // between its sets (`type_said_otherwise`), so `g : X → Y`
                // supplies g for "for all f : X → Y" (`SYNTAX.md`).
                let supplied = parts.facts.iter().any(|f| {
                    known.alike(f, &m.read)
                        || type_said_otherwise(f, library)
                            .is_some_and(|member| known.alike(&member, &m.read))
                });
                if supplied {
                    wants.push(m.read);
                    continue;
                }
                judged = false;
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} puts {} for {} in line {target}, so it needs {}, and nothing it cites or requires says it",
                        step.number,
                        known.print(&m.value),
                        m.letter,
                        known.print(&m.written)
                    ),
                );
            }
        }
        // A line the step cites supplies a value's membership of its domain
        // (`SYNTAX.md`, instantiate), so one whose absence leaves every
        // membership supplied supplies none: `instantiate x := x in H2, from
        // K2` where K2 lets x ∈ ℝ, which is said once.
        if !judged || wants.is_empty() {
            continue;
        }
        let defines: BTreeSet<&str> =
            thm.defines.iter().map(|d| d.label.as_str()).collect();
        for r in step
            .just
            .refs
            .iter()
            .filter(|r| **r != target && !defines.contains(r.as_str()))
        {
            let mut lighter = step.clone();
            lighter.just.refs.retain(|x| x != r);
            let left = known.read_out_parts(&lighter, library);
            if wants
                .iter()
                .all(|w| left.facts.iter().any(|f| known.alike(f, w)))
            {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} cites {r}, and no value it puts in line {target} needs what it says",
                        step.number
                    ),
                );
            }
        }
    }
}

/// The values `step` writes, each by the letter it is given to, as the page
/// writes them. A value that does not read is the elaborator's to report,
/// and is left out.
pub(super) fn values_written(step: &Step, known: &Known) -> IndexMap<String, Node> {
    step.just
        .values
        .read(known.env.g, &known.sorts)
        .unwrap_or_default()
        .into_iter()
        .map(|v| (v.name, v.value))
        .collect()
}

/// A value an instantiation puts in a domain of the sentence it reads, and
/// the membership that asks.
pub(super) struct ValueMembership {
    /// The letter of the sentence the value is given to.
    pub(super) letter: String,
    /// The value as the page writes it.
    pub(super) value: Node,
    /// The membership as it is compared, defined names written out.
    pub(super) read: Node,
    /// The membership as the page writes it.
    pub(super) written: Node,
}

/// The membership each value of `seed` asks of its domain in `read`, a
/// sentence of the line an instantiation names, outermost letter first.
/// `as_written` is the same sentence as the page writes it, and `written`
/// the values as the step writes them. A domain may name the letters bound
/// before it, and only those.
pub(super) fn value_memberships(
    read: &Node,
    as_written: &Node,
    seed: &Binding,
    written: &IndexMap<String, Node>,
    library: &Library,
) -> Vec<ValueMembership> {
    let mut outer = Binding::new();
    let mut outer_written = Binding::new();
    let mut out = Vec::new();
    for (b, w) in binders_of(read).iter().zip(binders_of(as_written)) {
        let Some(value) = seed.get(&b.letter.text) else {
            continue;
        };
        let domain = substitute_apart(&b.domain, &outer, &library.ctx);
        outer.insert(b.letter.text, value.clone());
        let value_written = written
            .get(b.letter.text.as_str())
            .cloned()
            .unwrap_or_else(|| value.clone());
        let domain_written = substitute_apart(&w.domain, &outer_written, &library.ctx);
        outer_written.insert(w.letter.text, value_written.clone());
        out.push(ValueMembership {
            // As the page writes it, which a reading may rename apart.
            letter: w.letter.text.to_string(),
            read: bound_in(b.how, value, &domain, library.env.g),
            written: bound_in(b.how, &value_written, &domain_written, library.env.g),
            value: value_written,
        });
    }
    out
}

/// `seed` with the letter of `read`'s binders it gives no value, whose
/// domain at the values before it is the set the claim's own "for all"
/// ranges over, `member` (`Known::step_member`), given the claim's letter:
/// "for all j ∈ {1, …, N}" at N := n, read in a claim "for all j ∈ {1, …,
/// n}", at j.
pub(super) fn at_claim_letter(
    read: &Node,
    seed: &Binding,
    member: Option<Node>,
    library: &Library,
) -> Binding {
    let mut out = seed.clone();
    let Some(member) = member else {
        return out;
    };
    let [letter, set] = member.children.as_slice() else {
        return out;
    };
    let none = IndexMap::new();
    for b in binders_of(read) {
        if out.contains_key(&b.letter.text) {
            continue;
        }
        let domain = substitute_apart(&b.domain, &out, &library.ctx);
        if alike(
            &standard(&domain, &library.ctx),
            &standard(set, &library.ctx),
            &library.ctx,
            &none,
            &none,
        ) {
            out.insert(b.letter.text, letter.clone());
        }
        break;
    }
    out
}

/// Where each value `step` puts in a domain of `said`, the sentence it
/// instantiates, is shown to be in it (`Instantiated::guards`): among the
/// lines the step names, its requires lines, or the `let` line that says
/// it once, as a citation's hypothesis is (`supplied_at`). A letter the
/// step gives no value is read at the letter of the claim's own "for all"
/// over its domain (`at_claim_letter`), whose membership the claim gives.
pub(super) fn value_guards(
    step: &Step,
    said: &super::super::library::Said,
    seed: &Binding,
    known: &Known,
    library: &Library,
) -> Vec<Guard> {
    let written = values_written(step, known);
    let seed = at_claim_letter(&said.cited, seed, known.step_member(step), library);
    value_memberships(&said.cited, &said.written, &seed, &written, library)
        .into_iter()
        .map(|m| {
            let by = supplied_at(
                step,
                &step.just.refs,
                None,
                vec![Supplying::sought(m.read)],
                &Binding::new(),
                None,
                known,
                library,
            )
            .pop()
            .map_or(SuppliedBy::Unstated, |s| s.by);
            Guard {
                letter: m.letter,
                written: m.written,
                by,
            }
        })
        .collect()
}

/// Where each condition an instantiation takes off, `conditions`, stands
/// (`Instantiated::conditions`): among the lines the step names, or its
/// requires lines, as a citation's hypothesis is (`supplied_at`).
pub(super) fn conditions_supplied(
    step: &Step,
    conditions: &[Node],
    known: &Known,
    library: &Library,
) -> Vec<Condition> {
    let supplying = conditions.iter().cloned().map(Supplying::sought).collect();
    supplied_at(
        step,
        &step.just.refs,
        None,
        supplying,
        &Binding::new(),
        None,
        known,
        library,
    )
    .into_iter()
    .map(|s| Condition {
        read: s.want,
        by: s.by,
    })
    .collect()
}

/// Whether `part` is an equation whose two sides are one term.
pub(super) fn sides_alike(part: &Node, known: &Known) -> bool {
    match part.children.as_slice() {
        [left, right] if known.ctx.equations.contains(&part.notation()) => {
            known.alike(left, right)
        }
        _ => false,
    }
}

/// One binder of a "for all": the letter, the domain, and how a value is
/// said to be in it, `x ∈ S`, or `x ⊆ S` for a part.
pub(super) struct Binder {
    pub(super) letter: Node,
    pub(super) domain: Node,
    pub(super) how: Bound,
}

/// An instantiation claims what its line says at the values it writes
/// (`SYNTAX.md`, instantiate): the "for all" of the line binding the names
/// it gives values, read at those values, and where what that says is an
/// implication, what it concludes, its conditions being the lines the step
/// cites. Compared as one formula (`Known::alike`), a claim of several
/// sentences as their conjunction.
pub fn check_instance_claimed(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        if let Some(read) = instance_reading(step, library, known) {
            for said in read.faults {
                report.say(&thm.path, step.just.line, said);
            }
        }
    }
}

/// How each instantiation's instance reaches its claim
/// (`record::Instantiated`), a step's, a calculation row's or a requires
/// line's, by the line of its justification; none for one whose instance
/// does not.
pub fn instantiations(
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> IndexMap<usize, Instantiated> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        let rows = chain_reasons(&step.just, &thm.path)
            .into_iter()
            .chain(step.requires.iter().cloned())
            .filter_map(|req| {
                let by = req.by.as_ref().ok()?;
                Some(reason_as_step(step, &req, by))
            });
        for at in iter::once(step.clone()).chain(rows) {
            let Some(read) = instance_reading(&at, library, known) else {
                continue;
            };
            if let (true, Some(found)) = (read.faults.is_empty(), read.found) {
                out.insert(at.just.line, found);
            }
        }
    }
    out
}

/// An `instantiate` step read against the line it names: what is wrong, and
/// the instance that reaches the claim.
pub(super) struct InstanceReading {
    pub(super) faults: Vec<String>,
    pub(super) found: Option<Instantiated>,
}

/// `check_instance_claimed` of one step; None for a step that is no
/// instantiation, or whose line or claim another check reports.
pub(super) fn instance_reading(
    step: &Step,
    library: &Library,
    known: &Known,
) -> Option<InstanceReading> {
    let mut reading = InstanceReading {
        faults: Vec::new(),
        found: None,
    };
    if !step.just.head.is(Method::Instantiate) {
        return None;
    }
    let target = step.just.target.clone()?;
    // A line or claim that does not read is another check's to report.
    let line = known.scope(step).get(&target).cloned()?;
    let claim = known.whole(step, &step.claim)?;
    {
        let named = known.read_out_parts(step, library);
        let seed = &named.seed;
        let defined = known.citing_step(step);
        let says = known.says(&line, &defined);
        let own = known.sentence_count(&line);
        let fits: Vec<Fit> =
            says.iter().map(|said| fit_of(&said.cited, seed)).collect();
        // The part instantiated is one the values fit: a part they leave
        // values over gives no instance, however its own letters fall.
        let instances: Vec<(&super::super::library::Said, Node)> = says
            .iter()
            .zip(&fits)
            .filter(|(_, fit)| **fit == Fit::Fits)
            .filter_map(|(said, _)| {
                Some((said, instance_at(&said.cited, seed, library)?))
            })
            .collect();
        if !fits.contains(&Fit::Fits) {
            let why = if fits.contains(&Fit::Skips) {
                "quantifies a name the step gives no value, before the ones it does"
            } else if fits.contains(&Fit::Over) {
                "quantifies fewer names than the step gives values"
            } else {
                "claims nothing of every such name"
            };
            reading.faults.push(format!(
                "step {} instantiates {target}, which {why}",
                step.number
            ));
            return Some(reading);
        }
        if instances.is_empty() {
            return None;
        }
        // The instance reaching the claim, and each condition met on the way
        // among what the step names; one it does not supply is said.
        let reached: Vec<(&super::super::library::Said, Vec<Node>, Meeting)> =
            instances
                .iter()
                .filter_map(|(said, i)| {
                    let (conditions, met) = concludes_claim(i, &claim, known)?;
                    Some((*said, conditions, met))
                })
                .collect();
        if let Some((said, conditions, meeting)) =
            reached.iter().min_by_key(|(_, c, _)| c.len())
        {
            reading.found = super::super::citations::placed(&target, said, &says, own)
                .map(|at| Instantiated {
                    at,
                    conditions: conditions_supplied(step, conditions, known, library),
                    meeting: meeting.clone(),
                    guards: value_guards(step, said, seed, known, library),
                });
            // A condition of several parts is met where each part is. An
            // equation whose two sides are then the same needs no line
            // (`SYNTAX.md`, an identity element goes without saying), as
            // k = a + b is at k := a + b.
            let unmet = conditions.iter().find(|c| {
                !conjuncts(c, library).iter().all(|part| {
                    sides_alike(part, known)
                        || named.facts.iter().any(|f| known.alike(f, part))
                })
            });
            if let Some(unmet) = unmet {
                reading.faults.push(format!(
                    "instantiating at that term wants {}, which step {} does not supply",
                    known.print(unmet),
                    step.number
                ));
            }
            return Some(reading);
        }
        // Said as the page writes the claim, not as it is compared.
        let written = known
            .whole_as_written(&step.claim)
            .map_or_else(|| step.claim_text(), |w| known.print(&w));
        reading.faults.push(format!(
            "{target} at those terms says {}, and the step claims {written}",
            known.print(&instances[0].1),
        ));
    }
    Some(reading)
}

/// What `said` says at the values `seed` gives the letters it binds, where
/// it is a "for all" binding at least one of them; None otherwise.
/// How an instantiation's values meet a sentence of the line it names
/// (`SYNTAX.md`, `instantiate`): the values are for the sentence's leading
/// "for all" letters, outermost first, each one given.
#[derive(PartialEq)]
pub(super) enum Fit {
    /// The values are for a run of its leading binders.
    Fits,
    /// A leading binder has no value before one that does.
    Skips,
    /// Values are left when its leading binders end.
    Over,
    /// No leading binder is one the values are for.
    Nothing,
}

/// How `seed`, the step's values by letter, meets the sentence `said`.
pub(super) fn fit_of(said: &Node, seed: &Binding) -> Fit {
    let mut body = said;
    let mut taken = 0;
    let mut skipped = false;
    loop {
        let (letter, inner) = match (body.notation(), body.children.as_slice()) {
            (FOR_ALL | FOR_ALL_PART, [letter, _, inner]) => (letter, inner),
            (FOR_ALL_SETS, [letter, inner]) => (letter, inner),
            _ => break,
        };
        if seed.contains_key(&letter.text) {
            if skipped {
                return Fit::Skips;
            }
            taken += 1;
        } else if taken > 0 {
            break;
        } else {
            skipped = true;
        }
        body = inner;
    }
    match taken {
        0 => Fit::Nothing,
        n if n < seed.len() => Fit::Over,
        _ => Fit::Fits,
    }
}

pub(super) fn instance_at(
    said: &Node,
    seed: &Binding,
    library: &Library,
) -> Option<Node> {
    let mut body = said.clone();
    let mut put = Binding::new();
    loop {
        // "for all x ∈ S, B" and "for all X ⊆ A, B" bind x over a set;
        // "for all sets X, B" binds X over every set.
        let (letter, inner) = match (body.notation(), body.children.as_slice()) {
            (FOR_ALL | FOR_ALL_PART, [letter, _, inner]) => (letter, inner),
            (FOR_ALL_SETS, [letter, inner]) => (letter, inner),
            _ => break,
        };
        let Some(value) = seed.get(&letter.text) else {
            break;
        };
        put.insert(letter.text, value.clone());
        body = inner.clone();
    }
    (!put.is_empty()).then(|| substitute_apart(&body, &put, &library.ctx))
}

/// The conditions an instance asks on its way to the claim: none where it
/// is the claim, and each implication's condition taken off until what is
/// left is; None where it never is.
pub(super) fn concludes_claim(
    instance: &Node,
    claim: &Node,
    known: &Known,
) -> Option<(Vec<Node>, Meeting)> {
    let mut at = instance.clone();
    let mut asked = Vec::new();
    loop {
        if let Some(met) = known.alike_how(&at, claim) {
            return Some((asked, met));
        }
        match (at.notation(), at.children.as_slice()) {
            (IMPLICATION | CONDITIONAL, [condition, then]) => {
                asked.push(condition.clone());
                at = then.clone();
            }
            _ => return None,
        }
    }
}

/// The binders a sentence opens with, outermost first.
pub(super) fn binders_of(node: &Node) -> Vec<Binder> {
    let mut out = Vec::new();
    let mut node = node.clone();
    loop {
        let how = match node.notation() {
            FOR_ALL => Bound::Member,
            FOR_ALL_PART => Bound::Part,
            _ => break,
        };
        if node.children.len() != 3 {
            break;
        }
        out.push(Binder {
            letter: node.children[0].clone(),
            domain: node.children[1].clone(),
            how,
        });
        node = node.children[2].clone();
    }
    out
}
