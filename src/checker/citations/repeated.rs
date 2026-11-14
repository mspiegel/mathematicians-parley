//! Repeated facts, lines given and what is surplus.

use super::*;

/// A requires line says something the step's other lines do not.
///
/// Every line does work (R3), and a fact the step already has does none:
/// `requires k ∈ ℝ: membership` under `requires k ∈ ℤ` says what k ∈ ℤ says
/// (`READERS.md`, what a membership line says). What the step has without
/// the line is the lines it cites, the requires lines above it, the lines
/// below it whose reason is a bare `from`, and what each of those implies.
/// Any other line below may rest on this one (R2): `2^p − 1 ∈ ℕ:
/// mun:prime-nat` below `2^p − 1 ∈ ℤ` implies it and needs it, where `m ∈
/// ℕ₀: from H3` rests on H3 alone. One line written twice is flagged where
/// it is written the second time. This holds on every step, whatever its
/// reason, so the checker and the elaborator need not each judge it.
///
/// What the step's own citations give is not in hand on a requires line
/// below, which sees only its own reason and the lines above it (R2). So a
/// line whose fact only the step's citations give is flagged only where no
/// line below needs it (`needed_below`), as the elaborator's R3 judges it.
pub fn check_repeated(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        for (i, req) in step.requires.iter().enumerate() {
            let Some(said) = known.whole(step, &req.fact) else {
                continue;
            };
            let mut lighter = step.clone();
            lighter.requires = step
                .requires
                .iter()
                .enumerate()
                .filter(|(j, o)| {
                    *j < i
                        || (*j > i
                            && o.is_lines()
                            && !same_fact(known, &o.fact, &req.fact))
                })
                .map(|(_, o)| o.clone())
                .collect();
            let says =
                |parts: &Parts| parts.facts.iter().any(|f| known.alike(f, &said));
            let mut uncited = lighter.clone();
            uncited.just.refs.clear();
            let bounded = bound_below(step, i, &said, known);
            let repeated = (says(&known.parts(&uncited, library)) && !bounded)
                || (says(&known.parts(&lighter, library))
                    && !bounded
                    && !needed_below(step, i, &said, known, library));
            if repeated {
                // A membership the page says once is said where its letters
                // are introduced, and the step's lines may say nothing.
                let why = match membership_said_once(&said, step, known) {
                    Some(named) if named.is_empty() => {
                        "which the page says once".to_string()
                    }
                    Some(named) => format!(
                        "which the page says once, where {} {} introduced",
                        named.join(" and "),
                        if named.len() == 1 { "is" } else { "are" }
                    ),
                    None => "which the step's other lines already say".to_string(),
                };
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of {} says {}, {why}",
                        step.called(),
                        str::trim(req.fact.text())
                    ),
                );
            }
        }
    }
}

/// Whether two requires lines state one fact, compared as formulas
/// (`Known::alike`). One that does not read states nothing another does,
/// and is `check_formulas`'s to report.
pub(super) fn same_fact(known: &Known, a: &Written, b: &Written) -> bool {
    match (known.whole_as_written(a), known.whole_as_written(b)) {
        (Some(a), Some(b)) => known.alike(&a, &b),
        _ => false,
    }
}

/// A requires line whose reason is only `from` uses each line it names.
///
/// Such a line reads its fact off the lines it names and the requires lines
/// above it (`ELABORATION.md`, R2), so a named line whose absence leaves the
/// fact read off is one it uses nothing of: `requires d(n) ∈ ℤ: from H1, K6`
/// where H1 says d : ℕ → ℤ and K6 lets n ∈ ℕ, which is said once. A fact is
/// read off where the facts say it, or say a function's type and a point of
/// its domain, a membership said once among them. The elaborator judges the
/// same by what the line's proof rests on (`Elaborator::does_work`).
pub fn check_from_lines(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    // The defines a line may name: the theorem's own, its file's and those
    // its file imports.
    let defines: BTreeSet<String> = crate::corpus::proof::in_scope(thm, scopes)
        .into_iter()
        .filter_map(|d| d.label)
        .collect();
    // A let's reason is read as a requires line of the step below it.
    // Its requires lines are the step's own, and are read there.
    let under = super::super::formulas::reasons_under_lets(thm, known);
    let lines = thm
        .steps
        .iter()
        .map(|s| (s, &s.requires[..]))
        .chain(under.iter().map(|u| {
            (
                &u.step,
                u.step.requires.last().map_or(&[][..], std::slice::from_ref),
            )
        }));
    for (step, reqs) in lines {
        for req in reqs.iter().filter(|r| r.is_lines()) {
            let read_off = |without: &[&str]| -> bool {
                let Some(parts) = requires_parts(step, req, without, known, library)
                else {
                    return false;
                };
                let mut facts = parts.facts.clone();
                facts.extend(function_values(&parts.facts, library.env, &known.sorts));
                parts
                    .claims
                    .iter()
                    .all(|c| facts.iter().any(|f| known.alike(f, c)))
            };
            // A fact the lines do not give is the line's defect: it claims
            // its lines supply what they do not. They give it where they say
            // it, or as the build proves the line from them alone
            // (`from_lines_give`, `ELABORATION.md`, R2): never from a type
            // in scope the line does not name. A define giving its function
            // on its domain is read apart, by `function_on_unshown`; any
            // other fact a line naming a define claims is read from its
            // lines, as the build reads it.
            let define_gives_function_on =
                req.lines().iter().any(|r| defines.contains(r.as_str()))
                    && claims_function_on(req, known);
            if !read_off(&[]) {
                if define_gives_function_on {
                    if let Some(why) = function_on_unshown(thm, req, known, scopes) {
                        report.say(
                            &thm.path,
                            req.line,
                            format!(
                                "{} does not give {}: {why}",
                                str::trim(&req.how),
                                str::trim(req.fact.text())
                            ),
                        );
                    }
                    continue;
                }
                let supplied =
                    requires_parts(step, req, &[], known, library).map(|parts| {
                        parts.claims.iter().all(|c| {
                            from_lines_give(
                                c,
                                &parts.facts,
                                step,
                                known,
                                library,
                                crate::methods::membership::holds,
                            )
                        })
                    });
                if supplied == Some(false) {
                    report.say(
                        &thm.path,
                        req.line,
                        format!(
                            "{} does not reach {}, which this line claims it supplies",
                            str::trim(&req.how),
                            str::trim(req.fact.text())
                        ),
                    );
                }
                if supplied != Some(true) {
                    continue;
                }
            }
            // Read off, or given as the build proves the line from its lines
            // (`from_lines_give`): d(k) ∈ ℝ from d : ℕ₀ → ℤ at a k said once.
            let gives = |without: &[&str]| -> bool {
                read_off(without)
                    || requires_parts(step, req, without, known, library).is_some_and(
                        |parts| {
                            parts.claims.iter().all(|c| {
                                from_lines_give(
                                    c,
                                    &parts.facts,
                                    step,
                                    known,
                                    library,
                                    crate::methods::membership::read_off,
                                )
                            })
                        },
                    )
            };
            let refs = req.lines();
            let spare: Vec<&str> = refs
                .iter()
                .map(String::as_str)
                .filter(|r| gives(&[r]))
                .collect();
            // Lines each spare alone that the fact needs one of say it twice,
            // which `check_repeated` and the elaborator judge.
            if spare.len() > 1 && !gives(&spare) {
                continue;
            }
            for r in spare {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of {} cites {r}, and {} needs nothing it says",
                        step.called(),
                        str::trim(req.fact.text())
                    ),
                );
            }
        }
    }
}

/// How a membership is decided from facts (`methods::membership`).
pub(super) type Member = fn(&Node, System, &crate::methods::membership::Facts) -> bool;

/// Whether the facts a bare `from` line reads give `claim` as the build
/// proves it from them (`ELABORATION.md`, R2), beside what they state and
/// supply: a membership the membership decider builds from them, a typed
/// function's value at a point of its domain among them; or an instance of
/// a "for all" among them, at a member the page says once is in its set, or
/// over a set inside its set (`SYNTAX.md`, a line said of every member).
/// Only the facts' own function types are offered, as the line rests on
/// its reason alone. `member` decides a membership: `holds` for whether
/// the lines reach the fact at all, as the build proves it, and `read_off`,
/// the page's rule, for whether a line among them is needed.
pub(super) fn from_lines_give(
    claim: &Node,
    facts: &[Node],
    step: &Step,
    known: &Known,
    library: &Library,
    member: Member,
) -> bool {
    let letters = super::super::library::introduced(known, step);
    if let (MEMBERSHIP, [term, set]) = (claim.notation(), claim.children.as_slice()) {
        if let Some(system) = (set.notation() == NUMBER_SYSTEMS)
            .then(|| System::of_sign(&set.text))
            .flatten()
        {
            let typed: Vec<Node> = facts
                .iter()
                .filter(|f| types_a_function(f))
                .cloned()
                .collect();
            let given = crate::methods::membership::Facts {
                facts,
                letters: letters.clone(),
                ranged: IndexMap::new(),
                typed: &typed,
                in_sums: &[],
                targets: &library.targets,
                ctx: known.ctx,
            };
            if member(term, system, &given) {
                return true;
            }
        }
    }
    facts.iter().any(|f| {
        let (FOR_ALL, [bound, over, body]) = (f.notation(), f.children.as_slice())
        else {
            return false;
        };
        if let (FOR_ALL, [letter, inner, said]) =
            (claim.notation(), claim.children.as_slice())
        {
            let put = Binding::from([(bound.text, letter.clone())]);
            return (known.alike(inner, over)
                || crate::citing::set_within(inner, over))
                && known.alike(&substitute_apart(body, &put, known.ctx), said);
        }
        // At a member: the claim is the body, or one part of it, there.
        let variables = BTreeSet::from([bound.text.to_string()]);
        conjuncts(body, library).iter().any(|part| {
            let Some(fit) = match_tree(
                part,
                claim,
                &Binding::new(),
                &variables,
                &IndexSet::new(),
                known.ctx,
            ) else {
                return false;
            };
            fit.get(&bound.text)
                .is_some_and(|member| member_in(member, over, &letters, step, known))
        })
    })
}

/// Where `fact` is a membership the page says once at `step` (`member_in`),
/// the letters of its term the page introduces, where it says so; None for
/// any other fact.
pub(in crate::checker) fn membership_said_once(
    fact: &Node,
    step: &Step,
    known: &Known,
) -> Option<Vec<String>> {
    let (MEMBERSHIP, [term, set]) = (fact.notation(), fact.children.as_slice()) else {
        return None;
    };
    let letters = super::super::library::introduced(known, step);
    member_in(term, set, &letters, step, known).then(|| {
        term.names()
            .into_iter()
            .filter(|n| letters.contains_key(n.as_str()))
            .collect()
    })
}

/// Whether `member` is in `set` as the page says it: by the membership it
/// says once, in a number system; or as the member of a step said of every
/// member of a set inside `set`, which its requires lines speak of
/// (`SYNTAX.md`, a step said of every member).
pub(super) fn member_in(
    member: &Node,
    set: &Node,
    letters: &crate::citing::Introduced,
    step: &Step,
    known: &Known,
) -> bool {
    let said_once = set.notation() == NUMBER_SYSTEMS
        && System::of_sign(&set.text).is_some_and(|system| {
            crate::citing::within(
                member,
                system,
                letters,
                &|d| crate::citing::nonzero_said_once(d, letters),
                &|_, _| false,
            )
        });
    if said_once {
        return true;
    }
    let Some(claimed) = known.step_member(step) else {
        return false;
    };
    matches!(
        (claimed.notation(), claimed.children.as_slice()),
        (MEMBERSHIP, [bound, over])
            if bound.is_name()
                && member.is_name()
                && bound.text == member.text
                && (known.alike(over, set) || crate::citing::set_within(over, set))
    )
}

/// Whether a cited line, as `stated` says it, does work the item's search
/// does not see: it states a function type the item asks for, or a sum's
/// term at every point (`asks`), or says a defined function is applied
/// inside its domain (`in_domain`, from `domains_asked`). A requires line
/// citing an item is the step it would be, so it is asked this as a step
/// is.
pub(super) fn does_other_work(
    stated: &[Node],
    asks: &FamilyAsks,
    in_domain: &FxIndexSet<ByShape>,
    known: &Known,
    library: &Library,
) -> bool {
    stated.iter().any(|part| {
        asks.states(part, known)
            || in_domain.contains(&part.by_shape())
            || asks.states_values(part, library)
    })
}

/// Whether the line `r` says a function's type, `H : [a, b] → ℝ`. A
/// citation of a function's value or of an item about a function names it
/// beside the function (`READERS.md`, a function's type cited for its
/// values). A point in a function's domain, `k ∈ {1, …, n}`, is asked about
/// as any other line is: the item's sets are the function's
/// (`citing::typed_seed`), so the search needs the line, and one cited for
/// what a range says once, k ∈ ℤ, is cited for nothing.
pub(super) fn in_a_domain(step: &Step, r: &str, known: &Known) -> bool {
    let scope = known.scope(step);
    let Some(stated) = scope.get(r) else {
        return false;
    };
    known.sentences(stated).iter().any(types_a_function)
}

/// Whether `lighter`, `step` with a line taken away, is no longer supplied.
/// Taking a line away leaves a step whose facts are some of `step`'s, so a
/// way that step could supply the item, by either route, is one of the ways
/// `step`'s do (`ways`, found the first time a line asks). Where no way they
/// supply it fits in what is left, the step without the line is not
/// supplied; the one search takes the place of a search for each line.
pub(super) fn fails_without(
    step: &Step,
    lighter: &Step,
    ways: &OnceCell<Option<Vec<Vec<Node>>>>,
    facts: &Parts,
    known: &Known,
    library: &Library,
) -> bool {
    let Some(ways) = ways.get_or_init(|| ways_supplied(step, known, library)) else {
        return false;
    };
    let left = known.parts(lighter, library);
    // What the argument rests on, asked rather than assumed: the facts left
    // are among these, and the claim and the seed are these, so the claim's
    // route is the one the ways were found by.
    within(&left.facts, &facts.facts)
        && lists_spelt_alike(&left.claims, &facts.claims)
        && lists_spelt_alike(
            &left.seed.values().cloned().collect::<Vec<_>>(),
            &facts.seed.values().cloned().collect::<Vec<_>>(),
        )
        && left.seed.keys().eq(facts.seed.keys())
        && !ways.iter().any(|way| within(way, &left.facts))
}

/// Whether a requires line below the step's `i`-th states a bound on the term
/// `said` puts in ℕ or ℕ₀, which that membership implies (`SYNTAX.md`, what a
/// membership line says) and the same membership said once does not
/// (`READERS.md`): `requires m·n ≥ 0` below `requires m·n ∈ ℕ`.
pub(super) fn bound_below(step: &Step, i: usize, said: &Node, known: &Known) -> bool {
    let [term, set] = said.children.as_slice() else {
        return false;
    };
    let system = rules::system_of(&set.text);
    if said.notation() != MEMBERSHIP || rules::implied(system).is_empty() {
        return false;
    }
    step.requires[i + 1..].iter().any(|o| {
        known.whole(step, &o.fact).is_some_and(|f| {
            matches!(f.notation(), ORDER | EQUALITY)
                && f.walk().iter().any(|n| known.alike(n, term))
        })
    })
}

/// Whether a requires line below the step's `i`-th rests on what it says,
/// `said`: one citing a record that asks for it (`citing::asked`), or one
/// whose method asks it of the terms the line names (`built_on`).
pub(super) fn needed_below(
    step: &Step,
    i: usize,
    said: &Node,
    known: &Known,
    library: &Library,
) -> bool {
    let req = &step.requires[i];
    if built_on(req, step, known) {
        return true;
    }
    step.requires[i + 1..].iter().any(|o| {
        let Some((named, _)) = o.cited_item() else {
            return false;
        };
        let Some(parts) = requires_parts(step, o, &[], known, library) else {
            return false;
        };
        match asked(&step.just.item(&named), &parts, library) {
            Built(asks) => asks.hypotheses.iter().any(|h| known.alike(h, said)),
            Declined(_) => false,
        }
    })
}

/// What an item citation names, it needs.
///
/// `DATABASE.md` holds that a named thing doing no work is an error, the
/// shape of a `metamath-proof` that never fires. For a step citing an item, the
/// item's statement says what is needed and the two checks above say
/// whether it is supplied; taking each named line away in turn and asking
/// them again says which lines supply it. One whose absence changes nothing
/// was supplying nothing. A requires line another one of the step leans on
/// is kept by the second check. A define is not asked about: citing one
/// names what a symbol means and supplies no fact.
pub fn check_surplus(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let defines: BTreeSet<&str> =
        thm.defines.iter().map(|d| d.label.as_str()).collect();
    let functions = defined_functions(&crate::corpus::proof::in_scope(thm, scopes));

    // A step holds where its item is supplied and concluded, and every
    // define it cites has its arguments in their domains: a line saying one
    // is in its domain does work as surely as one supplying a hypothesis.
    // `requires_concluded` says its requires lines' items are known to
    // conclude them: a requires line's parts are read from its own lines
    // and none the step cites, so a step that holds holds that still with a
    // cited line taken away.
    let holds_given = |step: &Step, requires_concluded: bool| -> bool {
        if unsupplied(step, known, library).is_some()
            || !map_types_unsaid(step, known, library).is_empty()
            || !map_domains_unsaid(step, known, library).is_empty()
            || (!requires_concluded && !unconcluded(step, known, library).is_empty())
            || !domains_unsaid(step, &functions, known, library).is_empty()
            || !unmet_codomains(
                step,
                &family_asks(step, known, library),
                &known.parts(step, library).facts,
                known,
            )
            .is_empty()
        {
            return false;
        }
        // What the step claims follows from what the item concludes and what
        // the step names: a definition read either way takes the other side
        // from a cited line, which asks for it as surely as a hypothesis
        // does.
        let found = |how| searched(step, how, known, library).map(|r| !r.is_declined());
        if step.just.head.is(Method::Obtain) {
            return found(Search::Obtains).unwrap_or(false);
        }
        let Some(takes) = found(Search::Takes) else {
            return false;
        };
        known.parts(step, library).claims.is_empty() || takes
    };
    let holds = |step: &Step| holds_given(step, false);

    for step in &thm.steps {
        // A requires line citing an item is the step it would be, whatever
        // its own step's reason, and what its reason names it needs as a
        // step's citation does: a line cited only for a membership said once
        // is cited for nothing there too.
        for req in &step.requires {
            // A reason citing an item is one the reader cut.
            let (Some((named, _)), Ok(by)) = (req.cited_item(), &req.by) else {
                continue;
            };
            let as_step = reason_as_step(step, req, by);
            if library.groups(&as_step.just.item(&named)).is_none() || !holds(&as_step)
            {
                continue;
            }
            let ways: OnceCell<Option<Vec<Vec<Node>>>> = OnceCell::new();
            let facts = known.parts(&as_step, library);
            let mut named_refs: IndexSet<&String> = IndexSet::new();
            named_refs.extend(as_step.just.refs.iter());
            let asks = family_asks(&as_step, known, library);
            let in_domain = domains_asked(thm, &as_step, scopes, known);
            let scope = known.scope(step);
            for r in named_refs {
                if defines.contains(r.as_str()) || in_a_domain(step, r, known) {
                    continue;
                }
                let stated: Vec<Node> = scope
                    .get(r)
                    .map(|s| known.writes_with_members(s, &known.citing_step(step)))
                    .unwrap_or_default();
                if does_other_work(&stated, &asks, &in_domain, known, library) {
                    continue;
                }
                let mut lighter = as_step.clone();
                lighter.just.refs = as_step
                    .just
                    .refs
                    .iter()
                    .filter(|x| *x != r)
                    .cloned()
                    .collect();
                if !fails_without(&as_step, &lighter, &ways, &facts, known, library)
                    && holds_given(&lighter, true)
                {
                    report.say(
                        &thm.path,
                        req.line,
                        format!(
                            "the requires line of {} cites {r}, and {named} asks for nothing it says",
                            step.called()
                        ),
                    );
                }
            }
        }
        let just = &step.just;
        let Some(item) = just.cited_item() else {
            continue;
        };
        if library.groups(&just.item(&item)).is_none() || !holds(step) {
            continue;
        }
        let mut refs: IndexSet<&String> = IndexSet::new();
        refs.extend(just.refs.iter());
        // The ways the step supplies its item, searched once and only if a
        // line asks (`fails_without`).
        let ways: OnceCell<Option<Vec<Vec<Node>>>> = OnceCell::new();
        let facts = known.parts(step, library);
        let lost_without = |lighter: &Step| {
            fails_without(step, lighter, &ways, &facts, known, library)
        };
        let asks = family_asks(step, known, library);
        let scope = known.scope(step);
        // Compared as formulas, so that `x∈ℤ` is `x ∈ ℤ`.
        let in_domain = domains_asked(thm, step, scopes, known);
        // Each line the step does without, taken away alone: a cited line,
        // and a requires line by its index.
        let mut spare_refs: Vec<&String> = Vec::new();
        let mut spare_requires: Vec<usize> = Vec::new();
        for r in refs {
            // A function's type is named beside the function where its value
            // is cited (`READERS.md`, a function's type is cited for its
            // values), as a requires line names it.
            if defines.contains(r.as_str()) || in_a_domain(step, r, known) {
                continue;
            }
            let stated: Vec<Node> = scope
                .get(r)
                .map(|s| known.writes_with_members(s, &known.citing_step(step)))
                .unwrap_or_default();
            if does_other_work(&stated, &asks, &in_domain, known, library) {
                continue;
            }
            let mut lighter = step.clone();
            lighter.just.refs = just.refs.iter().filter(|x| *x != r).cloned().collect();
            if !lost_without(&lighter) && holds_given(&lighter, true) {
                spare_refs.push(r);
            }
        }
        // What the step ends on by dropping an identity element asks to be
        // a number (`formulas::ends_asking`).
        let ends = super::super::formulas::ends_asking(thm, step, known, library, &[]);
        for (i, req) in step.requires.iter().enumerate() {
            let mut lighter = step.clone();
            lighter.requires.remove(i);
            let domain = known
                .whole_as_written(&req.fact)
                .is_some_and(|n| in_domain.contains(&n.by_shape()));
            let ended = known.whole_as_written(&req.fact).is_some_and(|n| {
                n.notation() == MEMBERSHIP
                    && ends.iter().any(|u| known.alike(&n.children[0], &u.left))
            });
            // What keeps a line without a search is asked before the search.
            if !asks.asks(step, &req.fact, known)
                && !domain
                && !ended
                && !built_on(req, step, known)
                && !lost_without(&lighter)
                && holds(&lighter)
            {
                spare_requires.push(i);
            }
        }
        // Lines that are each spare alone, and that the step cannot do
        // without all at once, say one hypothesis twice: the item asks for
        // what they say, and one of them is enough.
        let mut without_all = step.clone();
        without_all.just.refs.retain(|x| !spare_refs.contains(&x));
        without_all.requires = step
            .requires
            .iter()
            .enumerate()
            .filter(|(i, _)| !spare_requires.contains(i))
            .map(|(_, o)| o.clone())
            .collect();
        let twice = spare_refs.len() + spare_requires.len() > 1
            && (lost_without(&without_all) || !holds(&without_all));
        if twice {
            let mut named: Vec<String> =
                spare_refs.iter().map(|r| r.to_string()).collect();
            named.extend(spare_requires.iter().map(|&i| {
                format!(
                    "the requires line {}",
                    str::trim(step.requires[i].fact.text())
                )
            }));
            report.say(
                &thm.path,
                just.line,
                format!(
                    "step {} supplies one hypothesis of {item} twice, by {}; one of them is enough",
                    step.number,
                    named.join(" and ")
                ),
            );
            continue;
        }
        for r in spare_refs {
            report.say(
                &thm.path,
                just.line,
                format!(
                    "step {} cites {r}, and {item} asks for nothing it says",
                    step.number
                ),
            );
        }
        for i in spare_requires {
            let req = &step.requires[i];
            report.say(
                &thm.path,
                req.line,
                format!(
                    "the requires line of {} says {}, and neither {item} nor the {}'s other lines ask for it",
                    step.called(),
                    req.fact,
                    step.kind_word()
                ),
            );
        }
    }
}
