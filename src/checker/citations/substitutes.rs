//! Substitutions and obtained claims.

use std::iter;

use super::*;
use crate::checker::record::{FirstAt, Substituted, SubstitutedInto, TakenCase};
use crate::corpus::proof;
use crate::matching;
use crate::matching::{Flip, Meeting, SubstitutionPlaces};

/// A `substitute` claims the line it puts its equation into with one side
/// put for the other at some of the places it stands, or with no line to
/// put it into, `t = t′` where t′ is t so rewritten (`SYNTAX.md`). A line
/// of several sentences offers the whole and each of its parts, as the
/// elaborator offers them.
pub fn check_substitutes(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    // A requires line whose reason is `substitute` is the step it would be
    // (`requires_read_as_step`), and its substitution makes its fact or is
    // refused as a step's is.
    let read: Vec<Step> = thm
        .steps
        .iter()
        .flat_map(|step| {
            iter::once(step.clone()).chain(
                step.requires
                    .iter()
                    .filter_map(|req| requires_read_as_step(step, req)),
            )
        })
        .collect();
    for step in &read {
        if let Some(reading) = substitution_reading(step, thm, library, known) {
            for fault in reading.faults {
                report.say(&thm.path, step.just.line, fault);
            }
        }
    }
}

/// A `substitute` step read against its equation and what it is put into:
/// what is wrong with it, and how it makes its claim.
pub(super) struct SubstitutionReading {
    pub(super) faults: Vec<String>,
    /// How the substitution makes the claim as the page writes it; None
    /// where it is found only in the standard order, by the claim's other
    /// form, or not at all.
    pub(super) found: Option<Substituted>,
}

/// Something an equation may be put into, and what that must make.
pub(super) struct PutInto {
    /// What the equation is put into, as the page writes it.
    pub(super) start: Node,
    /// Where it stands; None for a fact of the line a backend is not told
    /// where to find.
    pub(super) into: Option<SubstitutedInto>,
}

/// The facts one put may start from, and what it must make: the claim, or
/// its other form (`rules::OTHER_FORMS`).
pub(super) struct PutWay {
    pub(super) starts: Vec<PutInto>,
    pub(super) aim: Node,
    /// Whether `aim` is the claim as the page writes it.
    pub(super) claimed: bool,
}

/// `check_substitutes` of one step; None for a step that is no
/// substitution, or one another check reports.
pub(super) fn substitution_reading(
    step: &Step,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> Option<SubstitutionReading> {
    // A justification matching no production has no reading, and
    // `check_justification_form` says so; what the substitution makes is
    // asked only of one that reads.
    let just = &step.just;
    if !just.head.is(Method::Substitute) || just.unproduced.is_some() {
        return None;
    }
    let fault = |message: String| {
        Some(SubstitutionReading {
            faults: vec![message],
            found: None,
        })
    };
    let claim = known.whole_as_written(&step.claim)?;
    let scope = known.scope(step);
    let defined = known.citing_step(step);
    let is_define = |r: &str| thm.defines.iter().any(|d| d.label == r);
    // The line the equation is taken from, as it says its facts. A define
    // of a name says its equation, as a link citing it reads it; a define of
    // a function is the elaborator's. A reference to nothing is
    // `check_references`'s to report.
    let source = just.source.as_ref().map(|s| s.named().to_string());
    let from_line = source
        .as_deref()
        .filter(|s| !is_define(s))
        .and_then(|s| scope.get(s).filter(|st| known.reads(st)).map(|st| (s, st)));
    let source_says: Vec<super::super::library::Said> = from_line
        .map(|(_, st)| known.says(st, &defined))
        .unwrap_or_default();
    let place_of = |s: &super::super::library::Said| {
        from_line.and_then(|(line, st)| {
            placed(line, s, &source_says, known.sentence_count(st))
        })
    };
    let source_define = source
        .as_deref()
        .filter(|s| is_define(s))
        .and_then(|s| super::super::formulas::define_equation(thm, step, s, known));
    // Each equation the step may put, with where its line says it.
    let equations: Vec<(Node, Option<FirstAt>)> = match &just.equation {
        Some(written) => {
            let equation = known.whole_as_written(written)?;
            let [left, right] = equation.children.as_slice() else {
                return None;
            };
            // An equation worked out where it stands, `(arithmetic)`, is a
            // fact of numerals `arithmetic` decides (`METHODS.md`,
            // arithmetic).
            if let Some(Source::Arithmetic) = &just.source {
                let worked = super::super::formulas::arithmetic_worked(
                    written,
                    known,
                    &library.targets,
                );
                if let super::super::formulas::Worked::Fails(why) = worked {
                    return fault(format!(
                        "step {} takes {} from arithmetic, which {why}",
                        step.number,
                        known.print(&equation)
                    ));
                }
            }
            // The equation is part of the line it is taken from (`SYNTAX.md`,
            // substitute), as that line writes it or turned, and of a define
            // of a name the name and what it names.
            let turned = equation.with_children(vec![right.clone(), left.clone()]);
            let says_it =
                |p: &Node| known.alike(p, &equation) || known.alike(p, &turned);
            let at = source_says.iter().find(|s| says_it(&s.written));
            let said = from_line.is_some() || source_define.is_some();
            let there = at.is_some() || source_define.as_ref().is_some_and(says_it);
            if let (true, false, Some(source)) = (said, there, &source) {
                return fault(format!(
                    "step {} takes {} from {source}, which does not say it",
                    step.number,
                    known.print(&equation)
                ));
            }
            vec![(equation, at.and_then(place_of))]
        }
        // `substitute line L` writes no equation (`skeleton::substitute`):
        // the equation is one the line says. A line saying no equation
        // gives nothing to put.
        None => {
            let source = source.as_ref()?;
            if from_line.is_none() && !is_define(source) {
                return None;
            }
            let equations: Vec<(Node, Option<FirstAt>)> = match is_define(source) {
                true => source_define.iter().map(|e| (e.clone(), None)).collect(),
                false => source_says
                    .iter()
                    .map(|s| (s.written.clone(), place_of(s)))
                    .collect(),
            };
            let equations: Vec<(Node, Option<FirstAt>)> = equations
                .into_iter()
                .filter(|(e, _)| {
                    known.ctx.equations.contains(&e.notation()) && e.children.len() == 2
                })
                .collect();
            if equations.is_empty() {
                return fault(format!(
                    "step {} substitutes {source}, which says no equation to put",
                    step.number
                ));
            }
            equations
        }
    };
    // What the equation is put into, and what that must make: the line
    // named, or one side of the claim, which is t = t′ either way round.
    let ways: Vec<PutWay> = match &just.into {
        Some(place) => {
            let into = place.named();
            // A define states no sentence for the equation to be put into:
            // the step that wants it written out writes it and cites the
            // define.
            if is_define(into) {
                return fault(format!(
                    "step {} puts its equation into {into}, which is a define and no line; a step citing {into} writes the line it gives",
                    step.number
                ));
            }
            // A reference to nothing is `check_references`'s to report.
            let stated = scope.get(into).filter(|s| known.reads(s))?;
            // Whatever the line says is what the equation may be put into
            // (`Known::says`): a part of it, an equation of a chain, a bound
            // of a range, and a part of a set said as `X ⊆ A` or as `X ∈ 𝒫A`
            // either way, as a reader puts X = ∅ into `let X ⊆ A` to make
            // X ⊆ ∅.
            let says = known.says(stated, &defined);
            let own = known.sentence_count(stated);
            let starts = || -> Vec<PutInto> {
                says.iter()
                    .map(|s| PutInto {
                        start: s.written.clone(),
                        into: placed(into, s, &says, own).map(SubstitutedInto::Line),
                    })
                    .collect()
            };
            // A claim in one of two forms is made by making the other
            // (`rules::OTHER_FORMS`), as a reader puts line HK = line XY into
            // Q ∉ line XY to make Q is not on line HK.
            let other = said_otherwise(&claim, known.env, &known.sorts);
            iter::once((claim.clone(), true))
                .chain(other.map(|o| (o, false)))
                .map(|(aim, claimed)| PutWay {
                    starts: starts(),
                    aim,
                    claimed,
                })
                .collect()
        }
        // With no line to put it into, the claim `t = t′`, where t′ is t
        // rewritten: it starts from either side and makes the other.
        None => match claim.children.as_slice() {
            [t, rewritten] if known.ctx.equations.contains(&claim.notation()) => {
                [(t, rewritten, 0), (rewritten, t, 1)]
                    .into_iter()
                    .map(|(start, aim, side)| PutWay {
                        starts: vec![PutInto {
                            start: start.clone(),
                            into: Some(SubstitutedInto::ClaimSide(side)),
                        }],
                        aim: aim.clone(),
                        claimed: true,
                    })
                    .collect()
            }
            _ => Vec::new(),
        },
    };
    // The first equation, way and start whose putting makes the aim, each
    // read in the standard order (`Known::substituted`).
    let made = equations.iter().find_map(|(equation, from)| {
        let [left, right] = equation.children.as_slice() else {
            return None;
        };
        ways.iter().find_map(|way| {
            way.starts
                .iter()
                .find(|s| known.substituted(&s.start, &way.aim, left, right))
                .map(|start| (equation, from, way, start))
        })
    });
    let Some((equation, from, way, start)) = made else {
        return fault(match &just.equation {
            Some(_) => format!(
                "step {} claims {}, which putting one side of {} for the other does not make",
                step.number,
                known.print(&claim),
                known.print(&equations[0].0)
            ),
            None => format!(
                "{} is not one side of an equation {} says put for the other",
                known.print(&claim),
                source.as_deref().unwrap_or_default()
            ),
        });
    };
    let [left, right] = equation.children.as_slice() else {
        return None;
    };
    // An identity element the putting makes and the claim leaves out is
    // dropped from a number, which a line says where the page does not say
    // it once.
    let facts = known.parts(step, library).facts.clone();
    let starts: Vec<Node> = way.starts.iter().map(|s| s.start.clone()).collect();
    let unsaid = substitution_unsaid(&starts, &way.aim, left, right, &facts, library);
    let faults: Vec<String> = unsaid
        .first()
        .map(|left| {
            format!(
                "step {} drops an identity element from what the substitution makes, and nothing says {} is a number; a requires line says it",
                step.number,
                known.print(left)
            )
        })
        .into_iter()
        .collect();
    // Where it is put, read as the page writes the trees: what a backend
    // puts the equation in at.
    // Where the putting makes the claim only as `Known::alike_how` meets the
    // two, an identity element it leaves dropped, `1·x` written `x`, or the
    // claim written turned round, `c ≡ b` of `b ≡ c`, or a listed set's
    // members in another order: the side put for at every place it stands,
    // and how what that makes meets the claim.
    let define_facing = source
        .as_deref()
        .filter(|s| is_define(s))
        .and_then(|s| define_facing(thm, s, equation, source_define.as_ref(), known));
    let line_facing = from
        .as_ref()
        .and_then(|at| facing_of(&at.written, equation, known));
    // A claim made by making its other form (`rules::OTHER_FORMS`), `Q ∉
    // line HK` for `Q is not on line HK`, is recorded with that form as what
    // the putting makes, which a backend that writes the two alike closes
    // the claim by; the meeting says the claim is respelt.
    let found = {
        let into = start.into.clone().unwrap_or(SubstitutedInto::Unplaced);
        put_found(&start.start, &way.aim, equation, library, known)
            .map(|(put, meeting)| match way.claimed {
                true => (put, meeting, start.start.clone()),
                false => (put, meeting.respelt(true), start.start.clone()),
            })
            .map(|(put, meeting, start)| Substituted {
                equation: equation.clone(),
                from: from.clone(),
                into: into.clone(),
                place_flips: place_flips(&start, &put, equation, known),
                equation_flips: from
                    .as_ref()
                    .and_then(|at| known.alike_how(equation, &at.written))
                    .map(|m| m.flips)
                    .unwrap_or_default(),
                start,
                put,
                meeting,
                made_other_form: !way.claimed,
                define_facing,
                line_facing,
            })
    };
    Some(SubstitutionReading { faults, found })
}

/// How each `substitute` step, calculation row and requires line makes its
/// claim (`record::Substituted`), as `check_substitutes` read it, by the line
/// of its justification; none for one with a fault, or whose substitution
/// is found only in the standard order or by the claim's other form.
pub fn substitutions(
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> IndexMap<usize, Substituted> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        // A row or link stands inside its step, whose requires lines say
        // what it rests on as the step's check reads them: a row dropping
        // `− 0` from F(x) − 0 rests on the step's `requires F(x) ∈ ℝ`.
        let rows = chain_reasons(&step.just, &thm.path)
            .into_iter()
            .filter_map(|req| {
                let by = req.by.as_ref().ok()?;
                Some(Step {
                    requires: step.requires.clone(),
                    ..reason_as_step(step, &req, by)
                })
            })
            .chain(
                step.requires
                    .iter()
                    .filter_map(|req| requires_read_as_step(step, req)),
            );
        for at in iter::once(step.clone()).chain(rows) {
            let Some(reading) = substitution_reading(&at, thm, library, known) else {
                continue;
            };
            if let (true, Some(found)) = (reading.faults.is_empty(), reading.found) {
                out.insert(at.just.line, found);
            }
        }
    }
    out
}

/// Of each `substitute` step, and each requires line whose reason is one,
/// that takes its equation from a define by cases, the case the equation
/// takes (`CheckedTheorem::define_cases`), as a step citing the define is read
/// (`formulas::case_of`); by the line of the step's justification.
pub fn substitute_cases(
    thm: &Theorem,
    library: &Library,
    known: &Known,
    substituted: &IndexMap<usize, Substituted>,
) -> IndexMap<usize, TakenCase> {
    let wrappers = super::super::formulas::wrappers(library.env);
    let mut out = IndexMap::new();
    for step in &thm.steps {
        let reasons = step
            .requires
            .iter()
            .filter_map(|req| requires_read_as_step(step, req));
        for at in iter::once(step.clone()).chain(reasons) {
            let Some(recorded) = substituted.get(&at.just.line) else {
                continue;
            };
            let Some(source) = at.just.source.as_ref().map(|s| s.named().to_string())
            else {
                continue;
            };
            if !thm.defines.iter().any(|d| d.label == source) {
                continue;
            }
            let parts = known.parts(&at, library);
            if let Some(taken) = super::super::formulas::case_of(
                &at,
                &recorded.equation,
                &parts.facts,
                &wrappers,
                library,
                known,
            ) {
                out.insert(at.just.line, taken);
            }
        }
    }
    out
}

/// Each substitution `substituted` records into a line's sentences together
/// whose claim has as many sentences, taken sentence by sentence
/// (`CheckedTheorem::substituted_sentences`): claim sentence k as the line's
/// sentence k with the equation put in, at the places found between the two
/// as the page writes them (`matching::substitution_places`), or at none
/// where the putting leaves the sentence as it is. None of a step where a
/// pair is neither.
pub fn sentence_substitutions(
    thm: &Theorem,
    known: &Known,
    substituted: &IndexMap<usize, Substituted>,
) -> IndexMap<(usize, usize), Substituted> {
    let mut out = IndexMap::new();
    for (line, s) in substituted {
        let SubstitutedInto::Line(at) = &s.into else {
            continue;
        };
        if at.sentence.is_some() || at.part.is_some() || at.implied.is_some() {
            continue;
        }
        let Some(step) = thm.steps.iter().find(|st| st.just.line == *line) else {
            continue;
        };
        let claims: Option<Vec<Node>> = step
            .claim
            .sentences()
            .iter()
            .map(|c| known.read_as_written(c))
            .collect();
        let Some(claims) = claims else {
            continue;
        };
        let scope = known.scope(step);
        let Some(stated) = scope.get(&at.line) else {
            continue;
        };
        let says = known.says(stated, &known.citing_step(step));
        let mut sentences: Vec<(usize, Node)> = says
            .iter()
            .filter_map(|said| match said.from {
                SaidFrom::Sentence(k) => Some((k, said.written.clone())),
                _ => None,
            })
            .collect();
        sentences.sort_by_key(|(k, _)| *k);
        if claims.len() < 2 || sentences.len() != claims.len() {
            continue;
        }
        let [left, right] = s.equation.children.as_slice() else {
            continue;
        };
        let mut each = Vec::new();
        for ((k, start), claim) in sentences.into_iter().zip(&claims) {
            let put = match start.spelt_alike(claim) {
                true => Some(SubstitutionPlaces {
                    turned: s.put.turned,
                    places: Vec::new(),
                }),
                false => matching::substitution_places(&start, claim, left, right),
            };
            let Some(put) = put else {
                each.clear();
                break;
            };
            each.push((
                (*line, k),
                Substituted {
                    equation: s.equation.clone(),
                    from: s.from.clone(),
                    into: SubstitutedInto::Line(FirstAt {
                        line: at.line.clone(),
                        sentence: Some(k),
                        part: None,
                        written: start.clone(),
                        implied: None,
                        pair: None,
                    }),
                    start,
                    put,
                    meeting: Meeting::default(),
                    made_other_form: false,
                    place_flips: Vec::new(),
                    equation_flips: s.equation_flips.clone(),
                    define_facing: s.define_facing,
                    line_facing: s.line_facing,
                },
            ));
        }
        out.extend(each);
    }
    out
}

/// Each row of a `substitute` step after the first, by its reason's line
/// (`CheckedTheorem::substituted_rows`): the change its reason proves, put
/// into the row above (`SubstitutedInto::RowAbove`) at the places the
/// change's left side stands where the row has its right.
pub fn row_substitutions(
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> IndexMap<usize, Substituted> {
    thm.steps
        .iter()
        .flat_map(|step| step_row_substitutions(step, thm, library, known))
        .collect()
}

/// Where an equation's one side is put for the other to make `aim` from
/// `start`, read as the page writes the trees (`matching::substitution_places`),
/// and how what that makes meets `aim`: as it stands, or, where the putting
/// makes the aim only as `Known::alike_how` meets the two, an identity
/// element it leaves dropped, `1·x` written `x`, the aim written turned
/// round, `c ≡ b` of `b ≡ c`, or a listed set's members in another order:
/// the side put for at every place it stands. A place the page writes in
/// another order of the parts of a notation that stands in no order, |BA|
/// for the side |AB|, is a place all the same; a backend turns it first.
pub(super) fn put_found(
    start: &Node,
    aim: &Node,
    equation: &Node,
    library: &Library,
    known: &Known,
) -> Option<(SubstitutionPlaces, Meeting)> {
    let [left, right] = equation.children.as_slice() else {
        return None;
    };
    matching::substitution_places(start, aim, left, right)
        .map(|put| (put, Meeting::default()))
        .or_else(|| {
            [(left, right, false), (right, left, true)]
                .into_iter()
                .find_map(|(was, now, turned)| {
                    let mut places = matching::places_of(start, was);
                    if places.is_empty() {
                        places = matching::places_alike(start, was, &library.ctx);
                    }
                    if places.is_empty() {
                        return None;
                    }
                    let made = matching::put_at_places(start, &places, now);
                    let met = known.alike_how(&made, aim)?;
                    Some((SubstitutionPlaces { turned, places }, met))
                })
        })
}

/// Each place of `put` in `start` that writes the side put for in another
/// order of a notation's parts, the side's term first.
pub(super) fn place_flips(
    start: &Node,
    put: &SubstitutionPlaces,
    equation: &Node,
    known: &Known,
) -> Vec<Flip> {
    let [left, right] = equation.children.as_slice() else {
        return Vec::new();
    };
    let was = match put.turned {
        true => right,
        false => left,
    };
    put.places
        .iter()
        .filter_map(|path| {
            let mut at = start;
            for &k in path {
                at = at.children.get(k)?;
            }
            known.alike_how(was, at)
        })
        .flat_map(|m| m.flips)
        .collect()
}

/// `row_substitutions` of one step, the places found by `put_found`.
pub(super) fn step_row_substitutions(
    step: &Step,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> Vec<(usize, Substituted)> {
    let Some(Ok(rows)) = proof::substitute_rows(&step.just, &thm.path) else {
        return Vec::new();
    };
    let read = |w: &Written| known.read_as_written(&w.formula().ok()?);
    rows.windows(2)
        .filter_map(|pair| {
            let (above, row) = (&pair[0], &pair[1]);
            let reason = row.reason.as_ref()?;
            let (start, aim, equation) = (
                read(&above.formula)?,
                read(&row.formula)?,
                read(&reason.fact)?,
            );
            let (put, meeting) = put_found(&start, &aim, &equation, library, known)?;
            Some((
                reason.line,
                Substituted {
                    place_flips: place_flips(&start, &put, &equation, known),
                    equation: equation.clone(),
                    from: None,
                    into: SubstitutedInto::RowAbove,
                    start,
                    put,
                    meeting,
                    made_other_form: false,
                    equation_flips: Vec::new(),
                    define_facing: None,
                    line_facing: None,
                },
            ))
        })
        .collect()
}

/// An obtain reaches a "there is" of the item it names.
///
/// What it claims is that existential's body, which `check_conclusion` does
/// not read. It does read the way there: a definition that gives one only
/// from a line saying n is odd, cited by an obtain that cites no such line,
/// has nothing to unfold.
pub fn check_obtained(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        let just = &step.just;
        let Some(item) = just.cited_item() else {
            continue;
        };
        if !just.head.is(Method::Obtain) {
            continue;
        }
        let Some(groups) = library.groups(&just.item(&item)) else {
            continue;
        };
        let parts = known.parts(step, library);
        // A hypothesis nothing supplies is `check_hypotheses`'s to name; the
        // way to the "there is" fails for it, and saying so again would
        // point at the line the step does cite.
        if !obtains(
            &groups,
            &parts.facts,
            &parts.claims,
            &just.obtained,
            &parts.seed,
            library,
        ) && unsupplied(step, known, library).is_none()
        {
            report.say(
                &thm.path,
                just.line,
                format!(
                    "step {} obtains from {item}, which says there is one only from something the step does not cite",
                    step.number
                ),
            );
        }
    }
}

/// What an obtain claims is the "there is" it obtains from, with its letters
/// the names obtained: a membership for each name, then the body
/// (`SYNTAX.md`). The "there is" is the line the step names, or what the
/// item it cites gives there. A definition that unfolds gives the existence
/// the step claims, which the elaborator reaches from the claim. The claim's
/// first sentences are the memberships, one for each name: one written
/// `x ∈ S` is compared with the "there is"'s, and one a notation spells its
/// own way (`f : X → Y`, `C ⊆ A`) is the elaborator's to read. The sentences
/// after them are the body, compared with its parts in any order. Each is
/// compared as one formula (`Known::alike`).
pub fn check_obtained_claims(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        if let Some(read) = obtained_reading(step, thm, library, known) {
            for (line, said) in read.faults {
                report.say(&thm.path, line, said);
            }
        }
    }
}

/// What the checker records of the obtain steps, each by the line of its
/// justification (`obtained_parts`).
pub struct Obtains {
    /// How each step's sentences after its memberships meet the parts of
    /// the "there is" it obtains from (`record::ObtainedPart`).
    pub parts: IndexMap<usize, Vec<ObtainedPart>>,
    /// Of a step that obtains from a line, where on it the "there is"
    /// stands: a sentence, a part of one, or a "for all" read at a block's
    /// letter (`CheckedTheorem::obtained_from`).
    pub from: IndexMap<usize, FirstAt>,
}

/// `Obtains` of each obtain step; no parts for a step whose sentences do
/// not meet the "there is" it obtains from.
pub fn obtained_parts(thm: &Theorem, library: &Library, known: &Known) -> Obtains {
    let mut out = Obtains {
        parts: IndexMap::new(),
        from: IndexMap::new(),
    };
    for step in &thm.steps {
        let just = &step.just;
        let from_line = just.head.is(Method::Obtain)
            && !just.obtained.is_empty()
            && just.cited_item().is_none();
        if from_line {
            if let Some(LineExistence::Found { at: Some(at), .. }) =
                line_existence(step, library, known)
            {
                out.from.insert(just.line, at);
            }
        }
        let Some(read) = obtained_reading(step, thm, library, known) else {
            continue;
        };
        if read.faults.is_empty() {
            out.parts.insert(just.line, read.parts);
        }
    }
    out
}

/// An obtain step read against the "there is" it obtains from: what is
/// wrong with its claim, by line, and how its sentences meet the parts.
pub(super) struct ObtainedReading {
    pub(super) faults: Vec<(usize, String)>,
    pub(super) parts: Vec<ObtainedPart>,
}

/// The "there is" an obtain that cites no item takes from the line it
/// names (`line_existence`).
enum LineExistence {
    /// The one the line says, and where on the line it stands; None where
    /// no one place on the line states it.
    Found { node: Node, at: Option<FirstAt> },
    /// Why the line states no one existence to obtain from.
    Fault(&'static str),
}

/// The line's one "there is" among what it says (`Known::says`): a
/// sentence, a part of one, or a "for all" read at a block's letter; or, of
/// a line of one sentence that says no "there is" in the notations read as
/// one, that sentence, which a part or a function said otherwise is, read
/// on. A fault where the line says none or several. None for a step that
/// names no line, or a line that does not read, which `check_formulas`
/// says.
fn line_existence(
    step: &Step,
    library: &Library,
    known: &Known,
) -> Option<LineExistence> {
    let just = &step.just;
    let stated = just
        .refs
        .first()
        .and_then(|r| known.scope(step).get(r).cloned())?;
    if !known.reads(&stated) {
        return None;
    }
    let defined = known.citing_step(step);
    let said = known.says(&stated, &defined);
    let existences: Vec<&Node> = said
        .iter()
        .map(|s| &s.cited)
        .filter(|s| library.ctx.existences.contains(&s.notation()))
        .collect();
    let sentences: Vec<&Node> = said
        .iter()
        .filter(|s| matches!(s.from, SaidFrom::Sentence(_)))
        .map(|s| &s.cited)
        .collect();
    let one = match (existences.as_slice(), sentences.as_slice()) {
        ([], [one]) | ([one], _) => *one,
        ([], _) => return Some(LineExistence::Fault("says no \"there is\"")),
        _ => {
            return Some(LineExistence::Fault(
                "says more than one \"there is\"; obtain from a line that says one",
            ))
        }
    };
    Some(LineExistence::Found {
        node: one.clone(),
        at: fact_at(step, &just.refs, None, one, known, library),
    })
}

/// `check_obtained_claims` of one step; None for a step that is no obtain,
/// or one another check reports or the elaborator reads.
pub(super) fn obtained_reading(
    step: &Step,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> Option<ObtainedReading> {
    let mut reading = ObtainedReading {
        faults: Vec::new(),
        parts: Vec::new(),
    };
    let just = &step.just;
    if !just.head.is(Method::Obtain) {
        return None;
    }
    if just.obtained.is_empty() {
        return None;
    }
    let names: Vec<&str> = just.obtained.iter().map(String::as_str).collect();
    let existence = match just.cited_item() {
        None => match line_existence(step, library, known)? {
            LineExistence::Found { node, .. } => Some(node),
            LineExistence::Fault(says) => {
                reading.faults.push((
                    just.line,
                    format!(
                        "step {} obtains {} from a line, which {says}",
                        step.number,
                        names.join(", ")
                    ),
                ));
                return Some(reading);
            }
        },
        Some(item) => {
            let name = just.item(&item);
            let groups = library.groups(&name)?;
            // A definition unfolded is its right side at the step's own
            // values: from `n is even ↔ there is k ∈ ℤ with n = 2k`,
            // `def:even n := P` obtains a k with P = 2k.
            if library.item(&name).is_some_and(|i| i.unfolds()) {
                let read = searched(step, Search::Obtains, known, library)?;
                let Built(taken) = &*read else {
                    return None;
                };
                let seed = &taken.binding;
                groups
                    .iter()
                    .flat_map(|g| &g.gives)
                    .filter(|g| g.notation() == BICONDITIONAL && g.children.len() == 2)
                    .map(|g| filled(&g.children[1], seed, &library.ctx))
                    .find(|right| exhibited(right, library).is_some())
            } else {
                let read = searched(step, Search::Obtains, known, library)?;
                let Built(taken) = &*read else {
                    return None; // `check_obtained` reports it
                };
                groups[taken.group]
                    .gives
                    .iter()
                    .map(|g| filled(g, &taken.binding, &library.ctx))
                    .find(|g| exhibited(g, library).is_some())
            }
        }
    };
    let existence = existence?;
    // The letters in the order the "there is" binds them, each the name
    // obtained in its place.
    let mut order: Vec<(&Node, &Node)> = Vec::new();
    let mut body = &existence;
    while order.len() < names.len() {
        let Some(last) = body.children.last() else {
            break;
        };
        let kids = &body.children;
        match body.notation() {
            THERE_IS if kids.len() == 3 => order.push((&kids[0], &kids[1])),
            _ => break,
        }
        body = last;
    }
    if order.len() != names.len() {
        // A line or an item that says no "there is" at all where one is
        // left to take has nothing to obtain; another spelling of one, a
        // part or a function, is the elaborator's to read.
        if !library.ctx.existences.contains(&body.notation()) {
            let from = just.cited_item().unwrap_or_else(|| "a line".to_string());
            reading.faults.push((
                    just.line,
                    format!(
                        "step {} obtains {} from {from}, which says no \"there is\" of as many",
                        step.number,
                        names.join(", ")
                    ),
                ));
            return Some(reading);
        }
        return None;
    }
    let mut put = Binding::new();
    for ((letter, _), name) in order.iter().zip(&names) {
        if letter.text != *name {
            let written = Written::new(*name, &thm.path, just.line);
            let Some(named) = written
                .formula()
                .ok()
                .and_then(|s| known.read_as_written(&s))
            else {
                continue;
            };
            put.insert(letter.text, named);
        }
    }
    let Some(said) = step
        .claim
        .sentences()
        .iter()
        .map(|s| known.read(step, s))
        .collect::<Option<Vec<Node>>>()
    else {
        return None; // `check_formulas` says it does not read
    };
    // A membership written `x ∈ S` is the one the "there is" gives, and
    // `X ⊆ A` is `X ∈ 𝒫A` written the other way; one its notation spells
    // otherwise, `f : X → Y`, is the elaborator's to read.
    for ((letter, domain), claimed) in order.iter().zip(&said) {
        let member = match (claimed.notation(), domain.notation()) {
            (SUBSET, POWERSET) if domain.children.len() == 1 => {
                bound_in(Bound::Part, letter, &domain.children[0], library.env.g)
            }
            _ => bound_in(Bound::Member, letter, domain, library.env.g),
        };
        let member = substitute_apart(&member, &put, &library.ctx);
        if claimed.notation() == member.notation() && !known.alike(claimed, &member) {
            reading.faults.push((
                step.line,
                format!(
                    "step {} claims {}, and what it obtains says {}",
                    step.number,
                    known.print(claimed),
                    known.print(&member)
                ),
            ));
        }
    }
    let owes: Vec<Node> = conjuncts(body, library)
        .iter()
        .map(|w| substitute_apart(w, &put, &library.ctx))
        .collect();
    // Each part of each sentence after the memberships, with its
    // sentence's place in the claim and its own in the sentence.
    let claimed: Vec<(usize, usize, Node)> = said
        .iter()
        .enumerate()
        .skip(names.len())
        .flat_map(|(s, c)| {
            conjuncts(c, library)
                .into_iter()
                .enumerate()
                .map(move |(p, part)| (s, p, part))
        })
        .collect();
    // Each part meets the first part of the "there is" left that it is
    // alike, the one in its own place first.
    let mut left: Vec<usize> = (0..owes.len()).collect();
    let mut all = true;
    for (k, (sentence, part, c)) in claimed.iter().enumerate() {
        let ahead = left.iter().position(|&o| o == k);
        let found = ahead
            .and_then(|at| Some((at, known.alike_how(c, &owes[k])?)))
            .or_else(|| {
                left.iter()
                    .enumerate()
                    .find_map(|(at, &o)| Some((at, known.alike_how(c, &owes[o])?)))
            });
        let Some((at, meeting)) = found else {
            all = false;
            break;
        };
        let owed = left.remove(at);
        reading.parts.push(ObtainedPart {
            sentence: *sentence,
            part: *part,
            owed,
            owed_written: owes[owed].clone(),
            meeting,
        });
    }
    if !all || !left.is_empty() {
        let says: Vec<String> = owes.iter().map(|o| known.print(o)).collect();
        reading.faults.push((
            step.line,
            format!(
                "step {} claims other than what it obtains, which says {}",
                step.number,
                says.join(". ")
            ),
        ));
    }
    Some(reading)
}
