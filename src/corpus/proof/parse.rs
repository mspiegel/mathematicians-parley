//! Parsing a proof.

use super::*;
use crate::outcome::Declined;

/// The theorems of a proof file, and what the file holds outside them.
/// Structure comes from the step number; indentation is presentation and is
/// not consulted.
pub fn parse_proof(
    path: &str,
    text: &str,
    scope_id: ScopeId,
) -> Checked<(FileScope, Vec<Theorem>)> {
    let mut theorems: Vec<Theorem> = Vec::new();
    let mut scope = FileScope::new(path);
    let mut thm: Option<DraftTheorem> = None;
    // Whether the step being read still waits for its justification: the
    // index of the draft step in the theorem being read.
    let mut step: Option<usize> = None;
    let mut just_defined: Option<DefineLine> = None;
    // A let saying what kind of number its name is, whose reason is the
    // next line.
    let mut awaiting_reason: Option<DefineLine> = None;
    // What the file's citations name, settled at its first theorem: every
    // import comes before it.
    let mut names: Option<Arc<Names>> = None;
    // Between a theorem line and its statement a theorem may carry fields,
    // and a line there that opens no field continues the one above it.
    let mut header = false;
    let mut last_field: Option<(String, usize)> = None;
    // A part marker or a block opener appears before the sub-steps it governs,
    // so it is held until the next step arrives and is then attached to that
    // step's parent, which is the step that owns the block.
    // Each held marker, its line, and the note said under it.
    type Said = (String, usize);
    /// An opener held until the step it belongs to arrives.
    struct HeldOpener {
        kind: Intro,
        text: String,
        label: String,
        line: usize,
        /// It stands after its part's `by` line (`Opener::after_by`).
        after_by: bool,
    }
    /// A part's `by` line, held as its openers are.
    struct HeldBy {
        method: Method,
        line: usize,
    }
    let mut pending_markers: Vec<(String, usize, Option<Said>)> = Vec::new();
    let mut pending_openers: Vec<HeldOpener> = Vec::new();
    let mut pending_by: Option<HeldBy> = None;
    let mut part_no: IndexMap<StepPlace, usize> = IndexMap::new();
    let mut by_number: IndexMap<StepPlace, usize> = IndexMap::new();

    /// The first marker held, by its word and line.
    fn first_marker(held: &[(String, usize, Option<Said>)]) -> Option<(&str, usize)> {
        held.first().map(|(marker, at, _)| (marker.as_str(), *at))
    }

    /// The first opener held, by its label and line.
    fn first_opener(held: &[HeldOpener]) -> Option<(&str, usize)> {
        held.first().map(|o| (o.label.as_str(), o.line))
    }

    fn close_step(
        path: &str,
        thm: &Option<DraftTheorem>,
        step: &mut Option<usize>,
    ) -> Checked<()> {
        if let (Some(at), Some(t)) = (*step, thm.as_ref()) {
            let draft = &t.steps[at];
            if !draft.has_just {
                return Err(Problem::new(
                    path,
                    draft.step.line,
                    format!("step {} has no justification", draft.step.number),
                ));
            }
        }
        *step = None;
        Ok(())
    }

    /// Held markers and openers given to the step that owns their block,
    /// `owner`, numbered `parent`; what comes back is the part they open.
    #[allow(clippy::too_many_arguments)]
    fn attach(
        path: &str,
        draft: &mut DraftTheorem,
        owner: Option<usize>,
        parent: &StepPlace,
        markers: &mut Vec<(String, usize, Option<Said>)>,
        openers: &mut Vec<HeldOpener>,
        held_by: &mut Option<HeldBy>,
        part_no: &mut IndexMap<StepPlace, usize>,
    ) -> Checked<Option<usize>> {
        for (marker, no, note) in markers.drain(..) {
            let Some(owner) = owner else {
                return Err(Problem::new(
                    path,
                    no,
                    format!("part marker {} outside any block", repr(&marker)),
                ));
            };
            draft.steps[owner].step.parts.push((marker, no));
            let index = part_no.get(parent).map_or(0, |n| n + 1);
            part_no.insert(parent.clone(), index);
            if let Some(note) = note {
                draft.steps[owner].step.part_notes.insert(index, note);
            }
        }
        let current = part_no.get(parent).copied();
        if let Some(HeldBy { method, line }) = held_by.take() {
            let Some(owner) = owner else {
                return Err(Problem::new(path, line, "`by` line outside any block"));
            };
            let step = &draft.steps[owner].step;
            if step.just.head.is(Method::Contradiction) {
                return Err(Problem::new(
                    path,
                    line,
                    format!(
                        "{} is a contradiction, whose block owes no claim for `by` to prove",
                        step.called()
                    ),
                ));
            }
            if step.just.head.is(Method::Proof) && method == Method::Proof {
                return Err(Problem::new(
                    path,
                    line,
                    format!(
                        "the proof block of {} says `by proof`; its let and assume lines go on without it",
                        step.called()
                    ),
                ));
            }
            draft.steps[owner].step.by_lines.push(PartBy {
                part: current,
                method,
                line,
            });
        }
        for held in openers.drain(..) {
            let Some(owner) = owner else {
                return Err(Problem::new(
                    path,
                    held.line,
                    format!("{} line outside any block", held.kind),
                ));
            };
            let hypothesis_for = match skeleton::induction_hypothesis(&held.text) {
                Some(_) if held.after_by => {
                    return Err(Problem::new(
                        path,
                        held.line,
                        "the induction hypothesis comes before the part's `by` line",
                    ));
                }
                Some(said) => Some(induction_hypothesis(
                    path,
                    &draft.steps[owner].step,
                    &said,
                    held.line,
                )?),
                None => None,
            };
            draft.steps[owner].step.openers.push(Opener {
                kind: held.kind,
                text: held.text,
                label: held.label,
                line: held.line,
                part: current,
                is_claim: false,
                is_hypothesis: hypothesis_for.is_some(),
                hypothesis_for,
                after_by: held.after_by,
            });
        }
        Ok(current)
    }

    /// The letter `assume step N is true for k, the induction hypothesis`
    /// says it is for. N is the induction the line opens the step part of;
    /// that k is the letter N's claim binds, and the hypothesis N's
    /// statement at it, is read off the claim's tree by the tools.
    fn induction_hypothesis(
        path: &str,
        owner: &Step,
        said: &skeleton::InductionHypothesis,
        no: usize,
    ) -> Checked<String> {
        if !owner.just.head.is(Method::Induction) {
            return Err(Problem::new(
                path,
                no,
                "an induction hypothesis outside the step part of an induction",
            ));
        }
        // The theorem proved `by` the induction is its own step, and its
        // hypothesis says the theorem is true for k.
        match (said.step, owner.number.number()) {
            (Some(step), Some(number)) if step == fmt(number) => {}
            (None, None) => {}
            (Some(_), None) => {
                return Err(Problem::new(
                    path,
                    no,
                    format!(
                        "the theorem has no step {}; its induction hypothesis says `assume the theorem is true for {}, the induction hypothesis`",
                        said.step.unwrap_or_default(),
                        said.letter
                    ),
                ));
            }
            (named, Some(number)) => {
                return Err(Problem::new(
                    path,
                    no,
                    format!(
                        "the induction hypothesis names {}, and the induction is step {}",
                        named.map_or("the theorem".to_string(), |s| format!("step {s}")),
                        fmt(number)
                    ),
                ));
            }
        }
        Ok(said.letter.to_string())
    }

    /// A define after a theorem's last step is the file's, for the theorems
    /// below it: that theorem could never use it.
    fn settle(
        path: &str,
        thm: Option<DraftTheorem>,
        scope: &mut FileScope,
        theorems: &mut Vec<Theorem>,
    ) -> Checked<()> {
        let Some(mut draft) = thm else { return Ok(()) };
        let last = draft
            .steps
            .iter()
            .map(|s| s.step.line)
            .max()
            .unwrap_or(draft.thm.line);
        // A name the theorem gives is a let, and one below its last step is
        // the file's and a define (`SYNTAX.md`).
        for d in &draft.thm.defines {
            if d.reason.is_some() && d.line < draft.thm.conclusion_line {
                return Err(Problem::new(
                    path,
                    d.line,
                    "a let in a theorem's statement says no kind of number: the statement is what the theorem assumes, and a reason is a step of its proof",
                ));
            }
            let outside = d.line > last;
            match (naming(&d.text), outside) {
                (Some(Naming::Define), false) => {
                    return Err(Problem::new(
                        path,
                        d.line,
                        "a define inside a theorem: a name one theorem gives is a let, `let <name> = <term>`, and a define is the file's, outside the theorems",
                    ));
                }
                (Some(Naming::Let), true) => {
                    return Err(Problem::new(
                        path,
                        d.line,
                        "a let below a theorem's last step names a thing for the file, which a define does",
                    ));
                }
                _ => {}
            }
        }
        let moved: Vec<DefineLine> = draft
            .thm
            .defines
            .iter()
            .filter(|d| d.line > last)
            .cloned()
            .collect();
        for d in moved {
            draft.thm.defines.retain(|x| x != &d);
            if let Some(reading) = draft.thm.readings.shift_remove(&d.label) {
                scope.readings.insert(d.label.clone(), reading);
            }
            match define_parts(&d.text) {
                Built(DefineParts::Phrase(_)) => scope.phrases.push(d),
                _ => scope.defines.push(d),
            }
        }
        draft.thm.steps = draft
            .steps
            .into_iter()
            .map(|s| impossible(s.step))
            .collect();
        scope
            .theorems
            .insert(draft.thm.name.clone(), draft.thm.line);
        theorems.push(draft.thm);
        Ok(())
    }

    for line in read_lines(text) {
        let t = line.text.clone();
        // A `reads` line belongs to the define immediately above it, so what
        // a define leaves behind survives exactly one line.
        let previous = just_defined.take();
        if let Some(d) = awaiting_reason.take() {
            let head = t.split_whitespace().next().unwrap_or_default();
            if line.indent == 0
                || head == "reads"
                || skeleton::step_line(&t).is_some()
                || naming(&t).is_some()
            {
                return Err(Problem::new(
                    path,
                    d.line,
                    format!(
                        "let {} says what kind of number its name is, and the line under it gives no reason",
                        d.label
                    ),
                ));
            }
            let names = thm
                .as_ref()
                .map(|d| d.thm.names.clone())
                .unwrap_or_default();
            let reason = Reason {
                how: str::trim(&t).to_string(),
                line: line.no,
                by: cut_reason(&t, path, line.no)
                    .map(|slots| Justification::of(slots, line.no, &names)),
                requires: Vec::new(),
            };
            if let Some(draft) = thm.as_mut() {
                for written in draft.thm.defines.iter_mut().filter(|x| x.line == d.line)
                {
                    written.reason = Some(reason.clone());
                }
            }
            just_defined = Some(DefineLine {
                reason: Some(reason),
                ..d
            });
            continue;
        }
        let opened = theorem_header(&t).filter(|_| line.indent == 0);
        if let Some(TheoremHeader { mundane, name }) = opened {
            close_step(path, &thm, &mut step)?;
            held_at_end(
                path,
                first_marker(&pending_markers),
                first_opener(&pending_openers),
                pending_by.as_ref().map(|b| b.line),
            )?;
            settle(path, thm.take(), &mut scope, &mut theorems)?;
            let name = str::trim(name).to_string();
            if !skeleton::is_name(&name) {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!("theorem name {} is malformed", repr(&name)),
                ));
            }
            if mundane && !in_stdlib(module_of(path)) {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!(
                        "mundane theorem {name}: only a theorem of the standard library is taken for granted; a proof elsewhere states `theorem {name}`"
                    ),
                ));
            }
            thm = Some(DraftTheorem {
                thm: Theorem {
                    name,
                    mundane,
                    hypotheses: Vec::new(),
                    ranges: Vec::new(),
                    conclusion: String::new(),
                    conclusion_line: 0,
                    defines: Vec::new(),
                    readings: IndexMap::new(),
                    steps: Vec::new(),
                    line: line.no,
                    path: path.to_string(),
                    fields: IndexMap::new(),
                    scope: scope_id,
                    names: names.get_or_insert_with(|| Arc::new(scope.names())).clone(),
                },
                steps: Vec::new(),
            });
            pending_markers.clear();
            pending_openers.clear();
            pending_by = None;
            part_no.clear();
            by_number.clear();
            header = true;
            last_field = None;
            continue;
        }
        let Some(draft) = thm.as_mut() else {
            if t.starts_with("import ") {
                if !scope.defines.is_empty() || !scope.phrases.is_empty() {
                    return Err(Problem::new(
                        path,
                        line.no,
                        "an import below a define; imports come first",
                    ));
                }
                if !scope.forbids.is_empty() {
                    return Err(Problem::new(
                        path,
                        line.no,
                        "an import below a forbid; imports come first, and the forbids after them",
                    ));
                }
                match importing(path, line.no, &t)? {
                    Imported::Item(import) => scope.items.push(import),
                    Imported::Define(import) => scope.imports.push(import),
                }
                continue;
            }
            if t.split_whitespace().next() == Some("forbid") {
                if !scope.defines.is_empty() || !scope.phrases.is_empty() {
                    return Err(Problem::new(
                        path,
                        line.no,
                        "a forbid below a define; the forbids follow the imports, before any define",
                    ));
                }
                scope.forbids.push(forbidding(path, line.no, &t)?);
                continue;
            }
            // A define before any theorem is the file's, for every theorem; a
            // let names a thing within one theorem, and none is open here.
            if naming(&t) == Some(Naming::Let) {
                return Err(Problem::new(
                    path,
                    line.no,
                    "a let names a thing within a theorem; a name the whole file gives, and another may import, is a define",
                ));
            }
            if naming(&t) == Some(Naming::Define) {
                let Some(label) = label_at_end(&t) else {
                    return Err(Problem::new(
                        path,
                        line.no,
                        "define line carries no label",
                    ));
                };
                let d = DefineLine {
                    text: t.clone(),
                    label,
                    path: path.to_string(),
                    line: line.no,
                    reason: None,
                };
                match define_parts(&t) {
                    Declined(d) => {
                        return Err(d.into_problem(path, line.no));
                    }
                    Built(DefineParts::Recursion(_)) => {
                        return Err(Problem::new(
                            path,
                            line.no,
                            "a define by recursion is written in the theorem that uses it, in its statement or its proof",
                        ));
                    }
                    Built(DefineParts::Phrase(_)) => scope.phrases.push(d.clone()),
                    Built(DefineParts::One(_)) => scope.defines.push(d.clone()),
                }
                just_defined = Some(d);
                continue;
            }
            if let (Some(rest), Some(d)) = (t.strip_prefix("reads"), &previous) {
                scope
                    .readings
                    .insert(d.label.clone(), (str::trim(rest).to_string(), line.no));
                continue;
            }
            return Err(Problem::new(
                path,
                line.no,
                "text before any theorem header that is neither an import nor a define",
            ));
        };

        let head = t.split_whitespace().next().unwrap_or_default().to_string();
        if header && THEOREM_FIELDS.contains(&head.as_str()) {
            if draft.thm.fields.contains_key(&head) {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!("theorem {} says {head} twice", draft.thm.name),
                ));
            }
            draft
                .thm
                .fields
                .insert(head.clone(), str::trim(&t[head.len()..]).to_string());
            last_field = Some((head, line.indent));
            continue;
        }
        if header {
            if let Some((field, indent)) = &last_field {
                if line.indent > *indent {
                    let value = draft.thm.fields.get_mut(field).unwrap();
                    value.push(' ');
                    value.push_str(&t);
                    continue;
                }
            }
        }
        header = false;

        if let Some(said) = skeleton::step_line(&t) {
            close_step(path, &thm, &mut step)?;
            let draft = thm.as_mut().unwrap();
            // `step_line` reads digits only, so the one number it gives that
            // does not read is one too large to count.
            let Some(number) = StepNo::parse(said.number) else {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!("step {} has a number too large to read", said.number),
                ));
            };
            // Resolve held markers and openers against the owner of the block
            // that this step sits in, and say which part it sits in.
            let parent = number.parent();
            let owner = by_number.get(&parent).copied();
            // A `case` held for a step whose block takes no cases is the last
            // case of the `cases` block open above, which has no steps: one
            // with none says it is the claim (`SYNTAX.md`).
            let cases_owner =
                |i: usize| draft.steps[i].step.just.head.is(Method::Cases);
            if let Some((_, at, _)) =
                pending_markers.iter().find(|(m, _, _)| m == "case")
            {
                if !owner.is_some_and(cases_owner) {
                    let last = draft.steps.last().map(|s| s.step.number.clone());
                    // The theorem proved `by cases` is the block of the
                    // theorem's own step.
                    let open = last.and_then(|n| {
                        (0..=n.depth()).rev().map(|k| n.prefix(k)).find_map(|p| {
                            by_number.get(&p).copied().filter(|&i| cases_owner(i))
                        })
                    });
                    if let Some(open) = open {
                        return Err(Problem::new(
                            path,
                            *at,
                            format!(
                                "this case of {} has no steps, and its assumption does not say it is the claim; write its steps, or end the line `, which is the claim`",
                                draft.steps[open].step.called()
                            ),
                        ));
                    }
                }
            }
            let current = attach(
                path,
                draft,
                owner,
                &parent,
                &mut pending_markers,
                &mut pending_openers,
                &mut pending_by,
                &mut part_no,
            )?;
            draft.steps.push(DraftStep {
                step: Step {
                    number: StepPlace::Step(number.clone()),
                    claim: Written::new(said.claim, path, line.no),
                    just: placeholder_justification(),
                    requires: Vec::new(),
                    parts: Vec::new(),
                    openers: Vec::new(),
                    line: line.no,
                    part: current,
                    note: None,
                    part_notes: IndexMap::new(),
                    by_lines: Vec::new(),
                    impossible: false,
                    reason_of: None,
                },
                has_just: false,
            });
            let at = draft.steps.len() - 1;
            by_number.insert(StepPlace::Step(number), at);
            step = Some(at);
            continue;
        }

        // `by <method>` under `then`: the theorem is the step the method
        // proves, at `StepPlace::Theorem`, and the method's blocks open at
        // the top level, its steps numbered 1, 2, … (`SYNTAX.md`, a theorem
        // proved by a method). A line opening with `by` that continues a
        // step's claim is the claim's.
        let continues_claim = step.is_some_and(|at| !draft.steps[at].has_just);
        if head == "by" && !continues_claim {
            let said = str::trim(&t["by".len()..]);
            let labels = justification_labels(&scope, &draft.thm);
            let written = Line {
                no: line.no,
                text: said.to_string(),
                indent: line.indent,
            };
            // A `by` under a part's marker or openers, before its first
            // step, names the method of the part's own block (`PartBy`).
            let held = !pending_markers.is_empty()
                || !pending_openers.is_empty()
                || pending_by.is_some();
            if held {
                if pending_by.is_some() {
                    return Err(Problem::new(
                        path,
                        line.no,
                        "a part says `by` once, after its openers and before its first step",
                    ));
                }
                let just =
                    parse_justification(path, &written, &labels, &draft.thm.names)?;
                let method = just
                    .head
                    .method()
                    .filter(|m| matches!(m, Method::Proof | Method::Contradiction));
                let word = said.split(',').next().unwrap_or(said);
                let Some(method) = method else {
                    let parts = just.head.method().is_some_and(|m| {
                        matches!(
                            m,
                            Method::Cases | Method::Induction | Method::BothDirections
                        )
                    });
                    let opens = if parts {
                        "opens parts"
                    } else {
                        "proves a step"
                    };
                    return Err(Problem::new(
                        path,
                        line.no,
                        format!(
                            "`by` inside a block names proof or contradiction, whose blocks open with lines; {word} {opens}"
                        ),
                    ));
                };
                if !just.refs.is_empty() {
                    return Err(Problem::new(
                        path,
                        line.no,
                        format!("`by` inside a block names its method alone; {word} cites nothing here"),
                    ));
                }
                pending_by = Some(HeldBy {
                    method,
                    line: line.no,
                });
                continue;
            }
            if draft.steps.last().is_some_and(|s| !s.step.proves_theorem()) {
                return Err(Problem::new(
                    path,
                    line.no,
                    "`by` in a block comes after its part's openers, before its first step",
                ));
            }
            if !draft.steps.is_empty() || draft.thm.conclusion.is_empty() {
                return Err(Problem::new(
                    path,
                    line.no,
                    "`by` comes once, under `then`, before the proof",
                ));
            }
            let just = parse_justification(path, &written, &labels, &draft.thm.names)?;
            const BLOCKS: [Method; 5] = [
                Method::BothDirections,
                Method::Contradiction,
                Method::Proof,
                Method::Induction,
                Method::Cases,
            ];
            if !BLOCKS.iter().any(|&m| just.head.is(m)) {
                let word = said.split(',').next().unwrap_or(said);
                return Err(Problem::new(
                    path,
                    line.no,
                    format!(
                        "`by` names a method that opens a block: both directions, contradiction, proof, induction or cases; {word} proves a step"
                    ),
                ));
            }
            let conclusion = draft.thm.conclusion.clone();
            draft.steps.push(DraftStep {
                step: Step {
                    number: StepPlace::Theorem,
                    claim: Written::new(&conclusion, path, draft.thm.conclusion_line),
                    just,
                    requires: Vec::new(),
                    parts: Vec::new(),
                    openers: Vec::new(),
                    line: line.no,
                    part: None,
                    note: None,
                    part_notes: IndexMap::new(),
                    by_lines: Vec::new(),
                    impossible: false,
                    reason_of: None,
                },
                has_just: true,
            });
            let at = draft.steps.len() - 1;
            by_number.insert(StepPlace::Theorem, at);
            step = Some(at);
            continue;
        }

        if step.is_none() {
            if let Some(range) = Range::read(&t, line.no) {
                draft.thm.ranges.push(range);
                continue;
            }
        }
        // A naming line, read before a `let` that takes a member, which it
        // also opens with. Which word it may open with is settled once the
        // theorem's last step is known (`settle`).
        if naming(&t).is_some() {
            let Some(label) = label_at_end(&t) else {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!("{} line carries no label", head),
                ));
            };
            let says_kind = match define_parts(&t) {
                Declined(d) => return Err(d.into_problem(path, line.no)),
                Built(parts) => parts.one().is_some_and(|one| one.kind.is_some()),
            };
            // A define names an object and is in scope from where it stands on.
            let d = DefineLine {
                text: t.clone(),
                label,
                path: path.to_string(),
                line: line.no,
                reason: None,
            };
            draft.thm.defines.push(d.clone());
            if says_kind {
                awaiting_reason = Some(d);
            } else {
                just_defined = Some(d);
            }
            continue;
        }
        let intro = Intro::parse(&head);
        if matches!(intro, Some(Intro::Let | Intro::Assume)) && step.is_none() {
            draft.thm.hypotheses.push(Hypothesis {
                kind: intro.unwrap(),
                text: t.clone(),
                label: label_at_end(&t),
                line: line.no,
            });
            continue;
        }
        if head == "then" && step.is_none() {
            draft.thm.conclusion = str::trim(&t["then".len()..]).to_string();
            draft.thm.conclusion_line = line.no;
            continue;
        }
        if head == "reads" {
            let Some(d) = &previous else {
                return Err(Problem::new(
                    path,
                    line.no,
                    "reads line that does not follow a define",
                ));
            };
            draft.thm.readings.insert(
                d.label.clone(),
                (str::trim(&t["reads".len()..]).to_string(), line.no),
            );
            continue;
        }
        if head == "note" {
            let said = (str::trim(&t["note".len()..]).to_string(), line.no);
            // Under a part marker, the note says what that part does; the
            // marker is still held, because the step owning it is found only
            // when the part's first step arrives.
            if let Some((marker, _no, held)) = pending_markers.last_mut() {
                if held.is_some() {
                    return Err(Problem::new(
                        path,
                        line.no,
                        format!("the {} part already carries a note", repr(marker)),
                    ));
                }
                if !pending_openers.is_empty() {
                    return Err(Problem::new(
                        path,
                        line.no,
                        format!(
                            "a note on the {} part goes directly under its marker, before its openers",
                            repr(marker)
                        ),
                    ));
                }
                *held = Some(said);
                continue;
            }
            match step {
                Some(at) if draft.steps[at].has_just => {
                    draft.steps[at].step.note = Some(said);
                }
                _ => {
                    return Err(Problem::new(
                        path,
                        line.no,
                        "note line outside a block",
                    ));
                }
            }
            continue;
        }
        if super::super::PART_MARKERS.contains(&t.as_str()) {
            if let Some(held) = &pending_by {
                return Err(Problem::new(
                    path,
                    held.line,
                    format!(
                        "the `by` line on line {} has no steps before the next part",
                        held.line
                    ),
                ));
            }
            pending_markers.push((t.clone(), line.no, None));
            continue;
        }
        if let Some(kind) = intro {
            let Some(label) = label_at_end(&t) else {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!("{head} line carries no label"),
                ));
            };
            let Some(said) = skeleton::which_is_the_claim(&t) else {
                pending_openers.push(HeldOpener {
                    kind,
                    text: t.clone(),
                    label,
                    line: line.no,
                    after_by: pending_by.is_some(),
                });
                continue;
            };
            // A case that is the claim has no step to say which block it is
            // in, so it is in the innermost `cases` block open at this line.
            let draft = thm.as_mut().unwrap();
            let last = draft.steps.last().map(|s| s.step.number.clone());
            // The theorem proved `by cases` is the block of the theorem's own
            // step.
            let owner = last.and_then(|n| {
                (0..=n.depth()).rev().map(|k| n.prefix(k)).find(|p| {
                    by_number.get(p).is_some_and(|&i| {
                        draft.steps[i].step.just.head.is(Method::Cases)
                    })
                })
            });
            let Some(parent) = owner else {
                return Err(Problem::new(
                    path,
                    line.no,
                    "a line saying it is the claim outside any `cases` block",
                ));
            };
            if pending_by.is_some() {
                return Err(Problem::new(
                    path,
                    line.no,
                    "a case that is the claim has no steps and says no `by`",
                ));
            }
            let at = by_number[&parent];
            let current = attach(
                path,
                draft,
                Some(at),
                &parent,
                &mut pending_markers,
                &mut pending_openers,
                &mut pending_by,
                &mut part_no,
            )?;
            draft.steps[at].step.openers.push(Opener {
                kind,
                text: format!("{said} ({label})"),
                label,
                line: line.no,
                part: current,
                is_claim: true,
                is_hypothesis: false,
                hypothesis_for: None,
                after_by: false,
            });
            continue;
        }
        if head == "requires" {
            // A let written between the step and this line stands between
            // them: the line would be read as the step's, which it is not
            // written under. Before any step, it is the let's or nothing's.
            let requires = requires_line(&t, path, line.no, &draft.thm.names)?;
            let since = step.map_or(0, |at| draft.steps[at].step.line);
            let between = draft
                .thm
                .defines
                .iter()
                .rfind(|d| d.line > since && d.line < line.no)
                .map(|d| d.label.clone());
            if let Some(label) = between {
                // Right under a let's reason, or under a requires line there,
                // it is the let's.
                let Some(mut under) = previous.filter(|p| p.label == label) else {
                    return Err(Problem::new(
                        path,
                        line.no,
                        format!(
                            "requires line under let {label}, which carries none here: a let's requires lines stand right under its reason, and only a let saying a kind of number has a reason"
                        ),
                    ));
                };
                let Some(reason) = under.reason.as_mut() else {
                    return Err(Problem::new(
                        path,
                        line.no,
                        format!(
                            "requires line under let {label}, which says no kind of number and so has no reason for it to serve"
                        ),
                    ));
                };
                reason.requires.push(requires);
                for written in draft
                    .thm
                    .defines
                    .iter_mut()
                    .filter(|x| x.line == under.line)
                {
                    written.reason = under.reason.clone();
                }
                just_defined = Some(under);
                continue;
            }
            let Some(at) = step else {
                return Err(Problem::new(
                    path,
                    line.no,
                    "requires line outside a step",
                ));
            };
            draft.steps[at].step.requires.push(requires);
            continue;
        }
        if let Some(at) = step {
            if !draft.steps[at].has_just {
                let labels = justification_labels(&scope, &draft.thm);
                if is_justification(&t, &labels) {
                    draft.steps[at].step.just =
                        parse_justification(path, &line, &labels, &draft.thm.names)?;
                    draft.steps[at].has_just = true;
                } else {
                    draft.steps[at].step.claim.continued(&t);
                }
                continue;
            }
            // An `inequalities` step with no `from` may write its rows; the
            // first row's reason is the line the step cites, and its only
            // citation (`GRAMMAR.md`, inequality rows).
            let just = &draft.steps[at].step.just;
            if just.head.is(Method::Inequalities)
                && (!just.rows.is_empty() || just.refs.is_empty())
            {
                let first = just.rows.is_empty();
                let just = &mut draft.steps[at].step.just;
                if first {
                    just.refs.extend(chain_cited(&line.text));
                }
                just.rows.push((line.text.clone(), line.no));
                continue;
            }
            if draft.steps[at].step.just.head.is(Method::Calculation) {
                let cited = chain_citation(path, &line)?;
                let just = &mut draft.steps[at].step.just;
                just.refs.extend(cited);
                just.chain.push((line.text.clone(), line.no));
                continue;
            }
            // A `substitute` with no equation writes its rows, each giving
            // its reason as a chain's line does (`GRAMMAR.md`, substitute
            // rows).
            let just = &draft.steps[at].step.just;
            if just.head.is(Method::Substitute)
                && just.equation.is_none()
                && just.source.is_none()
            {
                let cited = chain_citation(path, &line)?;
                let just = &mut draft.steps[at].step.just;
                just.refs.extend(cited);
                just.rows.push((line.text.clone(), line.no));
                continue;
            }
            if let Some(said) = misnumbered(&t) {
                return Err(Problem::new(path, line.no, said));
            }
            return Err(Problem::new(
                path,
                line.no,
                format!(
                    "unexpected line after a justification: {}",
                    repr(prefix(&t, 48))
                ),
            ));
        }
        if let Some(said) = misnumbered(&t) {
            return Err(Problem::new(path, line.no, said));
        }
        return Err(Problem::new(
            path,
            line.no,
            format!("unexpected line {}", repr(prefix(&t, 48))),
        ));
    }
    if let Some(d) = awaiting_reason {
        return Err(Problem::new(
            path,
            d.line,
            format!(
                "let {} says what kind of number its name is, and the line under it gives no reason",
                d.label
            ),
        ));
    }
    close_step(path, &thm, &mut step)?;
    held_at_end(
        path,
        first_marker(&pending_markers),
        first_opener(&pending_openers),
        pending_by.as_ref().map(|b| b.line),
    )?;
    settle(path, thm.take(), &mut scope, &mut theorems)?;
    Ok((scope, theorems))
}

/// A part marker or an opener is held for the step after it, so one the
/// theorem ends under has nothing in it: the last case of a `cases` block
/// with no steps, which only a case saying it is the claim may be. Each is
/// given by the first of its kind still held, with its line.
pub(super) fn held_at_end(
    path: &str,
    marker: Option<(&str, usize)>,
    opener: Option<(&str, usize)>,
    by: Option<usize>,
) -> Checked<()> {
    if let Some(at) = by {
        return Err(Problem::new(
            path,
            at,
            "this `by` line has no steps, and the theorem ends under it",
        ));
    }
    if let Some((marker, at)) = marker {
        let claim = if marker == "case" {
            ", or end its assumption `, which is the claim`"
        } else {
            ""
        };
        return Err(Problem::new(
            path,
            at,
            format!("this {marker} has no steps, and the theorem ends under it; write its steps{claim}"),
        ));
    }
    if let Some((label, at)) = opener {
        return Err(Problem::new(
            path,
            at,
            format!(
                "{label} opens a part with no steps, and the theorem ends under it"
            ),
        ));
    }
    Ok(())
}
