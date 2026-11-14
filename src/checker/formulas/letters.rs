//! Letters introduced, suppositions and contradictions.

use super::*;

/// Each letter a step's claim or requires line writes free is one the step
/// may use (`letters_in_scope`). A `for all` binds its letter to the end of
/// its sentence, so "for all k ∈ ℕ₀, A. B." leaves k free in B.
pub fn check_letters_introduced(
    report: &mut Report,
    thm: &Theorem,
    env: Env,
    known: &Known,
) {
    let binders = env.g.binders();
    let shape = CheckedTheorem::of(thm);
    for s in &thm.steps {
        // The letters the claim binds, which its requires lines may write.
        let claimed: BTreeSet<String> = s
            .claim
            .sentences()
            .iter()
            .filter_map(|c| known.parse(c).ok())
            .flat_map(|c| known.bound(&c))
            .collect();
        let mut texts: Vec<(usize, String, &Written, bool)> =
            vec![(s.line, format!("step {}", s.number), &s.claim, false)];
        for r in &s.requires {
            texts.push((
                r.line,
                format!("the requires line of {}", s.called()),
                &r.fact,
                true,
            ));
        }
        let mut in_scope: Option<BTreeSet<String>> = None;
        for (line, what, written, under_claim) in texts {
            // What the sentences before this one bound, whose letters end
            // with them.
            let mut ended: BTreeSet<String> = BTreeSet::new();
            for sentence in written.sentences() {
                let Ok(node) = known.parse(&sentence) else {
                    continue;
                };
                let scope = in_scope
                    .get_or_insert_with(|| letters_in_scope(thm, &shape, s, known));
                for name in free_names(&node, &binders) {
                    let bound = under_claim && claimed.contains(&name);
                    if !scope.contains(&name) && !bound {
                        let why = if ended.contains(&name) {
                            "; a `for all` binds its letter only to the end of its sentence"
                        } else {
                            ""
                        };
                        report.say(
                            &thm.path,
                            line,
                            format!("{what}: {name} is not introduced here{why}"),
                        );
                    }
                }
                ended.extend(known.bound(&node));
            }
        }
        // A value the step gives an item's letter, `k := t`, is a term it
        // writes, of letters it may use, the claim's bound ones among them
        // where the item is read at a member, as its requires lines may.
        let Ok(values) = s.just.values.read(env.g, &known.sorts) else {
            continue; // `check_formulas` says a value does not read
        };
        for v in &values {
            let scope =
                in_scope.get_or_insert_with(|| letters_in_scope(thm, &shape, s, known));
            for name in free_names(&v.value, &binders) {
                if !scope.contains(&name) && !claimed.contains(&name) {
                    report.say(
                        &thm.path,
                        s.just.line,
                        format!(
                            "step {}: {name} in {} := {} is not introduced here",
                            s.number, v.name, v.shown
                        ),
                    );
                }
            }
        }
    }
    header_letters_introduced(report, thm, env, known);
}

/// Each letter the theorem's statement writes free, in a hypothesis or the
/// `then` line, is one it introduces, the file's, or a define's written
/// above the `then`: the statement says what it says before its proof
/// begins (`check_statement_names`).
pub(super) fn header_letters_introduced(
    report: &mut Report,
    thm: &Theorem,
    env: Env,
    known: &Known,
) {
    let binders = env.g.binders();
    let mut scope = super::super::structure::hypotheses_introduce(thm, known);
    scope.extend(
        visible(env.scopes, thm.scope, thm.line)
            .into_iter()
            .map(|v| v.name.clone()),
    );
    scope.extend(known.sorts.imported.iter().cloned());
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        if let Built(said) = define_parts(&d.text) {
            scope.extend(said.names());
        }
    }
    let mut written: Vec<Written> =
        thm.hypotheses.iter().map(|h| h.body(&thm.path)).collect();
    written.push(thm.stated());
    for w in &written {
        for sentence in w.sentences() {
            let Ok(node) = known.parse(&sentence) else {
                continue; // `check_formulas` says it does not read
            };
            for name in free_names(&node, &binders) {
                if !scope.contains(&name) {
                    report.say(
                        &thm.path,
                        w.line(),
                        format!(
                            "the statement writes {name}, which it does not introduce"
                        ),
                    );
                }
            }
        }
    }
}

/// A notation that takes a part of a graph or a group, `deg(v)` the graph's
/// degree, is written where a `let` line of the theorem introduces one:
/// nothing on the page names the part, and the line is what gives it
/// (`targets::GRAPH_PARTS`, `GROUP_PARTS`).
pub fn check_structure_parts(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    let lets = thm
        .hypotheses
        .iter()
        .filter(|h| h.kind == Intro::Let)
        .map(|h| h.body(&thm.path))
        .chain(thm.steps.iter().flat_map(|s| {
            s.openers
                .iter()
                .filter(|o| o.kind == Intro::Let)
                .map(|o| Written::new(&o.text, &thm.path, o.line))
        }));
    let mut given: BTreeSet<&str> = BTreeSet::new();
    for body in lets {
        let parts = match Introduction::read(body).form {
            Form::Graph(_) | Form::GraphListed(_) => crate::targets::GRAPH_PARTS,
            Form::Group { .. } => crate::targets::GROUP_PARTS,
            _ => continue,
        };
        given.extend(parts.iter().map(|(name, _)| *name));
    }
    let mut written: Vec<Written> =
        thm.hypotheses.iter().map(|h| h.body(&thm.path)).collect();
    written.push(thm.stated());
    for s in &thm.steps {
        written.push(s.claim.clone());
        written.extend(s.requires.iter().map(|r| r.fact.clone()));
    }
    let mut told: BTreeSet<String> = BTreeSet::new();
    for w in &written {
        for sentence in w.sentences() {
            let Ok(node) = known.parse(&sentence) else {
                continue; // `check_formulas` says it does not read
            };
            for part in &node.walk() {
                for context in targets.contexts(part) {
                    if given.contains(context.as_str())
                        || !told.insert(part.notation_name().to_string())
                    {
                        continue;
                    }
                    let structure = if crate::targets::GRAPH_PARTS
                        .iter()
                        .any(|(name, _)| *name == context)
                    {
                        "a graph"
                    } else {
                        "a group"
                    };
                    report.say(
                        &thm.path,
                        w.line(),
                        format!(
                            "{} is said of {structure}, and no `let` line of the theorem introduces one",
                            known.print(part)
                        ),
                    );
                }
            }
        }
    }
}

/// A theorem's statement says what it says before its proof begins, so it
/// writes no name only the proof defines (`SYNTAX.md`, "A define may name a
/// function"): a define the statement uses is written in the header, among
/// its `let` lines, or above the theorem.
pub fn check_statement_names(
    report: &mut Report,
    thm: &Theorem,
    env: Env,
    known: &Known,
) {
    let proof_defines: BTreeSet<String> = thm
        .defines
        .iter()
        .filter(|d| d.line > thm.conclusion_line)
        .filter_map(|d| match define_parts(&d.text) {
            Built(said) => Some(said.names()),
            Declined(_) => None,
        })
        .flatten()
        .collect();
    if proof_defines.is_empty() {
        return;
    }
    let binders = env.g.binders();
    let assumed = thm
        .hypotheses
        .iter()
        .filter(|h| h.kind == Intro::Assume)
        .map(|h| (h.body(&thm.path), h.line));
    let stated = Written::new(&thm.conclusion, &thm.path, thm.conclusion_line);
    let mut named: BTreeSet<String> = BTreeSet::new();
    for (written, line) in assumed.chain(std::iter::once((stated, thm.conclusion_line)))
    {
        for sentence in written.sentences() {
            let Ok(node) = known.parse(&sentence) else {
                continue;
            };
            for name in free_names(&node, &binders) {
                if proof_defines.contains(&name) && named.insert(name.clone()) {
                    report.say(
                        &thm.path,
                        line,
                        format!(
                            "theorem {} states {name}, which only its proof defines; a define the statement uses is written in its header",
                            thm.name
                        ),
                    );
                }
            }
        }
    }
}

/// True when a is b with a negation in front.
///
/// A folded negation counts, because a record declaring `negates` makes "n
/// is not odd" the same tree as "not (n is odd)". `wrappers` is the set of
/// notations those records name, so no notation is known here by its text.
/// Whether `a` denies `b`: a negation of the same claim, however either is
/// written (`Known::alike`), so `b ≠ a` denies `a = b`.
pub(super) fn negates(
    a: Option<&Node>,
    b: Option<&Node>,
    wrappers: &FxIndexSet<NotationId>,
    known: &Known,
) -> bool {
    negates_how(a, b, wrappers, known).is_some()
}

/// `negates`, with how what `a` denies meets `b` (`Known::alike_how`).
pub(super) fn negates_how(
    a: Option<&Node>,
    b: Option<&Node>,
    wrappers: &FxIndexSet<NotationId>,
    known: &Known,
) -> Option<crate::matching::Meeting> {
    let (a, b) = (a?, b?);
    if a.children.is_empty() || !wrappers.contains(&a.notation()) {
        return None;
    }
    known.alike_how(&a.children[0], b)
}

pub(super) fn wrappers(env: Env) -> FxIndexSet<NotationId> {
    env.g
        .notations
        .iter()
        .filter_map(|n| n.folds.as_deref().map(NotationId::of))
        .collect()
}

/// A contradiction's supposition and what it is to show, as read: the
/// block's claim, or what a part proved by contradiction owes. Either is
/// None where it does not read, which is reported where it is read.
pub(super) struct SupposedReading {
    /// The line the `suppose` is on.
    pub(super) line: usize,
    pub(super) supposed: Option<Node>,
    pub(super) claimed: Option<Node>,
    /// The claim as the page writes it (`Reading::Written`), where it is
    /// read so.
    pub(super) written: Option<Node>,
}

impl SupposedReading {
    pub(super) fn reads(&self) -> bool {
        self.supposed.is_some() && self.claimed.is_some()
    }

    /// Which of the two `METHODS.md` shapes the supposition has; None where
    /// it has neither, or either side does not read.
    pub(super) fn kind(
        &self,
        wrappers: &FxIndexSet<NotationId>,
        known: &Known,
    ) -> Option<(Supposed, crate::matching::Meeting)> {
        let (supposed, claimed) = (self.supposed.as_ref(), self.claimed.as_ref());
        if let Some(met) = negates_how(supposed, claimed, wrappers, known) {
            return Some((Supposed::ClaimDenied, met));
        }
        negates_how(claimed, supposed, wrappers, known)
            .map(|met| (Supposed::Denial, met))
    }
}

/// The supposition a contradiction step opens its block with, and the
/// step's claim; None where the block supposes nothing.
pub(super) fn own_supposition(
    thm: &Theorem,
    step: &Step,
    known: &Known,
) -> Option<SupposedReading> {
    let own = step.opening(None).own;
    let opener = own.iter().find(|o| o.kind == Intro::Suppose)?;
    Some(SupposedReading {
        line: opener.line,
        supposed: known.whole(step, &opener.body(&thm.path)),
        claimed: known.whole(step, &step.claim),
        written: known.whole_as_written(&step.claim),
    })
}

/// The supposition part `part` of `owner`'s block opens with, and what the
/// part owes, one sentence each (`block_owes`), and as written where
/// `written` gives what the parts owe so read; None where the part
/// supposes nothing.
pub(super) fn part_supposition(
    thm: &Theorem,
    owner: &Step,
    part: Option<usize>,
    owed: &[Owed],
    written: &[Owed],
    outside: &crate::matching::Definitions,
    known: &Known,
) -> Option<SupposedReading> {
    let opening = owner.opening(part);
    let opener = opening.inner.first().filter(|o| o.kind == Intro::Suppose)?;
    let body = opener.body(&thm.path);
    let supposed = match body.sentences().as_slice() {
        [one] => known.read_citing(one, outside),
        _ => None,
    };
    let one_owed = |owed: &[Owed]| {
        owed.iter()
            .find(|o| o.part == part)
            .and_then(|o| match o.claim.as_slice() {
                [one] => Some(one.clone()),
                _ => None,
            })
    };
    Some(SupposedReading {
        line: opener.line,
        supposed,
        claimed: one_owed(owed),
        written: one_owed(written),
    })
}

/// How each contradiction's supposition stands to what it shows, by the
/// line its `suppose` is on (`record::Supposed`). A supposition of neither
/// shape is a problem `check_contradiction` reports, and has none.
pub fn suppositions(
    thm: &Theorem,
    env: Env,
    known: &Known,
) -> IndexMap<usize, Supposition> {
    let wrappers = wrappers(env);
    let outside = known.citing(&[]);
    let mut readings = Vec::new();
    for step in &thm.steps {
        if step.just.head.is(Method::Contradiction) {
            readings.extend(own_supposition(thm, step, known));
        }
        let by_parts = step
            .by_lines
            .iter()
            .filter(|b| b.method == Method::Contradiction);
        let mut by_parts = by_parts.peekable();
        if by_parts.peek().is_none() {
            continue;
        }
        let Ok(owed) = block_owes(step, known) else {
            continue;
        };
        let written =
            block_owes_read(step, known, Reading::Written).unwrap_or_default();
        for by in by_parts {
            readings.extend(part_supposition(
                thm, step, by.part, &owed, &written, &outside, known,
            ));
        }
    }
    readings
        .iter()
        .filter_map(|r| {
            let (shape, meeting) = r.kind(&wrappers, known)?;
            let against = r.written.clone()?;
            Some((
                r.line,
                Supposition {
                    shape,
                    against,
                    meeting,
                },
            ))
        })
        .collect()
}

/// The two lines each step written `contradicting N` that closes a block
/// closes it on, by the line of its justification (`record::Contradicted`):
/// what of line N it opposes, and which of the two says the other negated,
/// as `check_contradicting` finds them.
pub fn contradictions(
    thm: &Theorem,
    env: Env,
    known: &Known,
) -> IndexMap<usize, Contradicted> {
    let wrappers = wrappers(env);
    let mut out = IndexMap::new();
    for (at, step) in thm.steps.iter().enumerate() {
        let Some(other) = &step.just.contradicting else {
            continue;
        };
        if !ends_block(thm, at) {
            continue;
        }
        let scope = known.scope(step);
        let Some(said) = scope.get(other) else {
            continue;
        };
        let claimed = known.whole(step, &step.claim);
        let says = known.says(said, &known.citing_step(step));
        let own = known.sentence_count(said);
        let found = says.iter().find_map(|s| {
            let there = Some(s.cited.clone());
            let (negated, meeting) =
                match negates_how(claimed.as_ref(), there.as_ref(), &wrappers, known) {
                    Some(met) => (Negating::Step, met),
                    None => (
                        Negating::Line,
                        negates_how(
                            there.as_ref(),
                            claimed.as_ref(),
                            &wrappers,
                            known,
                        )?,
                    ),
                };
            // A thing the line says that `FirstAt` cannot place, a chain's
            // equation between two terms, is no line a backend can name.
            let placed = super::super::citations::placed(other, s, &says, own)?;
            Some(Contradicted {
                at: placed,
                negated,
                meeting,
            })
        });
        if let Some(c) = found {
            out.insert(step.just.line, c);
        }
    }
    out
}

/// A contradiction block relates its supposition to its claim, and closes
/// with a formula and that formula's negation.
///
/// `METHODS.md` specifies the two shapes: the supposition is the claim
/// negated, which is reductio, or the claim is the supposition negated,
/// which proves a negation directly. No formula is its own double negation,
/// so at most one holds and the expansion each needs is never in doubt.
/// Anything else the method refuses, which is why this is reported rather
/// than left to fail later with nothing to point at.
pub fn check_contradiction(
    report: &mut Report,
    thm: &Theorem,
    env: Env,
    known: &Known,
) {
    let wrappers = wrappers(env);
    let shape = CheckedTheorem::of(thm);
    for step in &thm.steps {
        check_part_contradictions(report, thm, step, &wrappers, known);
    }
    for (at, step) in thm.steps.iter().enumerate() {
        if !step.just.head.is(Method::Contradiction) {
            continue;
        }
        let Some(reading) = own_supposition(thm, step, known) else {
            continue; // already reported as a missing suppose
        };
        // What could not be read is reported where it is read; the block's
        // last step is checked all the same.
        if reading.reads() && reading.kind(&wrappers, known).is_none() {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "{} supposes something that is neither its claim negated nor the thing its claim negates, so neither expansion of `contradiction` applies",
                    step.called()
                ),
            );
        }
        // The block's last step is the last of its own, not the last of a
        // block inside it (`record::Block::last`): a `cases` step ending the
        // block names the line its cases together contradict (`SYNTAX.md`,
        // contradiction).
        let Some(last) = shape.block_of(at).and_then(|b| b.last()) else {
            continue;
        };
        let last_step = &thm.steps[last];
        if last_step.just.contradicting.is_none() && !last_step.impossible {
            report.say(
                &thm.path,
                last_step.line,
                format!(
                    "step {} ends a contradiction block and does not say which line it contradicts: write `contradicting` and the line after its reasons, or `, which is impossible` after a claim of numerals alone",
                    last_step.number
                ),
            );
        }
    }
}

/// Each part of the block `owner` opens that is proved `by contradiction`
/// relates its supposition to what the part owes, as a contradiction step
/// relates its supposition to its claim, and its last step says which line
/// it contradicts (`check_contradiction`). What the part owes is read as
/// `block_owes` reads it, and so is the supposition.
pub(super) fn check_part_contradictions(
    report: &mut Report,
    thm: &Theorem,
    owner: &Step,
    wrappers: &FxIndexSet<NotationId>,
    known: &Known,
) {
    let contradicted = owner
        .by_lines
        .iter()
        .any(|b| b.method == Method::Contradiction);
    if !contradicted {
        return;
    }
    // A claim that does not read is reported where it is read.
    let Ok(owed) = block_owes(owner, known) else {
        return;
    };
    let outside = known.citing(&[]);
    for by in owner
        .by_lines
        .iter()
        .filter(|b| b.method == Method::Contradiction)
    {
        let called = owner.part_called(by.part);
        // A part with no supposition is `check_part_by`'s to report.
        let Some(reading) =
            part_supposition(thm, owner, by.part, &owed, &[], &outside, known)
        else {
            continue;
        };
        if reading.reads() && reading.kind(wrappers, known).is_none() {
            report.say(
                &thm.path,
                reading.line,
                format!(
                    "{called} supposes something that is neither what it owes negated nor the thing it owes negates, so neither expansion of `contradiction` applies"
                ),
            );
        }
        let Some(last) = last_of_part(thm, owner, by.part) else {
            continue; // `check_block_ends` says the part has no steps
        };
        if last.just.contradicting.is_none() && !last.impossible {
            report.say(
                &thm.path,
                last.line,
                format!(
                    "step {} ends {called}, proved by contradiction, and does not say which line it contradicts: write `contradicting` and the line after its reasons, or `, which is impossible` after a claim of numerals alone",
                    last.number
                ),
            );
        }
    }
}

/// Whether the step at `at` is the last of a contradiction block, which it
/// closes, or of a case, which it shows cannot occur.
pub(super) fn ends_block(thm: &Theorem, at: usize) -> bool {
    let step = &thm.steps[at];
    // The step's block is the one its number sits directly under.
    let depth = step.number.depth();
    let owner = thm.steps[..at].iter().rev().find(|s| {
        s.number.depth() + 1 == depth
            && step.number.prefix(s.number.depth()) == s.number
    });
    let later = thm.steps[at + 1..]
        .iter()
        .find(|s| s.number.depth() <= depth);
    // The method whose block the step's part ends: the part's `by` method,
    // or the owner's. A `proof` block whose assumption cannot hold ends as a
    // case that cannot occur does.
    let closes = owner.and_then(|o| o.closing(step.part));
    match closes {
        Some(Method::Contradiction | Method::Proof | Method::Cases) => match later {
            None => true,
            Some(s) => s.number.depth() < depth || s.part != step.part,
        },
        _ => false,
    }
}

/// A step whose claim says `, which is impossible`: the claim is numerals
/// alone, which `arithmetic` works out and the elaborator shows false, and
/// the step ends a contradiction block or a case as one contradicting a
/// line does, in place of that line.
pub fn check_impossible(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for (at, step) in thm.steps.iter().enumerate() {
        if !step.impossible {
            continue;
        }
        if step.just.contradicting.is_some() {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {} says it is impossible and contradicts a line: one of the two says the block is closed",
                    step.number
                ),
            );
        }
        if let Some(node) = known.whole(step, &step.claim) {
            // A library function's name, ln in ln(2), is no letter.
            let named: Vec<String> = node
                .walk()
                .iter()
                .filter(|n| n.is_name() && !library_named(&n.text, known))
                .map(|n| n.text.to_string())
                .collect();
            if !named.is_empty() {
                report.say(
                    &thm.path,
                    step.line,
                    format!(
                        "step {} says it is impossible and names {}: only a closed claim is shown false by working it out, and one naming anything contradicts a line",
                        step.number,
                        named.join(", ")
                    ),
                );
            } else {
                // A closed claim said to be impossible is one that works out
                // false: by `real arithmetic` where it holds a square root,
                // π, e, a logarithm or an exponential, and by `arithmetic`
                // otherwise.
                let why = if beyond_arithmetic(&step.claim, known, targets) {
                    match real_worked(&step.claim, known, targets) {
                        RealWorked::Fails(_) => None,
                        RealWorked::Holds => Some("it holds"),
                        _ => Some("real arithmetic does not work it out"),
                    }
                } else {
                    match arithmetic_worked(&step.claim, known, targets) {
                        Worked::Fails(_) => None,
                        Worked::Holds => Some("it holds"),
                        Worked::Undecided => Some("arithmetic does not work it out"),
                    }
                };
                if let Some(why) = why {
                    report.say(
                        &thm.path,
                        step.line,
                        format!(
                            "step {} says {} is impossible, and {why}",
                            step.number,
                            step.claim_text()
                        ),
                    );
                }
            }
        }
        if !ends_block(thm, at) {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {} says it is impossible, which only the last step of a contradiction block, a case or a proof block may do",
                    step.number
                ),
            );
        }
    }
}

/// Whether a step's claim and something the line `said` says (`Known::says`,
/// with the defines the step cites written out) are a formula and that
/// formula negated, either way round.
pub(super) fn opposes(
    step: &Step,
    said: &Stated,
    wrappers: &FxIndexSet<NotationId>,
    known: &Known,
) -> bool {
    let claimed = known.whole(step, &step.claim);
    known.says(said, &known.citing_step(step)).iter().any(|s| {
        let there = Some(s.cited.clone());
        negates(claimed.as_ref(), there.as_ref(), wrappers, known)
            || negates(there.as_ref(), claimed.as_ref(), wrappers, known)
    })
}

/// Whether a step contradicts a line only with all it cites: with the lines
/// `without` in their place it no longer opposes the line (`opposes`).
pub(super) fn reads_contradicted(
    step: &Step,
    without: &[String],
    library: &Library,
    known: &Known,
) -> bool {
    let Some(other) = &step.just.contradicting else {
        return false;
    };
    let Some(said) = known.scope(step).get(other).cloned() else {
        return false;
    };
    let wrappers = wrappers(library.env);
    let mut lighter = step.clone();
    lighter.just.refs = without.to_vec();
    opposes(step, &said, &wrappers, known)
        && !opposes(&lighter, &said, &wrappers, known)
}

/// A step written `contradicting N`: its claim and line N are a formula and
/// that formula negated, and the step is the last of a contradiction block,
/// which it closes, or of a case, which it shows cannot occur.
pub fn check_contradicting(
    report: &mut Report,
    thm: &Theorem,
    env: Env,
    known: &Known,
) {
    let wrappers = wrappers(env);
    for (at, step) in thm.steps.iter().enumerate() {
        let Some(other) = &step.just.contradicting else {
            continue;
        };
        let scope = known.scope(step);
        let Some(said) = scope.get(other) else {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} contradicts {other}, which is no line in scope",
                    step.number
                ),
            );
            continue;
        };
        // The claim is the opposite of the line, or of one sentence of it:
        // a line may say several things and be contradicted in one, or in
        // all of them at once, since "A. B" is "A and B".
        let claimed = known.whole(step, &step.claim);
        let opposed = opposes(step, said, &wrappers, known);
        if claimed.is_some() && known.reads(said) && !opposed {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} says it contradicts {other}, and neither is the other negated",
                    step.number
                ),
            );
        }
        if !ends_block(thm, at) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} contradicts a line, which only the last step of a contradiction block, a case or a proof block may do",
                    step.number
                ),
            );
        }
    }
}

/// A case that says it is the claim assumes what its block claims, and has
/// no steps: there is nothing in it to show.
pub fn check_claimed_cases(report: &mut Report, thm: &Theorem, known: &Known) {
    for owner in &thm.steps {
        for o in owner.openers.iter().filter(|o| o.is_claim) {
            let assumed = known.whole(owner, &o.body(&thm.path));
            let claim = known.whole(owner, &owner.claim);
            let differ = match (&assumed, &claim) {
                (Some(a), Some(c)) => !known.alike(a, c),
                _ => false,
            };
            if differ {
                report.say(
                    &thm.path,
                    o.line,
                    format!(
                        "case {} says it is the claim of {}, and it is not",
                        o.label,
                        owner.called()
                    ),
                );
            }
            let depth = owner.number.depth() + 1;
            let inside = thm.steps.iter().any(|s| {
                s.number.depth() == depth
                    && s.number.prefix(depth - 1) == owner.number
                    && s.part == o.part
            });
            if inside {
                report.say(
                    &thm.path,
                    o.line,
                    format!("case {} is the claim and has steps of its own", o.label),
                );
            }
        }
    }
}

/// A `both directions` block proves "A ↔ B" as a textbook proves an "if and
/// only if": its first part assumes A, its second assumes B. What each
/// ends on, the other side, is `check_block_ends`'s to see (`block_owes`).
pub fn check_both_directions(report: &mut Report, thm: &Theorem, known: &Known) {
    for owner in &thm.steps {
        if !owner.just.head.is(Method::BothDirections) {
            continue;
        }
        let say = |report: &mut Report, why: String| {
            report.say(
                &thm.path,
                owner.line,
                format!("{} proves both directions, and {why}", owner.called()),
            );
        };
        let Some(claim) = known.whole(owner, &owner.claim) else {
            continue; // `check_formulas` says it does not read
        };
        if claim.notation() != BICONDITIONAL || claim.children.len() != 2 {
            say(report, "its claim is not \"A ↔ B\"".into());
            continue;
        }
        let mut assumed: Vec<_> = owner
            .openers
            .iter()
            .filter(|o| o.kind == Intro::Assume && o.part.is_some() && !o.after_by)
            .collect();
        assumed.sort_by_key(|o| o.part);
        if owner.parts.len() != 2 || assumed.len() != 2 {
            say(
                report,
                "it does not have two directions, each opening with `assume`".into(),
            );
            continue;
        }
        for (n, opener) in assumed.iter().enumerate() {
            let side = &claim.children[n];
            let read = known.whole(owner, &opener.body(&thm.path));
            if read.as_ref().is_some_and(|r| !known.alike(r, side)) {
                say(
                    report,
                    format!(
                        "direction {} does not assume the claim's side it starts from",
                        n + 1
                    ),
                );
            }
        }
    }
}
