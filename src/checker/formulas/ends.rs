//! What blocks owe, cases cited, places, chains and what holds.

use super::*;

/// What one part of a block owes: the part, as its steps are numbered, the
/// sentences its last step claims, and how a message names the part.
pub(in crate::checker) struct Owed {
    pub(in crate::checker) part: Option<usize>,
    /// What the part owes, as its owner's method gives it.
    pub(in crate::checker) claim: Vec<Node>,
    /// What the part's last step ends on: the claim, or what the part's `by`
    /// line makes of it (`after_by`).
    pub(in crate::checker) ends: Ends,
    pub(super) called: String,
}

/// What the last step of a part ends on.
pub(in crate::checker) enum Ends {
    /// These sentences.
    Claim(Vec<Node>),
    /// A contradiction: the part is proved `by contradiction`, and
    /// `check_contradiction` sees its last step.
    Contradiction,
}

impl Owed {
    /// A part owing `claim`, whose last step ends on it.
    pub(super) fn new(part: Option<usize>, claim: Vec<Node>, called: String) -> Owed {
        Owed {
            part,
            ends: Ends::Claim(claim.clone()),
            claim,
            called,
        }
    }
}

/// The last step of `part` of the block `owner` opens, one of its own and
/// not of a block inside it; None for a part with no steps.
pub(in crate::checker) fn last_of_part<'a>(
    thm: &'a Theorem,
    owner: &Step,
    part: Option<usize>,
) -> Option<&'a Step> {
    let depth = owner.number.depth() + 1;
    thm.steps.iter().rev().find(|s| {
        s.number.depth() == depth
            && s.number.prefix(depth - 1) == owner.number
            && s.part == part
    })
}

/// What each part of the block `owner` opens owes (`check_block_ends`):
/// none for a step opening no induction, `cases` or `proof` block, or one
/// whose claim does not read, which `check_formulas` reports. Each claim
/// is read with no define written out. A `proof` block whose claim has no
/// layer for an opener is the page's defect.
pub(in crate::checker) fn block_owes(
    owner: &Step,
    known: &Known,
) -> Checked<Vec<Owed>> {
    block_owes_read(owner, known, Reading::Compared)
}

/// How `block_owes_read` reads a block's claim.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::checker) enum Reading {
    /// As the checks compare it: with the outside defines written out, in
    /// the standard order (`Known::read_citing`).
    Compared,
    /// As the page writes it (`Known::read_as_written`): what a backend's
    /// goal is, the claim it states with the block's lines taken off.
    Written,
}

/// `block_owes`, the claim read as `reading` says.
pub(in crate::checker) fn block_owes_read(
    owner: &Step,
    known: &Known,
    reading: Reading,
) -> Checked<Vec<Owed>> {
    let outside = known.citing(&[]);
    let Some(claim) = owner
        .claim
        .sentences()
        .iter()
        .map(|s| match reading {
            Reading::Compared => known.read_citing(s, &outside),
            Reading::Written => known.read_as_written(s),
        })
        .collect::<Option<Vec<Node>>>()
    else {
        return Ok(Vec::new());
    };
    // A proof block and an induction prove one statement, which their
    // parts end on: a claim of several sentences is several steps.
    let method = owner.just.head.method();
    if matches!(method, Some(Method::Proof | Method::Induction)) && claim.len() != 1 {
        return Err(Problem::new(
            &known.thm.path,
            owner.line,
            format!(
                "{} opens a {} block and claims {} sentences; the block proves one, and each other sentence is a step of its own",
                owner.called(),
                owner.just.head,
                claim.len()
            ),
        ));
    }
    let owed = match (method, claim.as_slice()) {
        (Some(Method::Induction), [one]) => induction_owes(owner, one, known),
        (Some(Method::Cases), _) => (0..owner.parts.len())
            .map(|part| {
                let called = format!("case {} of {}", part + 1, owner.called());
                Owed::new(Some(part), claim.clone(), called)
            })
            .collect(),
        (Some(Method::Proof), [one]) => {
            let called = owner.called();
            let own = owner.opening(None).own;
            let rest = peel(&called, &own, one, known)?;
            vec![Owed::new(
                None,
                vec![rest],
                format!("the proof block of {called}"),
            )]
        }
        // Each direction ends on the side of "A ↔ B" the other assumes; a
        // claim of another shape is `check_both_directions`'s to report.
        (Some(Method::BothDirections), [one])
            if one.notation() == BICONDITIONAL
                && one.children.len() == 2
                && owner.parts.len() == 2 =>
        {
            (0..2)
                .map(|n| {
                    let called = format!("direction {} of {}", n + 1, owner.called());
                    Owed::new(Some(n), vec![one.children[1 - n].clone()], called)
                })
                .collect()
        }
        _ => Vec::new(),
    };
    owed.into_iter()
        .map(|o| after_by(owner, o, known))
        .collect()
}

/// Each part of an induction, a `cases` block and a `proof` block ends on
/// what it owes (`SYNTAX.md`, the methods that open a block): an
/// induction's base on the claim's statement at its start and its step on
/// the statement at k + 1; each case on the block's claim; a `proof` block
/// on its claim with what its `let` and `assume` lines took off it. A case
/// and a `proof` block may end instead on a step contradicting a line,
/// where what they assume cannot hold. `both directions` and
/// `contradiction` are checked where their other shapes are.
///
/// The two are compared as one formula (`Known::alike`), each read with no
/// define written out, so that a defined name is compared as it is written
/// on both sides.
pub fn check_block_ends(report: &mut Report, thm: &Theorem, known: &Known) {
    let outside = known.citing(&[]);
    let read = |written: &Written| -> Option<Vec<Node>> {
        written
            .sentences()
            .iter()
            .map(|s| known.read_citing(s, &outside))
            .collect()
    };
    for owner in &thm.steps {
        let owed = match block_owes(owner, known) {
            Ok(owed) => owed,
            Err(defect) => {
                report.problems.push(defect);
                continue;
            }
        };
        for Owed {
            part, ends, called, ..
        } in owed
        {
            let Some(last) = last_of_part(thm, owner, part) else {
                // A case that says it is the claim has no steps; any other
                // part with none shows nothing of what it owes.
                let claimed =
                    owner.openers.iter().any(|o| o.is_claim && o.part == part);
                if !claimed {
                    report.say(
                        &thm.path,
                        owner.line,
                        format!("{called} has no steps, so nothing shows what it owes"),
                    );
                }
                continue;
            };
            // A part proved `by contradiction` ends contradicting a line,
            // which `check_contradiction` sees.
            let Ends::Claim(claim) = ends else {
                continue;
            };
            // A case and a `proof` block whose assumption cannot hold end on
            // a contradiction; an induction's part never does.
            let contradicts = owner.closing(part) != Some(Method::Induction);
            if contradicts && (last.just.contradicting.is_some() || last.impossible) {
                continue;
            }
            // A last step whose reason matches no production may end its
            // part by a contradiction the reader did not take from it, so
            // what it ends on is not asked: it is told only that it does
            // not read.
            if last.just.unproduced.is_some() {
                continue;
            }
            let Some(ends) = read(&last.claim) else {
                continue;
            };
            // "A and B" is claimed by a step that says "A. B.", and the
            // other way round.
            let ends: Vec<Node> = ends.iter().flat_map(conjuncts).collect();
            let owes: Vec<Node> = claim.iter().flat_map(conjuncts).collect();
            let reached = ends.len() == owes.len()
                && ends.iter().zip(&owes).all(|(e, c)| known.alike(e, c));
            if !reached {
                let owes: Vec<String> = claim.iter().map(|c| known.print(c)).collect();
                report.say(
                    &thm.path,
                    last.line,
                    format!(
                        "step {} ends {called}, which owes {}",
                        last.number,
                        owes.join(". ")
                    ),
                );
            }
        }
    }
}

/// A sentence a step ends on, with the one it owes there: what a part of a
/// block owes of its last step, or what the theorem states of the proof's.
pub(super) struct Ending {
    pub(super) said: Node,
    pub(super) owed: Node,
    /// What the step ends, for a message: "the base", or the proof.
    pub(super) called: String,
}

/// What `step` ends owing, each sentence it says beside the one it owes:
/// for each part of a block it is the last step of (`check_block_ends`),
/// and for the proof where it is the last step (`check_last_step`). Empty
/// for any other step, and where the two do not say as many sentences.
pub(super) fn endings(thm: &Theorem, step: &Step, known: &Known) -> Vec<Ending> {
    let mut out = Vec::new();
    let outside = known.citing(&[]);
    for owner in &thm.steps {
        let Ok(owed) = block_owes(owner, known) else {
            continue;
        };
        for Owed {
            part, ends, called, ..
        } in owed
        {
            let Ends::Claim(claim) = ends else {
                continue;
            };
            let last = last_of_part(thm, owner, part);
            if last.is_none_or(|l| l.line != step.line) {
                continue;
            }
            let said = conjuncts_read(&step.claim, |s| known.read_citing(s, &outside));
            if let Some(said) = said {
                let owed = claim.iter().flat_map(conjuncts).collect();
                paired(said, owed, &called, &mut out);
            }
        }
    }
    // A theorem proved `by` a method ends with its block, which owes the
    // statement part by part, above; its own step, whose claim is the
    // statement, ends the proof, and owes it as written. Otherwise the last
    // top-level step owes it.
    let by_method = thm.steps.first().is_some_and(Step::proves_theorem);
    let last = thm.steps.iter().rev().find(|s| s.number.depth() == 1);
    let ends_proof = match by_method {
        true => step.proves_theorem(),
        false => last.is_some_and(|l| l.line == step.line),
    };
    if ends_proof {
        let stated = Written::new(&thm.conclusion, &thm.path, thm.line);
        let said = conjuncts_read(&step.claim, |s| known.read_as_written(s));
        let owed = conjuncts_read(&stated, |s| known.read_as_written(s));
        if let (Some(said), Some(owed)) = (said, owed) {
            paired(said, owed, "the proof", &mut out);
        }
    }
    out
}

/// How each step that ends a block, a part of one or the proof meets what it
/// owes there (`endings`), by the line of its justification: one meeting for
/// each part of its "and" in order, as the check paired them. A step whose parts do not
/// all meet what they owe has none, and the check reports it.
pub fn ended_meetings(
    thm: &Theorem,
    known: &Known,
) -> IndexMap<usize, Vec<crate::matching::Meeting>> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        let ends = endings(thm, step, known);
        if ends.is_empty() {
            continue;
        }
        let met: Option<Vec<_>> = ends
            .iter()
            .map(|e| known.alike_how(&e.said, &e.owed))
            .collect();
        if let Some(met) = met {
            out.insert(step.just.line, met);
        }
    }
    out
}

/// The conjuncts of what `written` says, each sentence read by `read`;
/// None where one does not read.
pub(super) fn conjuncts_read(
    written: &Written,
    read: impl Fn(&Sentence) -> Option<Node>,
) -> Option<Vec<Node>> {
    let mut out = Vec::new();
    for s in written.sentences() {
        out.extend(conjuncts(&read(&s)?));
    }
    Some(out)
}

/// Each sentence said beside the one owed in its place, into `out`, where
/// the two say as many.
pub(super) fn paired(
    said: Vec<Node>,
    owed: Vec<Node>,
    called: &str,
    out: &mut Vec<Ending>,
) {
    if said.len() != owed.len() {
        return;
    }
    for (said, owed) in said.into_iter().zip(owed) {
        out.push(Ending {
            said,
            owed,
            called: called.to_string(),
        });
    }
}

/// An identity element goes without saying where a step ends a part of a
/// block or the proof, and dropping one asks that what is left be a number
/// (`SYNTAX.md`, an identity element goes without saying): the base of an
/// induction claiming b(0) ≤ N where it owes b(0) + 0 ≤ N says b(0) is one,
/// by a line it cites or a requires line, where the page does not say it
/// once.
pub fn ends_unnumbered(
    report: &mut Report,
    thm: &Theorem,
    step: &Step,
    known: &Known,
    library: &Library,
) {
    let facts = known.parts(step, library).facts.clone();
    for Unnumbered { left, called } in ends_asking(thm, step, known, library, &facts) {
        report.say(
            &thm.path,
            step.line,
            format!(
                "step {} ends {called} by dropping an identity element, and nothing says {} is a number; a requires line says it",
                step.number,
                known.print(&left)
            ),
        );
    }
}

/// What dropping an identity element left where a step ends, and what it
/// ends.
pub struct Unnumbered {
    pub left: Node,
    pub(super) called: String,
}

/// What `step` ends on by dropping identity elements leaves that `facts`
/// do not say is a number and the page does not say once, each once
/// (`ends_unnumbered`). With no facts, what the step is asked to say.
pub fn ends_asking(
    thm: &Theorem,
    step: &Step,
    known: &Known,
    library: &Library,
    facts: &[Node],
) -> Vec<Unnumbered> {
    let mut out: Vec<Unnumbered> = Vec::new();
    for Ending { said, owed, called } in endings(thm, step, known) {
        let (said, owed) = (standard(&said, known.ctx), standard(&owed, known.ctx));
        if !known.alike(&said, &owed) {
            continue;
        }
        let mut dropped = identities_dropped(&owed, &said, known.ctx);
        dropped.extend(identities_dropped(&said, &owed, known.ctx));
        for left in not_numbers(dropped, &owed, &said, facts, library) {
            if !out.iter().any(|u| known.alike(&u.left, &left)) {
                out.push(Unnumbered {
                    left,
                    called: called.clone(),
                });
            }
        }
    }
    out
}

/// `ends_unnumbered` of every step of the theorem.
pub fn check_ends_numbered(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    library: &Library,
) {
    for step in &thm.steps {
        ends_unnumbered(report, thm, step, known, library);
    }
}

/// What an induction's parts owe: the base, the claim's statement at the
/// start the justification writes; the step, the statement at k + 1. A
/// claim not "for all k ∈ X, …" is `check_step_part`'s to report.
pub(super) fn induction_owes(owner: &Step, claim: &Node, known: &Known) -> Vec<Owed> {
    if claim.notation() != FOR_ALL || claim.children.len() != 3 {
        return Vec::new();
    }
    let letter = &claim.children[0];
    let at = |value: Node| -> Node {
        let mut put = Binding::new();
        put.insert(letter.text, value);
        substitute_apart_by(&claim.children[2], &put, &known.env.g.binders())
    };
    // The start as the justification writes it, `starting at 0`; one that
    // does not read is the elaborator's to report.
    let start = owner.just.start.as_deref().and_then(|v| {
        let written = Written::new(v, &known.thm.path, owner.just.line);
        known.read_as_written(&written.formula().ok()?)
    });
    // Over the parts of a set the step owes the statement at Y ∪ {a}, a the
    // member its third line adds; over numbers, at k + 1.
    let next = match super::super::structure::parts_of(&claim.children[1]) {
        None => Some(made(known.env.g, PLUS, vec![letter.clone(), numeral("1")])),
        Some(_) => member_added(owner, known).map(|a| {
            let one = made_by_name(known.env.g, SINGLETON, vec![a]);
            made(known.env.g, UNION, vec![letter.clone(), one])
        }),
    };
    let mut owed = Vec::new();
    for (part, (marker, _)) in owner.parts.iter().enumerate() {
        let (value, which) = match marker.as_str() {
            "base" => (start.clone(), "base"),
            "step" => (next.clone(), "step"),
            _ => continue,
        };
        if let Some(claim) = value.map(at) {
            owed.push(Owed::new(
                Some(part),
                vec![claim],
                format!("the {which} part of {}", owner.called()),
            ));
        }
    }
    owed
}

/// The member an induction over the parts of a set adds in its step part,
/// the a of its third line `let a ∈ X ∖ Y`; None where the part does not
/// open so, which `check_step_part` reports.
pub(super) fn member_added(owner: &Step, known: &Known) -> Option<Node> {
    let part = owner
        .parts
        .iter()
        .position(|(marker, _)| marker == "step")?;
    let lets: Vec<_> = owner
        .opening(Some(part))
        .own
        .into_iter()
        .filter(|o| o.kind == Intro::Let && !o.is_hypothesis)
        .collect();
    let [_, third] = lets.as_slice() else {
        return None;
    };
    let said = super::super::structure::let_said(third, known.thm, known)?;
    said.children.first().cloned()
}

/// What a `proof` block owes: `claim` with a "for all" taken off for each
/// `let` line of `opens` and an "if" for each `assume`, in the order they
/// open the block (`SYNTAX.md`, proof). A claim without the layer an opener
/// takes off is the page's defect, and so is a name that does not read;
/// `called` names the block's owner, or the part proved `by proof`, in the
/// message.
pub(super) fn peel(
    called: &str,
    opens: &[&Opener],
    claim: &Node,
    known: &Known,
) -> Checked<Node> {
    let path = &known.thm.path;
    let mut rest = claim.clone();
    for o in opens {
        rest = match (o.kind, rest.notation()) {
            (Intro::Let, FOR_ALL) if rest.children.len() == 3 => {
                let mut put = Binding::new();
                let opened = Introduction::read(o.body(path));
                let fixed = match opened.form {
                    Form::Member => opened.name().map(String::from),
                    _ => None,
                };
                let body = rest.children[2].clone();
                match fixed {
                    Some(name) if name != rest.children[0].text => {
                        let named = Written::new(name, path, o.line)
                            .formula()
                            .and_then(|s| known.parse(&s))?;
                        put.insert(rest.children[0].text, named);
                        substitute_apart_by(&body, &put, &known.env.g.binders())
                    }
                    _ => body,
                }
            }
            (Intro::Let, FOR_ALL_SETS) if rest.children.len() == 2 => {
                rest.children[1].clone()
            }
            (Intro::Assume, CONDITIONAL | IMPLICATION)
                if rest.children.len() == 2 =>
            {
                // What the block assumes is what the claim supposes, its
                // letters the block's (`SYNTAX.md`, `proof`).
                // "A. B" and "A and B" are one claim (`SYNTAX.md`).
                let body = o.body(path);
                let mut said = Vec::new();
                for s in body.sentences() {
                    said.push(known.parse(&s)?);
                }
                let assumed = match conjoined(known.env.g, said) {
                    Some(whole) => whole,
                    None => known.parse(&body.formula()?)?,
                };
                if !known.alike(&assumed, &rest.children[0]) {
                    return Err(Problem::new(
                        path,
                        o.line,
                        format!(
                            "{called} opens a proof block assuming {}, and its claim supposes {}",
                            known.print(&assumed),
                            known.print(&rest.children[0])
                        ),
                    ));
                }
                rest.children[1].clone()
            }
            (Intro::Let, _) => {
                return Err(Problem::new(
                    path,
                    o.line,
                    format!(
                        "{called} opens a proof block with a let line, and its claim says nothing of every such name"
                    ),
                ))
            }
            _ => {
                return Err(Problem::new(
                    path,
                    o.line,
                    format!(
                        "{called} opens a proof block with an assume line, and its claim supposes nothing there"
                    ),
                ))
            }
        };
    }
    Ok(rest)
}

/// What a part owes, with what its `by` line makes of it (`Owed::ends`):
/// under `by proof`, the claim with the part's inner `let` and `assume`
/// lines taken off (`peel`); under `by contradiction`, a contradiction.
pub(super) fn after_by(owner: &Step, owed: Owed, known: &Known) -> Checked<Owed> {
    let opening = owner.opening(owed.part);
    let Some(by) = opening.by else {
        return Ok(owed);
    };
    let called = owner.part_called(owed.part);
    let ends = match (by.method, owed.claim.as_slice()) {
        (Method::Contradiction, _) => Ends::Contradiction,
        (_, [one]) => Ends::Claim(vec![peel(&called, &opening.inner, one, known)?]),
        (_, many) => {
            return Err(Problem::new(
                &known.thm.path,
                by.line,
                format!(
                    "{called} is proved by `proof` and owes {} sentences; a proof block proves one",
                    many.len()
                ),
            ))
        }
    };
    Ok(Owed { ends, ..owed })
}

/// The sentences a formula says, an "and" taken apart, in order.
pub(super) fn conjuncts(node: &Node) -> Vec<Node> {
    if node.notation() == CONJUNCTION && node.children.len() == 2 {
        node.children.iter().flat_map(conjuncts).collect()
    } else {
        vec![node.clone()]
    }
}

/// A `cases` block cites one line, and that line claims the cases'
/// assumptions joined by "or", in the order the parts take them
/// (`SYNTAX.md`). A line with that disjunction as one part of what it says
/// is not it. The two are compared as one formula (`Known::alike`): an
/// equation or an order may be written either way round, and the cases keep
/// the order of the "or".
pub fn check_cases_cited(report: &mut Report, thm: &Theorem, known: &Known) {
    for owner in &thm.steps {
        if !owner.just.head.is(Method::Cases) {
            continue;
        }
        // The line split is the first the step cites that is not a define;
        // a define cited beside it reads its name (What a cited line says).
        let cited = owner
            .just
            .refs
            .iter()
            .find(|r| !names_define(thm, r))
            .or(owner.just.refs.first());
        let Some(cited) = cited else {
            continue;
        };
        // A reference to nothing is `check_references`'s to report.
        let scope = known.scope(owner);
        let Some(said) = scope.get(cited) else {
            continue;
        };
        let mut parts: Vec<_> = owner
            .openers
            .iter()
            .filter(|o| o.kind == Intro::Assume && o.part.is_some() && !o.after_by)
            .collect();
        if parts.is_empty() {
            continue;
        }
        parts.sort_by_key(|o| o.part);
        // Each assumption as one formula, and those joined by "or".
        let assumed: Option<Vec<Node>> = parts
            .iter()
            .map(|o| known.whole_as_written(&o.body(&thm.path)))
            .collect();
        let want = assumed.and_then(|a| disjoined(known.env.g, a));
        let Some(want) = want else {
            continue;
        };
        if !known.reads(said) {
            continue;
        }
        // The line as a whole (`SYNTAX.md`, `cases`): its one sentence, or
        // that sentence read at a block's letter, or its sentences joined.
        let says = known.says(said, &known.citing_step(owner));
        let sentences = says
            .iter()
            .filter(|s| matches!(s.from, SaidFrom::Sentence(_)))
            .count();
        let mut whole = says.iter().filter(|s| match s.from {
            SaidFrom::Whole => true,
            SaidFrom::Sentence(_) | SaidFrom::AtLetter { part: None, .. } => {
                sentences == 1
            }
            _ => false,
        });
        if !whole
            .any(|s| known.alike(&want, &s.written) || known.alike(&want, &s.cited))
        {
            report.say(
                &thm.path,
                owner.just.line,
                format!(
                    "{} takes its cases from {cited}, which does not claim their assumptions joined by \"or\", in the order the cases take them",
                    owner.called()
                ),
            );
        }
    }
}

/// Whether `label` names a define of `thm`.
pub(super) fn names_define(thm: &Theorem, label: &str) -> bool {
    thm.defines.iter().any(|d| d.label == label)
}

/// One link of a calculation: the line, with the term it continues from.
pub struct Link {
    /// The term the line before reaches, or the first line's first.
    pub from: Written,
    pub line: ChainLine,
}

impl Link {
    /// What the link claims, `from rel to`, with its modulus where the
    /// relation is a congruence, read as written; None where a part does
    /// not read, or the line's relation and modulus do not make a link,
    /// which the elaborator reports.
    pub fn claim(&self, known: &Known) -> Option<Node> {
        let read = |w: &Written| known.read_as_written(&w.formula().ok()?);
        let (from, to) = (read(&self.from)?, read(&self.line.term)?);
        let modulus = match &self.line.modulus {
            Some(n) => Some(read(n)?),
            None => None,
        };
        let at = (self.line.term.path(), self.line.line);
        let (g, sorts) = (known.env.g, &known.sorts);
        related(
            g,
            sorts,
            &self.line.relation,
            &from,
            &to,
            modulus.as_ref(),
            at,
        )
        .ok()
    }
}

/// A chain with a congruence in it says its modulus on each `≡` line and on
/// no other, says the same one on all of them, has no `≤` or `<`, since an
/// order and a congruence join into nothing, and once a line says `≡` does
/// not go back to `=` (`GRAMMAR.md`, calculation chains).
/// A notation whose definition lets its places in a number system, d and
/// n of "d divides n" in ℤ, p of "p is prime" in ℕ, a, b and n of
/// a ≡ b (mod n) in ℤ (`citing::PlaceSystems`), asks each term a step puts
/// there to be in that system: said once, by a line the step names, or
/// beside one in an equation such a line says
/// (`methods::membership::atom_held`). A chain that says ≡ joins all its
/// terms into one congruence, so each of them is asked an integer, as an
/// order's chain has its atoms real (`check_transitivity`). Each step shows
/// its own terms, a backend reading a step by the lines it names: a term a
/// cited line holds at such a place is asked again. A step citing an item
/// claims what the item concludes, whose `let` lines ask it; and a step
/// that only reads its lines again (`restates`) puts no new term anywhere. a^(p − 1) ≡ 1 (mod p) of a ∈ ℤ and p ∈ ℕ, reached by
/// substitution, asks a line saying p − 1 ∈ ℕ₀.
pub fn check_place_systems(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    library: &Library,
) {
    for step in &thm.steps {
        for a in places_at(step, known, library).unshown {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "nothing says {} ∈ {}, which step {} puts where its notation asks one",
                    known.print(&a.term),
                    a.system.sign(),
                    step.number
                ),
            );
        }
    }
}

/// The terms a step puts where a notation asks a number system
/// (`check_place_systems`): those it shows are in it, each with how, and
/// those it does not, each once.
pub struct PlacesAt {
    pub shown: Vec<super::super::record::PlaceShown>,
    pub(super) unshown: Vec<PlaceAsked>,
}

/// `PlacesAt` of one step; none for a step the rule asks nothing of.
pub fn places_at(step: &Step, known: &Known, library: &Library) -> PlacesAt {
    let mut out = PlacesAt {
        shown: Vec::new(),
        unshown: Vec::new(),
    };
    let places = library.place_systems();
    {
        if step.just.cited_item().is_some() || restates(step) {
            return out;
        }
        let Some(claimed) = known.whole_as_written(&step.claim) else {
            return out; // `check_formulas` says it does not read
        };
        // A name a define in scope gives a term is that term, b of `let b =
        // ∏(r ∈ S) r` (`SYNTAX.md`, a defined name is what it names), cited
        // or not: a substitution carries the name where its lines write it.
        // A function's define keeps its name, typed as its kind says.
        let defined = known.citing(&terms_defined_in_scope(step, known));
        let claimed = known.as_cited(&claimed, &defined);
        let links = chain_links(&step.just, &known.thm.path);
        let mut asked = Vec::new();
        let mut lines = Vec::new();
        let mut line_of = Vec::new();
        if links.is_empty() {
            places_asked(
                &claimed,
                step.openers.is_empty(),
                &places,
                &library.ctx,
                &mut asked,
            );
            let into = step.just.into.as_ref().map(|p| p.named().to_string());
            for (i, r) in step.just.refs.iter().chain(into.as_ref()).enumerate() {
                for said in cited_says(step, r, known) {
                    lines.push(said);
                    line_of.push(i);
                }
            }
        } else {
            for l in links.iter().filter_map(|l| l.claim(known)) {
                places_asked(&l, false, &places, &library.ctx, &mut asked);
            }
            if links.iter().any(|l| l.line.relation == "≡") {
                let read = |w: &Written| known.read_as_written(&w.formula().ok()?);
                let terms = links
                    .first()
                    .and_then(|l| read(&l.from))
                    .into_iter()
                    .chain(links.iter().filter_map(|l| read(&l.line.term)));
                asked.extend(terms.map(|term| PlaceAsked {
                    term,
                    system: System::Z,
                }));
            }
            for (i, l) in links.iter().enumerate() {
                for said in cited_says(step, &l.line.cite, known) {
                    lines.push(said);
                    line_of.push(i);
                }
            }
        }
        if asked.is_empty() {
            return out;
        }
        let read = ClosureRead::new(claimed, lines, line_of);
        let held = MembershipIn::of(&ClosureClaim::step(step), &read, known);
        let given = held.given(&library.targets, known);
        for a in asked {
            let once =
                |s: &PlaceAsked| s.system == a.system && known.alike(&s.term, &a.term);
            let shown_once = |s: &super::super::record::PlaceShown| {
                s.system == a.system && known.alike(&s.term, &a.term)
            };
            if out.unshown.iter().any(once) || out.shown.iter().any(shown_once) {
                continue;
            }
            use super::super::record::{PlaceShown, ShownBy};
            use methods_membership::Held;
            match methods_membership::atom_held_by(&a.term, a.system, &given) {
                Some(Held::Said) => out.shown.push(PlaceShown {
                    term: a.term,
                    system: a.system,
                    by: ShownBy::Said,
                }),
                Some(Held::Beside(b)) => out.shown.push(PlaceShown {
                    by: ShownBy::Beside(super::super::record::Besides::of(&b)),
                    term: a.term,
                    system: a.system,
                }),
                None => out.unshown.push(a),
            }
        }
    }
    out
}

/// The labels of the defines in scope at `step` that name a term and say
/// no kind of number: `let b = ∏(r ∈ S) r`, and not `let f(a) = …` or `let
/// p = k + 1, a positive integer`, whose name is in its kind's system as a
/// letter is.
pub(super) fn terms_defined_in_scope(step: &Step, known: &Known) -> Vec<String> {
    let thm = known.thm;
    thm.defines
        .iter()
        .enumerate()
        .filter(|(i, _)| known.shape().define_in_scope(thm, *i, step))
        .filter(|(_, d)| {
            matches!(crate::corpus::define_parts(&d.text),
                Built(crate::corpus::DefineParts::One(one))
                    if one.params.is_empty() && one.kind.is_none())
        })
        .map(|(_, d)| d.label.clone())
        .collect()
}

/// A term put at a place of a notation, and the number system the place
/// is in.
pub(super) struct PlaceAsked {
    pub(super) term: Node,
    pub(super) system: System,
}

/// Every term `claim` puts at a place `places` gives a number system,
/// with that system. A term holding a letter a binder in the claim binds
/// speaks of what no fact of the step can, and is left out, but for the
/// member of a step said of every member (`at_member`), whose facts put it
/// in its set.
pub(super) fn places_asked(
    claim: &Node,
    at_member: bool,
    places: &crate::citing::PlaceSystems,
    ctx: &crate::matching::Context,
    out: &mut Vec<PlaceAsked>,
) {
    let body = match (at_member, claim.notation(), claim.children.as_slice()) {
        (true, FOR_ALL, [_, _, body]) => body,
        _ => claim,
    };
    let mut bound = BTreeSet::new();
    super::super::citations::letters_bound(body, ctx, &mut bound);
    for node in body.walk() {
        let Some(systems) = places.get(&node.notation()) else {
            continue;
        };
        for (term, system) in node.children.iter().zip(systems.iter()) {
            if let (Some(system), true) = (system, term.names().is_disjoint(&bound)) {
                out.push(PlaceAsked {
                    term: term.clone(),
                    system: *system,
                });
            }
        }
    }
}

/// Whether a step's claim is what the lines it names say, read again and
/// putting no new term anywhere: a line read at a value (`instantiate`),
/// a line said again (`restate`), lines put together (`join`), the names a
/// "there is" line gives (`obtain`), or what its cases or its block show,
/// whose own lines are checked where they stand.
pub(super) fn restates(step: &Step) -> bool {
    [
        Method::Instantiate,
        Method::Restate,
        Method::Obtain,
        Method::Join,
        Method::Cases,
        Method::Proof,
        Method::Induction,
        Method::BothDirections,
        Method::Contradiction,
    ]
    .into_iter()
    .any(|m| step.just.head.is(m))
}

pub fn check_chain_congruences(report: &mut Report, thm: &Theorem) {
    for step in &thm.steps {
        let links = chain_links(&step.just, &thm.path);
        let mut said: Option<&str> = None;
        for Link { line: link, .. } in &links {
            if said.is_some() && link.relation == "=" {
                report.say(
                    &thm.path,
                    link.line,
                    format!(
                        "a link of step {} says = after a congruence; once a chain says ≡ every line after says ≡",
                        step.number
                    ),
                );
            }
            let modulus = link.modulus.as_ref().map(Written::text);
            match (link.relation.as_str(), modulus) {
                ("≡", None) => report.say(
                    &thm.path,
                    link.line,
                    format!(
                        "a link of step {} says ≡ and not what modulo; write it after the term, as (mod n)",
                        step.number
                    ),
                ),
                ("≡", Some(n)) => match said {
                    Some(first) if first != n => report.say(
                        &thm.path,
                        link.line,
                        format!(
                            "a link of step {} is a congruence modulo {n}, and an earlier one modulo {first}; a chain's congruences are modulo one number",
                            step.number
                        ),
                    ),
                    _ => said = Some(n),
                },
                (_, Some(n)) => report.say(
                    &thm.path,
                    link.line,
                    format!(
                        "a link of step {} says (mod {n}) after a relation that is not ≡",
                        step.number
                    ),
                ),
                _ => {}
            }
        }
        let ordered = links
            .iter()
            .any(|l| ["≤", "<", "≥", ">"].contains(&l.line.relation.as_str()));
        if said.is_some() && ordered {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {} joins a congruence with an order, and the two join into nothing",
                    step.number
                ),
            );
        }
    }
}

/// Each link of a calculation, as the skeleton cuts it (`corpus::chain`):
/// the first line's from its first term, each later one's from the term
/// the line before reaches. A chain whose first line names no relation is
/// the elaborator's to report, and has no links here.
pub fn chain_links(just: &Justification, path: &str) -> Vec<Link> {
    let Some(Ok(chain)) = chain(just, path) else {
        return Vec::new();
    };
    let mut from = chain.start;
    let mut out = Vec::new();
    for line in chain.lines {
        let next = line.term.clone();
        out.push(Link { from, line });
        from = next;
    }
    out
}

/// Whether two terms differ only in pieces with no letter in them.
///
/// `2/1 − 2/(n + 1)` and `2 − 2/(n + 1)` differ in `2/1` against `2`, and a
/// chain link between them uses that fact and no other. The terms are walked
/// in step; where they part, both pieces must be numerals alone.
pub(super) fn changed_closed(link: &Link, known: &Known) -> bool {
    let read = |term: &Written| known.read_as_written(&term.formula().ok()?);
    let (Some(one), Some(other)) = (read(&link.from), read(&link.line.term)) else {
        return false;
    };
    fn alike(a: &Node, b: &Node) -> bool {
        if a.spelt_alike(b) {
            return true;
        }
        if a.names().is_empty() && b.names().is_empty() {
            return true;
        }
        if a.notation() != b.notation()
            || a.text != b.text
            || a.children.len() != b.children.len()
        {
            return false;
        }
        a.children
            .iter()
            .zip(b.children.iter())
            .all(|(x, y)| alike(x, y))
    }
    alike(&one, &other)
}

/// What `arithmetic` claims holds when it is worked out (`METHODS.md`,
/// arithmetic): a step's claim and a requires line's fact of numerals alone
/// are decided (`methods::field::decide_closed`), and one that is false, or
/// asks a value that is no number, is reported. A claim with a letter in it
/// is not decided here, and `check_closed_arithmetic` says where it may not
/// stand.
pub fn check_arithmetic_holds(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    let shown = |fact: &Written| match arithmetic_worked(fact, known, targets) {
        Worked::Holds => Shown::Holds,
        Worked::Fails(why) => Shown::Unshown(why),
        Worked::Undecided => Shown::Unread(ARITHMETIC_UNREAD.to_string()),
    };
    for step in &thm.steps {
        check_shown_by(report, thm, step, Method::Arithmetic, &shown);
        // A link naming `arithmetic` changes pieces of numerals alone
        // (`check_closed_arithmetic`), each one equal to what it becomes.
        for link in chain_links(&step.just, &thm.path) {
            if link.line.cite != "arithmetic" {
                continue;
            }
            if let Some(why) = link_pieces_unworked(&link, known, targets) {
                report.say(
                    &thm.path,
                    link.line.line,
                    format!(
                        "a link of step {} names arithmetic for {}, which {why}",
                        step.number,
                        link.line.quoted(&link.from)
                    ),
                );
            }
        }
    }
}

/// Why `arithmetic` does not show a fact a line gives it as a reason, a
/// requires line's or a let's: it is false or has no value, or it is not a
/// fact of numerals alone, which is all arithmetic decides. None where it
/// holds.
pub(super) fn arithmetic_unshown(
    fact: &Written,
    known: &Known,
    targets: &Targets,
) -> Option<String> {
    match arithmetic_worked(fact, known, targets) {
        Worked::Holds => None,
        Worked::Fails(why) => Some(why),
        Worked::Undecided => Some(ARITHMETIC_UNREAD.to_string()),
    }
}

/// Why `arithmetic` does not show a fact that is not of numerals alone.
pub(super) const ARITHMETIC_UNREAD: &str =
    "is not a fact about numerals alone, and arithmetic decides nothing else";

/// What a method working out closed facts, `arithmetic` or `real
/// arithmetic`, says of one.
pub(super) enum Shown {
    Holds,
    /// It does not hold, or is not the method's, and why.
    Unshown(String),
    /// It is no fact the method reads, which a step leaves undecided and a
    /// requires line is told, and why.
    Unread(String),
}

/// A step whose reason is `method`, and each requires line of it naming
/// `method`, by what the method says of each fact (`shown`): a step's claim
/// it does not read is undecided, and any fact it does not show is reported
/// with why.
pub(super) fn check_shown_by(
    report: &mut Report,
    thm: &Theorem,
    step: &Step,
    method: Method,
    shown: &dyn Fn(&Written) -> Shown,
) {
    if step.just.head.is(method) {
        match shown(&step.claim) {
            Shown::Holds => {}
            Shown::Unread(_) => report.undecided(&thm.path, method, step),
            // A line marked impossible is reached by its reasons from the
            // lines they cite, and the marker is what finds it false
            // (`SYNTAX.md`, contradiction): the method as its reason proves
            // only what is true, and cites nothing to reach it from.
            Shown::Unshown(_) if step.impossible => report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} is marked impossible and gives {} as its reason, which proves only what is true; a line marked impossible is reached by its reasons from the lines they cite",
                    step.number,
                    method.as_str()
                ),
            ),
            Shown::Unshown(why) => report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} claims {}, which {why}",
                    step.number,
                    step.claim_text()
                ),
            ),
        }
    }
    for req in &step.requires {
        if !req.is(method) {
            continue;
        }
        if let Shown::Unshown(why) | Shown::Unread(why) = shown(&req.fact) {
            report.say(
                &thm.path,
                req.line,
                format!(
                    "the requires line {} of {} is {}, which {why}",
                    req.fact,
                    step.called(),
                    method.as_str()
                ),
            );
        }
    }
}

/// Each step giving `algebra` or `inequalities` for a claim, and each
/// requires line giving one of them for a fact, that `method` works out
/// (`worked_out`, true or false where it decides every sentence): a true
/// one cites `method`, and a false one is stated only by a line marked
/// impossible, which states a false fact its method reaches from the lines
/// it cites and which `method` would refuse (`METHODS.md`, arithmetic,
/// Boundary).
pub(super) fn check_closed_by(
    report: &mut Report,
    thm: &Theorem,
    method: Method,
    worked_out: &dyn Fn(&Written) -> Option<bool>,
) {
    let name = method.as_str();
    let why = |holds: bool, what: &str| {
        if holds {
            format!(
                "which {name} can work out; a {what} {name} can work out cites {name}"
            )
        } else {
            format!(
                "which {name} finds false; a false {what} with no letter is stated only by the last line of a contradiction, marked impossible"
            )
        }
    };
    for step in &thm.steps {
        let just = &step.just;
        if (just.head.is(Method::Algebra) || just.head.is(Method::Inequalities))
            && !step.impossible
        {
            if let Some(holds) = worked_out(&step.claim) {
                report.say(
                    &thm.path,
                    just.line,
                    format!(
                        "step {} gives {} for {}, {}",
                        step.number,
                        just.head,
                        step.claim_text(),
                        why(holds, "claim")
                    ),
                );
            }
        }
        for req in &step.requires {
            let Some(given) = [Method::Algebra, Method::Inequalities]
                .into_iter()
                .find(|m| req.is(*m))
            else {
                continue;
            };
            if let Some(holds) = worked_out(&req.fact) {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of {} gives {} for {}, {}",
                        step.called(),
                        given.as_str(),
                        req.fact,
                        why(holds, "fact")
                    ),
                );
            }
        }
    }
}

/// Why a link naming `arithmetic` does not hold where it is worked out: a
/// link of numerals alone is false or has no value; an equation's each
/// piece of numerals alone it changes, said equal to what it becomes, is.
/// A link of another relation with a letter in it is not worked out here:
/// its pieces need not be equal, `x + 2 < x + 3`, nor a congruence's. None
/// where it holds, or a side does not read, which the elaborator reports.
pub(super) fn link_pieces_unworked(
    link: &Link,
    known: &Known,
    targets: &Targets,
) -> Option<String> {
    let unworked = |fact: &Node| -> Option<String> {
        match decide_closed(&term_of_node(&written_out(fact, known), targets)) {
            Built(Verdict::Holds(false)) => {
                Some(format!("is false: {}", known.print(fact)))
            }
            Built(Verdict::Unworked(why)) => Some(why.to_string()),
            _ => None,
        }
    };
    let claim = link.claim(known)?;
    if claim.names().is_empty() {
        return unworked(&claim);
    }
    let (EQUALITY, [one, other]) = (claim.notation(), claim.children.as_slice()) else {
        return None;
    };
    let mut pieces = Vec::new();
    closed_pieces(one, other, known, &mut pieces);
    pieces.into_iter().find_map(|Piece { was, now }| {
        unworked(&made(known.env.g, EQUALS, vec![was, now]))
    })
}

/// The operations `arithmetic` does not work out (`operations`, false) that
/// a link naming it works out: those of what it changes, where a part both
/// sides build by one operation alike is not worked out, only what is
/// changed inside it. So 2! = (1 + 1)! works out 1 + 1 and no factorial,
/// and (1 + 1)! = 2 works the factorial out.
pub(super) fn link_undecided(
    one: &Node,
    other: &Node,
    known: &Known,
    operations: &IndexMap<NotationId, bool>,
    out: &mut BTreeSet<String>,
) {
    if known.alike(one, other) {
        return;
    }
    let undecided = |n: &Node| operations.get(&n.notation()) == Some(&false);
    if one.notation() == other.notation()
        && one.text == other.text
        && one.children.len() == other.children.len()
    {
        for (a, b) in one.children.iter().zip(&other.children) {
            link_undecided(a, b, known, operations, out);
        }
        return;
    }
    for side in [one, other] {
        out.extend(
            side.walk()
                .into_iter()
                .filter(|n| undecided(n))
                .map(|n| n.notation_name().to_string()),
        );
    }
}

/// A piece of numerals alone a link changes, and what it becomes.
pub(super) struct Piece {
    pub(super) was: Node,
    pub(super) now: Node,
}

/// The pieces of numerals alone where `one` and `other` differ, walking
/// both where they are built alike.
pub(super) fn closed_pieces(
    one: &Node,
    other: &Node,
    known: &Known,
    out: &mut Vec<Piece>,
) {
    if known.alike(one, other) {
        return;
    }
    if one.names().is_empty() && other.names().is_empty() {
        out.push(Piece {
            was: one.clone(),
            now: other.clone(),
        });
        return;
    }
    if one.notation() == other.notation()
        && one.text == other.text
        && one.children.len() == other.children.len()
    {
        for (a, b) in one.children.iter().zip(&other.children) {
            closed_pieces(a, b, known, out);
        }
    }
}

/// What `algebra` claims holds (`METHODS.md`, algebra): a step's claim of
/// one sentence is an identity of the field, or follows from the equations
/// the lines it cites say, added and subtracted with at most one multiplied
/// by a term, or is a disequality it cites rescaled
/// (`methods::algebra::decide`). Each is read with the defines the step
/// cites written out, as kernel terms (`term_of_node`), and a finite sum
/// read as linear where some term of the step is linear in something, as
/// the build reads it, and as one atom where none is.
pub fn check_algebra_holds(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in &thm.steps {
        if step.just.head.is(Method::Algebra) {
            if let Some(order) = cited_chain(thm, step, known) {
                let said = match order.as_slice() {
                    [one] => format!(
                        "step {} says an equation {one} says, which is `restate {one}`, not algebra",
                        step.number
                    ),
                    _ => format!(
                        "step {} chains the equations it cites, which is `transitivity, from {}`, not algebra",
                        step.number,
                        order.join(", ")
                    ),
                };
                report.say(&thm.path, step.just.line, said);
                continue;
            }
            let decided =
                algebra_holds(report, thm, &ClosureClaim::step(step), known, targets);
            if !decided {
                report.undecided(&thm.path, Method::Algebra, step);
            }
        }
        for req in step.requires.iter().filter(|r| r.is(Method::Algebra)) {
            let decided = algebra_holds(
                report,
                thm,
                &ClosureClaim::requires(step, req),
                known,
                targets,
            );
            if !decided {
                report.undecided_requires(&thm.path, Method::Algebra, step, req);
            }
        }
    }
}

/// The lines an `algebra` step cites in an order that chains them from one
/// side of its equation to the other (`METHODS.md`, algebra, Refusals),
/// each line by one equation it says, a define of a name by the equation it
/// gives; None where they make no such chain. A step whose claim is such a
/// chain is a `transitivity` or a calculation, or of one line a `restate`,
/// and combines nothing.
pub(super) fn cited_chain(
    thm: &Theorem,
    step: &Step,
    known: &Known,
) -> Option<Vec<String>> {
    let claim = known
        .whole_as_written(&step.claim)
        .as_ref()
        .and_then(Related::of)
        .filter(|c| c.rel == Rel::Eq)?;
    if step.just.refs.is_empty() {
        return None;
    }
    let mut links: Vec<Vec<Related>> = Vec::new();
    for r in &step.just.refs {
        let mut equations: Vec<Related> = line_relations(step, r, known)
            .into_iter()
            .filter(|l| l.rel == Rel::Eq)
            .collect();
        equations.extend(
            define_equation(thm, step, r, known)
                .as_ref()
                .and_then(Related::of),
        );
        if equations.is_empty() {
            return None;
        }
        links.push(equations);
    }
    let mut used: Vec<usize> = Vec::new();
    if !chain_order(&claim.left, &claim.right, &links, &mut used, known) {
        return None;
    }
    Some(used.iter().map(|&i| step.just.refs[i].clone()).collect())
}

/// Whether every link not yet `used` can be taken, one equation of each, in
/// an order going from `at` to `end`, each link's side meeting the term the
/// one before ends at, written the same way; `used` holds the order found.
pub(super) fn chain_order(
    at: &Node,
    end: &Node,
    links: &[Vec<Related>],
    used: &mut Vec<usize>,
    known: &Known,
) -> bool {
    if used.len() == links.len() {
        return known.alike(at, end);
    }
    for (i, equations) in links.iter().enumerate() {
        if used.contains(&i) {
            continue;
        }
        for link in equations {
            let next = if known.alike(at, &link.left) {
                &link.right
            } else if known.alike(at, &link.right) {
                &link.left
            } else {
                continue;
            };
            used.push(i);
            if chain_order(next, end, links, used, known) {
                return true;
            }
            used.pop();
        }
    }
    false
}

/// `check_algebra_holds` of one claim; whether it was decided, the build
/// left to decide one that was not.
pub(super) fn algebra_holds(
    report: &mut Report,
    thm: &Theorem,
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> bool {
    let Some(AlgebraDecided {
        read,
        facts,
        verdict,
        ..
    }) = algebra_decided(at, known, targets)
    else {
        return false;
    };
    let labels = FloatLabels::new(IndexMap::new());
    let shown: Vec<&Node> = std::iter::once(&read.claimed).chain(&read.lines).collect();
    let render = |t: &Term| printed(t, &shown, known, targets, &labels);
    let step = at.step.called();
    if let Some(said) =
        algebra::refusal(&verdict, &at.claim.to_string(), &step, &render)
    {
        report.say(&thm.path, at.line, at.said(said));
        return true;
    }
    if let algebra::Verdict::Holds { combined } = &verdict {
        if let Some(said) = algebra_unsaid(at, &read, &facts, combined, known, targets)
        {
            report.say(&thm.path, at.line, at.said(said));
        }
    }
    !matches!(verdict, algebra::Verdict::Undecided)
}
