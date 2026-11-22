//! Recursions cited, joins, function types and codomains.

use super::*;
use crate::citing;
use crate::corpus::{proof, DefineLine, Recursion};
use crate::formula::page::chain_links;
use crate::formula::Sorts;
use crate::methods::membership;
use crate::methods::membership::Range;

/// A theorem stated over a sequence it defines by recursion speaks of that
/// sequence, and a step citing it speaks of its own sequence of the name,
/// as the build reads it (`Elaborator::in_its_names`). The citation holds
/// only where the two are one recursion: the same names in the same order,
/// each with the same value at 0 and the same rule at k + 1, once the
/// letters the citation fills are put in and the index is read as the
/// citing define's. Otherwise what the theorem says is about another
/// sequence.
pub fn check_recursions_cited(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        let mut citations: Vec<(usize, String, Option<Cited>)> = Vec::new();
        if let Some(named) = step.just.cited_item() {
            citations.push((step.just.line, named, cited(step, library, known)));
        }
        for req in &step.requires {
            if let Some((named, _)) = req.cited_item() {
                let read = cited_requires(step, req, library, known);
                citations.push((req.line, named, read));
            }
        }
        // A citation no group reads is `check_conclusion`'s and
        // `check_requires`'s to report.
        for (line, named, read) in citations {
            let Some(read) = read else {
                continue;
            };
            let (Some(Item::Theorem(other)), Some(sorts)) =
                (library.item(&read.item), library.proved_sorts(&read.item))
            else {
                continue;
            };
            for (theirs_line, theirs) in other.stated_recursions() {
                let theirs_at = (theirs_line, &theirs);
                if let Some(why) = recursion_differs(
                    thm,
                    other,
                    sorts,
                    theirs_at,
                    &read.binding,
                    known,
                ) {
                    report.say(
                        &thm.path,
                        line,
                        format!(
                            "step {} cites {named}, which is stated over {}, defined by recursion there; {why}",
                            step.number,
                            theirs.names.join(", ")
                        ),
                    );
                }
            }
        }
    }
}

/// The define by recursion of `thm` that gives the first of the sequences
/// `theirs` gives, with its parts; None where it has none.
pub(super) fn our_recursion<'t>(
    thm: &'t Theorem,
    theirs: &Recursion,
) -> Option<(&'t DefineLine, Recursion)> {
    thm.defines
        .iter()
        .find_map(|d| match define_parts(&d.text) {
            Built(DefineParts::Recursion(r)) if r.names.contains(&theirs.names[0]) => {
                Some((d, r))
            }
            _ => None,
        })
}

/// Each recursion the theorem a citation names is stated over, by the
/// label of its define, with the define of the citing proof that is the
/// same recursion (`recursion_differs`), by its label (`Cited::recursions`).
/// One the citing proof has none the same of is `check_recursions_cited`'s
/// to report.
pub(super) fn recursions_met(
    read: &Cited,
    known: &Known,
    library: &Library,
) -> IndexMap<String, String> {
    let (Some(Item::Theorem(other)), Some(sorts)) =
        (library.item(&read.item), library.proved_sorts(&read.item))
    else {
        return IndexMap::new();
    };
    let thm = known.thm;
    let mut out = IndexMap::new();
    for (theirs_line, theirs) in other.stated_recursions() {
        let same = recursion_differs(
            thm,
            other,
            sorts,
            (theirs_line, &theirs),
            &read.binding,
            known,
        )
        .is_none();
        let theirs_define = other.defines.iter().find(|d| d.line == theirs_line);
        if let (true, Some(t), Some((o, _))) =
            (same, theirs_define, our_recursion(thm, &theirs))
        {
            out.insert(t.label.clone(), o.label.clone());
        }
    }
    out
}

/// How the citing proof's sequences differ from those `theirs`, a define by
/// recursion of the theorem `other` on its line `theirs_line`, read with
/// `sorts`, gives: in the names, or in the first value or rule that is not
/// the same once `binding` is put in and the index renamed. None where they
/// are one recursion.
pub(super) fn recursion_differs(
    thm: &Theorem,
    other: &Theorem,
    sorts: &Sorts,
    (theirs_line, theirs): (usize, &Recursion),
    binding: &Binding,
    known: &Known,
) -> Option<String> {
    let Some((define, ours)) = our_recursion(thm, theirs) else {
        return Some(format!(
            "this proof defines no {} by recursion",
            theirs.names[0]
        ));
    };
    let label = &define.label;
    if ours.names != theirs.names {
        return Some(format!(
            "{label} here gives {}, and the theorem's define gives {}",
            ours.names.join(", "),
            theirs.names.join(", ")
        ));
    }
    let g = known.env.g;
    let mut theirs_local = sorts.clone();
    theirs_local.insert(theirs.index.clone(), Sort::of("number"));
    let mut ours_local = known.sorts.clone();
    ours_local.insert(ours.index.clone(), Sort::of("number"));
    let mut put = binding.clone();
    put.insert(
        Symbol::of(&theirs.index),
        Node::name(Sort::of("number"), &ours.index),
    );
    for (rules_theirs, rules_ours, at) in [
        (&theirs.start, &ours.start, None),
        (&theirs.step, &ours.step, Some(&ours.index)),
    ] {
        for name in &ours.names {
            let (Some(a), Some(b)) = (rules_theirs.get(name), rules_ours.get(name))
            else {
                continue;
            };
            // A rule that does not read is `check_recursions`'s to report, in
            // the theorem that writes it.
            let read = |rule: Written, local: &Sorts| {
                rule.formula().and_then(|s| s.read(g, local))
            };
            let (Ok(a_tree), Ok(b_tree)) = (
                read(a.written(&other.path, theirs_line), &theirs_local),
                read(b.written(&thm.path, define.line), &ours_local),
            ) else {
                continue;
            };
            let a_tree = substitute_apart(&a_tree, &put, known.ctx);
            // The rules as written, not as alike: a sequence by recursion is
            // the term its rules build, and F(k) + 1 + 0 builds another term
            // than F(k) + 1, which the kernel will not fit to it.
            let as_written = |t: &Node| standard(t, known.ctx);
            if !as_written(&a_tree).spelt_alike(&as_written(&b_tree)) {
                let place = match at {
                    None => format!("{name}(0)"),
                    Some(k) => format!("{name}({k} + 1)"),
                };
                return Some(format!(
                    "there {place} is {}, and {label} here says it is {}",
                    known.print(&a_tree),
                    str::trim(b.text())
                ));
            }
        }
    }
    None
}

/// A definition folded from what its "there is" says of a witness is about
/// one letter, its subject, and with no pair for it the subject is the
/// proof's letter of the same name (`SYNTAX.md`, "No pair says what goes
/// without saying"): `def:odd, from H3`, where odd is about n and the proof
/// has an N and no n, writes `n := N`. A definition is folded so where its
/// right side is a "there is", the claim is not one, and no line the step
/// names is one, as the elaborator reads it too (`Elaborator::reading`,
/// `subject_given`).
pub fn check_subjects(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    let shape = super::super::record::CheckedTheorem::of(thm);
    for step in &thm.steps {
        let just = &step.just;
        if !just.head.is_item() || just.head.is(Method::Obtain) {
            continue;
        }
        let name = just.item(&just.head.to_string());
        let Some(Item::Record(record)) = library.item(&name) else {
            continue;
        };
        if !record.kind.unfolds() {
            continue;
        }
        let Some(whole) = library
            .groups(&name)
            .and_then(|groups| groups.first().and_then(|g| g.gives.first().cloned()))
        else {
            continue;
        };
        let [left, right] = whole.children.as_slice() else {
            continue;
        };
        if !library.bicond.contains(&whole.notation())
            || !library.exists.contains(&right.notation())
        {
            continue;
        }
        let parts = known.read_out_parts(step, library);
        let refs: Vec<&str> = just.refs.iter().map(String::as_str).collect();
        let cites_one = known
            .lines_say(step, &refs)
            .iter()
            .any(|n| library.exists.contains(&n.notation()));
        let claims_one = parts
            .claims
            .iter()
            .any(|n| library.exists.contains(&n.notation()));
        if cites_one || claims_one || parts.claims.is_empty() {
            continue;
        }
        let subject = left.leftmost();
        let letter = subject.text;
        if !subject.is_name() || just.values.names().any(|n| n == letter) {
            continue;
        }
        // The proof's letter of the same name is one in scope at the step,
        // which is the letter the build gives the subject.
        let in_scope = letters_in_scope(thm, &shape, step, known);
        if !in_scope.contains(letter.as_str()) {
            report.say(
                &thm.path,
                just.line,
                format!(
                    "{} is about {letter}, and the step gives {letter} no value and the proof has no {letter}; write it, as {letter} := t",
                    just.head
                ),
            );
        }
    }
}

/// Where each part of each `join` step's claim stands among the lines it
/// cites (`CheckedTheorem::joined`): for each sentence of the claim, each
/// of its parts joined by "and", by `fact_at` over the step's references,
/// as `check_joins` matches them; a part said with a define's name the step
/// cites, where the line states it with the name written out. A `restate`
/// whose claim has several sentences is read as a join is. A step with a
/// part no one line states is left out.
pub fn join_places(
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> IndexMap<usize, Vec<Vec<FirstAt>>> {
    let mut out = IndexMap::new();
    for step in thm.steps.iter().filter(|s| puts_parts_together(s)) {
        let placed = step
            .claim
            .sentences()
            .iter()
            .map(|s| {
                let sentence = known.read_as_written(s)?;
                conjuncts(&sentence, library)
                    .iter()
                    .map(|part| {
                        let standard_part = standard(part, &library.ctx);
                        fact_at(
                            step,
                            &step.just.refs,
                            None,
                            &standard_part,
                            known,
                            library,
                        )
                        .or_else(|| {
                            // A part said with a define's name the step
                            // cites, read with the name written out, as
                            // `check_joins` compares it.
                            let defined = known.citing_step(step);
                            let written_out = known.as_cited(part, &defined);
                            fact_at(
                                step,
                                &step.just.refs,
                                None,
                                &written_out,
                                known,
                                library,
                            )
                        })
                    })
                    .collect::<Option<Vec<FirstAt>>>()
            })
            .collect::<Option<Vec<_>>>();
        if let Some(placed) = placed {
            out.insert(step.just.line, placed);
        }
    }
    out
}

/// Of each `join` step, each run of its claim's parts that one line it cites
/// states whole (`CheckedTheorem::joined_wholes`): a sentence of several
/// parts, or an "and" of several within one, as the claim groups them, by
/// the place of its first part among the claim's parts, counted across its
/// sentences as `join_places` counts them.
pub fn join_wholes(
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> IndexMap<usize, Vec<JoinedWhole>> {
    let mut out = IndexMap::new();
    for step in thm.steps.iter().filter(|s| puts_parts_together(s)) {
        let mut found = Vec::new();
        let mut first = 0;
        for s in step.claim.sentences() {
            let Some(sentence) = known.read_as_written(&s) else {
                break;
            };
            first += whole_groups(step, &sentence, first, library, known, &mut found);
        }
        if !found.is_empty() {
            out.insert(step.just.line, found);
        }
    }
    out
}

/// Whether a step's claim is put together part by part from the lines it
/// cites (`join_places`): a `join`, or a `restate` whose claim has several
/// sentences, which `restatements` does not place whole.
fn puts_parts_together(step: &Step) -> bool {
    step.just.head.is(Method::Join)
        || (step.just.head.is(Method::Restate) && step.claim.sentences().len() > 1)
}

/// Of each `join` step, each part of its claim as the page writes it, in
/// the order `join_places` places them (`CheckedTheorem::joined_claim`).
pub fn join_claim_parts(
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> IndexMap<usize, Vec<Node>> {
    let mut out = IndexMap::new();
    for step in thm.steps.iter().filter(|s| puts_parts_together(s)) {
        let parts: Option<Vec<Node>> = step
            .claim
            .sentences()
            .iter()
            .map(|s| known.read_as_written(s).map(|n| conjuncts(&n, library)))
            .collect::<Option<Vec<_>>>()
            .map(|each| each.into_iter().flatten().collect());
        if let Some(parts) = parts {
            out.insert(step.just.line, parts);
        }
    }
    out
}

/// `join_wholes` of one node of a claim whose first part is part `first`:
/// each "and" within it, then the node itself, where one line states it and
/// it holds more than one part. The number of parts it holds.
fn whole_groups(
    step: &Step,
    node: &Node,
    first: usize,
    library: &Library,
    known: &Known,
    out: &mut Vec<JoinedWhole>,
) -> usize {
    let count = citing::conjuncts(node, library).len();
    let joined_by_and = chain_links(library.env.g, node).is_none()
        && library.ctx.conjunctions.contains(&node.notation())
        && node.children.len() == 2;
    if joined_by_and {
        let left = whole_groups(step, &node.children[0], first, library, known, out);
        whole_groups(step, &node.children[1], first + left, library, known, out);
    }
    if count > 1 {
        let whole = standard(node, &library.ctx);
        if let Some(at) = fact_at(step, &step.just.refs, None, &whole, known, library) {
            out.push(JoinedWhole { first, count, at });
        }
    }
    count
}

/// A `join` claims the sentences of the lines it cites put together and
/// infers nothing (`SYNTAX.md`): each sentence of its claim is one a cited
/// line says, and each cited line says one of them. They are compared as
/// formulas (`Known::alike`), and the claim may group them otherwise.
///
/// `join` cites two lines or more and `restate` one, a define read beside
/// them counting as no line (`SYNTAX.md`); otherwise the two are one check.
pub fn check_joins(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        let verb = if step.just.head.is(Method::Join) {
            "joins"
        } else if step.just.head.is(Method::Restate) {
            "restates"
        } else {
            continue;
        };
        let lines: Vec<&String> = step
            .just
            .refs
            .iter()
            .filter(|r| !thm.defines.iter().any(|d| &d.label == *r))
            .collect();
        let listed = lines
            .iter()
            .map(|r| r.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        if verb == "joins" && lines.len() == 1 {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} joins one line; a step citing one line is written `restate {}`",
                    step.number,
                    step.just.refs.join(", ")
                ),
            );
        }
        if verb == "restates" && lines.len() > 1 {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} restates {listed}; a step putting several lines together is written `join {}`",
                    step.number,
                    step.just.refs.join(", ")
                ),
            );
        }
        // Putting lines together asks nothing of them, so no requires line
        // under a join is used.
        if let Some(first) = step.requires.first() {
            report.say(
                &thm.path,
                first.line,
                format!(
                    "step {} is a {}, which asks nothing of the lines it puts together, and carries a requires line",
                    step.number,
                    step.just.head
                ),
            );
        }
        let Some(claim) = known.whole_as_written(&step.claim) else {
            continue;
        };
        let claimed = conjuncts(&claim, library);
        // A reference to nothing is `check_references`'s to report.
        let scope = known.scope(step);
        let mut cited: Vec<(&String, Vec<Node>)> = Vec::new();
        for r in &step.just.refs {
            let Some(stated) = scope.get(r).filter(|s| known.reads(s)) else {
                continue;
            };
            cited.push((r, known.writes(stated, &known.citing_step(step))));
        }
        if cited.len() != step.just.refs.len() {
            continue;
        }
        // Where the step cites a define, a name and what it names are one
        // formula (`SYNTAX.md`, A defined name and the term it names), so
        // a part and a sentence of the claim are also compared with the
        // names the step cites read out.
        let defined = known.citing_step(step);
        let alike = |p: &Node, n: &Node| {
            known.alike(p, n)
                || known
                    .alike(&known.as_cited(p, &defined), &known.as_cited(n, &defined))
        };
        let said = |n: &Node| {
            cited
                .iter()
                .any(|(_, parts)| parts.iter().any(|p| alike(p, n)))
        };
        if let Some(extra) = claimed.iter().find(|n| !said(n)) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} {verb} {} and claims {}, which no line it {verb} says",
                    step.number,
                    step.just.refs.join(", "),
                    known.print(extra)
                ),
            );
            continue;
        }
        // A define cited reads the names in the other lines, and need not
        // give a sentence of the claim itself where a sentence is said only
        // with the names read out.
        let read_out = claimed.iter().any(|n| {
            !cited
                .iter()
                .any(|(_, parts)| parts.iter().any(|p| known.alike(p, n)))
        });
        for (r, parts) in &cited {
            if read_out && thm.defines.iter().any(|d| &d.label == *r) {
                continue;
            }
            if !parts.iter().any(|p| claimed.iter().any(|n| alike(p, n))) {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} {verb} {r}, and claims nothing it says",
                        step.number
                    ),
                );
            }
        }
    }
}

/// An item's `let f : D → E` filled by a function no `let` types, `let F be
/// a function on A`, asks that type of the citation as a hypothesis, which
/// a line the step names or a requires line says (`SYNTAX.md`, a cited item
/// whose let a citation fills with a function that declares no type). A
/// function the proof defines is `check_surplus`'s and the define's to
/// read.
pub fn check_function_types(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let defines: BTreeSet<String> = defined_functions(&proof::in_scope(thm, scopes))
        .into_iter()
        .map(|f| f.name)
        .collect();
    for step in &thm.steps {
        let Some(item) = step.just.cited_item() else {
            continue;
        };
        if library.groups(&step.just.item(&item)).is_none() {
            continue;
        }
        let asks = family_asks(step, known, library);
        let cited = known.read_out_parts(step, library).facts.clone();
        codomains_unmet(report, thm, step, &item, &asks, &cited, known);
        let what = format!("step {}", step.number);
        let at = AskedAt {
            step,
            line: step.just.line,
            what: &what,
        };
        types_unstated(report, thm, &at, &asks, &defines, library, known);
        terms_unsaid(report, thm, step, step.just.line, &what, library, known);
    }
    for step in &thm.steps {
        for req in &step.requires {
            let Some(as_step) = requires_read_as_step(step, req) else {
                continue;
            };
            let named = as_step.just.cited_item().map(|c| as_step.just.item(&c));
            if !named.is_some_and(|n| library.groups(&n).is_some()) {
                continue;
            }
            let what = format!("the requires line {} of {}", req.fact, step.called());
            let asks = family_asks(&as_step, known, library);
            let at = AskedAt {
                step: &as_step,
                line: req.line,
                what: &what,
            };
            types_unstated(report, thm, &at, &asks, &defines, library, known);
            terms_unsaid(report, thm, &as_step, req.line, &what, library, known);
        }
    }
}

/// Where a citation asks what `types_unstated` looks for: the step, or a
/// requires line read as the step it would be, the line to report it on,
/// and how the report names it.
pub(super) struct AskedAt<'a> {
    pub(super) step: &'a Step,
    pub(super) line: usize,
    pub(super) what: &'a str,
}

/// Each function type a citation asks (`FamilyAsks::types`) of one of the
/// page's functions that no line it names states: of a function no `let`
/// types, its type, and of one a `let` declares on a domain that does not
/// hold the set the item asks it over, its values there. A function the
/// proof defines is `check_defined_types`'s.
pub(super) fn types_unstated(
    report: &mut Report,
    thm: &Theorem,
    at: &AskedAt,
    asks: &FamilyAsks,
    defines: &BTreeSet<String>,
    library: &Library,
    known: &Known,
) {
    let Some(item) = at.step.just.cited_item() else {
        return;
    };
    let parts = known.read_out_parts(at.step, library);
    let declared = typed_in_scope(known, at.step);
    for t in &asks.types {
        let function = &t.asked.children[0];
        if !function.is_name() || defines.contains(function.text.as_str()) {
            continue;
        }
        // A function the citation leaves the item's own letter is not one
        // of the page's, and one asked on a part of its domain is asked at
        // every point of the part (`terms_unsaid`).
        if !t.filled || t.rule.is_some() {
            continue;
        }
        if parts.facts.iter().any(|f| t.stated_by(f, known))
            || values_said(&t.asked, &parts.facts, library)
        {
            continue;
        }
        let what = at.what;
        if let Some(line) = declared
            .iter()
            .find(|d| d.children[0].text == function.text)
        {
            report.say(
                &thm.path,
                at.line,
                format!(
                    "{what} cites {item}, which asks {}, and {} is declared {}, whose domain does not hold {}; say its values there in a requires line, {}, from a line saying them",
                    known.print(&t.asked),
                    known.print(function),
                    known.print(line),
                    known.print(&t.asked.children[1]),
                    values_everywhere(&t.asked, known)
                ),
            );
            continue;
        }
        report.say(
            &thm.path,
            at.line,
            format!(
                "{what} cites {item}, which asks {}, and no line the step names gives {} a type; cite the line stating it, or say it in a requires line",
                known.print(&t.asked),
                known.print(function)
            ),
        );
    }
}

/// An item's function type asked of a function a `let` declares into a set
/// whose values need not be in the codomain asked (`citing::codomain_reason`,
/// `GRAMMAR.md`, the function's type is a declaration): product-real asks
/// `t : {a, …, b} → ℝ`, and `let t : {1, …, n} → ℂ` does not give that,
/// where `let t : {1, …, n} → ℕ` does, and so does `let f : X → X` with
/// `let X ⊆ ℤ` give f : X → ℤ. A codomain the item leaves open takes the
/// declared one, and a type a line the step cites states, `cited`, is
/// given by that line and asks nothing of the declaration.
pub(super) fn codomains_unmet(
    report: &mut Report,
    thm: &Theorem,
    step: &Step,
    item: &str,
    asks: &FamilyAsks,
    cited: &[Node],
    known: &Known,
) {
    for unmet in unmet_codomains(step, asks, cited, known) {
        report.say(
            &thm.path,
            step.just.line,
            format!(
                "step {} cites {item}, which asks {}, and {} is declared {}, whose values need not be in {}",
                step.number,
                known.print(&unmet.asked),
                known.print(&unmet.function),
                known.print(&unmet.declared),
                known.print(&unmet.codomain)
            ),
        );
    }
}

/// A function type a citation asks of a declared function whose declared
/// codomain does not give the one asked (`codomains_unmet`).
pub(super) struct UnmetCodomain {
    /// The type asked, `f : X → X`.
    pub(super) asked: Node,
    pub(super) function: Node,
    /// The type a line declares, `f : X → ℤ`.
    pub(super) declared: Node,
    /// The codomain asked, X.
    pub(super) codomain: Node,
}

/// `codomains_unmet`, each found.
pub(super) fn unmet_codomains(
    step: &Step,
    asks: &FamilyAsks,
    cited: &[Node],
    known: &Known,
) -> Vec<UnmetCodomain> {
    let mut out = Vec::new();
    let declared = typed_in_scope(known, step);
    let ask = PageCodomains {
        known,
        parts: parts_in_scope(known, step),
    };
    for t in &asks.declared_types {
        let [function, _, asked] = t.asked.children.as_slice() else {
            continue;
        };
        let open = asked.is_name() && t.open.contains(asked.text.as_str());
        // "F : A → C is one-to-one" states the type F : A → C as well.
        let stated = cited.iter().any(|f| {
            types_a_function(f)
                && f.children
                    .iter()
                    .zip(&t.asked.children)
                    .all(|(a, b)| known.alike(a, b))
        });
        if open || stated {
            continue;
        }
        let typed = declared
            .iter()
            .filter(|d| d.children[0].text == function.text)
            .filter_map(|d| d.children.get(2).map(|given| (d, given)));
        for (line, given) in typed {
            if codomain_reason(&ask, given, asked).is_some() {
                continue;
            }
            out.push(UnmetCodomain {
                asked: t.asked.clone(),
                function: function.clone(),
                declared: line.clone(),
                codomain: asked.clone(),
            });
        }
    }
    out
}

/// The page's codomains as `citing::codomain_reason` asks of them: sets as
/// the page writes them, and the parts the `let` lines in scope state.
pub(super) struct PageCodomains<'k, 'a> {
    pub(super) known: &'k Known<'a>,
    pub(super) parts: Vec<(Node, Node)>,
}

impl CodomainAsk for PageCodomains<'_, '_> {
    type T = Node;

    fn alike(&self, a: &Node, b: &Node) -> bool {
        self.known.alike(a, b)
    }

    fn system(&self, set: &Node) -> Option<System> {
        system_named(set)
    }

    fn part(&self, small: &Node, big: &Node) -> bool {
        self.parts
            .iter()
            .any(|(s, b)| self.known.alike(s, small) && self.known.alike(b, big))
    }
}

/// Whether every type `declared` gives the function of `asked` holds the
/// domain the item asks it over: the same set, a set the citation leaves
/// open, or a range the declared table puts inside a declared number
/// system, {1, …, n} inside ℕ (`SYNTAX.md`, a line said of every member of
/// a set). A function declared on {1, …, n} does not hold {1, …, 1} or
/// {1, …, j + 1} by its type alone.
pub(super) fn declared_domain_holds(
    asked: &AskedType,
    declared: &[Node],
    known: &Known,
) -> bool {
    let [function, domain, _] = asked.asked.children.as_slice() else {
        return true;
    };
    if domain.is_name() && asked.open.contains(domain.text.as_str()) {
        return true;
    }
    let inside = match domain.notation() {
        INTEGER_RANGE => range_system(domain),
        NUMBER_SYSTEMS => System::of_sign(&domain.text),
        _ => None,
    };
    declared
        .iter()
        .filter(|d| d.children[0].text == function.text)
        .all(|d| {
            let own = &d.children[1];
            known.alike(own, domain)
                || system_named(own)
                    .zip(inside)
                    .is_some_and(|(own, asked)| asked.within(own))
        })
}

/// The number system a set node is, where it is one.
pub(super) fn system_named(set: &Node) -> Option<System> {
    (set.notation() == NUMBER_SYSTEMS)
        .then(|| System::of_sign(&set.text))
        .flatten()
}

/// A sum item's function hypothesis, `t : {a, …, b} → ℝ`, where the
/// citation makes t a term that is no number by what the page says once
/// (`AskedType::needs_saying`), asks a line the citation names to say it at
/// every point: a divisor's `≠ 0` is written, a sum's term's too
/// (`SYNTAX.md`).
pub(super) fn terms_unsaid(
    report: &mut Report,
    thm: &Theorem,
    step: &Step,
    line: usize,
    what: &str,
    library: &Library,
    known: &Known,
) {
    let Some(item) = step.just.cited_item() else {
        return;
    };
    let asks = family_asks(step, known, library);
    let parts = known.read_out_parts(step, library);
    for t in &asks.types {
        let Some((letter, term)) = t.pointwise() else {
            continue;
        };
        let [_, domain, codomain] = t.asked.children.as_slice() else {
            continue;
        };
        // A term dividing by the type's letter is said at every point by a
        // line; one holding a sum whose term divides by that sum's index is
        // a number where `membership` would build it, the sum's term said
        // at every point by a line the citation names.
        let needs_saying = t.needs_saying(&asks.letters);
        let inner = !t.inner_sums(&asks.letters).is_empty();
        let untyped = applies_untyped(term, thm, &parts.facts, known);
        let unplaced = !said_over_any_set(
            &PointOfASet {
                term,
                letter,
                domain,
                codomain,
            },
            &asks.letters,
            &typed_in_scope(known, step),
            known,
        );
        if !needs_saying && !inner && !untyped && !unplaced {
            continue;
        }
        if parts
            .facts
            .iter()
            .any(|f| t.said_pointwise(f, known, &asks.ctx))
        {
            continue;
        }
        if !needs_saying && term_built(t, step, &parts.facts, known, library) {
            continue;
        }
        report.say(
            &thm.path,
            line,
            format!(
                "{what} cites {item}, which asks that every term {} is in {}, and it is no number by what the page says once; cite a line saying for all {letter} ∈ {}, {} ∈ {}",
                known.print(term),
                known.print(codomain),
                known.print(domain),
                known.print(term),
                known.print(codomain),
            ),
        );
    }
}

/// Whether `term` applies a sequence a define by recursion of the proof
/// gives, and no fact among `facts` gives its type. Nothing says what such
/// a sequence's values are, so F(j)² is no number by what the page says
/// once, as F(j) is not (`check_defined_types`). A function defined by a
/// rule is a number where its rule is, as the build reads it
/// (`Elaborator::map_into`).
pub(super) fn applies_untyped(
    term: &Node,
    thm: &Theorem,
    facts: &[Node],
    known: &Known,
) -> bool {
    let defines = proof::in_scope(thm, known.env.scopes);
    let sequences: Vec<String> = defined_functions(&defines)
        .into_iter()
        .filter(|d| d.recursive)
        .map(|d| d.name)
        .collect();
    term.walk().iter().any(|node| {
        let (APPLICATION, [f, _]) = (node.notation(), node.children.as_slice()) else {
            return false;
        };
        sequences.contains(&f.text.to_string())
            && !facts.iter().any(|fact| {
                TYPING.contains(&fact.notation())
                    && fact.children.first().is_some_and(|g| g.text == f.text)
            })
    })
}

/// The rule `k ↦ f(k)` an item's function type `f : D → E` asks of a
/// function a let declares on another set than D, where D is neither a
/// range nor a number system: a product over a part of f's domain takes f's
/// values on the part, which the declaration says nothing of, so the type
/// is asked at every point of D as a summand's is. None where f is no
/// declared function, or D is its declared domain.
pub(super) fn on_a_part(asked: &Node, typed: &[Node], known: &Known) -> Option<Node> {
    let [f, domain, _] = asked.children.as_slice() else {
        return None;
    };
    if !f.is_name() || matches!(domain.notation(), INTEGER_RANGE | NUMBER_SYSTEMS) {
        return None;
    }
    let declared = typed.iter().find(|t| t.children[0].text == f.text)?;
    if known.alike(&declared.children[1], domain) {
        return None;
    }
    let letter = Node::name(domain.sort.held().unwrap_or_else(Sort::none), "k");
    let value = page::made_as(known.env.g, "_(_)", vec![f.clone(), letter])?;
    Some(Node::property("k", value))
}

/// The term a function hypothesis `t : D → E` asks at every point of D,
/// with the letter it is asked at.
pub(super) struct PointOfASet<'a> {
    /// The term at a point, `x·f(x)` for `t := x ↦ x·f(x)`.
    pub(super) term: &'a Node,
    /// The letter standing for the point.
    pub(super) letter: &'a str,
    /// D.
    pub(super) domain: &'a Node,
    /// E.
    pub(super) codomain: &'a Node,
}

/// Whether the term a function hypothesis asks at every point of a set is
/// in its codomain by what the page says once. A range or a number system
/// puts its letter in a system, and the other rules judge the term there;
/// a set of anything else puts its letter in none (`SYNTAX.md`, a sum's
/// term said once: the index is in the system its range starts in), so the
/// term is said once only where it holds the letter in values of functions
/// a type in scope gives on that very set, `f(x)` where `f : X → ℝ` and the
/// product runs over X. `∏(x ∈ X) x` over `X ⊆ ℤ` asks a line saying every
/// x is a number.
pub(super) fn said_over_any_set(
    at: &PointOfASet,
    letters: &Introduced,
    typed: &[Node],
    known: &Known,
) -> bool {
    if matches!(at.domain.notation(), INTEGER_RANGE | NUMBER_SYSTEMS) {
        return true;
    }
    let Some(system) = system_named(at.codomain) else {
        return true;
    };
    let mut letters = letters.clone();
    letters.shift_remove(at.letter);
    let value_typed = |t: &Node, s: System| {
        let (APPLICATION, [f, x]) = (t.notation(), t.children.as_slice()) else {
            return false;
        };
        x.is_name()
            && x.text == at.letter
            && typed.iter().any(|ty| {
                matches!(ty.children.as_slice(), [g, dom, cod]
                    if g.is_name()
                        && g.text == f.text
                        && known.alike(dom, at.domain)
                        && system_named(cod).is_some_and(|c| c.within(s)))
            })
    };
    // The term at the join's own letter: a line speaks of the proof's
    // letters, not of it, so no fact says a divisor is not zero.
    citing::within(
        at.term,
        system,
        &letters,
        &|d| citing::nonzero_said_once(d, &letters),
        &value_typed,
    )
}

/// Whether the term a function hypothesis `t : D → E` asks at every point
/// of D is in E as `membership` builds it (`methods::membership::holds`),
/// from the facts a citation is given, its letter at a point of D.
pub(super) fn term_built(
    asked: &AskedType,
    step: &Step,
    facts: &[Node],
    known: &Known,
    library: &Library,
) -> bool {
    let (Some((letter, term)), [_, domain, codomain]) =
        (asked.pointwise(), asked.asked.children.as_slice())
    else {
        return false;
    };
    let Some(system) = (codomain.notation() == NUMBER_SYSTEMS)
        .then(|| System::of_sign(&codomain.text))
        .flatten()
    else {
        return false;
    };
    let mut letters = super::super::library::introduced(known, step);
    let mut ranged = IndexMap::new();
    match (domain.notation(), domain.children.as_slice()) {
        (NUMBER_SYSTEMS, _) => {
            if let Some(s) = System::of_sign(&domain.text) {
                letters.insert(letter.to_string(), s);
            }
        }
        (INTEGER_RANGE, [start, end]) => {
            if let Some(s) = range_system(domain) {
                letters.insert(letter.to_string(), s);
            }
            ranged.insert(
                letter.to_string(),
                Range {
                    start: start.clone(),
                    end: end.clone(),
                },
            );
        }
        _ => return false,
    }
    let mut typed = typed_in_scope(known, step);
    typed.extend(facts.iter().filter(|f| types_a_function(f)).cloned());
    let given = crate::methods::membership::Facts {
        facts,
        letters,
        ranged,
        typed: &typed,
        in_sums: &typed,
        targets: &library.targets,
        ctx: known.ctx,
    };
    membership::holds(term, system, &given)
}
