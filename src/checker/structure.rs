//! The shape of a proof: numbering, blocks, citations and what they may
//! reach, imports, definitions, and the forms justifications take.

use std::collections::BTreeSet;

use indexmap::{IndexMap, IndexSet};

use super::library::Known;
use super::record::CheckedTheorem;
use super::{Report, RELATIONS};
use crate::corpus::proof::visible;
use crate::corpus::skeleton::{let_name, let_names, letter_in, listed};
use crate::corpus::{
    cited_items, define_parts, fmt, is_label, item_kind, names_an_item, FileScope,
    Head, Intro, Item, Justification, Method, Range, Record, RecordKind, Requires,
    Step, StepNo, Theorem,
};
use crate::formula::library::Function;
use crate::formula::notation_id::{NotationId, Spelling};
use crate::formula::page::Written;
use crate::formula::token::{Token, TokenKind};
use crate::formula::{holds, Node, Sorts};
use crate::notations::{
    FOR_ALL, FUNCTION_TYPE, IS_A_POINT, IS_A_POLYNOMIAL, IS_A_SET, MEMBERSHIP, SUBSET,
};
use crate::outcome::{Built, Declined};
use crate::regex;
use crate::rules;
use crate::sorts::introduction::{Form, Introduction};
use crate::sorts::{
    bound_written, define_formulas, named_by_hypotheses, names_written, theorem_tokens,
    written_tokens,
};
use crate::text::{prefix, repr};

/// A step numbered `cited` is visible from the step numbered `here` when it
/// is an ancestor, or shares `here`'s path to some position and comes before
/// it there. Steps inside a closed block are not visible outside it.
pub fn in_scope(cited: &StepNo, here: &StepNo) -> bool {
    let (c, h) = (&cited.0, &here.0);
    if c.len() > h.len() {
        return false;
    }
    let k = c.len();
    c[..k - 1] == h[..k - 1] && c[k - 1] < h[k - 1]
}

/// Why a line that exists is not in scope where `here` cites it: it comes
/// later, or it is inside a block that closed before `here`.
fn why_out_of_scope(cited: &StepNo, here: &StepNo) -> &'static str {
    if cited.0 > here.0 && !cited.0.starts_with(&here.0) {
        "which comes after it"
    } else {
        "which is inside a block that has closed"
    }
}

/// Why the step numbered `cited` is not in scope where `here` cites it, or
/// None where it is: it comes later, it is inside a block that has closed,
/// or it is in another part of a block with parts. What one case shows
/// under its assumption is not known in the next, as one case's labels are
/// not (`labels_in_scope`).
pub fn out_of_reach(
    thm: &Theorem,
    shape: &CheckedTheorem,
    cited: &StepNo,
    here: &Step,
) -> Option<&'static str> {
    if !in_scope(cited, &here.number) {
        return Some(why_out_of_scope(cited, &here.number));
    }
    let written = CheckedTheorem::written(thm, cited, here)?;
    let at = CheckedTheorem::index_of(thm, here)?;
    (!shape.encloses(shape.places[written], at))
        .then_some("which is in another part of the block")
}

/// Where a label is declared: a hypothesis, a define, or a block's opener.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Declared {
    Hypothesis(usize),
    Define(usize),
    Block(usize),
}

/// Hypothesis labels hold throughout a proof. A label declared by a block
/// holds inside that block only. When the block has parts, a label declared
/// by one part holds in that part alone, so one case of a case analysis
/// cannot cite the assumption of another.
pub fn labels_in_scope(
    thm: &Theorem,
    shape: &CheckedTheorem,
    step: &Step,
    scopes: &[FileScope],
) -> IndexMap<String, Declared> {
    let mut out: IndexMap<String, Declared> = IndexMap::new();
    for h in &thm.hypotheses {
        if let Some(lab) = &h.label {
            out.insert(lab.clone(), Declared::Hypothesis(h.line));
        }
    }
    // A define the file writes above the theorem is cited by its label too,
    // and so is one it imports, by the label on the import.
    for (_n, d, src) in visible(scopes, thm.scope, thm.line) {
        if src == thm.scope {
            out.entry(d.label.clone())
                .or_insert(Declared::Define(d.line));
        }
    }
    for i in &scopes[thm.scope].imports {
        if let Some(label) = &i.label {
            out.entry(label.clone()).or_insert(Declared::Define(i.line));
        }
    }
    // A define written inside a block is the block's, and the part's it is
    // written in (`record::CheckedTheorem::define_in_scope`).
    for (i, d) in thm.defines.iter().enumerate() {
        if shape.define_in_scope(thm, i, step) {
            out.insert(d.label.clone(), Declared::Define(d.line));
        }
    }
    for other in &thm.steps {
        let k = other.number.len();
        if other.number != step.number.prefix(k) || other.number == step.number {
            continue;
        }
        let child = on_the_way(thm, step, &step.number.prefix(k + 1));
        for o in &other.openers {
            if o.part.is_none() || child.is_some_and(|c| c.part == o.part) {
                out.insert(o.label.clone(), Declared::Block(o.line));
            }
        }
    }
    out
}

/// The step numbered `number` that `step` stands under or is: the nearest
/// written at or above it. A number written twice is `check_numbering`'s to
/// report, and each of its steps keeps the blocks it is written in.
fn on_the_way<'t>(thm: &'t Theorem, step: &Step, number: &StepNo) -> Option<&'t Step> {
    thm.steps
        .iter()
        .rfind(|s| &s.number == number && s.line <= step.line)
}

/// The productions of `GRAMMAR.md`, one per justification form, as the
/// skeleton reader cut the line by them (`Justification::unproduced`); the
/// build refuses what this reports with the rest of the checker's problems.
pub fn check_justification_form(
    report: &mut Report,
    path: &str,
    just: &Justification,
) -> bool {
    match &just.unproduced {
        Some(why) => {
            report.say(path, just.line, why.clone());
            false
        }
        None => true,
    }
}

/// Every number once, under a step that exists, and each run of siblings
/// counting 1, 2, 3 in the order the text writes them: a gap is a defect,
/// since a reader meeting 3 after 1 looks for the 2 that is not there.
pub fn check_numbering(report: &mut Report, thm: &Theorem) {
    let mut seen: IndexSet<StepNo> = IndexSet::new();
    let mut last: IndexMap<StepNo, u32> = IndexMap::new();
    for step in &thm.steps {
        let n = &step.number;
        let parent = n.parent();
        if seen.contains(n) {
            report.say(&thm.path, step.line, format!("step {n} is numbered twice"));
        }
        if n.len() > 1 && !seen.contains(&parent) {
            report.say(
                &thm.path,
                step.line,
                format!("step {n} is numbered under {parent}, which does not exist"),
            );
        }
        let expected = last.get(&parent).copied().unwrap_or(0) + 1;
        if !seen.contains(n) && n.last() != expected {
            let mut should = parent.clone();
            should.0.push(expected);
            report.say(
                &thm.path,
                step.line,
                format!("step {n} comes where step {should} should; numbers run on without gaps"),
            );
        }
        let before = last.get(&parent).copied().unwrap_or(0);
        last.insert(parent, before.max(n.last()));
        seen.insert(n.clone());
    }
}

regex!(PARTS_SPLIT, r",\s*");

fn declared_parts(method: &Record) -> Vec<String> {
    match method.field("parts") {
        Some(parts) => PARTS_SPLIT
            .split(parts)
            .filter_map(|p| p.split_whitespace().next())
            .map(String::from)
            .collect(),
        None => Vec::new(),
    }
}

pub fn check_blocks(
    report: &mut Report,
    thm: &Theorem,
    methods: &IndexMap<String, &Record>,
    known: &Known,
) {
    for step in &thm.steps {
        let has_children = thm.steps.iter().any(|s| s.number.parent() == step.number);
        let head = step.just.head.to_string();
        let method = methods.get(&head);
        let wants_block = step.just.head.takes_block();
        if wants_block && !has_children && !step.just.head.is(Method::Calculation) {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {} is justified by {head}, which needs a block, and has no sub-steps",
                    step.number
                ),
            );
        }
        if has_children && !wants_block {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {} has sub-steps but its justification {head} takes no block",
                    step.number
                ),
            );
        }
        // A case split has two cases or more: one case is the step itself.
        if step.just.head.is(Method::Cases) && step.parts.len() == 1 {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {} takes one case, and a case split takes two or more; prove the one case as a plain step",
                    step.number
                ),
            );
        }
        // A calculation's chain stands where a block would, and is all of it.
        if has_children && step.just.head.is(Method::Calculation) {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {} is a calculation, which writes its chain and opens no block of steps",
                    step.number
                ),
            );
        }
        // A requires line is one line, with no block for a method that
        // opens one to hold.
        for req in &step.requires {
            let Ok(by) = req.by() else {
                continue; // the reader reports a reason that does not read
            };
            if by.head.takes_block() {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line {} of step {} names {}, which opens a block, and a requires line holds none; prove it as a step and cite it",
                        str::trim(req.fact.text()),
                        step.number,
                        by.head
                    ),
                );
            }
        }
        let declared = method.map(|m| declared_parts(m)).unwrap_or_default();
        if !declared.is_empty() && step.parts.is_empty() && has_children {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {} cites {head}, whose block carries the parts {}, and has no part markers",
                    step.number,
                    declared.join(", ")
                ),
            );
        }
        for (marker, no) in &step.parts {
            if declared.is_empty() {
                report.say(
                    &thm.path,
                    *no,
                    format!(
                        "part marker {} under a {head} block, which declares no parts",
                        repr(marker)
                    ),
                );
            } else if !declared.contains(marker) {
                report.say(
                    &thm.path,
                    *no,
                    format!(
                        "part marker {} is not one of the parts {} that {head} declares",
                        repr(marker),
                        declared.join(", ")
                    ),
                );
            }
        }
        if step.just.head.is(Method::Contradiction)
            && !step.openers.iter().any(|o| o.kind == Intro::Suppose)
        {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {} is a contradiction whose block does not open with `suppose`",
                    step.number
                ),
            );
        }
        if step.just.head.is(Method::Contradiction) {
            check_supposition_used(report, thm, step);
        }
        if step.just.head.is(Method::Proof)
            && !step
                .openers
                .iter()
                .any(|o| matches!(o.kind, Intro::Let | Intro::Assume))
        {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {} is a proof whose block does not open with `let` or `assume`",
                    step.number
                ),
            );
        }
        if step.just.head.is(Method::Proof) {
            check_proof_letters(report, thm, step, known);
        }
        if step.just.head.is(Method::Induction) {
            check_step_part(report, thm, step, known);
        }
        if method.and_then(|m| m.field("part-opens")) == Some("assume, labelled") {
            for (index, (marker, no)) in step.parts.iter().enumerate() {
                if !step
                    .openers
                    .iter()
                    .any(|o| o.kind == Intro::Assume && o.part == Some(index))
                {
                    report.say(
                        &thm.path,
                        *no,
                        format!(
                            "the {} part of step {} does not open with a labelled `assume`",
                            repr(marker),
                            step.number
                        ),
                    );
                }
            }
        }
    }
}

/// A contradiction's block uses what it supposes (`METHODS.md`,
/// contradiction): some step under it, or a requires line of one, names
/// the supposition. A block that reaches its contradiction without it
/// shows that lines above it contradict each other, which is not what
/// supposing the claim false and refuting it says.
fn check_supposition_used(report: &mut Report, thm: &Theorem, step: &Step) {
    let under = |s: &&Step| {
        s.number.len() > step.number.len()
            && s.number.prefix(step.number.len()) == step.number
    };
    for o in step.openers.iter().filter(|o| o.kind == Intro::Suppose) {
        let names = |s: &&Step| {
            s.just.refs.contains(&o.label)
                || s.just.contradicting.as_ref() == Some(&o.label)
                || s.requires.iter().any(|r| r.refs().contains(&o.label))
        };
        if !thm.steps.iter().filter(under).any(|s| names(&s)) {
            report.say(
                &thm.path,
                o.line,
                format!(
                    "step {} is a contradiction whose block never uses its supposition {}",
                    step.number, o.label
                ),
            );
        }
    }
}

/// A `proof` block of a claim about every member of a set opens with the
/// claim's own `let` lines (`SYNTAX.md`, the `proof` row): "for all u ∈ A, …"
/// is proved by a block letting u, and a block letting v proves it of no u.
fn check_proof_letters(report: &mut Report, thm: &Theorem, step: &Step, known: &Known) {
    let Some(first) = step.claim.sentences().into_iter().next() else {
        return;
    };
    let Some(claim) = known.read(step, &first) else {
        return;
    };
    let bound = letters_bound(&claim, known);
    if bound.is_empty() {
        return;
    }
    for o in step.openers.iter().filter(|o| o.kind == Intro::Let) {
        let introduced = Introduction::read(o.body(&thm.path));
        let Some(name) = introduced.name() else {
            continue;
        };
        if !bound.iter().any(|b| b == name) {
            report.say(
                &thm.path,
                o.line,
                format!(
                    "the block of step {} lets {name}, and the claim it proves is about every {}; the block opens with the claim's own letter",
                    step.number,
                    bound.join(", ")
                ),
            );
        }
    }
}

/// The letters a claim's leading binders bind, outermost first: "for all
/// x, y ∈ S, …" binds x and y.
fn letters_bound(claim: &Node, known: &Known) -> Vec<String> {
    let mut out = Vec::new();
    let mut node = claim;
    loop {
        let binds = known
            .env
            .g
            .notations
            .iter()
            .find(|n| Spelling::new(n.key_id, n.literal_id) == node.spelling())
            .and_then(|n| n.node_binds());
        let Some(binds) = binds else {
            return out;
        };
        for &h in &binds.held {
            if let Some(name) = node.children.get(h).filter(|c| c.is_name()) {
                out.push(name.text.clone());
            }
        }
        let Some(body) = binds.body.last().and_then(|&b| node.children.get(b)) else {
            return out;
        };
        node = body;
    }
}

/// An induction's step part opens as a textbook's does: `let k ∈ X`, with
/// the letter and the set the claim "for all k ∈ X, …" binds, and `assume
/// step N is true for k, the induction hypothesis`. Its base part opens with
/// nothing.
fn check_step_part(report: &mut Report, thm: &Theorem, step: &Step, known: &Known) {
    let number = fmt(&step.number);
    let Some(claim) = known.whole_as_written(&step.claim) else {
        return; // `check_formulas` says it does not read
    };
    let (letter, set) = match (claim.notation(), claim.children.as_slice()) {
        (FOR_ALL, [letter, set, body])
            if letter.is_name() && !body.names().contains(&letter.text) =>
        {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {number} inducts on {k}, and what it says of every {k} does not mention {k}; the induction does no work, and the statement is a step of its own",
                    k = letter.text
                ),
            );
            return;
        }
        (FOR_ALL, [letter, set, _]) if letter.is_name() => (letter, set),
        _ => {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {number} is an induction whose claim does not say \"for all k ∈ X, …\""
                ),
            );
            return;
        }
    };
    if let Some(over) = step.just.on.as_ref().filter(|on| **on != letter.text) {
        report.say(
            &thm.path,
            step.line,
            format!(
                "the induction is on {over}, and its claim is not said for all {over}"
            ),
        );
        return;
    }
    check_induction_runs(report, thm, step, set, known);
    // The letter an induction runs over is its own: one the page has
    // introduced where the induction stands would be two things at once.
    if letters_introduced(thm, &CheckedTheorem::of(thm), step).contains(&letter.text) {
        report.say(
            &thm.path,
            step.line,
            format!(
                "step {number} is an induction on {k}, and {k} is a letter already introduced here; an induction runs over a letter of its own",
                k = letter.text
            ),
        );
    }
    for (index, (marker, no)) in step.parts.iter().enumerate() {
        let opens: Vec<_> = step
            .openers
            .iter()
            .filter(|o| o.part == Some(index))
            .collect();
        if marker == "base" {
            if let Some(o) = opens.first() {
                report.say(
                    &thm.path,
                    o.line,
                    format!(
                        "the base part of step {number} opens with a {} line",
                        o.kind
                    ),
                );
            }
            continue;
        }
        // The part opens with its `let k ∈ X` and then its hypothesis, and
        // with nothing else: the induction lemma takes the statement at k
        // and gives it at k + 1.
        let fixed = match opens.as_slice() {
            [first, second] if first.kind == Intro::Let && second.is_hypothesis => {
                let i = Introduction::read(first.body(&thm.path));
                matches!(i.form, Form::Member)
                    .then(|| i.asserted(known.env.g, &known.sorts).ok()?.pop())
                    .flatten()
            }
            _ => None,
        };
        let opened = fixed.as_ref().is_some_and(|f| match f.children.as_slice() {
            [k, x] => k.text == letter.text && known.alike(x, set),
            _ => false,
        });
        if !opened {
            let (k, x) = (known.print(letter), known.print(set));
            report.say(
                &thm.path,
                *no,
                format!(
                    "the step part of step {number} does not open with `let {k} ∈ {x}` and `assume step {number} is true for {k}, the induction hypothesis`, those two lines in that order and no other"
                ),
            );
        }
        for o in opens.iter().filter(|o| o.is_hypothesis) {
            let Some(said) = o.hypothesis_for.as_ref().filter(|k| **k != letter.text)
            else {
                continue;
            };
            report.say(
                &thm.path,
                o.line,
                format!(
                    "the induction hypothesis is for {said}, and step {number} is said for all {}",
                    letter.text
                ),
            );
        }
    }
}

/// An induction has a `base` part and a `step` part, runs over ℕ or ℕ₀, and
/// starts at the set's first element, which it writes (`SYNTAX.md`, the
/// `induction` row). The sets and where each starts are the induction
/// lemmas' (`rules::INDUCTION`), which the build closes with.
fn check_induction_runs(
    report: &mut Report,
    thm: &Theorem,
    step: &Step,
    set: &Node,
    known: &Known,
) {
    let number = fmt(&step.number);
    for wanted in ["base", "step"] {
        if !step.parts.iter().any(|(marker, _)| marker == wanted) {
            report.say(
                &thm.path,
                step.line,
                format!("step {number} is an induction with no {wanted} part"),
            );
        }
    }
    let first_of = |label: &str| rules::digit_of(label).map(|d| d.to_string());
    let begins = (set.notation() == crate::notations::NUMBER_SYSTEMS)
        .then(|| rules::System::of_sign(&set.text))
        .flatten()
        .and_then(|s| rules::lookup(rules::INDUCTION, s.label()))
        .and_then(|(_, start)| first_of(start));
    let Some(begins) = begins else {
        let runs: Vec<String> = rules::INDUCTION
            .iter()
            .filter_map(|(set, (_, start))| {
                Some(format!("{} from {}", sign_of(set), first_of(start)?))
            })
            .collect();
        report.say(
            &thm.path,
            step.line,
            format!(
                "step {number} is an induction over {}, and an induction runs over {}",
                known.print(set),
                runs.join(" or ")
            ),
        );
        return;
    };
    let written = step.just.start.as_deref().map(str::trim);
    if written != Some(begins.as_str()) {
        let said = match written {
            Some(w) => format!("the text says {w}"),
            None => "the text says no start".to_string(),
        };
        report.say(
            &thm.path,
            step.just.line,
            format!(
                "an induction over {} starts at {begins}, and {said}",
                known.print(set)
            ),
        );
    }
}

/// How the page writes the number system set.mm's `label` names, `ℕ` for
/// `cn`; the label itself where it names none.
fn sign_of(label: &str) -> &str {
    rules::SYSTEM_OF
        .iter()
        .find(|(_, l)| *l == label)
        .map_or(label, |(sign, _)| sign)
}

/// A calculation only joins. Every line cites a numbered step or a label and
/// carries no reasoning of its own, so a line that names an item or
/// instantiates one is carrying a justification that belongs in a step.
pub fn check_chain(report: &mut Report, thm: &Theorem, step: &Step) {
    if !step.just.head.is(Method::Calculation) {
        return;
    }
    if step.just.chain.is_empty() {
        report.say(
            &thm.path,
            step.line,
            format!("step {} is a calculation with no chain", step.number),
        );
    }
    // A chain the skeleton cannot cut is refused as the build refuses it.
    let uncut = match crate::corpus::proof::chain(&step.just, &thm.path) {
        Some(Err(problem)) => Some(problem),
        _ => None,
    };
    if let Some(problem) = &uncut {
        report.say(&problem.path, problem.line, problem.message.clone());
    }
    for (text, no) in &step.just.chain {
        if names_an_item(text) || text.contains(":=") {
            report.say(
                &thm.path,
                *no,
                "a chain line carries a justification; a calculation only joins, so each line cites a numbered step or a label and the reasoning lives in that step",
            );
        }
        let related = RELATIONS.iter().any(|r| {
            text.trim_start().starts_with(r) || text.contains(&format!(" {r} "))
        });
        if !related && uncut.is_none() {
            report.say(&thm.path, *no, "chain line carries no relation");
        }
    }
}

/// The lines and labels a `from` list names more than once, each once: a
/// line cited fills every hypothesis it says, so it is named once
/// (`SYNTAX.md`).
fn named_twice(refs: &[String]) -> Vec<&String> {
    let mut seen: IndexSet<&String> = IndexSet::new();
    let mut twice: IndexSet<&String> = IndexSet::new();
    for r in refs {
        if !seen.insert(r) {
            twice.insert(r);
        }
    }
    twice.into_iter().collect()
}

/// What to say of a line or label `what` names twice in its `from` list.
fn cited_twice(what: &str, cited: &str) -> String {
    format!(
        "{what} cites {cited} more than once; a line is cited once, and fills every hypothesis it says"
    )
}

/// Where a line or label stands in a `from` list: labels first, by their
/// letters and then their number, none before 1, and then lines by their
/// step numbers, 2 before 2.1 before 10 (`SYNTAX.md`).
fn citation_order(cited: &str) -> (bool, String, Vec<u64>) {
    if is_label(cited) {
        let letters: String = cited
            .chars()
            .take_while(|c| c.is_ascii_uppercase())
            .collect();
        let number = cited[letters.len()..].parse::<u64>().ok();
        return (false, letters, number.into_iter().collect());
    }
    let parts = cited.split('.').map(|p| p.parse().unwrap_or(0)).collect();
    (true, String::new(), parts)
}

/// The lines and labels of a `from` list in the order it is written in.
pub fn cited_in_order<S: AsRef<str> + Clone>(refs: &[S]) -> Vec<S> {
    let mut sorted = refs.to_vec();
    sorted.sort_by_key(|r| citation_order(r.as_ref()));
    sorted
}

/// What to say of a `from` list out of order, or None where it is in order.
fn out_of_order(what: &str, refs: &[String]) -> Option<String> {
    let sorted = cited_in_order(refs);
    (sorted != refs).then(|| {
        format!(
            "{what} cites {} out of order; labels come first, by letter and then number, and then lines by number: from {}",
            refs.join(", "),
            sorted.join(", ")
        )
    })
}

/// What to say of a label cited and not in scope: where it is the name of a
/// define the file imports with no label, that the import is to give one,
/// since a define is cited by its label and not by its name.
fn out_of_scope(scope: &FileScope, cited: &str, said: String) -> String {
    match scope
        .imports
        .iter()
        .find(|i| i.alias == cited && i.label.is_none())
    {
        Some(i) => format!(
            "{said}; {cited} is the define import definition {}/{} brings in, which a line cites by a label its import gives, as `(D1)`: add one",
            i.module, i.name
        ),
        None => said,
    }
}

/// What to say of a citation that names nothing.
pub fn unresolved(cited: &str) -> String {
    if cited.contains('/') {
        return format!(
            "{cited} is cited by its path; an item is imported, and cited by the name its import gives it"
        );
    }
    format!("{cited} is neither imported nor a theorem of this file")
}

pub fn check_citations(
    report: &mut Report,
    thm: &Theorem,
    items: &IndexMap<String, Item>,
    methods: &IndexMap<String, &Record>,
    scopes: &[FileScope],
) {
    let numbers: IndexSet<&StepNo> = thm.steps.iter().map(|s| &s.number).collect();
    let shape = CheckedTheorem::of(thm);
    for step in &thm.steps {
        let just = &step.just;
        let scope = labels_in_scope(thm, &shape, step, scopes);
        if let Some(bad) = &just.bad_ref {
            report.say(
                &thm.path,
                just.line,
                format!(
                    "`from` names {}, which is neither a line nor a label",
                    repr(bad)
                ),
            );
        }
        // The step's own `from` list: a calculation gathers its links'
        // citations, and two links may cite one line.
        let own = &just.from;
        let what = format!("step {}", step.number);
        for r in named_twice(own) {
            report.say(&thm.path, just.line, cited_twice(&what, r));
        }
        // A chain's lines are in the chain's order (`SYNTAX.md`, a list is
        // in order).
        let chained = just.head.is(Method::Transitivity);
        if let Some(said) = out_of_order(&what, own).filter(|_| !chained) {
            report.say(&thm.path, just.line, said);
        }
        for r in &just.refs {
            if is_label(r) {
                if !scope.contains_key(r) {
                    report.say(
                        &thm.path,
                        just.line,
                        out_of_scope(
                            &scopes[thm.scope],
                            r,
                            format!(
                                "step {} cites {r}, which is not in scope here",
                                step.number
                            ),
                        ),
                    );
                }
                continue;
            }
            let cited = StepNo::parse(r);
            if !numbers.contains(&cited) {
                report.say(
                    &thm.path,
                    just.line,
                    format!(
                        "step {} cites line {r}, which does not exist",
                        step.number
                    ),
                );
            } else if let Some(why) = out_of_reach(thm, &shape, &cited, step) {
                report.say(
                    &thm.path,
                    just.line,
                    format!("step {} cites line {r}, {why}", step.number),
                );
            }
        }
        if let Some(target) = &just.target {
            if item_kind(target).is_some() {
                report.say(
                    &thm.path,
                    just.line,
                    format!(
                        "step {} instantiates {target}; the target of instantiate is a line or a label, never an item",
                        step.number
                    ),
                );
            }
        }
        if let Head::Method(m) = &just.head {
            if !methods.contains_key(m.as_str()) {
                report.say(
                    &thm.path,
                    just.line,
                    format!(
                        "{} is in no record of corpus/db/methods.records",
                        m.as_str()
                    ),
                );
            }
        }
        // The item a step cites, as its head or as what it obtains from,
        // resolves, and its prefix is its kind.
        if let Some(cited) = just.cited_item() {
            let kind = item_kind(&cited).expect("a citation opens with a prefix");
            match items.get(&just.item(&cited)) {
                None => report.say(&thm.path, just.line, unresolved(&cited)),
                Some(item) if item.cited_as() != kind => report.say(
                    &thm.path,
                    just.line,
                    format!("{cited} names {}", item.described()),
                ),
                Some(_) => {}
            }
        }
        let at = Cited {
            thm,
            items,
            scopes,
            numbers: &numbers,
            scope: &scope,
            shape: &shape,
            step,
        };
        for req in &step.requires {
            at.check_reason(report, req, "requires line");
        }
    }
    // A let's reason is written as a requires line's is, and is read under
    // the step below the let (`Theorem::step_after`).
    for d in &thm.defines {
        let (Some(reason), Some(step)) = (&d.reason, thm.step_after(d.line)) else {
            continue;
        };
        let scope = labels_in_scope(thm, &shape, step, scopes);
        let at = Cited {
            thm,
            items,
            scopes,
            numbers: &numbers,
            scope: &scope,
            shape: &shape,
            step,
        };
        let req = reason.shown(Written::new("", &thm.path, reason.line));
        at.check_reason(report, &req, &format!("the reason under let {}", d.label));
        // It is the let's, and rests on nothing written below the let.
        for r in req.lines() {
            let below = thm
                .steps
                .iter()
                .find(|s| fmt(&s.number) == *r)
                .is_some_and(|s| s.line > d.line);
            if below || *r == d.label {
                report.say(
                    &thm.path,
                    reason.line,
                    format!(
                        "the reason under let {} cites {r}, which is not above the let",
                        d.label
                    ),
                );
            }
        }
    }
}

/// Where a requires line's citations are read: its step, and what is in
/// scope there.
struct Cited<'a> {
    thm: &'a Theorem,
    items: &'a IndexMap<String, Item<'a>>,
    scopes: &'a [FileScope],
    numbers: &'a IndexSet<&'a StepNo>,
    scope: &'a IndexMap<String, Declared>,
    shape: &'a CheckedTheorem,
    step: &'a Step,
}

impl Cited<'_> {
    /// A requires line's reason, or a let's, names a method, an item or a
    /// line, and each thing it cites is there to cite. `what` names the line
    /// in a message.
    fn check_reason(&self, report: &mut Report, req: &Requires, what: &str) {
        let (thm, scopes) = (self.thm, self.scopes);
        let text = &req.how;
        let no = req.line;
        let unread = match &req.by {
            Err(_) => true,
            Ok(by) => by.head == Head::Lines && by.unproduced.is_some(),
        };
        if unread {
            report.say(
                &thm.path,
                no,
                format!(
                    "{what} justified by {}, which is neither a method, an item, nor a line",
                    repr(prefix(text, 40))
                ),
            );
        }
        // A manipulation names the one line it manipulates (`GRAMMAR.md`,
        // requires lines): `weakening, from 2.1`.
        if let Ok(by) = &req.by {
            if let (Head::Manipulation(made), Some(_)) = (&by.head, &by.unproduced) {
                report.say(
                    &thm.path,
                    no,
                    format!(
                        "{what} names {made}, which manipulates one line, and cites {}: `{made}, from L`",
                        match by.from.len() {
                            0 => "none".to_string(),
                            n => format!("{n}"),
                        }
                    ),
                );
            }
        }
        // A requires line cites an item like any other citation, so its
        // pointer resolves and its prefix matches the item's kind.
        if let Some((cited, kind)) = req.cited_item() {
            match self.items.get(&self.step.just.item(&cited)) {
                None => report.say(&thm.path, no, unresolved(&cited)),
                Some(item) if item.cited_as() != kind => report.say(
                    &thm.path,
                    no,
                    format!("{cited} names {}", item.described()),
                ),
                Some(_) => {}
            }
        }
        if let Some(bad) = req.by.as_ref().map_or(&None, |by| &by.bad_ref) {
            report.say(
                &thm.path,
                no,
                format!(
                    "`from` names {}, which is neither a line nor a label",
                    repr(bad)
                ),
            );
        }
        let refs = req.lines();
        for r in named_twice(refs) {
            report.say(&thm.path, no, cited_twice(what, r));
        }
        if let Some(said) = out_of_order(what, refs) {
            report.say(&thm.path, no, said);
        }
        for r in refs {
            if is_label(r) {
                if !self.scope.contains_key(r) {
                    report.say(
                        &thm.path,
                        no,
                        out_of_scope(
                            &scopes[thm.scope],
                            r,
                            format!("{what} cites {r}, which is not in scope here"),
                        ),
                    );
                }
                continue;
            }
            let cited = StepNo::parse(r);
            if !self.numbers.contains(&cited) {
                report.say(
                    &thm.path,
                    no,
                    format!("{what} cites line {r}, which does not exist"),
                );
            } else if let Some(why) = out_of_reach(thm, self.shape, &cited, self.step) {
                report.say(&thm.path, no, format!("{what} cites line {r}, {why}"));
            }
        }
    }
}

regex!(DECLARED_WORD, r"[A-Za-z]{2,}");

/// Every literal word appearing in a declared pattern.
pub fn declared_words(records: &[Record]) -> IndexSet<String> {
    let mut out = IndexSet::new();
    for r in records {
        if r.kind == RecordKind::Notation {
            for m in DECLARED_WORD.find_iter(r.field_or_empty("pattern")) {
                out.insert(m.as_str().to_string());
            }
        }
    }
    out
}

/// Where a pattern puts two holes side by side, as distance does in |CA|,
/// the names filling them run together in the text. If they spell a
/// declared word, a reader reads the word and so does anything lexing the
/// text.
///
/// Points are capitals throughout this corpus, which keeps |AN| clear of the
/// word `an`, but that is a convention of school geometry and not a rule:
/// topology and differential geometry both name points with lowercase
/// letters, and set.mm's plane is ℂ, where a point would naturally be z or
/// w. So the collision is checked rather than assumed away.
pub fn check_run_together(
    report: &mut Report,
    thm: &Theorem,
    words: &IndexSet<String>,
    g: &crate::formula::Grammar,
) {
    // A run of letters the lexer read whole as a word, between the bars of
    // |xy| or straight after ∠, where two names were meant.
    let whole = |t: &Token, next: Option<&Token>| {
        words.contains(&t.text)
            && t.text.chars().count() > 1
            && !next.is_some_and(|n| {
                n.kind == TokenKind::Name && n.at == t.at + t.text.chars().count()
            })
    };
    for s in &thm.steps {
        for line in written_tokens(std::slice::from_ref(&s.claim), g) {
            for (i, t) in line.iter().enumerate() {
                let next = line.get(i + 1);
                let end = t.at + t.text.chars().count();
                // The mark touches the run, with no space between: `|xy|`,
                // and not the bars of `|H| divides |G|`.
                let before = i
                    .checked_sub(1)
                    .and_then(|b| line.get(b))
                    .filter(|b| b.at + b.text.chars().count() == t.at);
                let barred = before.is_some_and(|b| b.text == "|")
                    && next.is_some_and(|n| n.text == "|" && n.at == end);
                let angled = before.is_some_and(|b| b.text == "∠") && whole(t, next);
                if !((barred && whole(t, next)) || angled) {
                    continue;
                }
                report.say(
                    &thm.path,
                    s.line,
                    format!(
                        "step {} writes {} in a notation whose holes are adjacent, and {} is a declared word; rename one of the names so the two do not run together",
                        s.number,
                        repr(&t.text),
                        repr(&t.text)
                    ),
                );
            }
        }
    }
}

/// A substitution may not capture. If the term being substituted names a
/// variable bound where it lands, the step is rejected rather than the
/// variable quietly renamed, because renaming would make the machine do
/// something the page does not show.
pub fn check_capture(report: &mut Report, thm: &Theorem, known: &Known) {
    let binders = known.env.g.binders();
    for s in &thm.steps {
        if !s.just.head.is(Method::Instantiate) {
            continue;
        }
        let Some(target) = s.just.target.clone() else {
            continue;
        };
        // The letters a binder in the target line binds: what the grammar
        // says each binding notation holds. A line that does not read is
        // `check_formulas`'s to report.
        let landing = known.scope(s).get(&target).cloned();
        let mut bound: BTreeSet<String> = BTreeSet::new();
        for tree in landing
            .iter()
            .flat_map(|l| known.said_parts(l, None))
            .flatten()
        {
            for node in tree.walk() {
                let Some(binds) = binders.get(&node.notation()) else {
                    continue;
                };
                for &at in &binds.held {
                    if let Some(letter) = node.children.get(at).filter(|l| l.is_name())
                    {
                        bound.insert(letter.text.clone());
                    }
                }
            }
        }
        // A letter given a value is the one the instantiation takes its
        // binder off, so the value lands where it is no longer bound.
        for name in s.just.values.names() {
            bound.remove(name);
        }
        if bound.is_empty() {
            continue;
        }
        // A value that does not read is the elaborator's to report.
        let Ok(values) = s.just.values.read(known.env.g, &known.sorts) else {
            continue;
        };
        for n in values {
            let value = n.value;
            // Substituting a variable for itself changes nothing and cannot
            // capture. A term that merely mentions the bound name does: that
            // mention refers to an outer binding and would be swallowed.
            if value.is_name() && value.text == n.name {
                continue;
            }
            let named = value.names();
            let clash: Vec<&String> = named.intersection(&bound).collect();
            if !clash.is_empty() {
                let shown: Vec<&str> = clash.iter().map(|s| s.as_str()).collect();
                report.say(
                    &thm.path,
                    s.just.line,
                    format!(
                        "step {} substitutes a term naming {}, which is bound where it lands; a substitution may not capture",
                        s.number,
                        shown.join(", ")
                    ),
                );
            }
        }
    }
}

/// A statement's range lines say what a short form leans on and nothing
/// more: each letter once, over a set, never against a `let` putting the
/// letter in another set, and only where some quantifier in the theorem
/// writes a bound in place of the letter's set. A line nothing leans on is
/// one a reader reads and then has no use for.
#[allow(clippy::too_many_arguments)]
pub fn check_ranges(
    report: &mut Report,
    path: &str,
    ranges: &[Range],
    lets: &[(&str, usize)],
    tokens: &[Vec<Token>],
    env: crate::sorts::Env,
    sorts: &Sorts,
) {
    let mut said: IndexMap<&str, &Range> = IndexMap::new();
    for range in ranges {
        let set = Written::new(&range.set, path, range.line);
        match set.sentence().and_then(|s| s.read(env.g, sorts)) {
            Err(p) => report.say(path, range.line, p.message),
            Ok(set) if holds(&set.sort).is_none() && !set.sort.is("set") => report.say(
                path,
                range.line,
                format!(
                    "{} is not a set, so nothing can range over it",
                    repr(&range.set)
                ),
            ),
            Ok(_) => {}
        }
        for name in &range.names {
            if said.contains_key(name.as_str()) {
                report.say(
                    path,
                    range.line,
                    format!("the statement already says what {name} ranges over"),
                );
                continue;
            }
            said.insert(name, range);
            // `for all ε > 0`, `there is δ > 0`: the quantifier, the name,
            // and an order in place of the set. Its tree is the long form's,
            // so it is told by how it is written.
            const ORDERS: [&str; 5] = [">", "≥", "<", "≤", "≠"];
            let short = tokens.iter().any(|line| {
                line.windows(4).any(|w| {
                    let opens = matches!(
                        (w[0].text.as_str(), w[1].text.as_str()),
                        ("for", "all") | ("there", "is") | ("there", "exists")
                    );
                    opens
                        && w[2].kind == TokenKind::Name
                        && &w[2].text == name
                        && ORDERS.contains(&w[3].text.as_str())
                })
            });
            if !short {
                report.say(
                    path,
                    range.line,
                    format!(
                        "the statement says what {name} ranges over, and no quantifier leaves {name}'s set out"
                    ),
                );
            }
        }
    }
    for (line, no) in lets {
        let body = crate::sorts::unlabel(line);
        let Some(put) = letter_in(&body) else {
            continue;
        };
        let Some(range) = said.get(put.letter) else {
            continue;
        };
        if put.set.split_whitespace().ne(range.set.split_whitespace()) {
            report.say(
                path,
                *no,
                format!(
                    "the statement says {} ranges over {}, and this line puts it in {}",
                    put.letter, range.set, put.set
                ),
            );
        }
    }
}

/// Every variable's sort is on the page, so the parser never infers one.
///
/// A `let` line gives it, and so does the claim of the `obtain` step that
/// introduces a name. Without that rule a parser would have to chase the
/// cited item's conclusion to learn a sort, and sorts are what disambiguate
/// a notation, so two implementations chasing differently would parse the
/// same formula differently.
pub fn check_sorts(report: &mut Report, thm: &Theorem, known: &Known) {
    // What says a name's sort: its membership, a part of a set by ⊆ as
    // surely as by ∈ 𝒫, its being a set, a point or a polynomial, or a
    // function's type.
    const SAYING: [NotationId; 6] = [
        MEMBERSHIP,
        SUBSET,
        IS_A_SET,
        IS_A_POINT,
        IS_A_POLYNOMIAL,
        FUNCTION_TYPE,
    ];
    for s in &thm.steps {
        if !s.just.head.is(Method::Obtain) {
            continue;
        }
        let Some(claim) = known.whole_as_written(&s.claim) else {
            continue; // `check_formulas` says it does not read
        };
        let said = claim.walk();
        for v in &s.just.obtained {
            let stated = said.iter().any(|n| {
                SAYING.contains(&n.notation())
                    && n.children
                        .first()
                        .is_some_and(|x| x.is_name() && x.text == *v)
            });
            if !stated {
                report.say(
                    &thm.path,
                    s.line,
                    format!(
                        "step {} obtains {v} without stating its sort; the claim of an obtain states the membership of each name it introduces, so no sort is inferred",
                        s.number
                    ),
                );
            }
        }
    }
}

/// A define carries a reading, and a note belongs to a block.
///
/// A define names an object and asserts nothing, so the acceptance test has
/// nothing to check about it and a reader can meet a construction with no
/// idea why it is there. The reading is the one line saying what the name
/// means in words. Nothing can judge the words, but their absence is the
/// commonest way for the device to be forgotten, so that much is required.
pub fn check_readings(report: &mut Report, thm: &Theorem) {
    for d in &thm.defines {
        if !thm.readings.contains_key(&d.label) {
            report.say(
                &thm.path,
                d.line,
                format!(
                    "let {} carries no `reads` line saying what the name means",
                    d.label
                ),
            );
        }
    }
    for step in &thm.steps {
        if let Some((_, line)) = &step.note {
            if !step.just.head.takes_block() {
                report.say(
                    &thm.path,
                    *line,
                    format!(
                        "step {} carries a note and opens no block; a note says what a block is doing",
                        step.number
                    ),
                );
            }
        }
    }
}

/// A numbered step is there to be used (`SYNTAX.md`, Steps): another step,
/// a requires line, a row or a let's reason cites it, or it is the last
/// step of its part of a block, or of the proof, which says what that part
/// owes. Any other step says something nothing goes on to use.
pub fn check_steps_used(report: &mut Report, thm: &Theorem) {
    let mut cited: BTreeSet<String> = BTreeSet::new();
    for step in &thm.steps {
        cites(&step.just, &mut cited);
        for r in &step.requires {
            if let Ok(by) = &r.by {
                cites(by, &mut cited);
            }
        }
    }
    for d in &thm.defines {
        if let Some(Ok(by)) = d.reason.as_ref().map(|r| &r.by) {
            cites(by, &mut cited);
        }
    }
    for (i, step) in thm.steps.iter().enumerate() {
        let number = step.number.to_string();
        if cited.contains(&number) {
            continue;
        }
        let depth = step.number.len();
        let parent = step.number.prefix(depth - 1);
        let followed = thm.steps[i + 1..].iter().any(|s| {
            s.number.len() == depth
                && s.number.prefix(depth - 1) == parent
                && s.part == step.part
        });
        if !followed {
            continue;
        }
        report.say(
            &thm.path,
            step.line,
            format!(
                "step {number} is cited by nothing, and is not the last step of its part"
            ),
        );
    }
}

/// What a justification cites, into `cited`: its lines and labels, among
/// them those its chain and rows cite (`Justification::refs`), an
/// instantiate's target, and the line it contradicts.
fn cites(just: &Justification, cited: &mut BTreeSet<String>) {
    cited.extend(just.refs.iter().cloned());
    cited.extend(just.target.iter().cloned());
    cited.extend(just.contradicting.iter().cloned());
}

/// The last step of a proof is the theorem's conclusion (`SYNTAX.md`): its
/// sentences, in order, each one formula with the statement's, as
/// `Known::alike` compares two. A sentence that does not read is reported by
/// `check_formulas`, and not compared here.
pub fn check_last_step(report: &mut Report, thm: &Theorem, known: &Known) {
    let Some(last) = thm.steps.iter().rev().find(|s| s.number.0.len() == 1) else {
        report.say(
            &thm.path,
            thm.line,
            format!("theorem {} has no steps", thm.name),
        );
        return;
    };
    // A claim of several sentences is their conjunction, and so is one
    // sentence joining them with "and" (`SYNTAX.md`), so each side is
    // compared as the conjuncts it says, in order.
    fn conjuncts(node: Node, out: &mut Vec<Node>) {
        if node.notation() == crate::notations::CONJUNCTION && node.children.len() == 2
        {
            for part in node.children.iter() {
                conjuncts(part.clone(), out);
            }
        } else {
            out.push(node);
        }
    }
    let read = |w: &Written| -> Option<Vec<Node>> {
        let mut out = Vec::new();
        for s in w.sentences() {
            conjuncts(known.read_as_written(&s)?, &mut out);
        }
        Some(out)
    };
    let stated = Written::new(&thm.conclusion, &thm.path, thm.line);
    let (Some(claimed), Some(stated)) = (read(&last.claim), read(&stated)) else {
        return;
    };
    let same = claimed.len() == stated.len()
        && claimed.iter().zip(&stated).all(|(a, b)| known.alike(a, b));
    if !same {
        report.say(
            &thm.path,
            last.line,
            format!(
                "step {} is the last, and does not claim what {} states",
                last.number, thm.name
            ),
        );
    }
}

/// The files of the corpus, each with its theorems, in the order the
/// theorems were read.
fn by_file(theorems: &[Theorem]) -> IndexMap<&str, Vec<&Theorem>> {
    let mut files: IndexMap<&str, Vec<&Theorem>> = IndexMap::new();
    for thm in theorems {
        files.entry(thm.module()).or_default().push(thm);
    }
    files
}

/// What a proof file defines outside its theorems and what it imports.
///
/// Two definitions of one name are a defect wherever both could be read:
/// two the file writes, one it writes and one it imports, two it imports,
/// or a proof's own define under a name the file already gives something.
/// A definition imported and never used is a defect, as an import cited
/// from nowhere is. A define outside a theorem carries a reading like any
/// other, and its label is not one a theorem below it also uses.
/// The functions a define gives: a define with an argument, and the
/// sequences of a recursion. A define of a set or a number gives none.
fn functions_defined(text: &str) -> Vec<String> {
    match define_parts(text) {
        Built(said) => match said.one() {
            Some(d) if d.params.is_empty() => Vec::new(),
            _ => said.names(),
        },
        Declined(_) => Vec::new(),
    }
}

/// A file applies each library function it imports. An import is one of a
/// function only where its full name is a function's record
/// (`link_functions`), so where it comes from is not asked again here.
pub fn check_function_imports(
    report: &mut Report,
    theorems: &[Theorem],
    scopes: &[FileScope],
    g: &crate::formula::Grammar,
) {
    for (id, scope) in scopes.iter().enumerate() {
        let tokens = file_tokens(theorems, id, scope, g);
        let mut seen: IndexSet<&str> = IndexSet::new();
        for fi in &scope.functions {
            let (path, no, name) = (&scope.path, fi.line, fi.name.as_str());
            if !seen.insert(name) {
                report.say(path, no, format!("{name} is imported twice"));
                continue;
            }
            // Applied: the name written with a bracket after it.
            let applied = tokens.iter().any(|line| {
                line.windows(2).any(|w| {
                    w[0].kind == TokenKind::Name
                        && w[0].text == name
                        && w[1].text == "("
                })
            });
            if !applied {
                report.say(path, no, format!("imports {name} and never applies it"));
            }
        }
    }
}

/// The tokens of every formula a file writes: its theorems' and its own
/// defines' (`theorem_tokens`, `define_formulas`).
fn file_tokens(
    theorems: &[Theorem],
    scope_id: usize,
    scope: &FileScope,
    g: &crate::formula::Grammar,
) -> Vec<Vec<Token>> {
    let mut out: Vec<Vec<Token>> = theorems
        .iter()
        .filter(|t| t.scope == scope_id)
        .flat_map(|t| theorem_tokens(t, g))
        .collect();
    let defines: Vec<Written> =
        scope.defines.iter().flat_map(define_formulas).collect();
    out.extend(written_tokens(&defines, g));
    out
}

/// A proof's own function does not take the name of a library function its
/// file imports.
///
/// Where the file imports C, `C(n, k)` is the binomial coefficient on every
/// line of it, so a reader never has to ask which C a line means. A define
/// with an argument, a sequence, a `let f : A → B` or a `let f be a function
/// on X`, and a definition imported under the name, are each a function of
/// the proof's; a set or a number with that letter is not, and may be
/// written. A file that does not import C may give the letter to a function
/// of its own.
pub fn check_function_names(
    report: &mut Report,
    theorems: &[Theorem],
    scopes: &[FileScope],
    functions: &IndexMap<String, Function>,
) {
    let mut say = |path: &str, no: usize, name: &str, imported: &IndexSet<String>| {
        if let Some(f) = functions.get(name).filter(|_| imported.contains(name)) {
            report.say(
                path,
                no,
                format!(
                    "{name} is the library's function, {}, which this file imports; name this function something else",
                    f.cited()
                ),
            );
        }
    };
    for scope in scopes {
        let imported = scope.function_names();
        for d in &scope.defines {
            for name in functions_defined(&d.text) {
                say(&scope.path, d.line, &name, &imported);
            }
        }
        for (alias, (_, d)) in &scope.linked {
            if !functions_defined(&d.text).is_empty() {
                let no = scope
                    .imports
                    .iter()
                    .find(|i| &i.alias == alias)
                    .map_or(0, |i| i.line);
                say(&scope.path, no, alias, &imported);
            }
        }
    }
    for thm in theorems {
        let imported = scopes[thm.scope].function_names();
        for d in &thm.defines {
            for name in functions_defined(&d.text) {
                say(&thm.path, d.line, &name, &imported);
            }
        }
        let lets = thm
            .hypotheses
            .iter()
            .filter(|h| h.kind == Intro::Let)
            .map(|h| (h.text.as_str(), h.line))
            .chain(thm.steps.iter().flat_map(|s| {
                s.openers
                    .iter()
                    .filter(|o| o.kind == Intro::Let)
                    .map(|o| (o.text.as_str(), o.line))
            }));
        for (text, no) in lets {
            let body = crate::sorts::unlabel(text);
            let body = str::trim(body.trim_start_matches("let"));
            let said = Introduction::read(Written::new(body, &thm.path, no));
            let function = matches!(
                said.form,
                Form::Function | Form::FunctionBeing { .. } | Form::FunctionOn { .. }
            );
            if let (true, Some(name)) = (function, said.name()) {
                say(&thm.path, no, name, &imported);
            }
        }
    }
}

pub fn check_definitions(
    report: &mut Report,
    theorems: &[Theorem],
    scopes: &[FileScope],
    g: &crate::formula::Grammar,
) {
    for thms in by_file(theorems).values() {
        let scope_id = thms[0].scope;
        let scope = &scopes[scope_id];
        let mut named: IndexMap<String, usize> = IndexMap::new();
        for alias in scope.linked.keys() {
            let no = scope
                .imports
                .iter()
                .find(|i| &i.alias == alias)
                .unwrap()
                .line;
            named.insert(alias.clone(), no);
        }
        // Every label a file gives outside its theorems is one label, cited
        // from any theorem below it.
        let mut tagged: IndexMap<String, usize> = IndexMap::new();
        let labels = scope
            .imports
            .iter()
            .filter_map(|i| Some((i.label.clone()?, i.line)))
            .chain(scope.defines.iter().map(|d| (d.label.clone(), d.line)));
        for (lab, no) in labels {
            if let Some(at) = tagged.get(&lab) {
                report.say(
                    &scope.path,
                    no,
                    format!("label {lab} is already used at line {at}"),
                );
            }
            tagged.entry(lab).or_insert(no);
        }
        for d in &scope.defines {
            let Built(said) = define_parts(&d.text) else {
                continue;
            };
            for name in said.names() {
                if let Some(at) = named.get(&name) {
                    report.say(
                        &scope.path,
                        d.line,
                        format!("{name} is already defined at line {at}"),
                    );
                }
                named.entry(name).or_insert(d.line);
            }
            if !scope.readings.contains_key(&d.label) {
                report.say(
                    &scope.path,
                    d.line,
                    format!(
                        "define {} carries no `reads` line saying what the name means",
                        d.label
                    ),
                );
            }
        }
        let written = names_written(&file_tokens(theorems, scope_id, scope, g));
        for i in &scope.imports {
            if scope.linked.contains_key(&i.alias) && !written.contains(&i.alias) {
                let message = if i.alias != i.name {
                    format!(
                        "imports definition {} as {} and never uses it",
                        i.name, i.alias
                    )
                } else {
                    format!("imports definition {} and never uses it", i.name)
                };
                report.say(&scope.path, i.line, message);
            }
        }
        // An imported define's label is what a line writing the define out
        // cites, so a label no line cites is given for nothing.
        let cited: IndexSet<String> = thms
            .iter()
            .flat_map(|t| &t.steps)
            .flat_map(|s| {
                let just = &s.just;
                just.refs
                    .iter()
                    .cloned()
                    .chain(just.defined.clone())
                    .chain(s.requires.iter().flat_map(|r| r.lines().to_vec()))
            })
            .chain(
                thms.iter()
                    .flat_map(|t| &t.defines)
                    .filter_map(|d| d.reason.as_ref())
                    .flat_map(|r| r.lines().to_vec()),
            )
            .collect();
        for i in &scope.imports {
            if let Some(label) = i.label.as_ref().filter(|l| !cited.contains(*l)) {
                report.say(
                    &scope.path,
                    i.line,
                    format!(
                        "import definition {}/{} gives the label {label}, which no line cites; a label is given only where a line writes the define out",
                        i.module, i.name
                    ),
                );
            }
        }
        for thm in thms {
            let shown = visible(scopes, scope_id, thm.line);
            let seen: IndexSet<&str> =
                shown.iter().map(|(n, _, _)| n.as_str()).collect();
            let mut labels: IndexSet<&str> = shown
                .iter()
                .filter(|(_, _, src)| *src == scope_id)
                .map(|(_, d, _)| d.label.as_str())
                .collect();
            labels.extend(scope.imports.iter().filter_map(|i| i.label.as_deref()));
            for d in &thm.defines {
                if let Built(said) = define_parts(&d.text) {
                    for name in said.names() {
                        if seen.contains(name.as_str()) {
                            report.say(
                                &thm.path,
                                d.line,
                                format!(
                                    "{name} is already defined outside theorem {}",
                                    thm.name
                                ),
                            );
                        }
                    }
                }
                if labels.contains(d.label.as_str()) {
                    report.say(
                        &thm.path,
                        d.line,
                        format!(
                            "label {} is already a define's outside theorem {}",
                            d.label, thm.name
                        ),
                    );
                }
            }
            for h in &thm.hypotheses {
                if let Some(lab) = &h.label {
                    if labels.contains(lab.as_str()) {
                        report.say(
                            &thm.path,
                            h.line,
                            format!(
                                "label {lab} is already a define's outside theorem {}",
                                thm.name
                            ),
                        );
                    }
                }
            }
        }
    }
}

/// A proof file imports each item it cites from another file, one to a
/// line, with the item's kind as the keyword, and cites each item it
/// imports.
///
/// Every name the file cites is distinct within it: its own theorems, and
/// each import under the name it gives. The imports have no cycle, because
/// the theorems a file imports are built before its own. A library file
/// imports nothing and is no part of that order.
pub fn check_imports(
    report: &mut Report,
    theorems: &[Theorem],
    scopes: &[FileScope],
    items: &IndexMap<String, Item>,
    library: &IndexSet<String>,
) {
    let files = by_file(theorems);
    let mut graph: IndexMap<&str, IndexMap<String, usize>> = IndexMap::new();
    for (module, thms) in &files {
        let path = &thms[0].path;
        let scope = &scopes[thms[0].scope];
        // Each name the file gives, and what gives it.
        let mut given: IndexMap<&str, String> = IndexMap::new();
        for thm in thms {
            given
                .entry(thm.name.as_str())
                .or_insert_with(|| format!("theorem {} of this file", thm.name));
        }
        for i in &scope.imports {
            given
                .entry(i.alias.as_str())
                .or_insert_with(|| format!("the import at line {}", i.line));
        }
        for f in &scope.functions {
            given
                .entry(f.name.as_str())
                .or_insert_with(|| format!("the import at line {}", f.line));
        }
        let mut imported: IndexSet<String> = IndexSet::new();
        let mut edges: IndexMap<String, usize> = IndexMap::new();
        for i in &scope.items {
            let (no, full_name) = (i.line, i.full());
            let keyword = &i.said;
            if !imported.insert(full_name.clone()) {
                report.say(path, no, format!("{full_name} is imported twice"));
                continue;
            }
            if let Some(other) = given.get(i.alias.as_str()) {
                report.say(
                    path,
                    no,
                    format!(
                        "{} is already the name of {other}; import one of them under another name with `as`",
                        i.alias
                    ),
                );
            } else {
                given.insert(&i.alias, format!("the import at line {no}"));
            }
            if i.module == *module {
                report.say(
                    path,
                    no,
                    format!("{full_name} is a theorem of this file, which is cited with no import"),
                );
                continue;
            }
            if !library.contains(&i.module) && !files.contains_key(i.module.as_str()) {
                report.say(
                    path,
                    no,
                    format!("import {keyword} {full_name}: {} is no file", i.module),
                );
                continue;
            }
            match items.get(&full_name) {
                None => report.say(
                    path,
                    no,
                    format!(
                        "import {keyword} {full_name}: {} holds no item {}",
                        i.module, i.name
                    ),
                ),
                Some(item) if item.header() != i.said => report.say(
                    path,
                    no,
                    format!(
                        "import {keyword} {full_name}: {full_name} is {}; import it as `import {} {full_name}`",
                        item.described(),
                        item.header()
                    ),
                ),
                Some(_) => {}
            }
            if files.contains_key(i.module.as_str()) {
                edges.entry(i.module.clone()).or_insert(no);
            }
        }
        let cited: IndexSet<String> = thms
            .iter()
            .flat_map(|thm| cited_items(thm).into_iter().map(|(name, _)| name))
            .collect();
        for i in &scope.items {
            if !cited.contains(&i.full()) {
                report.say(
                    path,
                    i.line,
                    format!("imports {} and cites nothing by it", i.alias),
                );
            }
        }
        // A definition imported is a file read before this one, as a proof
        // file cited is, so it is an edge of the same graph.
        for i in &scope.imports {
            if files.contains_key(i.module.as_str()) && i.module != *module {
                edges.entry(i.module.clone()).or_insert(i.line);
            }
        }
        graph.insert(module, edges);
    }

    fn visit<'g>(
        module: &'g str,
        graph: &'g IndexMap<&str, IndexMap<String, usize>>,
        files: &IndexMap<&str, Vec<&Theorem>>,
        done: &mut IndexSet<&'g str>,
        trail: &mut Vec<&'g str>,
        report: &mut Report,
    ) {
        if done.contains(module) {
            return;
        }
        trail.push(module);
        if let Some(edges) = graph.get(module) {
            for (name, no) in edges {
                if let Some(at) = trail.iter().position(|m| *m == name) {
                    let mut cycle: Vec<&str> = trail[at..].to_vec();
                    cycle.push(name);
                    report.say(
                        &files[module][0].path,
                        *no,
                        format!("import {name} closes a cycle: {}", cycle.join(" → ")),
                    );
                } else {
                    visit(name, graph, files, done, trail, report);
                }
            }
        }
        trail.pop();
        done.insert(module);
    }

    let mut done: IndexSet<&str> = IndexSet::new();
    let mut trail: Vec<&str> = Vec::new();
    let mut modules: Vec<&str> = graph.keys().copied().collect();
    modules.sort();
    for module in modules {
        visit(module, &graph, &files, &mut done, &mut trail, report);
    }
}

/// The names in a list a binder writes, `x` or `x, y`.
fn names_listed(list: &str) -> Vec<String> {
    list.split(',').map(|n| str::trim(n).to_string()).collect()
}

/// The names a theorem introduces itself: its `let` lines, a block's, and
/// what its `obtain` steps obtain. Not every name it gives a sort: `c = 5`
/// gives c one, and introduces nothing.
pub fn introduced(thm: &Theorem) -> BTreeSet<String> {
    let mut out: BTreeSet<String> = named_by_hypotheses(thm);
    for h in &thm.hypotheses {
        out.extend(let_name(&h.text).map(String::from));
    }
    for s in &thm.steps {
        for o in &s.openers {
            if o.kind == Intro::Let {
                out.extend(let_name(&o.text).map(String::from));
            }
        }
        if s.just.head.is(Method::Obtain) {
            out.extend(s.just.obtained.iter().cloned());
        }
    }
    out
}

/// The letters a line of `step` may write free: the theorem's hypotheses,
/// the defines above it, the library functions in scope, the `let` lines of
/// the blocks around it (of its own part only, as `labels_in_scope` reads
/// labels), and what the steps it may cite obtained, its own included.
pub fn letters_in_scope(
    thm: &Theorem,
    shape: &CheckedTheorem,
    step: &Step,
    scopes: &[FileScope],
    sorts: &Sorts,
) -> BTreeSet<String> {
    let mut out = letters_introduced(thm, shape, step);
    out.extend(
        visible(scopes, thm.scope, thm.line)
            .into_iter()
            .map(|(n, _, _)| n),
    );
    out.extend(sorts.imported.iter().cloned());
    for (i, d) in thm.defines.iter().enumerate() {
        if shape.define_in_scope(thm, i, step) {
            if let Built(said) = define_parts(&d.text) {
                out.extend(said.names());
            }
        }
    }
    out
}

/// The letters a theorem's hypotheses introduce: each `let`'s names, and of
/// a `let … be` line the things in the sets it lists, as a graph's vertices
/// and edges are named.
pub fn hypotheses_introduce(thm: &Theorem) -> BTreeSet<String> {
    let mut out: BTreeSet<String> = named_by_hypotheses(thm);
    for h in &thm.hypotheses {
        if let Some(names) = let_names(&h.text) {
            out.extend(names_listed(names));
        }
        if h.kind == Intro::Let {
            for list in listed(&h.text) {
                out.extend(names_listed(list));
            }
        }
    }
    out
}

/// The letters the page introduces that are in scope at `step`: the
/// theorem's hypotheses, the `let` lines of the blocks around it (of its own
/// part only), and what the steps it may cite obtained, its own included.
/// What a define or the library names is not among them.
pub fn letters_introduced(
    thm: &Theorem,
    shape: &CheckedTheorem,
    step: &Step,
) -> BTreeSet<String> {
    let mut out = hypotheses_introduce(thm);
    for other in &thm.steps {
        let k = other.number.len();
        let encloses =
            other.number == step.number.prefix(k) && other.number != step.number;
        if encloses {
            let child = on_the_way(thm, step, &step.number.prefix(k + 1));
            for o in &other.openers {
                let own_part =
                    o.part.is_none() || child.is_some_and(|c| c.part == o.part);
                if o.kind == Intro::Let && own_part {
                    if let Some(names) = let_names(&o.text) {
                        out.extend(names_listed(names));
                    }
                }
            }
        }
        let visible_here = other.number == step.number
            || out_of_reach(thm, shape, &other.number, step).is_none();
        if visible_here && other.just.head.is(Method::Obtain) {
            out.extend(other.just.obtained.iter().cloned());
        }
    }
    out
}

/// (name, line) for each name the tokens write that the theorem's file
/// defines outside its theorems only below it, and that the theorem does not
/// introduce itself: `own`, and what the text binds.
pub fn defined_below(
    thm: &Theorem,
    tokens: &[Vec<Token>],
    own: &BTreeSet<String>,
    scopes: &[FileScope],
) -> Vec<(String, usize)> {
    let mut seen: BTreeSet<String> = visible(scopes, thm.scope, thm.line)
        .into_iter()
        .map(|(n, _, _)| n)
        .collect();
    seen.extend(own.iter().cloned());
    seen.extend(bound_written(tokens));
    let written = names_written(tokens);
    let mut out = Vec::new();
    for d in &scopes[thm.scope].defines {
        let Built(said) = define_parts(&d.text) else {
            continue;
        };
        let Some(name) = said.name() else { continue };
        if d.line < thm.line || seen.contains(name) {
            continue;
        }
        if written.contains(name) {
            out.push((name.to_string(), d.line));
        }
    }
    out
}

/// A theorem uses only the definitions written above it.
///
/// Above its define a name names nothing: `c = 5` would be about a letter
/// nobody introduced, which parses and says nothing, and `U(0)` reads
/// several ways because nothing says U is a function. So a name the file
/// defines outside its theorems only further down, used in a theorem that
/// does not introduce it itself, is said once, at the theorem.
pub fn check_defined_below(
    report: &mut Report,
    thm: &Theorem,
    scopes: &[FileScope],
    g: &crate::formula::Grammar,
) {
    let tokens = theorem_tokens(thm, g);
    for (name, at) in defined_below(thm, &tokens, &introduced(thm), scopes) {
        report.say(
            &thm.path,
            thm.line,
            format!(
                "{name} is defined at line {at}, below theorem {}; a definition is used only below where it is written",
                thm.name
            ),
        );
    }
}
