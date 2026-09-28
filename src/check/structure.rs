//! The shape of a proof: numbering, blocks, citations and what they may
//! reach, imports, definitions, and the forms justifications take.

use std::collections::BTreeSet;

use indexmap::{IndexMap, IndexSet};

use super::{Report, CLOSURE, RELATIONS};
use crate::corpus::proof::{requires_item, starts_with_head, visible};
use crate::corpus::{
    cited_items, define_parts, fmt, full, in_stdlib, references, written_text,
    FileScope, Head, Intro, Item, Justification, Method, Record, RecordKind, Step,
    StepNo, Theorem, LABEL, NUMBER, REF,
};
use crate::matching::instantiation;
use crate::outcome::Built;
use crate::sorts::infer::obtains;
use crate::sorts::named_by_hypotheses;
use crate::text::{prefix, repr};
use crate::{fancy, regex};

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
        out.entry(i.label.clone())
            .or_insert(Declared::Define(i.line));
    }
    for d in &thm.defines {
        if d.line < step.line {
            out.insert(d.label.clone(), Declared::Define(d.line));
        }
    }
    let by_number: IndexMap<&StepNo, &Step> =
        thm.steps.iter().map(|s| (&s.number, s)).collect();
    for other in &thm.steps {
        let k = other.number.len();
        if other.number != step.number.prefix(k) || other.number == step.number {
            continue;
        }
        let child = by_number.get(&step.number.prefix(k + 1));
        for o in &other.openers {
            if o.part.is_none() || child.is_some_and(|c| c.part == o.part) {
                out.insert(o.label.clone(), Declared::Block(o.line));
            }
        }
    }
    out
}

fn inst() -> String {
    r"(?:[^\s,]+\s*:=\s*.+?)(?:,\s*[^\s,]+\s*:=\s*.+?)*".to_string()
}

fn from() -> String {
    format!(r"from\s+{REF}(?:\s*,\s*{REF})*")
}

fn productions() -> Vec<regex::Regex> {
    let cited = crate::corpus::CITED;
    let (inst, from) = (inst(), from());
    [
        format!(r"^(?:def|thm):{cited}(?:\s+{inst})?(?:,\s*{from})?$"),
        format!(r"^obtain\s+\S+(?:\s*,\s*\S+)*:\s*(?:def|thm):{cited}(?:\s+{inst})?(?:,\s*{from})?$"),
        format!(r"^obtain\s+\S+(?:\s*,\s*\S+)*\s+from\s+(?:line\s+{NUMBER}|{LABEL})$"),
        format!(r"^exhibit,\s*{from}$"),
        format!(r"^substitute\s+.+?\s*\((?:line\s+{NUMBER}|{LABEL}|arithmetic)\)(?:\s+into\s+(?:line\s+{NUMBER}|{LABEL}))?$"),
        format!(r"^instantiate\s+{inst}\s+in\s+(?:line\s+{NUMBER}|{LABEL})(?:,\s*{from})?$"),
        format!(r"^algebra(?:,\s*{from})?$"),
        r"^arithmetic$".to_string(),
        format!(r"^inequalities(?:,\s*{from})?$"),
        format!(r"^membership(?:,\s*{from})?$"),
        format!(r"^join\s+{REF}(?:\s*,\s*{REF})*$"),
        r"^contradiction$".to_string(),
        r"^fix$".to_string(),
        format!(r"^induction\s+on\s+\S+\s+starting\s+at\s+\S+,\s*{from}$"),
        format!(r"^cases,\s*{from}$"),
        r"^calculation$".to_string(),
        format!(r"^{LABEL}(?:,\s*{from})?$"),
    ]
    .iter()
    .map(|p| regex::Regex::new(p).unwrap())
    .collect()
}

static PRODUCTIONS: std::sync::LazyLock<Vec<regex::Regex>> =
    std::sync::LazyLock::new(productions);

/// The productions of `GRAMMAR.md`, one per justification form.
pub fn check_justification_form(
    report: &mut Report,
    path: &str,
    just: &Justification,
) -> bool {
    if !PRODUCTIONS.iter().any(|p| p.is_match(&just.text)) {
        report.say(
            path,
            just.line,
            format!(
                "justification matches no production in GRAMMAR.md: {}",
                repr(prefix(&just.text, 64))
            ),
        );
        return false;
    }
    true
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
        if step.just.head.is(Method::Fix)
            && !step
                .openers
                .iter()
                .any(|o| matches!(o.kind, Intro::Let | Intro::Assume))
        {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {} is a fix whose block does not open with `let` or `assume`",
                    step.number
                ),
            );
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

regex!(CHAIN_ITEM, r"\b(?:def|thm):");

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
    for (text, no) in &step.just.chain {
        if CHAIN_ITEM.is_match(text) || text.contains(":=") {
            report.say(
                &thm.path,
                *no,
                "a chain line carries a justification; a calculation only joins, so each line cites a numbered step or a label and the reasoning lives in that step",
            );
        }
        let related = RELATIONS.iter().any(|r| {
            text.trim_start().starts_with(r) || text.contains(&format!(" {r} "))
        });
        if !related {
            report.say(&thm.path, *no, "chain line carries no relation");
        }
    }
}

/// Every line's claim, by the reference that names it.
pub fn claims_of(thm: &Theorem) -> IndexMap<String, String> {
    let mut out: IndexMap<String, String> = thm
        .steps
        .iter()
        .map(|s| (fmt(&s.number), s.claim_text()))
        .collect();
    for h in &thm.hypotheses {
        if let Some(lab) = &h.label {
            out.insert(lab.clone(), h.text.clone());
        }
    }
    for s in &thm.steps {
        for o in &s.openers {
            out.insert(o.label.clone(), o.text.clone());
        }
    }
    out
}

/// What to say of a citation that names nothing.
fn unresolved(cited: &str) -> String {
    if !cited.contains('/') {
        return format!(
            "{cited} names no theorem of this file; an item of another file is cited by its full name"
        );
    }
    format!("{cited} resolves to no item")
}

regex!(LABEL_RE, LABEL);
regex!(FROM_REF, format!(r"^from\s+{REF}$"));

pub fn check_citations(
    report: &mut Report,
    thm: &Theorem,
    items: &IndexMap<String, Item>,
    methods: &IndexMap<String, &Record>,
    scopes: &[FileScope],
) {
    let numbers: IndexSet<&StepNo> = thm.steps.iter().map(|s| &s.number).collect();
    for step in &thm.steps {
        let just = &step.just;
        let scope = labels_in_scope(thm, step, scopes);
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
        for r in &just.refs {
            if full(&LABEL_RE, r) {
                if !scope.contains_key(r) {
                    report.say(
                        &thm.path,
                        just.line,
                        format!(
                            "step {} cites {r}, which is not in scope here",
                            step.number
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
            } else if !in_scope(&cited, &step.number) {
                report.say(
                    &thm.path,
                    just.line,
                    format!(
                        "step {} cites line {r}, which is inside a block that has closed",
                        step.number
                    ),
                );
            }
        }
        if let Some(target) = &just.target {
            if target.starts_with("def:") {
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
        match &just.head {
            Head::Item { kind, .. } => {
                let head = just.head.to_string();
                match items.get(&just.item(&head)) {
                    None => report.say(&thm.path, just.line, unresolved(&head)),
                    Some(item) if item.kind() != kind.record_kind() => report.say(
                        &thm.path,
                        just.line,
                        format!("{head} names a {}", item.kind()),
                    ),
                    Some(_) => {}
                }
            }
            Head::Define => {}
            Head::Method(m) => {
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
        }
        for req in &step.requires {
            let text = &req.how;
            let no = req.line;
            if !starts_with_head(text) && !FROM_REF.is_match(text) {
                report.say(
                    &thm.path,
                    no,
                    format!(
                        "requires line justified by {}, which is neither a method, an item, nor a line",
                        repr(prefix(text, 40))
                    ),
                );
            }
            // A requires line cites an item like any other citation, so its
            // pointer resolves and its prefix matches the item's kind.
            if let Some((cited, kind)) = requires_item(text) {
                match items.get(&just.item(&cited)) {
                    None => report.say(&thm.path, no, unresolved(&cited)),
                    Some(item) if item.kind() != kind.record_kind() => report.say(
                        &thm.path,
                        no,
                        format!("{cited} names a {}", item.kind()),
                    ),
                    Some(_) => {}
                }
            }
            let (refs, bad) = references(text);
            if let Some(bad) = bad {
                report.say(
                    &thm.path,
                    no,
                    format!(
                        "`from` names {}, which is neither a line nor a label",
                        repr(&bad)
                    ),
                );
            }
            for r in refs {
                if full(&LABEL_RE, &r) {
                    if !scope.contains_key(&r) {
                        report.say(
                            &thm.path,
                            no,
                            format!(
                                "requires line cites {r}, which is not in scope here"
                            ),
                        );
                    }
                    continue;
                }
                let cited = StepNo::parse(&r);
                if !numbers.contains(&cited) {
                    report.say(
                        &thm.path,
                        no,
                        format!("requires line cites line {r}, which does not exist"),
                    );
                } else if !in_scope(&cited, &step.number) {
                    report.say(
                        &thm.path,
                        no,
                        format!("requires line cites line {r}, which is inside a block that has closed"),
                    );
                }
            }
        }
        if let Some(m) = just.head.method() {
            if CLOSURE.contains(&m.as_str()) {
                report
                    .trusted
                    .push((m.as_str().to_string(), fmt(&step.number)));
            }
        }
    }
}

// `for all`, `there is` and `there exists` open a scope. The corpus
// capitalises each at the start of a sentence, so this is deliberately
// case-insensitive.
regex!(
    BINDER,
    r"(?i)(?:for all|there is(?: no)?|there exists)\s+([A-Za-zα-ω][₀-₉′]*)\s*∈"
);
fancy!(
    VARNAME,
    r"(?<![A-Za-zα-ω])([A-Za-zα-ω][₀-₉′]*)(?![A-Za-zα-ω])"
);
regex!(CAPTURE_TARGET, r"\bin\s+(?:line\s+)?([\w.]+)");

// Patterns whose holes sit next to each other with no token between them,
// so that the names filling them run together in the text.
regex!(ADJACENT_BARS, r"\|([A-Za-z]{2,})\|");
regex!(ADJACENT_ANGLE, r"∠([A-Za-z]{2,})");
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
) {
    for s in &thm.steps {
        for text in &s.claim {
            for pattern in [&*ADJACENT_BARS, &*ADJACENT_ANGLE] {
                for c in pattern.captures_iter(text) {
                    let run = &c[1];
                    if words.contains(run) {
                        report.say(
                            &thm.path,
                            s.line,
                            format!(
                                "step {} writes {} in a notation whose holes are adjacent, and {} is a declared word; rename one of the names so the two do not run together",
                                s.number,
                                repr(run),
                                repr(run)
                            ),
                        );
                    }
                }
            }
        }
    }
}

/// A substitution may not capture. If the term being substituted names a
/// variable bound where it lands, the step is rejected rather than the
/// variable quietly renamed, because renaming would make the machine do
/// something the page does not show.
pub fn check_capture(
    report: &mut Report,
    thm: &Theorem,
    claims: &IndexMap<String, String>,
) {
    for s in &thm.steps {
        if !s.just.head.is(Method::Instantiate) {
            continue;
        }
        let Some(m) = CAPTURE_TARGET.captures(&s.just.text) else {
            continue;
        };
        let landing = claims.get(&m[1]).map(String::as_str).unwrap_or("");
        let bound: BTreeSet<String> = BINDER
            .captures_iter(landing)
            .map(|c| c[1].to_string())
            .collect();
        if bound.is_empty() {
            continue;
        }
        for (v, value) in instantiation(&s.just.text) {
            // Substituting a variable for itself changes nothing and cannot
            // capture. A term that merely mentions the bound name does: that
            // mention refers to an outer binding and would be swallowed.
            if value == v {
                continue;
            }
            let named: BTreeSet<String> = VARNAME
                .captures_iter(&value)
                .filter_map(|c| c.ok())
                .map(|c| c[1].to_string())
                .collect();
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

/// Every variable's sort is on the page, so the parser never infers one.
///
/// A `let` line gives it, and so does the claim of the `obtain` step that
/// introduces a name. Without that rule a parser would have to chase the
/// cited item's conclusion to learn a sort, and sorts are what disambiguate
/// a notation, so two implementations chasing differently would parse the
/// same formula differently.
pub fn check_sorts(report: &mut Report, thm: &Theorem) {
    for s in &thm.steps {
        if !s.just.head.is(Method::Obtain) {
            continue;
        }
        let Some(names) = obtains(&s.just.text) else {
            continue;
        };
        let claim = s.claim_text();
        for v in names.split(',').map(str::trim) {
            if v.is_empty() {
                continue;
            }
            let n = regex::escape(v);
            // A part of a set is stated by ⊆ as surely as by ∈ 𝒫.
            let stated = [
                format!(r"(?<![A-Za-z]){n}\s*[∈⊆]"),
                format!(r"(?<![A-Za-z]){n}\s+is a (set|point)"),
                format!(r"(?<![A-Za-z]){n}\s*:"),
            ]
            .iter()
            .any(|p| {
                fancy_regex::Regex::new(p)
                    .ok()
                    .and_then(|re| re.is_match(&claim).ok())
                    .unwrap_or(false)
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
                    "define {} carries no `reads` line saying what the name means",
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

pub fn check_last_step(report: &mut Report, thm: &Theorem) {
    if thm.steps.is_empty() {
        report.say(
            &thm.path,
            thm.line,
            format!("theorem {} has no steps", thm.name),
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

fn word_bounded(name: &str) -> fancy_regex::Regex {
    fancy_regex::Regex::new(&format!(r"(?<![\w]){}(?![\w])", regex::escape(name)))
        .unwrap()
}

/// What a proof file defines outside its theorems and what it imports.
///
/// Two definitions of one name are a defect wherever both could be read:
/// two the file writes, one it writes and one it imports, two it imports,
/// or a proof's own define under a name the file already gives something.
/// A definition imported and never used is a defect, as an import cited
/// from nowhere is. A define outside a theorem carries a reading like any
/// other, and its label is not one a theorem below it also uses.
pub fn check_definitions(
    report: &mut Report,
    theorems: &[Theorem],
    scopes: &[FileScope],
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
            .map(|i| (i.label.clone(), i.line))
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
        let mut parts: Vec<String> = thms.iter().map(|t| written_text(t)).collect();
        parts.extend(scope.defines.iter().map(|d| d.text.clone()));
        let text = parts.join(" ");
        for i in &scope.imports {
            if scope.linked.contains_key(&i.alias)
                && !word_bounded(&i.alias).is_match(&text).unwrap_or(false)
            {
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
        for thm in thms {
            let shown = visible(scopes, scope_id, thm.line);
            let seen: IndexSet<&str> =
                shown.iter().map(|(n, _, _)| n.as_str()).collect();
            let mut labels: IndexSet<&str> = shown
                .iter()
                .filter(|(_, _, src)| *src == scope_id)
                .map(|(_, d, _)| d.label.as_str())
                .collect();
            labels.extend(scope.imports.iter().map(|i| i.label.as_str()));
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

/// A proof file imports exactly the other proof files it cites.
///
/// The standard library is never imported: every proof may cite it. The
/// imports have no cycle, because the theorems a file imports are built
/// before its own.
pub fn check_imports(report: &mut Report, theorems: &[Theorem], scopes: &[FileScope]) {
    let files = by_file(theorems);
    let mut graph: IndexMap<&str, IndexMap<String, usize>> = IndexMap::new();
    for (module, thms) in &files {
        let path = &thms[0].path;
        let scope = &scopes[thms[0].scope];
        let mut said: IndexMap<String, usize> = IndexMap::new();
        let mut seen: IndexSet<&str> = IndexSet::new();
        for (name, no) in &scope.proof_imports {
            if seen.contains(name.as_str()) {
                report.say(path, *no, format!("{name} is imported twice"));
                continue;
            }
            seen.insert(name);
            if name == crate::corpus::STDLIB || in_stdlib(name) {
                report.say(
                    path,
                    *no,
                    format!(
                        "import {name}: the standard library is never imported, and every proof may cite it"
                    ),
                );
            } else if name == module {
                report.say(path, *no, format!("{name} imports itself"));
            } else if !files.contains_key(name.as_str()) {
                report.say(path, *no, format!("import {name} names no proof file"));
            } else {
                said.insert(name.clone(), *no);
            }
        }
        let mut cited: IndexMap<String, (String, usize)> = IndexMap::new();
        for thm in thms {
            for (full_name, no) in cited_items(thm) {
                let other = match full_name.rfind('/') {
                    Some(at) => full_name[..at].to_string(),
                    None => full_name.clone(),
                };
                if other != *module && !in_stdlib(&full_name) {
                    cited.entry(other).or_insert((full_name, no));
                }
            }
        }
        for (other, (full_name, no)) in &cited {
            if files.contains_key(other.as_str()) && !seen.contains(other.as_str()) {
                report.say(
                    path,
                    *no,
                    format!("{full_name} is cited and {other} is not imported"),
                );
            }
        }
        for (name, no) in &said {
            if !cited.contains_key(name) {
                report.say(
                    path,
                    *no,
                    format!("imports {name} and cites nothing from it"),
                );
            }
        }
        // A definition imported is a file read before this one, as a proof
        // file cited is, so it is an edge of the same graph.
        let mut edges = said.clone();
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

// A name a formula binds for itself: `for all c ∈ ℕ`, `there is c ∈ A`,
// `{c ∈ A : …}`, `Σ(c = 1 to n)`, `the map sending c ∈ A to …`.
regex!(
    BOUND_HERE,
    r"(?:for all|there (?:is|are|exists)(?: no)?|sending|\{|Σ\()\s*([A-Za-zα-ω][₀-₉′]*)\s*(?:∈|=)"
);
regex!(LET_NAME, r"^let\s+([^\s∈∉:]+)");

/// The names a theorem introduces itself: its `let` lines, a block's, and
/// what its `obtain` steps obtain. Not every name it gives a sort: `c = 5`
/// gives c one, and introduces nothing.
pub fn introduced(thm: &Theorem) -> BTreeSet<String> {
    let mut out: BTreeSet<String> = named_by_hypotheses(thm);
    for h in &thm.hypotheses {
        if let Some(m) = LET_NAME.captures(&h.text) {
            out.insert(m[1].to_string());
        }
    }
    for s in &thm.steps {
        for o in &s.openers {
            if o.kind == Intro::Let {
                if let Some(m) = LET_NAME.captures(&o.text) {
                    out.insert(m[1].to_string());
                }
            }
        }
        if s.just.head.is(Method::Obtain) {
            if let Some(names) = obtains(&s.just.text) {
                out.extend(names.split(',').map(|n| str::trim(n).to_string()));
            }
        }
    }
    out
}

/// (name, line) for each name `text` writes that the theorem's file defines
/// outside its theorems only below it, and that the theorem does not
/// introduce itself: `own`, and what the text binds.
pub fn defined_below(
    thm: &Theorem,
    text: &str,
    own: &BTreeSet<String>,
    scopes: &[FileScope],
) -> Vec<(String, usize)> {
    let mut seen: BTreeSet<String> = visible(scopes, thm.scope, thm.line)
        .into_iter()
        .map(|(n, _, _)| n)
        .collect();
    seen.extend(own.iter().cloned());
    seen.extend(BOUND_HERE.captures_iter(text).map(|c| c[1].to_string()));
    let mut out = Vec::new();
    for d in &scopes[thm.scope].defines {
        let Built(said) = define_parts(&d.text) else {
            continue;
        };
        let Some(name) = said.name() else { continue };
        if d.line < thm.line || seen.contains(name) {
            continue;
        }
        if word_bounded(name).is_match(text).unwrap_or(false) {
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
pub fn check_defined_below(report: &mut Report, thm: &Theorem, scopes: &[FileScope]) {
    for (name, at) in defined_below(thm, &written_text(thm), &introduced(thm), scopes) {
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
