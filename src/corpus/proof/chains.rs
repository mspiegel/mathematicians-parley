//! Imports, header words, calculation chains and substitute rows.

use std::iter;

use super::*;

pub(super) enum Imported {
    Item(ItemImport),
    Define(Import),
}

/// The words an `import` or `forbid` line writes before its path, read as a
/// record's header, and the path cut into its file and the item's name.
pub(super) struct HeaderWords<'t> {
    /// What a citation of the item writes, which the words say.
    pub(super) kind: ItemKind,
    pub(super) record_kind: RecordKind,
    /// The words as one text: `mundane theorem`, `axiom`.
    pub(super) keyword: String,
    pub(super) module: &'t str,
    pub(super) name: &'t str,
}

/// The words `line`, `import` or `forbid`, writes before `whole`: a kind an
/// item may have, with `mundane` only before `theorem`, and a path naming a
/// file. Whether they are the header of the item the path names is the
/// checker's to ask, since it wants the item.
pub(super) fn header_words<'t>(
    path: &str,
    no: usize,
    line: &str,
    mundane: bool,
    word: &str,
    whole: &'t str,
) -> Checked<HeaderWords<'t>> {
    let Some(record_kind) = RecordKind::parse(word).filter(|k| k.is_item()) else {
        return Err(Problem::new(
            path,
            no,
            format!(
                "{line} {word}: {} says the header of the item it names, its kind, axiom, theorem or definition, with mundane before a theorem taken for granted, as `{line} mundane theorem stdlib/numbers/int-closure`",
                if line == "import" { "an import" } else { "a forbid" }
            ),
        ));
    };
    if mundane && record_kind != RecordKind::Theorem {
        return Err(Problem::new(
            path,
            no,
            format!(
                "{line} mundane {word} {whole}: an axiom or a definition gives meaning, and a pedantic textbook cites it, so it is never mundane; {line} it as `{line} {word} {whole}`"
            ),
        ));
    }
    let kind = if mundane {
        ItemKind::Mundane
    } else {
        match record_kind {
            RecordKind::Axiom => ItemKind::Axiom,
            RecordKind::Definition => ItemKind::Definition,
            _ => ItemKind::Theorem,
        }
    };
    let keyword = if mundane {
        format!("mundane {word}")
    } else {
        word.to_string()
    };
    let (module, name) = match whole.rfind('/') {
        Some(at) => (&whole[..at], &whole[at + 1..]),
        None => ("", whole),
    };
    if module.is_empty() {
        return Err(Problem::new(
            path,
            no,
            format!("{line} {keyword} {whole} names no file"),
        ));
    }
    Ok(HeaderWords {
        kind,
        record_kind,
        keyword,
        module,
        name,
    })
}

/// One `forbid` line: one item the file does not import, with the words its
/// record's header says before its name. It changes nothing in how the file
/// is read; the checker holds the file's imports to it.
pub(super) fn forbidding(path: &str, no: usize, text: &str) -> Checked<Forbid> {
    let Some(m) = skeleton::forbid_line(text) else {
        return Err(Problem::new(
            path,
            no,
            "a forbid says `forbid <kind> <file>/<name>`, as `forbid theorem stdlib/geometry/law-of-cosines` does",
        ));
    };
    let words = header_words(path, no, "forbid", m.mundane, m.kind, m.full)?;
    Ok(Forbid {
        said: words.keyword,
        module: words.module.to_string(),
        name: words.name.to_string(),
        line: no,
    })
}

/// One `import` line: one item, with the words its record's header says
/// before its name, `mundane` for a theorem a proof takes for granted and
/// then its kind.
///
/// `import theorem stdlib/divisibility/prime-factor` brings in an item a step
/// cites, `thm:prime-factor`, or by the name after `as`, and
/// `import mundane theorem stdlib/numbers/int-closure` one it cites
/// `mun:int-closure`. A library function is read here as any library item
/// is, and `link_functions` sets it apart once the records are read. A define
/// of a proof file is brought in as a `definition`, under one letter, with
/// the label a line of this file cites it by where a line does. Whether the
/// words are the header of what the line names is the checker's to ask,
/// since it wants the item.
pub(super) fn importing(path: &str, no: usize, text: &str) -> Checked<Imported> {
    let Some(m) = skeleton::import_line(text) else {
        return Err(Problem::new(
            path,
            no,
            "an import says `import <kind> <file>/<name>`, as `import theorem stdlib/divisibility/prime-factor` does",
        ));
    };
    let whole = m.full;
    let HeaderWords {
        kind,
        record_kind,
        keyword,
        module,
        name,
    } = header_words(path, no, "import", m.mundane, m.kind, whole)?;
    let alias = m.alias.unwrap_or(name);
    let label = m.label.map(String::from);
    let from_library = in_stdlib(whole);
    // A define of a proof file is written in formulas, and cited by the
    // label its import gives it, as one the file defines is: a calculation
    // link writing S(k + 1) out cites the equation. A file that never writes
    // it out gives it no label. A define of a phrase is named by a word, as
    // an item is, and is imported and cited as one, `def:<name>`.
    if !from_library
        && record_kind == RecordKind::Definition
        && super::super::define::is_one_name(name)
    {
        if !super::super::define::is_one_name(alias) {
            return Err(Problem::new(
                path,
                no,
                format!(
                    "a define is imported under one letter, perhaps with a subscript or a prime, and {} is not one",
                    repr(alias)
                ),
            ));
        }
        return Ok(Imported::Define(Import {
            module: module.to_string(),
            name: name.to_string(),
            alias: alias.to_string(),
            line: no,
            label,
        }));
    }
    // Everything else is written only in a justification, by its prefix and
    // the name it is imported under.
    if label.is_some() {
        return Err(Problem::new(
            path,
            no,
            format!(
                "import {keyword} {whole}: only a define of a proof file carries a label"
            ),
        ));
    }
    for said in [name, alias] {
        if !skeleton::is_name(said) {
            return Err(Problem::new(
                path,
                no,
                format!(
                    "import {keyword} {whole}: {} is not an item's name",
                    repr(said)
                ),
            ));
        }
    }
    Ok(Imported::Item(ItemImport {
        kind,
        said: keyword,
        module: module.to_string(),
        name: name.to_string(),
        alias: alias.to_string(),
        line: no,
    }))
}

/// What a chain line cites, read from its reason (`skeleton::chain_reason`)
/// rather than from the whitespace that happens to separate it: the line or
/// label it gives, or every line its reason names, `from 3` and `line 1`
/// among them.
///
/// A link relating numerals alone may name `arithmetic` in place of a line,
/// and then it cites nothing: the fact is worked out where it stands.
pub(super) fn chain_citation(path: &str, line: &Line) -> Checked<Vec<String>> {
    let Some(reason) = skeleton::chain_reason(&line.text) else {
        return Err(Problem::new(
            path,
            line.no,
            "chain line gives no reason; each line ends on a numbered step or a label it cites, or on its own reason: `algebra`, `arithmetic`, `real arithmetic`, `substitute line L`, `instantiate`, or a theorem or definition cited as a step cites it",
        ));
    };
    if skeleton::is_ref(reason) {
        return Ok(vec![reason.to_string()]);
    }
    if is_worked_out(reason) {
        return Ok(Vec::new());
    }
    Ok(cut_reason(reason, path, line.no)?.refs())
}

/// Whether a chain line's reason is `arithmetic` or `real arithmetic`,
/// which work a link out where it stands and cite nothing.
pub(super) fn is_worked_out(reason: &str) -> bool {
    matches!(reason, "arithmetic" | "real arithmetic")
}

/// The line or label a chain line or a row gives as its reason; None for
/// one giving a reason of its own, `arithmetic` or `algebra` among them, or
/// none.
pub fn chain_cited(text: &str) -> Option<String> {
    skeleton::chain_reason(text)
        .filter(|reason| skeleton::is_ref(reason))
        .map(String::from)
}

/// The relations a chain line joins by (`GRAMMAR.md`, calculation chains).
pub const CHAIN_RELATIONS: [&str; 6] = ["=", "≤", "<", "≥", ">", "≡"];

/// Each order a chain going down joins by, with the one it is read as going
/// up: `a ≥ b` is `b ≤ a`.
pub(super) const DOWNWARD: [(&str, &str); 2] = [("≥", "≤"), (">", "<")];

/// One line of a calculation, cut as `GRAMMAR.md`'s chain productions cut
/// it: the relation it joins by, the term it reaches, the modulus a `≡`
/// line says, and its reason.
#[derive(Clone, Debug)]
pub struct ChainLine {
    pub relation: String,
    pub term: Written,
    pub modulus: Option<Written>,
    /// The reason as written (`skeleton::chain_reason`): the line or label
    /// it cites, `arithmetic`, `real arithmetic`, or a reason of its own.
    pub cite: String,
    /// Where `cite` starts in the chain line's text.
    pub cite_at: usize,
    /// A reason of its own, `algebra` or `mun:x, from 3`, read as a
    /// requires line is: the link as its fact, proved as the step it would
    /// be (`reason_as_step`). None where the line cites a line or a label,
    /// or names `arithmetic` or `real arithmetic`.
    pub reason: Option<Requires>,
    pub line: usize,
}

impl ChainLine {
    /// The line or label the link cites; None where it names `arithmetic`
    /// and cites nothing, or gives a reason of its own.
    pub fn cited(&self) -> Option<&str> {
        skeleton::is_ref(&self.cite).then_some(self.cite.as_str())
    }

    /// The link as the page writes it, from the term `from` before it, for
    /// a message to quote: `1 = 1(1 + 1)/3`. It is never read.
    pub fn quoted(&self, from: &Written) -> String {
        let modulus = match &self.modulus {
            Some(n) => format!(" (mod {n})"),
            None => String::new(),
        };
        format!("{from} {} {}{modulus}", self.relation, self.term)
    }
}

/// A calculation: the term its first line starts from, and each line's
/// link from the term before it.
#[derive(Clone, Debug)]
pub struct Chain {
    pub start: Written,
    pub lines: Vec<ChainLine>,
}

impl Chain {
    /// Whether the chain goes down: one of its orders is ≥ or >, so that
    /// `upward` reads its links from the last term.
    pub fn falls(&self) -> bool {
        self.lines
            .iter()
            .any(|l| DOWNWARD.iter().any(|(d, _)| *d == l.relation))
    }

    /// The chain read going up: one whose orders go down, t₀ ≥ t₁ > t₂,
    /// is the same links read from its last term, t₂ < t₁ ≤ t₀, and
    /// concludes the same, since t₀ > t₂ is t₂ < t₀. A chain going up is
    /// itself.
    pub fn upward(&self) -> Chain {
        let down = |r: &str| DOWNWARD.iter().find(|(d, _)| *d == r).map(|(_, u)| *u);
        if !self.falls() {
            return self.clone();
        }
        let terms: Vec<&Written> = iter::once(&self.start)
            .chain(self.lines.iter().map(|l| &l.term))
            .collect();
        let lines = (0..self.lines.len())
            .rev()
            .map(|i| {
                let l = &self.lines[i];
                ChainLine {
                    relation: down(&l.relation).unwrap_or(&l.relation).to_string(),
                    term: terms[i].clone(),
                    modulus: None,
                    cite: l.cite.clone(),
                    cite_at: l.cite_at,
                    reason: l.reason.clone(),
                    line: l.line,
                }
            })
            .collect();
        Chain {
            start: terms[terms.len() - 1].clone(),
            lines,
        }
    }
}

/// What a row of an `inequalities` step names as its reason (`METHODS.md`,
/// inequalities, Rows).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RowReason {
    /// The line the first row writes out, by its reference.
    Cited(String),
    /// A term added to both sides.
    Adding(Written),
    /// Both sides multiplied by a number.
    Multiplying(Written),
    /// A relation turned round: an equation's two sides swapped, or an order
    /// or a `≠` read from its other side.
    Restate,
    /// A relation weakened.
    Weakening,
    /// A side written as the same number another way.
    Algebra,
}

/// One row of an `inequalities` step: the formula, the reason, and the line.
#[derive(Clone, Debug)]
pub struct Row {
    pub formula: Written,
    pub reason: RowReason,
    /// Where the line a `RowReason::Cited` names is written in the row's
    /// text; None for any other reason.
    pub cited_at: Option<usize>,
    pub line: usize,
}

/// The words a row's reason opens with that a term follows.
pub(super) const ROW_WORDS: [&str; 2] = ["adding", "multiplying by"];

/// The rows an `inequalities` step writes, each cut as `GRAMMAR.md`'s
/// inequality rows cut it, from the right: a last word that is a reference,
/// `restate`, `weakening` or `algebra`, or `adding` or `multiplying by` and
/// a term. None for a step with no rows; a row with no reason is a defect,
/// and so is one ending in `symmetry`, a word kept back for later.
pub fn rows(just: &Justification, path: &str) -> Option<Checked<Vec<Row>>> {
    if just.rows.is_empty() || !just.head.is(Method::Inequalities) {
        return None;
    }
    let mut out = Vec::new();
    for (text, no) in &just.rows {
        let whole = str::trim(text);
        // A formula writes neither `adding` nor `multiplying by`, so where a
        // row does, its reason starts there and the term after it may be
        // anything, a lone letter that would read as a label among them.
        let worded = ROW_WORDS
            .iter()
            .filter_map(|w| whole.rfind(&format!(" {w} ")).map(|at| (at, *w)))
            .max_by_key(|(at, _)| *at)
            .map(|(at, w)| {
                let term =
                    Written::new(str::trim(&whole[at + w.len() + 2..]), path, *no);
                let reason = if w == "adding" {
                    RowReason::Adding(term)
                } else {
                    RowReason::Multiplying(term)
                };
                (str::trim(&whole[..at]), reason)
            });
        let last = whole.rsplit(char::is_whitespace).next().unwrap_or(whole);
        let before_last = str::trim(&whole[..whole.len() - last.len()]);
        if last == "symmetry" {
            return Some(Err(Problem::new(
                path,
                *no,
                "`symmetry` is kept back for later; a row turning a relation round is `restate`",
            )));
        }
        let word = match last {
            "restate" => Some(RowReason::Restate),
            "weakening" => Some(RowReason::Weakening),
            "algebra" => Some(RowReason::Algebra),
            _ if skeleton::is_ref(last) => Some(RowReason::Cited(last.to_string())),
            _ => None,
        };
        let cut = worded.or(word.map(|reason| (before_last, reason)));
        let Some((formula, reason)) = cut.filter(|(f, _)| !f.is_empty()) else {
            return Some(Err(Problem::new(
                path,
                *no,
                "a row gives no reason: it ends in the line it writes out, `adding` or `multiplying by` and a term, `restate`, `weakening` or `algebra`",
            )));
        };
        let cited_at =
            matches!(reason, RowReason::Cited(_)).then(|| skeleton::offset(text, last));
        out.push(Row {
            formula: Written::new(formula, path, *no),
            reason,
            cited_at,
            line: *no,
        });
    }
    Some(Ok(out))
}

/// The chain a calculation writes, cut by the skeleton; None for a
/// justification that is not a calculation. The first line's relation is
/// the first of `CHAIN_RELATIONS` it writes outside brackets, and one with
/// none is a defect.
pub fn chain(just: &Justification, path: &str) -> Option<Checked<Chain>> {
    if !just.head.is(Method::Calculation) || just.chain.is_empty() {
        return None;
    }
    let mut start = None;
    let mut lines = Vec::new();
    for (i, (text, no)) in just.chain.iter().enumerate() {
        let whole = str::trim(text);
        // The reason is where `chain_reason` finds it, so that `real
        // arithmetic` is cut whole and the term does not end in "real".
        let (body, cite) = match skeleton::chain_reason(whole) {
            Some(cite) => (str::trim(&whole[..whole.len() - cite.len()]), cite),
            None => match whole.rfind(char::is_whitespace) {
                Some(at) => (str::trim(&whole[..at]), str::trim(&whole[at..])),
                None => ("", whole),
            },
        };
        let words: Vec<&str> = body.split_whitespace().collect();
        // A link cites one line (`SYNTAX.md`), so one written `1, 2` has its
        // first citation end the term with a comma.
        if words.last().is_some_and(|w| w.ends_with(',')) {
            let named = words
                .iter()
                .rev()
                .take_while(|w| w.ends_with(','))
                .map(|w| w.trim_end_matches(','))
                .collect::<Vec<_>>();
            let mut named: Vec<&str> = named.into_iter().rev().collect();
            named.push(cite);
            return Some(Err(Problem::new(
                path,
                *no,
                format!(
                    "a calculation line cites one line or label, and this one cites {}; a step with several cites them, and its line cites that step",
                    named.join(", ")
                ),
            )));
        }
        let at = if i == 0 {
            let found = (0..words.len()).find(|&at| {
                CHAIN_RELATIONS.contains(&words[at])
                    && outermost(&words, words[at]) == Some(at)
            });
            let Some(at) = found else {
                return Some(Err(Problem::new(
                    path,
                    *no,
                    "a chain's first line writes no =, ≤, <, ≥, > or ≡ outside brackets",
                )));
            };
            start = Some(Written::new(words[..at].join(" "), path, *no));
            at
        } else {
            0
        };
        let Some(relation) = words.get(at).map(|w| w.to_string()) else {
            return Some(Err(Problem::new(
                path,
                *no,
                "a chain line writes no relation",
            )));
        };
        let rest = words.get(at + 1..).unwrap_or(&[]).join(" ");
        let (term, modulus) = skeleton::chain_modulus(&rest);
        let modulus = modulus.map(|m| Written::new(str::trim(m), path, *no));
        lines.push(ChainLine {
            relation,
            term: Written::new(term, path, *no),
            modulus,
            cite: cite.to_string(),
            cite_at: skeleton::offset(text, cite),
            reason: None,
            line: *no,
        });
    }
    // A reason of its own proves the link as written, from the term the
    // line before reaches: a formula made from the two terms, never read
    // from text.
    let start = start.expect("a first line");
    let mut from = start.clone();
    for line in &mut lines {
        if !skeleton::is_ref(&line.cite) && !is_worked_out(&line.cite) {
            let by = cut_reason(&line.cite, path, line.line).map(|slots| {
                Justification::of(slots, line.line, &just.names).shifted(line.cite_at)
            });
            let fact = Written::related(
                from.clone(),
                &line.relation,
                line.term.clone(),
                line.modulus.clone(),
                path,
                line.line,
            );
            line.reason = Some(Requires {
                fact,
                how: line.cite.clone(),
                line: line.line,
                by,
            });
        }
        from = line.term.clone();
    }
    // A chain goes one way: a ≤ b ≥ c says nothing of a against c.
    let up = lines
        .iter()
        .find(|l| l.relation == "≤" || l.relation == "<");
    let down = lines
        .iter()
        .find(|l| l.relation == "≥" || l.relation == ">");
    if let (Some(up), Some(down)) = (up, down) {
        let later = if up.line > down.line { up } else { down };
        let earlier = if up.line > down.line { down } else { up };
        return Some(Err(Problem::new(
            path,
            later.line,
            format!(
                "a chain goes one way, and this line says {} after one saying {}; {} after {} says nothing of the first term against the last",
                later.relation, earlier.relation, later.relation, earlier.relation
            ),
        )));
    }
    Some(Ok(Chain { start, lines }))
}

/// The reasons of their own that a calculation's lines give
/// (`ChainLine::reason`), and those a `substitute` step's rows give
/// (`SubstituteRow::reason`), in the order written; none for a step that has
/// neither, or whose lines do not cut, which the checker reports.
pub fn chain_reasons(just: &Justification, path: &str) -> Vec<Requires> {
    if let Some(Ok(chain)) = chain(just, path) {
        return chain.lines.into_iter().filter_map(|l| l.reason).collect();
    }
    if let Some(Ok(rows)) = substitute_rows(just, path) {
        return rows.into_iter().filter_map(|r| r.reason).collect();
    }
    Vec::new()
}

/// One row of a `substitute` step (`GRAMMAR.md`, substitute rows): the
/// statement it writes, and its reason. The first row is a line the step
/// cites, written out; each row after it is the row above with one term
/// put for another, and its reason proves the two terms equal.
#[derive(Clone, Debug)]
pub struct SubstituteRow {
    pub formula: Written,
    /// The reason as written (`skeleton::chain_reason`).
    pub cite: String,
    /// Where `cite` starts in the row's text.
    pub cite_at: usize,
    /// For a row after the first, its reason read as a requires line is:
    /// the change the row makes, a formula made from the two rows' trees
    /// (`Written::changed`), as its fact.
    pub reason: Option<Requires>,
    pub line: usize,
}

/// The rows a `substitute` step writes, cut as a chain's lines are, its
/// reason where `skeleton::chain_reason` finds it; None for a step with
/// none. The first row cites the line it writes out, and each row after it
/// gives a reason of its own.
pub fn substitute_rows(
    just: &Justification,
    path: &str,
) -> Option<Checked<Vec<SubstituteRow>>> {
    if just.rows.is_empty() || !just.head.is(Method::Substitute) {
        return None;
    }
    let mut out: Vec<SubstituteRow> = Vec::new();
    for (text, no) in &just.rows {
        let whole = str::trim(text);
        let Some(cite) = skeleton::chain_reason(whole) else {
            return Some(Err(Problem::new(
                path,
                *no,
                "a row gives no reason; the first ends on the line it writes out, and each after it on its own reason",
            )));
        };
        let formula =
            Written::new(str::trim(&whole[..whole.len() - cite.len()]), path, *no);
        let reason = match out.last() {
            None if skeleton::is_ref(cite) => None,
            None => {
                return Some(Err(Problem::new(
                    path,
                    *no,
                    "the first row writes out the line the step starts from, and cites it",
                )));
            }
            Some(_) if skeleton::is_ref(cite) => {
                let written = if skeleton::is_label(cite) {
                    format!("substitute {cite}")
                } else {
                    format!("substitute line {cite}")
                };
                return Some(Err(Problem::new(
                    path,
                    *no,
                    format!("a row after the first gives its own reason; one that uses {cite}'s equation is `{written}`"),
                )));
            }
            Some(above) => {
                let by = cut_reason(cite, path, *no).map(|slots| {
                    Justification::of(slots, *no, &just.names)
                        .shifted(skeleton::offset(text, cite))
                });
                Some(Requires {
                    fact: Written::changed(
                        above.formula.clone(),
                        formula.clone(),
                        path,
                        *no,
                    ),
                    how: cite.to_string(),
                    line: *no,
                    by,
                })
            }
        };
        out.push(SubstituteRow {
            formula,
            cite: cite.to_string(),
            cite_at: skeleton::offset(text, cite),
            reason,
            line: *no,
        });
    }
    Some(Ok(out))
}

/// A step being read, whose justification may not have arrived yet.
pub(super) struct DraftStep {
    pub(super) step: Step,
    pub(super) has_just: bool,
}

pub(super) struct DraftTheorem {
    pub(super) thm: Theorem,
    pub(super) steps: Vec<DraftStep>,
}

pub(super) const THEOREM_FIELDS: [&str; 1] = ["note"];

pub(super) fn label_at_end(text: &str) -> Option<String> {
    skeleton::label_at_end(text).map(String::from)
}

/// A requires line read as the step it would be: its fact claimed, its
/// reason the justification, at its own line, under the step it sits in and
/// with no requires lines of its own. A reason that is a method or an item
/// is proved this way, so a requires line and a step are one thing to the
/// elaborator (`ELABORATION.md`, R2).
pub fn requires_as_step(step: &Step, req: &Requires) -> Checked<Step> {
    Ok(reason_as_step(step, req, req.by()?))
}

/// `requires_as_step`, with the reason `by` the line was cut into.
pub fn reason_as_step(step: &Step, req: &Requires, by: &Justification) -> Step {
    Step {
        claim: req.fact.clone(),
        just: by.clone(),
        requires: Vec::new(),
        parts: Vec::new(),
        openers: Vec::new(),
        line: req.line,
        note: None,
        part_notes: IndexMap::new(),
        by_lines: Vec::new(),
        impossible: false,
        ..step.clone()
    }
}

/// The step with `, which is impossible` taken off the end of its claim and
/// said by `impossible` instead.
pub(super) fn impossible(mut step: Step) -> Step {
    let claim = &step.claim;
    if let Some(said) = skeleton::which_is_impossible(claim.text()) {
        step.claim = Written::new(said, claim.path(), claim.line());
        step.impossible = true;
    }
    step
}

/// What to say of a line that opens as a step does with a number that is
/// not one: None for any other line.
pub(super) fn misnumbered(text: &str) -> Option<String> {
    let number = skeleton::misnumbered(text)?;
    Some(format!(
        "`{number}.` is no step number: a step is numbered by whole numbers joined by dots, as 1.6 or 1.6.2"
    ))
}

/// What a step holds until its justification line is read.
pub(super) fn placeholder_justification() -> Justification {
    Justification::of(Slots::new(Head::Define, ""), 0, &Arc::default())
}

/// A line opening a theorem: `theorem <name>`, or `mundane theorem <name>`
/// for a fact of the standard library a proof takes for granted.
pub(super) struct TheoremHeader<'t> {
    pub(super) mundane: bool,
    /// The rest of the line, the name before it is trimmed and checked.
    pub(super) name: &'t str,
}

/// The header a line opens a theorem with; None for any other line.
pub(super) fn theorem_header(t: &str) -> Option<TheoremHeader<'_>> {
    if let Some(name) = t.strip_prefix("mundane theorem ") {
        return Some(TheoremHeader {
            mundane: true,
            name,
        });
    }
    t.strip_prefix("theorem ").map(|name| TheoremHeader {
        mundane: false,
        name,
    })
}
