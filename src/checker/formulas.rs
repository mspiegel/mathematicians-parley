//! What the formulas on the page say: that each reads, that their sorts
//! fit, and that the methods which relate formulas are given the shapes
//! they need.

use std::collections::BTreeSet;

use indexmap::IndexMap;

use super::library::{Known, SaidFrom, Stated};
use super::record::{
    Antisymmetric, Chain, ChainLink, CheckedTheorem, Contradicted, FirstAt, Negating,
    OrderFact, OrderPart, OrderRestated, OrderStep, Supposed, Supposition, Weakened,
};
use super::structure::{defined_below, introduced, letters_in_scope};
use super::Report;
use crate::citing::{
    claimed_member, implied_facts, link_unsaid, not_numbers, said_once, said_otherwise,
    Library, Parts,
};
use crate::corpus::proof::{
    chain, rows, substitute_rows, visible, ChainLine, RowReason,
};
use crate::corpus::{
    define_parts, DefineParts, FileScope, Head, Intro, Item, Justification, Method,
    Opener, Record, RecordKind, Recursion, Requires, RuleText, Source, Step, Theorem,
    Value, Values,
};
use crate::formula::notation_id::{NotationId, Spelling};
use crate::formula::page::{
    conjoined, disjoined, made, made_by_name, numeral, related, Sentence, Written,
};
use crate::formula::symbol::Symbol;
use crate::formula::{walk, Node, Sort, Sorts};
use crate::matching::{
    alike_top, free_names, identities_dropped, standard, substitute_apart_by, Binding,
    FxIndexSet, Meeting,
};
use crate::methods::field::{decide_closed, Verdict};
use crate::methods::membership as methods_membership;
use crate::methods::terms::{term_of_node, term_of_node_reading, Targets};
use crate::methods::{algebra, inequalities, linear, reals};
use crate::mm::kernel::{FloatLabels, Term};
use crate::notations::{
    APPLICATION, APPLICATION_TO_TWO, AT_LEAST, AT_MOST, BICONDITIONAL, BY_CASES,
    CONDITIONAL, CONJUNCTION, EQUALITY, EQUALS, EQUAL_CHAIN, FOR_ALL, FOR_ALL_SETS,
    GREATER, IMPLICATION, INTEGER_RANGE, LESS, LOGICAL_NOT, MEMBERSHIP, NUMBER_SYSTEMS,
    NUMERAL, ORDER, PLUS, PRODUCT, PRODUCT_OVER, REAL_POWER, SINGLETON, SUM, TIMES,
    UNION,
};
use crate::outcome::{Built, Checked, Declined, Problem};
use crate::rules::System;
use crate::sorts::infer::{self, Reader, Store};
use crate::sorts::introduction::{Form, Introduction};
use crate::sorts::{define_sorts, types_a_function, unlabel, written_tokens, Env};
use crate::targets::split_entries;

/// The sorts an item's statement relates fit, as its reading found.
pub fn check_item_clashes(
    report: &mut Report,
    statements: &IndexMap<String, Reader>,
    names: &IndexMap<String, Item>,
) {
    for (name, reader) in statements {
        let path = names.get(name).map_or("", |i| i.path());
        for c in &reader.clashes {
            report.say(path, c.line, format!("{name}: {}: {}", c.what, c.why));
        }
    }
}

/// A proof's names, read off how it uses them: the theorem's one reading.
///
/// `READERS.md`: a set's sort says what it holds, nobody writes it, and a
/// set of any sort stays of any sort. Each line is read in the order it is
/// written — a `let` shadows an earlier name, since blocks reuse letters —
/// and each citation's written `v := t` is fitted to a fresh copy of what
/// the cited statement says v is. What the reading settles is the theorem's
/// sorts (`sorts::settled`), and what does not fit is `check_clashes`'s to
/// report.
pub fn read_with_citations(
    thm: &Theorem,
    env: Env,
    statements: &IndexMap<String, Reader>,
    store: &mut Store,
) -> Reader {
    let mut cite = |reader: &mut Reader,
                    store: &mut Store,
                    step: &Step,
                    req: Option<&Requires>| {
        cited_sorts(reader, store, step, req, env, statements);
    };
    infer::read_theorem(thm, env, store, Some(&mut cite))
}

/// What a proof's names are fits, as its reading found (`read_with_citations`).
///
/// What does not fit is reported where it is: two sorts joined where one is
/// wanted, an element of a set of numbers said to be a set, and a set
/// declared of any sort that a citation would narrow.
pub fn check_clashes(report: &mut Report, thm: &Theorem, clashes: &[infer::Clash]) {
    for c in clashes {
        report.say(&thm.path, c.line, format!("{}: {}", c.what, c.why));
    }
}

/// Each written `v := t` of a citation, fitted to the cited statement: the
/// step's own, or the requires line `req`'s, read once the line's fact is.
/// Each citation takes its own copy of what the statement says v is.
///
/// A citation checks what the proof's names are and does not say it. A name
/// whose sort only fitting a citation settles is reported: the sort decides
/// how a formula reads, the elaborator reads a proof's sorts from its own
/// lines without its citations, and a proof read only with the statements it
/// cites is one whose formulas change when a cited statement does, as the
/// rule for `obtain` in `GRAMMAR.md` says.
fn cited_sorts(
    reader: &mut Reader,
    store: &mut Store,
    step: &Step,
    req: Option<&Requires>,
    env: Env,
    statements: &IndexMap<String, Reader>,
) {
    let mut cites: Vec<(String, &Values)> = Vec::new();
    match req {
        None => {
            if let Some(item) = step.just.cited_item() {
                cites.push((step.just.item(&item), &step.just.values));
            }
        }
        Some(req) => {
            if let Some((cited, _)) = req.cited_item() {
                cites.push((step.just.item(&cited), req.values()));
            }
        }
    }
    // A claim "for all m ∈ X, P" may be cited as P would be, at a member m
    // of X (`SYNTAX.md`, a step said of every member), and what m is then is
    // what X holds: the claim's own "for all" says so.
    let claimed = match req {
        None => step.claim_text(),
        Some(req) => str::trim(&unlabel(req.fact.text())).to_string(),
    };
    let line = req.map_or(step.line, |r| r.line);
    let member = reader.member_sorts(&claimed, line, env, store);
    for (name, values) in cites {
        let Some(stated) = statements.get(&name) else {
            continue;
        };
        // Every value is read with the sorts as they stand before fitting
        // any of them settles one, and as its letter's place wants it. A
        // value that does not read is the elaborator's to report.
        let letters = stated.sorts(store);
        let Ok(values) =
            values.read_wanted(env.g, &reader.sorts(store), Some(&letters))
        else {
            continue;
        };
        let mut seen = IndexMap::new();
        for Value {
            name: v,
            value: tree,
            shown: value,
        } in values
        {
            let Some(wanted) = stated.env.get(&v) else {
                continue;
            };
            let got = reader.sort_of(&tree, step.line.into(), &member, store);
            let mut names: Vec<String> = Vec::new();
            for n in tree.walk() {
                if n.is_name()
                    && reader.env.contains_key(n.text.as_str())
                    && !member.contains_key(n.text.as_str())
                    && !names.iter().any(|m| *m == n.text)
                {
                    names.push(n.text.to_string());
                }
            }
            let before: Vec<Option<Sort>> = names
                .iter()
                .map(|n| infer::sort(store, &reader.env[n]))
                .collect();
            let copied = store.copy(wanted, &mut seen);
            if let Declined(said) = store.unify(&got, &copied) {
                reader.clashes.push(infer::Clash {
                    line: step.line.into(),
                    what: format!("citing {name} with {v} := {value}"),
                    why: said.reason(),
                });
                continue;
            }
            for (n, was) in names.iter().zip(before) {
                let now = infer::sort(store, &reader.env[n]);
                if now != was {
                    let is =
                        now.map_or_else(|| "settled".to_string(), |s| s.describe());
                    reader.clashes.push(infer::Clash {
                        line: step.line.into(),
                        what: format!("citing {name} with {v} := {value}"),
                        why: format!(
                            "only the citation says {n} is {is}; say so where {n} is introduced"
                        ),
                    });
                }
            }
        }
    }
}

/// Every formula on the page parses, and parses one way.
///
/// A claim, an `assume` or `suppose` line, the fact of a `requires` line and
/// the theorem's statement are all formulas, read from the declared
/// notations. One that does not parse is a defect in the text or a notation
/// nobody declared. One that parses two ways is worse, because the reader
/// and the kernel could take it differently and nothing downstream would
/// notice, so the parser refuses it rather than choosing.
///
/// This is the pass that says so, and it reaches every one of them. That is
/// what lets the passes which merely gather — sorts, the names a `proof`
/// block binds, the trees an item states — skip a formula they cannot read and
/// carry on: it has been reported here, once, with the line it is on.
pub fn check_formulas(report: &mut Report, thm: &Theorem, env: Env, known: &Known) {
    let own = introduced(thm, known);
    for part in claim_parts(thm) {
        // Each of these places says something: a `.` alone is no sentence.
        if part.written.sentences().is_empty() {
            report.say(&thm.path, part.line, format!("{} says nothing", part.what));
            continue;
        }
        for sentence in part.written.sentences() {
            match known.parse(&sentence) {
                Ok(node) => say_chain_inside(report, thm, &part, &node, known),
                Err(p) => say_unread(report, thm, env, &own, &part, p),
            }
        }
    }
    for part in one_formula_parts(thm) {
        match part.written.formula().and_then(|s| known.parse(&s)) {
            Ok(node) => say_chain_inside(report, thm, &part, &node, known),
            Err(p) => say_unread(report, thm, env, &own, &part, p),
        }
    }
    // A define's rule is a formula too, read with its argument's sort; one
    // that does not read would otherwise be passed over by everything that
    // gathers what the defines say, and surface only as citations that fail.
    for d in &thm.defines {
        let Built(DefineParts::One(said)) = define_parts(&d.text) else {
            continue;
        };
        let local =
            match define_sorts(&said, &known.sorts, known.env.g, &d.path, d.line) {
                Ok(local) => local,
                Err(p) => {
                    report.say(
                        &thm.path,
                        d.line,
                        format!("define {}: {}", d.label, p.message),
                    );
                    continue;
                }
            };
        let body = d.rule(&said.body);
        if let Err(p) = body.formula().and_then(|s| known.keep_read(&s, &local)) {
            report.say(
                &thm.path,
                d.line,
                format!("define {}: {}", d.label, p.message),
            );
        }
        // Each argument's name, with the sort its domain gives it, as the
        // build writes the map sending it to the rule.
        for p in &said.params {
            let name = Written::new(&p.name, &thm.path, d.line);
            if let Err(p) = name.formula().and_then(|s| known.keep_read(&s, &local)) {
                report.say(
                    &thm.path,
                    d.line,
                    format!("define {}: {}", d.label, p.message),
                );
            }
        }
    }
}

/// A part of a line that is formula text, and what a message calls it.
pub(super) struct FormulaPart {
    pub(super) line: usize,
    pub(super) what: String,
    pub(super) written: Written,
}

impl FormulaPart {
    pub(super) fn new(line: usize, what: String, written: &Written) -> FormulaPart {
        FormulaPart {
            line,
            what,
            written: written.clone(),
        }
    }
}

/// A part that does not read, reported, unless a name the file defines only
/// further down is why: `check_defined_below` says so, since above its
/// define it names nothing, and `U(0)` then reads several ways because
/// nothing says U is a function.
fn say_chain_inside(
    report: &mut Report,
    thm: &Theorem,
    part: &FormulaPart,
    node: &Node,
    known: &Known,
) {
    // A chain of equations is a whole sentence (`SYNTAX.md`): one standing
    // inside another formula is said once, at the outermost.
    let inside = node
        .children
        .iter()
        .flat_map(|c| c.walk())
        .find(|n| n.notation() == EQUAL_CHAIN);
    if let Some(chain) = inside {
        report.say(
            &thm.path,
            part.line,
            format!(
                "{}: the chain of equations {} stands inside another formula, and a chain is a whole sentence",
                part.what,
                known.print(&chain)
            ),
        );
    }
}

fn say_unread(
    report: &mut Report,
    thm: &Theorem,
    env: Env,
    own: &BTreeSet<String>,
    part: &FormulaPart,
    p: Problem,
) {
    let lexed = written_tokens(std::slice::from_ref(&part.written), env.g);
    if defined_below(thm, &lexed, own, env.scopes).is_empty() {
        let said = format!("{}: {}", part.what, p.message);
        report.say(&thm.path, part.line, said);
    }
}

/// Every part of a theorem that is a claim, of one sentence or several:
/// each step's claim, each `assume` and `suppose` line, and the statement. An induction hypothesis writes no formula: it assumes
/// what its induction's claim says.
pub(super) fn claim_parts(thm: &Theorem) -> Vec<FormulaPart> {
    let mut out = Vec::new();
    // The theorem proved `by` a method claims the statement, which is read
    // once, below.
    for s in thm.steps.iter().filter(|s| !s.proves_theorem()) {
        let what = format!("step {}", s.number);
        out.push(FormulaPart::new(s.line, what, &s.claim));
    }
    let assumed = |kind| matches!(kind, Intro::Assume | Intro::Suppose);
    for h in thm.hypotheses.iter().filter(|h| assumed(h.kind)) {
        let what = format!("the `{}` line", h.kind);
        out.push(FormulaPart::new(h.line, what, &h.body(&thm.path)));
    }
    let opened = thm.steps.iter().flat_map(|s| &s.openers);
    for o in opened.filter(|o| assumed(o.kind) && !o.is_hypothesis) {
        let what = format!("the `{}` line", o.kind);
        out.push(FormulaPart::new(o.line, what, &o.body(&thm.path)));
    }
    let stated = Written::new(&thm.conclusion, &thm.path, thm.line);
    let what = format!("the statement of {}", thm.name);
    out.push(FormulaPart::new(thm.line, what, &stated));
    out
}

/// Every part of a theorem that is one formula: a `let` line's parts, a
/// requires line's fact (one per hypothesis of the item, `SYNTAX.md`), each
/// value `x := t`, a substitute's equation, an induction's start, a
/// calculation's terms and moduli, an `inequalities` step's rows and the
/// terms they add or multiply by, and a define's parameter domains. A `let` line of none of the forms is
/// `check_introductions`'s to report, and a chain or rows that do not cut
/// `check_structure`'s.
pub(super) fn one_formula_parts(thm: &Theorem) -> Vec<FormulaPart> {
    let mut out = Vec::new();
    let mut add =
        |line, what, written: &Written| out.push(FormulaPart::new(line, what, written));
    let lets = thm
        .hypotheses
        .iter()
        .filter(|h| h.kind == Intro::Let)
        .map(|h| h.body(&thm.path));
    let opened = thm
        .steps
        .iter()
        .flat_map(|s| &s.openers)
        .filter(|o| o.kind == Intro::Let)
        .map(|o| o.body(&thm.path));
    for body in lets.chain(opened) {
        let line = body.line();
        let introduced = Introduction::read(body);
        if let Form::Other = introduced.form {
            continue;
        }
        for part in introduced.parts() {
            add(line, "the `let` line".to_string(), &part);
        }
    }
    for s in &thm.steps {
        for v in s.just.values.written() {
            add(s.just.line, format!("a value step {} gives", s.number), v);
        }
        for r in &s.requires {
            let what = format!("the requires line of {}", s.called());
            add(r.line, what, &r.fact);
            for v in r.values().written() {
                let what = format!("a value the requires line of {} gives", s.called());
                add(r.line, what, v);
            }
            if let Ok(Some(e)) = r.by().map(|by| by.equation.as_ref()) {
                let what =
                    format!("the equation the requires line of {} gives", s.called());
                add(r.line, what, e);
            }
        }
        if let Some(e) = &s.just.equation {
            add(s.just.line, format!("the equation of step {}", s.number), e);
        }
        if let Some(start) = &s.just.start {
            let start = Written::new(start.trim(), &thm.path, s.just.line);
            let what = format!("the start of step {}", s.number);
            add(s.just.line, what, &start);
        }
        if let Some(Ok(chain)) = chain(&s.just, &thm.path) {
            let what = || format!("the calculation of step {}", s.number);
            add(chain.start.line(), what(), &chain.start);
            for l in &chain.lines {
                add(l.line, what(), &l.term);
                if let Some(m) = &l.modulus {
                    add(l.line, what(), m);
                }
                // A line's own reason is read as a requires line's is: the
                // link it proves, and each value and equation it gives.
                let Some(req) = &l.reason else {
                    continue;
                };
                add(l.line, what(), &req.fact);
                for v in req.values().written() {
                    add(
                        l.line,
                        format!("a value a line of step {} gives", s.number),
                        v,
                    );
                }
                if let Ok(Some(e)) = req.by().map(|by| by.equation.as_ref()) {
                    add(
                        l.line,
                        format!("the equation a line of step {} gives", s.number),
                        e,
                    );
                }
            }
        }
        if let Some(Ok(rows)) = rows(&s.just, &thm.path) {
            for row in &rows {
                let what = format!("a row of step {}", s.number);
                add(row.line, what.clone(), &row.formula);
                if let RowReason::Adding(t) | RowReason::Multiplying(t) = &row.reason {
                    add(row.line, what, t);
                }
            }
        }
        // A substitute's rows, and each one's own reason as a chain line's
        // is read: the change it makes, and each value and equation it gives.
        if let Some(Ok(rows)) = substitute_rows(&s.just, &thm.path) {
            for row in &rows {
                let what = || format!("a row of step {}", s.number);
                add(row.line, what(), &row.formula);
                let Some(req) = &row.reason else {
                    continue;
                };
                add(row.line, what(), &req.fact);
                for v in req.values().written() {
                    add(
                        row.line,
                        format!("a value a row of step {} gives", s.number),
                        v,
                    );
                }
                if let Ok(Some(e)) = req.by().map(|by| by.equation.as_ref()) {
                    add(
                        row.line,
                        format!("the equation a row of step {} gives", s.number),
                        e,
                    );
                }
            }
        }
    }
    for d in &thm.defines {
        if let Built(DefineParts::One(said)) = define_parts(&d.text) {
            for p in &said.params {
                add(d.line, format!("define {}", d.label), &d.domain(p));
            }
        }
    }
    out
}

/// A word a definition defines, and the methods its record's `decided` field
/// names (`DATABASE.md`).
pub struct DefinedWord {
    pub record: String,
    pub methods: Vec<String>,
}

/// Every definition's word, keyed by the notation and the literal a parse
/// of its `then` line's left side gives it: a relation `arithmetic` does not
/// decide of its own nature, as an equation or a membership it does. Words
/// are what a `decided` field is about, so it may name only a method that
/// decides words, and one naming another is reported.
pub fn defined_words(
    report: &mut Report,
    records: &[Record],
    env: Env,
    sorts: &IndexMap<usize, Sorts>,
) -> IndexMap<Spelling, DefinedWord> {
    let mut out = IndexMap::new();
    for (i, r) in records.iter().enumerate() {
        if r.kind != RecordKind::Definition {
            continue;
        }
        let methods: Vec<String> = r
            .field("decided")
            .map(|v| {
                split_entries(v)
                    .into_iter()
                    .map(|m| str::trim(m).to_string())
                    .collect()
            })
            .unwrap_or_default();
        // A function's record names the method that works it out, and only
        // `real arithmetic` works out a function (`DATABASE.md`, decided).
        if r.is_function() {
            for m in methods.iter().filter(|m| *m != "real arithmetic") {
                report.say(
                    &r.path,
                    r.lines.get("decided").copied().unwrap_or(r.line),
                    format!(
                        "{} says {m} decides it, and {m} works out no function; the method that does is real arithmetic",
                        r.name
                    ),
                );
            }
            continue;
        }
        for m in &methods {
            if !DECIDING.contains(&m.as_str()) {
                report.say(
                    &r.path,
                    r.lines.get("decided").copied().unwrap_or(r.line),
                    format!(
                        "{} says {m} decides it, and {m} decides no word; the methods that do are {}",
                        r.name,
                        DECIDING.join(" and ")
                    ),
                );
            }
        }
        let (Some((text, line)), Some(record_sorts)) =
            (r.conclusions.first(), sorts.get(&i))
        else {
            continue;
        };
        let stated = Written::new(text, &r.path, *line).formula();
        let Ok(node) = stated.and_then(|s| s.read(env.g, record_sorts)) else {
            continue;
        };
        if node.notation() != BICONDITIONAL || node.children.len() != 2 {
            continue;
        }
        let left = &node.children[0];
        if NATIVE.contains(&left.notation()) {
            continue;
        }
        out.insert(
            left.spelling(),
            DefinedWord {
                record: r.name.clone(),
                methods,
            },
        );
    }
    out
}

/// The methods a `decided` field may name: those that decide a word of
/// numerals (`METHODS.md`).
const DECIDING: [&str; 2] = ["arithmetic", "inspection"];

/// The notations of the relations `arithmetic` decides of its own nature,
/// which a definition may unfold without making them words.
const NATIVE: [NotationId; 3] = [MEMBERSHIP, EQUALITY, ORDER];

/// Every operation a notation declares, one building a number from numbers,
/// by its notation's name, and whether `arithmetic` works it out: one of
/// its own nature, or one whose record names it in a `decided` field.
pub fn operations(records: &[Record]) -> IndexMap<NotationId, bool> {
    operations_by(records, crate::methods::field::worked_out, false)
}

/// `operations`, by whether `real arithmetic` works each out: one
/// `arithmetic` does, or one whose record names `real arithmetic`; and the
/// constants with them, π and e worked out, i not.
pub fn real_operations(records: &[Record]) -> IndexMap<NotationId, bool> {
    operations_by(records, crate::methods::surds::worked_out, true)
}

/// Each library function, by its name, and whether its record says
/// `real arithmetic` works it out (`DATABASE.md`, decided): ln and exp do,
/// cos and gcd do not.
pub fn real_functions(records: &[Record]) -> IndexMap<String, bool> {
    records
        .iter()
        .filter(|r| r.is_function())
        .map(|r| {
            let decided = crate::methods::field::decides(r, "real arithmetic");
            (r.name.clone(), decided)
        })
        .collect()
}

fn operations_by(
    records: &[Record],
    worked_out: fn(&Record) -> bool,
    constants: bool,
) -> IndexMap<NotationId, bool> {
    records
        .iter()
        .filter(|r| r.kind == RecordKind::Notation)
        .filter(|r| {
            r.field_or_empty("sort").trim_end().ends_with("→ number")
                && (constants || r.field_or_empty("pattern").contains('_'))
        })
        .map(|r| (NotationId::of(&r.name), worked_out(r)))
        .collect()
}

/// A method decides a word only where the word's record names it
/// (`DATABASE.md`, `decided`). `arithmetic` is asked of a step it justifies,
/// a requires line it is the reason for, and a claim said to be impossible,
/// which is a closed fact it shows false; a denial is asked of the word it
/// denies. `inspection` is asked of each word its claim says, where no line
/// the step cites says that word, since a word a cited line says of each
/// element is read off the line and not decided. The elaborator sees
/// "divides" and "is even" as one relation, and "is odd" as a membership of
/// ℤ joined to the denial of it, so the word is told apart here.
pub fn check_decided_words(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    words: &IndexMap<Spelling, DefinedWord>,
    operations: &IndexMap<NotationId, bool>,
    targets: &Targets,
) {
    for step in &thm.steps {
        if step.just.head.is(Method::Inspection) {
            let scope = known.scope(step);
            let cited: BTreeSet<Spelling> = step
                .just
                .refs
                .iter()
                .filter_map(|r| scope.get(r))
                .flat_map(|stated| known.supplied(stated, &known.citing_step(step)))
                .flat_map(|n| n.walk().iter().map(Node::spelling).collect::<Vec<_>>())
                .collect();
            if let Some(claim) = known.whole(step, &step.claim) {
                for node in claim.walk() {
                    let Some(word) = words.get(&node.spelling()) else {
                        continue;
                    };
                    if cited.contains(&node.spelling())
                        || word.methods.iter().any(|m| m == "inspection")
                    {
                        continue;
                    }
                    report.say(
                        &thm.path,
                        step.line,
                        format!(
                            "step {} asks inspection to decide a word {} defines, which no line it cites says, and inspection decides a word only where its record says so in a `decided` field",
                            step.number, word.record
                        ),
                    );
                }
            }
        }
        let mut asked: Vec<(usize, &Written)> = Vec::new();
        // A claim said to be impossible is `arithmetic`'s where it holds
        // nothing `real arithmetic` works out beyond it.
        let impossible =
            step.impossible && !beyond_arithmetic(&step.claim, known, targets);
        if step.just.head.is(Method::Arithmetic) || impossible {
            asked.push((step.line, &step.claim));
        }
        for r in &step.requires {
            if r.is(Method::Arithmetic) {
                asked.push((r.line, &r.fact));
            }
        }
        // A link naming `arithmetic` works out the pieces it changes, which
        // are asked as a step's claim is: (1 + 1)! = 2 is no fact of its.
        for link in chain_links(&step.just, &thm.path) {
            if link.line.cite != "arithmetic" {
                continue;
            }
            let Some(claim) = link.claim(known) else {
                continue;
            };
            let [one, other] = claim.children.as_slice() else {
                continue;
            };
            let mut worked: BTreeSet<String> = BTreeSet::new();
            link_undecided(one, other, known, operations, &mut worked);
            for operation in worked {
                report.say(
                    &thm.path,
                    link.line.line,
                    format!(
                        "a link of step {} names arithmetic for {}, which works out {operation}, and arithmetic works out an operation beyond its own only where the notation's record says so in a `decided` field",
                        step.number,
                        link.line.quoted(&link.from),
                    ),
                );
            }
        }
        let sentences = asked.into_iter().flat_map(|(line, written)| {
            written.sentences().into_iter().map(move |s| (line, s))
        });
        for (line, sentence) in sentences {
            let text = sentence.text();
            let Some(mut node) = known.read(step, &sentence) else {
                continue;
            };
            // Each operation is named once for the sentence, however often
            // the sentence writes it.
            let mut named: BTreeSet<String> = BTreeSet::new();
            for part in node.walk() {
                if operations.get(&part.notation()) == Some(&false)
                    && named.insert(part.notation_name().to_string())
                {
                    // A power whose exponent is not whole is no operation a
                    // record could mark: its value is in general irrational
                    // (`METHODS.md`).
                    let why = if part.notation() == REAL_POWER {
                        format!(
                            "{text}: {} has an exponent that is not whole, and arithmetic takes a power only with a whole one",
                            part.written(text).unwrap_or_else(|| "a power".to_string())
                        )
                    } else {
                        format!(
                            "{text} works out {}, and arithmetic works out an operation beyond its own only where the notation's record says so in a `decided` field",
                            part.notation_name()
                        )
                    };
                    report.say(&thm.path, line, why);
                }
            }
            while node.notation() == LOGICAL_NOT && node.children.len() == 1 {
                node = node.children[0].clone();
            }
            let Some(word) = words.get(&node.spelling()) else {
                continue;
            };
            if !word.methods.iter().any(|m| m == "arithmetic") {
                report.say(
                    &thm.path,
                    line,
                    format!(
                        "{text} is a word {} defines, and arithmetic decides a word only where its record says so in a `decided` field",
                        word.record
                    ),
                );
            }
        }
    }
}

/// `real arithmetic` works out an operation beyond `arithmetic`'s only
/// where its notation's record names it, as `square-root` does, and decides
/// no word (`DATABASE.md`, `decided`). Asked of a step it justifies and a
/// requires line it is the reason for.
pub fn check_real_decided_words(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    words: &IndexMap<Spelling, DefinedWord>,
    operations: &IndexMap<NotationId, bool>,
    functions: &IndexMap<String, bool>,
    targets: &Targets,
) {
    for step in &thm.steps {
        let mut asked: Vec<(usize, &Written)> = Vec::new();
        // A claim said to be impossible is `real arithmetic`'s where it
        // holds what it works out beyond `arithmetic`.
        let impossible =
            step.impossible && beyond_arithmetic(&step.claim, known, targets);
        if step.just.head.is(Method::RealArithmetic) || impossible {
            asked.push((step.line, &step.claim));
        }
        for r in &step.requires {
            if r.is(Method::RealArithmetic) {
                asked.push((r.line, &r.fact));
            }
        }
        if let (Some(Source::RealArithmetic), Some(equation)) =
            (&step.just.source, &step.just.equation)
        {
            asked.push((step.just.line, equation));
        }
        let mut read: Vec<(usize, String, Node)> = Vec::new();
        for (line, written) in asked {
            for sentence in written.sentences() {
                if let Some(node) = known.read(step, &sentence) {
                    read.push((line, sentence.text().to_string(), node));
                }
            }
        }
        for link in chain_links(&step.just, &thm.path) {
            if link.line.cite != "real arithmetic" {
                continue;
            }
            let Some(claim) = link.claim(known) else {
                continue;
            };
            let quoted = link.line.quoted(&link.from);
            // A link whose terms have letters works out the closed pieces it
            // changes, and nothing it leaves as it was (`real_pieces`).
            let closed = claim.names().iter().all(|name| library_named(name, known));
            let mut pieces = Vec::new();
            let split = !closed
                && match (claim.notation(), claim.children.as_slice()) {
                    (EQUALITY, [one, other]) => {
                        real_pieces(one, other, known, &mut pieces)
                    }
                    _ => false,
                };
            if split {
                for Piece { was, now } in pieces {
                    let piece = made(known.env.g, EQUALS, vec![was, now]);
                    read.push((link.line.line, quoted.clone(), piece));
                }
            } else {
                read.push((link.line.line, quoted, claim));
            }
        }
        for (line, text, mut node) in read {
            let mut named: BTreeSet<String> = BTreeSet::new();
            for part in node.walk() {
                if operations.get(&part.notation()) == Some(&false)
                    && named.insert(part.notation_name().to_string())
                {
                    report.say(
                        &thm.path,
                        line,
                        format!(
                            "{text} works out {}, and real arithmetic works out an operation beyond arithmetic's only where the notation's record says so in a `decided` field",
                            part.notation_name()
                        ),
                    );
                }
                let applied =
                    matches!(part.notation(), APPLICATION | APPLICATION_TO_TWO);
                let Some(head) =
                    part.children.first().filter(|h| applied && h.is_name())
                else {
                    continue;
                };
                let name = head.text.to_string();
                if library_named(&name, known)
                    && functions.get(&name) == Some(&false)
                    && named.insert(name.clone())
                {
                    report.say(
                        &thm.path,
                        line,
                        format!(
                            "{text} works out {name}, and real arithmetic works out a function only where its record says so in a `decided` field"
                        ),
                    );
                }
            }
            while node.notation() == LOGICAL_NOT && node.children.len() == 1 {
                node = node.children[0].clone();
            }
            if let Some(word) = words.get(&node.spelling()) {
                report.say(
                    &thm.path,
                    line,
                    format!(
                        "{text} is a word {} defines, and real arithmetic decides no word",
                        word.record
                    ),
                );
            }
        }
    }
}

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
fn header_letters_introduced(
    report: &mut Report,
    thm: &Theorem,
    env: Env,
    known: &Known,
) {
    let binders = env.g.binders();
    let mut scope = super::structure::hypotheses_introduce(thm, known);
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
fn negates(
    a: Option<&Node>,
    b: Option<&Node>,
    wrappers: &FxIndexSet<NotationId>,
    known: &Known,
) -> bool {
    negates_how(a, b, wrappers, known).is_some()
}

/// `negates`, with how what `a` denies meets `b` (`Known::alike_how`).
fn negates_how(
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

fn wrappers(env: Env) -> FxIndexSet<NotationId> {
    env.g
        .notations
        .iter()
        .filter_map(|n| n.folds.as_deref().map(NotationId::of))
        .collect()
}

/// A contradiction's supposition and what it is to show, as read: the
/// block's claim, or what a part proved by contradiction owes. Either is
/// None where it does not read, which is reported where it is read.
struct SupposedReading {
    /// The line the `suppose` is on.
    line: usize,
    supposed: Option<Node>,
    claimed: Option<Node>,
    /// The claim as the page writes it (`Reading::Written`), where it is
    /// read so.
    written: Option<Node>,
}

impl SupposedReading {
    fn reads(&self) -> bool {
        self.supposed.is_some() && self.claimed.is_some()
    }

    /// Which of the two `METHODS.md` shapes the supposition has; None where
    /// it has neither, or either side does not read.
    fn kind(
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
fn own_supposition(
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
fn part_supposition(
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
            let placed = super::citations::placed(other, s, &says, own)?;
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
fn check_part_contradictions(
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
fn ends_block(thm: &Theorem, at: usize) -> bool {
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
fn opposes(
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
fn reads_contradicted(
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

/// What one part of a block owes: the part, as its steps are numbered, the
/// sentences its last step claims, and how a message names the part.
pub(super) struct Owed {
    pub(super) part: Option<usize>,
    /// What the part owes, as its owner's method gives it.
    pub(super) claim: Vec<Node>,
    /// What the part's last step ends on: the claim, or what the part's `by`
    /// line makes of it (`after_by`).
    pub(super) ends: Ends,
    called: String,
}

/// What the last step of a part ends on.
pub(super) enum Ends {
    /// These sentences.
    Claim(Vec<Node>),
    /// A contradiction: the part is proved `by contradiction`, and
    /// `check_contradiction` sees its last step.
    Contradiction,
}

impl Owed {
    /// A part owing `claim`, whose last step ends on it.
    fn new(part: Option<usize>, claim: Vec<Node>, called: String) -> Owed {
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
pub(super) fn last_of_part<'a>(
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
pub(super) fn block_owes(owner: &Step, known: &Known) -> Checked<Vec<Owed>> {
    block_owes_read(owner, known, Reading::Compared)
}

/// How `block_owes_read` reads a block's claim.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Reading {
    /// As the checks compare it: with the outside defines written out, in
    /// the standard order (`Known::read_citing`).
    Compared,
    /// As the page writes it (`Known::read_as_written`): what a backend's
    /// goal is, the claim it states with the block's lines taken off.
    Written,
}

/// `block_owes`, the claim read as `reading` says.
pub(super) fn block_owes_read(
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
struct Ending {
    said: Node,
    owed: Node,
    /// What the step ends, for a message: "the base", or the proof.
    called: String,
}

/// What `step` ends owing, each sentence it says beside the one it owes:
/// for each part of a block it is the last step of (`check_block_ends`),
/// and for the proof where it is the last step (`check_last_step`). Empty
/// for any other step, and where the two do not say as many sentences.
fn endings(thm: &Theorem, step: &Step, known: &Known) -> Vec<Ending> {
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
fn conjuncts_read(
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
fn paired(said: Vec<Node>, owed: Vec<Node>, called: &str, out: &mut Vec<Ending>) {
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
    called: String,
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
fn induction_owes(owner: &Step, claim: &Node, known: &Known) -> Vec<Owed> {
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
    let next = match super::structure::parts_of(&claim.children[1]) {
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
fn member_added(owner: &Step, known: &Known) -> Option<Node> {
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
    let said = super::structure::let_said(third, known.thm, known)?;
    said.children.first().cloned()
}

/// What a `proof` block owes: `claim` with a "for all" taken off for each
/// `let` line of `opens` and an "if" for each `assume`, in the order they
/// open the block (`SYNTAX.md`, proof). A claim without the layer an opener
/// takes off is the page's defect, and so is a name that does not read;
/// `called` names the block's owner, or the part proved `by proof`, in the
/// message.
fn peel(called: &str, opens: &[&Opener], claim: &Node, known: &Known) -> Checked<Node> {
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
fn after_by(owner: &Step, owed: Owed, known: &Known) -> Checked<Owed> {
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
fn conjuncts(node: &Node) -> Vec<Node> {
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
fn names_define(thm: &Theorem, label: &str) -> bool {
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
    pub shown: Vec<super::record::PlaceShown>,
    unshown: Vec<PlaceAsked>,
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
            let shown_once = |s: &super::record::PlaceShown| {
                s.system == a.system && known.alike(&s.term, &a.term)
            };
            if out.unshown.iter().any(once) || out.shown.iter().any(shown_once) {
                continue;
            }
            use super::record::{PlaceShown, ShownBy};
            use methods_membership::Held;
            match methods_membership::atom_held_by(&a.term, a.system, &given) {
                Some(Held::Said) => out.shown.push(PlaceShown {
                    term: a.term,
                    system: a.system,
                    by: ShownBy::Said,
                }),
                Some(Held::Beside(b)) => out.shown.push(PlaceShown {
                    by: ShownBy::Beside(super::record::Besides::of(&b)),
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
fn terms_defined_in_scope(step: &Step, known: &Known) -> Vec<String> {
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
struct PlaceAsked {
    term: Node,
    system: System,
}

/// Every term `claim` puts at a place `places` gives a number system,
/// with that system. A term holding a letter a binder in the claim binds
/// speaks of what no fact of the step can, and is left out, but for the
/// member of a step said of every member (`at_member`), whose facts put it
/// in its set.
fn places_asked(
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
    super::citations::letters_bound(body, ctx, &mut bound);
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
fn restates(step: &Step) -> bool {
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
fn changed_closed(link: &Link, known: &Known) -> bool {
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
fn arithmetic_unshown(
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
const ARITHMETIC_UNREAD: &str =
    "is not a fact about numerals alone, and arithmetic decides nothing else";

/// What a method working out closed facts, `arithmetic` or `real
/// arithmetic`, says of one.
enum Shown {
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
fn check_shown_by(
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
fn check_closed_by(
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
fn link_pieces_unworked(
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
fn link_undecided(
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
struct Piece {
    was: Node,
    now: Node,
}

/// The pieces of numerals alone where `one` and `other` differ, walking
/// both where they are built alike.
fn closed_pieces(one: &Node, other: &Node, known: &Known, out: &mut Vec<Piece>) {
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
fn cited_chain(thm: &Theorem, step: &Step, known: &Known) -> Option<Vec<String>> {
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
fn chain_order(
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
fn algebra_holds(
    report: &mut Report,
    thm: &Theorem,
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> bool {
    let Some(mut read) = at.read(known, targets, false) else {
        return false;
    };
    read.read_at_member(known);
    let labels = FloatLabels::new(IndexMap::new());
    // The cited lines fact by fact, so that a line saying several things,
    // in sentences or joined by "and", asks only of the ones combined. Each
    // is decided with its identity elements dropped, as the claim is
    // (`SYNTAX.md`, "An identity element goes without saying"): F(0 + 1) and
    // F(1) are one atom.
    let ctx = &known.ctx;
    let facts: Vec<Node> = read.lines.iter().flat_map(conjuncts).collect();
    let cited: Vec<Term> = facts
        .iter()
        .map(|n| term_of_node(&crate::matching::bare(n, ctx), targets))
        .collect();
    let claimed = term_of_node(&crate::matching::bare(&read.claimed, ctx), targets);
    // Sums are read as linear where some term of the step is linear in
    // something, as the build reads them (`field::says_something_linear`).
    let linear = std::iter::once(&claimed)
        .chain(&cited)
        .any(|t| crate::methods::field::says_something_linear(t, &labels));
    let verdict = crate::methods::field::reading_sums(linear, || {
        algebra::decide(&claimed, &cited, &labels)
    });
    let shown: Vec<&Node> = std::iter::once(&read.claimed).chain(&read.lines).collect();
    let render = |t: &Term| printed(t, &shown, known, targets, &labels);
    let number = at.step.number.to_string();
    if let Some(said) =
        algebra::refusal(&verdict, &at.claim.to_string(), &number, &render)
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

/// What an `algebra` step that holds leaves unsaid of its hypotheses
/// (`METHODS.md`, algebra): every atom of its claim and of the cited lines
/// it combines, `combined` by their place among `facts`, the cited lines'
/// facts one by one, is a number, said once or by a line the step names,
/// and every divisor they write other than a numeral is not zero by such a
/// line. None where both are said.
fn algebra_unsaid(
    at: &ClosureClaim,
    read: &ClosureRead,
    facts: &[Node],
    combined: &[usize],
    known: &Known,
    targets: &Targets,
) -> Option<String> {
    let held = MembershipIn::of(at, read, known);
    let given = held.given(targets, known);
    let mut relations = vec![read.claimed.clone()];
    relations.extend(
        combined
            .iter()
            .filter_map(|&i| facts.get(i))
            .filter(|n| algebra_relation(n))
            .cloned(),
    );
    for relation in &relations {
        let sides = sides_of(relation)
            .into_iter()
            .flat_map(|side| coordinates_of(side, targets));
        for side in sides {
            let parts = methods_membership::Parts::of(side);
            if let Some(atom) = parts
                .atoms
                .iter()
                .find(|a| !methods_membership::atom_held(a, System::C, &given))
            {
                return Some(unsaid_number(
                    atom,
                    at,
                    known,
                    "∈ ℝ or ∈ ℂ",
                    "nothing says",
                ));
            }
            if let Some(unsaid) = parts
                .divisors
                .iter()
                .find_map(|d| methods_membership::unsaid_part(d, &given))
            {
                return Some(format!(
                    "nothing says {} ≠ 0, which this step needs to divide by it",
                    known.print(&unsaid)
                ));
            }
        }
    }
    None
}

/// What an `inequalities` step that holds leaves unsaid of its hypotheses
/// (`METHODS.md`, inequalities): every atom of its claim and of the facts
/// the step combines (`inequalities::combined`), not of every sentence a
/// cited line says, is a real number, said once or by a line the step
/// names, and a divisor that is not a numeral is not zero by such a line.
/// None where both are said.
fn inequalities_unsaid(
    at: &ClosureClaim,
    read: &ClosureRead,
    known: &Known,
    targets: &Targets,
) -> Option<String> {
    let labels = FloatLabels::new(IndexMap::new());
    // The cited lines fact by fact, so that a line saying several things
    // asks only of the ones combined.
    let mut facts: Vec<Node> = Vec::new();
    let mut line_of: Vec<usize> = Vec::new();
    for (said, &line) in read.lines.iter().zip(&read.line_of) {
        for part in conjuncts(said) {
            facts.push(part);
            line_of.push(line);
        }
    }
    let implied: Vec<Term> = facts
        .iter()
        .flat_map(|part| implied_facts(part, known.env, &known.sorts))
        .chain(read.member_implies(known))
        .map(|n| term_of_node(&n, targets))
        .collect();
    let terms: Vec<Term> = facts.iter().map(|n| term_of_node(n, targets)).collect();
    let claimed = term_of_node(&read.claimed, targets);
    let used = inequalities::combined(&claimed, &terms, &line_of, &implied, &labels)?;
    let relations: Vec<Node> = conjuncts(&read.claimed)
        .into_iter()
        .chain(used.cited.iter().filter_map(|&i| facts.get(i).cloned()))
        .collect();
    real_unsaid(at, read, &relations, known, targets)
}

/// What `relations` leave unsaid of an order's hypotheses (`METHODS.md`,
/// inequalities, Hypotheses): every atom of their sides a real number, and
/// every divisor that is not a numeral not zero, each said once or by a line
/// the step names. None where both are said.
fn real_unsaid(
    at: &ClosureClaim,
    read: &ClosureRead,
    relations: &[Node],
    known: &Known,
    targets: &Targets,
) -> Option<String> {
    unsaid_of(at, read, relations, known, targets).map(|u| match &u {
        Unsaid::Real(atom) => unsaid_number(atom, at, known, "∈ ℝ", "nothing says"),
        Unsaid::Nonzero(_) => u.said(known),
    })
}

/// The message for an atom a method needs to be a number and nothing says
/// is one: a point is never one, which no line can say, so a point is told
/// that the step treats it as a number (`METHODS.md`, Rows: each row's atoms
/// are real); any other atom is told what is not said of it, `systems`
/// being "∈ ℝ" or "∈ ℝ or ∈ ℂ" and `nothing` how the message opens.
fn unsaid_number(
    atom: &Node,
    at: &ClosureClaim,
    known: &Known,
    systems: &str,
    nothing: &str,
) -> String {
    let point = atom.is_name()
        && super::library::points_introduced(known, at.step)
            .contains(atom.text.as_str());
    if point {
        format!(
            "this step treats {} as a number, and it is a point",
            known.print(atom)
        )
    } else {
        format!(
            "{nothing} {} {systems}, which this step needs",
            known.print(atom)
        )
    }
}

/// What an order's relations need of a term that nothing says.
enum Unsaid {
    /// An atom of a side, which has to be a real number.
    Real(Node),
    /// A divisor, or the part of one, which has to be other than 0.
    Nonzero(Node),
}

impl Unsaid {
    fn said(&self, known: &Known) -> String {
        self.told(known, "nothing says")
    }

    /// The message, opening with `nothing`: "nothing says", or "nothing
    /// above says" where a line below says it.
    fn told(&self, known: &Known, nothing: &str) -> String {
        match self {
            Unsaid::Real(atom) => {
                format!("{nothing} {} ∈ ℝ, which this step needs", known.print(atom))
            }
            Unsaid::Nonzero(part) => format!(
                "{nothing} {} ≠ 0, which this step needs to divide by it",
                known.print(part)
            ),
        }
    }

    /// Whether the two ask the same of the same term.
    fn same(&self, other: &Unsaid, known: &Known) -> bool {
        match (self, other) {
            (Unsaid::Real(a), Unsaid::Real(b))
            | (Unsaid::Nonzero(a), Unsaid::Nonzero(b)) => known.alike(a, b),
            _ => false,
        }
    }
}

/// `real_unsaid`, naming the term and what it needs.
fn unsaid_of(
    at: &ClosureClaim,
    read: &ClosureRead,
    relations: &[Node],
    known: &Known,
    targets: &Targets,
) -> Option<Unsaid> {
    let held = MembershipIn::of(at, read, known);
    let given = held.given(targets, known);
    for relation in relations {
        for side in relation_sides(relation) {
            let parts = methods_membership::Parts::of(side);
            if let Some(atom) = parts
                .atoms
                .iter()
                .find(|a| !methods_membership::atom_held(a, System::R, &given))
            {
                return Some(Unsaid::Real(atom.clone()));
            }
            if let Some(unsaid) = parts
                .divisors
                .iter()
                .find_map(|d| methods_membership::unsaid_part(d, &given))
            {
                return Some(Unsaid::Nonzero(unsaid));
            }
        }
    }
    None
}

/// A relation of `=`, `≠`, `<`, `≤`, `>` or `≥` as the page writes it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Rel {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Rel {
    fn of(node: &Node) -> Option<Rel> {
        // A disequality is the negation of an equation (`Related::of`): a
        // record declares `_ ≠ _` the negation of `_ = _`.
        match node.spelling() {
            EQUALS => Some(Rel::Eq),
            LESS => Some(Rel::Lt),
            AT_MOST => Some(Rel::Le),
            GREATER => Some(Rel::Gt),
            AT_LEAST => Some(Rel::Ge),
            _ => None,
        }
    }

    fn up(self) -> bool {
        matches!(self, Rel::Lt | Rel::Le)
    }

    fn down(self) -> bool {
        matches!(self, Rel::Gt | Rel::Ge)
    }

    /// The same relation read from its right side: `a < b` is `b > a`.
    fn converse(self) -> Rel {
        match self {
            Rel::Eq => Rel::Eq,
            Rel::Ne => Rel::Ne,
            Rel::Lt => Rel::Gt,
            Rel::Le => Rel::Ge,
            Rel::Gt => Rel::Lt,
            Rel::Ge => Rel::Le,
        }
    }
}

/// One relation between two terms, its sides as the page writes them, and
/// the formula it is read from.
#[derive(Clone, Debug)]
struct Related {
    left: Node,
    right: Node,
    rel: Rel,
    said: Node,
    /// Whether the line it is taken from writes it; one the line says
    /// without writing it has no written orientation (`METHODS.md`,
    /// inequalities, the first row).
    written: bool,
    /// Whether it is read from the right side of the formula it is taken
    /// from (`turned`).
    turned: bool,
}

impl Related {
    /// A formula that is one relation; None for any other, a conjunction of
    /// two among them. `a ≠ b` is read as the negation of `a = b`.
    fn of(node: &Node) -> Option<Related> {
        if let (LOGICAL_NOT, [inner]) = (node.notation(), node.children.as_slice()) {
            let equation = Related::of(inner).filter(|e| e.rel == Rel::Eq)?;
            return Some(Related {
                rel: Rel::Ne,
                said: node.clone(),
                ..equation
            });
        }
        let rel = Rel::of(node)?;
        let [left, right] = node.children.as_slice() else {
            return None;
        };
        Some(Related {
            left: left.clone(),
            right: right.clone(),
            rel,
            said: node.clone(),
            written: true,
            turned: false,
        })
    }

    /// The link read from its right side, from the same formula.
    fn turned(&self) -> Related {
        Related {
            left: self.right.clone(),
            right: self.left.clone(),
            rel: self.rel.converse(),
            said: self.said.clone(),
            written: self.written,
            turned: !self.turned,
        }
    }

    /// Whether this says what `other` says, as written or read from its
    /// right side.
    fn says(&self, other: &Related, known: &Known) -> bool {
        let same = |a: &Related, b: &Related| {
            a.rel == b.rel
                && known.alike(&a.left, &b.left)
                && known.alike(&a.right, &b.right)
        };
        same(self, other) || same(self, &other.turned())
    }

    /// Whether this says what `other` says, written the same way round: a
    /// row's relation as it stands (`METHODS.md`, inequalities, Rows), where
    /// turning an order round is a `restate` row of its own.
    fn says_as_written(&self, other: &Related, known: &Known) -> bool {
        self.rel == other.rel
            && known.alike(&self.left, &other.left)
            && known.alike(&self.right, &other.right)
    }
}

/// The relation a chain of these links gives (`METHODS.md`, transitivity),
/// as a calculation's: `=` where every link is `=`, and otherwise the order
/// it goes, strict where a link is. None for a chain going both ways.
fn chain_rel(links: &[Related]) -> Option<Rel> {
    let up = links.iter().any(|l| l.rel.up());
    let down = links.iter().any(|l| l.rel.down());
    let strict = links.iter().any(|l| matches!(l.rel, Rel::Lt | Rel::Gt));
    match (up, down) {
        (true, true) => None,
        (false, false) => Some(Rel::Eq),
        (true, false) => Some(if strict { Rel::Lt } else { Rel::Le }),
        (false, true) => Some(if strict { Rel::Gt } else { Rel::Ge }),
    }
}

/// Whether `term` starts `link`, as written or, for an equation, from its
/// right side.
fn starts(term: &Node, link: &Related, known: &Known) -> bool {
    known.alike(term, &link.left) || known.alike(term, &link.right)
}

/// Each relation of `=`, `≠`, `<`, `≤`, `>` or `≥` the line `r` in a step's
/// scope says (`Known::says`), as written: the line's own, or of a line
/// saying several things, `0 < x and x < 1`, each of them, an equation of a
/// chain and a bound a membership or a range gives among them, each with
/// whether the line writes it.
fn line_relations(step: &Step, r: &str, known: &Known) -> Vec<Related> {
    let Some(stated) = known.scope(step).get(r).cloned() else {
        return Vec::new();
    };
    let mut out: Vec<Related> = Vec::new();
    for said in known.says(&stated, &known.citing_step(step)) {
        let Some(mut related) = Related::of(&said.written) else {
            continue;
        };
        related.written = said.from.is_written();
        if !out.iter().any(|o| known.alike(&o.said, &related.said)) {
            out.push(related);
        }
    }
    out
}

/// A define of a theorem names something new, and names a thing.
///
/// Its name is no letter the theorem introduces, by a `let` or an `obtain`,
/// and no other define's of the theorem: a name stands for one thing, so a
/// line saying x says which x. And what it names is a number, a set or a
/// map, never a statement, as a statement is nothing for the name to equal
/// (`SYNTAX.md`, a define).
pub fn check_define_names(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    scopes: &[FileScope],
) {
    let letters = introduced(thm, known);
    let mut named: IndexMap<String, usize> = IndexMap::new();
    for d in &thm.defines {
        let Built(said) = define_parts(&d.text) else {
            continue;
        };
        for name in said.names() {
            if letters.contains(&name) {
                report.say(
                    &thm.path,
                    d.line,
                    format!(
                        "define {} names {name}, which theorem {} already introduces",
                        d.label, thm.name
                    ),
                );
            } else if let Some(at) = named.get(&name) {
                report.say(
                    &thm.path,
                    d.line,
                    format!("{name} is already defined at line {at}"),
                );
            }
            named.entry(name).or_insert(d.line);
        }
        let Some(name) = define_named(thm, &d.label, scopes) else {
            continue;
        };
        let defined = known.citing(std::slice::from_ref(&d.label));
        // A function's value is a thing as the name is: Q(x) = x < 1 is a
        // statement of x, and no function.
        if let Some(crate::matching::Defined::Rule(rule)) = defined.get(&name) {
            if rule.body.sort.is("formula") {
                report.say(
                    &thm.path,
                    d.line,
                    format!(
                        "define {} says each value of {name} is {}, a statement, and a define names a thing: a number, a set or a map",
                        d.label,
                        known.print(&rule.body)
                    ),
                );
            }
        }
        if let Some(crate::matching::Defined::Term(term)) = defined.get(&name) {
            if term.sort.is("formula") {
                report.say(
                    &thm.path,
                    d.line,
                    format!(
                        "define {} says {name} is {}, a statement, and a define names a thing: a number, a set or a map",
                        d.label,
                        known.print(term)
                    ),
                );
            }
        }
    }
}

/// The equation a define of a name says, `e = ⌊A + 1/2⌋ − A` of `let e =
/// ⌊A + 1/2⌋ − A`, as a link citing it reads it (`SYNTAX.md`, a step may
/// cite a define); None where `r` carries no define of a name standing for
/// a term.
pub(super) fn define_equation(
    thm: &Theorem,
    step: &Step,
    r: &str,
    known: &Known,
) -> Option<Node> {
    let name = define_named(thm, r, known.env.scopes)?;
    let defined = known.citing(&[r.to_string()]);
    let Some(crate::matching::Defined::Term(term)) = defined.get(&name) else {
        return None;
    };
    let named = Written::new(&name, &thm.path, step.just.line)
        .formula()
        .ok()?;
    let named = known.read_as_written(&named)?;
    Some(made(known.env.g, EQUALS, vec![named, term.clone()]))
}

/// A define of a function cited among a chain's lines, as a calculation's
/// link citing it is read: an equation between the term the line before
/// ends at and the one the line after starts from, which the define makes
/// one. Each such equation the neighbouring lines' terms give, the claim's
/// first and last terms standing for the lines at the ends; none where `r`
/// is no define.
fn define_applied(thm: &Theorem, step: &Step, r: &str, known: &Known) -> Vec<Related> {
    if !thm.defines.iter().any(|d| d.label == r) {
        return Vec::new();
    }
    let refs = &step.just.refs;
    let Some(at) = refs.iter().position(|x| x == r) else {
        return Vec::new();
    };
    let claim = known
        .whole_as_written(&step.claim)
        .as_ref()
        .and_then(Related::of);
    let terms_of = |i: Option<usize>, end: fn(&Related) -> Node| -> Vec<Node> {
        match i.and_then(|i| refs.get(i)) {
            Some(other) => line_relations(step, other, known)
                .iter()
                .flat_map(|l| [l.left.clone(), l.right.clone()])
                .collect(),
            None => claim.iter().map(end).collect(),
        }
    };
    let before = terms_of(at.checked_sub(1), |c| c.left.clone());
    let after = terms_of(Some(at + 1), |c| c.right.clone());
    let defined = known.citing(std::slice::from_ref(&r.to_string()));
    let mut out = Vec::new();
    for one in &before {
        for other in &after {
            let same = known.alike(
                &known.as_cited(one, &defined),
                &known.as_cited(other, &defined),
            );
            if same && !known.alike(one, other) {
                let said = made(known.env.g, EQUALS, vec![one.clone(), other.clone()]);
                out.extend(Related::of(&said));
            }
        }
    }
    out
}

/// What the line `r` in a step's scope says (`Known::says`), as written.
fn cited_says(step: &Step, r: &str, known: &Known) -> Vec<Node> {
    let Some(stated) = known.scope(step).get(r).cloned() else {
        return Vec::new();
    };
    known
        .says(&stated, &known.citing_step(step))
        .into_iter()
        .map(|s| s.written)
        .collect()
}

/// The lines a step cites, each as one link, in the order cited
/// (`METHODS.md`, transitivity): a line's relation, or of a line saying
/// several, the one of them that meets its neighbours, which is to be one
/// only. A define of a name says its equation besides any kind of number it
/// gives. The first line with no such relation reported.
fn cited_links(
    thm: &Theorem,
    step: &Step,
    known: &Known,
    method: &str,
) -> Checked<Vec<Related>> {
    let number = &step.number;
    let mut each: Vec<Vec<Related>> = Vec::new();
    for r in &step.just.refs {
        let mut said: Vec<Related> = line_relations(step, r, known)
            .into_iter()
            .filter(|l| l.rel != Rel::Ne)
            .collect();
        said.extend(
            define_equation(thm, step, r, known)
                .as_ref()
                .and_then(Related::of),
        );
        if said.is_empty() {
            said = define_applied(thm, step, r, known);
        }
        if said.is_empty() {
            // A membership is what a requires line takes from a line, where
            // the page does not say it once.
            let membership = cited_says(step, r, known).iter().any(|c| {
                c.notation() == MEMBERSHIP
                    && super::citations::membership_said_once(c, step, known).is_none()
            });
            let instead = if membership {
                ", and a membership it states is taken by a requires line"
            } else {
                ""
            };
            return Err(Problem::new(
                &thm.path,
                step.just.line,
                format!(
                    "step {number} cites {r} by {method}, and {r} states no relation of =, <, ≤, > or ≥{instead}"
                ),
            ));
        }
        each.push(said);
    }
    // Where a line says several relations, the claim decides
    // (`METHODS.md`, transitivity): the one taken from each line is the one
    // making a chain from the claim's first term to its last.
    if each.iter().any(|said| said.len() > 1) {
        let reaching = reaching_claim(thm, step, &each, known);
        match reaching.as_slice() {
            [one] => return Ok(one.clone()),
            [_, _, ..] => {
                return Err(Problem::new(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {number} cites lines by {method} that say several relations, and more than one choice of them reaches the claim"
                    ),
                ));
            }
            [] => {}
        }
    }
    let meets = |a: &Related, b: &Related| {
        starts(&a.left, b, known) || starts(&a.right, b, known)
    };
    let mut out: Vec<Related> = Vec::new();
    for (i, said) in each.iter().enumerate() {
        if let [one] = said.as_slice() {
            out.push(one.clone());
            continue;
        }
        let fits: Vec<&Related> = said
            .iter()
            .filter(|s| match out.last() {
                Some(before) => meets(before, s),
                None => each
                    .get(i + 1)
                    .is_some_and(|next| next.iter().any(|n| meets(s, n))),
            })
            .collect();
        let [one] = fits.as_slice() else {
            return Err(Problem::new(
                &thm.path,
                step.just.line,
                format!(
                    "step {number} cites {} by {method}, which says several relations, and not just one of them meets the lines it is cited with",
                    step.just.refs[i]
                ),
            ));
        };
        out.push((*one).clone());
    }
    Ok(out)
}

/// Each choice of one relation from each cited line, `each` in the order
/// cited, whose chain reaches the step's claim; none where the claim does
/// not read or no choice reaches it. Choices whose relations are the same
/// formulas are one.
fn reaching_claim(
    thm: &Theorem,
    step: &Step,
    each: &[Vec<Related>],
    known: &Known,
) -> Vec<Vec<Related>> {
    let Some(claim) = known
        .whole_as_written(&step.claim)
        .as_ref()
        .and_then(Related::of)
    else {
        return Vec::new();
    };
    let mut choices: Vec<Vec<Related>> = vec![Vec::new()];
    for said in each {
        choices = choices
            .into_iter()
            .flat_map(|before| {
                said.iter().map(move |one| {
                    let mut next = before.clone();
                    next.push(one.clone());
                    next
                })
            })
            .collect();
    }
    let mut out: Vec<Vec<Related>> = Vec::new();
    for choice in choices {
        let Ok(chained) = chain_of(thm, step, &choice, known) else {
            continue;
        };
        if !claim.says(&chained, known) {
            continue;
        }
        let seen = out.iter().any(|o| {
            o.iter()
                .zip(&choice)
                .all(|(a, b)| known.alike(&a.said, &b.said))
        });
        if !seen {
            out.push(choice);
        }
    }
    out
}

/// The relation each line a `transitivity` step cites gives its chain, as
/// written, with where it stands in the line and whether the chain reads it
/// from its right side, by the line of each step's justification
/// (`CheckedTheorem::links`); a step whose lines make no chain has none, and
/// is among the theorem's problems.
pub fn transitivity_links(
    thm: &Theorem,
    known: &Known,
    library: &Library,
) -> IndexMap<usize, Chain> {
    thm.steps
        .iter()
        .filter(|s| s.just.head.is(Method::Transitivity))
        .filter_map(|s| {
            let links = cited_links(thm, s, known, "transitivity").ok()?;
            let chain = faced(thm, s, &links, known).ok()?;
            let each = links.iter().zip(&chain).zip(&s.just.refs);
            let linked = each
                .map(|((link, read), r)| ChainLink {
                    said: link.said.clone(),
                    at: order_line(thm, s, r, &link.said, known, library),
                    turned: read.turned,
                })
                .collect();
            // The claim runs from the chain's first left side, or from its
            // last right side, written the other way round.
            let ends = chain_of(thm, s, &links, known).ok()?;
            let claim = Related::of(&known.whole_as_written(&s.claim)?)?;
            let claim_turned = !known.alike(&claim.left, &ends.left);
            let same = |a: &Node, b: &Node| known.print(a) == known.print(b);
            let (left, right) = match claim_turned {
                false => (&claim.left, &claim.right),
                true => (&claim.right, &claim.left),
            };
            let as_written = chain.windows(2).all(|w| same(&w[0].right, &w[1].left))
                && same(left, &ends.left)
                && same(right, &ends.right);
            Some((
                s.just.line,
                Chain {
                    links: linked,
                    claim_turned,
                    as_written,
                },
            ))
        })
        .collect()
}

/// What each order step rests on (`CheckedTheorem::orders`), by the line of
/// its justification: each plain `inequalities` step and each requires line
/// whose reason is `inequalities`, the combination the checker decided it by
/// (`inequalities::combined`); each step with rows, the line its first row
/// writes out; each requires line naming one manipulation, the line it
/// manipulates. One with a fact that stands nowhere a backend can name it
/// is left out.
pub fn order_steps(
    thm: &Theorem,
    known: &Known,
    library: &Library,
) -> IndexMap<usize, OrderStep> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        if step.just.head.is(Method::Inequalities) {
            let recorded = match step.just.rows.is_empty() {
                true => combined_order(thm, &ClosureClaim::step(step), known, library),
                false => rows_order(thm, step, known, library),
            };
            if let Some(order) = recorded {
                out.insert(step.just.line, order);
            }
        }
        for req in &step.requires {
            let recorded = match req.is(Method::Inequalities) {
                true => combined_order(
                    thm,
                    &ClosureClaim::requires(step, req),
                    known,
                    library,
                ),
                false => manipulation_order(thm, step, req, known, library),
            };
            if let Some(order) = recorded {
                out.insert(req.line, order);
            }
        }
    }
    out
}

/// A fact a membership among an order step's facts implies
/// (`combined_order`), with the rule, and the fact it is implied by, by its
/// place; None for the member a claim said of every member is read at.
struct ImpliedFact {
    node: Node,
    rule: crate::citing::Implication,
    from: Option<usize>,
}

/// What a plain order claim rests on, read as `inequalities_hold` reads it
/// to decide it: each fact of the lines it cites, part by part, and what a
/// membership among them, or the member it is read at, implies.
fn combined_order(
    thm: &Theorem,
    at: &ClosureClaim,
    known: &Known,
    library: &Library,
) -> Option<OrderStep> {
    let targets = &library.targets;
    let mut read = at.read(known, targets, false)?;
    read.read_at_member(known);
    let mut facts: Vec<Node> = Vec::new();
    let mut line_of: Vec<usize> = Vec::new();
    for (said, &line) in read.lines.iter().zip(&read.line_of) {
        for part in conjuncts(said) {
            facts.push(part);
            line_of.push(line);
        }
    }
    let mut implied: Vec<ImpliedFact> = Vec::new();
    for (i, part) in facts.iter().enumerate() {
        for (node, rule) in crate::citing::implied_by(part, known.env, &known.sorts) {
            implied.push(ImpliedFact {
                node,
                rule,
                from: Some(i),
            });
        }
    }
    if let Some(member) = &read.member {
        for (node, rule) in crate::citing::implied_by(member, known.env, &known.sorts) {
            implied.push(ImpliedFact {
                node,
                rule,
                from: None,
            });
        }
    }
    let labels = FloatLabels::new(IndexMap::new());
    let terms: Vec<Term> = facts.iter().map(|n| term_of_node(n, targets)).collect();
    let implied_terms: Vec<Term> = implied
        .iter()
        .map(|i| term_of_node(&i.node, targets))
        .collect();
    let fact_of = |source: inequalities::Source| -> Option<OrderFact> {
        match source {
            inequalities::Source::Cited(i) => {
                order_fact(thm, at, line_of[i], &facts[i], known, library)
            }
            // What a fact implies stands where the fact does, with the rule.
            inequalities::Source::Implied(j) => {
                let one = &implied[j];
                let Some(i) = one.from else {
                    return Some(OrderFact::Member {
                        implied: one.rule,
                        written: one.node.clone(),
                    });
                };
                match order_fact(thm, at, line_of[i], &facts[i], known, library)? {
                    OrderFact::Line(source) => Some(OrderFact::Line(FirstAt {
                        written: one.node.clone(),
                        implied: Some(one.rule),
                        ..source
                    })),
                    OrderFact::Requires {
                        line,
                        implied: None,
                    } => Some(OrderFact::Requires {
                        line,
                        implied: Some(one.rule),
                    }),
                    OrderFact::Define(define) => Some(OrderFact::Kind {
                        define,
                        implied: one.rule,
                        written: one.node.clone(),
                    }),
                    _ => None,
                }
            }
        }
    };
    let mut sentences = Vec::new();
    for sentence in &read.sentences {
        let claimed = term_of_node(sentence, targets);
        let combined = inequalities::combined(
            &claimed,
            &terms,
            &line_of,
            &implied_terms,
            &labels,
        )?;
        // A define the step cites is read written out, its name its value,
        // so its equation stands among what every part adds.
        let defines: Vec<OrderFact> = at
            .refs
            .iter()
            .filter(|r| thm.defines.iter().any(|d| d.label == **r))
            .map(|r| OrderFact::Define(r.clone()))
            .collect();
        let mut parts = Vec::new();
        for part in combined.parts {
            let restates = match part.restates {
                Some(r) => Some(OrderRestated {
                    by: fact_of(r.by)?,
                    turned: r.turned,
                }),
                None => None,
            };
            let mut uses: Vec<OrderFact> =
                part.uses.into_iter().map(fact_of).collect::<Option<_>>()?;
            for d in &defines {
                let named = |f: &OrderFact| matches!((f, d), (OrderFact::Define(a), OrderFact::Define(b)) if a == b);
                if !uses.iter().any(named) {
                    uses.push(d.clone());
                }
            }
            parts.push(OrderPart {
                uses,
                split: part.split.into_iter().map(fact_of).collect::<Option<_>>()?,
                restates,
                weakened: None,
            });
        }
        sentences.push(parts);
    }
    Some(OrderStep { sentences })
}

/// Where `fact`, of the line `line` among what `at` reads (`ClosureRead::
/// line_of`), stands: a sentence or part of a cited line, a cited define's
/// equation, or a requires line above. None where it stands in none of
/// those as one sentence.
fn order_fact(
    thm: &Theorem,
    at: &ClosureClaim,
    line: usize,
    fact: &Node,
    known: &Known,
    library: &Library,
) -> Option<OrderFact> {
    let Some(r) = at.refs.get(line) else {
        let k = line - at.refs.len();
        let above = at.above.get(k)?;
        return (above.fact.sentences().len() == 1).then_some(OrderFact::Requires {
            line: k,
            implied: None,
        });
    };
    if thm.defines.iter().any(|d| d.label == *r) {
        return Some(OrderFact::Define(r.clone()));
    }
    // The line is read with every define the step cites written out, as
    // the step reads it; it is looked in first.
    let mut refs = vec![r.clone()];
    refs.extend(at.refs.iter().filter(|o| *o != r).cloned());
    super::citations::fact_at(at.step, &refs, None, fact, known, library)
        .filter(|found| found.line == *r)
        .map(OrderFact::Line)
}

/// What an `inequalities` step with rows rests on: the line its first row
/// writes out, and, where its last row weakens an order to a disequality,
/// which way the order runs.
fn rows_order(
    thm: &Theorem,
    step: &Step,
    known: &Known,
    library: &Library,
) -> Option<OrderStep> {
    let written = rows(&step.just, &thm.path)?.ok()?;
    let RowReason::Cited(r) = &written.first()?.reason else {
        return None;
    };
    let read: Vec<Related> = written
        .iter()
        .map(|row| {
            let node = known.parse(&row.formula.formula().ok()?).ok()?;
            Related::of(&node)
        })
        .collect::<Option<_>>()?;
    // The relation of the line the first row writes out, as
    // `check_inequality_rows` finds it.
    let said = line_relations(step, r, known).into_iter().find(|line| {
        line.says_as_written(&read[0], known)
            || (!line.written && line.says(&read[0], known))
    })?;
    let first = order_line(thm, step, r, &said.said, known, library)?;
    let weakened = match (written.last().map(|w| &w.reason), read.as_slice()) {
        (Some(RowReason::Weakening), [.., above, last]) if last.rel == Rel::Ne => {
            Some(weakened_of(above.rel)?)
        }
        _ => None,
    };
    // Rows from a disequality turn it round and nothing more: the claim is
    // the line, turned where an odd number of rows turns it.
    if read[0].rel == Rel::Ne {
        let turns = written
            .iter()
            .filter(|w| matches!(w.reason, RowReason::Restate))
            .count();
        return Some(OrderStep {
            sentences: vec![vec![OrderPart {
                uses: Vec::new(),
                split: Vec::new(),
                restates: Some(OrderRestated {
                    by: first,
                    turned: turns % 2 == 1,
                }),
                weakened: None,
            }]],
        });
    }
    Some(OrderStep {
        sentences: vec![vec![OrderPart {
            uses: vec![first],
            split: Vec::new(),
            restates: None,
            weakened,
        }]],
    })
}

/// What a requires line naming one manipulation, `requires q ≠ 0:
/// weakening, from 2.1`, rests on: the relation of the line it cites that
/// the manipulation makes its fact of, as `check_requires_manipulations`
/// finds it. None of any other requires line.
fn manipulation_order(
    thm: &Theorem,
    step: &Step,
    req: &Requires,
    known: &Known,
    library: &Library,
) -> Option<OrderStep> {
    let Ok(by) = &req.by else {
        return None;
    };
    let Head::Manipulation(made) = &by.head else {
        return None;
    };
    let [cited] = req.lines() else {
        return None;
    };
    let reason = made.as_row(&thm.path, req.line);
    let fact = Related::of(&known.whole_as_written(&req.fact)?)?;
    let term = match &reason {
        RowReason::Adding(t) | RowReason::Multiplying(t) => {
            Some(reason_term(&t.clone(), known).ok()?)
        }
        _ => None,
    };
    let targets = &library.targets;
    let line = line_relations(step, cited, known)
        .into_iter()
        .find(|line| {
            row_follows(line, &fact, &reason, term.as_ref(), known, targets)
        })?;
    let weakened = match (&reason, fact.rel) {
        (RowReason::Weakening, Rel::Ne) => Some(weakened_of(line.rel)?),
        _ => None,
    };
    Some(OrderStep {
        sentences: vec![vec![OrderPart {
            uses: vec![order_line(thm, step, cited, &line.said, known, library)?],
            split: Vec::new(),
            restates: None,
            weakened,
        }]],
    })
}

/// Where the relation `said` of the line `r` a step cites stands: the
/// line's sentence or part, or a define's equation.
fn order_line(
    thm: &Theorem,
    step: &Step,
    r: &str,
    said: &Node,
    known: &Known,
    library: &Library,
) -> Option<OrderFact> {
    if thm.defines.iter().any(|d| d.label == r) {
        return Some(OrderFact::Define(r.to_string()));
    }
    // A line's facts are found as the checker reads them, in the standard
    // order.
    let r = r.to_string();
    let said = standard(said, &library.ctx);
    super::citations::fact_at(
        step,
        std::slice::from_ref(&r),
        None,
        &said,
        known,
        library,
    )
    .map(OrderFact::Line)
}

/// Which way the strict order a disequality is weakened from runs, read
/// from its left side; None of an order that is not strict.
fn weakened_of(rel: Rel) -> Option<Weakened> {
    match rel {
        Rel::Lt => Some(Weakened::Below),
        Rel::Gt => Some(Weakened::Above),
        _ => None,
    }
}

/// How each `antisymmetry` step's two lines make its equation
/// (`CheckedTheorem::antisymmetric`), by the line of its justification: the
/// line that says the claim's left side is at most its right, and the line
/// that says the converse, as `check_antisymmetry` pairs them. One citing a
/// define is left out.
pub fn antisymmetries(
    thm: &Theorem,
    known: &Known,
    library: &Library,
) -> IndexMap<usize, Antisymmetric> {
    thm.steps
        .iter()
        .filter(|s| s.just.head.is(Method::Antisymmetry))
        .filter_map(|step| {
            let links = cited_links(thm, step, known, "antisymmetry").ok()?;
            let ([one, other], [r1, r2]) =
                (links.as_slice(), step.just.refs.as_slice())
            else {
                return None;
            };
            let claim = Related::of(&known.whole_as_written(&step.claim)?)?;
            // Each read from below: `b ≥ a` is `a ≤ b`.
            let low = |l: &Related| match l.rel {
                Rel::Ge => l.right.clone(),
                _ => l.left.clone(),
            };
            let (below, above) = match known.alike(&low(one), &claim.left) {
                true => ((one, r1), (other, r2)),
                false => ((other, r2), (one, r1)),
            };
            let at = |(link, r): (&Related, &String)| -> Option<FirstAt> {
                if thm.defines.iter().any(|d| d.label == *r) {
                    return None;
                }
                super::citations::fact_at(
                    step,
                    std::slice::from_ref(r),
                    None,
                    &standard(&link.said, &library.ctx),
                    known,
                    library,
                )
            };
            Some((
                step.just.line,
                Antisymmetric {
                    below: at(below)?,
                    above: at(above)?,
                },
            ))
        })
        .collect()
}

/// The chain a `transitivity` step's lines make, each line's right side the
/// next one's left side, written the same way. A line may be read from
/// either side, an order as its converse (`b > a` is `a < b`), and the chain
/// goes one way as its lines are read. The link from the first left side to
/// the last right side, or the defect.
fn chain_of(
    thm: &Theorem,
    step: &Step,
    links: &[Related],
    known: &Known,
) -> Checked<Related> {
    let number = &step.number;
    let defect = |message: String| Problem::new(&thm.path, step.just.line, message);
    let chain = faced(thm, step, links, known)?;
    let Some(rel) = chain_rel(&chain) else {
        return Err(defect(format!(
            "step {number} chains orders going up and going down, which say nothing of its ends"
        )));
    };
    // The skeleton refuses a `transitivity` with no `from`.
    let (first, last) = (
        chain.first().expect("a chain's first line"),
        chain.last().expect("a chain's last line"),
    );
    Ok(Related {
        left: first.left.clone(),
        right: last.right.clone(),
        rel,
        said: last.said.clone(),
        written: true,
        turned: false,
    })
}

/// The links of a `transitivity` step's chain, each read the way the chain
/// goes (`chain_of`): its right side the next one's left side.
fn faced(
    thm: &Theorem,
    step: &Step,
    links: &[Related],
    known: &Known,
) -> Checked<Vec<Related>> {
    let number = &step.number;
    let defect = |message: String| Problem::new(&thm.path, step.just.line, message);
    let mut chain: Vec<Related> = Vec::new();
    for (i, link) in links.iter().enumerate() {
        let link = match chain.last() {
            None => {
                // The first line faces the way the next line takes it.
                let next = links.get(i + 1);
                let turn = next.is_some_and(|n| {
                    !starts(&link.right, n, known) && starts(&link.left, n, known)
                });
                if turn {
                    link.turned()
                } else {
                    link.clone()
                }
            }
            Some(before) if known.alike(&before.right, &link.left) => link.clone(),
            Some(before) if known.alike(&before.right, &link.right) => link.turned(),
            Some(before) => {
                return Err(defect(format!(
                    "the lines step {number} chains do not meet: {} ends at {}, and {} starts from {}; a middle term is written the same way in both",
                    step.just.refs[i - 1],
                    known.print(&before.right),
                    step.just.refs[i],
                    known.print(&link.left)
                )));
            }
        };
        chain.push(link);
    }
    Ok(chain)
}

/// A `transitivity` step (`METHODS.md`, transitivity): the lines it cites
/// make a chain in the order cited, and the claim is the chain's first term
/// related to its last by the chain's relation, written either way round.
/// Where a link is an order, every atom of the chain is real.
pub fn check_transitivity(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in thm
        .steps
        .iter()
        .filter(|s| s.just.head.is(Method::Transitivity))
    {
        let checked = cited_links(thm, step, known, "transitivity")
            .and_then(|links| chain_of(thm, step, &links, known).map(|c| (links, c)));
        let (links, chained) = match checked {
            Ok(both) => both,
            Err(defect) => {
                report.problems.push(defect);
                continue;
            }
        };
        let Some(claim) = known.whole_as_written(&step.claim) else {
            continue; // `check_formulas` says it does not read
        };
        let reached = Related::of(&claim).is_some_and(|c| c.says(&chained, known));
        if !reached {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} claims {}, and the chain it cites gives {} {} {}",
                    step.number,
                    step.claim_text(),
                    known.print(&chained.left),
                    sign(chained.rel),
                    known.print(&chained.right)
                ),
            );
            continue;
        }
        if chained.rel != Rel::Eq {
            report_unreal(report, thm, step, &claim, &links, known, targets);
        }
    }
}

/// A calculation claims its chain's first term related to its last by the
/// chain's relation: `=` where every link is `=`, the way the chain goes
/// where a link is an order, strict where one is, and `≡ (mod n)` where a
/// link is a congruence (`SYNTAX.md`, calculation). A chain of `=` and `>`
/// claims `>`, not `≥`.
pub fn check_calculation_claims(report: &mut Report, thm: &Theorem, known: &Known) {
    for step in &thm.steps {
        let links = chain_links(&step.just, &thm.path);
        let Some(chained) = chain_claim(&links, known) else {
            continue;
        };
        let chained = match chained {
            ChainClaim::Ends(node) => node,
            ChainClaim::BothWays => {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} chains orders going up and going down, which say nothing of its ends",
                        step.number
                    ),
                );
                continue;
            }
        };
        let Some(claim) = known.whole_as_written(&step.claim) else {
            continue; // `check_formulas` says it does not read
        };
        if !known.alike(&claim, &chained) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {} claims {}, and its chain gives {}",
                    step.number,
                    step.claim_text(),
                    known.print(&chained)
                ),
            );
        }
    }
}

/// A `substitute` step's rows start from what the line the first row cites
/// says, written out, and end on the claim (`GRAMMAR.md`, substitute rows),
/// or on the claim in its other form (`rules::OTHER_FORMS`);
/// what each row after the first changes is its reason's to prove, which
/// `check_link_reasons` asks. A `substitute` writing no equation and no rows
/// says nothing.
pub fn check_substitute_rows(report: &mut Report, thm: &Theorem, known: &Known) {
    for step in &thm.steps {
        let just = &step.just;
        if !just.head.is(Method::Substitute) || just.equation.is_some() {
            continue;
        }
        if just.source.is_none() && just.rows.is_empty() {
            report.say(
                &thm.path,
                just.line,
                format!(
                    "step {} substitutes nothing: it writes its equation, `substitute e (line L)`, or its rows below it",
                    step.number
                ),
            );
            continue;
        }
        let rows = match substitute_rows(just, &thm.path) {
            None => continue,
            Some(Err(p)) => {
                report.say(&p.path, p.line, p.message);
                continue;
            }
            Some(Ok(rows)) => rows,
        };
        let read = |w: &Written| known.read_as_written(&w.formula().ok()?);
        let (Some(first), Some(last)) = (rows.first(), rows.last()) else {
            continue;
        };
        if let Some(written) = read(&first.formula) {
            let said = known.lines_say(step, &[first.cite.as_str()]);
            if !said.iter().any(|s| known.alike(s, &written)) {
                report.say(
                    &thm.path,
                    first.line,
                    format!(
                        "the first row of step {} writes {}, which {} does not say",
                        step.number, first.formula, first.cite
                    ),
                );
            }
        }
        let (Some(ends), Some(claim)) =
            (read(&last.formula), known.whole_as_written(&step.claim))
        else {
            continue; // `check_formulas` says it does not read
        };
        // The last row may write the claim in its other form, which says
        // the claim (`rules::OTHER_FORMS`).
        let other = said_otherwise(&ends, known.env, &known.sorts);
        let ends_on_claim = std::iter::once(&ends)
            .chain(other.as_ref())
            .any(|e| known.alike(e, &claim));
        if !ends_on_claim {
            report.say(
                &thm.path,
                last.line,
                format!(
                    "the last row of step {} writes {}, and the step claims {}",
                    step.number,
                    last.formula,
                    step.claim_text()
                ),
            );
        }
    }
}

/// What a calculation's chain gives of its ends.
enum ChainClaim {
    /// The first term related to the last by the chain's relation.
    Ends(Node),
    /// Orders going up and going down, which give nothing.
    BothWays,
}

/// What `links` give, as `check_calculation_claims` reads it; None for no
/// chain, a link that does not read (`check_formulas`' to report), or a
/// congruence joined with an order (`check_chain_congruences`').
fn chain_claim(links: &[Link], known: &Known) -> Option<ChainClaim> {
    let read = |w: &Written| known.read_as_written(&w.formula().ok()?);
    let first = read(&links.first()?.from)?;
    let last_line = &links.last()?.line;
    let last = read(&last_line.term)?;
    let congruence = links.iter().find(|l| l.line.relation == "≡");
    let (relation, modulus) = match congruence {
        Some(link) => {
            let ordered = links
                .iter()
                .any(|l| !["=", "≡"].contains(&l.line.relation.as_str()));
            if ordered {
                return None;
            }
            ("≡", Some(read(link.line.modulus.as_ref()?)?))
        }
        None => {
            let related: Option<Vec<Related>> = links
                .iter()
                .map(|l| l.claim(known).as_ref().and_then(Related::of))
                .collect();
            match chain_rel(&related?) {
                Some(rel) => (sign(rel), None),
                None => return Some(ChainClaim::BothWays),
            }
        }
    };
    let at = (last_line.term.path(), last_line.line);
    let (g, sorts) = (known.env.g, &known.sorts);
    related(g, sorts, relation, &first, &last, modulus.as_ref(), at)
        .ok()
        .map(ChainClaim::Ends)
}

/// An `antisymmetry` step (`METHODS.md`, antisymmetry): it cites two lines,
/// an order `a ≤ b` and its converse `b ≤ a`, and claims `a = b`, either way
/// round, every atom of the two sides real.
pub fn check_antisymmetry(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in thm
        .steps
        .iter()
        .filter(|s| s.just.head.is(Method::Antisymmetry))
    {
        let links = match cited_links(thm, step, known, "antisymmetry") {
            Ok(links) => links,
            Err(defect) => {
                report.problems.push(defect);
                continue;
            }
        };
        let number = &step.number;
        // Each read from below: `b ≥ a` is `a ≤ b`.
        let below: Vec<Related> = links
            .iter()
            .map(|l| {
                if l.rel == Rel::Ge {
                    l.turned()
                } else {
                    l.clone()
                }
            })
            .collect();
        let converse = match below.as_slice() {
            [one, other] => {
                one.rel == Rel::Le
                    && other.rel == Rel::Le
                    && known.alike(&one.left, &other.right)
                    && known.alike(&one.right, &other.left)
            }
            _ => false,
        };
        if !converse {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {number} cites by antisymmetry what is not two lines a ≤ b and b ≤ a, an order and its converse"
                ),
            );
            continue;
        }
        let Some(claim) = known.whole_as_written(&step.claim) else {
            continue; // `check_formulas` says it does not read
        };
        let equation = Related {
            left: below[0].left.clone(),
            right: below[0].right.clone(),
            rel: Rel::Eq,
            said: claim.clone(),
            written: true,
            turned: false,
        };
        if !Related::of(&claim).is_some_and(|c| c.says(&equation, known)) {
            report.say(
                &thm.path,
                step.just.line,
                format!(
                    "step {number} claims {}, and its lines give {} = {}",
                    step.claim_text(),
                    known.print(&equation.left),
                    known.print(&equation.right)
                ),
            );
            continue;
        }
        report_unreal(report, thm, step, &claim, &links, known, targets);
    }
}

/// Whether two terms are one number by the field's identities, as `algebra`
/// decides an identity (`methods::algebra`): what writing a side another way
/// keeps.
fn one_number(a: &Node, b: &Node, known: &Known, targets: &Targets) -> bool {
    let equation = made(known.env.g, EQUALS, vec![a.clone(), b.clone()]);
    let labels = FloatLabels::new(IndexMap::new());
    matches!(
        algebra::decide(&term_of_node(&equation, targets), &[], &labels),
        algebra::Verdict::Holds { .. }
    )
}

/// A term written in a row's reason, `adding 2·A` or `multiplying by 1/2`,
/// read through the tree reader.
fn reason_term(written: &Written, known: &Known) -> Checked<Node> {
    known.parse(&written.formula()?)
}

/// Whether `row` is `above` with the manipulation `reason` names
/// (`METHODS.md`, inequalities, Rows), each side compared as one number
/// (`one_number`). `term` is the term the reason writes, read.
fn row_follows(
    above: &Related,
    row: &Related,
    reason: &RowReason,
    term: Option<&Node>,
    known: &Known,
    targets: &Targets,
) -> bool {
    let g = known.env.g;
    let sides = |rel: Rel, left: &Node, right: &Node| {
        row_is(row, rel, left, right, known, targets)
    };
    match (reason, term) {
        (RowReason::Adding(_), Some(t)) => {
            let plus = |side: &Node| made(g, PLUS, vec![side.clone(), t.clone()]);
            sides(above.rel, &plus(&above.left), &plus(&above.right))
        }
        (RowReason::Multiplying(_), Some(c)) => {
            let labels = FloatLabels::new(IndexMap::new());
            let Some(value) = linear::numeral(&term_of_node(c, targets), &labels)
            else {
                return false;
            };
            if num_traits::Zero::is_zero(&value) {
                return false;
            }
            // A negative number turns an order round.
            let rel = if num_traits::Signed::is_negative(&value) {
                above.rel.converse()
            } else {
                above.rel
            };
            let times = |side: &Node| made(g, TIMES, vec![c.clone(), side.clone()]);
            sides(rel, &times(&above.left), &times(&above.right))
        }
        // An equation's sides swapped, or an order turned round: `a > 0` to
        // `0 < a`.
        (RowReason::Restate, _) => row.says_as_written(&above.turned(), known),
        (RowReason::Weakening, _) => {
            let weaker = matches!(
                (above.rel, row.rel),
                (Rel::Lt, Rel::Le)
                    | (Rel::Gt, Rel::Ge)
                    | (Rel::Eq, Rel::Le)
                    | (Rel::Eq, Rel::Ge)
                    | (Rel::Lt, Rel::Ne)
                    | (Rel::Gt, Rel::Ne)
            );
            weaker
                && known.alike(&row.left, &above.left)
                && known.alike(&row.right, &above.right)
        }
        (RowReason::Algebra, _) => sides(above.rel, &above.left, &above.right),
        _ => false,
    }
}

/// Whether `row` relates by `rel` two sides that are `left` and `right`,
/// each as one number (`one_number`), written that way round: an
/// equation's sides swapped, or an order turned round, is a `restate` row
/// of its own.
fn row_is(
    row: &Related,
    rel: Rel,
    left: &Node,
    right: &Node,
    known: &Known,
    targets: &Targets,
) -> bool {
    row.rel == rel
        && one_number(&row.left, left, known, targets)
        && one_number(&row.right, right, known, targets)
}

/// What a row names, said in a message: `with 2·A added to both sides`.
fn row_said(reason: &RowReason) -> String {
    match reason {
        RowReason::Cited(r) => format!("as {r} says it"),
        RowReason::Adding(t) => format!("with {t} added to both sides"),
        RowReason::Multiplying(c) => {
            format!("with both sides multiplied by {c}, a numeral other than 0")
        }
        RowReason::Restate => "with its two sides swapped".to_string(),
        RowReason::Weakening => "with its relation weakened".to_string(),
        RowReason::Algebra => {
            "with a side written as the same number another way".to_string()
        }
    }
}

/// An `inequalities` step's rows (`METHODS.md`, inequalities, Rows): each
/// a single relation, read through the tree reader; the first the line the
/// step cites, written out; each after it the row above with the
/// manipulation its reason names, its atoms real as a step's are; and the
/// last the claim, written either way round.
pub fn check_inequality_rows(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in &thm.steps {
        let Some(cut) = rows(&step.just, &thm.path) else {
            continue;
        };
        let number = &step.number;
        let written = match cut {
            Ok(written) => written,
            Err(defect) => {
                report.problems.push(defect);
                continue;
            }
        };
        let mut read: Vec<Related> = Vec::new();
        for row in &written {
            let node = match row.formula.formula().and_then(|s| known.parse(&s)) {
                Ok(node) => node,
                Err(problem) => {
                    report.problems.push(problem);
                    break;
                }
            };
            let Some(related) = Related::of(&node) else {
                report.say(
                    &thm.path,
                    row.line,
                    format!("a row of step {number} is no single relation of =, ≠, <, ≤, > or ≥"),
                );
                break;
            };
            read.push(related);
        }
        if read.len() != written.len() {
            continue;
        }
        // The first row writes out the line it cites, the step's only one,
        // or one of the relations a line saying several says.
        let cited_lines = match &written[0].reason {
            RowReason::Cited(r) => line_relations(step, r, known),
            _ => Vec::new(),
        };
        // A relation the line says without writing it has no written
        // orientation, and the row may write it either way round
        // (`METHODS.md`, inequalities).
        if !cited_lines.iter().any(|line| {
            line.says_as_written(&read[0], known)
                || (!line.written && line.says(&read[0], known))
        }) {
            // The line turned round is a restate row after it, not the
            // first row (`METHODS.md`, inequalities, Rows).
            let turned = cited_lines.iter().any(|line| line.says(&read[0], known));
            let said = if turned {
                format!(
                    "the first row of step {number} is the line it cites turned round; write the line as it is written, and turn it with a restate row"
                )
            } else {
                format!(
                    "the first row of step {number} is not a line the step cites, written out with its label as its reason"
                )
            };
            report.say(&thm.path, written[0].line, said);
            continue;
        }
        let whole_cited: Vec<Node> = match &written[0].reason {
            RowReason::Cited(r) => cited_says(step, r, known),
            _ => Vec::new(),
        };
        let mut held = true;
        for (i, row) in written.iter().enumerate().skip(1) {
            let term = match &row.reason {
                RowReason::Adding(t) | RowReason::Multiplying(t) => {
                    match reason_term(t, known) {
                        Ok(node) => Some(node),
                        Err(problem) => {
                            report.problems.push(problem);
                            held = false;
                            break;
                        }
                    }
                }
                _ => None,
            };
            if !row_follows(
                &read[i - 1],
                &read[i],
                &row.reason,
                term.as_ref(),
                known,
                targets,
            ) {
                // The manipulation and a turn are two rows, the turn a
                // restate row of its own.
                let turned = !matches!(row.reason, RowReason::Restate)
                    && row_follows(
                        &read[i - 1],
                        &read[i].turned(),
                        &row.reason,
                        term.as_ref(),
                        known,
                        targets,
                    );
                let said = if turned {
                    format!(
                        "a row of step {number} is the row above {}, turned round; turning it round is a restate row of its own",
                        row_said(&row.reason)
                    )
                } else {
                    format!(
                        "a row of step {number} is not the row above {}",
                        row_said(&row.reason)
                    )
                };
                report.say(&thm.path, row.line, said);
                held = false;
                break;
            }
            // What the cited line says besides the relation the rows start
            // from, `x ∈ ℝ. x > 0.`, says it of every row.
            let relations = [read[i].said.clone(), read[i - 1].said.clone()];
            let mut lines = vec![relations[1].clone()];
            lines.extend(whole_cited.iter().cloned());
            let line_of = vec![0; lines.len()];
            let pair = ClosureRead::new(relations[0].clone(), lines, line_of);
            if let Some(said) = real_unsaid(
                &ClosureClaim::step(step),
                &pair,
                &relations,
                known,
                targets,
            ) {
                report.say(&thm.path, row.line, said);
                held = false;
                break;
            }
        }
        let Some(claim) = known.whole_as_written(&step.claim) else {
            continue; // `check_formulas` says it does not read
        };
        let last = read.last().expect("a step's rows");
        let claimed = Related::of(&claim);
        if held
            && !claimed
                .as_ref()
                .is_some_and(|c| c.says_as_written(last, known))
        {
            let said = if claimed.is_some_and(|c| c.says(last, known)) {
                format!(
                    "the last row of step {number} is its claim turned round; end with a restate row that writes the claim as it is written"
                )
            } else {
                format!("the last row of step {number} is not its claim")
            };
            report.say(&thm.path, written[written.len() - 1].line, said);
        }
    }
}

/// A requires line naming one manipulation, `requires q ≠ 0: weakening,
/// from 2.1` (`METHODS.md`, inequalities, Rows): its fact is the one line it
/// cites with that manipulation, as a row is of the row above, and its
/// atoms are real.
pub fn check_requires_manipulations(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in &thm.steps {
        for req in &step.requires {
            let Ok(by) = &req.by else {
                continue;
            };
            let Head::Manipulation(made) = &by.head else {
                continue;
            };
            // One that does not name its one line is `check_reason`'s.
            let [cited] = req.lines() else {
                continue;
            };
            let cited = cited.clone();
            let reason = made.as_row(&thm.path, req.line);
            let said = line_relations(step, &cited, known);
            let fact = known
                .whole_as_written(&req.fact)
                .and_then(|n| Related::of(&n));
            let term = match &reason {
                RowReason::Adding(t) | RowReason::Multiplying(t) => {
                    match reason_term(&t.clone(), known) {
                        Ok(node) => Some(node),
                        Err(problem) => {
                            report.problems.push(problem);
                            continue;
                        }
                    }
                }
                _ => None,
            };
            // The fact is the line with the one manipulation, written the way
            // round the manipulation leaves it. Of a line saying several
            // relations, it is one of them manipulated.
            let line = fact.as_ref().and_then(|fact| {
                said.iter()
                    .find(|line| {
                        row_follows(line, fact, &reason, term.as_ref(), known, targets)
                    })
                    .cloned()
            });
            if line.is_none() {
                // The manipulation and a turn are two, and a requires line
                // names one (`METHODS.md`, inequalities, Rows).
                let turned = fact.as_ref().map(Related::turned).filter(|turned| {
                    !matches!(reason, RowReason::Restate)
                        && said.iter().any(|line| {
                            row_follows(
                                line,
                                turned,
                                &reason,
                                term.as_ref(),
                                known,
                                targets,
                            )
                        })
                });
                let message = if let Some(t) = turned {
                    format!(
                        "the requires line {} of {} is {cited} {}, turned round; a requires line names one manipulation, so write it as the manipulation leaves it: {} {} {}",
                        str::trim(req.fact.text()),
                        step.called(),
                        row_said(&reason),
                        known.print(&t.left),
                        sign(t.rel),
                        known.print(&t.right)
                    )
                } else {
                    format!(
                        "the requires line {} of {} is not {cited} {}",
                        str::trim(req.fact.text()),
                        step.called(),
                        row_said(&reason)
                    )
                };
                report.say(&thm.path, req.line, message);
                continue;
            }
            let (Some(line), Some(fact)) = (line, fact) else {
                continue;
            };
            let relations = [fact.said.clone(), line.said.clone()];
            let at = ClosureClaim::requires(step, req);
            let Some(read) = at.read(known, targets, false) else {
                continue;
            };
            let Some(unsaid) = unsaid_of(&at, &read, &relations, known, targets) else {
                continue;
            };
            // A requires line takes what the lines above it state (`SYNTAX.md`),
            // so a line below that would say it is named, read as if above.
            let below = step
                .requires
                .iter()
                .skip_while(|o| o.line != req.line)
                .skip(1)
                .find(|o| {
                    let mut with = ClosureClaim::requires(step, req);
                    with.above.push(o);
                    with.read(known, targets, false).is_some_and(|read| {
                        unsaid_of(&with, &read, &relations, known, targets)
                            .is_none_or(|still| !still.same(&unsaid, known))
                    })
                });
            let said = unsaid.said(known);
            let message = match (below, &unsaid) {
                (Some(o), _) => format!(
                    "{}; the requires line {} below says it, and a requires line takes only what the lines above it state: move it above",
                    unsaid.told(known, "nothing above says"),
                    str::trim(o.fact.text())
                ),
                (None, Unsaid::Real(_)) => format!(
                    "{said}; a requires line by {} takes a membership from a requires line above it",
                    by.head
                ),
                (None, Unsaid::Nonzero(_)) => said,
            };
            report.say(&thm.path, req.line, message);
        }
    }
}

/// How the page writes a relation.
fn sign(rel: Rel) -> &'static str {
    match rel {
        Rel::Eq => "=",
        Rel::Ne => "≠",
        Rel::Lt => "<",
        Rel::Le => "≤",
        Rel::Gt => ">",
        Rel::Ge => "≥",
    }
}

/// Reports an atom of the claim or of `links` that nothing says is real
/// (`real_unsaid`).
fn report_unreal(
    report: &mut Report,
    thm: &Theorem,
    step: &Step,
    claim: &Node,
    links: &[Related],
    known: &Known,
    targets: &Targets,
) {
    let relations: Vec<Node> = std::iter::once(claim.clone())
        .chain(links.iter().map(|l| l.said.clone()))
        .collect();
    // A cited line says all it says, not only the relation the chain takes
    // from it: `δ ∈ ℝ. δ > 0.` says δ is real.
    let mut lines = relations[1..].to_vec();
    let mut line_of: Vec<usize> = (0..links.len()).collect();
    for (i, r) in step.just.refs.iter().enumerate() {
        for said in cited_says(step, r, known) {
            lines.push(said);
            line_of.push(i);
        }
    }
    let read = ClosureRead::new(claim.clone(), lines, line_of);
    // The cited lines are the orders the step links, so a membership is
    // taken from a requires line (`METHODS.md`, transitivity, antisymmetry).
    if let Some(said) =
        real_unsaid(&ClosureClaim::step(step), &read, &relations, known, targets)
    {
        report.say(
            &thm.path,
            step.just.line,
            format!(
                "{said}; {} takes a membership from a requires line",
                step.just.head
            ),
        );
    }
}

/// The two sides of an equation, an order or a disequality; none for
/// anything else.
fn relation_sides(node: &Node) -> Vec<&Node> {
    match (node.notation(), node.children.as_slice()) {
        (EQUALITY | ORDER, [a, b]) => vec![a, b],
        (LOGICAL_NOT, [inner]) => relation_sides(inner),
        _ => Vec::new(),
    }
}

/// Whether a sentence is an equation or a disequality, what `algebra`
/// combines.
fn algebra_relation(node: &Node) -> bool {
    match (node.notation(), node.children.as_slice()) {
        (EQUALITY, [_, _]) => true,
        (LOGICAL_NOT, [inner]) => inner.notation() == EQUALITY,
        _ => false,
    }
}

/// What a side of a relation `algebra` asks to be numbers: a pair's two
/// coordinates (`METHODS.md`, Pairs), or the side itself.
fn coordinates_of<'n>(side: &'n Node, targets: &Targets) -> Vec<&'n Node> {
    if term_of_node(side, targets).label() == Some("cop") {
        side.children.iter().collect()
    } else {
        vec![side]
    }
}

/// The two sides of an equation or a disequality; none for anything else.
fn sides_of(node: &Node) -> Vec<&Node> {
    match (node.notation(), node.children.as_slice()) {
        (EQUALITY, [a, b]) => vec![a, b],
        (LOGICAL_NOT, [inner]) => sides_of(inner),
        _ => Vec::new(),
    }
}

/// What `inequalities` claims holds (`METHODS.md`, inequalities): a step's
/// claim of one sentence follows by linear arithmetic from what the lines it
/// cites say and the bounds a membership among them implies
/// (`methods::inequalities::decide`), each read as `check_algebra_holds`
/// reads it; and a requires line's whose reason is `inequalities`.
pub fn check_inequalities_holds(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in &thm.steps {
        // A step with rows is its rows' (`check_inequality_rows`).
        if step.just.head.is(Method::Inequalities) && step.just.rows.is_empty() {
            let at = ClosureClaim::step(step);
            if !inequalities_hold(report, thm, &at, known, targets) {
                report.undecided(&thm.path, Method::Inequalities, step);
            }
        }
        for req in step.requires.iter().filter(|r| r.is(Method::Inequalities)) {
            let at = ClosureClaim::requires(step, req);
            if !inequalities_hold(report, thm, &at, known, targets) {
                report.undecided_requires(&thm.path, Method::Inequalities, step, req);
            }
        }
    }
}

/// A requires line of an algebra, arithmetic or inequalities step saying a
/// membership says it of a term the step combines (`SYNTAX.md`, requires):
/// one in its claim, in a line it cites, or in another of its requires
/// lines, which may ask it. A membership of a term found in none of them is
/// a line the step neither uses nor asks for.
pub fn check_requires_combined(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in &thm.steps {
        let head = &step.just.head;
        if !(head.is(Method::Algebra)
            || head.is(Method::Arithmetic)
            || head.is(Method::Inequalities))
        {
            continue;
        }
        let Some(read) = ClosureClaim::step(step).read(known, targets, true) else {
            continue;
        };
        let mut combined: Vec<Node> = vec![read.claimed];
        combined.extend(read.lines);
        combined.extend(known.whole(step, &step.claim));
        let scope = known.scope(step);
        combined.extend(
            step.just
                .refs
                .iter()
                .filter_map(|r| scope.get(r))
                .flat_map(|s| known.writes(s, &known.citing_step(step))),
        );
        let said: Vec<Option<Node>> = step
            .requires
            .iter()
            .map(|r| known.whole(step, &r.fact))
            .collect();
        for (i, req) in step.requires.iter().enumerate() {
            let Some(fact) = &said[i] else {
                continue;
            };
            let (MEMBERSHIP, [term, _]) = (fact.notation(), fact.children.as_slice())
            else {
                continue;
            };
            let others = said
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .filter_map(|(_, o)| o.as_ref());
            let found = combined
                .iter()
                .chain(others)
                .any(|tree| tree.walk().iter().any(|n| known.alike(n, term)));
            if !found {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of {} says {}, and the {} neither uses nor asks for it",
                        step.called(),
                        str::trim(req.fact.text()),
                        step.kind_word()
                    ),
                );
            }
        }
    }
}

/// How a closure method decides a claim (`algebra_holds` and the like):
/// whether it decided, reporting what it refuses.
type Decides = fn(&mut Report, &Theorem, &ClosureClaim, &Known, &Targets) -> bool;

/// A `let` saying what kind of number its name is shows it by its reason,
/// as a requires line of the step after it would (`SYNTAX.md`, a let with a
/// kind; `citations::check_kinds` for a reason citing an item): where the
/// reason is a method, the method decides `gcd(s, w) ∈ ℕ`, and a reason it
/// does not decide, or that leaves a hypothesis unsaid, is reported.
pub fn check_kind_methods(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for UnderLet {
        define: d,
        step: under,
    } in reasons_under_lets(thm, known)
    {
        let Some(shown) = under.requires.last() else {
            continue;
        };
        if shown.is(Method::Arithmetic) {
            if let Some(why) = arithmetic_unshown(&shown.fact, known, targets) {
                report.say(
                    &thm.path,
                    d.line,
                    format!(
                        "the reason under let {} does not show {}: arithmetic finds it {why}",
                        d.label,
                        str::trim(shown.fact.text())
                    ),
                );
            }
            continue;
        }
        let decides: Decides = if shown.is(Method::Membership) {
            membership_holds
        } else if shown.is(Method::Algebra) {
            algebra_holds
        } else if shown.is(Method::Inequalities) {
            inequalities_hold
        } else {
            continue;
        };
        let mut scratch = Report::default();
        let at = ClosureClaim::requires(&under, shown);
        let decided = decides(&mut scratch, thm, &at, known, targets);
        let why = match scratch.problems.first() {
            Some(problem) => problem.message.clone(),
            None if !decided => "its method does not decide it".to_string(),
            None => continue,
        };
        report.say(
            &thm.path,
            d.line,
            format!(
                "the reason under let {} does not show {}: {why}",
                d.label,
                str::trim(shown.fact.text())
            ),
        );
    }
}

/// A let saying what kind of number its name is, and the step below it
/// with the let's requires lines and then its reason as its requires lines,
/// which is how the reason is read (`SYNTAX.md`, a let with a kind). The
/// reason is the last.
pub struct UnderLet<'t> {
    pub define: &'t crate::corpus::DefineLine,
    pub step: Step,
}

/// The theorem's lets that say a kind, each with its reason read as a
/// requires line of the step after it (`UnderLet`); a let with no step
/// after it is reported by the reader.
pub fn reasons_under_lets<'t>(thm: &'t Theorem, known: &Known) -> Vec<UnderLet<'t>> {
    thm.defines
        .iter()
        .filter_map(|d| {
            let Ok(Some(kinded)) = d.kinded(&thm.path, &known.env.g.members) else {
                return None;
            };
            let after = thm.step_after(d.line)?;
            let reason = d.reason.as_ref()?;
            Some(UnderLet {
                define: d,
                step: reason.under(&d.label, after, kinded.shown.fact.clone()),
            })
        })
        .collect()
}

/// What a method step's lines are asked against: how its method decides,
/// and the defines of functions the theorem may apply.
struct CitesAsked<'a> {
    decides: Decides,
    functions: &'a [super::citations::Defined],
    library: &'a Library<'a>,
    targets: &'a Targets,
}

impl CitesAsked<'_> {
    /// Whether `step` holds citing `refs` in place of its lines: its method
    /// decides it with nothing refused, and each define it applies has its
    /// argument in its domain by what it cites (`check_define_domains`).
    fn holds_citing(
        &self,
        thm: &Theorem,
        step: &Step,
        refs: &[String],
        known: &Known,
    ) -> bool {
        let mut lighter = step.clone();
        lighter.just.refs = refs.to_vec();
        self.holds(thm, &lighter, known)
    }

    /// Whether `lighter`, a step with something of it taken away, holds:
    /// its method decides it with nothing refused, and each define it
    /// applies has its argument in its domain.
    fn holds(&self, thm: &Theorem, lighter: &Step, known: &Known) -> bool {
        let mut scratch = Report::default();
        let decided = (self.decides)(
            &mut scratch,
            thm,
            &ClosureClaim::step(lighter),
            known,
            self.targets,
        );
        decided
            && scratch.problems.is_empty()
            && super::citations::domains_unsaid(
                lighter,
                self.functions,
                known,
                self.library,
            )
            .is_empty()
    }
}

/// A step resting on a closure method uses each line it cites, as a step
/// citing an item does (`check_surplus`; `DATABASE.md`, a named thing doing
/// no work is an error): with the line taken away, the method no longer
/// decides the claim, or a hypothesis of it, an atom's membership, a
/// divisor's `≠ 0` or a define's argument in its domain, is left unsaid. A
/// step that does not hold with all its lines is reported where the method
/// is checked, and asked nothing here. A step with rows cites the one line
/// its first row is.
pub fn check_method_cites_used(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let functions = super::citations::defined_functions(
        &crate::corpus::proof::in_scope(thm, scopes),
    );
    for step in &thm.steps {
        let decides: Decides = match step.just.head.method() {
            Some(Method::Algebra) => algebra_holds,
            Some(Method::Inequalities) if step.just.rows.is_empty() => {
                inequalities_hold
            }
            Some(Method::Membership) => membership_holds,
            Some(Method::Inspection) => inspection_holds,
            _ => continue,
        };
        let asked = CitesAsked {
            decides,
            functions: &functions,
            library,
            targets: &library.targets,
        };
        let refs = &step.just.refs;
        if !asked.holds(thm, step, known) {
            continue;
        }
        let mut seen = BTreeSet::new();
        for r in refs.iter().filter(|r| seen.insert(r.as_str())) {
            let without: Vec<String> =
                refs.iter().filter(|x| *x != r).cloned().collect();
            // A define the step cites may be what reads the line it
            // contradicts, `contradicting 1` where line 1 says e ≠ 0 and the
            // claim says it of what e names.
            if reads_contradicted(step, &without, library, known) {
                continue;
            }
            if asked.holds_citing(thm, step, &without, known) {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!("step {} cites {r} and uses nothing it says", step.number),
                );
            }
        }
        // A requires line other than a membership, `x ≠ 0` or an order,
        // does work in the same sense; a membership is
        // `check_requires_combined`'s. A requires line rests on those above
        // it (`SYNTAX.md`), so only the last is asked here: one above it is
        // what the elaborator judges by what the lines below rest on.
        for (i, req) in step.requires.iter().enumerate() {
            let membership = known
                .whole(step, &req.fact)
                .is_some_and(|n| n.notation() == MEMBERSHIP);
            if i + 1 != step.requires.len() || membership {
                continue;
            }
            let mut lighter = step.clone();
            lighter.requires.remove(i);
            if asked.holds(thm, &lighter, known) {
                report.say(
                    &thm.path,
                    req.line,
                    format!(
                        "the requires line of {} says {}, and the {} neither uses nor asks for it",
                        step.called(),
                        str::trim(req.fact.text()),
                        step.kind_word()
                    ),
                );
            }
        }
    }
}

/// `check_inequalities_holds` of one claim; whether it was decided.
fn inequalities_hold(
    report: &mut Report,
    thm: &Theorem,
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> bool {
    let Some(mut read) = at.read(known, targets, false) else {
        return false;
    };
    read.read_at_member(known);
    let labels = FloatLabels::new(IndexMap::new());
    let implied: Vec<Term> = read
        .lines
        .iter()
        .flat_map(conjuncts)
        .flat_map(|part| implied_facts(&part, known.env, &known.sorts))
        .chain(read.member_implies(known))
        .map(|n| term_of_node(&n, targets))
        .collect();
    let cited: Vec<Term> = read
        .lines
        .iter()
        .map(|n| term_of_node(n, targets))
        .collect();
    let claimed = term_of_node(&read.claimed, targets);
    match inequalities::decide(&claimed, &cited, &implied, &labels) {
        Some(true) => {
            if let Some(said) = inequalities_unsaid(at, &read, known, targets) {
                report.say(&thm.path, at.line, at.said(said));
            }
            true
        }
        Some(false) => {
            let number = at.step.number.to_string();
            let said = inequalities::refusal(
                &at.claim.to_string(),
                &number,
                &claimed,
                &cited,
                &implied,
                &labels,
            );
            report.say(&thm.path, at.line, at.said(said));
            true
        }
        None => false,
    }
}

/// What `inspection` claims holds (`METHODS.md`, inspection): a claim about
/// sets listed in full, checked element by element against what the lines
/// the step cites say (`methods::inspection`), each sentence a kernel term.
/// One the facts show false is refused; one they settle neither way is left
/// to the build, and counted.
pub fn check_inspection_holds(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in &thm.steps {
        if !step.just.head.is(Method::Inspection) {
            continue;
        }
        // A claim that does not read is `check_formulas`'s to report.
        if known.whole(step, &step.claim).is_none() {
            continue;
        }
        if !inspection_holds(report, thm, &ClosureClaim::step(step), known, targets) {
            report.undecided(&thm.path, Method::Inspection, step);
        }
    }
}

/// `check_inspection_holds` of one claim, from the lines it cites; whether
/// it was decided.
fn inspection_holds(
    report: &mut Report,
    thm: &Theorem,
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> bool {
    let Some(claim) = known.whole(at.step, at.claim) else {
        return false;
    };
    let scope = known.scope(at.step);
    let cited: Vec<Term> = at
        .refs
        .iter()
        .filter_map(|r| scope.get(r))
        .flat_map(|stated| known.supplied(stated, &known.citing_step(at.step)))
        .map(|n| term_of_node(&n, targets))
        .collect();
    use crate::methods::inspection::{Facts, Inspected};
    let what = format!("step {} claims {}", at.step.number, known.print(&claim));
    match Facts::of(&cited).decide(&term_of_node(&claim, targets)) {
        Inspected::Holds => true,
        Inspected::Fails => {
            report.say(
                &thm.path,
                at.line,
                format!("{what}, which inspection of what it cites shows false"),
            );
            true
        }
        Inspected::Unsettled(why) => {
            report.say(&thm.path, at.line, format!("{what}, and {why}"));
            true
        }
        Inspected::Undecided => false,
    }
}

/// What `membership` claims holds (`METHODS.md`, membership): a step's claim
/// `t ∈ S`, or `for all k ∈ X, t ∈ S` at a member of X, and a requires
/// line's whose reason is `membership`, each decided by
/// `methods::membership::holds` from what the lines it cites say, the
/// requires lines above it, what a membership among them implies, and the
/// memberships the page says once.
pub fn check_membership_holds(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    for step in &thm.steps {
        if step.just.head.is(Method::Membership) {
            let at = ClosureClaim::step(step);
            // A claim of no shape the method decides is refused once, by
            // `check_membership_claims`, which says why.
            if !membership_holds(report, thm, &at, known, targets)
                && membership_claim_refused(step, known).is_none()
            {
                report.undecided(&thm.path, Method::Membership, step);
            }
        }
        for req in step.requires.iter().filter(|r| r.is(Method::Membership)) {
            let at = ClosureClaim::requires(step, req);
            if !membership_holds(report, thm, &at, known, targets) {
                report.undecided_requires(&thm.path, Method::Membership, step, req);
            }
        }
    }
}

/// The claims the `membership` method proves whose term is in its system
/// beside an equation a line they name says, each by the line its reason
/// is on (`CheckedTheorem::members_shown`): how the check found the term
/// there, which a backend proves the same way.
pub fn members_shown(
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) -> IndexMap<usize, super::record::PlaceShown> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        if step.just.head.is(Method::Membership) {
            let at = ClosureClaim::step(step);
            if let Some(shown) = member_beside(&at, known, targets) {
                out.insert(step.just.line, shown);
            }
        }
        for req in step.requires.iter().filter(|r| r.is(Method::Membership)) {
            let (at, Ok(by)) = (ClosureClaim::requires(step, req), &req.by) else {
                continue;
            };
            if let Some(shown) = member_beside(&at, known, targets) {
                out.insert(by.line, shown);
            }
        }
    }
    out
}

/// The claims `inspection` decides hold, a step's and each requires line's
/// whose reason is the method, each by the line its reason is on, with the
/// case that decided it (`CheckedTheorem::inspected`).
pub fn inspected(
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) -> IndexMap<usize, super::record::Inspection> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        if step.just.head.is(Method::Inspection) {
            if let Some(how) =
                inspection_case(&ClosureClaim::step(step), known, targets)
            {
                out.insert(step.just.line, how);
            }
        }
        for req in step.requires.iter().filter(|r| r.is(Method::Inspection)) {
            let (at, Ok(by)) = (ClosureClaim::requires(step, req), &req.by) else {
                continue;
            };
            if let Some(how) = inspection_case(&at, known, targets) {
                out.insert(by.line, how);
            }
        }
    }
    out
}

/// The case of `inspection` that decides one claim from the lines it
/// cites, as `inspection_holds` reads them; None where it does not hold.
fn inspection_case(
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> Option<super::record::Inspection> {
    use super::record::Inspection;
    use crate::methods::inspection::{Case, Facts};
    let claim = known.whole(at.step, at.claim)?;
    let scope = known.scope(at.step);
    let defined = known.citing_step(at.step);
    // Each cited sentence beside the reference it is read from.
    let mut cited: Vec<Term> = Vec::new();
    let mut from: Vec<&String> = Vec::new();
    for r in at.refs {
        let Some(stated) = scope.get(r) else {
            continue;
        };
        for n in known.supplied(stated, &defined) {
            cited.push(term_of_node(&n, targets));
            from.push(r);
        }
    }
    Some(
        match Facts::of(&cited).case(&term_of_node(&claim, targets))? {
            Case::OneOf { fact, range } => Inspection::OneOf {
                from: from.get(fact)?.to_string(),
                range,
            },
            Case::Prime => Inspection::Prime,
            Case::Empty => Inspection::Empty,
            Case::Member => Inspection::Member,
            Case::Size => Inspection::Size,
            Case::TakenSize => Inspection::TakenSize,
            Case::Taken => Inspection::Taken,
            Case::Other => Inspection::Other,
        },
    )
}

/// The parts each reason's lines put in a number system, by the line the
/// reason is on (`CheckedTheorem::held_by_lines`): of a step's claim and the
/// lines it names, and of each requires line and the lines its own reason
/// names, read as the `membership` method reads what a claim rests on
/// (`MembershipIn`, `methods::membership::held_otherwise`).
pub fn held_by_lines(
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) -> IndexMap<usize, Vec<super::record::HeldByLines>> {
    let mut out = IndexMap::new();
    for step in &thm.steps {
        let at = ClosureClaim::step(step);
        out.insert(step.just.line, held_at(&at, known, targets));
        for req in &step.requires {
            if let Ok(by) = &req.by {
                let at = ClosureClaim::requires(step, req);
                out.insert(by.line, held_at(&at, known, targets));
            }
        }
    }
    // The reason under a define that says a kind, read as the requires line
    // it is checked as, under the step after the define
    // (`citations::check_kinds`, `Reason::under`).
    for d in &thm.defines {
        let Ok(Some(kinded)) = d.kinded(&thm.path, &known.env.g.members) else {
            continue;
        };
        let (Some(after), Some(reason)) = (thm.step_after(d.line), d.reason.as_ref())
        else {
            continue;
        };
        let under = reason.under(&d.label, after, kinded.shown.fact.clone());
        let Some(req) = under.requires.last() else {
            continue;
        };
        if let Ok(by) = &req.by {
            let at = ClosureClaim::requires(&under, req);
            out.insert(by.line, held_at(&at, known, targets));
        }
    }
    out
}

/// The number systems a part may be asked in.
const HELD_IN: [System; 5] = [System::N, System::N0, System::Z, System::Q, System::R];

/// `held_by_lines` of one claim: every part of its terms and of its lines'
/// that those lines put in a system, once for each system, with how.
fn held_at(
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> Vec<super::record::HeldByLines> {
    use super::record::{HeldByLines, LinesHold};
    use methods_membership::HeldHow;
    let Some(read) = at.read(known, targets, true) else {
        return Vec::new();
    };
    let mut held = MembershipIn::of(at, &read, known);
    // A claim said of every member is read at a member, as
    // `membership_holds` decides it: its letter in the set's system.
    if let (FOR_ALL, [bound, set, _]) =
        (read.claimed.notation(), read.claimed.children.as_slice())
    {
        member_of(bound, set, &mut held.letters, &mut held.ranged);
    }
    let given = held.given(targets, known);
    let mut out: Vec<HeldByLines> = Vec::new();
    let mut seen: FxIndexSet<(crate::formula::ByShape, System)> = FxIndexSet::default();
    for part in std::iter::once(&read.claimed)
        .chain(&read.lines)
        .flat_map(|n| n.walk())
    {
        if part.notation() == NUMERAL {
            continue;
        }
        for system in HELD_IN {
            if !seen.insert((part.by_shape(), system)) {
                continue;
            }
            let by = match methods_membership::held_otherwise(&part, system, &given) {
                Some(HeldHow::Stated(line)) => LinesHold::Stated { line: line.clone() },
                Some(HeldHow::Beside(b)) => {
                    LinesHold::Beside(super::record::Besides::of(&b))
                }
                Some(HeldHow::Closed) => LinesHold::Closed,
                None => continue,
            };
            out.push(HeldByLines {
                term: part.clone(),
                system,
                by,
            });
        }
    }
    out
}

/// Of a claim `t ∈ S` the `membership` method proves, how t is in S where
/// an equation among what it rests on puts t beside a term in S
/// (`methods::membership::atom_held_by`); None where t is said, or the
/// claim is of another shape.
fn member_beside(
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> Option<super::record::PlaceShown> {
    use super::record::{PlaceShown, ShownBy};
    let read = at.read(known, targets, true)?;
    let mut held = MembershipIn::of(at, &read, known);
    // A claim said of every member is read at a member, as
    // `membership_holds` decides it.
    // The claim as the page writes it, no define written out.
    let as_page = match at.claim.sentences().as_slice() {
        [one] => known.read_as_written(one),
        _ => None,
    };
    let (claimed, written) = match (
        read.claimed.notation(),
        read.claimed.children.as_slice(),
        as_page,
    ) {
        (FOR_ALL, [bound, set, body], written) => {
            if !member_of(bound, set, &mut held.letters, &mut held.ranged) {
                return None;
            }
            let written =
                written.and_then(|w| match (w.notation(), w.children.as_slice()) {
                    (FOR_ALL, [_, _, b]) => Some(b.clone()),
                    _ => None,
                });
            (body.clone(), written)
        }
        (_, _, written) => (read.claimed.clone(), written),
    };
    let (MEMBERSHIP, [term, set]) = (claimed.notation(), claimed.children.as_slice())
    else {
        return None;
    };
    let system = (set.notation() == NUMBER_SYSTEMS)
        .then(|| System::of_sign(&set.text))
        .flatten()?;
    let given = held.given(targets, known);
    let shown = |by| {
        Some(PlaceShown {
            term: term.clone(),
            system,
            by,
        })
    };
    if let Some(methods_membership::Held::Beside(b)) =
        methods_membership::atom_held_by(term, system, &given)
    {
        return shown(ShownBy::Beside(super::record::Besides::of(&b)));
    }
    // A term a cited define writes out, read as its value.
    let as_written =
        written.and_then(|w| match (w.notation(), w.children.as_slice()) {
            (MEMBERSHIP, [t, _]) => Some(t.clone()),
            _ => None,
        });
    if as_written.is_some_and(|w| !known.alike(&w, term)) {
        return shown(ShownBy::Define {
            value: term.clone(),
        });
    }
    // A function's value by its type.
    if let Some(map) = methods_membership::value_typed_by(term, system, &given) {
        if let [_, point] = term.children.as_slice() {
            return shown(ShownBy::Typed {
                map: map.clone(),
                at: point.clone(),
            });
        }
    }
    None
}

/// `check_membership_holds` of one claim; whether it was decided.
fn membership_holds(
    report: &mut Report,
    thm: &Theorem,
    at: &ClosureClaim,
    known: &Known,
    targets: &Targets,
) -> bool {
    let Some(read) = at.read(known, targets, true) else {
        return false;
    };
    let mut held = MembershipIn::of(at, &read, known);
    // A claim said of every member is decided at a member.
    let mut claimed = read.claimed.clone();
    if let (FOR_ALL, [bound, set, body]) =
        (claimed.notation(), claimed.children.as_slice())
    {
        if !member_of(bound, set, &mut held.letters, &mut held.ranged) {
            return false;
        }
        claimed = body.clone();
    }
    let (MEMBERSHIP, [term, set]) = (claimed.notation(), claimed.children.as_slice())
    else {
        return false;
    };
    let Some(system) = (set.notation() == NUMBER_SYSTEMS)
        .then(|| System::of_sign(&set.text))
        .flatten()
    else {
        return false;
    };
    let given = held.given(targets, known);
    if !methods_membership::holds(term, system, &given) {
        let number = at.step.number.to_string();
        // The first part the claim is built from that nothing held says is
        // a number there, through a cited equation where one carries it, or
        // a divisor nothing says is not zero.
        let parts = methods_membership::Parts::of(term);
        let unsaid = methods_membership::unsaid_atom(term, system, &given)
            .map(|a| {
                format!(
                    ": nothing says {} ∈ {}, which it needs",
                    known.print(&a),
                    known.print(set)
                )
            })
            .or_else(|| {
                parts
                    .divisors
                    .iter()
                    .find_map(|d| methods_membership::unsaid_part(d, &given))
                    .map(|d| {
                        format!(
                            ": nothing says {} ≠ 0, which it needs to divide by it",
                            known.print(&d)
                        )
                    })
            })
            .unwrap_or_default();
        let said = format!(
            "{} is not built from what step {number} cites{unsaid}",
            at.claim
        );
        report.say(&thm.path, at.line, at.said(said));
    }
    true
}

/// What a closure claim's terms are numbers by (`methods::membership`): the
/// lines it cites, the requires lines it rests on, each part of them and
/// what a membership among them implies; the letters the page puts in a
/// number system once, the member a step said of every member speaks of,
/// and the function types in scope.
struct MembershipIn {
    facts: Vec<Node>,
    letters: crate::citing::Introduced,
    ranged: IndexMap<String, methods_membership::Range>,
    typed: Vec<Node>,
    /// The function types in scope, which a sum's terms may use.
    in_sums: Vec<Node>,
}

impl MembershipIn {
    fn of(at: &ClosureClaim, read: &ClosureRead, known: &Known) -> MembershipIn {
        let mut letters = super::library::introduced(known, at.step);
        // A step's requires lines are among its facts in (`METHODS.md`), a
        // requires line's are the lines above it, which `read` holds.
        let mut lines = read.lines.clone();
        if at.requires.is_none() {
            let defined = known.citing_step(at.step);
            for r in &at.step.requires {
                lines.extend(
                    r.fact
                        .sentences()
                        .iter()
                        .filter_map(|s| known.read_citing(s, &defined)),
                );
            }
        }
        // A step said of every member in one line, and its requires lines,
        // speak of the member (`SYNTAX.md`), which the step's claim puts in
        // its set.
        let mut ranged = IndexMap::new();
        if at.step.openers.is_empty() {
            if let Some(member) = known.step_member(at.step) {
                if let (MEMBERSHIP, [bound, set]) =
                    (member.notation(), member.children.as_slice())
                {
                    member_of(bound, set, &mut letters, &mut ranged);
                }
            }
        }
        let mut facts: Vec<Node> = lines.iter().flat_map(conjuncts).collect();
        let implied: Vec<Node> = facts
            .iter()
            .flat_map(|f| implied_facts(f, known.env, &known.sorts))
            .collect();
        facts.extend(implied);
        for f in &facts {
            if let (MEMBERSHIP, [name, set]) = (f.notation(), f.children.as_slice()) {
                if let (true, Some(system)) =
                    (name.is_name(), System::of_sign(&set.text))
                {
                    letters.entry(name.text.to_string()).or_insert(system);
                }
            }
        }
        // A function's type is cited for its values (`READERS.md`): the
        // types among what the claim rests on, and none merely in scope.
        let typed: Vec<Node> = facts
            .iter()
            .filter(|f| types_a_function(f))
            .cloned()
            .collect();
        MembershipIn {
            facts,
            letters,
            ranged,
            typed,
            in_sums: super::library::typed_in_scope(known, at.step),
        }
    }

    /// What the decider reads.
    fn given<'a>(
        &'a self,
        targets: &'a Targets,
        known: &'a Known,
    ) -> methods_membership::Facts<'a> {
        methods_membership::Facts {
            facts: &self.facts,
            letters: self.letters.clone(),
            ranged: self.ranged.clone(),
            typed: &self.typed,
            in_sums: &self.in_sums,
            targets,
            ctx: known.ctx,
        }
    }
}

/// The letter a "for all" binds, put in the number system its set lies in,
/// a number system, a range or an interval, and where the set is a range,
/// as running over it. Any other set, ℝ ∖ {0}, puts the letter in no
/// system: what the member is is said by the step's requires lines
/// (`SYNTAX.md`, a step said of every member). False where the letter is
/// no name.
fn member_of(
    bound: &Node,
    set: &Node,
    letters: &mut crate::citing::Introduced,
    ranged: &mut IndexMap<String, methods_membership::Range>,
) -> bool {
    if !bound.is_name() {
        return false;
    }
    let system = match set.notation() {
        NUMBER_SYSTEMS => System::of_sign(&set.text),
        INTEGER_RANGE => crate::citing::range_system(set),
        _ => match crate::citing::interval_system(set, letters) {
            Some(system) => Some(system),
            None => return true,
        },
    };
    let Some(system) = system else {
        return false;
    };
    letters.insert(bound.text.to_string(), system);
    if let (INTEGER_RANGE, [start, end]) = (set.notation(), set.children.as_slice()) {
        ranged.insert(
            bound.text.to_string(),
            methods_membership::Range {
                start: start.clone(),
                end: end.clone(),
            },
        );
    }
    true
}

/// A claim a closure method is asked of: a step's own, or a requires line's
/// read as the step it would be, with the requires lines above it among what
/// it cites (`ELABORATION.md`, R2).
struct ClosureClaim<'s> {
    /// The step the claim is made at.
    step: &'s Step,
    claim: &'s Written,
    refs: &'s [String],
    /// The requires lines above a requires line, whose facts it rests on.
    above: Vec<&'s crate::corpus::proof::Requires>,
    /// Where a refusal is said.
    line: usize,
    /// The requires line, where the claim is one.
    requires: Option<&'s crate::corpus::proof::Requires>,
}

/// A closure claim and what it cites, read.
struct ClosureRead {
    claimed: Node,
    /// The claim's sentences, read, whose conjunction is `claimed`; the
    /// body of a claim read at a member.
    sentences: Vec<Node>,
    lines: Vec<Node>,
    /// The page's line each of `lines` is of: the cited line by its place
    /// among the references, and a requires line above after them, by its
    /// place among those.
    line_of: Vec<usize>,
    /// Where the claim is read at a member (`read_at_member`), the membership
    /// its "for all" gives the member.
    member: Option<Node>,
}

impl ClosureRead {
    /// A claim and the lines it is read from, as it stands, not at a member.
    fn new(claimed: Node, lines: Vec<Node>, line_of: Vec<usize>) -> ClosureRead {
        ClosureRead {
            sentences: vec![claimed.clone()],
            claimed,
            lines,
            line_of,
            member: None,
        }
    }

    /// A claim said of every member, read at a member (`SYNTAX.md`, a step
    /// said of every member), as a citation's is (`claimed_member`): the
    /// body in the claim's place, and the membership its "for all" gives
    /// the member, kept as `member`. The claim as it stands where it says
    /// no "for all".
    fn read_at_member(&mut self, known: &Known) {
        if let Some((member, body)) = claimed_member(&self.claimed, known.env.g) {
            self.member = Some(member);
            self.sentences = vec![body.clone()];
            self.claimed = body;
        }
    }

    /// What the member's membership implies, `i ≥ 1` of i ∈ ℕ, where the
    /// claim is read at a member.
    fn member_implies(&self, known: &Known) -> Vec<Node> {
        self.member
            .iter()
            .flat_map(|m| implied_facts(m, known.env, &known.sorts))
            .collect()
    }
}

impl<'s> ClosureClaim<'s> {
    fn step(step: &'s Step) -> ClosureClaim<'s> {
        ClosureClaim {
            step,
            claim: &step.claim,
            refs: &step.just.refs,
            above: Vec::new(),
            line: step.just.line,
            requires: None,
        }
    }

    fn requires(
        step: &'s Step,
        req: &'s crate::corpus::proof::Requires,
    ) -> ClosureClaim<'s> {
        ClosureClaim {
            step,
            claim: &req.fact,
            refs: req.lines(),
            above: step.requires_above(req.line).collect(),
            line: req.line,
            requires: Some(req),
        }
    }

    /// The claim and what it cites, read with the defines it cites written
    /// out; None for a claim of more than one sentence, or one that does
    /// not read, which `check_formulas` reports. Of the requires lines
    /// above, a disequality is left out where `differing` does not keep it:
    /// two terms differing is taken only from a line the claim cites
    /// (`METHODS.md`), as the build reads it (`as_a_step`), and `membership`
    /// reads a divisor's `≠ 0` above it.
    fn read(
        &self,
        known: &Known,
        targets: &Targets,
        differing: bool,
    ) -> Option<ClosureRead> {
        // The defines written out are those the claim cites, `refs`: the
        // step's own, or fewer where a check asks what a line does.
        let item = match self.requires {
            Some(_) => None,
            None => self.step.just.cited_item().map(|c| self.step.just.item(&c)),
        };
        let defined = known.citing_item(self.refs, item.as_deref());
        // A claim of several sentences is their conjunction (`SYNTAX.md`),
        // as `0 ≤ e. e ≤ 9.` is `0 ≤ e and e ≤ 9`.
        let sentences: Vec<Node> = self
            .claim
            .sentences()
            .iter()
            .map(|s| known.read_citing(s, &defined))
            .collect::<Option<_>>()?;
        let claimed = conjoined(known.env.g, sentences.clone())?;
        let scope = known.scope(self.step);
        let mut lines: Vec<Node> = Vec::new();
        let mut line_of: Vec<usize> = Vec::new();
        for (i, r) in self.refs.iter().enumerate() {
            let Some(written) = scope.get(r) else {
                continue;
            };
            for said in known.supplied(written, &defined) {
                lines.push(said);
                line_of.push(i);
            }
        }
        let labels = FloatLabels::new(IndexMap::new());
        for (k, o) in self.above.iter().enumerate() {
            for s in o.fact.sentences() {
                let Some(said) = known.read_citing(&s, &defined) else {
                    continue;
                };
                let apart = linear::fact(&term_of_node(&said, targets), &labels)
                    .is_some_and(|f| f.how == linear::How::Ne);
                if differing || !apart {
                    lines.push(said);
                    line_of.push(self.refs.len() + k);
                }
            }
        }
        Some(ClosureRead {
            sentences,
            ..ClosureRead::new(claimed, lines, line_of)
        })
    }

    /// A refusal as it is said here: of the requires line, where the claim
    /// is one.
    fn said(&self, refusal: String) -> String {
        match self.requires {
            Some(req) => format!(
                "the requires line {} of {}, read as a step citing what it cites: {refusal}",
                req.fact,
                self.step.called()
            ),
            None => refusal,
        }
    }
}

/// A term a decider names, in the page's words: the part of what it read
/// that makes that term (`term_of_node`), printed.
fn printed(
    term: &Term,
    read: &[&Node],
    known: &Known,
    targets: &Targets,
    labels: &FloatLabels,
) -> String {
    let want = term.rpn(labels);
    read.iter()
        .flat_map(|n| n.walk())
        .find(|part| term_of_node(part, targets).rpn(labels) == want)
        .map(|part| known.print(&part))
        .unwrap_or_else(|| want.to_string())
}

/// What working out a fact `arithmetic` claims finds.
pub(super) enum Worked {
    Holds,
    /// It is false, or cannot be worked out, and why.
    Fails(String),
    /// A sentence of it is no fact the decider works out, which the build
    /// is left to.
    Undecided,
}

/// A fact `arithmetic` claims, each sentence worked out
/// (`methods::field::decide_closed`). A sentence that does not read is
/// `check_formulas`'s to report.
pub(super) fn arithmetic_worked(
    written: &Written,
    known: &Known,
    targets: &Targets,
) -> Worked {
    let mut out = Worked::Holds;
    // "A. B." and "A and B" are one claim (SYNTAX.md), so each sentence is
    // taken apart at its "and"s and every fact worked out alone.
    let facts = written
        .sentences()
        .iter()
        .filter_map(|s| known.read_as_written(s))
        .flat_map(|n| conjuncts(&n))
        .collect::<Vec<_>>();
    for node in facts {
        let node = written_out(&node, known);
        match decide_closed(&term_of_node(&node, targets)) {
            Built(Verdict::Holds(false)) => {
                return Worked::Fails("is false".to_string())
            }
            Built(Verdict::Unworked(why)) => return Worked::Fails(why.to_string()),
            Built(Verdict::Holds(true)) => {}
            Declined(_) => out = Worked::Undecided,
        }
    }
    out
}

/// What working out a fact `real arithmetic` claims finds.
pub(super) enum RealWorked {
    Holds,
    /// It is false, or a part of it has no value, and why.
    Fails(String),
    /// Its sides have values, and the relation between them is not one
    /// real arithmetic decides, and why. It is not reported as false.
    Undecided(String),
    /// A sentence of it is not built from numerals, square roots, π, e and
    /// logarithms.
    Unread,
    /// It holds and takes nothing beyond what `arithmetic` works out, so it
    /// is `arithmetic`'s.
    NumeralsAlone,
}

/// A fact `real arithmetic` claims, each sentence worked out
/// (`methods::reals::decide_closed`). A sentence that does not read is
/// `check_formulas`'s to report.
pub(super) fn real_worked(
    written: &Written,
    known: &Known,
    targets: &Targets,
) -> RealWorked {
    // Each sentence taken apart at its "and"s, as `arithmetic_worked` does.
    let nodes: Vec<Node> = written
        .sentences()
        .iter()
        .filter_map(|s| known.read_as_written(s))
        .flat_map(|n| conjuncts(&n))
        .collect();
    real_worked_of(&nodes, known, targets)
}

/// A sentence as `real arithmetic` reads it: as `term_of_node` does, with
/// each library function the theorem imports, and gives no meaning of its
/// own, built out of what it builds, as the build reads it.
fn real_term(node: &Node, known: &Known, targets: &Targets) -> Term {
    let library = |name: &str| library_named(name, known);
    term_of_node_reading(&written_out(node, known), targets, &library)
}

/// Whether `name` is a library function in the theorem: imported, and not a
/// name its `let` lines or `obtain` steps introduce (`introduced`). The
/// settled sorts hold a library function's name with the library's sort, so
/// they do not tell the two apart; a define's name is one letter, which no
/// library function's is.
fn library_named(name: &str, known: &Known) -> bool {
    known.sorts.imported.contains(name) && !introduced(known.thm, known).contains(name)
}

/// The pieces two terms of a link differ in, into `out`, each closed as
/// `real arithmetic` reads one: no name in it but a library function's, ln
/// in ln(2). False where a piece they differ in has a letter of the proof's
/// in it, as `cos(x)` against `cos(y)`.
fn real_pieces(one: &Node, other: &Node, known: &Known, out: &mut Vec<Piece>) -> bool {
    if known.alike(one, other) {
        return true;
    }
    let closed = |n: &Node| n.names().iter().all(|name| library_named(name, known));
    if closed(one) && closed(other) {
        out.push(Piece {
            was: one.clone(),
            now: other.clone(),
        });
        return true;
    }
    one.notation() == other.notation()
        && one.text == other.text
        && one.children.len() == other.children.len()
        && one
            .children
            .iter()
            .zip(&other.children)
            .all(|(a, b)| real_pieces(a, b, known, out))
}

/// Each sentence of a fact as `real arithmetic` reads it (`real_term`),
/// taken apart at its "and"s as `arithmetic_worked` does; None where one
/// does not read.
fn real_terms(
    written: &Written,
    known: &Known,
    targets: &Targets,
) -> Option<Vec<Term>> {
    let read: Option<Vec<Node>> = written
        .sentences()
        .iter()
        .map(|s| known.read_as_written(s))
        .collect();
    Some(
        read?
            .iter()
            .flat_map(conjuncts)
            .map(|n| real_term(&n, known, targets))
            .collect(),
    )
}

/// Whether a fact holds a square root, π, e, a logarithm or an
/// exponential, which `real arithmetic` works out and `arithmetic` does not
/// (`reals::beyond_arithmetic`).
fn beyond_arithmetic(written: &Written, known: &Known, targets: &Targets) -> bool {
    real_terms(written, known, targets)
        .is_some_and(|terms| terms.iter().any(reals::beyond_arithmetic))
}

/// `real_worked` of sentences already read.
fn real_worked_of(nodes: &[Node], known: &Known, targets: &Targets) -> RealWorked {
    use crate::methods::surds::Verdict as Surd;
    let mut out = RealWorked::Holds;
    let mut beyond = false;
    for node in nodes {
        let term = real_term(node, known, targets);
        beyond |= reals::beyond_arithmetic(&term);
        match reals::decide_closed(&term) {
            Built(Surd::Holds(false)) => {
                return RealWorked::Fails("is false".to_string())
            }
            Built(Surd::Unworked(why)) => return RealWorked::Fails(why.to_string()),
            Built(Surd::Undecided(why)) => {
                return RealWorked::Undecided(why.to_string())
            }
            Built(Surd::Holds(true)) => {}
            Declined(_) => out = RealWorked::Unread,
        }
    }
    match out {
        RealWorked::Holds if !beyond => RealWorked::NumeralsAlone,
        out => out,
    }
}

/// Why `real arithmetic` does not show a fact, or None where it holds:
/// what is said after "which".
fn real_unshown(worked: RealWorked) -> Option<String> {
    match worked {
        RealWorked::Holds => None,
        RealWorked::Fails(why) => Some(why),
        RealWorked::Undecided(why) => Some(format!("{why}{}", reals::NOT_DECIDED_HERE)),
        RealWorked::Unread => Some(reals::UNREAD.to_string()),
        RealWorked::NumeralsAlone => Some(
            "takes no square root, π, e, logarithm or exponential; a claim of numerals alone cites arithmetic"
                .to_string(),
        ),
    }
}

/// What `real arithmetic` claims holds when it is worked out (`METHODS.md`,
/// real arithmetic): a step's claim and a requires line's fact are decided
/// (`methods::surds::decide_closed`), and one that is false, has a part with
/// no value, states a relation the method does not decide, or takes no
/// square root, is reported.
pub fn check_real_arithmetic_holds(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    let shown = |fact: &Written| match real_worked(fact, known, targets) {
        RealWorked::Unread => Shown::Unread(reals::UNREAD.to_string()),
        worked => real_unshown(worked).map_or(Shown::Holds, Shown::Unshown),
    };
    for step in &thm.steps {
        check_shown_by(report, thm, step, Method::RealArithmetic, &shown);
        let just = &step.just;
        if let (Some(Source::RealArithmetic), Some(equation)) =
            (&just.source, &just.equation)
        {
            if let Some(why) = real_unshown(real_worked(equation, known, targets)) {
                report.say(
                    &thm.path,
                    just.line,
                    format!(
                        "step {} takes {equation} from real arithmetic, which {why}",
                        step.number
                    ),
                );
            }
        }
        // A link naming `real arithmetic` is closed, and worked out whole.
        for link in chain_links(just, &thm.path) {
            if link.line.cite != "real arithmetic" {
                continue;
            }
            // A link that does not read is the elaborator's to report.
            let Some(claim) = link.claim(known) else {
                continue;
            };
            // A library function's name, ln in ln(2), is no letter.
            let closed = claim.names().iter().all(|name| library_named(name, known));
            let why = if closed {
                real_unshown(real_worked_of(&[claim], known, targets))
            } else {
                // A link whose terms have letters changes closed pieces
                // alone, each worked out, as one naming arithmetic does.
                let mut pieces = Vec::new();
                let split = match (claim.notation(), claim.children.as_slice()) {
                    (EQUALITY, [one, other]) => {
                        real_pieces(one, other, known, &mut pieces)
                    }
                    _ => false,
                };
                if split {
                    pieces.into_iter().find_map(|Piece { was, now }| {
                        let piece = made(known.env.g, EQUALS, vec![was, now]);
                        real_unshown(real_worked_of(&[piece], known, targets))
                    })
                } else {
                    Some(
                        "changes something with a letter in it; a link may name real arithmetic where only closed pieces change, and any other cites the numbered step that states it"
                            .to_string(),
                    )
                }
            };
            if let Some(why) = why {
                report.say(
                    &thm.path,
                    link.line.line,
                    format!(
                        "a link of step {} names real arithmetic for {}, which {why}",
                        step.number,
                        link.line.quoted(&link.from)
                    ),
                );
            }
        }
    }
}

/// A closed claim `real arithmetic` decides cites it, as one `arithmetic`
/// works out cites arithmetic (`check_closed_by_arithmetic`): asked of a
/// step and each requires line giving `algebra` or `inequalities` for a
/// claim that holds a square root, π, e or a logarithm and that real
/// arithmetic finds true or false. One it does not decide, π = e, stays
/// theirs, and so does an order, which `inequalities` may prove from what
/// it cites of a root or an atom whether or not real arithmetic decides it.
pub fn check_closed_by_real_arithmetic(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    use crate::methods::surds::Verdict as Surd;
    let decided = |written: &Written| {
        let terms = real_terms(written, known, targets)?;
        if !terms.iter().any(reals::beyond_arithmetic)
            || terms.iter().any(reals::is_order)
        {
            return None;
        }
        let mut holds = true;
        for t in &terms {
            let Built(Surd::Holds(this)) = reals::decide_closed(t) else {
                return None;
            };
            holds &= this;
        }
        Some(holds)
    };
    check_closed_by(report, thm, Method::RealArithmetic, &decided);
}

/// The most terms a sum or product over a range of numerals is written out
/// to; one over more is left as it is, and `arithmetic` does not decide it.
const WRITTEN_OUT: u64 = 1000;

/// `node` with each product and sum over a range of numerals written out as
/// its terms, `∏(k ∈ {0, …, 2}) (5 − k)` as `(5 − 0)·(5 − 1)·(5 − 2)`,
/// which `arithmetic` works out as it works any product (`METHODS.md`,
/// arithmetic).
fn written_out(node: &Node, known: &Known) -> Node {
    let children: Vec<Node> = node
        .children
        .iter()
        .map(|c| written_out(c, known))
        .collect();
    let here = node.with_children(children);
    let (index, start, end, body, joined) =
        match (here.notation(), here.children.as_slice()) {
            (PRODUCT_OVER, [index, range, body]) => match range.children.as_slice() {
                [start, end] if range.notation() == INTEGER_RANGE => {
                    (index, start, end, body, TIMES)
                }
                _ => return here,
            },
            (SUM, [index, start, end, body]) => (index, start, end, body, PLUS),
            (PRODUCT, [index, start, end, body]) => (index, start, end, body, TIMES),
            _ => return here,
        };
    let bound = |n: &Node| {
        (n.notation() == NUMERAL)
            .then(|| n.text.parse::<u64>().ok())
            .flatten()
    };
    let (Some(from), Some(to)) = (bound(start), bound(end)) else {
        return here;
    };
    if !index.is_name() || from > to || to - from >= WRITTEN_OUT {
        return here;
    }
    let g = known.env.g;
    let at = |k: u64| {
        let put = Binding::from([(index.text, numeral(&k.to_string()))]);
        crate::matching::substitute_apart(body, &put, known.ctx)
    };
    (from + 1..=to).fold(at(from), |acc, k| made(g, joined, vec![acc, at(k)]))
}

/// `arithmetic` stands in for a line only where the fact is numerals alone.
///
/// A `substitute` may take its equation from `arithmetic`, and a chain link
/// may give `arithmetic` as its reason, because a claim with no letter in it
/// gives a reader nothing to check but working it out. One with a letter has
/// something to check, and is a numbered step of its own. A link whose terms
/// have letters but change only where they have none uses a fact of numerals
/// alone (`changed_closed`). `SYNTAX.md` has the rule.
pub fn check_closed_arithmetic(report: &mut Report, thm: &Theorem, known: &Known) {
    // A sentence that does not read is `check_formulas`'s to report.
    let closed = |written: &Written| -> bool {
        written.sentences().iter().all(|s| {
            known
                .read_as_written(s)
                .is_none_or(|n| n.names().is_empty())
        })
    };
    for step in &thm.steps {
        let just = &step.just;
        if let (Some(Source::Arithmetic), Some(equation)) =
            (&just.source, &just.equation)
        {
            if !closed(equation) {
                report.say(
                    &thm.path,
                    just.line,
                    format!(
                        "step {} takes {equation} from arithmetic, and it has a letter in it; a fact with a letter is a numbered step of its own",
                        step.number
                    ),
                );
            }
        }
        for link in chain_links(just, &thm.path) {
            if link.line.cite != "arithmetic" {
                continue;
            }
            // A link that does not read is the elaborator's to report.
            let Some(claim) = link.claim(known) else {
                continue;
            };
            // An order is worked out of numerals alone: one relating terms
            // with letters in them is inequalities', which a step of its own
            // shows and the link cites.
            if !claim.names().is_empty() && claim.notation() == ORDER {
                report.say(
                    &thm.path,
                    link.line.line,
                    format!(
                        "a link of step {} names arithmetic for {}, an order of terms with letters in them, which arithmetic does not work out; a step showing it by inequalities is cited instead",
                        step.number,
                        link.line.quoted(&link.from)
                    ),
                );
                continue;
            }
            if !claim.names().is_empty() && !changed_closed(&link, known) {
                report.say(
                    &thm.path,
                    link.line.line,
                    format!(
                        "a link of step {} names arithmetic for {}, which changes something with a letter in it; a link may name arithmetic where only pieces of numerals alone change, and any other cites the numbered step that states it",
                        step.number,
                        link.line.quoted(&link.from)
                    ),
                );
            }
        }
    }
}

/// Whether `written` holds, where `arithmetic` works out each of its
/// sentences (`methods::field::decide_closed`): built from numerals by the
/// operations it reads, and a relation it decides. √2·√2 = 2 has no letter
/// and is not one, nor is 1 + i·0 = 1, nor |{1, …, 23}| = 23. A sentence
/// that does not read is `check_formulas`'s to report, and is none.
fn arithmetic_works_out(
    written: &Written,
    known: &Known,
    targets: &Targets,
) -> Option<bool> {
    let mut holds = true;
    for s in written.sentences().iter() {
        let n = known.read_as_written(s)?;
        let term = term_of_node(&written_out(&n, known), targets);
        let Built(Verdict::Holds(this)) = decide_closed(&term) else {
            return None;
        };
        holds &= this;
    }
    Some(holds)
}

/// A claim `arithmetic` can work out cites it, whatever relation it states:
/// `algebra` and `inequalities` combine what a step says of its letters and
/// constants, and a claim arithmetic works out gives a reader nothing to
/// check but working it out (`METHODS.md`, arithmetic). A claim with no
/// letter that it cannot work out, √2·√2 = 2, is theirs. Asked of a step
/// and of each requires line.
pub fn check_closed_by_arithmetic(
    report: &mut Report,
    thm: &Theorem,
    known: &Known,
    targets: &Targets,
) {
    let worked = |written: &Written| arithmetic_works_out(written, known, targets);
    check_closed_by(report, thm, Method::Arithmetic, &worked);
}

/// `membership` claims that a term is in a number system, and nothing else
/// (`METHODS.md`), or that every member of a set has a term in one.
pub fn check_membership_claims(report: &mut Report, thm: &Theorem, known: &Known) {
    for step in &thm.steps {
        if !step.just.head.is(Method::Membership) {
            continue;
        }
        if let Some(why) = membership_claim_refused(step, known) {
            report.say(&thm.path, step.just.line, why);
        }
    }
}

/// Why a `membership` step's claim is none the method makes, or None where
/// it is one, or does not read (`check_formulas` says so). One line, one
/// step: a membership step says one term is in a number system, and two,
/// as sentences or joined by "and", are two steps.
fn membership_claim_refused(step: &Step, known: &Known) -> Option<String> {
    fn says_membership(node: &Node) -> bool {
        if node.notation() == FOR_ALL && node.children.len() == 3 {
            return says_membership(&node.children[2]);
        }
        node.notation() == MEMBERSHIP
            && node.children.len() == 2
            && node.children[1].notation() == NUMBER_SYSTEMS
    }
    let many = |count: usize| {
        format!(
            "step {} claims {count} sentences by membership, which says one term is in a number system; each is a step of its own",
            step.number
        )
    };
    let sentences = step.claim.sentences();
    if sentences.len() > 1 {
        return Some(many(sentences.len()));
    }
    for sentence in sentences {
        let Ok(node) = known.parse(&sentence) else {
            continue;
        };
        let joined = conjuncts(&node).len();
        if joined > 1 {
            return Some(many(joined));
        }
        if !says_membership(&node) {
            return Some(format!(
                "step {} names membership for {sentence}, which says no term is in a number system",
                step.number
            ));
        }
    }
    None
}

/// The labels of the defines a theorem's links may cite: its own, its
/// file's and those its file imports.
fn define_labels(thm: &Theorem, scopes: &[FileScope]) -> BTreeSet<String> {
    crate::corpus::proof::in_scope(thm, scopes)
        .into_iter()
        .filter_map(|d| d.label)
        .collect()
}

/// How the two sides of a link citing a define meet once the define is
/// written out (`Known::alike_how`): Some(None) where they do not; None
/// where the link does not read or is no equation.
fn define_link_meeting(link: &Link, known: &Known) -> Option<Option<Meeting>> {
    let claim = link.claim(known)?;
    let cite = &link.line.cite;
    let written = known.as_cited(&claim, &known.citing(std::slice::from_ref(cite)));
    let (one, other) = equation_sides(&written)?;
    Some(known.alike_how(one, other))
}

/// The two sides of an equation, read under each "for all" it stands in:
/// `A` and `B` of `for all x ∈ S, A = B`. None for a statement of another
/// shape.
fn equation_sides(statement: &Node) -> Option<(&Node, &Node)> {
    match (statement.notation(), statement.children.as_slice()) {
        (EQUALITY, [one, other]) => Some((one, other)),
        (FOR_ALL, [_, _, body]) => equation_sides(body),
        _ => None,
    }
}

/// How each link citing a define, and each step whose reason is defines it
/// names, meets the defines written out: the two sides of the equation it
/// claims, a "for all"'s at its body, or None where they do not meet; by the
/// link's line or the line of the step's reason
/// (`CheckedTheorem::define_links`).
pub fn define_link_meetings(
    thm: &Theorem,
    known: &Known,
) -> IndexMap<usize, Option<Meeting>> {
    let defines = define_labels(thm, known.env.scopes);
    let mut out: IndexMap<usize, Option<Meeting>> = thm
        .steps
        .iter()
        .flat_map(|step| chain_links(&step.just, &thm.path))
        .filter(|link| defines.contains(link.line.cite.as_str()))
        .filter_map(|link| Some((link.line.line, define_link_meeting(&link, known)?)))
        .collect();
    for step in thm.steps.iter().filter(|s| s.just.head == Head::Define) {
        let Some(claim) = known.whole(step, &step.claim) else {
            continue;
        };
        let cited: Vec<String> = step
            .just
            .refs
            .iter()
            .filter(|r| defines.contains(r.as_str()))
            .cloned()
            .collect();
        let written = known.as_cited(&claim, &known.citing(&cited));
        if let Some((one, other)) = equation_sides(&written) {
            out.insert(step.just.line, known.alike_how(one, other));
        }
    }
    out
}

/// Where in the line each calculation link cites the link stands, by the
/// link's line (`CheckedTheorem::link_places`): the sentence or part of one
/// that says it, as `check_chain_links` finds it, placed as a citation's
/// facts are (`FirstAt`), and which way the link faces it
/// (`CheckedTheorem::link_facings`). None for a link citing a define,
/// arithmetic, or a line it finds nothing in to place.
pub fn link_places(thm: &Theorem, library: &Library, known: &Known) -> LinkPlaces {
    let defines = define_labels(thm, known.env.scopes);
    let mut out = LinkPlaces::default();
    for step in &thm.steps {
        let scope = known.scope(step);
        for link in chain_links(&step.just, &thm.path) {
            let cite = &link.line.cite;
            if defines.contains(cite.as_str()) || cite == "arithmetic" {
                continue;
            }
            let Some(stated) = scope.get(cite) else {
                continue;
            };
            let Some(reading) = link_reading(&link, step, known, library) else {
                continue;
            };
            let own = known.sentence_count(stated);
            // A link read off a chain, a = c of a = b = c, stands in the
            // sentence the chain is, and is the pair it reads.
            let placed = reading.at.and_then(|k| {
                let s = &reading.says[k];
                match s.from {
                    SaidFrom::Pair(sentence) => Some(crate::checker::record::FirstAt {
                        line: cite.to_string(),
                        sentence: Some(sentence),
                        part: None,
                        written: s.written.clone(),
                        implied: None,
                    }),
                    _ => super::citations::placed(cite, s, &reading.says, own),
                }
            });
            if let Some(at) = placed {
                // How the line as written met the link, where not as written.
                if let Some(met) = known
                    .alike_how(&reading.said, &at.written)
                    .filter(|m| !m.as_written())
                {
                    out.meetings.insert(link.line.line, met);
                }
                out.places.insert(link.line.line, at);
            }
            let facing = reading.at.and_then(|k| {
                super::citations::facing_of(
                    &reading.says[k].cited,
                    &reading.said,
                    known,
                )
            });
            if let Some(facing) = facing {
                out.facings.insert(link.line.line, facing);
            }
        }
    }
    out
}

/// Where each calculation link citing a line stands in it, and which way it
/// faces it, by the link's line (`link_places`).
#[derive(Default)]
pub struct LinkPlaces {
    pub places: IndexMap<usize, crate::checker::record::FirstAt>,
    pub facings: IndexMap<usize, crate::checker::record::Facing>,
    /// How the line met the link, where not as written.
    pub meetings: IndexMap<usize, crate::matching::Meeting>,
}

/// A calculation link read against the line it cites: what the line says
/// (`Known::says`), the link as a citation of the step compares it, and
/// which of the line's facts it is, the first alike (`alike_top`); None
/// where the line is not in scope or the link does not read.
struct LinkReading {
    says: Vec<super::library::Said>,
    said: Node,
    at: Option<usize>,
}

/// `LinkReading` of one link of `step`: what `check_chain_links` asks of
/// it, and where `link_places` finds it.
fn link_reading(
    link: &Link,
    step: &Step,
    known: &Known,
    library: &Library,
) -> Option<LinkReading> {
    let scope = known.scope(step);
    let stated = scope.get(&link.line.cite)?;
    let claim = link.claim(known)?;
    let defined = known.citing_step(step);
    let said = known.as_cited(&claim, &defined);
    let says = known.says(stated, &defined);
    let at = says
        .iter()
        .position(|s| alike_top(&said, &s.cited, &library.ctx));
    Some(LinkReading { says, said, at })
}

/// Each link of a calculation cites a line that says it.
///
/// `SYNTAX.md`: a link `rel t  L` cites one line whose claim is exactly the
/// previous term rel t, read either way round where it is an equation. A
/// line saying `a(0) = M` does not say `gcd(a(0), b(0)) = gcd(M, b(0))`:
/// that is a substitution, a step of its own. A line of several sentences,
/// or a conjunction, says each of them. A link naming `arithmetic` is
/// `check_closed_arithmetic`'s, and one citing a define is the define's
/// reading of the name.
pub fn check_chain_links(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let defines = define_labels(thm, scopes);
    for step in &thm.steps {
        for link in chain_links(&step.just, &thm.path) {
            let cite = &link.line.cite;
            // A link citing a define is what the define makes its name: with
            // the define written out, an equation's two sides are one.
            if defines.contains(cite.as_str()) {
                if let Some(None) = define_link_meeting(&link, known) {
                    report.say(
                        &thm.path,
                        link.line.line,
                        format!(
                            "{} is not what {cite} makes it",
                            link.line.quoted(&link.from)
                        ),
                    );
                }
                continue;
            }
            if cite == "arithmetic" || !known.scope(step).contains_key(cite) {
                continue;
            }
            // A link that does not read is the elaborator's to report.
            let Some(reading) = link_reading(&link, step, known, library) else {
                continue;
            };
            let said = reading.said;
            let lines: Vec<Node> = reading.says.into_iter().map(|s| s.cited).collect();
            if reading.at.is_none() {
                report.say(
                    &thm.path,
                    link.line.line,
                    format!(
                        "a link of step {} cites {cite}, which does not say {}; a link cites the line that states it, and a substitution is a step of its own",
                        step.number,
                        link.line.quoted(&link.from)
                    ),
                );
                continue;
            }
            // What the link drops an identity element from is a number by
            // what the step names or the page says once, the link's own
            // letters among them.
            let mut parts = Parts {
                facts: known.parts(step, library).facts.clone(),
                claims: vec![said.clone()],
                seed: Binding::new(),
                said_once: Vec::new(),
            };
            let introduced = super::library::introduced(known, step);
            let typed = super::library::typed_in_scope(known, step);
            let points = super::library::points_introduced(known, step);
            said_once(
                &mut parts,
                &introduced,
                &points,
                &typed,
                library,
                &known.sorts,
            );
            if let Some(left) =
                link_unsaid(&said, &lines, &parts.facts, library).first()
            {
                report.say(
                    &thm.path,
                    link.line.line,
                    format!(
                        "a link of step {} drops an identity element from {}, which nothing the step names says is a number; a requires line of the step says it",
                        step.number,
                        known.print(left)
                    ),
                );
            }
        }
    }
}

/// The name the define carrying `label` gives, or None: one this theorem
/// writes, one its file writes, or one its file imports under an alias.
fn define_named(thm: &Theorem, label: &str, scopes: &[FileScope]) -> Option<String> {
    // A recursion gives no one name.
    crate::corpus::proof::in_scope(thm, scopes)
        .into_iter()
        .find(|d| d.label.as_deref() == Some(label))
        .and_then(|d| d.parts.name().map(|_| d.name))
}

/// The define by recursion this theorem writes under `label`, with the line
/// it is written on, or None where the label is another kind of define or
/// none.
fn recursion_cited(thm: &Theorem, label: &str) -> Option<(Recursion, usize)> {
    let d = thm.defines.iter().find(|d| d.label == label)?;
    match define_parts(&d.text) {
        Built(DefineParts::Recursion(r)) => Some((r, d.line)),
        _ => None,
    }
}

/// What the define by recursion says `name` is at the argument `at`, as
/// (the rule's term there, the index it is taken at, or None at 0); or None
/// where `at` is neither 0 nor something plus one. 1 is 0 + 1 with its 0
/// dropped (`SYNTAX.md`, "An identity element goes without saying"), so
/// F(1) is the step rule at 0; 2 is not 1 + 1 by any element dropped, and
/// is a value no rule gives.
fn recursion_value(
    said: &Recursion,
    name: &str,
    at: &Node,
    written: impl Fn(&RuleText) -> Written,
    env: Env,
    sorts: &Sorts,
) -> Checked<Option<(Node, Option<Node>)>> {
    let (rule, index) = if at.notation() == NUMERAL && at.text == "0" {
        (&said.start[name], None)
    } else if at.spelling() == PLUS
        && at.children.len() == 2
        && at.children[1].notation() == NUMERAL
        && at.children[1].text == "1"
    {
        (&said.step[name], Some(at.children[0].clone()))
    } else if at.notation() == NUMERAL && at.text == "1" {
        (&said.step[name], Some(Node::numeral("0")))
    } else {
        return Ok(None);
    };
    let mut local = sorts.clone();
    local.insert(said.index.clone(), Sort::of("number"));
    let mut term = written(rule).formula()?.read(env.g, &local)?;
    if let Some(index) = &index {
        let mut put = Binding::new();
        put.insert(Symbol::of(&said.index), index.clone());
        // Apart from a letter the rule binds, a sum's index among them.
        term = substitute_apart_by(&term, &put, &env.g.binders());
    }
    Ok(Some((term, index)))
}

/// The value a term by cases takes where the facts say which case, with the
/// conditions passed to reach it, or why no case is said. A term not by
/// cases is its own value, passing none.
enum Case {
    Value { value: Node, passed: Vec<Passed> },
    Unsaid(&'static str),
}

/// A condition passed on the way to a case: whether it holds or fails, and
/// the fact that says so.
struct Passed {
    holds: bool,
    fact: Node,
}

/// A condition is said where a fact is it, or denies it, as one formula
/// (`Known::alike`): `0 = b(k)` says the condition `b(k) = 0` holds.
fn case_taken(
    node: &Node,
    facts: &[Node],
    wrappers: &FxIndexSet<NotationId>,
    known: &Known,
) -> Case {
    let mut node = node.clone();
    let mut passed = Vec::new();
    while node.notation() == BY_CASES && node.children.len() == 3 {
        let (value, condition, rest) = (
            node.children[0].clone(),
            node.children[1].clone(),
            node.children[2].clone(),
        );
        if let Some(f) = facts.iter().find(|f| known.alike(f, &condition)) {
            passed.push(Passed {
                holds: true,
                fact: f.clone(),
            });
            return Case::Value { value, passed };
        }
        if let Some(f) = facts.iter().find(|f| {
            wrappers.contains(&f.notation())
                && !f.children.is_empty()
                && known.alike(&f.children[0], &condition)
        }) {
            passed.push(Passed {
                holds: false,
                fact: f.clone(),
            });
            node = rest;
            continue;
        }
        return Case::Unsaid(
            "no line it cites says whether a case's condition holds or fails",
        );
    }
    Case::Value {
        value: node,
        passed,
    }
}

/// How a step's equation is a define's value: its two sides one term as
/// written, whatever case holds; one side's case, taken by the conditions
/// passed, alike the other side; or neither, with why where a condition is
/// unsaid. The check (`check_define_citation`) and the record
/// (`define_cases`) both read a step by this.
enum Given {
    AsWritten,
    Taken {
        passed: Vec<Passed>,
        /// How the case's value meets the other side (`Known::alike_how`).
        meeting: Option<Meeting>,
    },
    Not(Option<&'static str>),
}

fn value_given(
    left: &Node,
    right: &Node,
    facts: &[Node],
    wrappers: &FxIndexSet<NotationId>,
    known: &Known,
) -> Given {
    // Written out, the two sides one term: the claim is the define's
    // value as the define writes it, whatever case holds, as
    // `e(n) = s(D(f(n), n))` is where s is by cases.
    if known.alike(left, right) {
        return Given::AsWritten;
    }
    let mut why: Option<&'static str> = None;
    for (one, other) in [(left, right), (right, left)] {
        match case_taken(one, facts, wrappers, known) {
            Case::Unsaid(reason) => why = why.or(Some(reason)),
            Case::Value { value, passed } => {
                if known.alike(&value, other) {
                    let meeting = known.alike_how(&value, other);
                    return Given::Taken { passed, meeting };
                }
            }
        }
    }
    Given::Not(why)
}

/// What is wrong with a step's claim, read as one equation a define by
/// recursion gives; None where nothing is.
///
/// One side is a sequence at 0 or at X + 1, and the other is what the define
/// says it is there: the value at 0, or the rule at k + 1 with X for k, in
/// the case the cited lines say it is in. At X + 1 a cited line says X ∈ ℕ₀,
/// since the rule holds only at a step the index takes.
fn recursion_equation(
    claims: &[Node],
    facts: &[Node],
    said: &Recursion,
    line: usize,
    known: &Known,
    wrappers: &FxIndexSet<NotationId>,
    equals: &FxIndexSet<NotationId>,
) -> Option<String> {
    let sorts = &known.sorts;
    if claims.len() != 1 || !equals.contains(&claims[0].notation()) {
        return Some(
            "claims no one equation; a define says what its names are equal to"
                .to_string(),
        );
    }
    let mut why: Option<String> = Some(format!(
        "its claim has none of {} applied on either side",
        said.names.join(", ")
    ));
    let kids = &claims[0].children;
    let orders = [(&kids[0], &kids[1]), (&kids[1], &kids[0])];
    for (one, other) in orders {
        if !(one.notation() == APPLICATION
            && one.children.len() == 2
            && one.children[0].is_name()
            && said.names.iter().any(|n| *n == one.children[0].text))
        {
            continue;
        }
        why = None;
        let name = &one.children[0].text;
        let rule = |text: &RuleText| text.written(&known.thm.path, line);
        let Ok(found) =
            recursion_value(said, name, &one.children[1], rule, known.env, sorts)
        else {
            continue; // `check_formulas` says it does not read
        };
        let Some((term, index)) = found else {
            why = Some(format!(
                "{name} is given at 0 and at {} + 1, and nowhere else",
                said.index
            ));
            continue;
        };
        if let Some(index) = &index {
            let said_in = facts.iter().any(|f| {
                f.notation() == MEMBERSHIP
                    && f.children.len() == 2
                    && known.alike(&f.children[0], index)
                    && f.children[1].text == said.domain
            });
            if !said_in {
                why = Some(format!(
                    "no line it cites says the index is in {}",
                    said.domain
                ));
                continue;
            }
        }
        match case_taken(&term, facts, wrappers, known) {
            Case::Unsaid(reason) => {
                why = Some(reason.to_string());
                continue;
            }
            Case::Value { value: got, .. } => {
                if known.alike(&got, other) {
                    return None;
                }
            }
        }
    }
    Some(match why {
        Some(why) if !why.is_empty() => {
            format!("claims a value it does not give: {why}")
        }
        _ => "claims a value it does not give".to_string(),
    })
}

/// A define by recursion says each value from the values before it.
///
/// A value at 0 names none of the sequences, and a rule at k + 1 names them
/// only at k: `a(k + 1) := a(k + 1) + 1` says nothing, and `a(k + 1) :=
/// a(k − 1)` reaches a value the rule has not given yet. Each rule reads,
/// since a rule that does not is a value nobody can cite.
///
/// A rule at k + 1 may name k itself, as `c(k + 1) := c(k) + k` does; a
/// value at 0 has no k to name.
pub fn check_recursions(report: &mut Report, thm: &Theorem, known: &Known) {
    for d in &thm.defines {
        let Built(DefineParts::Recursion(said)) = define_parts(&d.text) else {
            continue;
        };
        let mut local = known.sorts.clone();
        local.insert(said.index.clone(), Sort::of("number"));
        let label = &d.label;
        for (given, at) in [(&said.start, None), (&said.step, Some(&said.index))] {
            for (name, rule) in given {
                let place = match at {
                    None => format!("{name}(0)"),
                    Some(at) => format!("{name}({at} + 1)"),
                };
                let rule = d.rule(rule);
                let tree = match rule
                    .formula()
                    .and_then(|s| known.keep_read(&s, &local))
                {
                    Ok(tree) => tree,
                    Err(p) => {
                        report.say(
                            &thm.path,
                            d.line,
                            format!(
                                "define {label}: the rule for {place} does not read: {}",
                                p.message
                            ),
                        );
                        continue;
                    }
                };
                let applied = |node: &Node| {
                    node.notation() == APPLICATION
                        && node.children.len() == 2
                        && node.children[0].is_name()
                        && said.names.iter().any(|n| *n == node.children[0].text)
                };
                let nodes = walk(std::slice::from_ref(&tree));
                let at_k: BTreeSet<usize> = nodes
                    .iter()
                    .filter(|n| applied(n))
                    .map(|n| n.children[1].id())
                    .collect();
                if at.is_none()
                    && nodes.iter().any(|n| {
                        n.is_name() && n.text == said.index && !at_k.contains(&n.id())
                    })
                {
                    report.say(
                        &thm.path,
                        d.line,
                        format!(
                            "define {label}: the value of {place} names {}, which has no value at 0",
                            said.index
                        ),
                    );
                }
                for node in &nodes {
                    if !applied(node) {
                        continue;
                    }
                    let arg = &node.children[1];
                    if let Some(at) = at {
                        if arg.is_name() && arg.text == *at {
                            continue;
                        }
                    }
                    let message = match at {
                        Some(_) => format!(
                            "define {label}: the rule for {place} names {} at a place other than {}",
                            node.children[0].text, said.index
                        ),
                        None => format!(
                            "define {label}: the value of {place} names {}, which has no value before 0",
                            node.children[0].text
                        ),
                    };
                    report.say(&thm.path, d.line, message);
                    break;
                }
            }
        }
    }
}

/// A step citing a define claims what the define says the name is.
///
/// The claim is an equation with the name on one side, applied or not, and
/// its value on the other, in either order. Written out, the two sides are
/// one term. Where the define is by cases, the lines the step cites say
/// which case it is in, by its condition or that condition's negation, and
/// the value is the one that case gives: `h(t) = g⁻¹(t)` cites D2 from a
/// line saying t ∉ C.
pub fn check_define_citation(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let env = library.env;
    let wrappers = wrappers(env);
    for step in &thm.steps {
        let just = &step.just;
        if just.head != crate::corpus::Head::Define {
            continue;
        }
        let label = just.defined.clone().unwrap_or_default();
        let say = format!("step {} cites {label}", step.number);
        if let Some((recursion, line)) = recursion_cited(thm, &label) {
            let parts = known.parts(step, library);
            if let Some(why) = recursion_equation(
                &parts.claims,
                &parts.facts,
                &recursion,
                line,
                known,
                &wrappers,
                &library.ctx.equations,
            ) {
                report.say(&thm.path, just.line, format!("{say} and {why}"));
            }
            continue;
        }
        let Some(name) = define_named(thm, &label, scopes) else {
            report.say(
                &thm.path,
                just.line,
                format!("{say}, which no define in scope carries"),
            );
            continue;
        };
        let parts = known.parts(step, library);
        let written: Result<Vec<Node>, _> = step
            .claim
            .sentences()
            .iter()
            .map(|s| known.parse(s))
            .collect();
        let Ok(written) = written else {
            continue;
        };
        // A define with a parameter says what its function is on, as well as
        // what its name is equal to (`ELABORATION.md`).
        if parts.claims.len() == 1
            && written.len() == 1
            && library
                .ctx
                .functions_on
                .contains(&parts.claims[0].notation())
        {
            // The subject as written: the claim's parts have the defined
            // name written out, and h is then the function it names.
            let subject = written[0].children.first();
            if !subject.is_some_and(|s| s.is_name() && s.text == name) {
                report.say(
                    &thm.path,
                    just.line,
                    format!("{say} and claims that something other than {name} is a function on a set"),
                );
            }
            continue;
        }
        if parts.claims.len() != 1
            || written.len() != 1
            || !library.ctx.equations.contains(&parts.claims[0].notation())
        {
            report.say(
                &thm.path,
                just.line,
                format!("{say} and claims no one equation; a define says what its name is equal to, and a define with a parameter what its function is on"),
            );
            continue;
        }
        let named: BTreeSet<String> = written[0]
            .walk()
            .iter()
            .filter(|n| n.is_name())
            .map(|n| n.text.to_string())
            .collect();
        if !named.contains(&name) {
            report.say(
                &thm.path,
                just.line,
                format!("{say} and its claim never names {name}"),
            );
            continue;
        }
        let (left, right) =
            (&parts.claims[0].children[0], &parts.claims[0].children[1]);
        if let Given::Not(why) =
            value_given(left, right, &parts.facts, &wrappers, known)
        {
            let tail = why.map(|w| format!(": {w}")).unwrap_or_default();
            report.say(
                &thm.path,
                just.line,
                format!("{say} and claims a value it does not give{tail}"),
            );
        }
    }
}

/// Of each step citing a define by cases whose value it claims in one case,
/// the conditions it passes to reach it, each placed in the line the step
/// cites that says it holds or fails, and how the case's value meets the
/// other side (`CheckedTheorem::define_cases`), as `check_define_citation`
/// reads the step; by the step's line.
pub fn define_cases(
    thm: &Theorem,
    library: &Library,
    known: &Known,
) -> IndexMap<usize, crate::checker::record::TakenCase> {
    let wrappers = wrappers(library.env);
    let mut out = IndexMap::new();
    for step in thm.steps.iter().filter(|s| s.just.head == Head::Define) {
        let label = step.just.defined.as_deref().unwrap_or_default();
        if recursion_cited(thm, label).is_some() {
            continue;
        }
        let parts = known.parts(step, library);
        let [claim] = parts.claims.as_slice() else {
            continue;
        };
        if !library.ctx.equations.contains(&claim.notation()) {
            continue;
        }
        let Given::Taken { passed, meeting } = value_given(
            &claim.children[0],
            &claim.children[1],
            &parts.facts,
            &wrappers,
            known,
        ) else {
            continue;
        };
        if passed.is_empty() {
            continue;
        }
        let passed = passed
            .iter()
            .map(|p| crate::checker::record::PassedCondition {
                holds: p.holds,
                said_by: fact_placed(step, &p.fact, known),
            })
            .collect();
        out.insert(
            step.just.line,
            crate::checker::record::TakenCase { passed, meeting },
        );
    }
    out
}

/// Where in a line the step cites the fact stands, the first line that says
/// it, placed as a citation's facts are (`FirstAt`); None where no line the
/// step cites says it, a requires line's fact among them.
pub(super) fn fact_placed(
    step: &Step,
    fact: &Node,
    known: &Known,
) -> Option<crate::checker::record::FirstAt> {
    let scope = known.scope(step);
    let defined = known.citing_step(step);
    step.just.refs.iter().find_map(|r| {
        let stated = scope.get(r)?;
        let says = known.says(stated, &defined);
        let s = says.iter().find(|s| known.alike(&s.cited, fact))?;
        super::citations::placed(r, s, &says, known.sentence_count(stated))
    })
}
