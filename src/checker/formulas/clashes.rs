//! Name clashes, formula parts and decided words.

use std::slice;

use super::*;
use crate::methods::{field, surds};

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
pub(super) fn cited_sorts(
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
pub(in crate::checker) struct FormulaPart {
    pub(in crate::checker) line: usize,
    pub(in crate::checker) what: String,
    pub(in crate::checker) written: Written,
}

impl FormulaPart {
    pub(in crate::checker) fn new(
        line: usize,
        what: String,
        written: &Written,
    ) -> FormulaPart {
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
pub(super) fn say_chain_inside(
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

pub(super) fn say_unread(
    report: &mut Report,
    thm: &Theorem,
    env: Env,
    own: &BTreeSet<String>,
    part: &FormulaPart,
    p: Problem,
) {
    let lexed = written_tokens(slice::from_ref(&part.written), env.g);
    if defined_below(thm, &lexed, own, env.scopes).is_empty() {
        let said = format!("{}: {}", part.what, p.message);
        report.say(&thm.path, part.line, said);
    }
}

/// Every part of a theorem that is a claim, of one sentence or several:
/// each step's claim, each `assume` and `suppose` line, and the statement. An induction hypothesis writes no formula: it assumes
/// what its induction's claim says.
pub(in crate::checker) fn claim_parts(thm: &Theorem) -> Vec<FormulaPart> {
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
pub(in crate::checker) fn one_formula_parts(thm: &Theorem) -> Vec<FormulaPart> {
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
pub(super) const DECIDING: [&str; 2] = ["arithmetic", "inspection"];

/// The notations of the relations `arithmetic` decides of its own nature,
/// which a definition may unfold without making them words.
pub(super) const NATIVE: [NotationId; 3] = [MEMBERSHIP, EQUALITY, ORDER];

/// Every operation a notation declares, one building a number from numbers,
/// by its notation's name, and whether `arithmetic` works it out: one of
/// its own nature, or one whose record names it in a `decided` field.
pub fn operations(records: &[Record]) -> IndexMap<NotationId, bool> {
    operations_by(records, field::worked_out, false)
}

/// `operations`, by whether `real arithmetic` works each out: one
/// `arithmetic` does, or one whose record names `real arithmetic`; and the
/// constants with them, π and e worked out, i not.
pub fn real_operations(records: &[Record]) -> IndexMap<NotationId, bool> {
    operations_by(records, surds::worked_out, true)
}

/// Each library function, by its name, and whether its record says
/// `real arithmetic` works it out (`DATABASE.md`, decided): ln and exp do,
/// cos and gcd do not.
pub fn real_functions(records: &[Record]) -> IndexMap<String, bool> {
    records
        .iter()
        .filter(|r| r.is_function())
        .map(|r| {
            let decided = field::decides(r, "real arithmetic");
            (r.name.clone(), decided)
        })
        .collect()
}

pub(super) fn operations_by(
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
