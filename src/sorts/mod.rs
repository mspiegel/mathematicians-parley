//! Where a name's sort comes from.
//!
//! `GRAMMAR.md`'s "Sorts" section is the specification. A name's sort is
//! what one reading of its lines settles (`infer`), in the order they are
//! written: each line is parsed with what the lines above it settled, and
//! what it says is added. A `let` line, a membership, a `define` and the way
//! a formula uses a name are all facts of that one reading, so `let n ∈ ℕ`
//! and `let S ∈ 𝒫X` settle n and S the same way, through what the set they
//! are in holds. A name the reading leaves open has no sort, which every hole
//! accepts.
//!
//! This module turns a reading into sorts, and holds what the text says in
//! so many words where a question is about the text and not the sort: which
//! names a theorem introduces, and what a `define`'s domain holds.

use std::collections::BTreeSet;
use std::rc::Rc;

use crate::corpus::proof::{chain, visible};
use crate::corpus::{
    define_parts, Define, DefineLine, DefineParts, FileScope, Intro, Record, ScopeId,
    Theorem,
};
pub(crate) mod infer;
pub mod introduction;

use crate::formula::notation_id::NotationId;
use crate::formula::page::{tokens, Written};
use crate::formula::token::{Token, TokenKind};
use crate::formula::{holds, Grammar, Sort, Sorts, Whole};
use crate::matching::{expand, Defined, Definitions, ParamRead, Rule};
use crate::notations::{FUNCTION_TYPE, ONE_TO_ONE, ONE_TO_ONE_ONTO, ONTO};
use crate::outcome::{Built, Checked, Declined};
pub use introduction::graph_line;
use introduction::Introduction;

pub const NUMBER_SYSTEMS: [&str; 5] = ["ℕ", "ℕ₀", "ℤ", "ℚ", "ℝ"];

/// The notations whose sentence says a function's type, with the function
/// first and its domain and codomain after: `f : X → Y`, and `f : X → Y is
/// one-to-one`, `is onto` and `is one-to-one and onto`, which say the type
/// and a property.
pub const TYPING: [NotationId; 4] = [FUNCTION_TYPE, ONE_TO_ONE, ONTO, ONE_TO_ONE_ONTO];

/// What the tools read a text against: the grammar, and every proof file's
/// scope, which is where a definition a theorem sees from outside it is
/// written.
#[derive(Clone, Copy)]
pub struct Env<'a> {
    pub g: &'a Grammar,
    pub scopes: &'a [FileScope],
}

/// A graph's `let` line, `G be an undirected multigraph with vertices V and
/// edges E` (`introduction::graph_line`): the graph and the names of its
/// two sets, and where the line gives the graph in full, `G be the
/// undirected multigraph with distinct vertices V = {A, B, C, D} and
/// distinct edges E = {a, …, g}, where a joins A and B, …`, its listing.
#[derive(Clone)]
pub struct GraphLine {
    pub graph: String,
    pub vertices: String,
    pub edges: String,
    pub listed: Option<GraphListing>,
}

/// What a graph given in full lists: its vertices and its edges, each list
/// said to be distinct, and the two ends of every edge.
#[derive(Clone)]
pub struct GraphListing {
    pub vertices: Vec<String>,
    pub edges: Vec<String>,
    pub joins: Vec<Joined>,
    /// `V = {A, B, C, D}` as the line writes it, a formula of its own.
    pub vertex_set: String,
    /// `E = {a, …, g}` as the line writes it.
    pub edge_set: String,
}

/// One clause "a joins A and B" of a graph given in full.
#[derive(Clone)]
pub struct Joined {
    pub edge: String,
    pub first: String,
    pub second: String,
    /// The clause as the line writes it, a formula of its own.
    pub said: String,
}

/// A line without the label it closes on (`skeleton::without_label`).
pub fn unlabel(text: &str) -> String {
    crate::corpus::skeleton::without_label(text).to_string()
}

/// The tokens of every part of a theorem that is formula text: those of
/// `written_formulas`, and of the values its citations name, which are read
/// only together (`Values`). A question about how the theorem is written,
/// which names it writes, asks these, and never its words.
pub fn theorem_tokens(thm: &Theorem, g: &Grammar) -> Vec<Vec<Token>> {
    let mut out = written_tokens(&written_formulas(thm), g);
    // A reason the skeleton reader could not cut gives no values; the
    // checker reports it (`check_reason`).
    for d in &thm.defines {
        if let Some(Ok(by)) = d.reason.as_ref().map(|r| &r.by) {
            out.extend(by.values.tokens(g));
        }
    }
    for step in &thm.steps {
        for r in &step.requires {
            if let Ok(by) = &r.by {
                out.extend(by.values.tokens(g));
            }
        }
        out.extend(step.just.values.tokens(g));
    }
    out
}

/// Every part of a theorem that is formula text, as the skeleton cuts it
/// out, but for the values its citations name: its hypotheses, a `let`
/// line's parts (`Introduction::parts`), its statement, its defines' rules
/// and domains, and each step's claim, opening lines, requires lines, the
/// equation a substitution writes and the terms of a calculation.
pub fn written_formulas(thm: &Theorem) -> Vec<Written> {
    let path = &thm.path;
    let lines = |kind: Intro, body: Written| match kind {
        Intro::Let => Introduction::read(body).parts(),
        _ => vec![body],
    };
    let mut out: Vec<Written> = Vec::new();
    for h in &thm.hypotheses {
        out.extend(lines(h.kind, h.body(path)));
    }
    out.push(thm.stated());
    for d in &thm.defines {
        out.extend(define_formulas(d));
    }
    for step in &thm.steps {
        out.push(step.claim.clone());
        for o in step.openers.iter().filter(|o| !o.is_hypothesis) {
            out.extend(lines(o.kind, o.body(path)));
        }
        for r in &step.requires {
            out.push(r.fact.clone());
        }
        out.extend(step.just.equation.clone());
        if let Some(Ok(chain)) = chain(&step.just, path) {
            out.push(chain.start);
            for line in chain.lines {
                out.push(line.term);
                out.extend(line.modulus);
            }
        }
    }
    out
}

/// Every part of a library record that is formula text: its hypotheses, a
/// `let` line's parts (`Introduction::parts`), and its statements.
pub fn record_formulas(r: &Record) -> Vec<Written> {
    let mut out: Vec<Written> = Vec::new();
    for h in &r.hypotheses {
        let body = h.body(&r.path);
        match h.kind {
            Intro::Let => out.extend(Introduction::read(body).parts()),
            _ => out.push(body),
        }
    }
    out.extend(r.stated());
    out
}

/// A define's parts that are formula text: its rule and each domain, or a
/// recursion's rules and the set its index runs over.
pub fn define_formulas(d: &DefineLine) -> Vec<Written> {
    match define_parts(&d.text) {
        Built(DefineParts::One(one)) => std::iter::once(d.rule(&one.body))
            .chain(one.params.iter().map(|p| d.domain(p)))
            .collect(),
        Built(DefineParts::Recursion(r)) => std::iter::once(d.formula(&r.domain))
            .chain(r.start.values().chain(r.step.values()).map(|v| d.rule(v)))
            .collect(),
        Declined(_) => Vec::new(),
    }
}

/// The tokens of each part, as the front end lexes it; a part that does not
/// lex is left out, as `check_formulas` reports it.
pub fn written_tokens(parts: &[Written], g: &Grammar) -> Vec<Vec<Token>> {
    parts.iter().filter_map(|p| tokens(p, g).ok()).collect()
}

/// The names the tokens write.
pub fn names_written(tokens: &[Vec<Token>]) -> BTreeSet<String> {
    tokens
        .iter()
        .flatten()
        .filter(|t| t.kind == TokenKind::Name)
        .map(|t| t.text.clone())
        .collect()
}

/// The letters a binder written in the tokens binds, read off how they are
/// written where the text may not read: the names after `for all`, `there
/// is`, `there are`, `there exists`, `sending`, `{` or `Σ(`, up to the `∈`,
/// `=` or order that follows them, `for all c, d ∈ ℕ` and `{c ∈ A : …}`.
pub fn bound_written(tokens: &[Vec<Token>]) -> BTreeSet<String> {
    const OPENS: [&str; 6] = ["all", "is", "are", "exists", "exist", "sending"];
    const AFTER: [&str; 7] = ["∈", "=", ">", "≥", "<", "≤", "≠"];
    let mut out = BTreeSet::new();
    for line in tokens {
        for (i, t) in line.iter().enumerate() {
            let opens = (t.kind == TokenKind::Word && OPENS.contains(&t.text.as_str()))
                || t.text == "{"
                || (t.text == "Σ" && line.get(i + 1).is_some_and(|n| n.text == "("));
            if !opens {
                continue;
            }
            let mut at = if t.text == "Σ" { i + 2 } else { i + 1 };
            if line.get(at).is_some_and(|n| n.text == "no") {
                at += 1;
            }
            let mut names = Vec::new();
            while let Some(n) = line.get(at).filter(|n| n.kind == TokenKind::Name) {
                names.push(n.text.clone());
                at += 1;
                if line.get(at).is_some_and(|c| c.text == ",") {
                    at += 1;
                } else {
                    break;
                }
            }
            if line
                .get(at)
                .is_some_and(|r| AFTER.contains(&r.text.as_str()))
            {
                out.extend(names);
            }
        }
    }
    out
}

/// A line without its keyword and without its trailing label.
pub fn body_of(text: &str, head: &str) -> String {
    let rest = str::trim(&text[head.len().min(text.len())..]);
    str::trim(&unlabel(rest)).to_string()
}

/// What the `define` lines a citation names by label stand for, and only
/// those: a defined name and the term it names are one formula in a step
/// that cites the define (`SYNTAX.md`), and a name whose define the step
/// does not cite is the name.
pub fn cited_defines(
    thm: &Theorem,
    env: Env,
    sorts: &Sorts,
    cited: &[String],
) -> Definitions {
    let mut out = Definitions::new();
    let lines = thm.defines.iter().filter(|d| cited.contains(&d.label));
    defines_into(&mut out, lines, env, sorts);
    out
}

/// Each define line's name and the tree it stands for, read in the order
/// written, put in `out`.
fn defines_into<'d>(
    out: &mut Definitions,
    lines: impl Iterator<Item = &'d DefineLine>,
    env: Env,
    sorts: &Sorts,
) {
    for d in lines {
        let Built(DefineParts::One(said)) = define_parts(&d.text) else {
            continue;
        };
        let local = define_sorts(&said, sorts);
        // A rule that does not read is `check_formulas`'s to report.
        let read = d.rule(&said.body).formula();
        let Ok((body, params)) = read
            .and_then(|s| s.read(env.g, &local))
            .and_then(|body| Ok((body, params_read(d, &said, &local, sorts, env)?)))
        else {
            continue;
        };
        let made = if said.params.is_empty() {
            Defined::Term(body)
        } else {
            Defined::Rule(Rule {
                params: said.params.clone(),
                read: params,
                body,
                binders: env.g.binders(),
            })
        };
        out.insert(said.name.clone(), made);
    }
}

/// What each definition the theorem sees from outside it stands for: those
/// its file writes above it and those its file imports.
///
/// Each is written out in the file that wrote it, and nowhere else. A
/// definition means what it meant there, whatever the reading file calls
/// things: a file with a T of its own, or one that imported this T as U,
/// reads the same rule, and a definition built from another is followed in
/// the names of the file that built it.
pub fn file_definitions(thm: &Theorem, env: Env) -> Definitions {
    written_definitions(thm.scope, thm.line, env, &BTreeSet::new())
}

/// The definitions from outside a theorem a citation in it may write out,
/// each with the label a citation names it by: its own where its file is the
/// theorem's, and the label on its import otherwise.
pub struct OutsideDefines {
    /// What each definition from outside the theorem stands for, written
    /// out (`file_definitions`).
    pub outside: Definitions,
    /// The label a citation names each by.
    pub labels: indexmap::IndexMap<String, String>,
}

impl OutsideDefines {
    pub fn of(thm: &Theorem, env: Env) -> OutsideDefines {
        let mut labels = indexmap::IndexMap::new();
        for (name, d, src) in visible(env.scopes, thm.scope, thm.line) {
            let label = if src == thm.scope {
                Some(d.label)
            } else {
                env.scopes[thm.scope].import_label(&name).map(String::from)
            };
            if let Some(label) = label {
                labels.insert(name, label);
            }
        }
        OutsideDefines {
            outside: file_definitions(thm, env),
            labels,
        }
    }

    /// What a citation naming `refs` writes out: each define from outside
    /// the theorem whose label it names, and each of the theorem's own it
    /// names (`cited_defines`).
    pub fn citing(
        &self,
        thm: &Theorem,
        env: Env,
        sorts: &Sorts,
        refs: &[String],
    ) -> Definitions {
        let mut made: Definitions = self
            .outside
            .iter()
            .filter(|(name, _)| {
                self.labels.get(*name).is_some_and(|l| refs.contains(l))
            })
            .map(|(name, d)| (name.clone(), d.clone()))
            .collect();
        made.extend(cited_defines(thm, env, sorts, refs));
        made
    }
}

/// The labels a citation in `thm` of `item`, by its full name, is read with
/// besides `refs` (`stated_over`).
pub fn citing_labels(
    thm: &Theorem,
    scopes: &[FileScope],
    refs: &[String],
    item: Option<&str>,
) -> Vec<String> {
    let mut all = refs.to_vec();
    if let Some(item) = item {
        all.extend(stated_over(thm, scopes, item));
    }
    all
}

/// The labels of the defines `item`, a theorem of `thm`'s own file by its
/// full name, is stated over: those the file writes above it. A step citing
/// it speaks of them by name as its statement does, and reads them without
/// citing them (`SYNTAX.md`, the one exception). None for an item of another
/// file, whose defines a step knows only through an import.
pub fn stated_over(thm: &Theorem, scopes: &[FileScope], item: &str) -> Vec<String> {
    let Some((module, name)) = item.rsplit_once('/') else {
        return Vec::new();
    };
    if module != thm.module() {
        return Vec::new();
    }
    let Some(&line) = scopes[thm.scope].theorems.get(name) else {
        return Vec::new();
    };
    visible(scopes, thm.scope, line)
        .into_iter()
        .filter(|(_, _, src)| *src == thm.scope)
        .map(|(_, d, _)| d.label)
        .collect()
}

/// What the theorem's statement is read with: the definitions above it
/// (`file_definitions`), and the defines in its header, between its `let`
/// lines and `then`, which name something of the theorem's own and are read
/// with its sorts. A define by recursion has no single rule and is left
/// out, as it is above.
pub fn statement_definitions(thm: &Theorem, env: Env, sorts: &Sorts) -> Definitions {
    let mut out = file_definitions(thm, env);
    let header = thm.defines.iter().filter(|d| d.line < thm.conclusion_line);
    defines_into(&mut out, header, env, sorts);
    out
}

/// `name -> tree` (a rule for a function) for every definition a line of
/// the scope's file at `line` may use, each written out.
fn written_definitions(
    scope: ScopeId,
    line: usize,
    env: Env,
    seen: &BTreeSet<(String, usize)>,
) -> Definitions {
    let mut out = Definitions::new();
    for (name, d, src) in visible(env.scopes, scope, line) {
        let key = (env.scopes[src].path.clone(), d.line);
        if seen.contains(&key) {
            continue; // an import cycle, which `check_imports` reports
        }
        let mut deeper = seen.clone();
        deeper.insert(key);
        if let Some(made) = written_definition(&d, src, env, &deeper) {
            out.insert(name, made);
        }
    }
    out
}

/// One definition, read and written out in the file that wrote it; None
/// where its rule does not parse, which `check_formulas` reports.
fn written_definition(
    d: &DefineLine,
    src: ScopeId,
    env: Env,
    seen: &BTreeSet<(String, usize)>,
) -> Option<Defined> {
    let Built(parts) = define_parts(&d.text) else {
        return None;
    };
    let said = parts.one()?;
    let inner = written_definitions(src, d.line, env, seen);
    let outer = definition_sorts(&inner);
    let local = define_sorts(said, &outer);
    let read = d.rule(&said.body).formula();
    let (body, params) = read
        .and_then(|s| s.read(env.g, &local))
        .and_then(|body| Ok((body, params_read(d, said, &local, &outer, env)?)))
        .ok()?;
    let body = expand(&body, &inner);
    Some(if said.params.is_empty() {
        Defined::Term(body)
    } else {
        Defined::Rule(Rule {
            params: said.params.clone(),
            read: params,
            body,
            binders: env.g.binders(),
        })
    })
}

/// A define's arguments read where it is written: each name with the sort
/// its domain gives it (`local`), and each domain with the sorts around the
/// define (`outer`).
pub fn params_read(
    d: &DefineLine,
    said: &Define,
    local: &Sorts,
    outer: &Sorts,
    env: Env,
) -> Checked<Vec<ParamRead>> {
    let read = |part: Written, sorts: &Sorts| part.formula()?.read(env.g, sorts);
    said.params
        .iter()
        .map(|p| {
            Ok(ParamRead {
                name: read(d.formula(&p.name), local)?,
                domain: read(d.domain(p), outer)?,
            })
        })
        .collect()
}

/// The sort each definition gives its name: a function takes arguments, and
/// any other is what its rule is.
pub fn definition_sorts(definitions: &Definitions) -> Sorts {
    let mut out = Sorts::new();
    for (name, made) in definitions {
        let sort = match made {
            Defined::Rule(rule) => rule_sort(rule),
            Defined::Term(t) => t.sort.clone(),
        };
        if !sort.is_unsorted() {
            out.insert(name.clone(), sort);
        }
    }
    out
}

/// The sort a function defined by a rule has: a function from its first
/// argument to a function from the next, and so on to its value, as a
/// library function's is (`infer::function_signature`), each argument a
/// number where its domain is a number system and open otherwise, and the
/// value open. So G(a, n) for a ∈ ℝ, n ∈ ℕ₀ is applied to two arguments
/// and not to a pair.
fn rule_sort(rule: &Rule) -> Sort {
    let whole = rule.params.iter().rev().fold(Whole::Open, |value, p| {
        let argument = if p.member_of().is_some_and(|d| NUMBER_SYSTEMS.contains(&d)) {
            Whole::Number
        } else {
            Whole::Open
        };
        Whole::Function(Rc::new(argument), Rc::new(value))
    });
    Sort::whole(whole).unwrap_or_else(|| Sort::of("function"))
}

/// The sort of what a define's domain holds: a number where the domain is a
/// number system, what a name's sort says it holds where it says (a group's
/// elements for a group's set), and otherwise none.
pub fn element_sort(domain: &str, sorts: &Sorts) -> Sort {
    let domain = str::trim(domain);
    if NUMBER_SYSTEMS.contains(&domain) {
        return Sort::of("number");
    }
    sorts.get(domain).and_then(holds).unwrap_or_default()
}

/// The sorts a define's rule is read with: `sorts`, and for a function each
/// argument as what its domain holds.
pub fn define_sorts(said: &crate::corpus::Define, sorts: &Sorts) -> Sorts {
    let mut out = sorts.clone();
    for p in &said.params {
        let held = p
            .member_of()
            .map(|d| element_sort(d, sorts))
            .unwrap_or_default();
        out.insert(p.name.clone(), held);
    }
    out
}

/// The sort of every name an item's own lines settle.
///
/// A record keeps the keyword of a hypothesis in the field name where a
/// proof line keeps it in the text, and a record has no steps and no
/// `define`. That is the whole difference from `sorts_in_scope`: `let k ∈
/// {a, …, n}` names no number system, and k is a number because the range
/// holds numbers.
pub fn sorts_of_record(record: &Record, env: Env) -> Sorts {
    let mut store = infer::Store::default();
    let reader = infer::read_record(record, env, &mut store);
    settled(&reader, &store)
}

/// `sorts_of_record` of every item record, by its place in `records`: read
/// once for a build, since every theorem cites from the same records.
pub fn sorts_of_records(
    records: &[Record],
    env: Env,
) -> indexmap::IndexMap<usize, Sorts> {
    records
        .iter()
        .enumerate()
        .filter(|(_, r)| r.kind.is_item())
        .map(|(i, r)| (i, sorts_of_record(r, env)))
        .collect()
}

/// The sort of every name a proved theorem's statement settles: what a
/// citation of it reads, the statement and not the proof beneath
/// (`infer::read_statement`).
pub fn sorts_of_statement(thm: &Theorem, env: Env) -> Sorts {
    let mut store = infer::Store::default();
    let reader = infer::read_statement(thm, env, &mut store);
    settled(&reader, &store)
}

/// The sorts a citation of a proved theorem reads its statement with, in
/// the checker and the build alike: what its statement settles, over the
/// sorts of the definitions it is read with (`statement_definitions`), so
/// that a function its file defines, s(t), is a function there. Only what
/// the statement says: a letter it leaves open is not the citing proof's
/// letter of that name.
pub fn sorts_of_cited(thm: &Theorem, env: Env) -> Sorts {
    let own = sorts_of_statement(thm, env);
    let written = statement_definitions(thm, env, &own);
    let mut sorts = Sorts::new();
    for (k, v) in &definition_sorts(&written) {
        sorts.insert(k.clone(), v.clone());
    }
    for (k, v) in &own {
        sorts.insert(k.clone(), v.clone());
    }
    sorts.ranges = own.ranges;
    sorts.imported = own.imported;
    sorts
}

/// The sort of every name the theorem's lines settle, read without its
/// citations: what the elaborator reads a theorem with. The checker reads
/// each theorem once, citations and all, and settles the same way
/// (`checker::run`).
pub fn sorts_in_scope(thm: &Theorem, env: Env) -> Sorts {
    let mut store = infer::Store::default();
    let reader = infer::read_theorem(thm, env, &mut store, None);
    settled(&reader, &store)
}

/// The sort of every name a reading of the lines settles.
///
/// What the lines state is a fact of the reading as much as what their
/// formulas imply: `let n ∈ ℕ` makes n a number through the membership, and
/// `let S ∈ 𝒫X` makes S a set because what 𝒫X holds is sets. A name the
/// reading leaves open, or reads as a statement, has no sort.
///
/// The checker's reading fits each citation as it goes and the elaborator's
/// reads no citation. The two settle the same sorts because a citation that
/// settles a name's sort is a defect the checker reports (`cited_sorts`).
pub fn settled(reader: &infer::Reader, store: &infer::Store) -> Sorts {
    let mut out = Sorts::new();
    out.ranges = reader.ranges.clone();
    out.imported = reader.imported.clone();
    for (name, term) in &reader.env {
        match infer::sort(store, term) {
            Some(sort) => {
                out.insert(name.clone(), sort);
            }
            None => {
                out.unsettled.insert(name.clone());
            }
        }
    }
    out
}
