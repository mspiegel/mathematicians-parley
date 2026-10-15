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

use crate::corpus::proof::{chain, substituted, visible};
use crate::corpus::{
    define_parts, DefineLine, DefineParts, FileScope, Intro, Record, ScopeId, Theorem,
};
pub(crate) mod infer;
pub mod introduction;

use crate::formula::page::{tokens, Written};
use crate::formula::token::{Token, TokenKind};
use crate::formula::{holds, Grammar, Sort, Sorts};
use crate::matching::{expand, Defined, Definitions, Rule};
use crate::outcome::{Built, Declined};
use crate::regex;
use introduction::Introduction;

pub const NUMBER_SYSTEMS: [&str; 5] = ["ℕ", "ℕ₀", "ℤ", "ℚ", "ℝ"];

/// The notations whose sentence says a function's type, with the function
/// first and its domain and codomain after: `f : X → Y`, and `f : X → Y is
/// one-to-one`, `is onto` and `is one-to-one and onto`, which say the type
/// and a property.
pub const TYPING: [&str; 4] =
    ["function-type", "one-to-one", "onto", "one-to-one-onto"];

/// What the tools read a text against: the grammar, and every proof file's
/// scope, which is where a definition a theorem sees from outside it is
/// written.
#[derive(Clone, Copy)]
pub struct Env<'a> {
    pub g: &'a Grammar,
    pub scopes: &'a [FileScope],
}

// A label stands apart from what it labels, so `M(X)` ending a line is M
// applied to X and not a line labelled X.
regex!(LABEL, r"\s+\([A-Z]+[0-9]*\)\s*$");
// `let x ∈ A` and `let a ∉ X`: a thing, and a set it is in or is not in.
regex!(MEMBERSHIP, r"^(\S+)\s*∈\s*\S");
regex!(NOT_IN, r"^(\S+)\s*∉\s*\S");
// `n ∈ ℕ`: a membership whose set is one name, which may say the sort.
regex!(NAMED_MEMBER, r"^(\S+)\s*∈\s*(\S+)$");
regex!(SET_OR_POINT, r"^(\S+)\s+be a (set|point)$");
// `let x be an element`: an element of nothing yet named.
regex!(ELEMENT, r"^(\S+)\s+be\s+an\s+element$");
// `let P be a property of the elements of A`: the property, and its domain.
regex!(
    PROPERTY,
    r"^(\S+)\s+be a property of the elements of\s+(\S+)$"
);
regex!(FUNCTION, r"^(\S+)\s*:\s*.+→.+$");
// `let f : A → B be one-to-one`: a function's type, and a property of it.
regex!(FUNCTION_BEING, r"^(\S+\s*:\s*.+→.+?)\s+be\s+(\S.*)$");
// `let X ⊆ A`: a part of a set.
regex!(PART, r"^(\S+)\s*⊆\s*(\S.*)$");
// `let E be a function on X`: a function, and the set it is on.
regex!(FUNCTION_ON, r"^(\S+)\s+be\s+a\s+function\s+on\s+(\S.*)$");
// `let p be a polynomial`: a function, and that it is a polynomial.
regex!(POLYNOMIAL, r"^(\S+)\s+be\s+a\s+polynomial$");
// `let G be a finite group with operation · and identity e`: a set whose
// members are group elements, its operation, and its identity, which is one
// of them.
regex!(
    GROUP,
    r"^(?P<group>\S+)\s+be\s+a\s+(?P<finite>finite\s+)?group\s+with\s+operation\s+(?P<operation>\S+)\s+and\s+identity\s+(?P<identity>\S+)$"
);
// `H is a subgroup of G`: a set of the group's elements.
regex!(SUBGROUP, r"^(\S+)\s+is\s+a\s+subgroup\s+of\s+(\S+)$");
// `let G be an undirected multigraph with vertices V and edges E`: the graph,
// the set of its vertices, and the set of the names of its edges.
regex!(
    GRAPH,
    r"^(?P<graph>\S+)\s+be\s+an\s+undirected\s+multigraph\s+with\s+vertices\s+(?P<vertices>\S+)\s+and\s+edges\s+(?P<edges>\S+)$"
);
// `let G be the undirected multigraph with distinct vertices V = {A, B, C, D}
// and distinct edges E = {a, …, g}, where a joins A and B, …`: a graph given
// in full, whose vertices and edges are listed, said to be distinct, and
// whose every edge is said to join two of the vertices.
regex!(
    GRAPH_LISTED,
    r"^(?P<graph>\S+)\s+be\s+the\s+undirected\s+multigraph\s+with\s+distinct\s+vertices\s+(?P<vset>(?P<vertices>\S+)\s*=\s*\{(?P<vlist>[^}]*)\})\s+and\s+distinct\s+edges\s+(?P<eset>(?P<edges>\S+)\s*=\s*\{(?P<elist>[^}]*)\}),\s+where\s+(?P<joins>.+)$"
);
regex!(JOINED, r"^(\S+)\s+joins\s+(\S+)\s+and\s+(\S+)$");

/// A graph's `let` line: the graph and the names of its two sets, and where
/// the line gives the graph in full, its listing.
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

/// The graph a `let` body states, in either form; None for any other body,
/// or a listing one of whose clauses says no join.
pub fn graph_line(body: &str) -> Option<GraphLine> {
    if let Some(m) = GRAPH.captures(body) {
        return Some(GraphLine {
            graph: m["graph"].to_string(),
            vertices: m["vertices"].to_string(),
            edges: m["edges"].to_string(),
            listed: None,
        });
    }
    let m = GRAPH_LISTED.captures(body)?;
    let names = |list: &str| -> Vec<String> {
        list.split(',').map(|n| str::trim(n).to_string()).collect()
    };
    let mut joins = Vec::new();
    for clause in m["joins"].split(',') {
        let said = str::trim(clause);
        let j = JOINED.captures(said)?;
        joins.push(Joined {
            edge: j[1].to_string(),
            first: j[2].to_string(),
            second: j[3].to_string(),
            said: said.to_string(),
        });
    }
    Some(GraphLine {
        graph: m["graph"].to_string(),
        vertices: m["vertices"].to_string(),
        edges: m["edges"].to_string(),
        listed: Some(GraphListing {
            vertices: names(&m["vlist"]),
            edges: names(&m["elist"]),
            joins,
            vertex_set: m["vset"].to_string(),
            edge_set: m["eset"].to_string(),
        }),
    })
}

pub fn label_re() -> &'static regex::Regex {
    &LABEL
}
pub fn membership_re() -> &'static regex::Regex {
    &MEMBERSHIP
}
pub fn not_in_re() -> &'static regex::Regex {
    &NOT_IN
}
pub fn set_or_point_re() -> &'static regex::Regex {
    &SET_OR_POINT
}
pub fn element_re() -> &'static regex::Regex {
    &ELEMENT
}
pub fn property_re() -> &'static regex::Regex {
    &PROPERTY
}
pub fn function_re() -> &'static regex::Regex {
    &FUNCTION
}
pub fn function_being_re() -> &'static regex::Regex {
    &FUNCTION_BEING
}
pub fn function_on_re() -> &'static regex::Regex {
    &FUNCTION_ON
}
pub fn polynomial_re() -> &'static regex::Regex {
    &POLYNOMIAL
}
pub fn part_re() -> &'static regex::Regex {
    &PART
}
pub fn group_re() -> &'static regex::Regex {
    &GROUP
}
pub fn graph_re() -> &'static regex::Regex {
    &GRAPH
}
pub fn graph_listed_re() -> &'static regex::Regex {
    &GRAPH_LISTED
}

/// A line without its trailing label, as `LABEL.sub('', text)` leaves it.
pub fn unlabel(text: &str) -> String {
    LABEL.replace(text, "").into_owned()
}

/// The tokens of every part of a theorem that is formula text: those of
/// `written_formulas`, and of the values its citations name, which are read
/// only together (`Values`). A question about how the theorem is written,
/// which names it writes, asks these, and never its words.
pub fn theorem_tokens(thm: &Theorem, g: &Grammar) -> Vec<Vec<Token>> {
    let mut out = written_tokens(&written_formulas(thm), g);
    for d in &thm.defines {
        if let Some(reason) = &d.reason {
            out.extend(reason.values.tokens(g));
        }
    }
    for step in &thm.steps {
        for r in &step.requires {
            out.extend(r.values.tokens(g));
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
        out.extend(substituted(&step.just, path));
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
        Built(DefineParts::One(one)) => std::iter::once(d.formula(&one.body))
            .chain(one.params.iter().map(|p| d.formula(&p.domain)))
            .collect(),
        Built(DefineParts::Recursion(r)) => std::iter::once(d.formula(&r.domain))
            .chain(
                r.start
                    .values()
                    .chain(r.step.values())
                    .map(|v| d.formula(v)),
            )
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

/// The (name, sort) pairs a `let` body or a sentence states: none, one, or,
/// for a group, the group and its identity. `known` is the sorts found so
/// far, since a member of a group's set is a group element.
fn introduced(body: &str, known: &Sorts) -> Vec<(String, &'static str)> {
    if let Some(m) = GROUP.captures(body) {
        return vec![
            (m["group"].to_string(), "group-set"),
            (m["identity"].to_string(), "group-element"),
        ];
    }
    if let Some(m) = SUBGROUP.captures(body) {
        return vec![(m[1].to_string(), "group-set")];
    }
    if let Some(line) = graph_line(body) {
        return vec![
            (line.graph, "set"),
            (line.vertices, "set"),
            (line.edges, "set"),
        ];
    }
    if let Some(m) = SET_OR_POINT.captures(body) {
        let sort = if &m[2] == "set" { "set" } else { "point" };
        return vec![(m[1].to_string(), sort)];
    }
    if let Some(m) = PROPERTY.captures(body) {
        return vec![(m[1].to_string(), "property")];
    }
    if let Some(m) = FUNCTION
        .captures(body)
        .or_else(|| FUNCTION_ON.captures(body))
        .or_else(|| POLYNOMIAL.captures(body))
    {
        return vec![(m[1].to_string(), "function")];
    }
    if let Some(m) = NAMED_MEMBER.captures(body) {
        let set = m[2].trim_end_matches('.');
        if NUMBER_SYSTEMS.contains(&set) {
            return vec![(m[1].to_string(), "number")];
        }
        if known.get(set).is_some_and(|s| s.is("group-set")) {
            return vec![(m[1].to_string(), "group-element")];
        }
    }
    Vec::new()
}

fn set_default(out: &mut Sorts, name: String, sort: Sort) {
    out.entry(name).or_insert(sort);
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
        let read = d.formula(&said.body).sentence();
        let Ok(body) = read.and_then(|s| s.read(env.g, &local)) else {
            continue;
        };
        let made = if said.params.is_empty() {
            Defined::Term(body)
        } else {
            Defined::Rule(Rule {
                params: said.params.clone(),
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
    /// The labels of the defines the theorem's file writes above it.
    pub file_labels: Vec<String>,
}

impl OutsideDefines {
    pub fn of(thm: &Theorem, env: Env) -> OutsideDefines {
        let mut labels = indexmap::IndexMap::new();
        let mut file_labels = Vec::new();
        for (name, d, src) in visible(env.scopes, thm.scope, thm.line) {
            let label = if src == thm.scope {
                file_labels.push(d.label.clone());
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
            file_labels,
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

    /// The labels a citation of `item`, by its full name, is read with
    /// besides `refs`: a theorem of the theorem's own file speaks of the
    /// file's defines by name as its statement does, and is read with them
    /// without citing them (`SYNTAX.md`, the one exception).
    pub fn citing_labels(
        &self,
        thm: &Theorem,
        refs: &[String],
        item: Option<&str>,
    ) -> Vec<String> {
        let own_file = item.is_some_and(|full| {
            full.rsplit_once('/')
                .is_some_and(|(module, _)| module == thm.module())
        });
        let mut all = refs.to_vec();
        if own_file {
            all.extend(self.file_labels.iter().cloned());
        }
        all
    }
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
    let local = define_sorts(said, &definition_sorts(&inner));
    let read = d.formula(&said.body).sentence();
    let body = read.and_then(|s| s.read(env.g, &local)).ok()?;
    let body = expand(&body, &inner);
    Some(if said.params.is_empty() {
        Defined::Term(body)
    } else {
        Defined::Rule(Rule {
            params: said.params.clone(),
            body,
            binders: env.g.binders(),
        })
    })
}

/// The sort each definition gives its name: a function takes arguments, and
/// any other is what its rule is.
pub fn definition_sorts(definitions: &Definitions) -> Sorts {
    let mut out = Sorts::new();
    for (name, made) in definitions {
        let sort = match made {
            Defined::Rule(_) => Sort::of("function"),
            Defined::Term(t) => t.sort.clone(),
        };
        if !sort.is_unsorted() {
            out.insert(name.clone(), sort);
        }
    }
    out
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
        let held = element_sort(&p.domain, sorts);
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

/// The names a theorem's hypotheses introduce in so many words: `n ∈ ℕ`, a
/// group and its identity, a set, a point, a property or a function.
///
/// Which names a theorem introduces itself is a question about its text,
/// and `check_defined_below` asks it; what their sorts are is the reading's
/// (`sorts_of_statement`), which also reaches a name the file defines.
pub fn named_by_hypotheses(thm: &Theorem) -> BTreeSet<String> {
    let mut out = Sorts::new();
    for h in &thm.hypotheses {
        for (name, sort) in introduced(&body_of(&h.text, h.kind.as_str()), &out) {
            set_default(&mut out, name, Sort::of(sort));
        }
    }
    out.keys().cloned().collect()
}

/// The sort of every name a proved theorem's statement settles: what a
/// citation of it reads, the statement and not the proof beneath
/// (`infer::read_statement`).
pub fn sorts_of_statement(thm: &Theorem, env: Env) -> Sorts {
    let mut store = infer::Store::default();
    let reader = infer::read_statement(thm, env, &mut store);
    settled(&reader, &store)
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
