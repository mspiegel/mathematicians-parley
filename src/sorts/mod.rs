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

use crate::corpus::proof::visible;
use crate::corpus::{
    define_parts, DefineLine, DefineParts, FileScope, Intro, Record, ScopeId, Theorem,
};
pub mod infer;

use crate::formula::{holds, parse_here, Grammar, Sort, Sorts};
use crate::matching::{expand, Defined, Definitions, Rule};
use crate::outcome::Built;
use crate::regex;

pub const NUMBER_SYSTEMS: [&str; 5] = ["ℕ", "ℕ₀", "ℤ", "ℚ", "ℝ"];

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
    r"^(?P<graph>\S+)\s+be\s+the\s+undirected\s+multigraph\s+with\s+distinct\s+vertices\s+(?P<vertices>\S+)\s*=\s*\{(?P<vlist>[^}]*)\}\s+and\s+distinct\s+edges\s+(?P<edges>\S+)\s*=\s*\{(?P<elist>[^}]*)\},\s+where\s+(?P<joins>.+)$"
);
regex!(JOINED, r"^(\S+)\s+joins\s+(\S+)\s+and\s+(\S+)$");

/// A graph's `let` line: the graph and the names of its two sets, and where
/// the line gives the graph in full, its listing.
pub struct GraphLine {
    pub graph: String,
    pub vertices: String,
    pub edges: String,
    pub listed: Option<GraphListing>,
}

/// What a graph given in full lists: its vertices and its edges, each list
/// said to be distinct, and the two ends of every edge.
pub struct GraphListing {
    pub vertices: Vec<String>,
    pub edges: Vec<String>,
    pub joins: Vec<Joined>,
}

/// One clause "a joins A and B" of a graph given in full.
pub struct Joined {
    pub edge: String,
    pub first: String,
    pub second: String,
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
        let j = JOINED.captures(str::trim(clause))?;
        joins.push(Joined {
            edge: j[1].to_string(),
            first: j[2].to_string(),
            second: j[3].to_string(),
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

/// A `let` body as the formula it asserts.
///
/// `let f : A → B be one-to-one` introduces f and says it is one-to-one, and
/// the formula is `f : A → B is one-to-one`: "be" is how English says "is"
/// after "let". `let X ⊆ A` introduces a part of A, which is a member of its
/// power set, and the formula is `X ∈ 𝒫A`, the one `for all X ⊆ A`
/// quantifies over. `let E be a function on X` says E is a function on X, a
/// fact a proof citing the line supplies. `let G be a finite group …` says G
/// is finite; the rest of it names things and asserts nothing a proof cites.
/// Every other body is read as it is written.
pub fn let_formula(body: &str) -> String {
    // A graph given in full says what its two sets are, that the names in
    // each list differ, and which vertices each edge joins.
    if let Some(GraphLine {
        vertices,
        edges,
        listed: Some(listing),
        ..
    }) = graph_line(body)
    {
        let mut said = vec![
            format!("{vertices} = {{{}}}", listing.vertices.join(", ")),
            format!("{edges} = {{{}}}", listing.edges.join(", ")),
        ];
        for list in [&listing.vertices, &listing.edges] {
            for (i, one) in list.iter().enumerate() {
                for other in &list[i + 1..] {
                    said.push(format!("{one} ≠ {other}"));
                }
            }
        }
        for j in &listing.joins {
            said.push(format!("{} joins {} and {}", j.edge, j.first, j.second));
        }
        return said.join(". ");
    }
    if let Some(m) = GROUP.captures(body) {
        if m.name("finite").is_some() {
            return format!("{} is finite", &m["group"]);
        }
    }
    if let Some(m) = FUNCTION_ON.captures(body) {
        return format!("{} is a function on {}", &m[1], str::trim(&m[2]));
    }
    if let Some(m) = POLYNOMIAL.captures(body) {
        return format!("{} is a polynomial", &m[1]);
    }
    if let Some(m) = FUNCTION_BEING.captures(body) {
        return format!("{} is {}", &m[1], &m[2]);
    }
    if let Some(m) = PART.captures(body) {
        let whole = str::trim(&m[2]);
        let whole = if whole.contains(' ') {
            format!("({whole})")
        } else {
            whole.to_string()
        };
        return format!("{} ∈ 𝒫{whole}", &m[1]);
    }
    body.to_string()
}

/// What a hypothesis or a block's opening line says to a citation of it:
/// the text after its first word, its label taken off, and for a `let` line
/// the formula `let_formula` gives. Both tools read a cited line this way.
pub fn said_by_line(kind: Intro, text: &str) -> String {
    let body = str::trim(&unlabel(&text[kind.as_str().len()..])).to_string();
    if kind == Intro::Let {
        let_formula(&body)
    } else {
        body
    }
}

/// What a cited line supplies (`SYNTAX.md`): each of its sentences, and,
/// where it has several, their conjunction, since "A. B" and "A and B" are
/// one claim. The conjunction is joined from the left, as a claim of several
/// sentences is, and each sentence is bracketed so that it stays one part.
pub fn supplied_by(text: &str) -> Vec<String> {
    let mut out = sentences(text);
    if out.len() > 1 {
        let joined: Vec<String> = out.iter().map(|s| format!("({s})")).collect();
        out.push(joined.join(" and "));
    }
    out
}

/// The sentences of a line, each without its full stop.
///
/// A sentence ends at a full stop followed by any space, a line break
/// included, so a claim written across two lines splits where it would
/// written on one.
pub fn sentences(text: &str) -> Vec<String> {
    let text = str::trim(text);
    let chars: Vec<(usize, char)> = text.char_indices().collect();
    let mut pieces: Vec<&str> = Vec::new();
    let mut start = 0;
    let mut i = 0;
    while i < chars.len() {
        let (at, c) = chars[i];
        if c.is_whitespace() && i > 0 && chars[i - 1].1 == '.' {
            let mut j = i;
            while j < chars.len() && chars[j].1.is_whitespace() {
                j += 1;
            }
            pieces.push(&text[start..at]);
            start = if j < chars.len() {
                chars[j].0
            } else {
                text.len()
            };
            i = j;
            continue;
        }
        i += 1;
    }
    pieces.push(&text[start..]);
    pieces
        .into_iter()
        .map(|p| str::trim(str::trim(p).trim_end_matches('.')).to_string())
        .filter(|p| !p.is_empty())
        .collect()
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

/// What each `define` line names, as a tree, read with the theorem's sorts.
///
/// A define asserts nothing; it abbreviates. So the name and the term are one
/// formula wherever two formulas are compared, and this is the table that
/// says which term each name stands for. A define may name something in terms
/// of an earlier one, so the terms are read in the order they are written.
///
/// A sequence defined by recursion has no term to stand for: its rule names
/// the sequence itself, so it is never expanded, and a step that needs a
/// value cites the define.
pub fn definitions_in_scope(thm: &Theorem, env: Env, sorts: &Sorts) -> Definitions {
    let mut out = file_definitions(thm, env);
    defines_into(&mut out, thm.defines.iter(), env, sorts);
    out
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
        let Ok(body) = parse_here(&said.body, env.g, &local) else {
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
    let body = parse_here(&said.body, env.g, &local).ok()?;
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
/// (`check::run`).
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
