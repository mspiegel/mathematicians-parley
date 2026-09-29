//! Every library item with a target, proved by citing it from nothing but
//! what it says.
//!
//! An item's statement is written by hand beside the set.mm theorem its
//! `target` names, and a citation of it is built from that theorem, with the
//! theorem's own hypotheses. So a proof citing it builds and verifies
//! whatever the item's hypotheses say, and an item that says less than the
//! theorem asks — `let k ∈ ℤ` where `hashgt0elex` asks k ∈ ℕ₀ — misstates
//! the lemma, and no proof citing it notices. This stage restates each such
//! item as a theorem of its own: its hypotheses, one of its conclusions, and
//! one step citing it from every hypothesis. That proof builds only where
//! what the item says gives its target what the target asks, and the verifier
//! checks what was built.
//!
//! The restatements are made from the records on every run and never
//! written, so there is no copy of a statement to drift from its record, and
//! an item added to the library is restated the day it is written.

use std::collections::BTreeSet;
use std::path::Path;

use indexmap::IndexMap;

use crate::corpus::{corpus, parse_proof, Corpus, Intro, Record, RecordKind};
use crate::formula::{parse_here, Grammar, Node, Sorts};
use crate::regex;
use crate::said::Said;
use crate::sorts::infer;
use crate::source::{Overlay, Source};

// The name a `let` line introduces: what stands before its `∈`, `∉`, `:`,
// `⊆` or `be`.
regex!(INTRODUCES, r"^([^\s∈∉:⊆]+)");

/// The shapes a restatement asks about, read off a sentence's tree by what
/// the notation at its root builds in the kernel — `wb`, `wi`, `wrex` —
/// never by how it is spelt, and cut from the sentence where the parser read
/// each part (`Node::written`).
struct Shapes<'a> {
    g: &'a Grammar,
    /// The kernel constructor each notation builds, by its record's name.
    builds: IndexMap<String, String>,
}

impl<'a> Shapes<'a> {
    fn new(records: &[Record], g: &'a Grammar) -> Shapes<'a> {
        let mut builds = IndexMap::new();
        for (name, entries) in crate::targets::terms(records) {
            if let Some(head) = entries
                .iter()
                .flatten()
                .next()
                .and_then(|e| e.split_whitespace().last())
            {
                builds.insert(name, head.to_string());
            }
        }
        Shapes { g, builds }
    }

    /// The sentence's tree, where it reads, and what its root builds.
    fn root(&self, sentence: &str, sorts: &Sorts) -> Option<(Node, &str)> {
        let tree = parse_here(sentence, self.g, sorts).ok()?;
        let head = self.builds.get(&tree.notation)?.as_str();
        Some((tree, head))
    }

    /// The two parts of a sentence whose root builds `head`, as written.
    fn parts(
        &self,
        sentence: &str,
        sorts: &Sorts,
        head: &str,
    ) -> Option<(String, String)> {
        let (tree, built) = self.root(sentence, sorts)?;
        if built != head || tree.children.len() != 2 {
            return None;
        }
        Some((
            tree.children[0].written(sentence)?,
            tree.children[1].written(sentence)?,
        ))
    }

    /// `there is k ∈ ℤ with …`, `there are m ∈ ℤ and n ∈ ℤ with …`: each
    /// name with the set it is in, and what is said of them, as written.
    /// The names are the holes the notation's `binds` line says it
    /// introduces, and each one's set the hole its `sort` says holds it.
    fn witnesses(
        &self,
        sentence: &str,
        sorts: &Sorts,
    ) -> Option<(Vec<(String, String)>, String)> {
        let (tree, built) = self.root(sentence, sorts)?;
        if built != "wrex" {
            return None;
        }
        let n = self.g.notations.iter().find(|n| {
            n.key() == tree.notation
                && n.holes.len() == tree.children.len()
                && n.binds.is_some()
        })?;
        let binds = n.binds.as_ref()?;
        let crate::outcome::Built(sig) = infer::signature(n.sort.as_deref()?) else {
            return None;
        };
        let members = sig.members();
        let mut names = Vec::new();
        for &held in &binds.held {
            let (_, set) = members.iter().find(|(element, _)| *element == held)?;
            names.push((
                tree.children.get(held)?.written(sentence)?,
                tree.children.get(*set)?.written(sentence)?,
            ));
        }
        let [body] = binds.body.as_slice() else {
            return None;
        };
        Some((names, tree.children.get(*body)?.written(sentence)?))
    }
}

/// The steps naming what `there is` says there is: its sentences, `k ∈ ℤ`
/// for each name and then what is said of them, obtained by `how`.
fn obtaining(
    number: usize,
    names: &[(String, String)],
    said: &str,
    how: &str,
) -> String {
    let mut claim: Vec<String> = names
        .iter()
        .map(|(x, set)| format!("{x} ∈ {set}."))
        .collect();
    claim.push(format!("{said}."));
    let named: Vec<&str> = names.iter().map(|(x, _)| x.as_str()).collect();
    format!(
        "{number}.  {}\n    obtain {}{how}\n",
        claim.join(" "),
        named.join(", ")
    )
}

use super::build::{artifacts, Artifact, Maker, DEFINITIONS, PROVED};
use super::{path_of, verify};

/// Where the restatements stand, as if they were proof files of the tree.
pub const RESTATED: &str = "tests/restated";

/// A proof file per library file, restating each of its items that has a
/// target: (path, text).
///
/// A record may use a name no line of it introduces, as `nat0-as-int` says
/// `n ∈ ℕ₀ ↔ …` of every n, and a proof introduces every name it uses. So
/// each such name is introduced by `let … be an element`, which claims
/// nothing of it: a restatement that said more than its item would supply
/// what the item leaves out, and pass where the item says too little.
///
/// An item whose letters stand for statements, as `P or not P` does, or for
/// properties, as `{t ∈ X : P(t)}` does, is a schema a proof cannot restate:
/// a proof introduces a thing, never a statement, and a proof citing the
/// item does so at a formula of its own. Those are given back by name, in
/// the second list.
///
/// A definition says `A ↔ B`, and a step unfolds it one way from a line
/// saying the other, so each way is restated: from `assume A`, `B`, and from
/// `assume B`, `A`.
pub fn restatements(
    records: &[Record],
    g: &Grammar,
) -> (Vec<(String, String)>, Vec<String>) {
    let mut files: IndexMap<String, String> = IndexMap::new();
    let mut schemas: Vec<String> = Vec::new();
    let shapes = Shapes::new(records, g);
    for r in records {
        if !r.kind.is_item() || !r.fields.contains_key("target") {
            continue;
        }
        if says_of_statements(r, g) {
            schemas.push(r.qualified());
            continue;
        }
        let free = free_names(r, g);
        let file = r.module().rsplit('/').next().unwrap_or("");
        let text = files.entry(format!("{RESTATED}/{file}.proof")).or_default();
        let prefix = if r.kind == RecordKind::Definition {
            "def"
        } else {
            "thm"
        };
        // The item's assumptions, and what its `let` lines claim, are what
        // the step cites it from, as a proof citing it names the lines that
        // say them.
        let from: Vec<String> = r
            .hypotheses
            .iter()
            .filter(|h| h.kind == Intro::Assume || is_claim(&h.text))
            .filter_map(|h| h.label.clone())
            .collect();
        // A step citing an item says what each of its names stands for,
        // which here is itself.
        let about = {
            let names: Vec<String> = let_names(r)
                .into_iter()
                .chain(free.iter().cloned())
                .collect();
            let said: Vec<String> =
                names.iter().map(|x| format!("{x} := {x}")).collect();
            if said.is_empty() {
                String::new()
            } else {
                format!(" {}", said.join(", "))
            }
        };
        let sorts =
            crate::sorts::sorts_of_record(r, crate::sorts::Env { g, scopes: &[] });
        let mut ways: Vec<(Option<String>, String)> = Vec::new();
        for (conclusion, _) in &r.conclusions {
            let claim = conclusion.split_whitespace().collect::<Vec<_>>().join(" ");
            let said = crate::sorts::sentences(&claim);
            let sides = match said.as_slice() {
                [one] => shapes.parts(one, &sorts, "wb"),
                _ => None,
            };
            let cases: Vec<(String, String)> = said
                .iter()
                .filter_map(|s| shapes.parts(s, &sorts, "wi"))
                .collect();
            if let (RecordKind::Definition, Some((left, right))) = (r.kind, sides) {
                ways.push((Some(left.clone()), right.clone()));
                ways.push((Some(right), left));
            } else if r.kind == RecordKind::Definition
                && !cases.is_empty()
                && cases.len() == said.len()
            {
                // A definition by cases is unfolded one case at a time, from
                // a line saying its condition.
                for (condition, then) in cases {
                    ways.push((Some(condition), then));
                }
            } else {
                ways.push((None, claim));
            }
        }
        for (n, (assumed, claim)) in ways.iter().enumerate() {
            let name = if n == 0 {
                r.name.clone()
            } else {
                format!("{}-{}", r.name, n + 1)
            };
            text.push_str(&format!("theorem {name}\n"));
            for x in &free {
                text.push_str(&format!("  let {x} be an element\n"));
            }
            for h in &r.hypotheses {
                text.push_str(&format!("  {} {}\n", h.kind.as_str(), h.text));
            }
            for range in &r.ranges {
                text.push_str(&format!("  {}\n", range.text));
            }
            let mut from = from.clone();
            let mut steps: Vec<String> = Vec::new();
            if let Some(side) = assumed {
                text.push_str(&format!("  assume {side}    (R1)\n"));
                // What a line says there is, a step names before it is used,
                // as a proof reads a "there is" it was given.
                match shapes.witnesses(side, &sorts) {
                    Some((names, said)) => {
                        steps.push(obtaining(
                            steps.len() + 1,
                            &names,
                            &said,
                            " from R1",
                        ));
                        from.push(steps.len().to_string());
                    }
                    None => from.push("R1".to_string()),
                }
            }
            let item = format!("{prefix}:{}{about}", r.qualified());
            let from_text = if from.is_empty() {
                String::new()
            } else {
                format!(", from {}", from.join(", "))
            };
            text.push_str(&format!("  then {claim}\n\n"));
            // A claim that there is something is obtained from the item,
            // named, and exhibited, as a proof citing it does.
            match shapes.witnesses(claim, &sorts) {
                Some((names, said)) => {
                    let n = steps.len() + 1;
                    let how = format!(": {item}{from_text}\n");
                    let got = obtaining(n, &names, &said, &how);
                    steps.push(got.trim_end_matches('\n').to_string() + "\n");
                    steps.push(format!("{}.  {claim}\n    exhibit, from {n}\n", n + 1));
                }
                None => {
                    let n = steps.len() + 1;
                    steps.push(format!("{n}.  {claim}\n    {item}{from_text}\n"));
                }
            }
            text.push_str(&steps.join("\n"));
            text.push('\n');
        }
    }
    (files.into_iter().collect(), schemas)
}

/// Whether the reading of a record's lines makes one of its names a
/// statement, or a property, which is a statement about a thing: neither is
/// something a proof can introduce.
fn says_of_statements(r: &Record, g: &Grammar) -> bool {
    let mut store = infer::Store::default();
    let reader =
        infer::read_record(r, crate::sorts::Env { g, scopes: &[] }, &mut store);
    reader.env.values().any(|term| {
        matches!(
            store.find(term),
            infer::SortTerm::Atom(infer::Atom::Formula) | infer::SortTerm::Property(_)
        )
    })
}

/// The names a record's `let` lines introduce, in order.
fn let_names(r: &Record) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for h in r.hypotheses.iter().filter(|h| h.kind == Intro::Let) {
        let body = crate::sorts::unlabel(&h.text);
        let body = str::trim(&body);
        if let Some(m) = crate::sorts::group_re().captures(body) {
            out.push(m["group"].to_string());
            out.push(m["identity"].to_string());
        } else if let Some(m) = INTRODUCES.captures(body) {
            out.push(m[1].to_string());
        }
    }
    out
}

/// The names a record's formulas use that none of its `let` lines
/// introduces and no binder in them binds, in the order they first appear.
fn free_names(r: &Record, g: &Grammar) -> Vec<String> {
    let introduced: BTreeSet<String> = let_names(r).into_iter().collect();
    let sorts = crate::sorts::sorts_of_record(r, crate::sorts::Env { g, scopes: &[] });
    let mut texts: Vec<String> = r
        .hypotheses
        .iter()
        .map(|h| {
            let body = crate::sorts::unlabel(&h.text);
            crate::sorts::let_formula(str::trim(&body))
        })
        .collect();
    texts.extend(r.conclusions.iter().map(|(t, _)| t.clone()));
    let mut out: Vec<String> = Vec::new();
    for text in texts {
        for sentence in crate::sorts::sentences(&text) {
            let Ok(tree) = parse_here(&sentence, g, &sorts) else {
                continue; // the checker says it does not read
            };
            let nodes = tree.walk();
            let bound: BTreeSet<&str> = nodes
                .iter()
                .filter(|n| n.is_name() && n.sort.is("variable"))
                .map(|n| n.text.as_str())
                .collect();
            // A library function's name is the library's, and free in no
            // item that applies it.
            for n in &nodes {
                if n.is_name()
                    && !bound.contains(n.text.as_str())
                    && !introduced.contains(&n.text)
                    && !g.functions.contains_key(&n.text)
                    && !out.contains(&n.text)
                {
                    out.push(n.text.clone());
                }
            }
        }
    }
    out
}

/// Whether a `let` line claims something a step may cite, as `let k ∈ ℕ₀`
/// does, rather than only naming a thing, as `let X be a set` does.
fn is_claim(text: &str) -> bool {
    let body = crate::sorts::unlabel(text);
    let body = str::trim(&body);
    ![
        crate::sorts::set_or_point_re(),
        crate::sorts::element_re(),
        crate::sorts::group_re(),
        crate::sorts::property_re(),
    ]
    .iter()
    .any(|re| re.is_match(body))
}

/// Build every restatement and verify what was built.
pub fn run(source: &dyn Source, setmm: Option<&Path>) -> Said {
    let fail = |message: String| Said {
        printed: String::new(),
        complained: format!("{message}\n"),
        status: 2,
    };
    let Some(setmm) = setmm else {
        return Said {
            printed:
                "set.mm not found; say where it is with SET_MM, or leave a copy or a \
                      link at the root of the working tree\n"
                    .into(),
            complained: String::new(),
            status: 2,
        };
    };
    let found = match corpus(source) {
        Ok(found) => found,
        Err(problem) => return fail(problem.to_string()),
    };
    let g = match Grammar::load(&found.records) {
        Ok(g) => g,
        Err(problem) => return fail(problem.to_string()),
    };
    // The library and the restatements alone: a restatement cites the
    // library and nothing else, and read beside the corpus's own proofs its
    // theorem would compete with them for the labels a stem allows.
    let mut all = Corpus {
        records: found.records.clone(),
        ..Corpus::default()
    };
    let (files, schemas) = restatements(&found.records, &g);
    for (path, text) in files {
        match parse_proof(&path, &text, all.scopes.len()) {
            Ok((scope, theorems)) => {
                all.scopes.push(scope);
                all.theorems.extend(theorems);
            }
            Err(problem) => return fail(problem.to_string()),
        }
    }
    let wanted: Vec<Artifact> = artifacts(&all)
        .into_iter()
        .filter(|a| a.name.starts_with(RESTATED))
        .collect();

    let mut said = Said::default();
    let mut made: Vec<(String, String)> = Vec::new();
    {
        let mut maker = match Maker::new(source, &all, setmm) {
            Ok(maker) => maker,
            Err(problem) => return fail(problem.to_string()),
        };
        for artifact in &wanted {
            match maker.make(artifact) {
                Ok(text) => made.push((artifact.path(), text)),
                Err(problem) => {
                    said.printed += &format!("{problem}\n");
                }
            }
        }
    }
    let unbuilt = wanted.len() - made.len();
    if unbuilt > 0 {
        said.printed += &format!(
            "\n{unbuilt} of {} library items do not give their target what it asks\n",
            wanted.len()
        );
        said.status = 1;
        return said;
    }

    // What was built is verified with the library files it includes.
    let mut built = Overlay::new(source);
    let mut paths = vec![path_of(DEFINITIONS), path_of(PROVED)];
    for (path, text) in made {
        built.write(&path, text.into_bytes());
        paths.push(path);
    }
    let verified = verify::run(&built, &paths, Some(setmm));
    if !verified.green() {
        return verified;
    }
    // What is skipped is written up, and only that (GOALS.md, decision 17).
    let text = source.read_text("docs/ELABORATION.md").unwrap_or_default();
    let Some(listed) = unrestated(&text) else {
        return fail(format!(
            "docs/ELABORATION.md has no paragraph \"{UNRESTATED}\""
        ));
    };
    let skipped: BTreeSet<String> = schemas.into_iter().collect();
    let mut problems: Vec<String> = skipped
        .difference(&listed)
        .map(|name| {
            format!("{name} states a schema no proof restates, and ELABORATION.md does not list it")
        })
        .collect();
    problems.extend(listed.difference(&skipped).map(|name| {
        format!("ELABORATION.md lists {name} as not restated, and it is restated")
    }));
    if !problems.is_empty() {
        return fail(problems.join("\n"));
    }
    said.printed += &format!(
        "all {} restated library items build and verify\n",
        wanted.len()
    );
    said
}

/// The paragraph of `ELABORATION.md` naming the items no proof restates.
const UNRESTATED: &str = "Library items no proof restates.";

regex!(NAMED_ITEM, r"`(stdlib/[^`\s]+)`");

/// The items that paragraph names, from its bold opening to the next
/// paragraph that opens bold or the next heading; None where it is missing.
fn unrestated(text: &str) -> Option<BTreeSet<String>> {
    let start = text.find(&format!("**{UNRESTATED}**"))?;
    let rest = &text[start + UNRESTATED.len() + 4..];
    let end = rest
        .find("\n**")
        .into_iter()
        .chain(rest.find("\n#"))
        .min()
        .unwrap_or(rest.len());
    Some(
        NAMED_ITEM
            .captures_iter(&rest[..end])
            .map(|c| c[1].to_string())
            .collect(),
    )
}
