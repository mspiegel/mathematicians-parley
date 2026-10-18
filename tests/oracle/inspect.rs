//! Claims for `inspection`: sets listed in full, and what a reader sees by
//! running down the list (`METHODS.md`, inspection).
//!
//! Two kinds. Sets of numerals the claim writes itself, which the step
//! cites nothing for: a membership, a size, two listings compared, and the
//! members a word `inspection` decides holds of. And a multigraph a `let`
//! line lists, its vertices and edges distinct and each edge joining two
//! vertices: which edges a vertex is incident with, how many, and
//! memberships. The oracle is the set itself, worked out by the test.
//!
//! A size counts what a list names, a thing written twice once: numerals
//! differ by their values, and a list may write one value twice.

use parley::formula::grammar::Grammar;
use parley::formula::node::Node;
use parley::formula::page::numeral;
use parley::formula::Sort;

use crate::gen::{made, Drawn};
use crate::judge::Verdict;
use crate::shared::Random;

/// How `inspection` refuses a claim it cannot see, and a size or value it
/// works out to something else: the build's words, and the checker's,
/// which decides it first.
const NOT_SEEN: &str = "is not seen by inspection of what it cites";
const FALSE: &str = "which is false";
const SHOWN_FALSE: &str = "which inspection of what it cites shows false";

/// Listings the database declares, by size: a set written with any other
/// number of elements has no notation.
const SIZES: [usize; 4] = [1, 2, 3, 4];

fn verdict(holds: bool) -> Verdict {
    if holds {
        Verdict::Holds(true)
    } else {
        Verdict::Refused(vec![NOT_SEEN, FALSE, SHOWN_FALSE])
    }
}

fn number(g: &Grammar, n: i64) -> Node {
    if n < 0 {
        made(g, "−_", vec![numeral(&(-n).to_string())])
    } else {
        numeral(&n.to_string())
    }
}

fn name(text: &str) -> Node {
    Node::name(Sort::of("object"), text)
}

/// A set listed in full, or ∅ where nothing is listed.
fn listed(g: &Grammar, items: Vec<Node>) -> Node {
    let pattern = match items.len() {
        0 => return made(g, "∅", Vec::new()),
        1 => "{_}",
        2 => "{_, _}",
        3 => "{_, _, _}",
        4 => "{_, _, _, _}",
        n => panic!("no listing of {n} is declared"),
    };
    made(g, pattern, items)
}

fn size(g: &Grammar, set: Node) -> Node {
    made(g, "|_|", vec![set])
}

fn equal(g: &Grammar, a: Node, b: Node) -> Node {
    made(g, "_ = _", vec![a, b])
}

/// Numerals 0 to 9, now and then negated.
fn value(r: &mut Random) -> i64 {
    let n = r.below(10) as i64;
    if r.below(5) == 0 {
        -n
    } else {
        n
    }
}

/// `count` numerals, distinct unless `twice`, where one value is listed
/// twice.
fn values(r: &mut Random, count: usize, twice: bool) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    while out.len() < count {
        let v = value(r);
        if !out.contains(&v) {
            out.push(v);
        }
    }
    if twice && count >= 2 {
        let at = r.below(count as u64) as usize;
        let from = (at + 1 + r.below(count as u64 - 1) as usize) % count;
        out[at] = out[from];
    }
    out
}

fn distinct(vs: &[i64]) -> Vec<i64> {
    let mut out = Vec::new();
    for v in vs {
        if !out.contains(v) {
            out.push(*v);
        }
    }
    out
}

fn shuffled<T: Clone>(r: &mut Random, items: &[T]) -> Vec<T> {
    let mut out = items.to_vec();
    for i in (1..out.len()).rev() {
        out.swap(i, r.below(i as u64 + 1) as usize);
    }
    out
}

/// A claim about sets of numerals the claim writes.
fn numerals(r: &mut Random, g: &Grammar) -> (Node, Verdict) {
    let count = SIZES[r.below(4) as usize];
    let twice = count >= 2 && r.below(6) == 0;
    let vs = values(r, count, twice);
    let set =
        |g: &Grammar, vs: &[i64]| listed(g, vs.iter().map(|v| number(g, *v)).collect());
    match r.below(5) {
        // t ∈ S or t ∉ S.
        0 => {
            let t = if r.below(2) == 0 {
                vs[r.below(count as u64) as usize]
            } else {
                value(r)
            };
            let inside = vs.contains(&t);
            let said_in = r.below(2) == 0;
            let pattern = if said_in { "_ ∈ _" } else { "_ ∉ _" };
            (
                made(g, pattern, vec![number(g, t), set(g, &vs)]),
                verdict(inside == said_in),
            )
        }
        // |S| = n, a value listed twice counted once.
        1 => {
            let things = distinct(&vs).len() as i64;
            let n = (things + [0, 0, 1, -1][r.below(4) as usize]).max(0);
            let claim = equal(g, size(g, set(g, &vs)), number(g, n));
            (claim, verdict(n == things))
        }
        // Two listings, the second the first's values in another order, or
        // with one changed.
        2 => {
            let mut other = shuffled(r, &vs);
            if r.below(2) == 0 {
                let at = r.below(other.len() as u64) as usize;
                other[at] = value(r);
            }
            let same = {
                let (mut a, mut b) = (distinct(&vs), distinct(&other));
                a.sort();
                b.sort();
                a == b
            };
            (equal(g, set(g, &vs), set(g, &other)), verdict(same))
        }
        // {x ∈ S : x is even} = T, or its size.
        _ => {
            let vs = distinct(&vs);
            let even = r.below(2) == 0;
            let word = if even { "_ is even" } else { "_ is odd" };
            let kept: Vec<i64> = vs
                .iter()
                .copied()
                .filter(|v| (v.rem_euclid(2) == 0) == even)
                .collect();
            let x = || Node::name(Sort::of("number"), "x");
            let builder = made(
                g,
                "{_ ∈ _ : _}",
                vec![x(), set(g, &vs), made(g, word, vec![x()])],
            );
            if r.below(2) == 0 {
                let n = (kept.len() as i64 + [0, 0, 1, -1][r.below(4) as usize]).max(0);
                let claim = equal(g, size(g, builder), number(g, n));
                (claim, verdict(n == kept.len() as i64))
            } else {
                let mut said = shuffled(r, &kept);
                if r.below(2) == 0 {
                    if said.is_empty() || r.below(2) == 0 {
                        let more = vs[r.below(vs.len() as u64) as usize];
                        if !said.contains(&more) && said.len() < 4 {
                            said.push(more);
                        }
                    } else {
                        said.pop();
                    }
                }
                let holds = {
                    let (mut a, mut b) = (kept.clone(), said.clone());
                    a.sort();
                    b.sort();
                    a == b
                };
                (equal(g, builder, set(g, &said)), verdict(holds))
            }
        }
    }
}

const VERTICES: [&str; 4] = ["A", "B", "C", "D"];
const EDGES: [&str; 4] = ["b₁", "b₂", "b₃", "b₄"];

/// A claim about a multigraph a `let` line lists, and whether the step
/// cites that line: a vertex the claim says is in a list it writes is seen
/// there without it, and inspection uses every line it cites.
fn graph(r: &mut Random, g: &Grammar) -> (String, Node, Verdict, bool) {
    let vertices = &VERTICES[..3 + r.below(2) as usize];
    let edges = &EDGES[..SIZES[r.below(4) as usize]];
    let ends: Vec<(usize, usize)> = edges
        .iter()
        .map(|_| {
            let a = r.below(vertices.len() as u64) as usize;
            let b =
                (a + 1 + r.below(vertices.len() as u64 - 1) as usize) % vertices.len();
            (a, b)
        })
        .collect();
    let line = format!(
        "let G be the undirected multigraph with distinct vertices V = {{{}}} and distinct edges E = {{{}}}, where {}",
        vertices.join(", "),
        edges.join(", "),
        edges
            .iter()
            .zip(&ends)
            .map(|(e, (a, b))| format!("{e} joins {} and {}", vertices[*a], vertices[*b]))
            .collect::<Vec<_>>()
            .join(", ")
    );
    let names =
        |g: &Grammar, ns: &[&str]| listed(g, ns.iter().map(|n| name(n)).collect());
    let v = r.below(vertices.len() as u64) as usize;
    let incident: Vec<&str> = edges
        .iter()
        .zip(&ends)
        .filter(|(_, (a, b))| *a == v || *b == v)
        .map(|(e, _)| *e)
        .collect();
    let x = || Node::name(Sort::of("object"), "x");
    let builder = || {
        made(
            g,
            "{_ ∈ _ : _}",
            vec![
                x(),
                name("E"),
                made(g, "_ is incident with _", vec![name(vertices[v]), x()]),
            ],
        )
    };
    let (claim, holds, cites) = match r.below(3) {
        // The edges at a vertex.
        0 => {
            let mut said = shuffled(r, &incident);
            if r.below(2) == 0 {
                let other = edges[r.below(edges.len() as u64) as usize];
                if said.contains(&other) {
                    said.retain(|e| *e != other);
                } else {
                    said.push(other);
                }
            }
            let holds = {
                let (mut a, mut b) = (incident.clone(), said.clone());
                a.sort();
                b.sort();
                a == b
            };
            (equal(g, builder(), names(g, &said)), holds, true)
        }
        // How many there are.
        1 => {
            let n = (incident.len() as i64 + [0, 0, 1, -1][r.below(4) as usize]).max(0);
            (
                equal(g, size(g, builder()), number(g, n)),
                n == incident.len() as i64,
                true,
            )
        }
        // A vertex in a list of vertices.
        _ => {
            let some: Vec<&str> = shuffled(r, vertices)
                .into_iter()
                .take(1 + r.below(vertices.len() as u64) as usize)
                .collect();
            let t = vertices[r.below(vertices.len() as u64) as usize];
            let said_in = r.below(2) == 0;
            let pattern = if said_in { "_ ∈ _" } else { "_ ∉ _" };
            let holds = some.contains(&t) == said_in;
            (
                made(g, pattern, vec![name(t), names(g, &some)]),
                holds,
                !(holds && said_in),
            )
        }
    };
    (line, claim, verdict(holds), cites)
}

/// A claim for `inspection`, drawn and judged.
pub fn claim(r: &mut Random, g: &Grammar) -> Drawn {
    let (header, claim, verdict, cites) = if r.below(2) == 0 {
        let (claim, verdict) = numerals(r, g);
        (Vec::new(), claim, verdict, false)
    } else {
        let (line, claim, verdict, cites) = graph(r, g);
        (vec![line], claim, verdict, cites)
    };
    let justification = if cites {
        "inspection, from H1".to_string()
    } else {
        "inspection".to_string()
    };
    let written = g.print(&claim);
    Drawn {
        header,
        shown: written.clone(),
        written,
        justification,
        verdict,
    }
}
