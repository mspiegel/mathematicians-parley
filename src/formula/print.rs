//! A tree written back as the page writes it.
//!
//! A message that names a formula the tools built, rather than one cut from
//! the page, prints it: `requires −f(c) ∈ ℝ` from the membership the
//! instantiation asks. Each node is written by the plain pattern of the
//! notation that built it, with its children in the holes, and a negation is
//! written by the pattern its record declares for it, so `not (a = b)` comes
//! out `a ≠ b`. A child at the edge of a pattern is bracketed where the
//! parser would otherwise read it into a different tree, by the same
//! precedence the parser uses; a child between two tokens never is.

use super::grammar::Grammar;
use super::node::Node;
use super::notation::{binds_tighter, Notation, Part, Tighter, RAISED_HOLE};
use super::notation_id::Spelling;
use super::token::raised;

impl Grammar {
    /// The node as page text.
    pub fn print(&self, node: &Node) -> String {
        if node.children.is_empty() {
            return node.text.to_string();
        }
        // A negation its record spells as one pattern: `a ≠ b`.
        if node.notation() == crate::notations::LOGICAL_NOT && node.children.len() == 1
        {
            let inner = &node.children[0];
            if let Some(n) = self.notations.iter().find(|n| {
                n.folds.is_some() && n.writes(inner) && holes(n) == inner.children.len()
            }) {
                return self.fill(n, &inner.children);
            }
        }
        // A set the page names in words and never writes, filled by the
        // spelling that names it: `q ∈ polynomials` is `q is a polynomial`.
        for n in &self.notations {
            let Some(f) = &n.fill else { continue };
            let at = f.hole.saturating_sub(1);
            let named = node.children.get(at).is_some_and(|c| {
                c.notation() == f.spelling.notation && c.children.is_empty()
            });
            if n.spelling() == node.spelling()
                && named
                && holes(n) + 1 == node.children.len()
            {
                let rest: Vec<Node> = node
                    .children
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != at)
                    .map(|(_, c)| c.clone())
                    .collect();
                return self.fill(n, &rest);
            }
        }
        // A set the page never writes alone, joined from two holes by the
        // spelling that writes it: "there is f ∈ (the functions from X to
        // Y) with …" is `there is f : X → Y with …`.
        if let Some((n, parts)) = self.joined_set(node) {
            return self.fill(n, &parts);
        }
        match self.plain(node) {
            Some(n) => self.fill(n, &node.children),
            None => {
                let inner: Vec<String> =
                    node.children.iter().map(|c| self.print(c)).collect();
                format!("{}({})", node.notation_name(), inner.join(", "))
            }
        }
    }

    /// The spelling that joins two of its holes into a set where `node`
    /// holds that set, and the children it is filled with: the node's own,
    /// the set taken apart into the two it was joined from. None where no
    /// spelling joins a set the node holds.
    fn joined_set(&self, node: &Node) -> Option<(&Notation, Vec<Node>)> {
        self.notations.iter().find_map(|n| {
            let j = n.joins.as_ref()?;
            let at = j.first - 1;
            let set = node.children.get(at)?;
            let fits = n.spelling() == node.spelling()
                && joins_a_set(n)
                && holes(n) == node.children.len() + 1
                && set.spelling() == j.by.spelling
                && set.children.len() == 2;
            if !fits {
                return None;
            }
            let mut parts = node.children.clone();
            parts.splice(at..=at, set.children.iter().cloned());
            Some((n, parts))
        })
    }

    /// The plain pattern a node of this notation and literal is written by,
    /// where it has one: what each hole takes and what it yields.
    pub fn written_by(&self, spelling: Spelling) -> Option<&Notation> {
        let literal = spelling.text();
        self.notations.iter().find(|n| {
            n.record_id == spelling.notation
                && *n.literal == *literal
                && n.places.is_none()
                && n.nests.is_none()
                && n.bounds.is_none()
                && n.joins.is_none()
                && n.wrap.is_none()
                && n.fill.is_none()
        })
    }

    /// The pattern of this record and literal that joins two neighbouring
    /// holes into a set the page never writes alone, `there is _ : _ → _
    /// with _`, where it has one.
    pub fn joined_by(&self, spelling: Spelling) -> Option<&Notation> {
        let literal = spelling.text();
        self.notations.iter().find(|n| {
            n.record_id == spelling.notation && *n.literal == *literal && joins_a_set(n)
        })
    }

    /// The pattern a node is written by: its own notation's, with its
    /// literal, as many holes as it has children or fewer where its last
    /// one repeats, and none of the rules a second spelling adds.
    fn plain(&self, node: &Node) -> Option<&Notation> {
        self.notations.iter().find(|n| {
            n.writes(node)
                && n.folds.is_none()
                && n.places.is_none()
                && n.nests.is_none()
                && n.bounds.is_none()
                && n.joins.is_none()
                && n.wrap.is_none()
                && n.fill.is_none()
                && (holes(n) == node.children.len()
                    || (n.repeat.is_some() && holes(n) < node.children.len()))
        })
    }

    /// The pattern with each child in its hole, as the record writes the
    /// pattern's spacing.
    fn fill(&self, n: &Notation, children: &[Node]) -> String {
        let last = n.parts.len() - 1;
        let mut written: Vec<String> = Vec::new();
        let mut at = 0;
        for (i, part) in n.parts.iter().enumerate() {
            match part {
                Part::Lit(_) => {}
                Part::Raised => {
                    written.push(raised(&children[at].text));
                    at += 1;
                }
                // The hole that repeats takes every child from here on, each
                // after the separator spaced as the pattern writes it before
                // that hole: `, ` in {_, _, _, _}, ` = ` in _ = _ = _.
                Part::Hole if n.repeat.as_ref().is_some_and(|r| r.hole == at + 1) => {
                    let each: Vec<String> =
                        children[at..].iter().map(|c| self.print(c)).collect();
                    written.push(each.join(before_last_hole(&n.pattern)));
                    at = children.len();
                }
                Part::Hole => {
                    let child = &children[at];
                    let text = self.print(child);
                    let edge = if i == 0 {
                        Some(Edge::Left)
                    } else if i == last {
                        Some(Edge::Right)
                    } else {
                        None
                    };
                    let bracket = edge.is_some_and(|e| self.brackets(n, child, e));
                    written.push(if bracket { format!("({text})") } else { text });
                    at += 1;
                }
            }
        }
        let mut out = String::new();
        let mut holes = written.into_iter();
        for c in n.pattern.chars() {
            if c == '_' || c == RAISED_HOLE {
                out.push_str(&holes.next().unwrap_or_default());
            } else {
                out.push(c);
            }
        }
        out
    }

    /// Whether a child at an edge of `outer` needs brackets, by the rules the
    /// parser reads it with (`expression`).
    ///
    /// On the left, the outer pattern extends a term only where the term's
    /// level binds tighter, or is the same level and the pattern chains to
    /// the left; a term with no level is extended freely. On the right, the
    /// term the hole reads stops at any pattern that competes with the outer
    /// one, ending in a hole or declaring a level, unless that pattern binds
    /// tighter or is the same level nesting to the right.
    fn brackets(&self, outer: &Notation, child: &Node, edge: Edge) -> bool {
        if child.children.is_empty() {
            return false;
        }
        // A pattern of no level that a term opens, as f(x) is, reads its
        // operand as the last name before its token, so a child ending in a
        // hole is bracketed to be the operand: (g ∘ f)(x), not g ∘ (f(x)).
        if outer.level.is_empty() {
            let ends_open = self
                .notations
                .iter()
                .find(|n| n.writes(child))
                .is_some_and(|n| n.parts.last().is_some_and(|p| p.is_hole()));
            return matches!(edge, Edge::Left) && ends_open;
        }
        let Some(inner) = self
            .plain(child)
            .or_else(|| self.notations.iter().find(|n| n.writes(child)))
        else {
            return true;
        };
        let tighter =
            binds_tighter(&self.tighter, &inner.level, &outer.level) == Tighter::Yes;
        match edge {
            Edge::Left => {
                let level = self
                    .notations
                    .iter()
                    .find(|n| n.record_id == child.notation())
                    .map(|n| n.level.as_str())
                    .unwrap_or("");
                if level.is_empty() {
                    return false;
                }
                let tighter =
                    binds_tighter(&self.tighter, level, &outer.level) == Tighter::Yes;
                let chains =
                    level == outer.level && outer.assoc.as_deref() == Some("left");
                !(tighter || chains)
            }
            Edge::Right => {
                let competes = inner.parts[inner.parts.len() - 1].is_hole()
                    || !inner.level.is_empty();
                let nests = inner.level == outer.level
                    && inner.assoc.as_deref() == Some("right");
                competes && !(tighter || nests)
            }
        }
    }
}

/// Which edge of a pattern a hole stands at.
#[derive(Clone, Copy)]
enum Edge {
    Left,
    Right,
}

/// Whether a pattern joins two neighbouring holes into a set, and adds no
/// other rule: "there is f : X → Y with …" joins X and Y into the functions
/// from X to Y. A join into a formula, "for all x ∈ S with A, B", is a
/// second spelling of what the plain pattern writes, and is not one.
fn joins_a_set(n: &Notation) -> bool {
    n.joins
        .as_ref()
        .is_some_and(|j| j.by.yields.starts_with("set") && j.then == j.first + 1)
        && n.places.is_none()
        && n.nests.is_none()
        && n.bounds.is_none()
        && n.wrap.is_none()
        && n.fill.is_none()
}

fn holes(n: &Notation) -> usize {
    n.parts.iter().filter(|p| p.fills()).count()
}

/// What a pattern writes between its last two holes, spacing included:
/// what stands between the children its last hole repeats over.
fn before_last_hole(pattern: &str) -> &str {
    let last = pattern.rfind('_').unwrap_or(pattern.len());
    let start = pattern[..last].rfind('_').map_or(0, |at| at + 1);
    &pattern[start..last]
}
