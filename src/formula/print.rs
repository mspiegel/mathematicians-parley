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
use super::notation::{binds_tighter, Notation, Part, Tighter};

impl Grammar {
    /// The node as page text.
    pub fn print(&self, node: &Node) -> String {
        if node.children.is_empty() {
            return node.text.clone();
        }
        // A negation its record spells as one pattern: `a ≠ b`.
        if node.notation == "logical-not" && node.children.len() == 1 {
            let inner = &node.children[0];
            if let Some(n) = self.notations.iter().find(|n| {
                n.folds.is_some()
                    && n.name == inner.notation
                    && n.literal == inner.text
                    && holes(n) == inner.children.len()
            }) {
                return self.fill(n, &inner.children);
            }
        }
        // A set the page names in words and never writes, filled by the
        // spelling that names it: `q ∈ polynomials` is `q is a polynomial`.
        for n in &self.notations {
            let Some(f) = &n.fill else { continue };
            let at = f.hole.saturating_sub(1);
            let named = node
                .children
                .get(at)
                .is_some_and(|c| c.notation == f.name && c.children.is_empty());
            if n.stands_under == node.notation
                && n.literal == node.text
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
        match self.plain(node) {
            Some(n) => self.fill(n, &node.children),
            None => {
                let inner: Vec<String> =
                    node.children.iter().map(|c| self.print(c)).collect();
                format!("{}({})", node.notation, inner.join(", "))
            }
        }
    }

    /// The plain pattern a node of this notation and literal is written by,
    /// where it has one: what each hole takes and what it yields.
    pub fn written_by(&self, notation: &str, literal: &str) -> Option<&Notation> {
        self.notations.iter().find(|n| {
            n.name == notation
                && n.literal == literal
                && n.places.is_none()
                && n.nests.is_none()
                && n.bounds.is_none()
                && n.joins.is_none()
                && n.wrap.is_none()
                && n.fill.is_none()
        })
    }

    /// The pattern a node is written by: its own notation's, with its
    /// literal, as many holes as it has children, and none of the rules a
    /// second spelling adds.
    fn plain(&self, node: &Node) -> Option<&Notation> {
        self.notations.iter().find(|n| {
            n.name == node.notation
                && n.literal == node.text
                && n.folds.is_none()
                && n.places.is_none()
                && n.nests.is_none()
                && n.bounds.is_none()
                && n.joins.is_none()
                && n.wrap.is_none()
                && n.fill.is_none()
                && holes(n) == node.children.len()
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
            if c == '_' {
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
        if child.children.is_empty() || outer.level.is_empty() {
            return false;
        }
        let Some(inner) = self.plain(child).or_else(|| {
            self.notations
                .iter()
                .find(|n| n.name == child.notation && n.literal == child.text)
        }) else {
            return true;
        };
        let tighter =
            binds_tighter(&self.tighter, &inner.level, &outer.level) == Tighter::Yes;
        match edge {
            Edge::Left => {
                let level = self
                    .notations
                    .iter()
                    .find(|n| n.name == child.notation)
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

fn holes(n: &Notation) -> usize {
    n.parts.iter().filter(|p| p.is_hole()).count()
}
