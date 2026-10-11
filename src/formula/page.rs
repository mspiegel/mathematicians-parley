//! The one way page text becomes a formula (`GOALS.md` decision 18,
//! `GRAMMAR.md` "One front end").
//!
//! The skeleton reader cuts a line into its parts, and a part that is
//! formula text is `Written`, with the place it was written. The splitter
//! cuts it into `Sentence`s at its full stops and drops them, and the parser
//! reads one sentence into a tree. A `Sentence` is made only here, so a tree
//! read from text was read from what the splitter cut, the same way for
//! every tool.

use super::grammar::{parse, Grammar, Sorts};
use super::node::{Node, Sort};
use crate::outcome::{Checked, Problem};

/// Formula text as the skeleton reader cut it out of a line, and where.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Written {
    text: String,
    path: String,
    line: usize,
}

/// One sentence of a `Written`, without its full stop, and where it was
/// written.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Sentence {
    text: String,
    path: String,
    line: usize,
}

impl Written {
    pub fn new(text: impl Into<String>, path: &str, line: usize) -> Written {
        Written {
            text: text.into(),
            path: path.to_string(),
            line,
        }
    }

    /// The text with a line that continues it, as one claim written across
    /// two lines is one text.
    pub fn continued(&mut self, more: &str) {
        self.text.push(' ');
        self.text.push_str(more);
    }

    /// Formula text no file holds.
    pub fn here(text: impl Into<String>) -> Written {
        Written::new(text, "", 0)
    }

    /// The text as written, for a message or a key.
    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub fn line(&self) -> usize {
        self.line
    }

    /// The sentences, in the order written.
    ///
    /// A sentence ends at a full stop followed by any space, a line break
    /// included, so a claim written across two lines splits where it would
    /// written on one. The full stop is dropped, the last one included.
    pub fn sentences(&self) -> Vec<Sentence> {
        split(&self.text)
            .into_iter()
            .map(|text| Sentence {
                text,
                path: self.path.clone(),
                line: self.line,
            })
            .collect()
    }

    /// The one sentence of a part that is one formula: a term, a set, a
    /// value; a defect where it is not one.
    pub fn sentence(&self) -> Checked<Sentence> {
        let mut all = self.sentences();
        if all.len() != 1 {
            return Err(Problem::new(
                &self.path,
                self.line,
                format!(
                    "{:?} is {} sentences where one formula is written",
                    self.text,
                    all.len()
                ),
            ));
        }
        Ok(all.remove(0))
    }
}

impl std::fmt::Display for Written {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(&self.text)
    }
}

impl Sentence {
    /// The sentence as written, without its full stop.
    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub fn line(&self) -> usize {
        self.line
    }

    /// The tree the sentence reads as, with the sorts in scope.
    pub fn read(&self, g: &Grammar, sorts: &Sorts) -> Checked<Node> {
        parse(&self.text, g, sorts, &self.path, self.line)
    }
}

impl std::fmt::Display for Sentence {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(&self.text)
    }
}

/// A formula a tool makes from trees it has, by the notation the database
/// declares under `name` with the symbol or words `literal` (`+` of the two
/// `additive` patterns): the tree the parser builds for that notation over
/// those holes, made without text to read.
///
/// The code names the notations it makes, as `rules` names those it reads,
/// so one the database does not declare is a fault of the build, not of a
/// page.
pub fn made(g: &Grammar, name: &str, literal: &str, children: Vec<Node>) -> Node {
    let Some(n) = g.notations.iter().find(|n| {
        n.key() == name && n.literal == literal && n.holes.len() == children.len()
    }) else {
        panic!(
            "the database declares no notation {name} written {literal} of {} holes",
            children.len()
        );
    };
    Node::new(n.key(), Sort::of(&n.yields), children, &n.literal)
}

/// A formula the code writes with letters to fill, `x ≠ 0`, read as the
/// page's are, by the one parser; the letters are then filled with trees
/// (`matching::substitute`). The text is the code's own, fixed when it is
/// compiled, so no formula is put together as text and read: what fills it
/// is a tree.
pub fn template(text: &'static str, g: &Grammar, sorts: &Sorts) -> Checked<Node> {
    Written::here(text).sentence()?.read(g, sorts)
}

/// A template filled: each letter it writes read with the sort of the tree
/// that fills it, whatever the page calls that letter, and then that tree
/// put in its place. A template binds no letter of what fills it.
pub fn filled(
    text: &'static str,
    g: &Grammar,
    sorts: &Sorts,
    fills: &[(&str, &Node)],
) -> Checked<Node> {
    let mut local = sorts.clone();
    let mut put = crate::matching::Binding::new();
    for (letter, node) in fills {
        local.insert(letter.to_string(), node.sort.clone());
        put.insert(letter.to_string(), (*node).clone());
    }
    let made = template(text, g, &local)?;
    Ok(crate::matching::substitute_apart_by(
        &made,
        &put,
        &g.binders(),
    ))
}

/// The formula the notation written `pattern` builds over `children`, where
/// the database declares one; the words of the pattern are the page's, as
/// `be one-to-one` names the notation `_ : _ → _ is one-to-one`.
pub fn made_as(g: &Grammar, pattern: &str, children: Vec<Node>) -> Option<Node> {
    let n = g
        .notations
        .iter()
        .find(|n| n.pattern == pattern && n.holes.len() == children.len())?;
    Some(Node::new(
        n.key(),
        Sort::of(&n.yields),
        children,
        &n.literal,
    ))
}

/// A numeral, as the parser reads one.
pub fn numeral(digits: &str) -> Node {
    Node::leaf("numeral", Sort::of("number"), digits)
}

/// Several sentences as one claim: their conjunction, joined from the left
/// as a claim of several sentences is (`SYNTAX.md`); the one sentence where
/// there is one.
pub fn conjoined(g: &Grammar, said: Vec<Node>) -> Option<Node> {
    joined(g, "conjunction", "and", said)
}

/// Several formulas joined by "or", from the left, as `A or B or C` reads.
pub fn disjoined(g: &Grammar, said: Vec<Node>) -> Option<Node> {
    joined(g, "disjunction", "or", said)
}

fn joined(g: &Grammar, name: &str, literal: &str, mut said: Vec<Node>) -> Option<Node> {
    if said.is_empty() {
        return None;
    }
    let first = said.remove(0);
    Some(said.into_iter().fold(first, |whole, next| {
        made(g, name, literal, vec![whole, next])
    }))
}

/// The sentences of a text, each without its full stop.
fn split(text: &str) -> Vec<String> {
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
