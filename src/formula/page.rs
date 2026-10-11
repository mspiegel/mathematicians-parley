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
use super::node::Node;
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
