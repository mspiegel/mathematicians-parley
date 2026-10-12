//! The values a citation gives the letters of what it cites, `v := t`.
//!
//! The letter on the left is the cited item's own, and the value on the
//! right is written in the citing proof's names, as they stand before any
//! value is given: `a := b/k, b := a/k` swaps the two, and `n := d, d := a`
//! puts the proof's d at n. So the values are read together or not at all.
//! The skeleton reader cuts them out of a line once, here, and keeps their
//! text to itself: what leaves this module is every value read with one
//! grammar and one set of sorts, or the tokens they are written in, never
//! one value's text for a tool to read after giving another.

use crate::formula::page::{tokens, Written};
use crate::formula::token::Token;
use crate::formula::{Grammar, Node, Sorts};
use crate::outcome::Checked;
use crate::regex;

// A value may itself contain a comma, as `e := gcd(a, b)` does, so the list
// is split at the commas that sit outside brackets rather than by a pattern
// that stops at the first one.
regex!(ASSIGN, r"^([^\s,]+)\s*:=\s*(.+)");
regex!(
    END,
    format!(
        r",\s*from\b|\s+in\s+(?:line\b|{}|[A-Z]+[0-9]*\b)",
        super::ITEM_PREFIX
    )
);
// What comes before the pairs: the item cited, after the names an `obtain`
// takes, `obtain q, r: thm:division-algorithm`, or `instantiate`.
regex!(
    HEAD,
    format!(
        r"^(?:obtain\s[^:]*:\s*)?(?:{}[^\s]+\s*|instantiate\s+)",
        super::ITEM_PREFIX
    )
);

/// The `v := t` a line writes, in order, as the skeleton reader cut them.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Values {
    given: Vec<Given>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Given {
    name: String,
    value: Written,
}

/// One value read: the cited item's letter, and the tree the proof's text
/// for it reads as.
#[derive(Clone, Debug)]
pub struct Value {
    pub name: String,
    pub value: Node,
    /// The value as written, for a message.
    pub shown: String,
}

impl Values {
    /// The values written in `text`, a justification or a requires line's
    /// reason, on `line` of `path`.
    ///
    /// An `instantiate` says where it lands, and that is a line, an item or
    /// a bare label: a value stops at whichever of them follows it, and `IH`
    /// is a label.
    pub(crate) fn cut(text: &str, path: &str, line: usize) -> Values {
        let mut body = match END.find(text) {
            Some(m) => &text[..m.start()],
            None => text,
        };
        if let Some(head) = HEAD.find(body) {
            body = &body[head.end()..];
        }
        let given = crate::matching::split_commas(body)
            .into_iter()
            .filter_map(|piece| ASSIGN.captures(str::trim(piece)))
            .map(|m| Given {
                name: str::trim(&m[1]).to_string(),
                value: Written::new(str::trim(&m[2]), path, line),
            })
            .collect();
        Values { given }
    }

    pub fn is_empty(&self) -> bool {
        self.given.is_empty()
    }

    /// The cited item's letters the values are given for, in order.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.given.iter().map(|g| g.name.as_str())
    }

    /// Every value, each read as one formula with the same grammar and
    /// sorts; a defect where one is not a formula that reads.
    pub fn read(&self, g: &Grammar, sorts: &Sorts) -> Checked<Vec<Value>> {
        self.given
            .iter()
            .map(|given| {
                Ok(Value {
                    name: given.name.clone(),
                    value: given.value.sentence()?.read(g, sorts)?,
                    shown: given.value.text().to_string(),
                })
            })
            .collect()
    }

    /// The tokens each value is written in, for a question about how the
    /// theorem is written, which names it writes (`sorts::written_tokens`);
    /// a value that does not lex is left out, as the elaborator reports a
    /// value that does not read.
    pub fn tokens(&self, g: &Grammar) -> Vec<Vec<Token>> {
        self.given
            .iter()
            .filter_map(|given| tokens(&given.value, g).ok())
            .collect()
    }
}
