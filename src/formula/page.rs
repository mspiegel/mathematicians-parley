//! The one way page text becomes a formula (`GOALS.md` decision 18,
//! `GRAMMAR.md` "One front end").
//!
//! The skeleton reader cuts a line into its parts, and a part that is
//! formula text is `Written`, with the place it was written. The splitter
//! cuts it into `Sentence`s at its full stops and drops them, and the parser
//! reads one sentence into a tree. A `Sentence` is made only here, so a tree
//! read from text was read from what the splitter cut, the same way for
//! every tool.

use std::sync::Arc;

use super::grammar::{fits, parse, wanted_reading, Grammar, Sorts};
use super::node::{Node, Sort};
use super::notation_id::Spelling;
use super::symbol::Symbol;
use super::token::Token;
use crate::notations::{AND, EQUALS, EQUAL_CHAIN, OR};
use crate::outcome::{Built, Checked, Declined, Problem, Route};

/// Formula text as the skeleton reader cut it out of a line, and where.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Written {
    text: String,
    /// Shared by the sentences cut from it, which each say where they are.
    path: Arc<str>,
    line: usize,
    /// Where the formula is one the page says in parts, the parts, from
    /// which its tree is made (`Made`).
    made: Option<Box<Made>>,
}

/// A formula a line says in parts it writes, whose tree is made from the
/// parts' trees and never from text.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Made {
    /// A membership said in words, `let A = …, a real number`: the term,
    /// and the set a kind of number names.
    Member { term: Written, set: Written },
    /// A define by cases: each value and the condition it is taken under,
    /// and the value `otherwise`, nested from the right into `_ if _, _
    /// otherwise` (`SYNTAX.md`).
    Cases {
        cases: Vec<Case>,
        otherwise: Written,
    },
    /// The domain of `for X ⊆ A`, the parts of A: 𝒫A.
    Parts { of: Written },
    /// The set a define's argument runs over, A of `for x ∈ A`, read where
    /// a set is wanted, as the right of ∈ is: `(a, b)` is the open interval
    /// there and not the pair of its ends (`wanted_reading`).
    Set { of: Written },
}

/// One line of a define by cases: its value, and the condition it is
/// taken under.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Case {
    pub value: Written,
    pub condition: Written,
}

/// One sentence of a `Written`, without its full stop, and where it was
/// written.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Sentence {
    text: String,
    path: Arc<str>,
    line: usize,
    made: Option<Box<Made>>,
}

impl Written {
    pub fn new(text: impl Into<String>, path: &str, line: usize) -> Written {
        Written {
            text: text.into(),
            path: Arc::from(path),
            line,
            made: None,
        }
    }

    /// `term ∈ set`, a membership no line writes, with the place of the
    /// line that says it. It reads as the tree of `x ∈ S` filled with the
    /// two parts' trees; its text is for a message and is never read.
    pub fn member(term: Written, set: Written, path: &str, line: usize) -> Written {
        Written {
            text: format!("{term} ∈ {set}"),
            path: Arc::from(path),
            line,
            made: Some(Box::new(Made::Member { term, set })),
        }
    }

    /// A define by cases, its lines as `text` writes them: each case's value
    /// and condition, and the value `otherwise`. It reads as `_ if _, _
    /// otherwise` nested from the right, made from the parts' trees.
    pub fn cases(
        text: impl Into<String>,
        cases: Vec<Case>,
        otherwise: Written,
        path: &str,
        line: usize,
    ) -> Written {
        Written {
            text: text.into(),
            path: Arc::from(path),
            line,
            made: Some(Box::new(Made::Cases { cases, otherwise })),
        }
    }

    /// The domain `for X ⊆ A` gives X, as `text` writes it: the parts of
    /// A, read as the tree of 𝒫A made from the tree of A.
    pub fn parts(
        text: impl Into<String>,
        of: Written,
        path: &str,
        line: usize,
    ) -> Written {
        Written {
            text: text.into(),
            path: Arc::from(path),
            line,
            made: Some(Box::new(Made::Parts { of })),
        }
    }

    /// The set `for x ∈ A` gives x, A as it is written, read where a set is
    /// wanted: `for t ∈ (a, b)` runs over the open interval.
    pub fn set(of: Written) -> Written {
        Written {
            text: of.text.clone(),
            path: of.path.clone(),
            line: of.line,
            made: Some(Box::new(Made::Set { of })),
        }
    }

    /// The text with a line that continues it, as one claim written across
    /// two lines is one text.
    pub fn continued(&mut self, more: &str) {
        self.text.push(' ');
        self.text.push_str(more);
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

    /// The sentences of a part that is a claim, in the order written:
    /// a step's claim, an `assume` or `suppose` line, a statement. Several
    /// mean their conjunction (`conjoined`). Every other part is one formula
    /// and is read with `formula`.
    ///
    /// A sentence ends at a full stop followed by any space, a line break
    /// included, so a claim written across two lines splits where it would
    /// written on one. The full stop is dropped, the last one included.
    pub fn sentences(&self) -> Vec<Sentence> {
        if self.made.is_some() {
            return vec![Sentence {
                text: self.text.to_string(),
                path: self.path.clone(),
                line: self.line,
                made: self.made.clone(),
            }];
        }
        split(&self.text)
            .into_iter()
            .map(|text| Sentence {
                text,
                path: self.path.clone(),
                line: self.line,
                made: None,
            })
            .collect()
    }

    /// The one sentence of a part that is one formula: a `let` line's
    /// introduction, a requires line's fact, a substitute's equation, a
    /// value, a term, a set; a defect where it is not one.
    pub fn formula(&self) -> Checked<Sentence> {
        let mut all = self.sentences();
        if all.len() != 1 {
            return Err(Problem::new(
                &*self.path,
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

    /// The text that alone decides what the sentence reads as, with given
    /// sorts: its own, where it is not made from parts (`Made`); None for
    /// one that is.
    pub fn deciding_text(&self) -> Option<&str> {
        self.made.is_none().then_some(self.text.as_str())
    }

    pub fn path(&self) -> &str {
        &self.path
    }

    pub fn line(&self) -> usize {
        self.line
    }

    /// The tree the sentence reads as, with the sorts in scope.
    /// A reading that waits on a letter's sort is a defect here, where the
    /// sorts are what the lines say.
    pub fn read(&self, g: &Grammar, sorts: &Sorts) -> Checked<Node> {
        match self.read_so_far(g, sorts)? {
            Built(node) => Ok(node),
            Declined(why) => Err(why.into_problem(&*self.path, self.line)),
        }
    }

    /// The tree the sentence reads as with the sorts found so far, while
    /// they are still being found (`sorts::infer`): it declines where the
    /// reading waits on the sort of a letter nothing has given one yet,
    /// `s(t)` before anything says whether s is a function or a number.
    pub fn read_so_far(&self, g: &Grammar, sorts: &Sorts) -> Checked<Route<Node>> {
        let Some(made) = self.made.as_deref() else {
            return parse(&self.text, g, sorts, &self.path, self.line);
        };
        let mut read = Vec::new();
        for part in parts_of(made) {
            match part.formula()?.read_so_far(g, sorts)? {
                Built(node) => read.push(node),
                waits => return Ok(waits),
            }
        }
        made_of(made, read, g, sorts).map(Built)
    }
}

/// The parts a formula said in parts is read from, each one formula the
/// page writes, in the order `made_of` takes their trees.
fn parts_of(made: &Made) -> Vec<&Written> {
    match made {
        Made::Member { term, set } => vec![term, set],
        Made::Cases { cases, otherwise } => cases
            .iter()
            .flat_map(|c| [&c.value, &c.condition])
            .chain([otherwise])
            .collect(),
        Made::Parts { of } | Made::Set { of } => vec![of],
    }
}

/// The tree of a formula said in parts, from the parts' trees in the order
/// `parts_of` gives them.
fn made_of(
    made: &Made,
    mut read: Vec<Node>,
    g: &Grammar,
    sorts: &Sorts,
) -> Checked<Node> {
    match made {
        Made::Member { .. } => {
            let [term, set] = <[Node; 2]>::try_from(read).expect("a term and a set");
            filled("x ∈ S", g, sorts, &[("x", &term), ("S", &set)])
        }
        Made::Parts { .. } => filled("𝒫A", g, sorts, &[("A", &read[0])]),
        Made::Set { .. } => {
            let set = read.pop().expect("the set");
            if fits("set", &set.sort) {
                return Ok(set);
            }
            Ok(wanted_reading(g, &set, "set").unwrap_or(set))
        }
        Made::Cases { .. } => {
            let mut term = read.pop().expect("the value otherwise");
            while let (Some(condition), Some(value)) = (read.pop(), read.pop()) {
                term = filled(
                    "a if c, b otherwise",
                    g,
                    sorts,
                    &[("a", &value), ("c", &condition), ("b", &term)],
                )?;
            }
            Ok(term)
        }
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
pub fn made(g: &Grammar, spelling: Spelling, children: Vec<Node>) -> Node {
    let Some(n) = g
        .notations
        .iter()
        .find(|n| n.spelling() == spelling && n.holes.len() == children.len())
    else {
        panic!(
            "the database declares no notation {} written {} of {} holes",
            spelling.notation.name(),
            spelling.text(),
            children.len()
        );
    };
    Node::of(n.spelling(), Sort::of(&n.yields), children)
}

/// The tokens the front end lexes a written part into, for a question about
/// how it is written rather than what it says: which names it writes, or
/// whether a quantifier writes a bound in place of its set, which reads as
/// the same tree as the long form. Lexing is the parser's first stage, so
/// this is the same reading, stopped before the tree.
pub fn tokens(written: &Written, g: &Grammar) -> Checked<Vec<Token>> {
    if let Some(made) = written.made.as_deref() {
        return parts_of(made)
            .into_iter()
            .map(|part| tokens(part, g))
            .collect::<Checked<Vec<_>>>()
            .map(|all| all.into_iter().flatten().collect());
    }
    written
        .sentences()
        .iter()
        .map(|s| g.tokens(s.text(), s.path(), s.line()))
        .collect::<Checked<Vec<_>>>()
        .map(|all| all.iter().flat_map(|t| t.iter().cloned()).collect())
}

/// What the page reads `node` as, printed: a tree a tool built, read back
/// as the page would read its printed form with `sorts`. It answers a
/// question about the printer and the notations, whether a tree is one the
/// page writes as itself (`|x − c|` is, of two numbers, and `|xc|` is a
/// distance between points); the printed text is no page's, and is read
/// nowhere else.
pub fn read_back(g: &Grammar, node: &Node, sorts: &Sorts) -> Checked<Node> {
    Written::new(g.print(node), "", 0).formula()?.read(g, sorts)
}

/// A formula the code writes with letters to fill, `x ≠ 0`, read as the
/// page's are, by the one parser; the letters are then filled with trees
/// (`matching::substitute_apart`). The text is the code's own, fixed when it is
/// compiled, so no formula is put together as text and read: what fills it
/// is a tree.
pub fn template(text: &'static str, g: &Grammar, sorts: &Sorts) -> Checked<Node> {
    Written::new(text, "", 0).formula()?.read(g, sorts)
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
        put.insert(Symbol::of(letter), (*node).clone());
    }
    let made = template(text, g, &local)?;
    Ok(crate::matching::substitute_apart_by(
        &made,
        &put,
        &g.binders(),
    ))
}

/// `a rel b`, and `a ≡ b (mod n)` for a congruence, as a chain's link
/// claims it (`GRAMMAR.md`, calculation chains); a defect for a relation a
/// chain does not join by, a `≡` with no modulus, or a modulus on any other
/// relation.
pub fn related(
    g: &Grammar,
    sorts: &Sorts,
    relation: &str,
    a: &Node,
    b: &Node,
    modulus: Option<&Node>,
    at: (&str, usize),
) -> Checked<Node> {
    let terms = [("a", a), ("b", b)];
    let form = match (relation, modulus) {
        ("=", None) => "a = b",
        ("≤", None) => "a ≤ b",
        ("<", None) => "a < b",
        ("≥", None) => "a ≥ b",
        (">", None) => "a > b",
        ("≡", Some(n)) => {
            return filled("a ≡ b (mod n)", g, sorts, &[("a", a), ("b", b), ("n", n)]);
        }
        ("≡", None) => {
            return Err(Problem::new(at.0, at.1, "a ≡ line says its modulus"));
        }
        (_, Some(_)) => {
            return Err(Problem::new(at.0, at.1, "only a ≡ line says a modulus"));
        }
        _ => {
            return Err(Problem::new(
                at.0,
                at.1,
                format!(
                    "a chain line joins by =, ≤, <, ≥, > or ≡, and not by {relation:?}"
                ),
            ));
        }
    };
    filled(form, g, sorts, &terms)
}

/// The formula the notation written `pattern` builds over `children`, where
/// the database declares one; the words of the pattern are the page's, as
/// `be one-to-one` names the notation `_ : _ → _ is one-to-one`.
pub fn made_as(g: &Grammar, pattern: &str, children: Vec<Node>) -> Option<Node> {
    let n = g
        .notations
        .iter()
        .find(|n| n.pattern == pattern && n.holes.len() == children.len())?;
    let node = Node::of(n.spelling(), Sort::of(&n.yields), children);
    // A pattern declared as the negation of another builds the other and
    // wraps it, as the parser builds it: `a ≠ b` is not (a = b).
    Some(match n.fold {
        Some(fold) => Node::of(fold, Sort::of("formula"), vec![node]),
        None => node,
    })
}

/// A numeral, as the parser reads one.
pub fn numeral(digits: &str) -> Node {
    Node::numeral(digits)
}

/// Several sentences as one claim: their conjunction, joined from the left
/// as a claim of several sentences is (`SYNTAX.md`); the one sentence where
/// there is one.
pub fn conjoined(g: &Grammar, said: Vec<Node>) -> Option<Node> {
    joined(g, AND, said)
}

/// What a chain of equations states: the equation between each term and
/// the next, `a = b` and `b = c` of `a = b = c` (`SYNTAX.md`). None for any
/// other node.
pub fn chain_links(g: &Grammar, node: &Node) -> Option<Vec<Node>> {
    (node.notation() == EQUAL_CHAIN).then(|| {
        node.children
            .windows(2)
            .map(|two| made(g, EQUALS, two.to_vec()))
            .collect()
    })
}

/// What a line claiming a chain of equations supplies: the equation between
/// any two of its terms, `a = c` of `a = b = c` as well as its links
/// (`SYNTAX.md`). None for any other node.
pub fn chain_pairs(g: &Grammar, node: &Node) -> Option<Vec<Node>> {
    if node.notation() != EQUAL_CHAIN {
        return None;
    }
    let terms = &node.children;
    let mut pairs = Vec::new();
    for (i, first) in terms.iter().enumerate() {
        for second in &terms[i + 1..] {
            pairs.push(made(g, EQUALS, vec![first.clone(), second.clone()]));
        }
    }
    Some(pairs)
}

/// Several formulas joined by "or", from the left, as `A or B or C` reads.
pub fn disjoined(g: &Grammar, said: Vec<Node>) -> Option<Node> {
    joined(g, OR, said)
}

fn joined(g: &Grammar, by: Spelling, mut said: Vec<Node>) -> Option<Node> {
    if said.is_empty() {
        return None;
    }
    let first = said.remove(0);
    Some(
        said.into_iter()
            .fold(first, |whole, next| made(g, by, vec![whole, next])),
    )
}

/// The sentences of a text, each without its full stop.
fn split(text: &str) -> Vec<String> {
    let text = str::trim(text);
    let mut pieces: Vec<&str> = Vec::new();
    let mut start = 0;
    let mut chars = text.char_indices().peekable();
    let mut before = None;
    while let Some((at, c)) = chars.next() {
        if c.is_whitespace() && before == Some('.') {
            while chars.next_if(|(_, w)| w.is_whitespace()).is_some() {}
            pieces.push(&text[start..at]);
            start = chars.peek().map_or(text.len(), |&(next, _)| next);
            before = None;
            continue;
        }
        before = Some(c);
    }
    pieces.push(&text[start..]);
    pieces
        .into_iter()
        .map(|p| str::trim(str::trim(p).trim_end_matches('.')).to_string())
        .filter(|p| !p.is_empty())
        .collect()
}
