//! A kernel term said back in the page's notation, for a message.
//!
//! The elaborator holds terms as set.mm writes them, and a message naming
//! one in that spelling, `( p ` x ) e. RR`, makes the reader translate it.
//! Each notation's `target` says what kernel term its pattern builds, holes
//! numbered, so the same table read the other way says which pattern a term
//! came from: the term is matched against each target, what fills each hole
//! is said back the same way, and the tree is printed (`Grammar::print`).
//! A name is the page name the proof gave the kernel term, a numeral its
//! digits, and a library function its application.
//!
//! A term no target reads, as a lemma's own construct may be, is said in
//! the kernel's spelling whole: half a translation would read as page text
//! and mean something else.

use crate::formula::{Node, Sort};
use crate::mm::kernel::Term;
use crate::outcome::Checked;
use crate::rules::NUMERALS;
use crate::targets::{is_context, is_hole};

use super::state::Elaborator;

/// A `target` read as a tree: a hole, numbered from 1, a label applied to
/// what it takes, or a part of a structure a `let` line introduced, which
/// stands for the kernel term the theorem gave it (`@op`).
enum Pattern {
    Hole(usize),
    Apply(String, Vec<Pattern>),
    Fixed(String),
}

/// The digits of a numeral as set.mm writes it: a digit's label, or
/// decimals `; A B` with A the digits before the last.
fn numeral(term: &Term) -> Option<String> {
    let label = term.label()?;
    if let Some((digit, _)) = NUMERALS.iter().find(|(_, l)| *l == label) {
        return term.children().is_empty().then(|| digit.to_string());
    }
    if label == "cdc" && term.children().len() == 2 {
        let before = numeral(&term.children()[0])?;
        let last = numeral(&term.children()[1])?;
        return (last.len() == 1).then(|| format!("{before}{last}"));
    }
    None
}

/// One way to read a term: the target a pattern builds, the notation and
/// literal its node has, and for a library function the name it applies.
struct Reading {
    target: String,
    notation: String,
    literal: String,
    applies: Option<String>,
}

impl Elaborator<'_> {
    /// The term as page text, or None where some part of it has no page
    /// reading.
    pub fn spoken(&self, rpn: &str) -> Option<String> {
        let node = self.page_node(&self.to_term(rpn))?;
        Some(self.g.print(&node))
    }

    /// Each sentence read as the kernel term it is, said back, and read
    /// again; one that comes back as another term, or cannot be said, is
    /// kept in `said_back`.
    pub fn say_back(&mut self, sentences: &[String], line: usize) -> Checked<()> {
        self.aside(|me| me.said_back_each(sentences, line))
    }

    /// `f`, leaving nothing behind of what reading does: reading a sentence
    /// may give a bound letter a kernel letter, and what a test reads it
    /// reads only to compare.
    pub fn aside<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let kept = (
            self.names.clone(),
            self.bound_as.clone(),
            self.written_as.clone(),
            self.spare.clone(),
        );
        let out = f(self);
        (self.names, self.bound_as, self.written_as, self.spare) = kept;
        out
    }

    fn said_back_each(&mut self, sentences: &[String], line: usize) -> Checked<()> {
        for sentence in sentences {
            let node = self.read(sentence)?;
            let kernel = self.term(&node)?;
            let again = match self.spoken(&kernel) {
                Some(said) => {
                    let back = self.read(&said).and_then(|n| self.term(&n)).ok();
                    (back.as_deref() != Some(kernel.as_str())).then_some(said)
                }
                None => Some("(no page reading)".to_string()),
            };
            if let Some(said) = again {
                let path = self.thm.path.clone();
                if let Some(out) = &mut self.said_back {
                    out.push(format!(
                        "{path}:{line}  {sentence}  said back as  {said}"
                    ));
                }
            }
        }
        Ok(())
    }

    fn page_node(&self, term: &Term) -> Option<Node> {
        let rpn = self.rpn(term);
        // A name the proof gave this term; a part of a structure is held
        // under a name no page writes (`@op`), and is read by its notation.
        let named = |page: &str| {
            let sort = self.sorts_now.get(page).cloned().unwrap_or_else(Sort::none);
            Node::leaf("name", sort, page)
        };
        if let Some((page, _)) = self
            .names
            .iter()
            .find(|(page, kernel)| **kernel == rpn && !is_context(page))
        {
            return Some(named(page));
        }
        // A letter a binder introduced, by the name the page bound it under.
        if let Some(letter) = term.variable() {
            return Some(named(
                self.written_as.get(&rpn).map_or(letter, String::as_str),
            ));
        }
        let label = term.label()?;
        let kids = term.children();
        // A letter a binder introduced, used as a class.
        if label == "cv" && kids.len() == 1 {
            return self.page_node(&kids[0]);
        }
        if let Some(digits) = numeral(term) {
            return Some(Node::leaf("numeral", Sort::of("number"), &digits));
        }
        // Every pattern that builds a term of this shape, the one saying most
        // of it first: ∠PQR is an absolute value too, and reads as an angle.
        let mut readings: Vec<Reading> = Vec::new();
        for f in self.g.functions.values() {
            let notation = if f.arity == 1 {
                "application"
            } else {
                "application-to-two"
            };
            let Some(literal) = self.literals.get(notation).and_then(|l| l.first())
            else {
                continue;
            };
            readings.push(Reading {
                target: f.builds.clone(),
                notation: notation.to_string(),
                literal: literal.clone(),
                applies: Some(f.name.clone()),
            });
        }
        for (notation, entries) in &self.terms {
            for (at, entry) in entries.iter().enumerate() {
                let Some(target) = entry else { continue };
                let Some(literal) = self.literals.get(notation).and_then(|l| l.get(at))
                else {
                    continue;
                };
                if self.g.written_by(notation, literal).is_some() {
                    readings.push(Reading {
                        target: target.clone(),
                        notation: notation.clone(),
                        literal: literal.clone(),
                        applies: None,
                    });
                }
            }
        }
        readings
            .sort_by_key(|r| std::cmp::Reverse(r.target.split_whitespace().count()));
        for r in &readings {
            let Some(holes) = self.matched(&r.target, term) else {
                continue;
            };
            let Some(mut children) = holes
                .iter()
                .map(|h| self.page_node(h))
                .collect::<Option<Vec<Node>>>()
            else {
                continue;
            };
            if let Some(name) = &r.applies {
                children.insert(0, Node::leaf("name", Sort::none(), name));
            }
            let node = Node::new(&r.notation, Sort::none(), children, &r.literal);
            // A reading is the page's only where the page reads it back as
            // itself: |xc| is a distance between points, and of two numbers
            // the page reads nothing, so |x − c| is the reading.
            let back = self.read(&self.g.print(&node));
            if back.is_ok_and(|b| b.shape() == node.shape()) {
                return Some(node);
            }
        }
        None
    }

    /// What fills each hole of `target` where the term is what it builds,
    /// in hole order; None where it is not.
    fn matched(&self, target: &str, term: &Term) -> Option<Vec<Term>> {
        let pattern = self.pattern_tree(target)?;
        let mut holes: Vec<Option<Term>> = Vec::new();
        if !self.fills_target(&pattern, term, &mut holes) {
            return None;
        }
        holes.into_iter().collect()
    }

    /// A target as a tree, by each label's arity; None for one that takes a
    /// part of a structure this theorem has none of.
    fn pattern_tree(&self, target: &str) -> Option<Pattern> {
        let mut stack: Vec<Pattern> = Vec::new();
        for token in target.split_whitespace() {
            if is_context(token) {
                stack.push(Pattern::Fixed(self.names.get(token)?.clone()));
                continue;
            }
            if is_hole(token) {
                stack.push(Pattern::Hole(token[1..].parse().ok()?));
                continue;
            }
            let sig = self.b.sigs.get(token)?;
            // A letter the target binds itself, as `s` in "u is an upper
            // bound of S", is that letter in the term, which reads it as a
            // variable.
            if sig.kind == crate::mm::Kind::Float {
                stack.push(Pattern::Fixed(token.to_string()));
                continue;
            }
            let arity = sig.floats.len();
            if stack.len() < arity {
                return None;
            }
            let args = stack.split_off(stack.len() - arity);
            stack.push(Pattern::Apply(token.to_string(), args));
        }
        if stack.len() == 1 {
            stack.pop()
        } else {
            None
        }
    }

    fn fills_target(
        &self,
        pattern: &Pattern,
        term: &Term,
        holes: &mut Vec<Option<Term>>,
    ) -> bool {
        match pattern {
            Pattern::Hole(n) => {
                if holes.len() < *n {
                    holes.resize(*n, None);
                }
                match &holes[n - 1] {
                    Some(held) => self.rpn(held) == self.rpn(term),
                    None => {
                        holes[n - 1] = Some(term.clone());
                        true
                    }
                }
            }
            Pattern::Fixed(rpn) => self.rpn(term) == *rpn,
            Pattern::Apply(label, args) => {
                term.label() == Some(label.as_str())
                    && term.children().len() == args.len()
                    && args
                        .iter()
                        .zip(term.children())
                        .all(|(a, t)| self.fills_target(a, t, holes))
            }
        }
    }
}
