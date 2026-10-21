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

use indexmap::IndexMap;

use crate::formula::notation_id::Spelling;
use crate::formula::page::{read_back, Sentence};
use crate::formula::{wanted_reading, Node, Sort};
use crate::mm::kernel::Term;
use crate::mm::Rpn;
use crate::notations::{APPLICATION, APPLICATION_TO_TWO, SUPERSCRIPT};
use crate::outcome::Checked;
use crate::rules::NUMERALS;
use crate::targets::{is_context, is_hole, repeated};

use super::state::{fit, Binding, Elaborator};

/// A `target` read as a tree: a hole, numbered from 1, a label applied to
/// what it takes, or a part of a structure a `let` line introduced, which
/// stands for the kernel term the theorem gave it (`@op`).
enum Pattern {
    Hole(usize),
    Apply(String, Vec<Pattern>),
    Fixed(Rpn),
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
#[derive(Clone)]
struct Reading {
    target: String,
    /// The notation record's and its literal, which the node read back is
    /// of.
    spelling: Spelling,
    applies: Option<String>,
}

/// A reading of the grammar's, with where it stands among them, the order
/// that settles readings of one length.
pub(super) struct Ranked {
    reading: Reading,
    place: usize,
    /// For a list's pattern, what reads it at more elements than it writes.
    list: Option<ListReading>,
}

/// What reads a list's pattern at more elements: the holes it writes, the
/// target each further element adds, and that target's last label, which a
/// term holds once for each element it adds.
struct ListReading {
    holes: usize,
    building: String,
    last: String,
}

/// A list's pattern read at `count` elements, standing where its pattern
/// does.
struct ListAt {
    place: usize,
    count: usize,
    reading: Reading,
}

/// The order readings are tried in: the one saying most of the term first,
/// then by where its pattern stands, a list's at fewer elements first.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct ReadingOrder {
    longer: std::cmp::Reverse<usize>,
    place: usize,
    count: usize,
}

impl ReadingOrder {
    fn of(reading: &Reading, place: usize, count: usize) -> ReadingOrder {
        ReadingOrder {
            longer: std::cmp::Reverse(reading.target.split_whitespace().count()),
            place,
            count,
        }
    }
}

impl Elaborator<'_> {
    /// The term as page text, or None where some part of it has no page
    /// reading.
    pub fn spoken(&self, rpn: &Rpn) -> Option<String> {
        let node = self.page_node(&self.to_term(rpn))?;
        Some(self.g.print(&node))
    }

    /// Each sentence read as the kernel term it is, said back, and read
    /// again; one that comes back as another term, or cannot be said, is
    /// kept in `said_back`.
    pub fn say_back(&mut self, sentences: &[Sentence], line: usize) -> Checked<()> {
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

    fn said_back_each(&mut self, sentences: &[Sentence], line: usize) -> Checked<()> {
        for sentence in sentences {
            let node = self.read(sentence)?;
            let kernel = self.term(&node)?;
            let again = match self.page_node(&self.to_term(&kernel)) {
                Some(said) => {
                    // What the page would write, read as the page is read.
                    let back = read_back(self.g, &said, &self.sorts_now)
                        .and_then(|n| self.term(&n))
                        .ok();
                    (back.as_ref() != Some(&kernel)).then(|| self.g.print(&said))
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

    /// Every reading the grammar has, library functions first and then
    /// each notation's patterns, in the order they are tried
    /// (`ReadingOrder`), made once for an elaborator, since its grammar and
    /// targets do not change.
    pub(super) fn reading_table(&self) -> Vec<Ranked> {
        let mut table: Vec<Ranked> = Vec::new();
        for f in self.g.functions.values() {
            let notation = if f.arity == 1 {
                APPLICATION
            } else {
                APPLICATION_TO_TWO
            };
            let Some(&spelling) = self.literals.get(&notation).and_then(|l| l.first())
            else {
                continue;
            };
            table.push(Ranked {
                reading: Reading {
                    target: f.builds.clone(),
                    spelling,
                    applies: Some(f.name.clone()),
                },
                place: table.len(),
                list: None,
            });
        }
        for (notation, entries) in &self.terms {
            for (at, entry) in entries.iter().enumerate() {
                let Some(target) = entry else { continue };
                let Some(&spelling) =
                    self.literals.get(notation).and_then(|l| l.get(at))
                else {
                    continue;
                };
                let Some(written) = self.g.written_by(spelling) else {
                    continue;
                };
                let list = written.repeat.as_ref().and_then(|r| {
                    let last = r.building.split_whitespace().last()?;
                    Some(ListReading {
                        holes: written.holes.len(),
                        building: r.building.clone(),
                        last: last.to_string(),
                    })
                });
                table.push(Ranked {
                    reading: Reading {
                        target: target.clone(),
                        spelling,
                        applies: None,
                    },
                    place: table.len(),
                    list,
                });
            }
        }
        // A power to a numeral is written raised, t², as the page writes it
        // (the `superscript` record); `^` builds the same term, and reads
        // back any other exponent, which a raised one does not.
        for r in &mut table {
            if r.reading.spelling.notation == SUPERSCRIPT {
                r.place = 0;
            }
        }
        table.sort_by_key(|r| ReadingOrder::of(&r.reading, r.place, 0));
        table
    }

    pub(super) fn page_node(&self, term: &Term) -> Option<Node> {
        self.page_node_under(term, &IndexMap::new(), None)
    }

    /// `page_node` of a part of a term, inside binders that introduce the
    /// letters `bound`: a part is read back with them as names, as the page
    /// reads it inside its binder, so the i of {i ∈ X : P(i)} is a letter and
    /// not the imaginary unit. Each letter has the sort of what its binder's
    /// domain holds where the domain says, as the page reads it: the k of
    /// "there is k ∈ H" is an element of the group H is a set of, and g·k
    /// reads as the group's product. `want` is the category the place the
    /// part fills wants, where a notation's hole says: a reading the page
    /// gives only where a hole wants it (`wanted`) is taken only there, so
    /// x + i·y is the point (x, y) where a point is wanted and a sum
    /// anywhere else.
    fn page_node_under(
        &self,
        term: &Term,
        bound: &IndexMap<String, Sort>,
        want: Option<&str>,
    ) -> Option<Node> {
        let rpn = self.rpn(term);
        // A name the proof gave this term; a part of a structure is held
        // under a name no page writes (`@op`), and is read by its notation.
        let named = |page: &str| {
            let sort = self.sorts_now.get(page).cloned().unwrap_or_else(Sort::none);
            Node::name(sort, page)
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
                rpn.alone()
                    .and_then(|float| self.written_as.get(float))
                    .map_or(letter, String::as_str),
            ));
        }
        let label = term.label()?;
        let kids = term.children();
        // A letter a binder introduced, used as a class.
        if label == "cv" && kids.len() == 1 {
            return self.page_node_under(&kids[0], bound, want);
        }
        if let Some(digits) = numeral(term) {
            return Some(Node::numeral(&digits));
        }
        // Every pattern that builds a term of this shape, the one saying most
        // of it first: ∠PQR is an absolute value too, and reads as an angle.
        // A list is read at each length the term could hold: no more
        // elements past the pattern's than the term has of what each one
        // adds last, `cun` for {a, b, c, d, e}.
        let table = self.readings.get_or_init(|| self.reading_table());
        let mut lists: Vec<ListAt> = Vec::new();
        for ranked in table {
            let Some(list) = &ranked.list else { continue };
            let most = rpn.tokens().iter().filter(|t| **t == list.last).count();
            for count in list.holes + 1..=list.holes + most {
                lists.push(ListAt {
                    place: ranked.place,
                    count,
                    reading: Reading {
                        target: repeated(
                            &ranked.reading.target,
                            &list.building,
                            list.holes,
                            count,
                        ),
                        ..ranked.reading.clone()
                    },
                });
            }
        }
        let readings: Vec<&Reading> = if lists.is_empty() {
            table.iter().map(|r| &r.reading).collect()
        } else {
            let mut all: Vec<(ReadingOrder, &Reading)> = table
                .iter()
                .map(|r| (ReadingOrder::of(&r.reading, r.place, 0), &r.reading))
                .chain(lists.iter().map(|l| {
                    (ReadingOrder::of(&l.reading, l.place, l.count), &l.reading)
                }))
                .collect();
            all.sort_by_key(|(order, _)| *order);
            all.into_iter().map(|(_, r)| r).collect()
        };
        for r in readings {
            let written = self.g.written_by(r.spelling);
            let wanted = written.and_then(|n| n.wanted.as_deref());
            if wanted.is_some() && wanted != want {
                continue;
            }
            let Some(holes) = self.matched(&r.target, term) else {
                continue;
            };
            // What each part's place wants, from the notation's holes; a
            // function applied has its name in the first.
            let skip = usize::from(r.applies.is_some());
            let hole_wants: Vec<Option<&str>> = (0..holes.len())
                .map(|i| {
                    written
                        .and_then(|n| n.holes.get(i + skip))
                        .map(String::as_str)
                })
                .collect();
            // The letters this reading binds are names in its parts, of the
            // sort its domain's elements have where a hole holds one.
            let binding_at: Vec<usize> = self
                .binders
                .get(&r.spelling.notation)
                .into_iter()
                .flatten()
                .copied()
                .collect();
            let domain_holds = holes
                .iter()
                .enumerate()
                .filter(|(at, _)| !binding_at.contains(at))
                .filter_map(|(_, h)| self.page_node_under(h, bound, None))
                .filter(Node::is_name)
                .find_map(|n| self.sorts_now.get(n.text.as_str()).and_then(Sort::held))
                .unwrap_or_else(Sort::none);
            let mut inner = bound.clone();
            for at in &binding_at {
                if let Some(letter) = holes
                    .get(*at)
                    .and_then(|h| self.page_node_under(h, bound, None))
                {
                    if letter.is_name() {
                        inner.insert(letter.text.to_string(), domain_holds.clone());
                    }
                }
            }
            let Some(mut children) = holes
                .iter()
                .zip(&hole_wants)
                .map(|(h, w)| self.page_node_under(h, &inner, *w))
                .collect::<Option<Vec<Node>>>()
            else {
                continue;
            };
            if let Some(name) = &r.applies {
                children.insert(0, Node::name(Sort::none(), name));
            }
            let node = Node::of(r.spelling, Sort::none(), children);
            // A reading is the page's only where the page reads it back as
            // itself: |xc| is a distance between points, and of two numbers
            // the page reads nothing, so |x − c| is the reading.
            let mut sorts = self.sorts_now.clone();
            for (letter, sort) in bound {
                if sort.name().is_some() {
                    sorts.insert(letter.clone(), sort.clone());
                } else if !sorts.introduces(letter) {
                    sorts.unsettled.insert(letter.clone());
                }
            }
            let back = read_back(self.g, &node, &sorts);
            // A reading the page gives only where a hole wants it, the open
            // interval of `(a, b)`, is read back as that hole reads it.
            let back = back.map(|b| match wanted {
                Some(want) => wanted_reading(self.g, &b, want).unwrap_or(b),
                None => b,
            });
            if back.is_ok_and(|b| b.same_shape(&node)) {
                return Some(node);
            }
        }
        // A term no notation reads, said as the standard form puts it
        // (`rules::STANDARD`): set.mm's a =/= b is the page's not (a = b),
        // which the page says as a ≠ b.
        let [plain, _] = self.standard_rules();
        for rule in plain {
            if let Some(found) = fit(&rule.given, term, &Binding::new(), &rule.names) {
                if rule.gives.names().iter().all(|n| found.contains_key(&**n)) {
                    return self.page_node_under(
                        &rule.gives.substitute(&found),
                        bound,
                        want,
                    );
                }
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
                stack.push(Pattern::Fixed(Rpn::read(token)));
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
