//! Rewrites of a whole proof file that keep what each theorem says.
//!
//! A rewrite finds the formulas of a theorem with the readers the tools use:
//! the proof parser says which line is a hypothesis, a claim, a requires
//! line, a justification or a link of a chain, and the tokeniser says which
//! characters of a formula are a letter. Only those characters change. A
//! rewrite that cannot tell it keeps the meaning, a letter written where no
//! formula is read, a formula that does not read, declines the theorem and
//! says why; it never guesses.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use indexmap::IndexSet;
use parley::checker::{
    statements_in_scope, BoundThere, CheckedTheorem, NeededThere, ObtainedThere,
    SaidOnceThere,
};
use parley::corpus::proof::{
    chain, chain_cited, parse_proof, rows, substitute_rows, Head, Intro, Method,
    Requires, RowReason, StepNo, Theorem,
};
use parley::corpus::skeleton::{chain_reason, is_ref};
use parley::corpus::{define_parts, naming_pieces, Corpus, DefineParts, Values};
use parley::formula::grammar::{Grammar, Sorts};
use parley::formula::node::Node;
use parley::formula::page::{conjoined, made_as, Written};
use parley::formula::token::{is_letter, is_mark, tokenise, Token, TokenKind};
use parley::matching::free_names;
use parley::outcome::{Built, Checked, Route};
use parley::sorts::introduction::Introduction;
use parley::sorts::{sorts_in_scope, Env};
use regex::Regex;

use self::layout::*;
use self::letters::*;
pub use self::letters::{
    bound_letters_to_library, claims_split, letter_to_i, letters_swapped,
    letters_to_library, relations_turned, values_bracketed, values_reversed,
};
use self::lifting::*;
pub use self::lifting::{
    blocks_lifted, defines_raised, dull_steps_moved, requires_raised,
};
use self::obtains::*;
pub use self::obtains::{
    cited_lines_restated, defines_lowered, header_defines_raised, obtains_claimed,
    steps_as_requires,
};
use self::statements::*;
pub use self::statements::{parts_named, statements_renamed};

mod layout;
mod letters;
mod lifting;
mod obtains;
mod statements;

/// What every rewrite reads: the corpus, its grammar, and what the corpus
/// says about letters.
pub struct Context {
    pub corpus: Corpus,
    pub g: Rc<Grammar>,
    /// The library's function names of more than one letter, which the
    /// tokeniser reads whole.
    long_names: IndexSet<String>,
    /// The theorems another theorem cites, by qualified name. Its citers
    /// name its letters, so its own are not renamed.
    cited: BTreeSet<String>,
    /// Every single letter a notation's pattern spells: `i`, `π`, and the
    /// `a` of "is a point". Such a letter is not renamed, nor made.
    constants: BTreeSet<String>,
    /// The letters the library's items bind, most used first.
    library_letters: Vec<String>,
    /// What the item each obtain cites says there is, as the checker reads
    /// it at the step, by the step's file and line.
    obtained: BTreeMap<(String, usize), Route<Vec<String>>>,
    /// What each step citing an item makes its letters, as the checker
    /// reads it at the step, by the step's file and line.
    bound: BTreeMap<(String, usize), BTreeMap<String, String>>,
    /// Each step whose claim is a membership the page says once at a step
    /// citing it, by the file, the step's line and the citing step's line.
    said_once: BTreeSet<(String, usize, usize)>,
    /// Each step a step citing it needs, by the file, the step's line and
    /// the citing step's line.
    needed: BTreeSet<(String, usize, usize)>,
}

/// A theorem a rewrite left alone, and why.
pub struct Declined {
    pub theorem: String,
    pub why: String,
}

/// A file as a rewrite left it.
pub struct Rewritten {
    pub text: String,
    /// How many lines it changed.
    pub lines: usize,
    /// The theorems it changed, where it reads theorem by theorem.
    pub theorems: Vec<String>,
    pub declined: Vec<Declined>,
}

/// One sentence, read by the front end every tool reads by.
fn read_one(sentence: &str, g: &Grammar, sorts: &Sorts) -> Checked<Node> {
    Written::new(sentence, "rewritten", 0)
        .formula()?
        .read(g, sorts)
}

/// The sentences of a text the test rewrites, as the front end's splitter
/// cuts them.
fn sentences(text: &str) -> Vec<String> {
    Written::new(text, "rewritten", 0)
        .sentences()
        .iter()
        .map(|s| s.text().to_string())
        .collect()
}

/// The compiled `pattern`, compiled once: the rewrites ask for the same few
/// patterns on every line of every theorem, and compiling them each time
/// took 8% of the test's run.
fn re(pattern: &str) -> Regex {
    thread_local! {
        static COMPILED: RefCell<BTreeMap<String, Regex>> =
            const { RefCell::new(BTreeMap::new()) };
    }
    COMPILED.with(|compiled| {
        compiled
            .borrow_mut()
            .entry(pattern.to_string())
            .or_insert_with(|| Regex::new(pattern).expect("the pattern compiles"))
            .clone()
    })
}

/// A letter as the tokeniser reads one: a letter and its marks, `x₁`, `f′`.
fn is_one_letter(text: &str) -> bool {
    let mut chars = text.chars();
    chars.next().is_some_and(is_letter) && chars.all(is_mark)
}

/// Which alphabet and case a letter is in. A letter is renamed only within
/// its class: the corpus writes points and sets in capitals, numbers in
/// lower case.
fn class(letter: &str) -> u8 {
    let c = letter.chars().next().unwrap_or(' ');
    if c.is_ascii_lowercase() {
        0
    } else if c.is_ascii_uppercase() {
        1
    } else if c.is_lowercase() {
        2
    } else {
        3
    }
}

/// A reason a theorem writes, and the values it gives what it cites.
struct Reasoned {
    text: String,
    values: Values,
}

impl Reasoned {
    fn of(r: &Requires) -> Reasoned {
        Reasoned {
            text: r.how.clone(),
            values: r.values().clone(),
        }
    }
}

/// Every reason a theorem writes: each step's justification, each requires
/// line's, each chain line's and substitute row's of its own, and each
/// let's under it.
fn reasons(thm: &Theorem) -> Vec<Reasoned> {
    let mut out = Vec::new();
    for step in &thm.steps {
        out.push(Reasoned {
            text: step.just.text.clone(),
            values: step.just.values.clone(),
        });
        out.extend(step.requires.iter().map(Reasoned::of));
        if let Some(Ok(c)) = chain(&step.just, &thm.path) {
            out.extend(
                c.lines
                    .iter()
                    .filter_map(|l| l.reason.as_ref())
                    .map(Reasoned::of),
            );
        }
        if let Some(Ok(rows)) = substitute_rows(&step.just, &thm.path) {
            out.extend(
                rows.iter()
                    .filter_map(|r| r.reason.as_ref())
                    .map(Reasoned::of),
            );
        }
    }
    out.extend(
        thm.defines
            .iter()
            .filter_map(|d| d.reason.as_ref())
            .map(|r| Reasoned {
                text: r.how.clone(),
                values: r.values().clone(),
            }),
    );
    out
}

/// The items a justification or requires line cites, by full name.
fn cites(thm: &Theorem, text: &str) -> Vec<String> {
    let names = &thm.names;
    re(r"\b[a-z]+:([A-Za-z0-9′-]+)")
        .captures_iter(text)
        .map(|m| names.full(&m[1]))
        .collect()
}

/// The single letter a `let` body introduces, `let a ∈ ℕ` or `let f : X → Y`.
fn let_letter(body: &str) -> Option<String> {
    let first = body.split([' ', '∈', ':']).next()?.trim();
    is_one_letter(first).then(|| first.to_string())
}

impl Context {
    pub fn new(
        corpus: Corpus,
        obtained: Vec<ObtainedThere>,
        bound: Vec<BoundThere>,
        said_once: Vec<SaidOnceThere>,
        needed: Vec<NeededThere>,
    ) -> Context {
        let g = Grammar::load(&corpus.records).expect("the grammar loads");
        let long_names: IndexSet<String> = g
            .functions
            .keys()
            .filter(|k| k.chars().count() > 1)
            .cloned()
            .collect();
        let mut cited = BTreeSet::new();
        let theorems: BTreeSet<String> =
            corpus.theorems.iter().map(|t| t.qualified()).collect();
        for thm in &corpus.theorems {
            for reason in reasons(thm) {
                for full in cites(thm, &reason.text) {
                    if theorems.contains(&full) && full != thm.qualified() {
                        cited.insert(full);
                    }
                }
            }
        }
        // The letters a pattern spells, as the grammar reads its parts: the
        // d of ∫(_ to _) _ d_ is written against its hole, and is a literal
        // all the same.
        let mut constants = BTreeSet::new();
        for notation in &g.notations {
            for literal in notation.parts.iter().filter_map(|p| p.literal()) {
                if is_one_letter(literal) {
                    constants.insert(literal.to_string());
                }
            }
        }
        let mut counts: BTreeMap<String, usize> = BTreeMap::new();
        let mut context = Context {
            corpus,
            g,
            long_names,
            cited,
            constants,
            library_letters: Vec::new(),
            obtained: obtained
                .into_iter()
                .map(|o| ((o.path, o.line), o.said))
                .collect(),
            bound: bound
                .into_iter()
                .map(|b| ((b.path, b.line), b.letters.into_iter().collect()))
                .collect(),
            said_once: said_once
                .into_iter()
                .map(|s| (s.path, s.line, s.at))
                .collect(),
            needed: needed.into_iter().map(|n| (n.path, n.line, n.at)).collect(),
        };
        for record in &context.corpus.records {
            let mut texts: Vec<&str> =
                record.hypotheses.iter().map(|h| h.text.as_str()).collect();
            texts.extend(record.conclusions.iter().map(|(c, _)| c.as_str()));
            for text in texts {
                for letter in context.letters_of(text) {
                    *counts.entry(letter).or_default() += 1;
                }
            }
        }
        let mut ranked: Vec<(String, usize)> = counts.into_iter().collect();
        ranked.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        context.library_letters = ranked.into_iter().map(|(l, _)| l).collect();
        context
    }

    /// The tokens of a formula, a sentence at a time as the readers take
    /// it: a full stop followed by a space or the end closes a sentence and
    /// is no token. Each token's place counts from the start of `text`.
    fn tokens(&self, text: &str) -> Option<Vec<Token>> {
        let c = chars(text);
        let mut out = Vec::new();
        let mut start = 0;
        let mut i = 0;
        while i <= c.len() {
            let ends = i == c.len()
                || (c[i] == '.' && (i + 1 == c.len() || c[i + 1].is_whitespace()));
            if ends {
                let piece: String = c[start..i].iter().collect();
                if !piece.trim().is_empty() {
                    let tokens = tokenise(
                        &piece,
                        &self.g.words,
                        &self.long_names,
                        &self.g.symbols,
                        "",
                        0,
                    )
                    .ok()?;
                    out.extend(tokens.into_iter().map(|t| Token {
                        at: t.at + start,
                        ..t
                    }));
                }
                start = i + 1;
            }
            i += 1;
        }
        Some(out)
    }

    /// The single letters a formula writes, where it tokenises.
    fn letters_of(&self, text: &str) -> Vec<String> {
        self.tokens(text)
            .unwrap_or_default()
            .into_iter()
            .filter(|t| t.kind == TokenKind::Name && is_one_letter(&t.text))
            .map(|t| t.text)
            .collect()
    }
}
