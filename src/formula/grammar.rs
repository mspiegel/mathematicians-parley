//! Reading one sentence against the declared notations.

use indexmap::{IndexMap, IndexSet};

use super::node::{Node, Sort};
use super::notation::{
    binds_tighter, compile_notations, compile_precedence, Notation, Part, Tighter,
};
use super::token::{tokenise, Token, TokenKind};
use crate::corpus::Record;
use crate::outcome::{Checked, Problem};
use crate::text::repr;

/// The sort of each name a text states one for.
pub type Sorts = IndexMap<String, Sort>;

/// The declared notations, the words and symbols they are written with, and
/// the precedence order between their levels.
pub struct Grammar {
    pub notations: Vec<Notation>,
    pub words: IndexSet<String>,
    pub symbols: Vec<String>,
    pub tighter: IndexMap<String, IndexSet<String>>,
}

impl Grammar {
    pub fn load(records: &[Record]) -> Checked<Grammar> {
        let (notations, words, symbols) = compile_notations(records)?;
        Ok(Grammar {
            notations,
            words,
            symbols,
            tighter: compile_precedence(records),
        })
    }
}

/// The sorts a term may have to fill any hole: every sort of a term.
pub const TERM_SORTS: [&str; 7] = [
    "number",
    "set",
    "point",
    "group-element",
    "group-set",
    "set-of-sets",
    "any",
];

/// What a set of each sort holds, where the sort says: a group's set holds
/// its elements, and a set of sets holds sets.
pub fn holds(sort: &Sort) -> Option<&'static str> {
    match sort.name() {
        Some("group-set") => Some("group-element"),
        Some("set-of-sets") => Some("set"),
        _ => None,
    }
}

/// A value fits a hole when the sorts agree, when the hole takes any term,
/// or when the value's sort is not known. The last is the permissive rule: a
/// value of no known sort fits anywhere, because refusing it would reject
/// proofs for failing a test the sorts were never introduced to run.
///
/// `any` means two different things and both are unknown-ish. As a hole it
/// says "any term"; as what a notation yields, as application does, it says
/// "whatever came back", which is exactly a value of no known sort.
pub fn fits(hole: &str, sort: &Sort) -> bool {
    // Except a group element's hole: `k·m` with neither sort known is a
    // product of numbers, as it always was, and a letter is a group element
    // only where the page says so or says what it ranges over.
    if sort.is_unsorted() {
        return hole != "group-element";
    }
    let name = sort.name().unwrap_or("");
    if hole == "any" {
        return TERM_SORTS.contains(&name);
    }
    // A group's set and a set of sets are sets, and fit wherever one is
    // wanted.
    if hole == "set" && holds(sort).is_some() {
        return true;
    }
    hole == name
}

/// Parse one sentence.
///
/// Nothing below gives up by raising: a reading that did not work out gives
/// back no node and says where it stopped. This is the one place that turns
/// having no reading into a defect, because it is the one place that knows
/// there is no other reading left to try. Two readings fitting is the other
/// defect, and that is raised wherever it is found.
///
/// A letter the sentence binds has no sort of its own, but what it ranges
/// over may say one: in `for every g ∈ G, …` with G a group's set, g is a
/// group element, and `g·h` is the group's operation and not a product of
/// numbers. So each `x ∈ S` the sentence writes gives an x of no sort what S
/// holds, for this sentence only (`bound_sorts`).
pub fn parse(
    text: &str,
    g: &Grammar,
    sorts: &Sorts,
    path: &str,
    line: usize,
) -> Checked<Node> {
    let tokens = tokenise(text, &g.words, &g.symbols, path, line)?;
    let mut local = sorts.clone();
    for (k, v) in bound_sorts(&tokens, sorts) {
        local.insert(k, v);
    }
    let mut p = Parser {
        t: &tokens,
        g,
        sorts: &local,
        path,
        line,
        src: text,
        i: 0,
        stopped: None,
    };
    let Some(node) = p.expression(None, None)? else {
        return Err(Problem::new(path, line, p.why()));
    };
    if p.i != tokens.len() {
        return Err(Problem::new(
            path,
            line,
            format!(
                "{} has {} token(s) left over, starting at {}",
                repr(text),
                tokens.len() - p.i,
                repr(&tokens[p.i].text)
            ),
        ));
    }
    Ok(node)
}

/// Parse with nowhere to point: a sentence no file holds.
pub fn parse_here(text: &str, g: &Grammar, sorts: &Sorts) -> Checked<Node> {
    parse(text, g, sorts, "", 0)
}

/// The sort of each letter the tokens put in a set that says what it holds,
/// `x ∈ S`, or in a coset of one, `x ∈ gH`. Only for letters of no sort
/// already.
fn bound_sorts(tokens: &[Token], sorts: &Sorts) -> Vec<(String, Sort)> {
    let mut out: IndexMap<String, Sort> = IndexMap::new();
    let sort_of = |name: &str| sorts.get(name).cloned().unwrap_or_default();
    for i in 0..tokens.len().saturating_sub(2) {
        let (x, sign, s) = (&tokens[i], &tokens[i + 1], &tokens[i + 2]);
        if x.kind != TokenKind::Name
            || sign.text != "∈"
            || s.kind != TokenKind::Name
            || !sort_of(&x.text).is_unknown()
        {
            continue;
        }
        let mut held = holds(&sort_of(&s.text));
        if held.is_none()
            && i + 3 < tokens.len()
            && tokens[i + 3].kind == TokenKind::Name
            && sort_of(&s.text).is("group-element")
        {
            held = holds(&sort_of(&tokens[i + 3].text));
        }
        if let Some(held) = held {
            out.entry(x.text.clone()).or_insert_with(|| Sort::of(held));
        }
    }
    out.into_iter().collect()
}

/// One sentence being read.
///
/// A notation is recognised by trying it, so most of what is tried does not
/// fit and saying so is not a complaint: `p` in `d divides p, and ...` is a
/// candidate first point of a triangle until the comma rules it out, and a
/// sentence of ordinary words rules out dozens. So not fitting is a value
/// here: no node. Two notations fitting is a defect however it was reached,
/// and that is the error.
///
/// `stopped` keeps the furthest any reading reached and what stood in its
/// way there, which is the reading that got closest to working and the one
/// worth telling a reader about.
struct Parser<'a> {
    t: &'a [Token],
    g: &'a Grammar,
    sorts: &'a Sorts,
    path: &'a str,
    line: usize,
    src: &'a str,
    i: usize,
    stopped: Option<(usize, String)>,
}

/// A reading, no reading, or two readings.
type Reading = Checked<Option<Node>>;

impl Parser<'_> {
    fn peek(&self) -> Option<&Token> {
        self.t.get(self.i)
    }

    /// No reading here, and why.
    fn no(&mut self, message: String) -> Reading {
        let further = match &self.stopped {
            None => true,
            Some((at, _)) => self.i > *at,
        };
        if further {
            self.stopped = Some((self.i, message));
        }
        Ok(None)
    }

    /// What to say about a sentence no reading fitted.
    fn why(&self) -> String {
        match &self.stopped {
            Some((_, message)) if !message.is_empty() => message.clone(),
            _ => format!("nothing reads {}", repr(self.src)),
        }
    }

    /// Parse a primary, then extend it with any notation whose first hole it
    /// can fill, so long as that notation binds tighter than `outer`.
    ///
    /// `stop` is the literal that closes an interior hole. Without it the hole
    /// runs past its own delimiter: the set in `for every s ∈ S, d ≤ s` would
    /// swallow the comma and try to be the first point of a triangle.
    fn expression(&mut self, outer: Option<&str>, stop: Option<&str>) -> Reading {
        let Some(mut left) = self.primary()? else {
            return Ok(None);
        };
        loop {
            if let (Some(stop), Some(next)) = (stop, self.peek()) {
                if next.text == stop {
                    return Ok(Some(left));
                }
            }
            match self.extend(&left, outer)? {
                None => return Ok(Some(left)),
                Some(next) => left = next,
            }
        }
    }

    fn primary(&mut self) -> Reading {
        let Some(tok) = self.peek().cloned() else {
            return self.no(format!("{} ends early", repr(self.src)));
        };
        if tok.kind == TokenKind::Open {
            self.i += 1;
            let Some(inner) = self.expression(None, None)? else {
                return Ok(None);
            };
            if self.peek().is_none_or(|t| t.kind != TokenKind::Close) {
                return self.no(format!("unclosed bracket in {}", repr(self.src)));
            }
            self.i += 1;
            return Ok(Some(inner));
        }
        // A notation may open with a literal that is also a name, as the two
        // sum functions do with S and G. Try those as well as the bare name
        // and take whichever reaches further.
        let g = self.g;
        let cands: Vec<&Notation> = g
            .notations
            .iter()
            .filter(|n| {
                n.parts.first().and_then(Part::literal) == Some(tok.text.as_str())
            })
            .collect();
        if tok.kind == TokenKind::Name || tok.kind == TokenKind::Numeral {
            let leaf = if tok.kind == TokenKind::Name {
                let sort = self
                    .sorts
                    .get(&tok.text)
                    .cloned()
                    .unwrap_or_else(Sort::unknown);
                Node::leaf("name", sort, &tok.text)
            } else {
                Node::leaf("numeral", Sort::of("number"), &tok.text)
            };
            if cands.is_empty() {
                self.i += 1;
                return Ok(Some(leaf));
            }
            if let Some(found) = self.apply(&cands, None)? {
                return Ok(Some(found));
            }
            self.i += 1;
            return Ok(Some(leaf));
        }
        self.apply(&cands, None)
    }

    /// Notations whose pattern opens with a hole, which `left` fills.
    fn extend(&mut self, left: &Node, outer: Option<&str>) -> Reading {
        let Some(tok) = self.peek().cloned() else {
            return Ok(None);
        };
        if tok.kind == TokenKind::Close {
            return Ok(None);
        }
        let g = self.g;
        let mut cands: Vec<&Notation> = Vec::new();
        for n in &g.notations {
            if n.parts.len() < 2 || !n.parts[0].is_hole() {
                continue;
            }
            // A pattern whose second part is also a hole has no token to
            // recognise it by: juxtaposition. It is a candidate whenever what
            // follows could begin a term.
            match &n.parts[1] {
                Part::Hole => {
                    if !matches!(
                        tok.kind,
                        TokenKind::Name | TokenKind::Numeral | TokenKind::Open
                    ) {
                        continue;
                    }
                    // Juxtaposition never joins two bare names. That
                    // restriction is what makes a run of letters decidable at
                    // all, since `and` would otherwise read as a product of
                    // three variables the corpus uses. It leaves `2k` and
                    // `k(k + 1)`, which are the only shapes the corpus writes.
                    // The one pair of letters it does join is a group element
                    // beside a group's set, `gH`, the coset: the sorts say so,
                    // and "and" has none.
                    if tok.kind == TokenKind::Name
                        && left.is_name()
                        && !(left.sort.is("group-element")
                            && self
                                .sorts
                                .get(&tok.text)
                                .is_some_and(|s| s.is("group-set"))
                            && n.holes.len() >= 2
                            && n.holes[0] == "group-element"
                            && n.holes[1] == "group-set")
                    {
                        continue;
                    }
                }
                Part::Lit(lit) => {
                    if *lit != tok.text {
                        continue;
                    }
                }
            }
            if !fits(n.holes.first().map_or("", String::as_str), &left.sort) {
                continue;
            }
            // A pattern that ends in a token and declares no level is closed:
            // it competes for nothing that follows and nests anywhere, as
            // `f(x)` and `|x|` do. A pattern that declares a level takes part
            // in precedence wherever it stands, even when a token closes it,
            // or `√2 is irrational` reads as the root of `2 is irrational`.
            if let Some(outer) = outer {
                let competes =
                    n.parts[n.parts.len() - 1].is_hole() || !n.level.is_empty();
                if competes
                    && binds_tighter(&g.tighter, &n.level, outer) != Tighter::Yes
                {
                    continue;
                }
            }
            cands.push(n);
        }
        if cands.is_empty() {
            return Ok(None);
        }
        // An extension is optional, so a candidate that cannot match ends the
        // expression rather than failing it. The sorts only narrow the
        // candidates and a value of unknown sort fits every hole, so a
        // pattern is regularly reached here that the tokens then rule out.
        self.apply(&cands, Some(left))
    }

    /// Try each candidate. Exactly one must fit, or none does and this is no
    /// reading; two do and the text is ambiguous, which is a defect.
    fn apply(&mut self, cands: &[&Notation], left: Option<&Node>) -> Reading {
        if cands.is_empty() {
            let tok = self.peek().map(|t| t.text.clone()).unwrap_or_default();
            return self.no(format!(
                "no notation starts at {} in {}",
                repr(&tok),
                repr(self.src)
            ));
        }
        let start = self.i;
        let mut results: Vec<(Node, usize)> = Vec::new();
        for n in cands {
            self.i = start;
            if let Some(found) = self.match_pattern(n, left)? {
                results.push((found, self.i));
            }
        }
        if results.is_empty() {
            self.i = start;
            let tok = self.peek().map(|t| t.text.clone()).unwrap_or_default();
            return self.no(format!(
                "no notation fits at {} in {}",
                repr(&tok),
                repr(self.src)
            ));
        }
        let best = results.iter().map(|r| r.1).max().unwrap();
        let winners: Vec<&(Node, usize)> =
            results.iter().filter(|r| r.1 == best).collect();
        if winners.len() > 1 {
            let names: std::collections::BTreeSet<&str> =
                winners.iter().map(|w| w.0.notation.as_str()).collect();
            let names: Vec<&str> = names.into_iter().collect();
            return Err(Problem::new(
                self.path,
                self.line,
                format!(
                    "{} fits {} and the sorts do not separate them",
                    repr(self.src),
                    names.join(", ")
                ),
            ));
        }
        self.i = winners[0].1;
        Ok(Some(winners[0].0.clone()))
    }

    /// Match one pattern, filling its holes.
    ///
    /// A hole with a token after it is delimited by that token and takes any
    /// expression. Only a hole at the right edge needs the pattern's level as
    /// a barrier, since only there can a looser notation swallow the rest.
    fn match_pattern(&mut self, n: &Notation, left: Option<&Node>) -> Reading {
        let mut kids: Vec<Node> = Vec::new();
        for (k, part) in n.parts.iter().enumerate() {
            match part {
                Part::Hole => {
                    let want = n.holes.get(kids.len()).map_or("any", String::as_str);
                    if let (0, Some(left)) = (k, left) {
                        kids.push(left.clone());
                    } else {
                        let at_edge = k == n.parts.len() - 1;
                        let after = if at_edge {
                            None
                        } else {
                            n.parts[k + 1].literal()
                        };
                        let barrier = if at_edge {
                            Some(n.level.as_str())
                        } else {
                            None
                        };
                        let Some(kid) = self.hole(want, barrier, after)? else {
                            return Ok(None);
                        };
                        kids.push(kid);
                    }
                }
                Part::Lit(lit) => {
                    let message = match self.peek() {
                        Some(tok) if tok.text == *lit => None,
                        Some(tok) => Some(format!(
                            "{} does not fit at {} in {}",
                            n.name,
                            repr(&tok.text),
                            repr(self.src)
                        )),
                        None => Some(format!("{} ends early", repr(self.src))),
                    };
                    if let Some(message) = message {
                        return self.no(message);
                    }
                    self.i += 1;
                }
            }
        }
        // A pattern may name fewer hole sorts than it has holes, which the
        // record check reports; here the extra holes simply go unchecked.
        for (kid, want) in kids.iter().zip(n.holes.iter()) {
            if !fits(want, &kid.sort) {
                return self
                    .no(format!("{} wants {} and got {}", n.name, want, kid.sort));
            }
        }
        // The node is named by the record and carries the literal of the
        // pattern it stands for. Both are needed: ℝ and ℕ₀ are one record,
        // and so are `a < b` and `a ≥ b`, and nothing comparing two formulas
        // could otherwise tell either pair apart.
        if let Some(w) = &n.wrap {
            let inner = kids[w.hole - 1].clone();
            kids[w.hole - 1] =
                Node::new(&w.name, Sort::of(&w.yields), vec![inner], &w.literal);
        }
        let node = Node::new(n.key(), Sort::of(&n.yields), kids, &n.literal);
        // A pattern declared as the negation of another builds the other and
        // wraps it, so the folded spelling and the `not` spelling are one
        // tree. The wrapper is named by the record, not known here.
        match &n.folds {
            None => Ok(Some(node)),
            Some(folds) => Ok(Some(Node::new(
                folds,
                Sort::of("formula"),
                vec![node],
                &n.fold_literal,
            ))),
        }
    }

    /// A `variable` hole takes a bare name; any other takes an expression,
    /// bounded by `barrier` when the hole sits at the pattern's right edge
    /// and by `stop`, the literal that follows it, when it does not.
    fn hole(
        &mut self,
        want: &str,
        barrier: Option<&str>,
        stop: Option<&str>,
    ) -> Reading {
        if want == "variable" {
            let Some(tok) = self.peek().cloned() else {
                return self.no("a binder wants a name".into());
            };
            if tok.kind != TokenKind::Name {
                return self.no("a binder wants a name".into());
            }
            self.i += 1;
            return Ok(Some(Node::leaf("name", Sort::of("variable"), &tok.text)));
        }
        self.expression(barrier, stop)
    }
}
