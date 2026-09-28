//! Reading one sentence against the declared notations.

use std::cell::{OnceCell, RefCell};
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use super::node::{describe_category, Node, Sort};
use super::notation::{
    binds_tighter, compile_notations, compile_precedence, Notation, Part, Tighter, Wrap,
};
use super::token::{tokenise, Token, TokenKind};
use crate::corpus::Record;
use crate::outcome::{Checked, Problem};
use crate::sorts::infer::NotationSorts;
use crate::text::repr;

/// The sort of each name a text states one for, and the set each letter its
/// theorem declares a range for belongs to (`ε, δ range over ℝ`).
///
/// It reads as the map of sorts, which is what nearly every use wants. The
/// ranges ride along with it because a theorem's sorts go everywhere its
/// text is read, and a short form, "for all ε > 0", reads only where its
/// range is known.
#[derive(Clone, Debug, Default)]
pub struct Sorts {
    names: IndexMap<String, Sort>,
    pub ranges: IndexMap<String, String>,
}

impl Sorts {
    pub fn new() -> Sorts {
        Sorts::default()
    }
}

impl std::ops::Deref for Sorts {
    type Target = IndexMap<String, Sort>;
    fn deref(&self) -> &IndexMap<String, Sort> {
        &self.names
    }
}

impl std::ops::DerefMut for Sorts {
    fn deref_mut(&mut self) -> &mut IndexMap<String, Sort> {
        &mut self.names
    }
}

impl FromIterator<(String, Sort)> for Sorts {
    fn from_iter<I: IntoIterator<Item = (String, Sort)>>(iter: I) -> Sorts {
        Sorts {
            names: iter.into_iter().collect(),
            ranges: IndexMap::new(),
        }
    }
}

impl<'a> IntoIterator for &'a Sorts {
    type Item = (&'a String, &'a Sort);
    type IntoIter = indexmap::map::Iter<'a, String, Sort>;
    fn into_iter(self) -> Self::IntoIter {
        self.names.iter()
    }
}

/// A sentence, the sort of each name it holds in the order the names first
/// appear, and the range declared for each: everything a reading of it
/// depends on besides the grammar.
type ReadingKey = (String, Vec<Option<Sort>>, Vec<Option<String>>);

/// The declared notations, the words and symbols they are written with, and
/// the precedence order between their levels.
///
/// It also keeps what it has read. One check reads the same sentence many
/// times over (the sorts, the formulas, and every citation asking again with
/// a line taken away), and a reading depends only on the grammar, the
/// sentence, and the sorts of the names in it; so each is read once. Only a
/// reading that succeeded is kept, since a failure names the place it was
/// asked from.
pub struct Grammar {
    pub notations: Vec<Notation>,
    pub words: IndexSet<String>,
    pub symbols: Vec<String>,
    pub tighter: IndexMap<String, IndexSet<String>>,
    tokens: RefCell<IndexMap<String, Rc<Vec<Token>>>>,
    readings: RefCell<IndexMap<ReadingKey, Node>>,
    notation_sorts: OnceCell<Rc<NotationSorts>>,
}

impl Grammar {
    pub fn load(records: &[Record]) -> Checked<Grammar> {
        let (notations, words, symbols) = compile_notations(records)?;
        Ok(Grammar {
            notations,
            words,
            symbols,
            tighter: compile_precedence(records),
            tokens: RefCell::new(IndexMap::new()),
            readings: RefCell::new(IndexMap::new()),
            notation_sorts: OnceCell::new(),
        })
    }

    /// What the notations say about sorts, read the first time a reading
    /// asks and shared by every one after.
    pub fn notation_sorts(&self) -> Rc<NotationSorts> {
        Rc::clone(
            self.notation_sorts
                .get_or_init(|| Rc::new(NotationSorts::read(self))),
        )
    }

    /// The sentence's tokens, read once.
    fn tokens(&self, text: &str, path: &str, line: usize) -> Checked<Rc<Vec<Token>>> {
        if let Some(found) = self.tokens.borrow().get(text) {
            return Ok(Rc::clone(found));
        }
        let read = Rc::new(tokenise(text, &self.words, &self.symbols, path, line)?);
        self.tokens
            .borrow_mut()
            .insert(text.to_string(), Rc::clone(&read));
        Ok(read)
    }
}

/// What a reading of these tokens depends on besides the grammar: the text,
/// and the sort each name in it has, or that it has none.
fn reading(text: &str, tokens: &[Token], sorts: &Sorts) -> ReadingKey {
    let mut seen: IndexSet<&str> = IndexSet::new();
    for t in tokens {
        if t.kind == TokenKind::Name {
            seen.insert(&t.text);
        }
    }
    let said = seen.iter().map(|name| sorts.get(*name).cloned()).collect();
    let ranges = seen
        .iter()
        .map(|name| sorts.ranges.get(*name).cloned())
        .collect();
    (text.to_string(), said, ranges)
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

/// What a set of each sort holds, where the sort says (`Sort::held`).
pub fn holds(sort: &Sort) -> Option<Sort> {
    sort.held()
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
/// over may say one: in `for all g ∈ G, …` with G a group's set, g is a
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
    let tokens = g.tokens(text, path, line)?;
    let key = reading(text, &tokens, sorts);
    if let Some(found) = g.readings.borrow().get(&key) {
        return Ok(found.clone());
    }
    let node = read(text, &tokens, g, sorts, path, line)?;
    g.readings.borrow_mut().insert(key, node.clone());
    Ok(node)
}

/// Read the sentence's tokens into one node, or say why there is none.
fn read(
    text: &str,
    tokens: &[Token],
    g: &Grammar,
    sorts: &Sorts,
    path: &str,
    line: usize,
) -> Checked<Node> {
    let mut local = sorts.clone();
    for (k, v) in bound_sorts(tokens, sorts) {
        local.insert(k, v);
    }
    let mut p = Parser {
        t: tokens,
        g,
        sorts: &local,
        path,
        line,
        src: text,
        i: 0,
        stopped: None,
        refused: None,
        refused_order: false,
    };
    let Some(node) = p.expression(None, None)? else {
        return Err(Problem::new(path, line, p.why()));
    };
    if p.i != tokens.len() {
        // A reading that went further than the one that stopped here, and
        // was turned away, says why the rest does not read: in `s is a set`
        // with s a number, `s` reads and `_ is a set` does not take it.
        if let Some((at, why)) = &p.refused {
            if *at > p.i {
                return Err(Problem::new(path, line, format!("{}: {why}", repr(text))));
            }
        }
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

/// `a or as b`, `a, as b or as c`: the readings a sentence has, for a
/// message saying it has more than one.
fn one_of(readings: &[String]) -> String {
    match readings {
        [] => String::new(),
        [one] => one.clone(),
        [rest @ .., last] => format!("{} or as {last}", rest.join(", as ")),
    }
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
            out.entry(x.text.clone()).or_insert(held);
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
/// worth telling a reader about. `refused` keeps the furthest a notation the
/// text writes was turned away by the sort of what stood in one of its
/// holes, which is what to say when a shorter reading leaves tokens over.
struct Parser<'a> {
    t: &'a [Token],
    g: &'a Grammar,
    sorts: &'a Sorts,
    path: &'a str,
    line: usize,
    src: &'a str,
    i: usize,
    stopped: Option<(usize, String)>,
    refused: Option<(usize, String)>,
    /// Whether what `refused` says is about the precedence order.
    refused_order: bool,
}

/// A reading, no reading, or two readings.
type Reading = Checked<Option<Node>>;

impl Parser<'_> {
    fn peek(&self) -> Option<&Token> {
        self.t.get(self.i)
    }

    /// No reading here, and why.
    /// The sentence's text from token `from` up to token `to`, as written.
    fn written(&self, from: usize, to: usize) -> String {
        let (Some(first), Some(last)) = (
            self.t.get(from),
            to.checked_sub(1).and_then(|l| self.t.get(l)),
        ) else {
            return String::new();
        };
        let end = last.at + last.text.chars().count();
        self.src
            .chars()
            .skip(first.at)
            .take(end.saturating_sub(first.at))
            .collect()
    }

    /// Keep the furthest place a notation the text writes was turned away by
    /// the sort of what stood in a hole, and why.
    fn refuse(&mut self, at: usize, why: String) {
        if self.refused.as_ref().is_none_or(|(was, _)| at > *was) {
            self.refused = Some((at, why));
            self.refused_order = false;
        }
    }

    /// `refuse`, for two notations the precedence order leaves unrelated:
    /// at the same point it is said over a sort refused inside one of the
    /// readings tried, since it is about the text as written, and not over
    /// another such, since the first found is the innermost pair.
    fn refuse_order(&mut self, at: usize, why: String) {
        let over = match &self.refused {
            None => true,
            Some((was, _)) => at > *was || (at == *was && !self.refused_order),
        };
        if over {
            self.refused = Some((at, why));
            self.refused_order = true;
        }
    }

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
    /// runs past its own delimiter: the set in `for all s ∈ S, d ≤ s` would
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
            let Some(close) =
                self.peek().filter(|t| t.kind == TokenKind::Close).cloned()
            else {
                return self.no(format!("unclosed bracket in {}", repr(self.src)));
            };
            self.i += 1;
            // The brackets are part of what was written, and what extends
            // the group starts at the first of them.
            inner.set_span(tok.at, close.at + close.text.chars().count());
            inner.set_grouped();
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
            leaf.set_span(tok.at, tok.at + tok.text.chars().count());
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

    /// The precedence level of the notation a node was built by, where it
    /// declares one; a name, a numeral and a closed pattern have none.
    fn level_of(&self, node: &Node) -> Option<String> {
        self.g
            .notations
            .iter()
            .find(|n| n.name == node.notation)
            .map(|n| n.level.clone())
            .filter(|level| !level.is_empty())
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
            let want = n.holes.first().map_or("", String::as_str);
            if !fits(want, &left.sort) {
                // The tokens after it are the pattern's own, so the text
                // writes this notation and only the sort of what stands
                // before it turns it away: say so, in case nothing reads.
                let run: Vec<&str> =
                    n.parts[1..].iter().map_while(|p| p.literal()).collect();
                let written = !run.is_empty()
                    && run.iter().enumerate().all(|(j, lit)| {
                        self.t.get(self.i + j).is_some_and(|t| t.text == *lit)
                    });
                if written {
                    let what = if left.is_name() {
                        left.text.clone()
                    } else {
                        format!("what stands before `{}`", n.pattern)
                    };
                    let why = format!(
                        "{what} is {}, and `{}` wants {}",
                        left.sort.describe(),
                        n.pattern,
                        describe_category(want)
                    );
                    self.refuse(self.i + run.len(), why);
                }
                continue;
            }
            // A pattern that ends in a token and declares no level is closed:
            // it competes for nothing that follows and nests anywhere, as
            // `f(x)` and `|x|` do. A pattern that declares a level takes part
            // in precedence wherever it stands, even when a token closes it,
            // or `√2 is irrational` reads as the root of `2 is irrational`.
            // A notation declared `assoc right` nests in its own last hole,
            // so `a ^ b ^ c` is a ^ (b ^ c).
            if let Some(outer) = outer {
                let competes =
                    n.parts[n.parts.len() - 1].is_hole() || !n.level.is_empty();
                let nests = n.level == outer && n.assoc.as_deref() == Some("right");
                if competes
                    && !nests
                    && binds_tighter(&g.tighter, &n.level, outer) != Tighter::Yes
                {
                    continue;
                }
            }
            // What stands to the left is this notation's operand only where
            // it binds tighter, or is the same level chained as `assoc left`
            // says. Levels unrelated in the precedence order need brackets
            // whichever side each stands on, so `P and Q or R` has no
            // reading; a bracketed group is closed and extends at any level.
            if !n.level.is_empty() && !left.grouped() {
                if let Some(level) = self.level_of(left) {
                    let chains = level == n.level && n.assoc.as_deref() == Some("left");
                    if !chains
                        && binds_tighter(&g.tighter, &level, &n.level) != Tighter::Yes
                    {
                        // The pattern's own tokens follow, so the text writes
                        // it and only the order turns it away: say so.
                        let run: Vec<&str> =
                            n.parts[1..].iter().map_while(|p| p.literal()).collect();
                        let written = !run.is_empty()
                            && run.iter().enumerate().all(|(j, lit)| {
                                self.t.get(self.i + j).is_some_and(|t| t.text == *lit)
                            });
                        if written {
                            // Each is named by the words the text wrote for
                            // it, which a pattern shares with its variants.
                            let before = self
                                .g
                                .notations
                                .iter()
                                .find(|m| m.name == left.notation)
                                .map(|m| {
                                    m.parts
                                        .iter()
                                        .skip_while(|p| p.is_hole())
                                        .map_while(|p| p.literal())
                                        .collect::<Vec<_>>()
                                        .join(" ")
                                })
                                .unwrap_or_else(|| left.notation.clone());
                            let why = format!(
                                "`{before}` and `{}` are not ordered against each other, so which is inside the other is written with brackets",
                                run.join(" ")
                            );
                            self.refuse_order(self.i + run.len(), why);
                        }
                        continue;
                    }
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
            let readings: std::collections::BTreeSet<&str> =
                winners.iter().map(|w| w.0.notation.as_str()).collect();
            let readings: Vec<String> =
                readings.into_iter().map(String::from).collect();
            // What would tell the readings apart is the sort of a name in
            // them that nothing has given one.
            let mut open: Vec<String> = Vec::new();
            for (w, _) in &winners {
                for node in w.walk() {
                    if node.is_name()
                        && node.sort.is_unknown()
                        && !open.contains(&node.text)
                    {
                        open.push(node.text.clone());
                    }
                }
            }
            let undecided = match open.as_slice() {
                [] => "nothing tells them apart".to_string(),
                [one] => format!("nothing says what {one} is"),
                [rest @ .., last] => {
                    format!("nothing says what {} and {last} are", rest.join(", "))
                }
            };
            return Err(Problem::new(
                self.path,
                self.line,
                format!(
                    "{} reads as {}, and {undecided}",
                    repr(self.src),
                    one_of(&readings)
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
        let begin = match left {
            Some(l) => l.span().map(|s| s.0),
            None => self.t.get(self.i).map(|t| t.at),
        };
        let mut kids: Vec<Node> = Vec::new();
        // The tokens each hole took, for a message to quote; the value to
        // the left of an extension was read before it, and took none here.
        let mut took: Vec<Option<(usize, usize)>> = Vec::new();
        for (k, part) in n.parts.iter().enumerate() {
            match part {
                Part::Hole => {
                    let want = n.holes.get(kids.len()).map_or("any", String::as_str);
                    if let (0, Some(left)) = (k, left) {
                        kids.push(left.clone());
                        took.push(None);
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
                        let from = self.i;
                        let Some(kid) = self.hole(want, barrier, after)? else {
                            return Ok(None);
                        };
                        kids.push(kid);
                        took.push(Some((from, self.i)));
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
        for ((kid, want), span) in kids.iter().zip(n.holes.iter()).zip(&took) {
            if !fits(want, &kid.sort) {
                let what = match span {
                    _ if kid.is_name() => kid.text.clone(),
                    Some((from, to)) => repr(&self.written(*from, *to)),
                    None => format!("what stands before `{}`", n.pattern),
                };
                let why = format!(
                    "{what} is {}, and `{}` wants {}",
                    kid.sort.describe(),
                    n.pattern,
                    describe_category(want)
                );
                self.refuse(self.i, why.clone());
                return self.no(why);
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
        // A binder written with a bound where its set stands, "for all ε >
        // 0", builds the node its long form builds, "for all ε ∈ ℝ with ε >
        // 0": the set is the one its theorem declares for the name, and the
        // condition is what the text wrote from the name to the bound, read
        // as it would be read anywhere else.
        if let Some(b) = &n.bounds {
            let held = kids[b.name - 1].clone();
            let name = held.text.clone();
            let Some(set) = self.sorts.ranges.get(&name).cloned() else {
                let why = format!(
                    "nothing says what set {name} belongs to: write `{name} ∈` a set before the bound, or say what {name} ranges over in the theorem's statement"
                );
                self.refuse(self.i, why.clone());
                return self.no(why);
            };
            let set =
                parse(&set, self.g, self.sorts, self.path, self.line)?.unwritten();
            let (Some(Some((from, _))), Some(Some((_, to)))) =
                (took.get(b.name - 1).copied(), took.get(b.to - 1).copied())
            else {
                return self.no(format!("`{}` has no condition to read", n.pattern));
            };
            let mut sub = Parser {
                t: &self.t[..to],
                g: self.g,
                sorts: self.sorts,
                path: self.path,
                line: self.line,
                src: self.src,
                i: from,
                stopped: None,
                refused: None,
                refused_order: false,
            };
            let condition = match sub.expression(None, None)? {
                Some(c) if sub.i == to => c,
                _ => {
                    return self.no(format!(
                        "{} does not read as a condition",
                        repr(&self.written(from, to))
                    ))
                }
            };
            // The holes outside the condition, in the order written: the body
            // after "for all ε > 0,", or before "for all n ≥ N".
            let rest: Vec<Node> = kids
                .iter()
                .enumerate()
                .filter(|(i, _)| *i + 1 < b.name || *i + 1 > b.to)
                .map(|(_, k)| k.clone())
                .collect();
            kids = match &b.join {
                None => [vec![held, set, condition], rest].concat(),
                Some(w) => {
                    let body = self.joined(condition, &kids[w.hole - 1], w);
                    vec![held, set, body]
                }
            };
        }
        // A spelling that writes the other notation's holes in another order
        // puts them back in that notation's order, so the two build one tree:
        // "f(x) ≠ B for all x ∈ A" is "for all x ∈ A, f(x) ≠ B".
        let wrapped_at = n.wrap.as_ref().map(|w| match &n.places {
            Some(places) => places
                .iter()
                .position(|p| *p == w.hole)
                .unwrap_or(w.hole - 1),
            None => w.hole - 1,
        });
        // A spelling that holds two of its holes as one puts that node where
        // the first stood, so "for all x ∈ S with A, B" is "for all x ∈ S, if
        // A then B". `places` counts holes as written, and names the joined
        // node by the first hole's number and the second by none.
        let mut gone: Option<usize> = None;
        if let Some(j) = &n.joins {
            let (first, then) = (&kids[j.first - 1], &kids[j.then - 1]);
            let joined = Node::new(
                &j.by.name,
                Sort::of(&j.by.yields),
                vec![first.clone(), then.clone()],
                &j.by.literal,
            );
            if let (Some(a), Some(b)) = (first.span(), then.span()) {
                joined.set_span(a.0.min(b.0), a.1.max(b.1));
            }
            kids[j.first - 1] = joined;
            gone = Some(j.then - 1);
        }
        if let Some(places) = &n.places {
            kids = places.iter().map(|p| kids[p - 1].clone()).collect();
        } else if let Some(gone) = gone {
            kids.remove(gone);
        }
        // Where it was read from: its first token, or the value it extends,
        // to its last token.
        let end = self
            .i
            .checked_sub(1)
            .and_then(|last| self.t.get(last))
            .map(|t| t.at + t.text.chars().count());
        // A spelling for several names builds the binder it spells once for
        // each, innermost last, so "for all x, y ∈ ℤ, P" is "for all x ∈ ℤ,
        // for all y ∈ ℤ, P".
        if let Some(levels) = &n.nests {
            let mut body = kids[kids.len() - 1].clone();
            for (name, domain) in levels.iter().rev() {
                let level = Node::new(
                    n.key(),
                    Sort::of(&n.yields),
                    vec![kids[name - 1].clone(), kids[domain - 1].clone(), body],
                    &n.literal,
                );
                if let (Some(from), Some(to)) = (begin, end) {
                    level.set_span(from, to);
                }
                body = level;
            }
            return Ok(Some(body));
        }
        let node = Node::new(n.key(), Sort::of(&n.yields), kids, &n.literal);
        if let (Some(from), Some(to)) = (begin, end) {
            node.set_span(from, to);
            if let Some(at) = wrapped_at {
                if let Some(span) = node.children[at].children[0].span() {
                    node.children[at].set_span(span.0, span.1);
                }
            }
        }
        // A pattern declared as the negation of another builds the other and
        // wraps it, so the folded spelling and the `not` spelling are one
        // tree. The wrapper is named by the record, not known here.
        match &n.folds {
            None => Ok(Some(node)),
            Some(folds) => {
                let folded =
                    Node::new(folds, Sort::of("formula"), vec![node], &n.fold_literal);
                if let (Some(from), Some(to)) = (begin, end) {
                    folded.set_span(from, to);
                }
                Ok(Some(folded))
            }
        }
    }

    /// `condition` put in front of `body` as the long form writes it there,
    /// "δ > 0 and A and B". Conjunctions group to the left, so it goes at
    /// the far left of the body's run of them, by the join that run itself
    /// uses there; a body that is no such run is joined by `join`. Put in
    /// front of the whole run instead, "δ > 0 and (A and B)", it would build
    /// another tree than the long form does. A join that does not group to
    /// the left has no run to go into, and takes the body whole: "if ε > 0
    /// then if A then B".
    fn joined(&self, condition: Node, body: &Node, join: &Wrap) -> Node {
        let level = self
            .g
            .notations
            .iter()
            .find(|m| m.name == join.name)
            .filter(|m| m.assoc.as_deref() == Some("left"))
            .map(|m| m.level.clone());
        let in_run = |node: &Node| {
            !node.grouped() && node.children.len() == 2 && self.level_of(node) == level
        };
        let from = condition.span().map(|s| s.0);
        let spanned = |node: Node, over: &Node| {
            if let (Some(from), Some((_, to))) = (from, over.span()) {
                node.set_span(from, to);
            }
            node
        };
        if level.is_none() || !in_run(body) {
            let node = Node::new(
                &join.name,
                Sort::of(&join.yields),
                vec![condition, body.clone()],
                &join.literal,
            );
            return spanned(node, body);
        }
        let first = &body.children[0];
        let first = if in_run(first) {
            self.joined(condition, first, join)
        } else {
            // The new join is never a list's last, so it takes the run's
            // first pattern: "d > 1, A, and B" joins d > 1 to A by `_, _`,
            // and only B by `_, and _`.
            let literal = self
                .g
                .notations
                .iter()
                .find(|m| m.name == body.notation)
                .map_or(body.text.as_str(), |m| m.literal.as_str());
            let node = Node::new(
                &body.notation,
                body.sort.clone(),
                vec![condition, first.clone()],
                literal,
            );
            spanned(node, first)
        };
        let node = Node::new(
            &body.notation,
            body.sort.clone(),
            vec![first, body.children[1].clone()],
            &body.text,
        );
        spanned(node, body)
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
            let leaf = Node::leaf("name", Sort::of("variable"), &tok.text);
            leaf.set_span(tok.at, tok.at + tok.text.chars().count());
            return Ok(Some(leaf));
        }
        self.expression(barrier, stop)
    }
}
