//! What the formulas on the page say: that each reads, that their sorts
//! fit, and that the methods which relate formulas are given the shapes
//! they need.

use std::collections::BTreeSet;

use indexmap::{IndexMap, IndexSet};

use super::library::{Known, Library};
use super::structure::{defined_below, introduced};
use super::{Report, RELATIONS};
use crate::corpus::proof::requires_item;
use crate::corpus::{
    cited_item, define_parts, outermost, DefineParts, FileScope, Intro, Item,
    Justification, Method, Recursion, Step, Theorem,
};
use crate::formula::{parse_here, walk, Node, Sort, Sorts};
use crate::matching::{alike_top, instantiation, substitute, Binding};
use crate::outcome::{Built, Checked, Declined};
use crate::regex;
use crate::sorts::infer::{self, Reader, Store};
use crate::sorts::{sentences, unlabel, Env};

/// The sorts an item's statement relates fit, as its reading found.
pub fn check_item_clashes(
    report: &mut Report,
    statements: &IndexMap<String, Reader>,
    names: &IndexMap<String, Item>,
) {
    for (name, reader) in statements {
        let path = names.get(name).map_or("", |i| i.path());
        for c in &reader.clashes {
            report.say(path, c.line, format!("{name}: {}: {}", c.what, c.why));
        }
    }
}

/// A proof's names, read off how it uses them: the theorem's one reading.
///
/// `READERS.md`: a set's sort says what it holds, nobody writes it, and a
/// set of any sort stays of any sort. Each line is read in the order it is
/// written — a `let` shadows an earlier name, since blocks reuse letters —
/// and each citation's written `v := t` is fitted to a fresh copy of what
/// the cited statement says v is. What the reading settles is the theorem's
/// sorts (`sorts::settled`), and what does not fit is `check_clashes`'s to
/// report.
pub fn read_with_citations(
    thm: &Theorem,
    env: Env,
    statements: &IndexMap<String, Reader>,
    store: &mut Store,
) -> Reader {
    let mut cite = |reader: &mut Reader, store: &mut Store, step: &Step| {
        cited_sorts(reader, store, step, env, statements);
    };
    infer::read_theorem(thm, env, store, Some(&mut cite))
}

/// What a proof's names are fits, as its reading found (`read_with_citations`).
///
/// What does not fit is reported where it is: two sorts joined where one is
/// wanted, an element of a set of numbers said to be a set, and a set
/// declared of any sort that a citation would narrow.
pub fn check_clashes(report: &mut Report, thm: &Theorem, clashes: &[infer::Clash]) {
    for c in clashes {
        report.say(&thm.path, c.line, format!("{}: {}", c.what, c.why));
    }
}

/// Each written `v := t` of a step's citations, fitted to the cited
/// statement. Each citation takes its own copy of what the statement says v
/// is.
fn cited_sorts(
    reader: &mut Reader,
    store: &mut Store,
    step: &Step,
    env: Env,
    statements: &IndexMap<String, Reader>,
) {
    let mut cites: Vec<(String, &str)> = Vec::new();
    if let Some(item) = cited_item(&step.just) {
        cites.push((step.just.item(&item), &step.just.text));
    }
    for req in &step.requires {
        if let Some((cited, _)) = requires_item(&req.how) {
            cites.push((step.just.item(&cited), &req.how));
        }
    }
    for (name, text) in cites {
        let Some(stated) = statements.get(&name) else {
            continue;
        };
        let mut seen = IndexMap::new();
        for (v, t) in instantiation(text) {
            let Some(wanted) = stated.env.get(&v) else {
                continue;
            };
            let Ok(tree) = parse_here(&t, env.g, &reader.sorts(store)) else {
                continue;
            };
            let got = reader.sort_of(&tree, step.line.into(), &IndexMap::new(), store);
            let copied = store.copy(wanted, &mut seen);
            if let Declined(said) = store.unify(&got, &copied) {
                reader.clashes.push(infer::Clash {
                    line: step.line.into(),
                    what: format!("citing {name} with {v} := {t}"),
                    why: said.reason(),
                });
            }
        }
    }
}

/// Every formula on the page parses, and parses one way.
///
/// A claim, an `assume` or `suppose` line, the fact of a `requires` line and
/// the theorem's statement are all formulas, read from the declared
/// notations. One that does not parse is a defect in the text or a notation
/// nobody declared. One that parses two ways is worse, because the reader
/// and the kernel could take it differently and nothing downstream would
/// notice, so the parser refuses it rather than choosing.
///
/// This is the pass that says so, and it reaches every one of them. That is
/// what lets the passes which merely gather — sorts, the names a `fix`
/// binds, the trees an item states — skip a formula they cannot read and
/// carry on: it has been reported here, once, with the line it is on.
pub fn check_formulas(report: &mut Report, thm: &Theorem, env: Env, known: &Known) {
    let own = introduced(thm);
    let mut places: Vec<(usize, String, String)> = thm
        .steps
        .iter()
        .map(|s| (s.line, format!("step {}", s.number), s.claim_text()))
        .collect();
    for s in &thm.steps {
        for r in &s.requires {
            places.push((
                r.line,
                format!("the requires line of step {}", s.number),
                r.fact.clone(),
            ));
        }
    }
    let mut lines: Vec<(Intro, &str, usize)> = thm
        .hypotheses
        .iter()
        .map(|h| (h.kind, h.text.as_str(), h.line))
        .collect();
    for s in &thm.steps {
        lines.extend(s.openers.iter().map(|o| (o.kind, o.text.as_str(), o.line)));
    }
    for (k, t, n) in lines {
        if matches!(k, Intro::Assume | Intro::Suppose) {
            places.push((
                n,
                format!("the `{k}` line"),
                str::trim(&unlabel(&t[k.as_str().len()..])).to_string(),
            ));
        }
    }
    places.push((
        thm.line,
        format!("the statement of {}", thm.name),
        thm.conclusion.clone(),
    ));
    for (line, what, text) in places {
        for sentence in sentences(&text) {
            if let Err(p) = parse_here(&sentence, env.g, &known.sorts) {
                // A name the file defines only further down is why, and
                // `check_defined_below` says so: above its define it names
                // nothing, and `U(0)` then reads several ways because
                // nothing says U is a function.
                if defined_below(thm, &sentence, &own, env.scopes).is_empty() {
                    report.say(&thm.path, line, format!("{what}: {}", p.message));
                }
            }
        }
    }
}

/// True when a is b with a negation in front.
///
/// A folded negation counts, because a record declaring `negates` makes "n
/// is not odd" the same tree as "not (n is odd)". `wrappers` is the set of
/// notations those records name, so no notation is known here by its text.
fn negates(a: Option<&Node>, b: Option<&Node>, wrappers: &IndexSet<String>) -> bool {
    let (Some(a), Some(b)) = (a, b) else {
        return false;
    };
    !a.children.is_empty()
        && wrappers.contains(&a.notation)
        && a.children[0].shape() == b.shape()
}

fn wrappers(env: Env) -> IndexSet<String> {
    env.g
        .notations
        .iter()
        .filter_map(|n| n.folds.clone())
        .collect()
}

/// A contradiction block relates its supposition to its claim, and closes
/// with a formula and that formula's negation.
///
/// `METHODS.md` specifies the two shapes: the supposition is the claim
/// negated, which is reductio, or the claim is the supposition negated,
/// which proves a negation directly. No formula is its own double negation,
/// so at most one holds and the expansion each needs is never in doubt.
/// Anything else the method refuses, which is why this is reported rather
/// than left to fail later with nothing to point at.
pub fn check_contradiction(
    report: &mut Report,
    thm: &Theorem,
    env: Env,
    known: &Known,
) {
    let wrappers = wrappers(env);
    for step in &thm.steps {
        if !step.just.head.is(Method::Contradiction) {
            continue;
        }
        let Some(opener) = step.openers.iter().find(|o| o.kind == Intro::Suppose)
        else {
            continue; // already reported as a missing suppose
        };
        let rest = &opener.text[opener.kind.as_str().len()..];
        let supposed = known.read(str::trim(&unlabel(rest)));
        let claimed = known.read(&step.claim_text());
        let (Some(supposed), Some(claimed)) = (supposed, claimed) else {
            continue; // already reported as unreadable
        };
        if !(negates(Some(&supposed), Some(&claimed), &wrappers)
            || negates(Some(&claimed), Some(&supposed), &wrappers))
        {
            report.say(
                &thm.path,
                step.line,
                format!(
                    "step {} supposes something that is neither its claim negated nor the thing its claim negates, so neither expansion of `contradiction` applies",
                    step.number
                ),
            );
        }
        let inside: Vec<&Step> = thm
            .steps
            .iter()
            .filter(|s| {
                s.number.len() > step.number.len()
                    && s.number.prefix(step.number.len()) == step.number
            })
            .collect();
        let Some(last_step) = inside.last() else {
            continue;
        };
        let last = sentences(&last_step.claim_text());
        let pair: Vec<Option<Node>> = if last.len() == 2 {
            last.iter().map(|s| known.read(s)).collect()
        } else {
            Vec::new()
        };
        let closes = pair.len() == 2
            && (negates(pair[0].as_ref(), pair[1].as_ref(), &wrappers)
                || negates(pair[1].as_ref(), pair[0].as_ref(), &wrappers));
        if !closes {
            report.say(
                &thm.path,
                last_step.line,
                format!(
                    "step {} ends a contradiction block and does not state a formula and that formula negated",
                    last_step.number
                ),
            );
        }
    }
}

/// One link of a calculation.
pub struct Link {
    /// What the link claims: `previous rel t`.
    pub claim: String,
    /// Its two terms, where the first line says where its relation stands.
    pub sides: Option<(String, String)>,
    /// What it cites.
    pub cite: String,
    pub line: usize,
}

/// Each link of a calculation. The first line is written whole; each later
/// one writes its relation and new term, and the previous term is the one
/// before it.
pub fn chain_links(just: &Justification) -> Vec<Link> {
    let mut out = Vec::new();
    if !just.head.is(Method::Calculation) {
        return out;
    }
    let mut previous: Option<String> = None;
    for (text, no) in &just.chain {
        let whole = str::trim(text);
        let (body, cite) = match whole.rfind(' ') {
            Some(at) => (&whole[..at], &whole[at + 1..]),
            None => ("", whole),
        };
        let body = str::trim(body);
        let (claim, sides);
        match &previous {
            None => {
                let words: Vec<&str> = body.split_whitespace().collect();
                let at = RELATIONS.iter().find_map(|r| outermost(&words, r));
                claim = body.to_string();
                let before = match at {
                    Some(at) => words[at + 1..].join(" "),
                    None => String::new(),
                };
                sides = at.map(|at| (words[..at].join(" "), before.clone()));
                previous = Some(before);
            }
            Some(prev) => {
                let (mark, added) = match body.find(' ') {
                    Some(at) => (&body[..at], &body[at + 1..]),
                    None => (body, ""),
                };
                let added = str::trim(added).to_string();
                claim = format!("{prev} {mark} {added}");
                sides = Some((prev.clone(), added.clone()));
                previous = Some(added);
            }
        }
        out.push(Link {
            claim,
            sides,
            cite: cite.to_string(),
            line: *no,
        });
    }
    out
}

/// Whether two terms differ only in pieces with no letter in them.
///
/// `2/1 − 2/(n + 1)` and `2 − 2/(n + 1)` differ in `2/1` against `2`, and a
/// chain link between them uses that fact and no other. The terms are walked
/// in step; where they part, both pieces must be numerals alone.
fn changed_closed(sides: &Option<(String, String)>, env: Env, sorts: &Sorts) -> bool {
    let Some((one, other)) = sides else {
        return false;
    };
    let (Ok(one), Ok(other)) = (
        parse_here(one, env.g, sorts),
        parse_here(other, env.g, sorts),
    ) else {
        return false;
    };
    fn alike(a: &Node, b: &Node) -> bool {
        if a.shape() == b.shape() {
            return true;
        }
        if a.names().is_empty() && b.names().is_empty() {
            return true;
        }
        if a.notation != b.notation
            || a.text != b.text
            || a.children.len() != b.children.len()
        {
            return false;
        }
        a.children
            .iter()
            .zip(b.children.iter())
            .all(|(x, y)| alike(x, y))
    }
    alike(&one, &other)
}

regex!(
    ARITHMETIC_SOURCE,
    r"^substitute\s+(.*?)\s*\(\s*arithmetic\s*\)"
);

/// `arithmetic` stands in for a line only where the fact is numerals alone.
///
/// A `substitute` may take its equation from `arithmetic`, and a chain link
/// may give `arithmetic` as its reason, because a claim with no letter in it
/// gives a reader nothing to check but working it out. One with a letter has
/// something to check, and is a numbered step of its own. A link whose terms
/// have letters but change only where they have none uses a fact of numerals
/// alone (`changed_closed`). `SYNTAX.md` has the rule.
pub fn check_closed_arithmetic(
    report: &mut Report,
    thm: &Theorem,
    env: Env,
    known: &Known,
) {
    let closed = |text: &str| -> bool {
        match parse_here(text, env.g, &known.sorts) {
            Ok(n) => n.names().is_empty(),
            Err(_) => true, // `check_formulas` says it does not read
        }
    };
    for step in &thm.steps {
        let just = &step.just;
        if just.head.is(Method::Substitute) {
            if let Some(m) = ARITHMETIC_SOURCE.captures(&just.text) {
                if !closed(&m[1]) {
                    report.say(
                        &thm.path,
                        just.line,
                        format!(
                            "step {} takes {} from arithmetic, and it has a letter in it; a fact with a letter is a numbered step of its own",
                            step.number, &m[1]
                        ),
                    );
                }
            }
        }
        for Link {
            claim,
            sides,
            cite,
            line: no,
        } in chain_links(just)
        {
            if cite == "arithmetic"
                && !closed(&claim)
                && !changed_closed(&sides, env, &known.sorts)
            {
                report.say(
                    &thm.path,
                    no,
                    format!(
                        "a link of step {} names arithmetic for {claim}, which changes something with a letter in it; a link may name arithmetic where only pieces of numerals alone change, and any other cites the numbered step that states it",
                        step.number
                    ),
                );
            }
        }
    }
}

/// `membership` claims that a term is in a number system, and nothing else
/// (`METHODS.md`), or that every member of a set has a term in one.
pub fn check_membership_claims(
    report: &mut Report,
    thm: &Theorem,
    env: Env,
    known: &Known,
) {
    fn says_membership(node: &Node) -> bool {
        if node.notation == "for-every" && node.children.len() == 3 {
            return says_membership(&node.children[2]);
        }
        node.notation == "membership"
            && node.children.len() == 2
            && node.children[1].notation == "number-systems"
    }
    for step in &thm.steps {
        if !step.just.head.is(Method::Membership) {
            continue;
        }
        for sentence in sentences(&step.claim_text()) {
            let Ok(node) = parse_here(&sentence, env.g, &known.sorts) else {
                continue; // `check_formulas` says it does not read
            };
            if !says_membership(&node) {
                report.say(
                    &thm.path,
                    step.just.line,
                    format!(
                        "step {} names membership for {sentence}, which says no term is in a number system",
                        step.number
                    ),
                );
            }
        }
    }
}

/// Each link of a calculation cites a line that says it.
///
/// `SYNTAX.md`: a link `rel t  L` cites one line whose claim is exactly the
/// previous term rel t, read either way round where it is an equation. A
/// line saying `a(0) = M` does not say `gcd(a(0), b(0)) = gcd(M, b(0))`:
/// that is a substitution, a step of its own. A line of several sentences,
/// or a conjunction, says each of them. A link naming `arithmetic` is
/// `check_closed_arithmetic`'s, and one citing a define is the define's
/// reading of the name.
pub fn check_chain_links(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let scope = &scopes[thm.scope];
    let mut defines: BTreeSet<&str> =
        thm.defines.iter().map(|d| d.label.as_str()).collect();
    defines.extend(scope.defines.iter().map(|d| d.label.as_str()));
    defines.extend(scope.imports.iter().map(|i| i.label.as_str()));
    for step in &thm.steps {
        for Link {
            claim,
            cite,
            line: no,
            ..
        } in chain_links(&step.just)
        {
            if cite == "arithmetic"
                || defines.contains(cite.as_str())
                || !known.scope(step).contains_key(&cite)
            {
                continue;
            }
            let Some(said) = known.read(&claim) else {
                continue; // `check_formulas` says it does not read
            };
            let lines = known.lines_say(step, &[cite.as_str()], library);
            if !lines.iter().any(|x| alike_top(&said, x, &library.ctx)) {
                report.say(
                    &thm.path,
                    no,
                    format!(
                        "a link of step {} cites {cite}, which does not say {claim}; a link cites the line that states it, and a substitution is a step of its own",
                        step.number
                    ),
                );
            }
        }
    }
}

/// The name the define carrying `label` gives, or None: one this theorem
/// writes, one its file writes, or one its file imports under an alias.
fn define_named(thm: &Theorem, label: &str, scopes: &[FileScope]) -> Option<String> {
    let scope = &scopes[thm.scope];
    for d in thm.defines.iter().chain(scope.defines.iter()) {
        if d.label == label {
            return match define_parts(&d.text) {
                Built(said) => said.name().map(String::from),
                Declined(_) => None,
            };
        }
    }
    scope
        .imports
        .iter()
        .find(|i| i.label == label)
        .map(|i| i.alias.clone())
}

/// The define by recursion this theorem writes under `label`, or None where
/// the label is another kind of define or none.
fn recursion_cited(thm: &Theorem, label: &str) -> Option<Recursion> {
    let d = thm.defines.iter().find(|d| d.label == label)?;
    match define_parts(&d.text) {
        Built(DefineParts::Recursion(r)) => Some(r),
        _ => None,
    }
}

/// What the define by recursion says `name` is at the argument `at`, as
/// (the rule's term there, the index it is taken at, or None at 0); or None
/// where `at` is neither 0 nor something plus one.
fn recursion_value(
    said: &Recursion,
    name: &str,
    at: &Node,
    env: Env,
    sorts: &Sorts,
) -> Checked<Option<(Node, Option<Node>)>> {
    let (rule, index) = if at.notation == "numeral" && at.text == "0" {
        (&said.start[name], None)
    } else if at.notation == "additive"
        && at.text == "+"
        && at.children.len() == 2
        && at.children[1].notation == "numeral"
        && at.children[1].text == "1"
    {
        (&said.step[name], Some(at.children[0].clone()))
    } else {
        return Ok(None);
    };
    let mut local = sorts.clone();
    local.insert(said.index.clone(), Sort::of("number"));
    let mut term = parse_here(rule, env.g, &local)?;
    if let Some(index) = &index {
        let mut put = Binding::new();
        put.insert(said.index.clone(), index.clone());
        term = substitute(&term, &put);
    }
    Ok(Some((term, index)))
}

/// The value a term by cases takes where the facts say which case, or why
/// no case is said. A term not by cases is its own value.
enum Case {
    Value(Node),
    Unsaid(&'static str),
}

fn case_taken(
    node: &Node,
    said: &[&str],
    facts: &[Node],
    wrappers: &IndexSet<String>,
) -> Case {
    let mut node = node.clone();
    while node.notation == "by-cases" && node.children.len() == 3 {
        let (value, condition, rest) = (
            node.children[0].clone(),
            node.children[1].clone(),
            node.children[2].clone(),
        );
        if said.contains(&condition.shape()) {
            return Case::Value(value);
        }
        if facts
            .iter()
            .any(|f| negates(Some(f), Some(&condition), wrappers))
        {
            node = rest;
            continue;
        }
        return Case::Unsaid(
            "no line it cites says whether a case's condition holds or fails",
        );
    }
    Case::Value(node)
}

/// What is wrong with a step's claim, read as one equation a define by
/// recursion gives; None where nothing is.
///
/// One side is a sequence at 0 or at X + 1, and the other is what the define
/// says it is there: the value at 0, or the rule at k + 1 with X for k, in
/// the case the cited lines say it is in. At X + 1 a cited line says X ∈ ℕ₀,
/// since the rule holds only at a step the index takes.
fn recursion_equation(
    claims: &[Node],
    facts: &[Node],
    said: &Recursion,
    env: Env,
    sorts: &Sorts,
    wrappers: &IndexSet<String>,
    equals: &IndexSet<String>,
) -> Option<String> {
    if claims.len() != 1 || !equals.contains(&claims[0].notation) {
        return Some(
            "claims no one equation; a define says what its names are equal to"
                .to_string(),
        );
    }
    let said_shapes: Vec<&str> = facts.iter().map(|f| f.shape()).collect();
    let mut why: Option<String> = Some(format!(
        "its claim has none of {} applied on either side",
        said.names.join(", ")
    ));
    let kids = &claims[0].children;
    let orders = [(&kids[0], &kids[1]), (&kids[1], &kids[0])];
    for (one, other) in orders {
        if !(one.notation == "application"
            && one.children.len() == 2
            && one.children[0].is_name()
            && said.names.contains(&one.children[0].text))
        {
            continue;
        }
        why = None;
        let name = &one.children[0].text;
        let Ok(found) = recursion_value(said, name, &one.children[1], env, sorts)
        else {
            continue; // `check_formulas` says it does not read
        };
        let Some((term, index)) = found else {
            why = Some(format!(
                "{name} is given at 0 and at {} + 1, and nowhere else",
                said.index
            ));
            continue;
        };
        if let Some(index) = &index {
            let said_in = facts.iter().any(|f| {
                f.notation == "membership"
                    && f.children.len() == 2
                    && f.children[0].shape() == index.shape()
                    && f.children[1].text == said.domain
            });
            if !said_in {
                why = Some(format!(
                    "no line it cites says the index is in {}",
                    said.domain
                ));
                continue;
            }
        }
        match case_taken(&term, &said_shapes, facts, wrappers) {
            Case::Unsaid(reason) => {
                why = Some(reason.to_string());
                continue;
            }
            Case::Value(got) => {
                if got.shape() == other.shape() {
                    return None;
                }
            }
        }
    }
    Some(match why {
        Some(why) if !why.is_empty() => {
            format!("claims a value it does not give: {why}")
        }
        _ => "claims a value it does not give".to_string(),
    })
}

/// A define by recursion says each value from the values before it.
///
/// A value at 0 names none of the sequences, and a rule at k + 1 names them
/// only at k: `a(k + 1) := a(k + 1) + 1` says nothing, and `a(k + 1) :=
/// a(k − 1)` reaches a value the rule has not given yet. Each rule reads,
/// since a rule that does not is a value nobody can cite.
///
/// Nor does a rule name k itself, outside a value at k: set.mm's recursion
/// steps from the values alone, so `c(k + 1) := c(k) + k` has no reading
/// there. A sequence that needs its index keeps it as a value of its own,
/// `i(0) := 0, i(k + 1) := i(k) + 1`.
pub fn check_recursions(report: &mut Report, thm: &Theorem, env: Env, known: &Known) {
    for d in &thm.defines {
        let Built(DefineParts::Recursion(said)) = define_parts(&d.text) else {
            continue;
        };
        let mut local = known.sorts.clone();
        local.insert(said.index.clone(), Sort::of("number"));
        let label = &d.label;
        for (given, at) in [(&said.start, None), (&said.step, Some(&said.index))] {
            for (name, rule) in given {
                let place = match at {
                    None => format!("{name}(0)"),
                    Some(at) => format!("{name}({at} + 1)"),
                };
                let tree = match parse_here(rule, env.g, &local) {
                    Ok(tree) => tree,
                    Err(p) => {
                        report.say(
                            &thm.path,
                            d.line,
                            format!(
                                "define {label}: the rule for {place} does not read: {}",
                                p.message
                            ),
                        );
                        continue;
                    }
                };
                let applied = |node: &Node| {
                    node.notation == "application"
                        && node.children.len() == 2
                        && node.children[0].is_name()
                        && said.names.contains(&node.children[0].text)
                };
                let nodes = walk(std::slice::from_ref(&tree));
                let at_k: BTreeSet<usize> = nodes
                    .iter()
                    .filter(|n| applied(n))
                    .map(|n| n.children[1].id())
                    .collect();
                if nodes.iter().any(|n| {
                    n.is_name() && n.text == said.index && !at_k.contains(&n.id())
                }) {
                    report.say(
                        &thm.path,
                        d.line,
                        format!(
                            "define {label}: the rule for {place} names {} outside a value at {}; a step sees only the values",
                            said.index, said.index
                        ),
                    );
                }
                for node in &nodes {
                    if !applied(node) {
                        continue;
                    }
                    let arg = &node.children[1];
                    if let Some(at) = at {
                        if arg.is_name() && arg.text == *at {
                            continue;
                        }
                    }
                    let message = match at {
                        Some(_) => format!(
                            "define {label}: the rule for {place} names {} at a place other than {}",
                            node.children[0].text, said.index
                        ),
                        None => format!(
                            "define {label}: the value of {place} names {}, which has no value before 0",
                            node.children[0].text
                        ),
                    };
                    report.say(&thm.path, d.line, message);
                    break;
                }
            }
        }
    }
}

/// A step citing a define claims what the define says the name is.
///
/// The claim is an equation with the name on one side, applied or not, and
/// its value on the other, in either order. Written out, the two sides are
/// one term. Where the define is by cases, the lines the step cites say
/// which case it is in, by its condition or that condition's negation, and
/// the value is the one that case gives: `h(t) = g⁻¹(t)` cites D2 from a
/// line saying t ∉ C.
pub fn check_define_citation(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
    scopes: &[FileScope],
) {
    let env = library.env;
    let wrappers = wrappers(env);
    for step in &thm.steps {
        let just = &step.just;
        if just.head != crate::corpus::Head::Define {
            continue;
        }
        let label = just.defined.clone().unwrap_or_default();
        let say = format!("step {} cites {label}", step.number);
        if let Some(recursion) = recursion_cited(thm, &label) {
            let parts = known.parts(step, library);
            if let Some(why) = recursion_equation(
                &parts.claims,
                &parts.facts,
                &recursion,
                env,
                &known.sorts,
                &wrappers,
                &library.ctx.equations,
            ) {
                report.say(&thm.path, just.line, format!("{say} and {why}"));
            }
            continue;
        }
        let Some(name) = define_named(thm, &label, scopes) else {
            report.say(
                &thm.path,
                just.line,
                format!("{say}, which no define in scope carries"),
            );
            continue;
        };
        let parts = known.parts(step, library);
        let written: Result<Vec<Node>, _> = sentences(&step.claim_text())
            .iter()
            .map(|s| parse_here(s, env.g, &known.sorts))
            .collect();
        let Ok(written) = written else {
            continue;
        };
        if parts.claims.len() != 1
            || written.len() != 1
            || !library.ctx.equations.contains(&parts.claims[0].notation)
        {
            report.say(
                &thm.path,
                just.line,
                format!("{say} and claims no one equation; a define says what its name is equal to"),
            );
            continue;
        }
        let named: BTreeSet<String> = written[0]
            .walk()
            .iter()
            .filter(|n| n.is_name())
            .map(|n| n.text.clone())
            .collect();
        if !named.contains(&name) {
            report.say(
                &thm.path,
                just.line,
                format!("{say} and its claim never names {name}"),
            );
            continue;
        }
        let (left, right) =
            (&parts.claims[0].children[0], &parts.claims[0].children[1]);
        let said: Vec<&str> = parts.facts.iter().map(|f| f.shape()).collect();
        let mut why: Option<&str> = None;
        let mut gives = false;
        for (one, other) in [(left, right), (right, left)] {
            match case_taken(one, &said, &parts.facts, &wrappers) {
                Case::Unsaid(reason) => {
                    why = why.or(Some(reason));
                    continue;
                }
                Case::Value(got) => {
                    if got.shape() == other.shape() {
                        gives = true;
                        break;
                    }
                }
            }
        }
        if !gives {
            let tail = why.map(|w| format!(": {w}")).unwrap_or_default();
            report.say(
                &thm.path,
                just.line,
                format!("{say} and claims a value it does not give{tail}"),
            );
        }
    }
}
