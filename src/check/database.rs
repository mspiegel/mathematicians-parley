//! What the database files say of themselves: records, notation, symbols,
//! item statements, and the characters every file is written in.

use std::collections::BTreeSet;

use indexmap::{IndexMap, IndexSet};

use super::library::Known;
use super::Report;
use crate::corpus::records::allowed_fields;
use crate::corpus::{in_stdlib, Intro, Record, RecordKind, Theorem, PART_MARKERS};
use crate::formula::{parse_here, patterns_of, Node, Sorts, TERM_SORTS};
use crate::kinds;
use crate::regex;
use crate::sorts::{
    element_re, function_being_re, function_re, group_re, kind_re, let_formula,
    membership_re, not_in_re, part_re, property_re, sentences, settled,
    stated_record_sorts, unlabel, Env,
};
use crate::text::{prefix, repr};

pub fn check_characters(
    report: &mut Report,
    path: &str,
    text: &str,
    allowed: &IndexSet<char>,
) {
    for (at, line) in text.split('\n').enumerate() {
        for ch in line.chars() {
            if (ch as u32) < 128 || allowed.contains(&ch) {
                continue;
            }
            let name = unicode_names2::name(ch)
                .map(|n| n.to_string())
                .unwrap_or_else(|| "unnamed".to_string());
            report.say(
                path,
                at + 1,
                format!(
                    "character {} (U+{:04X}, {name}) is in no record of corpus/db/notation.records",
                    repr(&ch.to_string()),
                    ch as u32
                ),
            );
            return;
        }
    }
}

regex!(PART_SPLIT, r",\s*");

pub fn check_database(report: &mut Report, records: &[Record]) {
    let mut seen: IndexMap<(String, String), usize> = IndexMap::new();
    for r in records {
        // Notation and methods are one vocabulary; an item's name need only
        // be unique within its file, since it is cited with the file's path.
        let key = if matches!(r.kind, RecordKind::Notation | RecordKind::Method) {
            (r.kind.as_str().to_string(), r.name.clone())
        } else {
            ("item".to_string(), r.qualified())
        };
        if let Some(at) = seen.get(&key) {
            report.say(
                &r.path,
                r.line,
                format!("{} {} is already defined at line {at}", r.kind, r.name),
            );
        }
        seen.insert(key, r.line);
        for (name, no) in &r.repeats {
            report.say(
                &r.path,
                *no,
                format!(
                    "{} {} states {name} a second time; the two are joined into one field, so the second is not read on its own and saying it changes nothing",
                    r.kind, r.name
                ),
            );
        }
        if let Some(allowed) = allowed_fields(r.kind) {
            for name in r.fields.keys() {
                if !allowed.contains(&name.as_str()) {
                    let mut sorted: Vec<&str> = allowed.to_vec();
                    sorted.sort();
                    report.say(
                        &r.path,
                        r.lines.get(name).copied().unwrap_or(r.line),
                        format!(
                            "{} {} has a field {}, which a {} record does not have; its fields are {}",
                            r.kind,
                            r.name,
                            repr(name),
                            r.kind,
                            sorted.join(", ")
                        ),
                    );
                }
            }
        }
        if r.kind.is_item() {
            if !in_stdlib(&r.qualified()) {
                report.say(
                    &r.path,
                    r.line,
                    format!(
                        "{} {} is outside stdlib/; a definition or theorem the database states lives in the standard library",
                        r.kind, r.name
                    ),
                );
            }
            if !r.fields.contains_key("metamath") && !r.fields.contains_key("open") {
                report.say(
                    &r.path,
                    r.line,
                    format!(
                        "{} says neither which set.mm label supplies it nor that it is open",
                        r.name
                    ),
                );
            }
            // A definition that introduces a symbol says what it stands for
            // in `defines`, and that is its statement: what follows from it
            // is a theorem of its own.
            if r.conclusions.is_empty()
                && !r.fields.contains_key("open")
                && !r.fields.contains_key("defines")
            {
                report.say(&r.path, r.line, format!("{} has no `then` line", r.name));
            }
        }
        if r.kind == RecordKind::Method {
            if let Some(parts) = r.field("parts") {
                for part in PART_SPLIT.split(parts) {
                    let word = part.split_whitespace().next().unwrap_or("");
                    if !word.is_empty() && !PART_MARKERS.contains(&word) {
                        report.say(
                            &r.path,
                            r.line,
                            format!(
                                "method {} declares part {}, which is not a part marker",
                                r.name,
                                repr(word)
                            ),
                        );
                    }
                }
            }
        }
    }
}

regex!(TARGET_HOLE, r"_(\d+)");
regex!(CONTEXT_TOKEN, r"@[a-z]+");

/// A notation record declares a pattern, the sort of each hole, and what it
/// yields. Two things follow mechanically and are checked here.
pub fn check_notation(report: &mut Report, records: &[Record]) {
    for r in records {
        if r.kind != RecordKind::Notation {
            continue;
        }
        let raw = match r.field("pattern") {
            Some(raw) if !raw.is_empty() => raw,
            _ => {
                report.say(
                    &r.path,
                    r.line,
                    format!("notation {} declares no pattern", r.name),
                );
                continue;
            }
        };
        let patterns = patterns_of(str::trim(raw));
        let holes: Vec<&str> = r
            .field_or_empty("holes")
            .split(',')
            .map(str::trim)
            .filter(|h| !h.is_empty())
            .collect();
        let yields = str::trim(r.field_or_empty("yields"));

        // Where a hole or the result is a set, a function, a property, a
        // variable or any term, what it holds is a kind the text reads off,
        // and `kinds` says how the holes' kinds relate. One kind per hole.
        let want = if holes == ["none"] { 0 } else { holes.len() };
        let needs = holes.iter().any(|h| {
            matches!(*h, "set" | "function" | "property" | "variable" | "any")
        }) || matches!(yields, "set" | "function" | "any");
        let said = r.field("kinds").filter(|s| !s.is_empty());
        if needs && said.is_none() {
            report.say(
                &r.path,
                r.line,
                format!(
                    "notation {} has a {yields} or set-like hole and no `kinds` saying what it holds",
                    r.name
                ),
            );
        }
        if let Some(said) = said {
            match kinds::signature(str::trim(said)) {
                crate::outcome::Declined(d) => report.say(
                    &r.path,
                    r.line,
                    format!("notation {}: kinds {}", r.name, d.reason()),
                ),
                crate::outcome::Built(made) if made.holes() != want => report.say(
                    &r.path,
                    r.line,
                    format!(
                        "notation {} declares {want} hole(s) and kinds for {}",
                        r.name,
                        made.holes()
                    ),
                ),
                crate::outcome::Built(_) => {}
            }
        }

        // Every pattern of one record takes the same holes, so they must
        // agree on how many there are.
        let counts: BTreeSet<usize> =
            patterns.iter().map(|p| p.matches('_').count()).collect();
        if counts.len() != 1 || !counts.contains(&want) {
            let shown: Vec<String> = counts.iter().map(|c| c.to_string()).collect();
            report.say(
                &r.path,
                r.line,
                format!(
                    "notation {} declares {want} hole(s) but its pattern(s) have [{}]",
                    r.name,
                    shown.join(", ")
                ),
            );
        }

        // A `target` says what each pattern builds, one entry per pattern, so
        // the two lists have to line up and every hole has to be used. What
        // the entries name is checked against set.mm, which is not read here.
        if let Some(target) = r.field("target") {
            let entries: Vec<&str> = target
                .split(',')
                .map(str::trim)
                .filter(|e| !e.is_empty())
                .collect();
            if entries.len() != patterns.len() {
                report.say(
                    &r.path,
                    r.line,
                    format!(
                        "notation {} has {} pattern(s) but {} target entr(ies)",
                        r.name,
                        patterns.len(),
                        entries.len()
                    ),
                );
            }
            for entry in entries {
                if entry == "folded" {
                    continue;
                }
                let used: BTreeSet<usize> = TARGET_HOLE
                    .captures_iter(entry)
                    .map(|c| c[1].parse().unwrap_or(0))
                    .collect();
                let all: BTreeSet<usize> = (1..=want).collect();
                if used.iter().any(|&n| n < 1 || n > want) {
                    report.say(
                        &r.path,
                        r.line,
                        format!(
                            "notation {} target {} names a hole outside 1 to {want}",
                            r.name,
                            repr(entry)
                        ),
                    );
                } else if used != all
                    // A hole naming the group a context token takes the part
                    // from, as `H is a subgroup of G` names G, is left to it.
                    && !(CONTEXT_TOKEN.is_match(entry) && used.len() + 1 == want)
                {
                    report.say(
                        &r.path,
                        r.line,
                        format!(
                            "notation {} target {} leaves a hole out",
                            r.name,
                            repr(entry)
                        ),
                    );
                }
            }
        }

        // Associativity is needed exactly when the pattern can nest in
        // itself: both edges are holes, and what it yields fits those holes.
        for p in &patterns {
            let edges = p.starts_with('_') && p.ends_with('_');
            let nests = holes.contains(&yields)
                || (TERM_SORTS.contains(&yields) && holes.contains(&"any"));
            if edges && nests && !r.fields.contains_key("assoc") {
                report.say(
                    &r.path,
                    r.line,
                    format!(
                        "notation {} has a hole at each edge and yields {yields}, so {} can nest in itself and is ambiguous without an assoc",
                        r.name,
                        repr(p)
                    ),
                );
            }
            if !(edges && nests) && r.fields.contains_key("assoc") {
                report.say(
                    &r.path,
                    r.line,
                    format!(
                        "notation {} declares an assoc it does not need: {} cannot nest in itself",
                        r.name,
                        repr(p)
                    ),
                );
            }
        }
    }
}

/// A definition that introduces a symbol says which, and is alone in it.
///
/// Most definitions name a word for something the library already has and
/// introduce nothing. One that introduces a symbol is the case decision 12
/// of `GOALS.md` is about, wanting a definitional axiom "syntactically
/// checked to introduce one new symbol and be eliminable". It says so with a
/// `symbol` field naming the token, and a `defines` field giving the term the
/// token stands for.
///
/// What is checked here is what the corpus knows about itself: that the two
/// fields come together, that the token is one word, that no two definitions
/// claim the same token, and that some notation actually reaches it. Whether
/// the token is already a label of the library, and whether the term parses
/// and closes over its own variables, wants the library — which this checker
/// does not read — and is checked where the library is.
pub fn check_symbols(report: &mut Report, records: &[Record]) {
    let mut claimed: IndexMap<String, &Record> = IndexMap::new();
    for r in records {
        if r.kind != RecordKind::Definition {
            continue;
        }
        let token = str::trim(r.field_or_empty("symbol"));
        let body = str::trim(r.field_or_empty("defines"));
        if !token.is_empty() && body.is_empty() {
            report.say(
                &r.path,
                r.line,
                format!(
                    "definition {}: introduces {} and says nothing it stands for",
                    r.name,
                    repr(token)
                ),
            );
        }
        if !body.is_empty() && token.is_empty() {
            report.say(
                &r.path,
                r.line,
                format!(
                    "definition {}: defines a term and names no symbol for it",
                    r.name
                ),
            );
        }
        if token.is_empty() {
            continue;
        }
        if token.split_whitespace().count() != 1 {
            report.say(
                &r.path,
                r.line,
                format!("definition {}: {} is not one token", r.name, repr(token)),
            );
            continue;
        }
        if let Some(other) = claimed.get(token) {
            report.say(
                &r.path,
                r.line,
                format!(
                    "definition {}: {} is already introduced by definition {}",
                    r.name,
                    repr(token),
                    other.name
                ),
            );
            continue;
        }
        claimed.insert(token.to_string(), r);
    }
    // A symbol nothing reaches is a symbol the corpus cannot write. The
    // constant a definition introduces is `c` and the token, by the naming
    // set.mm uses for every other one.
    let mut reached: IndexSet<&str> = IndexSet::new();
    for r in records {
        if r.kind == RecordKind::Notation {
            reached.extend(r.field_or_empty("target").split_whitespace());
        }
    }
    for (token, r) in &claimed {
        if !reached.contains(format!("c{token}").as_str()) {
            report.say(
                &r.path,
                r.line,
                format!(
                    "definition {}: nothing writes c{token}, so the symbol it introduces cannot be reached",
                    r.name
                ),
            );
        }
    }
}

/// Every statement in the database parses, and parses one way.
///
/// An item's statement is a formula in the same language as a claim, and
/// the elaborator matches one against the other, so a statement that does
/// not read is a defect wherever it is written. An item proved in this
/// corpus keeps its statement at the head of its proof file and has none
/// here.
pub fn check_statements(
    report: &mut Report,
    records: &[Record],
    env: Env,
    record_sorts: &IndexMap<usize, Sorts>,
) {
    for (i, r) in records.iter().enumerate() {
        if !r.kind.is_item() {
            continue;
        }
        let sorts = &record_sorts[&i];
        for h in &r.hypotheses {
            if h.kind != Intro::Let {
                continue;
            }
            let body = str::trim(&unlabel(&h.text)).to_string();
            if let Some(said) = introduction_problem(&body, env, sorts) {
                report.say(&r.path, h.line, format!("{} {}: {said}", r.kind, r.name));
            }
        }
        let mut places: Vec<(&str, usize)> = r
            .hypotheses
            .iter()
            .filter(|h| h.kind == Intro::Assume)
            .map(|h| (h.text.as_str(), h.line))
            .collect();
        places.extend(r.conclusions.iter().map(|(t, n)| (t.as_str(), *n)));
        for (text, no) in places {
            for sentence in sentences(&unlabel(text)) {
                if let Err(p) = parse_here(&sentence, env.g, sorts) {
                    report.say(
                        &r.path,
                        no,
                        format!("{} {}: {}", r.kind, r.name, p.message),
                    );
                }
            }
        }
    }
}

/// A name an item treats as a number, a line of the item says what it is.
///
/// An item with no target is assumed exactly as it states itself, so a name
/// it leaves open is read as anything at all. An item that said `assume |X|
/// = k + 1` and never what k was held its hypotheses at k = −1 and X = ∅ and
/// not its conclusion, and the kernel accepted the axiom. A name standing
/// where the notation wants a number, which nothing says anything of, is
/// that shape.
///
/// This asks what the lines say, not what the name's sort is: `k + 1` makes
/// k a number, and that is the use being asked about, not an answer to it.
/// A name is spoken for where a `let` says what it is, where a binder
/// introduces it, or where a line puts it in a set said to hold numbers, as
/// `n ∈ ℕ₀` does in `nat0-as-int`, a statement true of every n. The set
/// must say so itself, through a notation or a `let`: a set read as holding
/// numbers only because its elements are added tells the kernel nothing.
///
/// It asks whether anything is said, not whether enough is: `let k ∈ ℤ`
/// where the statement needs `k ∈ ℕ₀` passes here.
pub fn check_unsorted(
    report: &mut Report,
    records: &[Record],
    env: Env,
    record_sorts: &IndexMap<usize, Sorts>,
) {
    let mut shapes: IndexMap<&str, Vec<&Vec<String>>> = IndexMap::new();
    for n in &env.g.notations {
        shapes.entry(n.key()).or_default().push(&n.holes);
        shapes.entry(n.name.as_str()).or_default().push(&n.holes);
    }
    let wanted = |node: &Node, i: usize| -> BTreeSet<String> {
        shapes
            .get(node.notation.as_str())
            .map(|all| {
                all.iter()
                    .filter(|h| i < h.len())
                    .map(|h| h[i].clone())
                    .collect()
            })
            .unwrap_or_default()
    };
    type Wanted<'w> = &'w dyn Fn(&Node, usize) -> BTreeSet<String>;
    fn bound(node: &Node, wanted: Wanted, out: &mut BTreeSet<String>) {
        for (i, kid) in node.children.iter().enumerate() {
            if wanted(node, i).contains("variable") {
                out.insert(kid.text.clone());
            }
            bound(kid, wanted, out);
        }
    }
    fn open_numbers(
        node: &Node,
        spoken: &BTreeSet<String>,
        wanted: Wanted,
        out: &mut Vec<String>,
    ) {
        for (i, kid) in node.children.iter().enumerate() {
            let w = wanted(node, i);
            if kid.is_name()
                && !spoken.contains(&kid.text)
                && w.len() == 1
                && w.contains("number")
            {
                out.push(kid.text.clone());
            }
            open_numbers(kid, spoken, wanted, out);
        }
    }

    /// Each name a membership in `node` puts in a set of numbers, the set's
    /// kind read with what the `let` lines say (`probe`).
    fn put_in_numbers(
        node: &Node,
        notations: &kinds::NotationKinds,
        probe: &mut kinds::Reader,
        store: &mut kinds::Store,
        line: usize,
        out: &mut BTreeSet<String>,
    ) {
        if let Some(sig) = notations.signature(&node.notation) {
            if sig.holes() == node.children.len() {
                for (element, set) in sig.members() {
                    let named = &node.children[element];
                    if !named.is_name() {
                        continue;
                    }
                    let held = probe.kind(
                        &node.children[set],
                        line.into(),
                        &IndexMap::new(),
                        store,
                    );
                    if let kinds::Kind::Set(inner) = store.find(&held) {
                        if store.find(&inner) == kinds::NUMBER {
                            out.insert(named.text.clone());
                        }
                    }
                }
            }
        }
        for kid in &node.children {
            put_in_numbers(kid, notations, probe, store, line, out);
        }
    }

    let notations = env.g.notation_kinds();
    for (i, r) in records.iter().enumerate() {
        if !r.kind.is_item() {
            continue;
        }
        let mut places: Vec<(&str, usize)> = r
            .hypotheses
            .iter()
            .filter(|h| h.kind == Intro::Assume)
            .map(|h| (h.text.as_str(), h.line))
            .collect();
        if r.kind == RecordKind::Theorem {
            places.extend(r.conclusions.iter().map(|(t, n)| (t.as_str(), *n)));
        }
        let mut trees: Vec<(usize, Node)> = Vec::new();
        for (text, no) in places {
            for sentence in sentences(&unlabel(text)) {
                let Ok(tree) = parse_here(&sentence, env.g, &record_sorts[&i]) else {
                    continue; // check_statements says so
                };
                trees.push((no, tree));
            }
        }
        // What the `let` lines say, and every name a line puts in a set
        // they or a notation say holds numbers.
        let stated = stated_record_sorts(r);
        let mut store = kinds::Store::default();
        let lets = kinds::read_lets(r, env, &stated, &mut store);
        let mut members: BTreeSet<String> = BTreeSet::new();
        for (no, tree) in &trees {
            let mut probe = kinds::Reader::new(env);
            probe.env = lets.env.clone();
            put_in_numbers(tree, &notations, &mut probe, &mut store, *no, &mut members);
        }
        let declared = settled(stated, &lets, &store);
        for (no, tree) in &trees {
            let mut spoken: BTreeSet<String> = declared.keys().cloned().collect();
            spoken.extend(members.iter().cloned());
            bound(tree, &wanted, &mut spoken);
            let mut found = Vec::new();
            open_numbers(tree, &spoken, &wanted, &mut found);
            let mut said: IndexSet<String> = IndexSet::new();
            for name in found {
                if said.insert(name.clone()) {
                    report.say(
                        &r.path,
                        *no,
                        format!(
                            "{} {}: {name} stands where a number goes, and no line says what {name} is",
                            r.kind, r.name
                        ),
                    );
                }
            }
        }
    }
}

/// Every form a `let` line takes, with what each is called.
fn introductions() -> [(&'static str, &'static regex::Regex); 9] {
    [
        ("a membership", membership_re()),
        ("a thing not in a set", not_in_re()),
        ("an arbitrary element", element_re()),
        ("an arbitrary set or point", kind_re()),
        ("a function", function_re()),
        ("a function with a property", function_being_re()),
        ("a part of a set", part_re()),
        ("a group", group_re()),
        ("a property", property_re()),
    ]
}

regex!(ARROW, r"^\S+\s*:\s*.+→\s*(\S+)$");

fn sort_name(word: &str) -> bool {
    TERM_SORTS.contains(&word)
        || matches!(word, "formula" | "function" | "property" | "variable")
}

/// What is wrong with a `let` body, or None. Used for a proof's lines and
/// for an item's alike, since an item states its hypotheses the same way.
pub fn introduction_problem(body: &str, env: Env, sorts: &Sorts) -> Option<String> {
    let forms = introductions();
    if !forms.iter().any(|(_, p)| p.is_match(body)) {
        let names: Vec<&str> = forms.iter().map(|(n, _)| *n).collect();
        return Some(format!(
            "`let {}` is none of the {} introductions: {}",
            prefix(body, 40),
            forms.len(),
            names.join(", ")
        ));
    }
    // A function's type is a function into a set, and nothing else: `let g
    // : Y → X is one-to-one` fits the shape with "X is one-to-one" for the
    // set, which is a statement, and the property it states was never asked
    // for.
    if function_re().is_match(body) && !function_being_re().is_match(body) {
        if let Ok(node) = parse_here(body, env.g, sorts) {
            if node.notation != "function-type" {
                return Some(format!(
                    "`let {}` says more than a function's type; a property of it follows `be`, as `let f : A → B be one-to-one`",
                    prefix(body, 40)
                ));
            }
        }
    }
    if function_being_re().is_match(body)
        && parse_here(&let_formula(body), env.g, sorts).is_err()
    {
        return Some(format!(
            "`let {}` says the function is something no notation says a function is",
            prefix(body, 40)
        ));
    }
    // A function's codomain is a set. A sort is a label for what kind of
    // thing a name is, and there is no set of formulas to map into: writing
    // one there says a property is a function, which it is not.
    if let Some(arrow) = ARROW.captures(body) {
        if sort_name(&arrow[1]) {
            return Some(format!(
                "`let {}` sends a function into {}, which is a sort and not a set; a property is introduced with `be a property of the elements of`",
                prefix(body, 40),
                repr(&arrow[1])
            ));
        }
    }
    None
}

regex!(LET_KEYWORD, r"^\s*let\s+");

/// A `let` line carries an introduction, not a formula. It names something
/// and says what it is, and `introductions` is every form one takes; what it
/// asserts is only what `be` says of a function it names. `assume` takes a
/// formula, because it does assert.
pub fn check_introductions(
    report: &mut Report,
    thm: &Theorem,
    env: Env,
    known: &Known,
) {
    let mut lines: Vec<(Intro, &str, usize)> = thm
        .hypotheses
        .iter()
        .map(|h| (h.kind, h.text.as_str(), h.line))
        .collect();
    for s in &thm.steps {
        lines.extend(s.openers.iter().map(|o| (o.kind, o.text.as_str(), o.line)));
    }
    for (kind, text, no) in lines {
        if kind != Intro::Let {
            continue;
        }
        let body = LET_KEYWORD.replace(text, "");
        let body = str::trim(&unlabel(&body)).to_string();
        if let Some(said) = introduction_problem(&body, env, &known.sorts) {
            report.say(&thm.path, no, said);
        }
    }
}
