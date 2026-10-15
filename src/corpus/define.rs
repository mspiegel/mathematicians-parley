//! What a `define` line says.

use indexmap::IndexMap;

use crate::outcome::{Built, Declined, Route};
use crate::regex;
use crate::text::{repr, squash};

/// What a `define` line says: a name, and the term it stands for.
///
/// A name with a parameter is a function, as a reader writes
/// "S(m) = 1 + 2 + … + m": `define S(m) := Σ(j = 1 to m) j, for m ∈ ℕ`. Its
/// domain is said with it, because a rule without one says what S does and
/// not where S is defined. A function of two arguments says each one's
/// domain in order: `define G(a, n) := Σ(j = 0 to n) a^j, for a ∈ ℝ, n ∈
/// ℕ₀`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Define {
    pub name: String,
    pub body: String,
    /// The arguments, in the order the name takes them; none for a name
    /// that stands for a term.
    pub params: Vec<Param>,
    /// What kind of number a let says its name is, in a reader's words:
    /// `let m = gcd(s, w), a natural number`. The reason is the line under
    /// it (`DefineLine::reason`).
    pub kind: Option<String>,
}

/// One argument of a defined function, and the set it runs over.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub domain: String,
}

/// What a `define` of sequences by recursion says: each name's value at 0,
/// and its value at k + 1 in terms of the values at k.
///
/// `define a(0) := M, b(0) := N, a(k + 1) := b(k), b(k + 1) := a(k) mod
/// b(k), for k ∈ ℕ₀` defines two sequences together, as a textbook writes
/// Euclid's algorithm; one name alone is the same form with one sequence.
/// `start` and `step` hold each name's rule as written, a rule by cases
/// already folded into `_ if _, _ otherwise` as a `Define` folds one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Recursion {
    pub names: Vec<String>,
    pub index: String,
    pub domain: String,
    pub start: IndexMap<String, String>,
    pub step: IndexMap<String, String>,
}

/// A define read into its parts: one name, or sequences by recursion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefineParts {
    One(Define),
    Recursion(Recursion),
}

impl DefineParts {
    /// The names the define gives.
    pub fn names(&self) -> Vec<String> {
        match self {
            DefineParts::One(d) => vec![d.name.clone()],
            DefineParts::Recursion(r) => r.names.clone(),
        }
    }

    /// The one define, where this is not a recursion.
    pub fn one(&self) -> Option<&Define> {
        match self {
            DefineParts::One(d) => Some(d),
            DefineParts::Recursion(_) => None,
        }
    }

    pub fn recursion(&self) -> Option<&Recursion> {
        match self {
            DefineParts::Recursion(r) => Some(r),
            DefineParts::One(_) => None,
        }
    }

    /// The name, where there is one: a recursion has no one name, and none
    /// of its callers asks one of it.
    pub fn name(&self) -> Option<&str> {
        self.one().map(|d| d.name.as_str())
    }
}

regex!(
    DEFINED,
    r"(?s)^(?:define|let)\s+(?P<name>[^\s(]+)(?:\((?P<params>[^()]+)\))?\s*(?P<gives>:=|=)\s*(?P<body>.+?)(?:,\s*for\s+(?P<fors>.+))?$"
);

/// Which word a naming line opens with (`SYNTAX.md`): `define`, for a name
/// the file gives and another may import, written outside every theorem; or
/// `let` followed by `=`, for a name one theorem gives, written inside it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Naming {
    Define,
    Let,
}

impl Naming {
    /// The word itself.
    pub fn word(self) -> &'static str {
        match self {
            Naming::Define => "define",
            Naming::Let => "let",
        }
    }

    /// What the word puts between a name and what it names.
    pub fn gives(self) -> &'static str {
        match self {
            Naming::Define => ":=",
            Naming::Let => "=",
        }
    }
}

// A `let` that names: a name, perhaps applied, and `=`, or the `:=` a let
// does not take, which `define_parts` then reports. Any other `let` takes a
// member of a set, or a letter of a sort, and is no naming line.
regex!(LET_NAMING, r"^let\s+[^\s(=∈∉⊆:]+(?:\([^()]*\))?\s*:?=[^=]");

/// The word a naming line opens with, or None for a line that names
/// nothing: `let x ∈ ℝ` takes any member and is no naming line.
pub fn naming(text: &str) -> Option<Naming> {
    if text.starts_with("define ") {
        return Some(Naming::Define);
    }
    LET_NAMING.is_match(text).then_some(Naming::Let)
}
// One argument's domain in a define's `for` clause: `m ∈ ℕ₀`, or `X ⊆ A`.
regex!(
    FOR_ONE,
    r"(?s)^(?P<over>\S+)\s*(?P<how>[∈⊆])\s*(?P<domain>.+)$"
);

/// A define's `for` clause split at the commas that separate its arguments,
/// and not at those inside a domain: `a ∈ ℝ, x ∈ [a, b]` is two pieces. An
/// application's arguments split the same way: `G(a, f(x, y))` takes two.
pub fn for_pieces(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut piece = String::new();
    for c in text.chars() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ => {}
        }
        if c == ',' && depth == 0 {
            out.push(str::trim(&piece).to_string());
            piece.clear();
        } else {
            piece.push(c);
        }
    }
    out.push(str::trim(&piece).to_string());
    out
}
// One line of a define by cases: a value and the condition it is taken
// under, or the last value, taken `otherwise`.
regex!(CASE, r"(?s)^(?P<value>.+?)\s+if\s+(?P<condition>.+)$");
regex!(OTHERWISE, r"(?s)^(?P<value>.+?)\s+otherwise$");

/// The lines of a define by cases as one term: each value and its
/// condition, nested from the right into `_ if _, _ otherwise`; or a decline
/// saying which line is not a case.
fn by_cases(lines: &[&str]) -> Route<String> {
    let Some(last) = OTHERWISE.captures(lines[lines.len() - 1]) else {
        return Route::no(
            "the last line of a define by cases is its value `otherwise`",
        );
    };
    let mut term = str::trim(&last["value"]).to_string();
    let mut nested = false;
    for line in lines[..lines.len() - 1].iter().rev() {
        let Some(case) = CASE.captures(line) else {
            return Route::no(format!(
                "{} is not a case: write the value, then `if` and the condition it is taken under",
                repr(line)
            ));
        };
        let rest = if nested { format!("({term})") } else { term };
        term = format!(
            "{} if {}, {rest} otherwise",
            str::trim(&case["value"]),
            str::trim(&case["condition"])
        );
        nested = true;
    }
    Built(term)
}

// A sequence is named as a variable is: a letter, perhaps with a subscript
// or a prime.
pub const SEQUENCE_NAME: &str = r"[A-Za-zα-ω][₀-₉′]*";
// The head of one rule of a recursion: a name, the index it is said at, and
// `:=`. A rule runs to the next head or to the closing `for`.
regex!(
    RECURSIVE_HEAD,
    format!(r"(?s)(?:^|,)\s*(?P<name>{SEQUENCE_NAME})\((?P<at>[^()]*)\)\s*(?::=|=)")
);
regex!(
    RECURSIVE_FOR,
    r"(?s),\s*for\s+(?P<index>\S+)\s*∈\s*(?P<domain>\S+)\s*$"
);

/// One rule's text as a term: its lines joined, or folded by cases where its
/// last line is taken `otherwise`.
fn rule_term(text: &str) -> Route<String> {
    let trimmed = str::trim(text).trim_end_matches(',');
    let pieces: Vec<&str> = trimmed.split('\n').map(str::trim).collect();
    if pieces.len() > 1 && OTHERWISE.is_match(pieces[pieces.len() - 1]) {
        return by_cases(&pieces);
    }
    Built(pieces.join(" "))
}

/// The index value at which an argument is a recursion's step: `a(m + 1)`
/// is the step rule at m (`SYNTAX.md`: a value at 0 and a rule from k to
/// k + 1). None for any other argument, the value at 0 among them. A rule
/// is read by this, and so is an application of the sequence.
pub fn step_index(arg: &str) -> Option<String> {
    squash(arg)
        .strip_suffix(" + 1")
        .map(|index| str::trim(index).to_string())
}

/// A define of sequences by recursion, without its label, read into its
/// parts; or a decline saying what is wrong with it.
fn recursion_parts(said: &str) -> Route<DefineParts> {
    let Some(closing) = RECURSIVE_FOR.captures(said) else {
        return Route::no(
            "a define by recursion ends `, for k ∈ ℕ₀`, naming the index its rules are written in",
        );
    };
    let index = closing["index"].to_string();
    let domain = closing["domain"].to_string();
    if domain != "ℕ₀" {
        return Route::no(format!(
            "a define by recursion starts at 0, so its index runs over ℕ₀, not {domain}"
        ));
    }
    let word = naming(said).map_or("define", Naming::word);
    let body = &said[word.len()..closing.get(0).unwrap().start()];
    let heads: Vec<_> = RECURSIVE_HEAD.captures_iter(body).collect();
    let mut names: Vec<String> = Vec::new();
    let mut start: IndexMap<String, String> = IndexMap::new();
    let mut step: IndexMap<String, String> = IndexMap::new();
    for (i, head) in heads.iter().enumerate() {
        let name = head["name"].to_string();
        let at = squash(&head["at"]);
        let end = heads.get(i + 1).map(|after| after.get(0).unwrap().start());
        let from = head.get(0).unwrap().end();
        let text = match end {
            Some(end) => &body[from..end],
            None => &body[from..],
        };
        let rule = match rule_term(text) {
            Built(rule) => rule,
            Declined(d) => return Declined(d),
        };
        let table = if at == "0" {
            &mut start
        } else if step_index(&at).as_deref() == Some(index.as_str()) {
            &mut step
        } else {
            return Route::no(format!(
                "{name}({at}) is neither {name}(0) nor {name}({index} + 1): a rule gives a value at 0 or at the step"
            ));
        };
        if table.contains_key(&name) {
            return Route::no(format!("{name}({at}) is given twice"));
        }
        table.insert(name.clone(), rule);
        if !names.contains(&name) {
            names.push(name);
        }
    }
    for name in &names {
        if !start.contains_key(name) {
            return Route::no(format!("{name} has no value at 0"));
        }
        if !step.contains_key(name) {
            return Route::no(format!("{name} has no rule for {name}({index} + 1)"));
        }
    }
    Built(DefineParts::Recursion(Recursion {
        names,
        index,
        domain,
        start,
        step,
    }))
}

// What a define may be called: one name as the lexer reads one, a letter
// with perhaps a subscript or a prime. A longer name is read as several.
regex!(ONE_NAME, format!(r"^{SEQUENCE_NAME}$"));

/// Whether a define, or a definition imported under another name, may be
/// called this.
pub fn is_one_name(name: &str) -> bool {
    ONE_NAME.is_match(name)
}
regex!(
    RECURSION_START,
    format!(r"^(?:define|let)\s+{SEQUENCE_NAME}\(0\)\s*(?::=|=)")
);

/// A `define` line, without its label, read into its parts; or a decline
/// saying what is wrong with it. A define whose first rule is said at 0 is
/// a recursion; any other is one name.
pub fn define_parts(text: &str) -> Route<DefineParts> {
    let said = str::trim(super::skeleton::without_label(text));
    // A define gives its name with `:=` and a let with `=`, as a textbook's
    // "let x₁ = …" does.
    match naming(said) {
        Some(Naming::Let) if said.contains(":=") => {
            return Route::no("a let names with `=`, and `:=` is a define's");
        }
        Some(Naming::Define) if !said.contains(":=") => {
            return Route::no("a define names with `:=`, and `=` is a let's");
        }
        _ => {}
    }
    if RECURSION_START.is_match(said) {
        return recursion_parts(said);
    }
    let m = match DEFINED.captures(said) {
        Some(m) if !str::trim(&m["body"]).is_empty() => m,
        _ => {
            return Route::no(
                "a naming line says `let <name> = <term>`, or `define <name> := <term>` outside the theorems",
            )
        }
    };
    let name = m["name"].to_string();
    // Every name on the page is a letter, so `avg(x)` is three names and never
    // the function a define called `avg` would give.
    if !is_one_name(&name) {
        return Route::no(format!(
            "a define names one letter, perhaps with a subscript or a prime, and {} is not one",
            repr(&name)
        ));
    }
    let names: Vec<String> = m
        .name("params")
        .map(|p| {
            p.as_str()
                .split(',')
                .map(|n| str::trim(n).to_string())
                .collect()
        })
        .unwrap_or_default();
    let fors: Vec<String> = m
        .name("fors")
        .map(|f| for_pieces(f.as_str()))
        .unwrap_or_default();
    let (body, kind) = match kind_said(str::trim(&m["body"])) {
        Some((body, kind)) => (body, Some(kind)),
        None => (str::trim(&m["body"]), None),
    };
    if kind.is_some() && naming(said) == Some(Naming::Define) {
        return Route::no(
            "a define says no kind of number: a let says one, with its reason on the line under it",
        );
    }
    if kind.is_some() && !names.is_empty() {
        return Route::no(format!(
            "let {name}({}) says a kind of number, and a function is no number",
            names.join(", ")
        ));
    }
    // A define over several lines is either one term wrapped by the comma
    // rule, or a function by cases, one case to a line.
    let pieces: Vec<&str> = body.split('\n').map(str::trim).collect();
    let body = if pieces.len() > 1 && OTHERWISE.is_match(pieces[pieces.len() - 1]) {
        match by_cases(&pieces) {
            Built(term) => term,
            Declined(d) => return Declined(d),
        }
    } else {
        pieces.join(" ")
    };
    let said = names.join(", ");
    if let Some(bad) = names.iter().find(|n| !is_one_name(n)) {
        return Route::no(format!(
            "define {name}({said}) takes {}, which is not one letter",
            repr(bad)
        ));
    }
    if names.is_empty() && !fors.is_empty() {
        return Route::no(format!(
            "define {name} gives a domain and takes no argument"
        ));
    }
    if !names.is_empty() && fors.is_empty() {
        let first = &names[0];
        return Route::no(format!(
            "define {name}({said}) says no domain: write `, for {first} ∈ …` after its rule"
        ));
    }
    let mut params = Vec::new();
    for (at, piece) in fors.iter().enumerate() {
        let Some(f) = FOR_ONE.captures(piece) else {
            return Route::no(format!(
                "define {name}({said}) says `for {piece}`, which is not `x ∈ D`"
            ));
        };
        if names.get(at) != Some(&f["over"].to_string()) {
            return Route::no(format!(
                "define {name}({said}) gives the domain of {}",
                &f["over"]
            ));
        }
        // `for X ⊆ A` is `for X ∈ 𝒫A`: X runs over the parts of A.
        let domain = squash(&f["domain"]);
        let domain = if &f["how"] == "⊆" {
            if domain.contains(' ') {
                format!("𝒫({domain})")
            } else {
                format!("𝒫{domain}")
            }
        } else {
            domain
        };
        params.push(Param {
            name: f["over"].to_string(),
            domain,
        });
    }
    if params.len() != names.len() {
        return Route::no(format!(
            "define {name}({said}) says the domain of {} of its {} arguments",
            params.len(),
            names.len()
        ));
    }
    if params.len() > 2 {
        return Route::no(format!(
            "define {name}({said}) takes {} arguments, and a function here takes one or two",
            params.len()
        ));
    }
    Built(DefineParts::One(Define {
        name,
        body,
        params,
        kind,
    }))
}

/// The term a let gives and the kind of number it says its name is, where
/// the last piece after a comma outside brackets opens with `a` or `an`: `let
/// m = gcd(s, w), a natural number`. None where the line says no kind.
fn kind_said(body: &str) -> Option<(&str, String)> {
    let mut depth = 0i32;
    let mut cut = None;
    for (at, c) in body.char_indices() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            ',' if depth == 0 => cut = Some(at),
            _ => {}
        }
    }
    let at = cut?;
    let kind = squash(&body[at + 1..]);
    (kind.starts_with("a ") || kind.starts_with("an "))
        .then(|| (str::trim(&body[..at]), kind))
}
