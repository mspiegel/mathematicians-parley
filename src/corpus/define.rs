//! What a `define` line says.

use indexmap::IndexMap;

use crate::outcome::{Built, Declined, Route};
use crate::regex;
use crate::text::{pystr, repr};

/// What a `define` line says: a name, and the term it stands for.
///
/// A name with a parameter is a function, as a reader writes
/// "S(m) = 1 + 2 + … + m": `define S(m) := Σ(j = 1 to m) j, for m ∈ ℕ`. Its
/// domain is said with it, because a rule without one says what S does and
/// not where S is defined.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Define {
    pub name: String,
    pub body: String,
    pub param: Option<String>,
    pub domain: Option<String>,
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

    /// The name, as the reference implementation's `said.name` reads it: a
    /// recursion has no one name, and none of its callers asks one of it.
    pub fn name(&self) -> Option<&str> {
        self.one().map(|d| d.name.as_str())
    }
}

regex!(
    DEFINED,
    r"(?s)^define\s+(?P<name>[^\s(]+)(?:\((?P<param>[^\s()]+)\))?\s*:=\s*(?P<body>.+?)(?:,\s*for\s+(?P<over>\S+)\s*(?P<how>[∈⊆])\s*(?P<domain>.+))?$"
);
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
    let mut term = pystr::strip(&last["value"]).to_string();
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
            pystr::strip(&case["value"]),
            pystr::strip(&case["condition"])
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
    format!(r"(?s)(?:^|,)\s*(?P<name>{SEQUENCE_NAME})\((?P<at>[^()]*)\)\s*:=")
);
regex!(
    RECURSIVE_FOR,
    r"(?s),\s*for\s+(?P<index>\S+)\s*∈\s*(?P<domain>\S+)\s*$"
);

/// One rule's text as a term: its lines joined, or folded by cases where its
/// last line is taken `otherwise`.
fn rule_term(text: &str) -> Route<String> {
    let trimmed = pystr::strip(text).trim_end_matches(',');
    let pieces: Vec<&str> = trimmed.split('\n').map(pystr::strip).collect();
    if pieces.len() > 1 && OTHERWISE.is_match(pieces[pieces.len() - 1]) {
        return by_cases(&pieces);
    }
    Built(pieces.join(" "))
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
    let body = &said["define".len()..closing.get(0).unwrap().start()];
    let heads: Vec<_> = RECURSIVE_HEAD.captures_iter(body).collect();
    let mut names: Vec<String> = Vec::new();
    let mut start: IndexMap<String, String> = IndexMap::new();
    let mut step: IndexMap<String, String> = IndexMap::new();
    for (i, head) in heads.iter().enumerate() {
        let name = head["name"].to_string();
        let at = pystr::squash(&head["at"]);
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
        } else if at == format!("{index} + 1") {
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

regex!(TRAILING_LABEL, r"\s*\([A-Z]+[0-9]*\)\s*$");
regex!(
    RECURSION_START,
    format!(r"^define\s+{SEQUENCE_NAME}\(0\)\s*:=")
);

/// A `define` line, without its label, read into its parts; or a decline
/// saying what is wrong with it. A define whose first rule is said at 0 is
/// a recursion; any other is one name.
pub fn define_parts(text: &str) -> Route<DefineParts> {
    let unlabelled = TRAILING_LABEL.replace(text, "");
    let said = pystr::strip(&unlabelled);
    if RECURSION_START.is_match(said) {
        return recursion_parts(said);
    }
    let m = match DEFINED.captures(said) {
        Some(m) if !pystr::strip(&m["body"]).is_empty() => m,
        _ => return Route::no("a define says `define <name> := <term>`"),
    };
    let name = m["name"].to_string();
    let param = m.name("param").map(|p| p.as_str().to_string());
    let over = m.name("over").map(|o| o.as_str().to_string());
    let body = pystr::strip(&m["body"]);
    // A define over several lines is either one term wrapped by the comma
    // rule, or a function by cases, one case to a line.
    let pieces: Vec<&str> = body.split('\n').map(pystr::strip).collect();
    let body = if pieces.len() > 1 && OTHERWISE.is_match(pieces[pieces.len() - 1]) {
        match by_cases(&pieces) {
            Built(term) => term,
            Declined(d) => return Declined(d),
        }
    } else {
        pieces.join(" ")
    };
    match (&param, &over) {
        (Some(param), None) => {
            return Route::no(format!(
                "define {name}({param}) says no domain: write `, for {param} ∈ …` after its rule"
            ))
        }
        (None, Some(_)) => {
            return Route::no(format!(
                "define {name} gives a domain and takes no argument"
            ))
        }
        (Some(param), Some(over)) if over != param => {
            return Route::no(format!(
                "define {name}({param}) gives the domain of {over}"
            ))
        }
        _ => {}
    }
    // `for X ⊆ A` is `for X ∈ 𝒫A`: X runs over the parts of A.
    let domain = param.as_ref().map(|_| {
        let domain = pystr::squash(&m["domain"]);
        if !domain.is_empty() && &m["how"] == "⊆" {
            if domain.contains(' ') {
                format!("𝒫({domain})")
            } else {
                format!("𝒫{domain}")
            }
        } else {
            domain
        }
    });
    Built(DefineParts::One(Define {
        name,
        body,
        param,
        domain,
    }))
}
