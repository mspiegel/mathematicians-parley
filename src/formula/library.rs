//! The functions the library declares.
//!
//! A library definition may say that it introduces a function: its
//! `function` line writes the name applied to one hole for each argument,
//! `gcd(_, _)`, its `sort` line says what the arguments and the value are,
//! and its `builds` line is the set.mm term an application of it stands for.
//! Nothing here is notation: `gcd(a, b)` is read as the name gcd applied to a
//! and b, through the application patterns `corpus/db/notation.records`
//! declares for every function, as a proof's `T(k)` is. What the library
//! adds is the name, its sort, and what it builds.

use indexmap::IndexMap;

use crate::corpus::{Record, RecordKind};
use crate::outcome::{Checked, Problem};
use crate::regex;
use crate::text::repr;

/// One function a library definition declares.
#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub arity: usize,
    /// Its `sort` line: `number, number → number`.
    pub sort: String,
    /// Its `builds` line: the set.mm term, `_1` for the first argument.
    pub builds: String,
    /// The definition that declares it, as a citation names it.
    pub item: String,
    pub path: String,
    pub line: usize,
}

// A name applied to one hole for each argument, and nothing else: that is
// what keeps a function from being notation.
regex!(FUNCTION, r"^([A-Za-zα-ω]+)\(\s*(_(?:\s*,\s*_)*)\s*\)$");

/// Every function the library's definitions declare, by name. A `function`
/// line that does not read, one without its `sort` or `builds`, and a name
/// declared twice are defects in the database, and end the reading as a
/// notation that does not read does.
pub fn library_functions(records: &[Record]) -> Checked<IndexMap<String, Function>> {
    let mut out: IndexMap<String, Function> = IndexMap::new();
    for r in records {
        if r.kind != RecordKind::Definition {
            continue;
        }
        let Some(said) = r.field("function") else {
            continue;
        };
        let line = r.lines.get("function").copied().unwrap_or(r.line);
        let Some(m) = FUNCTION.captures(str::trim(said)) else {
            return Err(Problem::new(
                &r.path,
                line,
                format!(
                    "definition {}: `function {}` is not a name applied to holes, as `gcd(_, _)` is",
                    r.name,
                    str::trim(said)
                ),
            ));
        };
        let (Some(sort), Some(builds)) = (r.field("sort"), r.field("builds")) else {
            return Err(Problem::new(
                &r.path,
                line,
                format!(
                    "definition {} declares a function and does not say its `sort` and what it `builds`",
                    r.name
                ),
            ));
        };
        let name = m[1].to_string();
        if let Some(was) = out.get(&name) {
            return Err(Problem::new(
                &r.path,
                line,
                format!(
                    "{} is already the function def:{} declares",
                    repr(&name),
                    was.item
                ),
            ));
        }
        out.insert(
            name.clone(),
            Function {
                name,
                arity: m[2].matches('_').count(),
                sort: str::trim(sort).to_string(),
                builds: str::trim(builds).to_string(),
                item: r.qualified(),
                path: r.path.clone(),
                line,
            },
        );
    }
    Ok(out)
}
