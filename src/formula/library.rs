//! The functions the library declares.
//!
//! A function record declares a name a formula applies: the record's name is
//! the function's, its `sort` line says what the arguments and the value
//! are, one argument for each place before the arrow, and its `builds` line
//! is the set.mm term an application of it stands for. So `function gcd`
//! with `sort number, number → number` is applied as `gcd(_, _)`. Nothing
//! here is notation: `gcd(a, b)` is read as the name gcd applied to a and b,
//! through the application patterns `corpus/db/notation.records` declares
//! for every function, as a proof's `T(k)` is. What the library adds is the
//! name, its sort, and what it builds. A proof file has the name in scope
//! where it imports it, `import function stdlib/divisibility/gcd`; the
//! library's own records have every one.

use indexmap::IndexMap;

use crate::corpus::{Record, RecordKind};
use crate::outcome::{Checked, Problem};
use crate::regex;
use crate::text::repr;

/// One function a function record declares.
#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub arity: usize,
    /// Its `sort` line: `number, number → number`.
    pub sort: String,
    /// Its `builds` line: the set.mm term, `_1` for the first argument.
    pub builds: String,
    /// The record that declares it, by its full name.
    pub item: String,
    pub path: String,
    pub line: usize,
}

// A function's name is letters and nothing else, so that a formula reads it
// as one name: a digit or a hyphen would not be part of it there.
regex!(FUNCTION_NAME, r"^[A-Za-zα-ω]+$");
// A sort line: the places, then the arrow and the value.
regex!(FUNCTION_SORT, r"^([^→]+)→\s*\S+$");

/// Every function the library's function records declare, by name. A name a
/// formula cannot write, a record without its `sort` or `builds`, and a sort
/// with no arrow are defects in the database, and end the reading as a
/// notation that does not read does.
pub fn library_functions(records: &[Record]) -> Checked<IndexMap<String, Function>> {
    let mut out: IndexMap<String, Function> = IndexMap::new();
    for r in records {
        if r.kind != RecordKind::Function {
            continue;
        }
        let line = r.line;
        if !FUNCTION_NAME.is_match(&r.name) {
            return Err(Problem::new(
                &r.path,
                line,
                format!(
                    "function {}: a function's name is letters only, since a formula writes it",
                    r.name
                ),
            ));
        }
        let (Some(sort), Some(builds)) = (r.field("sort"), r.field("builds")) else {
            return Err(Problem::new(
                &r.path,
                line,
                format!(
                    "function {} does not say its `sort` and what it `builds`",
                    r.name
                ),
            ));
        };
        let Some(places) = FUNCTION_SORT.captures(str::trim(sort)) else {
            return Err(Problem::new(
                &r.path,
                r.lines.get("sort").copied().unwrap_or(line),
                format!(
                    "function {}: `sort {}` gives no places before an arrow, as `number, number → number` does",
                    r.name,
                    str::trim(sort)
                ),
            ));
        };
        let name = r.name.clone();
        if let Some(was) = out.get(&name) {
            return Err(Problem::new(
                &r.path,
                line,
                format!(
                    "{} is already the function {} declares",
                    repr(&name),
                    was.item
                ),
            ));
        }
        out.insert(
            name.clone(),
            Function {
                name,
                arity: places[1].split(',').count(),
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
