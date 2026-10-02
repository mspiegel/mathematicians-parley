//! The functions the library declares.
//!
//! A definition with a `sort` line declares a name a formula applies: the
//! record's name is the function's, its `sort` line says what the arguments
//! and the value are, one argument for each place before the arrow, and its
//! `builds` line is the set.mm term an application of it stands for. So
//! `definition gcd` with `sort number, number → number` is applied as
//! `gcd(_, _)`. Nothing here is notation: `gcd(a, b)` is read as the name gcd
//! applied to a and b, through the application patterns
//! `corpus/db/notation.records` declares for every function, as a proof's
//! `T(k)` is. What the library adds is the name, its sort, and what it
//! builds. A proof file has the name in scope where it imports it, `import
//! mundane stdlib/divisibility/gcd`; the library's own records have every
//! one.

use indexmap::IndexMap;

use crate::corpus::{ItemKind, Record};
use crate::outcome::{Checked, Problem};
use crate::regex;
use crate::text::repr;

/// One function a definition declares.
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
    /// What a citation of its record writes.
    pub cited_as: ItemKind,
    /// Its record's header before the name, which an import of it says:
    /// `mundane definition`.
    pub header: String,
    pub path: String,
    pub line: usize,
}

impl Function {
    /// Its record as prose names it, with its prefix: `mun:stdlib/divisibility/gcd`.
    pub fn cited(&self) -> String {
        format!("{}:{}", self.cited_as.prefix(), self.item)
    }

    /// The import that brings it in.
    pub fn import(&self) -> String {
        format!("import {} {}", self.header, self.item)
    }
}

// A function's name is letters and nothing else, so that a formula reads it
// as one name: a digit or a hyphen would not be part of it there.
regex!(FUNCTION_NAME, r"^[A-Za-zα-ω]+$");
// A sort line: the places, then the arrow and the value.
regex!(FUNCTION_SORT, r"^([^→]+)→\s*\S+$");

/// Every function the library's definitions declare, by name. A name a
/// formula cannot write, a record without its `sort` or `builds`, and a sort
/// with no arrow are defects in the database, and end the reading as a
/// notation that does not read does.
pub fn library_functions(records: &[Record]) -> Checked<IndexMap<String, Function>> {
    let mut out: IndexMap<String, Function> = IndexMap::new();
    for r in records {
        if !r.is_function() {
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
                    "definition {} gives a function's `sort` and does not say what it `builds`",
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
                cited_as: ItemKind::of_record(r),
                header: r.header(),
                path: r.path.clone(),
                line,
            },
        );
    }
    Ok(out)
}
