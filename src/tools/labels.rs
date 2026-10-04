//! Every set.mm label this corpus names, checked against set.mm.
//!
//! The database names labels from memory — a `target` field says which lemma
//! a word lands on, a `defines` field spells a definition's body — and
//! nothing else notices when one of them is wrong. Every other check
//! compares the corpus against itself; this is the one that compares it
//! against something outside.
//!
//! It is a set membership and nothing more, so it costs a pass over set.mm
//! and no verification.

use std::collections::BTreeSet;
use std::path::Path;

use indexmap::{IndexMap, IndexSet};

use super::path_of;
use crate::corpus::corpus;
use crate::mm;
use crate::regex;
use crate::rules;
use crate::said::Said;
use crate::source::Source;
use crate::targets;

// What a set.mm label looks like, strictly enough that no word of a
// sentence is mistaken for one: lower case, and hyphenated only as `df-`
// names are.
regex!(LABEL_SHAPED, r"^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$");
// What a label in a rule table looks like. A table holds nothing but labels
// and a few symbols, so this admits what prose would not: a leading digit,
// as in `1re`, and a dot, as in `pm2.21dd`.
regex!(TABLED, r"^[a-z0-9][a-z0-9.]*(?:-[a-z0-9.]+)*$");

/// Where a label was named.
struct Where {
    /// The file.
    place: String,
    line: usize,
    /// The record or table that named it.
    who: String,
}

/// What names labels: a record, or a proved theorem's `metamath` line.
struct Naming<'a> {
    path: &'a str,
    line: usize,
    name: &'a str,
    fields: &'a IndexMap<String, String>,
}

/// Every label the databases name, with where each was written.
///
/// A `target` is reverse Polish or a list of labels and a `defines` is
/// reverse Polish, so every token in either is a label unless it is a hole
/// or a marker, which says how to read the lemma beside it rather than
/// naming one.
///
/// `metamath` is prose meant for a person and names its labels in a
/// sentence, so it is read only as far as it is certainly naming them: the
/// leading entries that are a single label-shaped word, stopping at the
/// first that is not.
fn named(namings: &[Naming], tables_at: &str) -> IndexMap<String, Where> {
    let mut out: IndexMap<String, Where> = IndexMap::new();
    for r in namings {
        let here = || Where {
            place: r.path.to_string(),
            line: r.line,
            who: r.name.to_string(),
        };
        for field in ["target", "defines"] {
            let Some(value) = r.fields.get(field) else {
                continue;
            };
            // What a target writes after `with` is the lemma's variables and
            // the item's own formulas for them, which are not labels and are
            // not set.mm's words. Only the head before it names a lemma.
            let value = match (field, value.split_once(" with ")) {
                ("target", Some((head, _))) => head,
                _ => value.as_str(),
            };
            for entry in targets::split_entries(value) {
                if targets::is_marker(entry) {
                    continue;
                }
                for token in entry.split_whitespace() {
                    if targets::is_hole(token) || targets::is_context(token) {
                        continue;
                    }
                    out.entry(token.to_string()).or_insert_with(here);
                }
            }
        }
        let metamath = r.fields.get("metamath").map_or("", String::as_str);
        for entry in targets::split_entries(metamath) {
            if !LABEL_SHAPED.is_match(entry) {
                break;
            }
            out.entry(entry.to_string()).or_insert_with(here);
        }
    }
    for (table, one) in rules::every_label() {
        if TABLED.is_match(one) {
            out.entry(one.to_string()).or_insert_with(|| Where {
                place: tables_at.to_string(),
                line: 0,
                who: table.to_string(),
            });
        }
    }
    out
}

/// The labels this corpus introduces, which set.mm will not have.
///
/// A definition that carries a `symbol` brings a constant and the axiom
/// defining it; the library's own proofs bring whatever they prove.
fn supplied(
    source: &dyn Source,
    records: &[crate::corpus::Record],
) -> IndexSet<String> {
    let mut out = IndexSet::new();
    for r in records {
        if let Some(symbol) = r.field("symbol") {
            let token = str::trim(symbol);
            out.insert(format!("c{token}"));
            out.insert(format!("df-{token}"));
        }
    }
    let built = path_of("stdlib/proved");
    if let Ok(text) = source.read_text(&built) {
        out.extend(mm::read_texts(&[&text]).into_keys());
    }
    out
}

/// Check every label the corpus names against the library at `library`.
///
/// `tables_at` is what a label missing from a rule table is said to be
/// written in.
pub fn run(source: &dyn Source, library: Option<&Path>, tables_at: &str) -> Said {
    let Some(library) = library else {
        return Said {
            printed: "set.mm not found; say where it is with SET_MM, or leave a copy or a link at the root of the working tree\n".into(),
            complained: String::new(),
            status: 2,
        };
    };
    let c = match corpus(source) {
        Ok(c) => c,
        Err(trouble) => {
            return Said {
                printed: String::new(),
                complained: format!("{trouble}\n"),
                status: 2,
            }
        }
    };
    let mut namings: Vec<Naming> = c
        .records
        .iter()
        .map(|r| Naming {
            path: &r.path,
            line: r.line,
            name: &r.name,
            fields: &r.fields,
        })
        .collect();
    // A proved theorem's `metamath` line says which set.mm theorem is its
    // counterpart, and is checked like any record's.
    namings.extend(c.theorems.iter().map(|t| Naming {
        path: &t.path,
        line: t.line,
        name: &t.name,
        fields: &t.fields,
    }));
    let wanted = named(&namings, tables_at);
    let mut have: BTreeSet<String> = match mm::read(&[library]) {
        Ok(sigs) => sigs.into_keys().collect(),
        Err(e) => {
            return Said {
                printed: String::new(),
                complained: format!("{}: {e}\n", library.display()),
                status: 2,
            }
        }
    };
    have.extend(supplied(source, &c.records));
    let file = library
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    let mut missing: Vec<(&String, usize, &String, &String)> = wanted
        .iter()
        .filter(|(label, _)| !have.contains(*label))
        .map(|(label, Where { place, line, who })| (place, *line, who, label))
        .collect();
    missing.sort();
    let mut printed = String::new();
    for (place, line, who, label) in &missing {
        printed.push_str(&format!(
            "{place}:{line}  {who} names {label}, which {file} does not have\n"
        ));
    }
    printed.push_str(&format!(
        "\n{} labels named, {} not in {file}\n",
        wanted.len(),
        missing.len()
    ));
    Said {
        printed,
        complained: String::new(),
        status: if missing.is_empty() { 0 } else { 1 },
    }
}
