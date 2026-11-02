//! Every set.mm label this corpus names, checked against set.mm.
//!
//! The database names labels from memory — a `metamath-proof` field says
//! which lemma an item is proved by, a `defines` field spells a definition's
//! body — and
//! nothing else notices when one of them is wrong. Every other check
//! compares the corpus against itself; this is the one that compares it
//! against something outside.
//!
//! It is a set membership and nothing more, so it costs a pass over set.mm
//! and no verification.

use std::collections::BTreeSet;
use std::path::Path;

use indexmap::{IndexMap, IndexSet};

use crate::corpus::corpus;
use crate::mm;
use crate::outcome::{Checked, Problem};
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

/// What names labels: a record.
struct Naming<'a> {
    path: &'a str,
    line: usize,
    name: &'a str,
    fields: &'a IndexMap<String, String>,
    kind: crate::corpus::RecordKind,
}

/// Every label the databases name, with where each was written.
///
/// A `metamath-builds` is reverse Polish, a `metamath-proof` a list of
/// labels and a `defines` reverse Polish, so every token in any of them is a
/// label unless it is a hole or a marker, which says how to read the lemma
/// beside it rather than naming one.
///
/// A notation's `metamath-syntax` and a method's `metamath-proof` are prose
/// meant for a person and name their labels in a sentence, so each is read
/// only as far as it is certainly naming them: the leading entries that are a
/// single label-shaped word, stopping at the first that is not. An item's
/// `metamath-proof` of `none`, `not yet implemented` or a Parley proof names
/// none.
fn named(namings: &[Naming], tables_at: &str) -> IndexMap<String, Where> {
    let mut out: IndexMap<String, Where> = IndexMap::new();
    for r in namings {
        let here = || Where {
            place: r.path.to_string(),
            line: r.line,
            who: r.name.to_string(),
        };
        // What the Metamath build writes for the record: a notation's
        // template, or an item's lemmas. A method's `metamath-proof` says in
        // words which lemma families its steps expand into, and is read as
        // prose below.
        let method = r.kind == crate::corpus::RecordKind::Method;
        let target = match r.kind {
            crate::corpus::RecordKind::Notation => {
                crate::corpus::records::METAMATH_BUILDS
            }
            _ => crate::corpus::records::METAMATH_PROOF,
        };
        let read = if method {
            vec!["defines"]
        } else {
            vec![target, "defines"]
        };
        for field in read {
            let Some(value) = r.fields.get(field) else {
                continue;
            };
            // Only what the build cites names labels: not `none`, `not yet
            // implemented` or a Parley proof.
            let cited = field != crate::corpus::records::METAMATH_PROOF
                || matches!(
                    crate::corpus::records::Provided::read(value),
                    crate::corpus::records::Provided::By(_)
                );
            if !cited {
                continue;
            }
            // What a target writes after `with` is the lemma's variables and
            // the item's own formulas for them, which are not labels and are
            // not set.mm's words. Only the head before it names a lemma.
            let value = match value.split_once(" with ") {
                Some((head, _)) if field == target => head,
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
        // Prose read only as far as it certainly names labels: a method's
        // `metamath-proof` and a notation's `metamath-syntax`.
        let prose = if method {
            crate::corpus::records::METAMATH_PROOF
        } else {
            crate::corpus::records::METAMATH_SYNTAX
        };
        let said = r.fields.get(prose).map_or("", String::as_str);
        for entry in targets::split_entries(said) {
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

/// The labels this corpus introduces by a definition, which set.mm will not
/// have: a definition that carries a `symbol` brings a constant and the
/// axiom defining it.
fn symbols(records: &[crate::corpus::Record]) -> IndexSet<String> {
    let mut out = IndexSet::new();
    for r in records {
        if let Some(symbol) = r.field("symbol") {
            let token = str::trim(symbol);
            out.insert(format!("c{token}"));
            out.insert(format!("df-{token}"));
        }
    }
    out
}

/// Each Metamath bridge's label, with the group whose file holds it.
fn bridges(source: &dyn Source) -> Checked<IndexMap<String, String>> {
    let mut out = IndexMap::new();
    for group in crate::proofs::stdlib::NAMES {
        let path = format!("{}{group}.bridge", crate::proofs::stdlib::WORKSHEETS);
        let text = source
            .read_text(&path)
            .map_err(|e| Problem::new(&path, 0, format!("cannot read it: {e}")))?;
        for label in crate::proofs::worksheet::labels(&path, &text)? {
            out.insert(label, group.to_string());
        }
    }
    Ok(out)
}

/// Why a label the corpus names is wrong, or None where it is right.
///
/// A set.mm label is written bare and a bridge by its full name,
/// `metamath-bridges/numbers/gzmodlt`, so a record says which it means. A
/// rule table names a bridge's lemma bare, as `proved.mm` has it.
fn wrong(
    named: &str,
    at: &Where,
    tables_at: &str,
    have: &BTreeSet<String>,
    bridged: &IndexMap<String, String>,
    file: &str,
) -> Option<String> {
    if let Some(rest) = named.strip_prefix(targets::METAMATH_BRIDGES) {
        let label = targets::label_of(named);
        let group = rest.strip_suffix(label).and_then(|g| g.strip_suffix('/'));
        return match (group, bridged.get(label)) {
            (Some(group), Some(holds)) if group == holds => None,
            (_, Some(holds)) => Some(format!(
                "{named}, which is a lemma of metamath-bridges/{holds}"
            )),
            (_, None) => Some(format!("{named}, which no Metamath bridge proves")),
        };
    }
    if have.contains(named) {
        return None;
    }
    match bridged.get(named) {
        Some(_) if at.place == tables_at => None,
        Some(group) => Some(format!(
            "{named}, a Metamath bridge, which is written metamath-bridges/{group}/{named}"
        )),
        None => Some(format!("{named}, which {file} does not have")),
    }
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
    let namings: Vec<Naming> = c
        .records
        .iter()
        .map(|r| Naming {
            path: &r.path,
            line: r.line,
            name: &r.name,
            fields: &r.fields,
            kind: r.kind,
        })
        .collect();
    let wanted = named(&namings, tables_at);
    let mut have: BTreeSet<String> = match mm::read(&[library]) {
        Ok(sigs) => sigs.into_keys().map(String::from).collect(),
        Err(e) => {
            return Said {
                printed: String::new(),
                complained: format!("{}: {e}\n", library.display()),
                status: 2,
            }
        }
    };
    have.extend(symbols(&c.records));
    let bridged = match bridges(source) {
        Ok(b) => b,
        Err(trouble) => {
            return Said {
                printed: String::new(),
                complained: format!("{trouble}\n"),
                status: 2,
            }
        }
    };
    let file = library
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    let mut missing: Vec<(&String, usize, &String, String)> = wanted
        .iter()
        .filter_map(|(named, at)| {
            let why = wrong(named, at, tables_at, &have, &bridged, &file)?;
            Some((&at.place, at.line, &at.who, why))
        })
        .collect();
    missing.sort();
    let mut printed = String::new();
    for (place, line, who, why) in &missing {
        printed.push_str(&format!("{place}:{line}  {who} names {why}\n"));
    }
    printed.push_str(&format!(
        "\n{} labels named, {} not in {file} or a bridge as written\n",
        wanted.len(),
        missing.len()
    ));
    Said {
        printed,
        complained: String::new(),
        status: if missing.is_empty() { 0 } else { 1 },
    }
}
