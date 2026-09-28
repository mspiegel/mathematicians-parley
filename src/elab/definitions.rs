//! The constants this corpus introduces, and what they stand for.

use sha2::{Digest, Sha256};

use crate::corpus::{Record, RecordKind};
use crate::mm::kernel::term_of;
use crate::mm::library::{render, thousands};
use crate::mm::{Kind, Signatures};
use crate::outcome::{Checked, Problem};
use crate::text::{repr, squash};

/// One constant: its token, the definition's name, and the term it stands
/// for in reverse Polish.
pub struct Introduced {
    pub token: String,
    pub name: String,
    pub body: String,
}

/// The constants the corpus's definitions introduce.
///
/// A definition that names a word for something the library already has
/// points at its label; one that introduces a symbol has nothing to point
/// at, and the corpus has to declare the constant itself. set.mm writes the
/// angle function inline in every theorem about it and never names it,
/// which is the only such case the corpus has.
///
/// They are written once, for the corpus rather than for a proof. Two proofs
/// both using angles would otherwise each declare the constant, and the
/// declarations would collide the moment one included the other.
///
/// What the checker cannot check without the library is checked here: that
/// the token is not already a label, and that the term parses and closes
/// over its own variables. A definition introducing a symbol the library
/// already has would not be a definition, and one whose term had a free
/// variable would not be eliminable.
pub fn definitions(records: &[Record], sigs: &Signatures) -> Checked<Vec<Introduced>> {
    let mut labels = indexmap::IndexMap::new();
    for s in sigs.values() {
        if s.kind == Kind::Float {
            labels.insert(s.statement[1].clone(), s.label.clone());
        }
    }
    let mut said = Vec::new();
    for r in records {
        let token = str::trim(r.field_or_empty("symbol"));
        if r.kind != RecordKind::Definition || token.is_empty() {
            continue;
        }
        if sigs.contains_key(&format!("c{token}")) || sigs.contains_key(token) {
            return Err(Problem::new(
                &r.path,
                r.line,
                format!(
                    "definition {}: the library already has {}, so this defines nothing",
                    r.name,
                    repr(token)
                ),
            ));
        }
        let body = squash(r.field_or_empty("defines"));
        let term = term_of(&body, sigs);
        let free: Vec<String> = term
            .names()
            .iter()
            .filter(|v| sigs[&labels[&***v]].statement[0] != "setvar")
            .map(|v| v.to_string())
            .collect();
        if !free.is_empty() {
            let shown: Vec<String> = free.iter().map(|v| repr(v)).collect();
            return Err(Problem::new(
                &r.path,
                r.line,
                format!(
                    "definition {}: [{}] are free in what it defines, so it is not eliminable",
                    r.name,
                    shown.join(", ")
                ),
            ));
        }
        said.push(Introduced {
            token: token.to_string(),
            name: r.name.clone(),
            body,
        });
    }
    Ok(said)
}

/// Which set.mm the file being written was checked against.
///
/// An elaborated file is a record rather than a build product: it cannot be
/// rebuilt from this repository, because set.mm belongs to metamath. So it
/// has to say which set.mm, and set.mm carries no version of its own. It is
/// named by what it holds instead: the count says at a glance whether the
/// library grew, and the hash is the half that decides. Both are read off
/// the file and never off the clock, so elaborating twice from one library
/// gives one file.
///
/// SHA-256 rather than SHA-1 because everything these proofs claim rests on
/// the library being what it says it is, and chosen-prefix collisions
/// against SHA-1 are practical.
///
/// `count` is read off the library before anything is elaborated, since an
/// elaborator adds to its own table as it goes.
pub fn say_library(bytes: &[u8], count: usize) -> String {
    let digest = Sha256::digest(bytes);
    let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
    format!(
        "   Checked against a set.mm of {} assertions, sha256\n   {hex}. $)\n",
        thousands(count)
    )
}

/// The corpus's definitions, as a file the proofs include.
pub fn write_definitions(
    records: &[Record],
    sigs: &Signatures,
    setmm: &[u8],
) -> Checked<String> {
    let said = definitions(records, sigs)?;
    let mut out = String::from(
        "$( stdlib/definitions, from the stdlib/*.records files by parley/elaborate.py.\n",
    );
    if said.is_empty() {
        out.push_str("   The corpus introduces none.\n");
    } else {
        out.push_str("   Each introduces one constant the library does not have,\n");
        out.push_str("   and stands for a term that closes over its own names.\n");
    }
    out.push_str(&say_library(setmm, sigs.len()));
    out.push('\n');
    out.push_str("$[ set.mm $]\n\n");
    // A new symbol is declared before it is used, the way set.mm declares
    // every one of its own. Without the `$c` the syntax axiom below names a
    // token the file has never heard of.
    for one in &said {
        out.push_str(&format!("$c {} $.\n", one.token));
    }
    if !said.is_empty() {
        out.push('\n');
    }
    for one in &said {
        out.push_str(&format!("$( {} $)\n", one.name));
        out.push_str(&format!("  c{} $a class {} $.\n", one.token, one.token));
        out.push_str(&format!(
            "  df-{} $a |- {} = {} $.\n",
            one.token,
            one.token,
            render(&one.body, sigs)
        ));
    }
    Ok(out)
}
