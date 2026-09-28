//! Nothing an elaborated proof takes as stated goes unrecorded.
//!
//! `GOALS.md` decision 17: a step the elaborator cannot build enters the
//! archive as an axiom and weakens what the archive proves, so it is a
//! defect and the gate is red, or `ELABORATION.md` records it — the step,
//! why it is not built, and what would build it. A list in the elaborated
//! file's header says what the file assumes, and is not a record: nothing
//! makes anyone read it.
//!
//! So every `$a` in a file under `elaboration/proofs/` or
//! `elaboration/tests/` must be named in the section "Steps taken as stated"
//! of `ELABORATION.md`, and every statement named there must still be one a
//! file takes. The second keeps the record from outliving what it records.
//! The tests are read because a library item's test is where an item no
//! lemma builds shows itself first.

use std::collections::BTreeSet;

use crate::regex;
use crate::said::Said;
use crate::source::Source;

regex!(AXIOM, r"(?m)^\s*(\S+)\s+\$a\s");
// A record starts at the margin; the indented form shown in the section is
// its example, not a record.
regex!(
    RECORD,
    r"(?m)^- `(elaboration/(?:proof|tests)/[^`]+\.mm)` `([^`]+)`:"
);
regex!(NEXT_SECTION, r"(?m)^#{2,3} ");

const SECTION: &str = "### Steps taken as stated";

/// (file, label) pairs the section of `ELABORATION.md` names.
fn recorded(text: &str) -> Option<BTreeSet<(String, String)>> {
    let at = text.find(SECTION)?;
    let after = &text[at + SECTION.len()..];
    let body = match NEXT_SECTION.find(after) {
        Some(m) => &after[..m.start()],
        None => after,
    };
    Some(
        RECORD
            .captures_iter(body)
            .map(|c| (c[1].to_string(), c[2].to_string()))
            .collect(),
    )
}

/// (file, label) pairs the elaborated proofs take as stated.
fn taken(source: &dyn Source) -> BTreeSet<(String, String)> {
    let mut out = BTreeSet::new();
    for rel in source.found(".mm") {
        let read = ["elaboration/proofs/", "elaboration/tests/"]
            .iter()
            .any(|p| rel.starts_with(p));
        if !read {
            continue;
        }
        let Ok(text) = source.read_text(&rel) else {
            continue;
        };
        for c in AXIOM.captures_iter(&text) {
            out.insert((rel.clone(), c[1].to_string()));
        }
    }
    out
}

pub fn run(source: &dyn Source) -> Said {
    let text = source.read_text("docs/ELABORATION.md").unwrap_or_default();
    let Some(written) = recorded(&text) else {
        return Said {
            printed: "docs/ELABORATION.md has no section \"Steps taken as stated\"\n"
                .into(),
            complained: String::new(),
            status: 1,
        };
    };
    let found = taken(source);
    let mut problems: Vec<String> = found
        .difference(&written)
        .map(|(rel, label)| {
            format!("{rel}: {label} is taken as stated, and ELABORATION.md does not record it")
        })
        .collect();
    problems.extend(written.difference(&found).map(|(rel, label)| {
        format!("ELABORATION.md records {label} in {rel}, which that file no longer takes as stated")
    }));
    let mut printed: String = problems.iter().map(|p| format!("{p}\n")).collect();
    if !problems.is_empty() {
        return Said {
            printed,
            complained: String::new(),
            status: 1,
        };
    }
    printed
        .push_str("nothing is taken as stated that ELABORATION.md does not record\n");
    Said {
        printed,
        complained: String::new(),
        status: 0,
    }
}
