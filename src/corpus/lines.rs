//! Physical lines joined into logical ones.

use crate::regex;

/// One logical line: a physical line plus any continuations of it.
#[derive(Clone, Debug)]
pub struct Line {
    pub no: usize,
    pub text: String,
    pub indent: usize,
}

regex!(UNLABELLED, r"\([A-Z]+[0-9]*\)$");

/// Whether a line ends without the label a define closes on.
pub fn unlabelled(text: &str) -> bool {
    !UNLABELLED.is_match(text)
}

/// Physical lines, comments and blanks dropped, joined by the continuation
/// rule: a line continues onto the next when it ends with a comma.
///
/// A `define` continues until the line carrying its label, because a
/// function defined by cases writes one case to a line (`SYNTAX.md`). Its
/// lines are joined keeping the break, which is what tells one case from
/// the next: a value may hold a comma of its own, as gcd(a, b) does.
pub fn read_lines(text: &str) -> Vec<Line> {
    let mut out = Vec::new();
    let mut pending: Option<Line> = None;
    for (at, raw) in text.split('\n').enumerate() {
        let no = at + 1;
        let stripped = raw.trim();
        if stripped.is_empty() || stripped.starts_with('#') {
            if let Some(line) = pending.take() {
                out.push(line);
            }
            continue;
        }
        // Indentation is counted in characters of leading whitespace.
        let indent = raw.chars().count() - raw.trim_start().chars().count();
        if let Some(line) = pending.as_mut() {
            let defining = line.text.starts_with("define ");
            line.text.push(if defining { '\n' } else { ' ' });
            line.text.push_str(stripped);
            let goes_on = if defining {
                unlabelled(&line.text)
            } else {
                stripped.ends_with(',')
            };
            if !goes_on {
                out.push(pending.take().unwrap());
            }
            continue;
        }
        let line = Line {
            no,
            text: stripped.to_string(),
            indent,
        };
        if stripped.ends_with(',')
            || (stripped.starts_with("define ") && unlabelled(stripped))
        {
            pending = Some(line);
        } else {
            out.push(line);
        }
    }
    if let Some(line) = pending {
        out.push(line);
    }
    out
}
