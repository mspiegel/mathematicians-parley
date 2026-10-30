//! Physical lines joined into logical ones.

/// One logical line: a physical line plus any continuations of it.
#[derive(Clone, Debug)]
pub struct Line {
    pub no: usize,
    pub text: String,
    pub indent: usize,
}

/// Whether a line ends without the label a define closes on.
pub fn unlabelled(text: &str) -> bool {
    super::skeleton::label_at_end(text).is_none()
}

/// Where in the file `at` bytes into the logical line starting on `line`
/// falls, as `read_lines` joins them: each physical line trimmed, and one
/// character between it and the next. The physical line, counted from 0,
/// and the byte in it; None past the file's end.
pub fn physical(raw: &[&str], line: usize, at: usize) -> Option<(usize, usize)> {
    let mut left = at;
    for (index, text) in raw.iter().enumerate().skip(line.checked_sub(1)?) {
        let lead = text.len() - text.trim_start().len();
        let len = text.trim().len();
        if left < len {
            return Some((index, lead + left));
        }
        left = left.checked_sub(len + 1)?;
    }
    None
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
            let defining = super::define::naming(&line.text).is_some();
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
            || (super::define::naming(stripped).is_some() && unlabelled(stripped))
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_place_in_a_logical_line_is_found_in_the_file() {
        let text = "3.  x = 1\n    mun:x a := 2,\n      from 1, 12\n";
        let read = read_lines(text);
        let raw: Vec<&str> = text.split('\n').collect();
        let reason = &read[1];
        assert_eq!(reason.text, "mun:x a := 2, from 1, 12");
        let twelve = reason.text.find("12").unwrap();
        assert_eq!(physical(&raw, reason.no, twelve), Some((2, 14)));
        assert_eq!(&raw[2][14..16], "12");
        let two = reason.text.find('2').unwrap();
        assert_eq!(physical(&raw, reason.no, two), Some((1, 15)));
    }
}
