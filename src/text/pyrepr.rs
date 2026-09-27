//! A string written the way Python's `repr()` writes it.
//!
//! The checker's and the elaborator's messages quote text with `!r`, and the
//! planted-defect tests look for those messages. So the quoting is the
//! reference implementation's: single quotes, unless the text holds a single
//! quote and no double one; a backslash, the chosen quote, and the three
//! common control characters escaped by name; any other character that is
//! not printable escaped by its code; everything printable kept as it is,
//! non-ASCII included.

use unicode_properties::{GeneralCategory, UnicodeGeneralCategory};

/// Whether Python's `str.isprintable` holds of `c`: everything except the
/// control, format, surrogate, private-use and unassigned characters and the
/// separators other than the ASCII space.
fn printable(c: char) -> bool {
    use GeneralCategory::*;
    if c == ' ' {
        return true;
    }
    !matches!(
        c.general_category(),
        Control
            | Format
            | Surrogate
            | PrivateUse
            | Unassigned
            | SpaceSeparator
            | LineSeparator
            | ParagraphSeparator
    )
}

/// `repr(s)`.
pub fn repr(s: &str) -> String {
    let quote = if s.contains('\'') && !s.contains('"') {
        '"'
    } else {
        '\''
    };
    let mut out = String::with_capacity(s.len() + 2);
    out.push(quote);
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c == quote => {
                out.push('\\');
                out.push(c);
            }
            c if printable(c) => out.push(c),
            c => {
                let code = c as u32;
                if code < 0x100 {
                    out.push_str(&format!("\\x{code:02x}"));
                } else if code < 0x10000 {
                    out.push_str(&format!("\\u{code:04x}"));
                } else {
                    out.push_str(&format!("\\U{code:08x}"));
                }
            }
        }
    }
    out.push(quote);
    out
}

#[cfg(test)]
mod tests {
    use super::repr;

    // Each expected value is what CPython 3.14 prints for `repr` of the input.
    #[test]
    fn quotes_as_python_does() {
        assert_eq!(repr("abc"), "'abc'");
        assert_eq!(repr("it's"), "\"it's\"");
        assert_eq!(repr("'\""), "'\\'\"'");
        assert_eq!(repr("a\\b"), "'a\\\\b'");
        assert_eq!(repr("x ∈ 𝒫A"), "'x ∈ 𝒫A'");
        assert_eq!(repr("a\nb\tc"), "'a\\nb\\tc'");
        assert_eq!(
            repr("\u{a0}\u{ad}\u{200b}\u{7f}"),
            "'\\xa0\\xad\\u200b\\x7f'"
        );
        assert_eq!(repr("\u{e000}"), "'\\ue000'");
    }
}
