//! The character set every file is read in (`DATABASE.md`).
//!
//! Files are UTF-8 in Normalisation Form C, and are read as Unicode scalar
//! values. A file that is not UTF-8, or not in Form C, is refused rather
//! than normalised: an editor that normalised differently would otherwise
//! change the archive without anyone editing it.

use unicode_normalization::UnicodeNormalization;

use crate::outcome::{Checked, Problem};

/// The text of a file that is UTF-8 in Form C.
pub fn check_encoding(path: &str, raw: &[u8]) -> Checked<String> {
    let text = match std::str::from_utf8(raw) {
        Ok(text) => text,
        Err(e) => {
            return Err(Problem::new(
                path,
                1,
                format!("not valid UTF-8: {}", utf8_error(raw, &e)),
            ))
        }
    };
    if text.nfc().collect::<String>() != text {
        for (no, line) in text.split('\n').enumerate() {
            if line.nfc().collect::<String>() != line {
                return Err(Problem::new(
                    path,
                    no + 1,
                    "not in Unicode Normalisation Form C",
                ));
            }
        }
    }
    Ok(text.to_string())
}

/// A decoding failure, said the way Python's codec says it.
fn utf8_error(raw: &[u8], e: &std::str::Utf8Error) -> String {
    let at = e.valid_up_to();
    match e.error_len() {
        Some(len) => {
            let reason = if (0x80..0xc2).contains(&raw[at]) || raw[at] >= 0xf5 {
                "invalid start byte"
            } else {
                "invalid continuation byte"
            };
            if len == 1 {
                format!(
                    "'utf-8' codec can't decode byte 0x{:02x} in position {at}: {reason}",
                    raw[at]
                )
            } else {
                format!(
                    "'utf-8' codec can't decode bytes in position {at}-{}: {reason}",
                    at + len - 1
                )
            }
        }
        None => {
            let end = raw.len() - 1;
            if end == at {
                format!(
                    "'utf-8' codec can't decode byte 0x{:02x} in position {at}: unexpected end of data",
                    raw[at]
                )
            } else {
                format!(
                    "'utf-8' codec can't decode bytes in position {at}-{end}: unexpected end of data"
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn form_c_is_required() {
        let decomposed = "a\n\u{2208}\u{338}\n";
        let e = check_encoding("f", decomposed.as_bytes()).unwrap_err();
        assert_eq!(e.to_string(), "f:2  not in Unicode Normalisation Form C");
        assert_eq!(check_encoding("f", "∉".as_bytes()).unwrap(), "∉");
    }

    #[test]
    fn bad_bytes_are_said_as_python_says_them() {
        let e = check_encoding("f", b"ab\xffc").unwrap_err();
        assert_eq!(
            e.message,
            "not valid UTF-8: 'utf-8' codec can't decode byte 0xff in position 2: invalid start byte"
        );
    }
}
