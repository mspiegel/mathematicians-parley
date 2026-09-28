//! Splitting a sentence into tokens.

use indexmap::IndexSet;
use unicode_properties::{GeneralCategory, UnicodeGeneralCategory};

use crate::outcome::{Checked, Problem};
use crate::text::repr;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Word,
    Name,
    Numeral,
    Symbol,
    Open,
    Close,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub text: String,
    /// Where it starts, counted in characters.
    pub at: usize,
}

/// A letter as a name or a word is spelt with: Latin, or Greek.
pub fn is_letter(c: char) -> bool {
    c.is_ascii_alphabetic() || ('α'..='ω').contains(&c) || ('Α'..='Ω').contains(&c)
}

/// What may follow a name's letter: a subscript digit, or a prime.
pub fn is_mark(c: char) -> bool {
    ('₀'..='₉').contains(&c) || c == '′'
}

/// A decimal digit, as `\d` reads one: any character that is a digit in
/// some script.
pub fn is_digit(c: char) -> bool {
    c.general_category() == GeneralCategory::DecimalNumber
}

/// A run of letters is a declared word if one matches by longest match, and
/// otherwise a single name. A numeral is a maximal run of digits. Round
/// brackets belong to the grammar rather than to any notation.
///
/// The position is carried because text that does not lex is a defect with
/// somewhere to point, and a defect with nowhere to point reads like a route
/// declining.
///
/// At the start of a sentence a declared word also matches with its first
/// letter capitalised, which is how the corpus writes `For all` and `There
/// is`. The allowance is deliberately that narrow: matching case anywhere
/// would let the name `s` match the declared word `S`.
pub fn tokenise(
    text: &str,
    words: &IndexSet<String>,
    symbols: &[String],
    path: &str,
    line: usize,
) -> Checked<Vec<Token>> {
    let chars: Vec<char> = text.chars().collect();
    let mut out: Vec<Token> = Vec::new();
    let mut i = 0;
    let take = |out: &mut Vec<Token>, kind, spelling: String, at: usize| -> usize {
        let len = spelling.chars().count();
        out.push(Token {
            kind,
            text: spelling,
            at,
        });
        at + len
    };
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            while i < chars.len() && chars[i].is_whitespace() {
                i += 1;
            }
            continue;
        }
        if c == '(' || c == ')' {
            let kind = if c == '(' {
                TokenKind::Open
            } else {
                TokenKind::Close
            };
            i = take(&mut out, kind, c.to_string(), i);
            continue;
        }
        if is_digit(c) {
            let end = (i..chars.len())
                .find(|&j| !is_digit(chars[j]))
                .unwrap_or(chars.len());
            i = take(
                &mut out,
                TokenKind::Numeral,
                chars[i..end].iter().collect(),
                i,
            );
            continue;
        }
        if is_letter(c) {
            let end = (i..chars.len())
                .find(|&j| !is_letter(chars[j]))
                .unwrap_or(chars.len());
            let run: Vec<char> = chars[i..end].to_vec();
            let mut candidates = vec![run.clone()];
            if out.is_empty() && run[0].is_uppercase() {
                let mut lowered: Vec<char> = run[0].to_lowercase().collect();
                lowered.extend_from_slice(&run[1..]);
                candidates.push(lowered);
            }
            // Only a word of two letters or more is lexed as a word. Three
            // declared literals are a single letter, `a` in "form a triangle"
            // and in "there is a bijection", and `S` and `G` naming the two
            // sum functions. All three are also variable names in the corpus,
            // and `a` is one of the commonest. A single letter is therefore
            // always a name, and a pattern's single-letter literal still
            // matches it, because a pattern matches a token by its text.
            let hit = candidates.iter().find_map(|cand| {
                (2..=cand.len())
                    .rev()
                    .map(|n| cand[..n].iter().collect::<String>())
                    .find(|w| words.contains(w))
            });
            if let Some(word) = hit {
                i = take(&mut out, TokenKind::Word, word, i);
                continue;
            }
            let mut end = i + 1;
            while end < chars.len() && is_mark(chars[end]) {
                end += 1;
            }
            i = take(&mut out, TokenKind::Name, chars[i..end].iter().collect(), i);
            continue;
        }
        let rest: String = chars[i..].iter().collect();
        if let Some(sym) = symbols.iter().find(|s| rest.starts_with(s.as_str())) {
            i = take(&mut out, TokenKind::Symbol, sym.clone(), i);
            continue;
        }
        let near: String = chars[i..(i + 12).min(chars.len())].iter().collect();
        return Err(Problem::new(
            path,
            line,
            format!("no token at {} in {}", repr(&near), repr(text)),
        ));
    }
    Ok(out)
}
