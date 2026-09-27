//! The three things a step of the tools can come back with.
//!
//! A value, which is what was asked for. A [`Problem`], which is a defect
//! somebody has to fix: the proof text says something wrong, or a database
//! record does, and nothing carries on past it. And a [`Decline`], which is a
//! route saying it does not apply: a lemma that does not fit, a pattern that
//! does not match, an emitter with no shape for what it was given. Nothing has
//! gone wrong when a route declines; it is the ordinary course of a run, and
//! what receives one tries the next way.
//!
//! The two failures are different types so that neither can be mistaken for
//! the other. A `Problem` travels in the error position of a `Result` and is
//! propagated with `?`. A `Decline` travels inside a [`Route`], which is
//! `#[must_use]` and is neither a proof nor a term, so a caller that forgot to
//! ask whether a route declined does not compile. There is no conversion from
//! a `Decline` into a `Problem`: turning one into the other is always written
//! out, with [`Decline::into_problem`], at the place that decides the decline
//! was a defect after all.

use std::borrow::Cow;
use std::fmt;

/// A defect found while reading or elaborating, with where it was found.
///
/// Nothing matches on a `Problem` in order to try another way: that would be
/// accepting a proof with a defect in it. The checker collects them, one per
/// defect, into its report; everything else propagates them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Problem {
    pub path: String,
    pub line: usize,
    pub message: String,
}

impl Problem {
    pub fn new(
        path: impl Into<String>,
        line: usize,
        message: impl Into<String>,
    ) -> Self {
        Problem {
            path: path.into(),
            line,
            message: message.into(),
        }
    }
}

impl fmt::Display for Problem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}  {}", self.path, self.line, self.message)
    }
}

impl std::error::Error for Problem {}

/// What can go wrong, as the error type of everything that can find a defect.
pub type Checked<T> = Result<T, Problem>;

/// A route saying it does not apply, and why.
///
/// The reason is built only when something reads it. Most are read by
/// nobody: a route declines and the caller tries the next. Elaborating the
/// geometric series declines over a million times, and writing each reason
/// out the way a Metamath file writes a term was a third of what that cost.
/// So a decline keeps a shape with `{}` holes and the terms that fill them,
/// and fills them only when [`Decline::render`] is asked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decline {
    shape: Cow<'static, str>,
    terms: Vec<String>,
}

impl Decline {
    /// A decline whose reason is already written out.
    pub fn new(reason: impl Into<Cow<'static, str>>) -> Self {
        Decline {
            shape: reason.into(),
            terms: Vec::new(),
        }
    }

    /// A decline whose reason has a `{}` hole for each term, filled in the
    /// way a Metamath file writes the term only when the reason is read.
    pub fn shaped(shape: impl Into<Cow<'static, str>>, terms: Vec<String>) -> Self {
        Decline {
            shape: shape.into(),
            terms,
        }
    }

    /// The reason, with each hole filled by `spell` applied to its term.
    pub fn render(&self, spell: impl Fn(&str) -> String) -> String {
        if self.terms.is_empty() {
            return self.shape.to_string();
        }
        let mut out = String::new();
        let mut terms = self.terms.iter();
        let mut rest: &str = &self.shape;
        while let Some(at) = rest.find("{}") {
            out.push_str(&rest[..at]);
            if let Some(term) = terms.next() {
                out.push_str(&spell(term));
            }
            rest = &rest[at + 2..];
        }
        out.push_str(rest);
        out
    }

    /// The reason as written, for a decline that has no terms to spell.
    pub fn reason(&self) -> String {
        self.render(|t| t.to_string())
    }

    /// The decline, taken as the defect it is at this place.
    pub fn into_problem(self, path: impl Into<String>, line: usize) -> Problem {
        Problem::new(path, line, self.reason())
    }
}

/// What a route gives back: what it built, or that it does not apply.
#[must_use = "a route may have declined, and a declined route is not a result"]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Route<T> {
    Built(T),
    Declined(Decline),
}

pub use Route::{Built, Declined};

impl<T> Route<T> {
    /// A route that declines for the reason given.
    pub fn no(reason: impl Into<Cow<'static, str>>) -> Self {
        Route::Declined(Decline::new(reason))
    }

    pub fn is_declined(&self) -> bool {
        matches!(self, Route::Declined(_))
    }

    /// What was built, or None where the route declined.
    pub fn built(self) -> Option<T> {
        match self {
            Route::Built(t) => Some(t),
            Route::Declined(_) => None,
        }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Route<U> {
        match self {
            Route::Built(t) => Route::Built(f(t)),
            Route::Declined(d) => Route::Declined(d),
        }
    }

    /// This route, or the next where this one declined.
    pub fn or_try(self, next: impl FnOnce() -> Route<T>) -> Route<T> {
        match self {
            Route::Built(t) => Route::Built(t),
            Route::Declined(_) => next(),
        }
    }

    /// What was built, or the defect the decline is at this place.
    pub fn or_problem(self, path: impl Into<String>, line: usize) -> Checked<T> {
        match self {
            Route::Built(t) => Ok(t),
            Route::Declined(d) => Err(d.into_problem(path, line)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_problem_says_where() {
        let p = Problem::new("proof/a.proof", 12, "no justification");
        assert_eq!(p.to_string(), "proof/a.proof:12  no justification");
    }

    #[test]
    fn a_decline_fills_its_holes_only_when_read() {
        let d = Decline::shaped("{} is not {}", vec!["cA".into(), "cB".into()]);
        assert_eq!(d.render(|t| t.to_uppercase()), "CA is not CB");
    }

    #[test]
    fn the_next_route_is_tried_only_after_a_decline() {
        let first: Route<u32> = Route::Built(1);
        assert_eq!(first.or_try(|| panic!("not asked")), Route::Built(1));
        let second: Route<u32> = Route::no("does not fit");
        assert_eq!(second.or_try(|| Route::Built(2)), Route::Built(2));
    }
}
