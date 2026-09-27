//! A decline that nobody asks about does not compile.
//!
//! Each file directly under `tests/declines/` is a shape in which a route's
//! answer is used without asking whether the route declined: passed on as
//! though it were what was asked for, formatted into text, stored, unpacked,
//! spread, handed back, or reached through another module or through
//! `self`. Each one must fail to compile. A shape that compiled would be a
//! place where a decline could reach a proof and shorten it without a word.
//!
//! The files under `tests/declines/asked/` are the ways of asking that are
//! right, and each must compile: a check that refused them would be refusing
//! the code it exists to require.

#[test]
fn a_decline_nobody_asks_about_does_not_compile() {
    let cases = trybuild::TestCases::new();
    cases.compile_fail("tests/declines/*.rs");
    cases.pass("tests/declines/asked/*.rs");
}
