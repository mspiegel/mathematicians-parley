//! A decline that nobody asks about does not compile.
//!
//! Each file under `tests/declines/` is a shape in which a route's answer is
//! used without asking whether the route declined: passed on as though it
//! were what was asked for, formatted into text, stored, unpacked, or
//! dropped. Each one must fail to compile. A shape that compiled would be a
//! place where a decline could reach a proof and shorten it without a word.

#[test]
fn a_decline_nobody_asks_about_does_not_compile() {
    let cases = trybuild::TestCases::new();
    cases.compile_fail("tests/declines/*.rs");
}
