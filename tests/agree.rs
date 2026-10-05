//! The checker and the elaborator answer alike where both answer.
//!
//! Each tool answers some questions about a line on its own: what a line
//! implies besides itself, for one. Two answers to one question are two
//! rules, and a proof the one accepts the other refuses. Every theorem is
//! elaborated with each answer compared, as kernel terms, with the checker's
//! to the same question about the same line (`Options::list_answers`).
//!
//! What an item cited by a requires line asks, and what an obtain claims,
//! the elaborator answers with its own matcher, and each answer is compared
//! with the shared one (`citing`) the checker gives.
//!
//! Answers they give differently are listed in `KNOWN`, each a gap a later
//! change closes. The test fails on any other
//! difference, and on a known one that is gone, so that the list says what
//! is so. This reads set.mm, and fails if set.mm cannot be found.

use std::collections::BTreeSet;
use std::path::Path;
use std::sync::Mutex;

use parley::corpus::corpus;
use parley::elab::elaborate::Options;
use parley::source::{Disk, Memory};
use parley::tools::build::{elaborate_one, library};

/// The differences there are, each a gap a later change closes.
///
/// Each is between what the elaborator says an item cited by a requires
/// line asks, or what an obtain claims, and what the shared matcher
/// (`citing::asked`, `citing::obtained`) says. They are of four kinds:
/// - the elaborator binds a letter wrongly, and the shared answer is right
///   (`m + 1 + 1 ∈ ℕ₀` for `m + 1 ∈ ℕ₀`, `P, P, R form a triangle`);
/// - `let P be a point` and `let a be a set` declare a letter, which the
///   elaborator reads as a fact asked (`P ∈ ℂ`) and the shared matcher
///   does not;
/// - the two read a line differently: a define the checker writes out
///   (`min-real`), an induction hypothesis held as kernel terms (`euclid`),
///   a group hypothesis that does not parse (`lagrange`), and an obtain whose
///   function letter only the claim fixes (`harmonic`);
/// - the item applied several times (`derives`), which has no one binding.
const KNOWN: &[&str] = &[
    "proofs/angle-sum.proof:26 | mun:triangle-rotate asks | elaborator only | A ∈ ℂ",
    "proofs/angle-sum.proof:26 | mun:triangle-rotate asks | elaborator only | B ∈ ℂ",
    "proofs/angle-sum.proof:26 | mun:triangle-rotate asks | elaborator only | C ∈ ℂ",
    "proofs/angle-sum.proof:32 | mun:triangle asks | elaborator only | A ∈ ℂ",
    "proofs/angle-sum.proof:32 | mun:triangle asks | elaborator only | B ∈ ℂ",
    "proofs/angle-sum.proof:32 | mun:triangle asks | elaborator only | C ∈ ℂ",
    "proofs/angle-sum.proof:33 | mun:triangle asks | elaborator only | A ∈ ℂ",
    "proofs/angle-sum.proof:33 | mun:triangle asks | elaborator only | B ∈ ℂ",
    "proofs/angle-sum.proof:33 | mun:triangle asks | elaborator only | C ∈ ℂ",
    "proofs/bezout.proof:54 | mun:int-closure asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/bezout.proof:55 | mun:int-closure asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/binomial.proof:119 | mun:power-real asks | elaborator only | m + 1 + 1 ∈ ℕ₀",
    "proofs/binomial.proof:119 | mun:power-real asks | shared only | m + 1 ∈ ℕ₀",
    "proofs/binomial.proof:180 | mun:power-real asks | elaborator only | m − k − k ∈ ℕ₀",
    "proofs/binomial.proof:180 | mun:power-real asks | shared only | m − k ∈ ℕ₀",
    "proofs/binomial.proof:265 | mun:power-real asks | elaborator only | m + 1 + 1 ∈ ℕ₀",
    "proofs/binomial.proof:265 | mun:power-real asks | shared only | m + 1 ∈ ℕ₀",
    "proofs/binomial.proof:333 | mun:binomial-nat0 asks | elaborator only | k − 1 − 1 ∈ ℤ",
    "proofs/binomial.proof:333 | mun:binomial-nat0 asks | shared only | k − 1 ∈ ℤ",
    "proofs/binomial.proof:335 | mun:power-real asks | elaborator only | m + 1 − k + 1 − k ∈ ℕ₀",
    "proofs/binomial.proof:335 | mun:power-real asks | shared only | m + 1 − k ∈ ℕ₀",
    "proofs/binomial.proof:80 | mun:power-real asks | elaborator only | m − k − k ∈ ℕ₀",
    "proofs/binomial.proof:80 | mun:power-real asks | shared only | m − k ∈ ℕ₀",
    "proofs/divisibility-by-three.proof:95 | mun:power-integer asks | elaborator only | m + 1 + 1 ∈ ℕ₀",
    "proofs/divisibility-by-three.proof:95 | mun:power-integer asks | shared only | m + 1 ∈ ℕ₀",
    "proofs/euclid.proof:137 | mun:nat0-nonzero asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/euclid.proof:138 | mun:nat0-int asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/euclid.proof:148 | mun:nat0-nonzero asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/euclid.proof:149 | mun:nat0-int asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/euclid.proof:153 | mun:nat0-int asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/euclid.proof:175 | mun:nat0-nonzero asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/euclid.proof:176 | mun:nat0-int asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/euclid.proof:184 | mun:nat0-int asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/euclid.proof:189 | mun:nat0-real asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/euler.proof:101 | mun:mod-natural asks | elaborator only | r · (r · a) ∈ ℤ",
    "proofs/euler.proof:101 | mun:mod-natural asks | shared only | r · a ∈ ℤ",
    "proofs/euler.proof:222 | mun:int-closure asks | elaborator only | (a^φ(n))^φ(n) ∈ ℤ",
    "proofs/euler.proof:222 | mun:int-closure asks | shared only | a^φ(n) ∈ ℤ",
    "proofs/harmonic.proof:188 | stdlib/calculus/convergent-bounded obtains | shared cannot read | no kernel name for 'x'",
    "proofs/intermediate-value.proof:159 | mun:min-real asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/intermediate-value.proof:169 | mun:min-real asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/intermediate-value.proof:175 | mun:min-real asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/intermediate-value.proof:182 | mun:min-real asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/intermediate-value.proof:189 | mun:min-real asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/intermediate-value.proof:196 | mun:min-real asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/intermediate-value.proof:223 | mun:min-real asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/intermediate-value.proof:259 | mun:interval asks | shared only | b ∈ ℝ",
    "proofs/intermediate-value.proof:265 | mun:interval asks | shared only | b ∈ ℝ",
    "proofs/intermediate-value.proof:270 | mun:interval asks | shared only | b ∈ ℝ",
    "proofs/isosceles.proof:32 | mun:triangle asks | elaborator only | A ∈ ℂ",
    "proofs/isosceles.proof:32 | mun:triangle asks | elaborator only | B ∈ ℂ",
    "proofs/isosceles.proof:32 | mun:triangle asks | elaborator only | C ∈ ℂ",
    "proofs/isosceles.proof:33 | mun:triangle asks | elaborator only | A ∈ ℂ",
    "proofs/isosceles.proof:33 | mun:triangle asks | elaborator only | B ∈ ℂ",
    "proofs/isosceles.proof:33 | mun:triangle asks | elaborator only | C ∈ ℂ",
    "proofs/isosceles.proof:38 | mun:triangle-swap asks | elaborator only | A ∈ ℂ",
    "proofs/isosceles.proof:38 | mun:triangle-swap asks | elaborator only | B ∈ ℂ",
    "proofs/isosceles.proof:38 | mun:triangle-swap asks | elaborator only | C ∈ ℂ",
    "proofs/isosceles.proof:39 | mun:triangle-rotate asks | elaborator only | A ∈ ℂ",
    "proofs/isosceles.proof:39 | mun:triangle-rotate asks | elaborator only | B ∈ ℂ",
    "proofs/isosceles.proof:39 | mun:triangle-rotate asks | elaborator only | C ∈ ℂ",
    "proofs/isosceles.proof:46 | mun:triangle-rotate asks | elaborator only | A ∈ ℂ",
    "proofs/isosceles.proof:46 | mun:triangle-rotate asks | elaborator only | B ∈ ℂ",
    "proofs/isosceles.proof:46 | mun:triangle-rotate asks | elaborator only | C ∈ ℂ",
    "proofs/isosceles.proof:52 | mun:triangle-swap asks | elaborator only | A ∈ ℂ",
    "proofs/isosceles.proof:52 | mun:triangle-swap asks | elaborator only | B ∈ ℂ",
    "proofs/isosceles.proof:52 | mun:triangle-swap asks | elaborator only | C ∈ ℂ",
    "proofs/lagrange.proof:381 | mun:card-nat0 asks | shared cannot read | 'G be a finite group with operation · and identity e' has 29 token(s) left over, starting at 'b'",
    "proofs/lagrange.proof:389 | mun:card-nat0 asks | shared cannot read | 'G be a finite group with operation · and identity e' has 29 token(s) left over, starting at 'b'",
    "proofs/mean-value.proof:52 | mun:interval asks | shared only | b ∈ ℝ",
    "proofs/mean-value.proof:63 | mun:interval asks | shared only | b ∈ ℝ",
    "proofs/perfect-numbers.proof:111 | mun:prime-nat asks | elaborator only | 2^(2^p − 1) − 1 ∈ ℤ",
    "proofs/perfect-numbers.proof:111 | mun:prime-nat asks | elaborator only | 2^(2^p − 1) − 1 is prime",
    "proofs/perfect-numbers.proof:111 | mun:prime-nat asks | shared only | 2^p − 1 ∈ ℤ",
    "proofs/perfect-numbers.proof:111 | mun:prime-nat asks | shared only | 2^p − 1 is prime",
    "proofs/perfect-numbers.proof:116 | mun:prime-nat asks | elaborator only | 2^(2^p − 1) − 1 ∈ ℤ",
    "proofs/perfect-numbers.proof:116 | mun:prime-nat asks | elaborator only | 2^(2^p − 1) − 1 is prime",
    "proofs/perfect-numbers.proof:116 | mun:prime-nat asks | shared only | 2^p − 1 ∈ ℤ",
    "proofs/perfect-numbers.proof:116 | mun:prime-nat asks | shared only | 2^p − 1 is prime",
    "proofs/perfect-numbers.proof:178 | mun:prime-nat asks | elaborator only | 2^(2^p − 1) − 1 ∈ ℤ",
    "proofs/perfect-numbers.proof:178 | mun:prime-nat asks | elaborator only | 2^(2^p − 1) − 1 is prime",
    "proofs/perfect-numbers.proof:178 | mun:prime-nat asks | shared only | 2^p − 1 ∈ ℤ",
    "proofs/perfect-numbers.proof:178 | mun:prime-nat asks | shared only | 2^p − 1 is prime",
    "proofs/perfect-numbers.proof:74 | mun:prime-nat asks | elaborator only | 2^(2^p − 1) − 1 ∈ ℤ",
    "proofs/perfect-numbers.proof:74 | mun:prime-nat asks | elaborator only | 2^(2^p − 1) − 1 is prime",
    "proofs/perfect-numbers.proof:74 | mun:prime-nat asks | shared only | 2^p − 1 ∈ ℤ",
    "proofs/perfect-numbers.proof:74 | mun:prime-nat asks | shared only | 2^p − 1 is prime",
    "proofs/perfect-numbers.proof:79 | mun:prime-nat asks | elaborator only | 2^(2^p − 1) − 1 ∈ ℤ",
    "proofs/perfect-numbers.proof:79 | mun:prime-nat asks | elaborator only | 2^(2^p − 1) − 1 is prime",
    "proofs/perfect-numbers.proof:79 | mun:prime-nat asks | shared only | 2^p − 1 ∈ ℤ",
    "proofs/perfect-numbers.proof:79 | mun:prime-nat asks | shared only | 2^p − 1 is prime",
    "proofs/perfect-numbers.proof:88 | mun:prime-nat asks | elaborator only | 2^(2^p − 1) − 1 ∈ ℤ",
    "proofs/perfect-numbers.proof:88 | mun:prime-nat asks | elaborator only | 2^(2^p − 1) − 1 is prime",
    "proofs/perfect-numbers.proof:88 | mun:prime-nat asks | shared only | 2^p − 1 ∈ ℤ",
    "proofs/perfect-numbers.proof:88 | mun:prime-nat asks | shared only | 2^p − 1 is prime",
    "proofs/pythagoras.proof:100 | mun:sine-positive asks | elaborator only | P ∈ ℂ",
    "proofs/pythagoras.proof:100 | mun:sine-positive asks | elaborator only | Q ∈ ℂ",
    "proofs/pythagoras.proof:100 | mun:sine-positive asks | elaborator only | R ∈ ℂ",
    "proofs/pythagoras.proof:118 | mun:triangle-rotate asks | elaborator only | A ∈ ℂ",
    "proofs/pythagoras.proof:118 | mun:triangle-rotate asks | elaborator only | B ∈ ℂ",
    "proofs/pythagoras.proof:118 | mun:triangle-rotate asks | elaborator only | C ∈ ℂ",
    "proofs/pythagoras.proof:123 | mun:triangle-rotate asks | elaborator only | A ∈ ℂ",
    "proofs/pythagoras.proof:123 | mun:triangle-rotate asks | elaborator only | B ∈ ℂ",
    "proofs/pythagoras.proof:123 | mun:triangle-rotate asks | elaborator only | C ∈ ℂ",
    "proofs/pythagoras.proof:140 | mun:triangle-swap asks | elaborator only | A ∈ ℂ",
    "proofs/pythagoras.proof:140 | mun:triangle-swap asks | elaborator only | B ∈ ℂ",
    "proofs/pythagoras.proof:140 | mun:triangle-swap asks | elaborator only | C ∈ ℂ",
    "proofs/pythagoras.proof:147 | mun:triangle-swap asks | elaborator only | A ∈ ℂ",
    "proofs/pythagoras.proof:147 | mun:triangle-swap asks | elaborator only | B ∈ ℂ",
    "proofs/pythagoras.proof:147 | mun:triangle-swap asks | elaborator only | C ∈ ℂ",
    "proofs/pythagoras.proof:152 | mun:triangle asks | elaborator only | A ∈ ℂ",
    "proofs/pythagoras.proof:152 | mun:triangle asks | elaborator only | B ∈ ℂ",
    "proofs/pythagoras.proof:152 | mun:triangle asks | elaborator only | C ∈ ℂ",
    "proofs/pythagoras.proof:153 | mun:triangle-swap asks | elaborator only | A ∈ ℂ",
    "proofs/pythagoras.proof:153 | mun:triangle-swap asks | elaborator only | B ∈ ℂ",
    "proofs/pythagoras.proof:153 | mun:triangle-swap asks | elaborator only | C ∈ ℂ",
    "proofs/pythagoras.proof:163 | mun:triangle asks | elaborator only | A ∈ ℂ",
    "proofs/pythagoras.proof:163 | mun:triangle asks | elaborator only | B ∈ ℂ",
    "proofs/pythagoras.proof:163 | mun:triangle asks | elaborator only | C ∈ ℂ",
    "proofs/pythagoras.proof:164 | mun:triangle asks | elaborator only | A ∈ ℂ",
    "proofs/pythagoras.proof:164 | mun:triangle asks | elaborator only | B ∈ ℂ",
    "proofs/pythagoras.proof:164 | mun:triangle asks | elaborator only | C ∈ ℂ",
    "proofs/pythagoras.proof:175 | mun:triangle-rotate asks | elaborator only | A ∈ ℂ",
    "proofs/pythagoras.proof:175 | mun:triangle-rotate asks | elaborator only | B ∈ ℂ",
    "proofs/pythagoras.proof:175 | mun:triangle-rotate asks | elaborator only | C ∈ ℂ",
    "proofs/pythagoras.proof:194 | mun:distance-real asks | elaborator only | A ∈ ℂ",
    "proofs/pythagoras.proof:194 | mun:distance-real asks | elaborator only | B ∈ ℂ",
    "proofs/pythagoras.proof:195 | mun:distance-real asks | elaborator only | A ∈ ℂ",
    "proofs/pythagoras.proof:195 | mun:distance-real asks | elaborator only | C ∈ ℂ",
    "proofs/pythagoras.proof:196 | mun:distance-real asks | elaborator only | B ∈ ℂ",
    "proofs/pythagoras.proof:196 | mun:distance-real asks | elaborator only | C ∈ ℂ",
    "proofs/pythagoras.proof:197 | mun:distance-real asks | elaborator only | A ∈ ℂ",
    "proofs/pythagoras.proof:197 | mun:distance-real asks | elaborator only | D ∈ ℂ",
    "proofs/pythagoras.proof:198 | mun:distance-real asks | elaborator only | B ∈ ℂ",
    "proofs/pythagoras.proof:198 | mun:distance-real asks | elaborator only | D ∈ ℂ",
    "proofs/pythagoras.proof:45 | mun:triangle-angle-real asks | elaborator only | P ∈ ℂ",
    "proofs/pythagoras.proof:45 | mun:triangle-angle-real asks | elaborator only | Q ∈ ℂ",
    "proofs/pythagoras.proof:45 | mun:triangle-angle-real asks | elaborator only | R ∈ ℂ",
    "proofs/pythagoras.proof:46 | mun:triangle-angle-real asks | elaborator only | P ∈ ℂ",
    "proofs/pythagoras.proof:46 | mun:triangle-angle-real asks | elaborator only | P, P, R form a triangle",
    "proofs/pythagoras.proof:46 | mun:triangle-angle-real asks | elaborator only | R ∈ ℂ",
    "proofs/pythagoras.proof:46 | mun:triangle-angle-real asks | shared only | P, Q, R form a triangle",
    "proofs/pythagoras.proof:47 | mun:triangle-angle-real asks | elaborator only | Q ∈ ℂ",
    "proofs/pythagoras.proof:47 | mun:triangle-angle-real asks | elaborator only | R ∈ ℂ",
    "proofs/pythagoras.proof:47 | mun:triangle-angle-real asks | elaborator only | R, Q, R form a triangle",
    "proofs/pythagoras.proof:47 | mun:triangle-angle-real asks | shared only | P, Q, R form a triangle",
    "proofs/pythagoras.proof:48 | mun:triangle-angle-real asks | elaborator only | P′ ∈ ℂ",
    "proofs/pythagoras.proof:48 | mun:triangle-angle-real asks | elaborator only | Q′ ∈ ℂ",
    "proofs/pythagoras.proof:48 | mun:triangle-angle-real asks | elaborator only | R′ ∈ ℂ",
    "proofs/pythagoras.proof:49 | mun:triangle-angle-real asks | elaborator only | P′ ∈ ℂ",
    "proofs/pythagoras.proof:49 | mun:triangle-angle-real asks | elaborator only | Q′ ∈ ℂ",
    "proofs/pythagoras.proof:49 | mun:triangle-angle-real asks | elaborator only | R′ ∈ ℂ",
    "proofs/pythagoras.proof:50 | mun:triangle-angle-real asks | elaborator only | P′ ∈ ℂ",
    "proofs/pythagoras.proof:50 | mun:triangle-angle-real asks | elaborator only | Q′ ∈ ℂ",
    "proofs/pythagoras.proof:50 | mun:triangle-angle-real asks | elaborator only | R′ ∈ ℂ",
    "proofs/pythagoras.proof:66 | mun:distance-real asks | elaborator only | P ∈ ℂ",
    "proofs/pythagoras.proof:66 | mun:distance-real asks | elaborator only | Q ∈ ℂ",
    "proofs/pythagoras.proof:67 | mun:distance-real asks | elaborator only | P ∈ ℂ",
    "proofs/pythagoras.proof:67 | mun:distance-real asks | elaborator only | R ∈ ℂ",
    "proofs/pythagoras.proof:68 | mun:distance-real asks | elaborator only | P′ ∈ ℂ",
    "proofs/pythagoras.proof:68 | mun:distance-real asks | elaborator only | R′ ∈ ℂ",
    "proofs/pythagoras.proof:69 | mun:triangle-angle-real asks | elaborator only | P ∈ ℂ",
    "proofs/pythagoras.proof:69 | mun:triangle-angle-real asks | elaborator only | P, P, R form a triangle",
    "proofs/pythagoras.proof:69 | mun:triangle-angle-real asks | elaborator only | R ∈ ℂ",
    "proofs/pythagoras.proof:69 | mun:triangle-angle-real asks | shared only | P, Q, R form a triangle",
    "proofs/pythagoras.proof:71 | mun:triangle-angle-real asks | elaborator only | Q ∈ ℂ",
    "proofs/pythagoras.proof:71 | mun:triangle-angle-real asks | elaborator only | R ∈ ℂ",
    "proofs/pythagoras.proof:71 | mun:triangle-angle-real asks | elaborator only | R, Q, R form a triangle",
    "proofs/pythagoras.proof:71 | mun:triangle-angle-real asks | shared only | P, Q, R form a triangle",
    "proofs/pythagoras.proof:76 | mun:distance-real asks | elaborator only | P ∈ ℂ",
    "proofs/pythagoras.proof:76 | mun:distance-real asks | elaborator only | R ∈ ℂ",
    "proofs/pythagoras.proof:77 | mun:distance-real asks | elaborator only | P′ ∈ ℂ",
    "proofs/pythagoras.proof:77 | mun:distance-real asks | elaborator only | Q′ ∈ ℂ",
    "proofs/pythagoras.proof:78 | mun:distance-real asks | elaborator only | P′ ∈ ℂ",
    "proofs/pythagoras.proof:78 | mun:distance-real asks | elaborator only | R′ ∈ ℂ",
    "proofs/pythagoras.proof:79 | mun:triangle-angle-real asks | elaborator only | P ∈ ℂ",
    "proofs/pythagoras.proof:79 | mun:triangle-angle-real asks | elaborator only | P, P, R form a triangle",
    "proofs/pythagoras.proof:79 | mun:triangle-angle-real asks | elaborator only | R ∈ ℂ",
    "proofs/pythagoras.proof:79 | mun:triangle-angle-real asks | shared only | P, Q, R form a triangle",
    "proofs/pythagoras.proof:81 | mun:triangle-angle-real asks | elaborator only | Q ∈ ℂ",
    "proofs/pythagoras.proof:81 | mun:triangle-angle-real asks | elaborator only | R ∈ ℂ",
    "proofs/pythagoras.proof:81 | mun:triangle-angle-real asks | elaborator only | R, Q, R form a triangle",
    "proofs/pythagoras.proof:81 | mun:triangle-angle-real asks | shared only | P, Q, R form a triangle",
    "proofs/pythagoras.proof:92 | mun:distance-real asks | elaborator only | P ∈ ℂ",
    "proofs/pythagoras.proof:92 | mun:distance-real asks | elaborator only | Q ∈ ℂ",
    "proofs/pythagoras.proof:93 | mun:distance-real asks | elaborator only | P ∈ ℂ",
    "proofs/pythagoras.proof:93 | mun:distance-real asks | elaborator only | R ∈ ℂ",
    "proofs/pythagoras.proof:94 | mun:distance-real asks | elaborator only | P′ ∈ ℂ",
    "proofs/pythagoras.proof:94 | mun:distance-real asks | elaborator only | Q′ ∈ ℂ",
    "proofs/pythagoras.proof:95 | mun:distance-real asks | elaborator only | P′ ∈ ℂ",
    "proofs/pythagoras.proof:95 | mun:distance-real asks | elaborator only | R′ ∈ ℂ",
    "proofs/pythagoras.proof:98 | mun:triangle-angle-real asks | elaborator only | P ∈ ℂ",
    "proofs/pythagoras.proof:98 | mun:triangle-angle-real asks | elaborator only | P, P, R form a triangle",
    "proofs/pythagoras.proof:98 | mun:triangle-angle-real asks | elaborator only | R ∈ ℂ",
    "proofs/pythagoras.proof:98 | mun:triangle-angle-real asks | shared only | P, Q, R form a triangle",
    "proofs/sqrt2-irrational.proof:145 | mun:int-closure asks | elaborator only | p ∈ ℤ",
    "proofs/sqrt2-irrational.proof:173 | mun:int-closure asks | elaborator only | p ∈ ℤ",
    "proofs/sqrt2-irrational.proof:46 | mun:int-closure asks | shared declines | no group of the item concludes the claim from the facts named",
    "proofs/subsets.proof:283 | mun:not-in-difference asks | elaborator only | a is a set",
    "proofs/subsets.proof:283 | mun:not-in-difference asks | elaborator only | X is a set",
];

#[test]
fn the_tools_answer_alike() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let tree = Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap();
    let names: Vec<String> = corpus(&tree)
        .expect("the corpus reads")
        .theorems
        .iter()
        .map(|t| t.qualified())
        .collect();
    let options = Options {
        list_answers: true,
        ..Options::default()
    };
    let found = Mutex::new(BTreeSet::new());
    let next = Mutex::new(names.iter());
    // Each worker loads set.mm once for itself: the library is not shared
    // between threads.
    let workers = std::thread::available_parallelism()
        .map_or(1, |n| n.get())
        .clamp(1, 8);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                let lib = library(root, None).expect(
                    "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
                );
                loop {
                    let Some(name) = next.lock().unwrap().next() else {
                        break;
                    };
                    let done = elaborate_one(&tree, name, &lib, options)
                        .unwrap_or_else(|p| panic!("{name} does not elaborate: {p}"));
                    found.lock().unwrap().extend(done.answers);
                }
            });
        }
    });
    let all: BTreeSet<String> = found.into_inner().unwrap();
    // What the elaborator answers alone, which a later change compares with
    // the shared answer: what an item cited by a requires line asks, and
    // what an obtain claims. The hook is counted, so that one that stopped
    // running is not taken for one that agrees.
    let asked = all.iter().filter(|a| a.contains(" | asked | ")).count();
    let obtained = all.iter().filter(|a| a.contains(" | obtained | ")).count();
    let unanswered: Vec<&String> = all
        .iter()
        .filter(|a| a.contains(" | asked | ") && a.contains("cannot answer"))
        .collect();
    println!(
        "{asked} hypotheses asked, {obtained} sentences obtained, {} citations the elaborator cannot answer:",
        unanswered.len()
    );
    for a in &unanswered {
        println!("  {a}");
    }
    assert!(
        asked > 0 && obtained > 0,
        "the listing hook gave no asked items"
    );
    let found: BTreeSet<String> = all
        .into_iter()
        .filter(|a| !a.contains(" | asked | ") && !a.contains(" | obtained | "))
        .collect();
    let known: BTreeSet<String> = KNOWN.iter().map(|s| s.to_string()).collect();
    let new: Vec<&String> = found.difference(&known).collect();
    let gone: Vec<&String> = known.difference(&found).collect();
    println!("{} theorems, {} differences", names.len(), found.len());
    assert!(
        new.is_empty() && gone.is_empty(),
        "differences not known:\n{}\n\nknown differences no longer found:\n{}",
        new.iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n"),
        gone.iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n")
    );
}
