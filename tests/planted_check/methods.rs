//! The planted cases about what a method decides: algebra, inequalities, arithmetic, inspection, membership, cases, contradiction and induction.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
        // A line marked impossible is reached by its reasons from the lines
        // they cite (`SYNTAX.md`, contradiction); `arithmetic` as its reason
        // cites nothing and proves only what is true, and the step is told
        // so rather than only that its claim is false.
        case(
            "give a line marked impossible arithmetic as its reason",
            vec![edit(
                "proofs/wiedijk/impossible-by-arithmetic.proof",
                None,
                "theorem impossible-by-arithmetic\n  let a ∈ ℝ                                                           (H1)\n  assume a > 0                                                        (H2)\n  then a ≠ 0\n\n1.  a ≠ 0\n    contradiction\n    suppose a = 0                                                     (S)\n\n    1.1.  0 > 0\n          substitute a = 0 (S) into H2\n\n    1.2.  0 > 0, which is impossible\n          arithmetic\n".to_string(),
            )],
            "proofs/wiedijk/impossible-by-arithmetic.proof:14  step 1.2 is marked impossible and gives arithmetic as its reason, which proves only what is true; a line marked impossible is reached by its reasons from the lines they cite",
        ),
        // A requires line's reason shows its fact as a step's reason shows
        // its claim, so a method that does not decide the fact is refused
        // there as it is for a step: `algebra` decides equations, and a
        // membership is `membership`'s.
        case(
            "give a requires line's membership a method that does not decide it",
            vec![edit(
                "proofs/setmm/square-root-positive.proof",
                Some("inequalities, from S\n          requires √a ∈ ℝ: from 1".to_string()),
                "inequalities, from S\n          requires √a ∈ ℝ: algebra".to_string(),
            )],
            "the requires line √a ∈ ℝ of step 2.1 names algebra, which does not decide what it says",
        ),
        // A false divisibility of numerals, on a requires line: the checker
        // works it out as `arithmetic` does (`check_arithmetic_holds`).
        case(
            "a divisibility of numerals that does not hold",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("                       ≡ 1 (mod 3)        arithmetic\n".to_string()),
                "                       ≡ 1 (mod 3)        arithmetic\n          requires 3 divides 10 − 2: arithmetic\n".to_string(),
            )],
            "the requires line 3 divides 10 − 2 of step 1.3 is arithmetic, which is false",
        ),
        // An odd number is an integer, so arithmetic finds a half not odd
        // though it does not say whether 2 divides it.
        case(
            "say a half is odd",
            vec![edit(
                "tests/elaborator/a-half-odd.proof",
                None,
                "theorem a-half-odd\n  then 1/2 is odd\n\n1.  1/2 is odd\n    arithmetic\n".to_string(),
            )],
            "step 1 claims 1/2 is odd, which is false",
        ),
        // An induction over ℕ starts at 1 and writes it, runs over ℕ or ℕ₀,
        // and has a base part and a step part.
        case(
            "an induction starting where its set does not",
            vec![edit(
                "proofs/wiedijk/sum-formula.proof",
                Some("    induction on k starting at 1\n".to_string()),
                "    induction on k starting at 2\n".to_string(),
            )],
            "an induction over ℕ starts at 1, and the text says 2",
        ),
        case(
            "an induction over a set no induction runs over",
            vec![edit(
                "proofs/wiedijk/sum-formula.proof",
                Some("1.  For all k ∈ ℕ, S(k) = k(k + 1)/2.\n".to_string()),
                "1.  For all k ∈ ℤ, S(k) = k(k + 1)/2.\n".to_string(),
            )],
            "step 1 is an induction over ℤ, and an induction runs over ℕ from 1 or ℕ₀ from 0",
        ),
        case(
            "an induction on a letter the theorem already introduces",
            vec![edit(
                "proofs/wiedijk/sum-formula.proof",
                Some("(H1)\n  then ".to_string()),
                "(H1)\n  let k ∈ ℕ (H2)\n  then ".to_string(),
            )],
            "step 1 is an induction on k, and k is a letter already introduced here; an induction runs over a letter of its own",
        ),
        // A claim the method named does not decide, a membership said by
        // `inequalities`: no closure step is taken without examining it.
        case(
            "rest a claim on a method that does not decide it",
            vec![edit(
                "proofs/hammack/mersenne-prime-exponent.proof",
                Some("    1.13. j ≤ q\n          inequalities, from 1.3\n".to_string()),
                "    1.13. j ∈ ℤ\n          inequalities, from 1.3\n".to_string(),
            )],
            "step 1.13 names inequalities, which does not decide what it claims",
        ),
        // A link of numerals alone naming arithmetic, worked out whole.
        case(
            "a chain link of numerals that is false",
            vec![edit(
                "proofs/wiedijk/sum-formula.proof",
                Some("= 1(1 + 1)/2            arithmetic".to_string()),
                "= 1(1 + 1)/3            arithmetic".to_string(),
            )],
            "a link of step 1.1 names arithmetic for 1 = 1(1 + 1)/3, which is false",
        ),
        case(
            "claim by arithmetic that a pair differs from itself",
            vec![edit(
                "tests/elaborator/pairs-compared.proof",
                Some("  then (1, 1) ≠ (2, 3)\n\n1.  (1, 1) ≠ (2, 3)".to_string()),
                "  then (1, 1) ≠ (1, 1)\n\n1.  (1, 1) ≠ (1, 1)".to_string(),
            )],
            "step 1 claims (1, 1) ≠ (1, 1), which is false",
        ),
        case(
            "claim by algebra that two pairs differ, citing nothing",
            vec![edit(
                "tests/elaborator/pairs-compared.proof",
                Some("    algebra, from H5".to_string()),
                "    algebra".to_string(),
            )],
            "(a, b) ≠ (c, d) is not a rescaling of any disequality step 1 cites",
        ),
        case(
            "claim by inspection that a listed pair is not in its list",
            vec![edit(
                "tests/elaborator/pairs-compared.proof",
                Some(
                    "  then (1, 2) ∉ {(3, 4), (1, 5)}\n\n1.  (1, 2) ∉ {(3, 4), (1, 5)}"
                        .to_string(),
                ),
                "  then (1, 5) ∉ {(3, 4), (1, 5)}\n\n1.  (1, 5) ∉ {(3, 4), (1, 5)}"
                    .to_string(),
            )],
            "step 1 claims (1, 5) ∉ {(3, 4), (1, 5)}, which inspection of what it cites shows false",
        ),
        // Inspection decides "is prime" by the number: a composite at any
        // size by its least factor, and a prime only below 29², past which
        // trial division by the primes up to 23 settles nothing.
        case(
            "claim by inspection that a composite number is prime",
            vec![edit(
                "tests/notations/primes.proof",
                Some("  then 97 is prime\n\n1.  97 is prime\n".to_string()),
                "  then 91 is prime\n\n1.  91 is prime\n".to_string(),
            )],
            "step 1 claims 91 is prime, which inspection of what it cites shows false",
        ),
        case(
            "claim by inspection that a prime past 841 is prime",
            vec![edit(
                "tests/notations/primes.proof",
                Some("  then 97 is prime\n\n1.  97 is prime\n".to_string()),
                "  then 853 is prime\n\n1.  853 is prime\n".to_string(),
            )],
            "and 853 is not below 841",
        ),
        // A count of the odd vertices that leaves A out, 5 being odd, which
        // the checker counts by inspection as the reader does.
        case(
            "a parity inspection settles that a count leaves out",
            vec![edit(
                "proofs/wiedijk/konigsberg.proof",
                Some("6.  |{x ∈ V : deg(x) is odd}| = 4".to_string()),
                "6.  |{x ∈ V : deg(x) is odd}| = 3".to_string(),
            )],
            "step 6 claims |{x ∈ V : deg(x) is odd}| = 3, which inspection of what it cites shows false",
        ),
        // A line of "or"s read from a membership has an equation for each
        // element of the set and for nothing else, and a range is read as
        // a list only up to its cap.
        case(
            "a line of ors by inspection that leaves out an element of the range",
            vec![
                edit(
                    "tests/elaborator/inspection-cases-of-a-range.proof",
                    Some("  then k = 4 or k = 0 or 2 = k or k = 1 or k = 1 + 2\n".to_string()),
                    "  then k = 4 or k = 0 or 2 = k or k = 1 + 2\n".to_string(),
                ),
                edit(
                    "tests/elaborator/inspection-cases-of-a-range.proof",
                    Some("1.  k = 4 or k = 0 or 2 = k or k = 1 or k = 1 + 2\n".to_string()),
                    "1.  k = 4 or k = 0 or 2 = k or k = 1 + 2\n".to_string(),
                ),
            ],
            "and the claim leaves out 1, an element of the set the cited membership names",
        ),
        case(
            "a line of ors by inspection that names something the range does not list",
            vec![
                edit(
                    "tests/elaborator/inspection-cases-of-a-range.proof",
                    Some("  then x = 1 or x = 2\n".to_string()),
                    "  then x = 1 or x = 2 or x = 3\n".to_string(),
                ),
                edit(
                    "tests/elaborator/inspection-cases-of-a-range.proof",
                    Some("1.  x = 1 or x = 2\n".to_string()),
                    "1.  x = 1 or x = 2 or x = 3\n".to_string(),
                ),
            ],
            "and 3 is not an element of the set the cited membership names",
        ),
        case(
            "a line of ors by inspection from a range past the cap",
            vec![edit(
                "tests/elaborator/inspection-cases-of-a-range.proof",
                Some("  let x ∈ {1, …, 2}".to_string()),
                "  let x ∈ {1, …, 100}".to_string(),
            )],
            "and inspection lists a range of at most 64 numerals, and the one from 1 to 100 holds 100",
        ),
        // One equation is a line of one, read against a listed set as a
        // line of "or"s is: from x ∈ {3, 4} it leaves out 4.
        case(
            "one equation by inspection from a set of two",
            vec![edit(
                "tests/elaborator/inspection-cases-of-a-range.proof",
                Some("  let x ∈ {3}".to_string()),
                "  let x ∈ {3, 4}".to_string(),
            )],
            "and the claim leaves out 4, an element of the set the cited membership names",
        ),
        // A claim of numerals said to be impossible, given to `inequalities`:
        // a claim arithmetic can work out is arithmetic's, and is refused
        // there.
        case(
            "say a true claim is impossible",
            vec![edit(
                "proofs/wiedijk/reals-uncountable.proof",
                Some("    2.2.  10 divides 1, which is impossible\n          substitute\n            10 divides (t + 1) − t      2.1\n            10 divides 1                algebra\n".to_string()),
                "    2.2.  10 divides 1\n          substitute\n            10 divides (t + 1) − t      2.1\n            10 divides 1                algebra\n\n    2.3.  1 ≤ 10, which is impossible\n          inequalities\n".to_string(),
            )],
            "step 2.3 says 1 ≤ 10 is impossible, and it holds",
        ),
        // A claim holding a square root said to be impossible is worked out
        // by `real arithmetic`, which finds this one true.
        case(
            "say a true claim with a root is impossible",
            vec![edit(
                "tests/elaborator/an-impossible-line-by-algebra.proof",
                Some("    1.1.  √2 − 1 = 0, which is impossible\n".to_string()),
                "    1.1.  (√2)² = 2, which is impossible\n".to_string(),
            )],
            "step 1.1 says (√2)² = 2 is impossible, and it holds",
        ),
        // A claim of `algebra` that is not an identity, and one asking a
        // power past what algebra may multiply out: the checker decides
        // algebra (`check_algebra_holds`).
        case(
            "claim an algebra step the cited lines do not give",
            vec![edit(
                "proofs/wiedijk/geometric-series.proof",
                Some("= (1 − a^(k + 1)·a)/(1 − a)                  algebra".to_string()),
                "= (1 − a^(k + 1)·a)/(1 − a) + 1              algebra".to_string(),
            )],
            "(1 − a^(k + 1))/(1 − a) + a^(k + 1) = (1 − a^(k + 1)·a)/(1 − a) + 1 is not an identity, nor does it follow from what step 1.5 cites",
        ),
        // A bound the cited lines do not give: q ≥ j says j ≤ q, never
        // j < q (`check_inequalities_holds`).
        case(
            "claim an inequalities step the cited lines do not give",
            vec![edit(
                "proofs/hammack/mersenne-prime-exponent.proof",
                Some("    1.13. j ≤ q\n          inequalities, from 1.3\n".to_string()),
                "    1.13. j < q\n          inequalities, from 1.3\n".to_string(),
            )],
            "j < q does not follow from what step 1.13 cites",
        ),
        case(
            "ask algebra to multiply out a power past its cost",
            vec![edit(
                "proofs/wiedijk/geometric-series.proof",
                Some("= (1 − a^(k + 1)·a)/(1 − a)                  algebra".to_string()),
                "= (1 − a^(k + 1)·a)/(1 − a) + (a + 1)^30 − (a + 1)^30    algebra".to_string(),
            )],
            "(a + 1)^30 is a power algebra does not multiply out",
        ),
        // False closed claims, and below them claims with no exact value, on
        // a requires line: the checker works out what `arithmetic` makes of
        // each (`check_arithmetic_holds`).
        case(
            "claim a false numeral fact with a number past one digit",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("                       ≡ 1 (mod 3)        arithmetic\n".to_string()),
                "                       ≡ 1 (mod 3)        arithmetic\n          requires 10 − 1 = 3·4: arithmetic\n".to_string(),
            )],
            "the requires line 10 − 1 = 3·4 of step 1.3 is arithmetic, which is false",
        ),
        case(
            "claim a false numeral fact of digits",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("                       ≡ 1 (mod 3)        arithmetic\n".to_string()),
                "                       ≡ 1 (mod 3)        arithmetic\n          requires 9 = 3·4: arithmetic\n".to_string(),
            )],
            "the requires line 9 = 3·4 of step 1.3 is arithmetic, which is false",
        ),
        case(
            "divide by zero in a numeral fact",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("                       ≡ 1 (mod 3)        arithmetic\n".to_string()),
                "                       ≡ 1 (mod 3)        arithmetic\n          requires 3/0 ∈ ℝ: arithmetic\n".to_string(),
            )],
            "the requires line 3/0 ∈ ℝ of step 1.3 is arithmetic, which divides by zero",
        ),
        case(
            "state a numeral too large to work out",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("                       ≡ 1 (mod 3)        arithmetic\n".to_string()),
                "                       ≡ 1 (mod 3)        arithmetic\n          requires 9^(9^9) ∈ ℕ: arithmetic\n".to_string(),
            )],
            "the requires line 9^(9^9) ∈ ℕ of step 1.3 is arithmetic, which is too large to work out",
        ),
        case(
            "raise a numeral to a power that is not whole",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("                       ≡ 1 (mod 3)        arithmetic\n".to_string()),
                "                       ≡ 1 (mod 3)        arithmetic\n          requires 4^(1/2) ∈ ℕ: arithmetic\n".to_string(),
            )],
            "4^(1/2) ∈ ℕ: 4^(1/2) has an exponent that is not whole, and arithmetic takes a power only with a whole one",
        ),
        case(
            "prove a false numeral fact by arithmetic",
            vec![edit(
                "tests/notations/numbers.proof",
                Some("  then 2³ = 8\n\n1.  2³ = 8\n".to_string()),
                "  then 2³ = 9\n\n1.  2³ = 9\n".to_string(),
            )],
            "step 1 claims 2³ = 9, which is false",
        ),
        // A substitution by a false fact of numerals, 1 + 1 = 3, which the
        // checker works out as `arithmetic` does.
        case(
            "substitute by a false fact of numerals",
            vec![edit(
                "proofs/wiedijk/wilson.proof",
                Some("    substitute 1 + 1 = 2 (arithmetic) into line 2\n".to_string()),
                "    substitute 1 + 1 = 3 (arithmetic) into line 2\n".to_string(),
            )],
            "step 3 takes 1 + 1 = 3 from arithmetic, which is false",
        ),
        // A link naming `arithmetic` for a piece of numerals that is false,
        // 2/1 is not 3, with the claim changed to match: the checker works
        // the piece out as `arithmetic` does.
        case(
            "a chain link whose closed piece is false",
            vec![edit(
                "proofs/wiedijk/triangular-reciprocals.proof",
                Some("    5.1.  Σ(k = 1 to n) 1/T(k) = 2 − 2/(n + 1)\n          calculation\n            Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))    mun:sum-termwise a := 1, b := n, from 1, 2, 4\n                                 = 2 − 2/(n + 1)                      thm:sum-telescopes a := 1, b := n, from 3\n".to_string()),
                "    5.1.  Σ(k = 1 to n) 1/T(k) = 3 − 2/(n + 1)\n          calculation\n            Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))    mun:sum-termwise a := 1, b := n, from 1, 2, 4\n                                 = 2/1 − 2/(n + 1)                    thm:sum-telescopes a := 1, b := n, from 3\n                                 = 3 − 2/(n + 1)                      arithmetic\n".to_string(),
            )],
            "names arithmetic for 2/1 − 2/(n + 1) = 3 − 2/(n + 1), which is false",
        ),
        // Σ(a(k)t + b(k))² is t²Σa(k)² + 2tΣa(k)b(k) + Σb(k)², and with 3t
        // in place of 2t the `algebra` claim is no identity, which the
        // checker finds reading the sums as linear, as the build does.
        case(
            "expand a sum linearly with a wrong coefficient",
            vec![edit(
                "proofs/wiedijk/cauchy-schwarz.proof",
                Some("            t²·(Σ(k = 1 to n) a(k)²) + 2t·".to_string()),
                "            t²·(Σ(k = 1 to n) a(k)²) + 3t·".to_string(),
            )],
            "is not an identity, nor does it follow from what step 1.3 cites",
        ),
        // A `decided` field names a method that decides words.
        case(
            "say a method decides a word that decides none",
            vec![edit(
                "corpus/stdlib/divisibility.records",
                Some("  then        n is even ↔ there is k ∈ ℤ with n = 2k\n  decided     arithmetic, inspection".to_string()),
                "  then        n is even ↔ there is k ∈ ℤ with n = 2k\n  decided     arithmetic, algebra".to_string(),
            )],
            "even says algebra decides it, and algebra decides no word",
        ),
        // The block's last step is the cases step, not the last step of its
        // last case, and it must name what it contradicts.
        case(
            "a contradiction ending in a cases step that names no line",
            vec![edit(
                "tests/elaborator/textbook-exercise-shapes-two.proof",
                Some("          cases, from H2, contradicting S\n".to_string()),
                "          cases, from H2\n".to_string(),
            )],
            "step 1.1 ends a contradiction block and does not say which line it contradicts",
        ),
        case(
            "induct on a letter the statement does not mention",
            vec![edit(
                "proofs/zz/induct-unused.proof",
                None,
                "theorem induct-unused\n  then for all m ∈ ℕ₀, 0 + 0 = 0\n\n1.  For all m ∈ ℕ₀, 0 + 0 = 0.\n    induction on m starting at 0\n\n    base\n    1.1.  0 + 0 = 0\n          arithmetic\n\n    step\n    let m ∈ ℕ₀                                                        (K)\n    assume step 1 is true for m, the induction hypothesis             (IH)\n\n    1.2.  0 + 0 = 0\n          arithmetic\n".to_string(),
            )],
            "step 1 inducts on m, and what it says of every m does not mention m",
        ),
        // An induction proves a statement of every k; a claim about the
        // theorem's own n leaves the step part no letter of the claim's.
        case(
            "an induction whose claim is not said for all",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("1.  For all k ∈ ℕ, S(k) = k(k + 1)/2.".to_string()), "1.  S(n) = n(n + 1)/2".to_string()),
            ],
            "step 1 is an induction whose claim does not say \"for all k ∈ X, …\"",
        ),
        // The letter an induction says it is on is the one its claim binds.
        case(
            "an induction on a letter its claim does not bind",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("    induction on k starting at 1".to_string()), "    induction on j starting at 1".to_string()),
            ],
            "the induction is on j, and its claim is not said for all j",
        ),
        case(
            "justify a requires line by a method that opens a block",
            vec![edit(
                "proofs/zz/requires-block.proof",
                None,
                "theorem requires-block\n  let x ∈ ℝ                                                           (H1)\n  assume x > 1                                                        (H2)\n  then (x·x)/x = x\n\n1.  (x·x)/x = x\n    algebra\n    requires x ≠ 0: cases, from H2\n".to_string(),
            )],
            "the requires line x ≠ 0 of step 1 names cases, which opens a block, and a requires line holds none",
        ),
        case(
            "give arithmetic a requires line with a letter in it",
            vec![edit(
                "proofs/zz/requires-arithmetic.proof",
                None,
                "theorem requires-arithmetic\n  let x ∈ ℝ                                                           (H1)\n  assume x > 1                                                        (H2)\n  then (x·x)/x = x\n\n1.  (x·x)/x = x\n    algebra\n    requires x ≠ 0: arithmetic\n".to_string(),
            )],
            "the requires line x ≠ 0 of step 1 is arithmetic, which is not a fact about numerals alone, and arithmetic decides nothing else",
        ),
        // `arithmetic` takes a power only with a whole exponent, and a
        // principal power is no value of its.
        case(
            "work out a principal power by arithmetic",
            vec![edit(
                "tests/notations/powers.proof",
                Some("  then x^(1/2) = √x\n\n1.  x^(1/2) = √x\n    mun:half-power\n".to_string()),
                "  then 4^(1/2) = 2\n\n1.  4^(1/2) = 2\n    arithmetic\n".to_string(),
            )],
            "4^(1/2) = 2: 4^(1/2) has an exponent that is not whole, and arithmetic takes a power only with a whole one",
        ),
        case(
            "suppose something unrelated to the claim",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("3.  r = 0\n    contradiction\n    suppose r ≠ 0".to_string()), "3.  r = 0\n    contradiction\n    suppose not r ≤ 0".to_string()),
            ],
            "neither expansion of `contradiction` applies",
        ),
        case(
            "end a contradiction block without saying what it contradicts",
            vec![
                edit("proofs/wiedijk/infinitely-many-primes.proof", Some("inequalities, contradicting 5.5\n".to_string()), "inequalities\n".to_string()),
            ],
            "does not say which line it contradicts",
        ),
        case(
            "contradict a line that is not the claim's opposite",
            vec![
                edit("proofs/wiedijk/infinitely-many-primes.proof", Some("inequalities, contradicting 5.5\n".to_string()), "inequalities, contradicting 5.4\n".to_string()),
            ],
            "says it contradicts 5.4, and neither is the other negated",
        ),
        case(
            "give a method that combines letters for a fact of numerals alone",
            vec![
                edit("proofs/wiedijk/pythagorean-triples.proof", Some("    requires 2 ≠ 0: arithmetic\n".to_string()), "    requires 2 ≠ 0: inequalities\n".to_string()),
            ],
            "gives inequalities for 2 ≠ 0, which arithmetic can work out",
        ),
        // A closed claim with a square root that real arithmetic decides
        // cites it, as one of numerals alone cites arithmetic.
        case(
            "give algebra for a closed claim with a square root",
            vec![
                edit("tests/elaborator/real-arithmetic.proof", Some("1.  √2·√2 = 2\n    real arithmetic".to_string()), "1.  √2·√2 = 2\n    algebra".to_string()),
            ],
            "step 1 gives algebra for √2·√2 = 2, which real arithmetic can work out; a claim real arithmetic can work out cites real arithmetic",
        ),
        case(
            "give algebra for a closed fact with a square root on a requires line",
            vec![
                edit("tests/elaborator/real-arithmetic-in-place.proof", Some("    requires √2 − 1 ≠ 0: real arithmetic".to_string()), "    requires √2 − 1 ≠ 0: algebra".to_string()),
            ],
            "the requires line of step 1 gives algebra for √2 − 1 ≠ 0, which real arithmetic can work out; a fact real arithmetic can work out cites real arithmetic",
        ),
        // A false closed claim reached under a supposition is stated only by
        // the line marked impossible; the method that works it out would
        // refuse it, so the message does not send the writer there.
        case(
            "give algebra for a false claim of numerals not marked impossible",
            vec![
                edit("tests/elaborator/an-impossible-line-by-algebra.proof", Some("    1.1.  5 = 0, which is impossible".to_string()), "    1.1.  5 = 0".to_string()),
            ],
            "step 1.1 gives algebra for 5 = 0, which arithmetic finds false; a false claim with no letter is stated only by the last line of a contradiction, marked impossible",
        ),
        case(
            "give algebra for a false claim with a square root not marked impossible",
            vec![
                edit("tests/elaborator/an-impossible-line-by-algebra.proof", Some("    1.1.  √2 − 1 = 0, which is impossible".to_string()), "    1.1.  √2 − 1 = 0".to_string()),
            ],
            "step 1.1 gives algebra for √2 − 1 = 0, which real arithmetic finds false; a false claim with no letter is stated only by the last line of a contradiction, marked impossible",
        ),
        // A claim the cited equations chain to combines nothing, and is
        // `transitivity`'s, or of one line `restate`'s.
        case(
            "give algebra for a chain of two equations",
            vec![edit(
                "tests/stdlib/geometry.proof",
                Some("5.  |AO| = |BO|\n    transitivity, from 1, 2".to_string()),
                "5.  |AO| = |BO|\n    algebra, from 2, 1".to_string(),
            )],
            "step 5 chains the equations it cites, which is `transitivity, from 1, 2`, not algebra",
        ),
        case(
            "give algebra for an equation turned round",
            vec![edit(
                "corpus/stdlib/geometry.proof",
                Some("37. ∠ECA = ∠BAC\n    restate 14".to_string()),
                "37. ∠ECA = ∠BAC\n    algebra, from 14".to_string(),
            )],
            "step 37 says an equation 14 says, which is `restate 14`, not algebra",
        ),
        // An induction over the parts of a set holds of a finite set only,
        // starts at ∅, opens its step with the member it adds, and ends it
        // on the statement at Y ∪ {a}.
        case(
            "induct over the parts of a set not said to be finite",
            vec![edit(
                "tests/elaborator/induction-over-a-set.proof",
                Some("    induction on Y starting at ∅\n    requires X is finite: from H2\n".to_string()),
                "    induction on Y starting at ∅\n".to_string(),
            )],
            "step 1 inducts over the parts of X, which holds of a finite set only; it carries `requires X is finite`",
        ),
        case(
            "induct over the parts of a set from somewhere other than ∅",
            vec![edit(
                "tests/elaborator/induction-over-a-set.proof",
                Some("    induction on Y starting at ∅\n".to_string()),
                "    induction on Y starting at X\n".to_string(),
            )],
            "an induction over the parts of X starts at ∅, and the text says X",
        ),
        // An order set.mm's bounds on π do not reach is not decided, and
        // not false.
        case(
            "ask real arithmetic for an order past the bounds on π",
            vec![edit(
                "tests/elaborator/real-arithmetic-order.proof",
                Some("  then π² < 16\n\n1.  π² < 16\n".to_string()),
                "  then π² < 10\n\n1.  π² < 10\n".to_string(),
            )],
            "is an order that the bounds on π, e and logarithms do not decide; real arithmetic does not decide it",
        ),
        case(
            "ask real arithmetic to decide a word",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("                       ≡ 1 (mod 3)        arithmetic\n".to_string()),
                "                       ≡ 1 (mod 3)        arithmetic\n          requires √9 is prime: real arithmetic\n".to_string(),
            )],
            "is a word prime defines, and real arithmetic decides no word",
        ),
        case(
            "say a step is impossible and contradict a line as well",
            vec![
                edit("proofs/wiedijk/pythagorean-triples.proof", Some("          def:divides d := 2, n := 1, from 9.5\n".to_string()), "          def:divides d := 2, n := 1, from 9.5, contradicting 9.5\n".to_string()),
            ],
            "says it is impossible and contradicts a line",
        ),
        case(
            "say a claim with a letter in it is impossible",
            vec![
                edit("proofs/wiedijk/reals-uncountable.proof", Some("    2.2.  10 divides 1, which is impossible\n".to_string()), "    2.2.  10 divides t, which is impossible\n".to_string()),
            ],
            "says it is impossible and names t",
        ),
        case(
            "contradict a line before the end of the block",
            vec![
                edit("proofs/wiedijk/infinitely-many-primes.proof", Some("mun:divides-one d := p, from 5.4".to_string()), "mun:divides-one d := p, from 5.4, contradicting 5.4".to_string()),
            ],
            "only the last step of a contradiction block, a case or a proof block may do",
        ),
        // `arithmetic` may stand where a closed-numeral fact is used, and only
        // there: an equation with a letter in it gives a reader something to
        // check, and is a numbered step. `SYNTAX.md` has the rule.
        case(
            "take an equation with a letter in it from arithmetic",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("substitute C(m, m + 1)·x^((m + 1) − (m + 1))·y^(m + 1) = 0 (line 12)".to_string()), "substitute C(m, m + 1)·x^((m + 1) − (m + 1))·y^(m + 1) = 0 (arithmetic)".to_string()),
            ],
            "from arithmetic, and it has a letter in it",
        ),
        case(
            "a chain link with a letter in it naming arithmetic",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("= (k + 1)((k + 1) + 1)/2       algebra".to_string()), "= (k + 1)((k + 1) + 1)/2       arithmetic".to_string()),
            ],
            "names arithmetic for",
        ),
        // `membership` claims a term is in a number system and nothing else.
        case(
            "membership named for a claim that is no membership",
            vec![
                edit("proofs/wiedijk/triangular-reciprocals.proof", Some("    def:series-sum L := 2, from 7\n".to_string()), "    membership, from 7\n".to_string()),
            ],
            "names membership for",
        ),
        case(
            "a step that is impossible and not the last of its block",
            vec![
                edit("proofs/wiedijk/reals-uncountable.proof", Some("            10 divides 1                algebra\n".to_string()), "            10 divides 1                algebra\n\n    2.3.  10 divides 1\n          substitute\n            10 divides (t + 1) − t      2.1\n            10 divides 1                algebra\n".to_string()),
            ],
            "step 2.2 says it is impossible, which only the last step",
        ),
        case(
            "contradicting a line that is not in scope",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("inequalities, from 1, contradicting 3.4".to_string()), "inequalities, from 1, contradicting 3.9".to_string()),
            ],
            "contradicts 3.9, which is no line in scope",
        ),
        case(
            "a direction that does not assume a side of the claim",
            vec![
                edit("proofs/wiedijk/pythagorean-triples.proof", Some("assume a² + b² = c²                                                   (D1)".to_string()), "assume a² + b² = c² + 1                                               (D1)".to_string()),
            ],
            "the theorem proves both directions, and direction 1 does not assume the claim's side it starts from",
        ),
        case(
            "algebra giving a claim of numerals alone",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("11. (m + 1) − (m + 1) = 0\n    algebra".to_string()), "11. 2 + 2 = 4\n    algebra".to_string()),
            ],
            "step 11 gives algebra for 2 + 2 = 4, which arithmetic can work out",
        ),
        case(
            "a chain line naming real arithmetic for a change with a letter in it",
            vec![
                edit("tests/elaborator/a-chain-showing-its-work.proof", Some("      x·√4 = x·2     real arithmetic".to_string()), "      x·√4 = 2·x     real arithmetic".to_string()),
            ],
            "which changes something with a letter in it; a link may name real arithmetic where only closed pieces change",
        ),
        case(
            "a chain line of numerals alone naming algebra",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("= 1(1 + 1)/2            arithmetic".to_string()), "= 1(1 + 1)/2            algebra".to_string()),
            ],
            "which arithmetic can work out",
        ),
        case(
            "a chain line whose algebra does not hold",
            vec![
                edit("tests/elaborator/a-chain-showing-its-work.proof", Some("         = 4k² + 4k + 1        algebra".to_string()), "         = 4k² + 4k + 2        algebra".to_string()),
            ],
            "(2k + 1)² = 4k² + 4k + 2 is not an identity",
        ),
        case(
            "two memberships claimed by one membership step",
            vec![
                edit("proofs/hammack/constant-multiple-limit.proof", Some("    4.2.  ε/(|c| + 1) ∈ ℝ\n          membership".to_string()), "    4.2.  ε/(|c| + 1) ∈ ℝ. |c| + 1 ∈ ℝ.\n          membership".to_string()),
            ],
            "step 4.2 claims 2 sentences by membership, which says one term is in a number system; each is a step of its own",
        ),
        // A plain inequalities step adds its lines as they stand; a claim
        // that follows only by another move is told the row it takes.
        case(
            "a disequality from an order in a plain inequalities step",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let P ∈ ℕ    (H1)\n  assume P > 1    (H2)\n  then P ≠ 1\n\n1.  P ≠ 1\n    inequalities, from H2\n".to_string(),
            )],
            "P ≠ 1 follows from an order step 1 cites by a `weakening` row, and a plain inequalities step only adds its lines as they stand",
        ),
        case(
            "a plain inequalities step that follows only by cancelling",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  let y ∈ ℝ    (H2)\n  let a ∈ ℝ    (H3)\n  let c ∈ ℝ    (H4)\n  assume y = x + c    (H5)\n  assume x ≤ 2 − a    (H6)\n  assume c ≤ a − 1    (H7)\n  then y ≤ 1\n\n1.  y ≤ 1\n    inequalities, from H5, H6, H7\n".to_string(),
            )],
            "y ≤ 1 follows from what step 1 cites by a move other than adding its lines as they stand, which is all a plain inequalities step does",
        ),
        case(
            "a false factorial by arithmetic",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  then 4! = 20\n\n1.  4! = 20\n    arithmetic\n".to_string(),
            )],
            "step 1 claims 4! = 20, which is false",
        ),
        // "Which is impossible" says a claim of numerals alone works out
        // false.
        case(
            "say a true claim of numerals is impossible",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  then not x < x\n\n1.  not x < x\n    contradiction\n    suppose x < x    (S)\n\n    1.1.  x − x < 0\n          inequalities\n            x < x          S\n            x − x < 0      adding −x\n\n    1.2.  1 < 2, which is impossible\n          arithmetic\n".to_string(),
            )],
            "step 1.2 says 1 < 2 is impossible, and it holds",
        ),
        // An order between terms with letters is no link arithmetic works
        // out, false or true.
        case(
            "name arithmetic for an order link with letters",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  then x + 2 < x + 1\n\n1.  x + 2 < x + 1\n    calculation\n      x + 2 < x + 1      arithmetic\n".to_string(),
            )],
            "names arithmetic for x + 2 < x + 1, an order of terms with letters in them, which arithmetic does not work out",
        ),
        // y below and above the midpoint at once cannot be, so the block
        // reaches its contradiction from H4 and H5 alone and never uses S:
        // what it shows is that the hypotheses contradict each other.
        case(
            "a contradiction whose block never uses its supposition",
            vec![edit(
                "proofs/wiedijk/refute.proof",
                None,
                "theorem bounds-that-refute-each-other\n  let a ∈ ℝ                                                           (H1)\n  let b ∈ ℝ                                                           (H2)\n  let y ∈ ℝ                                                           (H3)\n  assume y < (a + b)/2                                                (H4)\n  assume (a + b)/2 < y                                                (H5)\n  then b ≤ a\n\n1.  b ≤ a\n    contradiction\n    suppose not (b ≤ a)                                               (S)\n\n    1.1.  y ≤ (a + b)/2\n          inequalities\n            y < (a + b)/2              H4\n            y ≤ (a + b)/2              weakening\n\n    1.2.  not ((a + b)/2 < y)\n          inequalities, from 1.1, contradicting H5\n"
                    .to_string(),
            )],
            "step 1 is a contradiction whose block never uses its supposition S",
        ),
        // A chain's congruence of numerals is worked out like any closed
        // fact: 10 is not 2 more than a multiple of 3.
        case(
            "a congruence link of numerals that does not hold",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("                       ≡ 1 (mod 3)        arithmetic".to_string()),
                "                       ≡ 2 (mod 3)        arithmetic".to_string(),
            )],
            "names arithmetic for 10 ≡ 2 (mod 3), which is false",
        ),
        // Two equations each multiplied by a term is two steps: the proof
        // multiplies each law of sines in a step of its own and joins them by
        // a calculation, and one `algebra` step citing both is refused.
        case(
            "one algebra step multiplying two cited equations",
            in_sines(
                "    calculation\n      |PQ|·|P′R′|·sin(∠PQR) = |PR|·|P′R′|·sin(∠QRP)       9\n                            = |P′Q′|·|PR|·sin(∠PQR)       10",
                "    algebra, from 5, 8",
            ),
            "at most one equation multiplied by a term",
        ),
        // A requires line is read as a step citing what it cites. Citing
        // nothing, it leaves `inequalities` no order to show sin(∠PQR) ≠ 0
        // from: the order is step 12's, and only step 13 cites it.
        case(
            "a requires line its method cannot prove",
            in_sines(
                "    requires sin(∠PQR) ≠ 0: from 13\n",
                "    requires sin(∠PQR) ≠ 0: inequalities\n",
            ),
            "the requires line sin(∠PQR) ≠ 0 of step 14, read as a step citing what it cites: sin(∠PQR) ≠ 0 does not follow from what step 14 cites",
        ),
        // A range is listed only where its ends are integers, and a refusal
        // says so.
        case(
            "ask inspection to list a range whose end is no integer",
            vec![edit(
                "tests/elaborator/inspection-of-a-range-below-zero.proof",
                Some("  assume n ∈ {−1, …, 1}    (H2)\n".to_string()),
                "  assume n ∈ {1/2, …, 1}    (H2)\n".to_string(),
            )],
            "inspection lists a range whose ends work out to integers",
        ),
        // Two memberships joined by "and" are two sentences, as two
        // sentences written apart are.
        case(
            "claim two memberships joined by and in one membership step",
            vec![edit(
                "tests/elaborator/floor-in-a-bound.proof",
                Some("2.  ⌊A⌋ ∈ ℝ\n    membership, from 1\n".to_string()),
                "2.  ⌊A⌋ ∈ ℝ and ⌊A⌋ ∈ ℂ\n    membership, from 1\n".to_string(),
            )],
            "step 2 claims 2 sentences by membership, which says one term is in a number system; each is a step of its own",
        ),
    ]
}
