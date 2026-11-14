//! Part 2 of 6 of the planted cases, in the order they are run.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
        // The least upper bound is the supremum, which is a number only of a
        // set bounded above, and line 7 is what says S is. Without it cited
        // nothing supplies the hypothesis naming a bound, and the step says
        // which.
        case(
            "obtain the least upper bound without the line bounding the set",
            vec![edit(
                "proofs/wiedijk/intermediate-value.proof",
                Some("obtain c: axi:completeness, from 2, 5, 7".to_string()),
                "obtain c: axi:completeness, from 2, 5".to_string(),
            )],
            "step 8 cites axi:completeness, which asks for there is u ∈ ℝ with u is an upper bound of S, and what it cites does not supply it",
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
        // g(a) is the rule at a only where a is in g's domain [a, b]. That
        // is no number system, so no introducing line says it once, and
        // line 2, which does, is not named.
        case(
            "read a defined function at a value nothing puts in its domain",
            vec![edit(
                "proofs/wiedijk/mean-value.proof",
                Some("    D2, from 2\n".to_string()),
                "    D2\n".to_string(),
            )],
            "step 18 cites D2 at a, so it needs a ∈ [a, b], and nothing it cites or requires says it",
        ),
        // A cited line read through a define is the define's rule at the
        // argument the line writes, and holds only where that argument is in
        // the domain: u ∈ I(k) says u is a size of a run ending at k only
        // for k ∈ {1, …, N}, which K1 says.
        case(
            "read a defined function in a cited line at a value nothing puts in its domain",
            vec![edit(
                "proofs/wiedijk/erdos-szekeres.proof",
                Some("def:set-image, from D4, K1, K5\n".to_string()),
                "def:set-image, from D4, K5\n".to_string(),
            )],
            "step 1.10.1 cites D4 at k, so it needs k ∈ {1, …, N}, and nothing it cites or requires says it",
        ),
        // a ∈ S because S is the points of [a, b] where f is below zero; the
        // item speaks of a set written by its condition, and without the
        // define S is only a name.
        case(
            "membership in a defined set without citing its define",
            vec![edit(
                "proofs/wiedijk/intermediate-value.proof",
                Some("u := a, from D1, H6, 1".to_string()),
                "u := a, from H6, 1".to_string(),
            )],
            "step 2 claims something that def:set-builder does not conclude",
        ),
        // Said of every member, a term's divisor must not be zero for each: k ∈ ℤ
        // gives no k ≠ 0.
        case(
            "membership said of every integer where a divisor may be zero",
            vec![edit(
                "proofs/wiedijk/triangular-reciprocals.proof",
                Some("requires for all k ∈ ℕ, 1/T(k) ∈ ℝ: from 2".to_string()),
                "requires for all k ∈ ℤ, 1/T(k) ∈ ℝ: membership, from D1".to_string(),
            )],
            "the requires line for all k ∈ ℤ, 1/T(k) ∈ ℝ of step 8 cites D1 at k, so it needs k ∈ ℕ, and nothing it cites or the requires lines above it say it",
        ),
        // A membership line says what the table in `rules` says it does and
        // nothing more: k ∈ ℤ gives no k ≠ 0, and n ∈ ℝ gives no n ∈ ℤ, since
        // the table goes one way. A membership said once is carried up the
        // same table and never down: with n let into ℝ, nothing gives the
        // n ∈ ℤ that sum-telescopes asks of its range's end. Its bound line
        // goes too, as n ∈ ℝ gives no n + 1 ≥ 1 either, and would be reported
        // first. sum-termwise asks the same of its b := n, so step 2.1 is
        // where the citation is first refused.
        case(
            "a membership read for a bound it does not give",
            vec![edit(
                "proofs/wiedijk/triangular-reciprocals.proof",
                Some("    let k ∈ ℕ                                                         (K1)".to_string()),
                "    let k ∈ ℤ                                                         (K1)".to_string(),
            )],
            "step 1.1 cites D1 at k, so it needs k ∈ ℕ, and nothing it cites or requires says it",
        ),
        // A define a file writes outside its theorems is read whether or not
        // a theorem uses it.
        case(
            "a file's define whose rule does not read",
            vec![edit(
                "tests/planted-file-define.proof",
                None,
                "define T(k) := k + + 1, for k ∈ ℕ                                    (D1)\n       reads one more than k\n\ntheorem planted-file-define\n  then 1 = 1\n\n1.  1 = 1\n    arithmetic\n".to_string(),
            )],
            "define D1: 'k + + 1' has 3 token(s) left over",
        ),
        // Outside the theorems no `let` introduces a letter, so a define
        // there writes only its arguments and what is given above it.
        case(
            "a file's define whose domain names a letter nothing gives",
            vec![edit(
                "tests/planted-file-define.proof",
                None,
                "define T(k) := k + 1, for k ∈ {1, …, N}                              (D1)\n       reads one more than k\n\ntheorem planted-file-define\n  then 1 = 1\n\n1.  1 = 1\n    arithmetic\n".to_string(),
            )],
            "define D1 writes N, which neither its arguments nor an import or a define above it gives",
        ),
        case(
            "a membership read into a smaller number system",
            vec![edit(
                "proofs/wiedijk/triangular-reciprocals.proof",
                Some("    let n ∈ ℕ                                                         (K5)\n\n    5.1.  Σ(k = 1 to n) 1/T(k) = 2 − 2/(n + 1)\n          calculation\n            Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))    mun:sum-termwise a := 1, b := n, from 1, 2, 4\n                                 = 2 − 2/(n + 1)                      thm:sum-telescopes a := 1, b := n, from 3\n          requires n + 1 ≥ 1: inequalities, from K5\n".to_string()),
                "    let n ∈ ℝ                                                         (K5)\n\n    5.1.  Σ(k = 1 to n) 1/T(k) = 2 − 2/(n + 1)\n          calculation\n            Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))    mun:sum-termwise a := 1, b := n, from 1, 2, 4\n                                 = 2 − 2/(n + 1)                      thm:sum-telescopes a := 1, b := n, from 3\n".to_string(),
            )],
            "the statement says n ranges over ℕ, and this line puts it in ℝ",
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
        // sum-divisible asks that 3 divide each term, and line 1 says it for
        // all k ∈ ℕ₀. Without line 1 cited nothing says it.
        case(
            "sum what no cited line says each term of is divisible",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("    mun:sum-divisible m := 3, from 1\n".to_string()),
                "    mun:sum-divisible m := 3\n".to_string(),
            )],
            "step 2 cites mun:sum-divisible, which asks for for all a ∈ ℕ₀, 3 divides d(a) · 10^a − d(a), and what it cites does not supply it",
        ),
        // A link of a calculation is what the line it cites says, and a line
        // saying something else is not taken for it.
        case(
            "cite a line for a link it does not say",
            vec![edit(
                "proofs/wiedijk/pythagoras.proof",
                Some("      ∠ADC = 90°        1\n".to_string()),
                "      ∠ADC = 90°        2\n".to_string(),
            )],
            "a link of step 3 cites 2, which does not say ∠ADC = 90°; a link cites the line that states it, and a substitution is a step of its own",
        ),
        // What says f is continuous is H5. Without it cited, the step unfolds
        // a continuity nothing it names says.
        case(
            "unfold continuity without the line saying f is continuous",
            vec![edit(
                "proofs/wiedijk/intermediate-value.proof",
                Some("    def:continuous-on, from H5".to_string()),
                "    def:continuous-on".to_string(),
            )],
            "step 15 claims something that def:continuous-on does not conclude",
        ),
        // The item asks |X| = k + 1, which C2 says. Without C2 cited, the
        // equation is in scope and not in hand, and the hypothesis must go
        // unanswered rather than be answered by a line the step does not name.
        // C2 is also what binds the item's k, so k ∈ ℕ₀ goes unanswered with
        // it: the item's letter is not the proof's k said once by K2.
        case(
            "answer a side condition by an equation the step does not cite",
            vec![edit(
                "proofs/wiedijk/subsets.proof",
                Some("obtain a: mun:card-nonempty, from C2\n".to_string()),
                "obtain a: mun:card-nonempty\n".to_string(),
            )],
            "step 1.6 cites mun:card-nonempty, which asks for k ∈ ℕ₀; |X| = k + 1, and what it cites does not supply them",
        ),
        // What is put in an image comes from a cited line saying where the
        // map is read. With the line gone nothing says it.
        case(
            "put something in an image without the line saying where it comes from",
            vec![edit(
                "proofs/wiedijk/subsets.proof",
                Some("s := V ∖ {a},\n                    from 1.3.2".to_string()),
                "s := V ∖ {a}".to_string(),
            )],
            "step 1.3.3 cites mun:added-element-in-image, which asks for V ∖ {a} ∈ 𝒫(X ∖ {a}), and what it cites does not supply it",
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
        // A closed exponent that comes to −1, which is not in ℕ₀. The checker
        // does not work the exponent out: the link by mun:sum-single between
        // the two changed terms passes, and the link above them, which puts
        // C(0, 0) = 1 for one side, is reported for what it no longer makes.
        case(
            "a closed exponent that is not a whole number",
            vec![edit(
                "proofs/wiedijk/binomial.proof",
                Some("                      = C(0, 0)·x^0·y^0                          substitute line 1.1\n                      = Σ(k = 0 to 0) C(0, k)·x^(0 − k)·y^k      mun:sum-single a := 0\n".to_string()),
                "                      = C(0, 0)·x^((0 − 1) − 0)·y^0              substitute line 1.1\n                      = Σ(k = 0 to 0) C(0, k)·x^((0 − 1) − k)·y^k      mun:sum-single a := 0\n".to_string(),
            )],
            "x^0 · y^0 = C(0, 0) · x^(0 − 1 − 0) · y^0 is not one side of an equation 1.1 says put for the other",
        ),
        // A link reads its cited equation from either side, and nothing on the
        // page says which: line 3 says ∠ADC = ∠ACB, which is neither way round
        // the link's 90° = ∠ACB.
        case(
            "cite an equation that says the link neither way round",
            vec![edit(
                "proofs/wiedijk/pythagoras.proof",
                Some("      ∠BDC = 90°        1\n           = ∠ACB       H5\n".to_string()),
                "      ∠BDC = 90°        1\n           = ∠ACB       3\n".to_string(),
            )],
            "a link of step 6 cites 3, which does not say 90° = ∠ACB; a link cites the line that states it, and a substitution is a step of its own",
        ),
        // A claim of u = a where the item says u ≠ a is not what it says.
        case(
            "claim what a lemma says with one relation changed",
            vec![edit(
                "tests/stdlib/sets.proof",
                Some("then u ∈ Y ∖ {a} ↔ u ∈ Y and u ≠ a\n\n1.  u ∈ Y ∖ {a} ↔ u ∈ Y and u ≠ a\n".to_string()),
                "then u ∈ Y ∖ {a} ↔ u ∈ Y and u = a\n\n1.  u ∈ Y ∖ {a} ↔ u ∈ Y and u = a\n".to_string(),
            )],
            "step 1 claims something that mun:sets-remove-member does not conclude",
        ),
        // A step citing a define by cases takes the case from a line it cites.
        // Here the only line cited says x ∈ A, which is h's domain and no case.
        case(
            "cite a define by cases from a line that does not say the case",
            vec![edit(
                "proofs/wiedijk/schroeder-bernstein.proof",
                Some("                  D2, from 8.2.1\n".to_string()),
                "                  D2, from 8.2.2\n".to_string(),
            )],
            "step 8.2.3 cites D2 and claims a value it does not give: no line it cites says whether a case's condition holds or fails",
        ),
        // An obtain from part-builder claims what K's condition says of the set
        // the cited line puts in K: K2 gives Y = aH, and Z = aH is another
        // claim.
        case(
            "obtain from part-builder a claim the condition does not give",
            vec![edit(
                "proofs/wiedijk/lagrange.proof",
                Some("    8.1.  a ∈ G. Y = aH.\n".to_string()),
                "    8.1.  a ∈ G. Z = aH.\n".to_string(),
            )],
            "step 8.4 takes Y = aH from 8.1, which does not say it",
        ),
        // An obtain from a definition reads its left side off a line it cites,
        // through a define's name where the line uses one: C9 says b ∈ R, and R
        // is f[C]. K7 says only that b is in B.
        case(
            "obtain from a definition citing no line that says its left side",
            vec![edit(
                "proofs/wiedijk/schroeder-bernstein.proof",
                Some("obtain x: def:image u := b, Y := C, from C9, D1".to_string()),
                "obtain x: def:image u := b, Y := C, from D1, K7".to_string(),
            )],
            "step 8.2.1 obtains from def:image, which says there is one only from something the step does not cite",
        ),
        // g ∈ gH is shown by the member of H that g is g times, and the line
        // saying g·e = g is what names it.
        case(
            "a coset member with no line naming what it is the element times",
            vec![edit(
                "proofs/wiedijk/lagrange.proof",
                Some("def:coset u := g, from H2, H3, 1, 2".to_string()),
                "def:coset u := g, from H2, H3, 1".to_string(),
            )],
            "step 3 claims something that def:coset does not conclude",
        ),
        // `inequalities` takes two terms differing only from a line it cites,
        // and not from a requires line above: 0 ≤ r alone gives no 0 < r.
        case(
            "rest an inequalities line on r ≠ 0 above it instead of citing it",
            vec![edit(
                "proofs/wiedijk/bezout.proof",
                Some("          requires 0 < r: inequalities, from S, 1\n".to_string()),
                "          requires r ≠ 0: from S\n          requires 0 < r: inequalities, from 1\n".to_string(),
            )],
            "the requires line of step 3.1 says r ≠ 0, and neither mun:pos-int-nat nor the step's other lines ask for it",
        ),
        // A method decides a word only where the word's record names it
        // (`DATABASE.md`, `decided`). With `inspection` struck from the
        // record of `odd`, Königsberg's count of its odd vertices asks it to
        // decide "is odd", which no line the count cites says.
        case(
            "a parity inspection decides with its record not naming it",
            vec![edit(
                "corpus/stdlib/divisibility.records",
                Some("  then        n is odd ↔ there is k ∈ ℤ with n = 2k + 1\n  decided     arithmetic, inspection".to_string()),
                "  then        n is odd ↔ there is k ∈ ℤ with n = 2k + 1\n  decided     arithmetic".to_string(),
            )],
            "step 6 asks inspection to decide a word odd defines",
        ),
        // A line fills every hypothesis it says, so it is cited once.
        case(
            "cite one line twice in a step's list",
            vec![edit(
                "proofs/wiedijk/sqrt2-irrational.proof",
                Some("thm:divides-gcd a := p, b := q, from 2.1\n".to_string()),
                "thm:divides-gcd a := p, b := q, from 2.1, 2.1\n".to_string(),
            )],
            "step 2.2 cites 2.1 more than once",
        ),
        case(
            "cite one line twice in a requires line's list",
            vec![edit(
                "proofs/wiedijk/mean-value.proof",
                Some(
                    "    requires b − a ≠ 0: weakening, from 1\n    requires f(a) ∈ ℝ: from H4, 2\n    requires f(b) ∈ ℝ: from H4, 3\n\n22."
                        .to_string(),
                ),
                "    requires b − a ≠ 0: weakening, from 1\n    requires f(a) ∈ ℝ: from H4, H4, 2\n    requires f(b) ∈ ℝ: from H4, 3\n\n22."
                    .to_string(),
            )],
            "cites H4 more than once",
        ),
        // Labels come first and then lines, each in order.
        case(
            "cite a list out of order",
            vec![edit(
                "proofs/wiedijk/sqrt2-irrational.proof",
                Some("Q := n is odd, from 1, 2\n".to_string()),
                "Q := n is odd, from 2, 1\n".to_string(),
            )],
            "cites 2, 1 out of order",
        ),
        case(
            "cite a line before a label",
            vec![edit(
                "proofs/wiedijk/bezout.proof",
                Some("algebra, from H9, H10, 1\n".to_string()),
                "algebra, from 1, H9, H10\n".to_string(),
            )],
            "from H9, H10, 1",
        ),
        // A chain's congruence says what it is modulo, on its own line, and
        // every congruence of the chain says the same (`GRAMMAR.md`).
        case(
            "a congruence link that says no modulus",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("                       ≡ 1·10 (mod 3)     thm:congruent-times".to_string()),
                "                       ≡ 1·10     thm:congruent-times".to_string(),
            )],
            "says ≡ and not what modulo",
        ),
        case(
            "two congruence links modulo different numbers",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("                       ≡ 1 (mod 3)        arithmetic".to_string()),
                "                       ≡ 1 (mod 9)        arithmetic".to_string(),
            )],
            "is a congruence modulo 9, and an earlier one modulo 3",
        ),
        case(
            "a congruence and an order in one chain",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("            10^0 = 1              arithmetic".to_string()),
                "            10^0 ≤ 1              arithmetic".to_string(),
            )],
            "joins a congruence with an order",
        ),
        // Once a chain says ≡, it says ≡ to the end: 1·10 = 10 holds, and is
        // written as a congruence after one.
        case(
            "go back to equality after a congruence",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("                       ≡ 10 (mod 3)       arithmetic".to_string()),
                "                       = 10               arithmetic".to_string(),
            )],
            "says = after a congruence",
        ),
        // That 3 is prime holds plainly, and the record of `prime` does not
        // say `arithmetic` decides it.
        case(
            "ask arithmetic to decide a word its record does not name it for",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("                       ≡ 1 (mod 3)        arithmetic\n".to_string()),
                "                       ≡ 1 (mod 3)        arithmetic\n          requires 3 is prime: arithmetic\n".to_string(),
            )],
            "is a word prime defines, and arithmetic decides a word only where its record says so",
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
        // A letter is written only where something introduced it, and a
        // `for all` introduces its letter to the end of its sentence only.
        case(
            "write a for-all's letter in the sentence after it",
            vec![edit(
                "proofs/wiedijk/reals-uncountable.proof",
                Some("4.  For all k ∈ ℕ₀, L(k) ∈ ℝ and U(k) ∈ ℝ and L(k) ≤ U(k).".to_string()),
                "4.  For all k ∈ ℕ₀, L(k) ∈ ℝ. U(k) ∈ ℝ. L(k) ≤ U(k).".to_string(),
            )],
            "k is not introduced here; a `for all` binds its letter only to the end of its sentence",
        ),
        case(
            "write a letter nothing introduces",
            vec![edit(
                "proofs/wiedijk/euler.proof",
                Some("2.  {0, …, n − 1} ⊆ ℤ".to_string()),
                "2.  {0, …, m − 1} ⊆ ℤ".to_string(),
            )],
            "m is not introduced here",
        ),
        // Definitions outside a theorem, and definitions imported.
        case(
            "import a definition from a file that is not there",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/wiedijk/nonesuch/W\n\ntheorem cantor\n".to_string()),
            ],
            "names no proof file",
        ),
        // A step said of every member is the item applied at one: what the
        // item concludes there has to be the claim's body, and what it asks
        // there has to be supplied, by the member's domain or by a line.
        case(
            "say of every member what the item does not conclude at one",
            vec![edit(
                "proofs/wiedijk/cauchy-schwarz.proof",
                Some("2.  For all k ∈ {1, …, n}, a(k)² ≥ 0.".to_string()),
                "2.  For all k ∈ {1, …, n}, a(k)² > 0.".to_string(),
            )],
            "claims something that mun:square-nonneg does not conclude",
        ),
        case(
            "say of every member what the item asks a line for, citing none",
            vec![edit(
                "proofs/wiedijk/cauchy-schwarz.proof",
                Some("    mun:square-nonneg x := a(k), from H2\n".to_string()),
                "    mun:square-nonneg x := a(k)\n".to_string(),
            )],
            "asks for a(k) ∈ ℝ",
        ),
        // A function's type says its value is in the codomain only at a point
        // of its domain, so the line putting k in {1, …, n} is cited with it.
        case(
            "cite a function's type for a value without the point's domain",
            vec![edit(
                "proofs/wiedijk/cauchy-schwarz.proof",
                Some("mun:square-zero x := a(k), from H2, K4, 5.2".to_string()),
                "mun:square-zero x := a(k), from H2, 5.2".to_string(),
            )],
            "asks for a(k) ∈ ℝ",
        ),
        case(
            "import a definition the file does not define",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/wiedijk/tri/W\n\ntheorem cantor\n".to_string()),
            ],
            "defines no W outside its theorems",
        ),
        case(
            "import a definition and never use it",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/wiedijk/tri/T\n\ntheorem cantor\n".to_string()),
            ],
            "imports definition T and never uses it",
        ),
        // Every define is imported as a definition, whether or not it takes
        // an argument.
        case(
            "import a define that takes an argument as a function",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/tri-use.proof", None, "import theorem proofs/wiedijk/tri/tri-one\nimport function proofs/wiedijk/tri/T\n\ntheorem use-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:tri-one\n".to_string()),
            ],
            "import function: an import says the header of the item it names",
        ),
        // An imported define's label is what a line writing it out cites, and
        // is given only where a line does.
        case(
            "label an imported definition no line writes out",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/tri-use.proof", None, "import theorem proofs/wiedijk/tri/tri-one\nimport definition proofs/wiedijk/tri/T (D2)\n\ntheorem use-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:tri-one\n".to_string()),
            ],
            "import definition proofs/wiedijk/tri/T gives the label D2, which no line cites",
        ),
        case(
            "write out an imported definition its import gives no label",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/tri-use.proof", None, "import definition proofs/wiedijk/tri/T\n\ntheorem use-two\n  then T(2) = 3\n\n1.  T(2) = 3\n    calculation\n      T(2) = 2(2 + 1)/2        T\n           = 3                 arithmetic\n".to_string()),
            ],
            "T is the define import definition proofs/wiedijk/tri/T brings in, which a line cites by a label its import gives, as `(D1)`: add one",
        ),
        case(
            "label an imported definition as a theorem labels a line",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/tri-use.proof", None, "import theorem proofs/wiedijk/tri/tri-one\nimport definition proofs/wiedijk/tri/T (H1)\n\ntheorem use-one\n  let n ∈ ℕ                                                           (H1)\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:tri-one\n".to_string()),
            ],
            "label H1 is already a define's outside theorem use-one",
        ),
        // A library function is declared by its record, and nowhere else:
        // give the record another name and gcd is three letters again.
        case(
            "write gcd where the library declares no such function",
            vec![
                edit("corpus/stdlib/divisibility.records", Some("definition gcd\n".to_string()), "definition gcdx\n".to_string()),
            ],
            "'d divides gcd(a, b)' does not read past 'gcd', a word no notation in scope writes",
        ),
        case(
            "let a function of the proof's take a library function's name",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("              gcd(a, b) ≤ d.\n".to_string()), "              gcd(a, b) ≤ d.\n  let gcd : ℕ → ℕ                                                     (H9)\n".to_string()),
            ],
            "gcd is the library's function, def:stdlib/divisibility/gcd, which this file imports; name this function something else",
        ),
        // A file that imports a library function may not give its name to a
        // function of its own; one that does not import it may.
        case(
            "define a function of the proof's with an imported library function's name",
            vec![
                edit("proofs/wiedijk/tri.proof", None, format!("import definition stdlib/counting/C\n\n{}", TRI.replacen("define T(k)", "define C(k)", 1))),
            ],
            "C is the library's function, def:stdlib/counting/C, which this file imports; name this function something else",
        ),
        case(
            "import a function under the name of an imported library function",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition stdlib/counting/C\nimport definition proofs/wiedijk/tri/T as C\n\ntheorem cantor\n".to_string()),
            ],
            "C is the library's function, def:stdlib/counting/C, which this file imports; name this function something else",
        ),
        // A library function is in scope where it is imported, by its name,
        // from the library file that declares it.
        case(
            "apply a library function the file does not import",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("import definition         stdlib/divisibility/gcd\n".to_string()), String::new()),
            ],
            "gcd is the library's function def:stdlib/divisibility/gcd, and this file does not import it: write `import definition stdlib/divisibility/gcd`",
        ),
        case(
            "import a library function from a file that does not declare it",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("import definition         stdlib/divisibility/gcd\n".to_string()), "import definition         stdlib/numbers/gcd\n".to_string()),
            ],
            "import definition stdlib/numbers/gcd: stdlib/numbers holds no item gcd",
        ),
        // A library function is a definition, and a definition is never
        // mundane.
        case(
            "import a library function as mundane",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("import definition         stdlib/divisibility/gcd\n".to_string()), "import mundane definition stdlib/divisibility/gcd\n".to_string()),
            ],
            "import mundane definition stdlib/divisibility/gcd: an axiom or a definition gives meaning, and a pedantic textbook cites it, so it is never mundane; import it as `import definition stdlib/divisibility/gcd`",
        ),
        // An item's name may open with a Greek letter, as σ's does, and is
        // imported from the file that holds it like any other.
        case(
            "import a Greek-named item from a file that does not hold it",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition stdlib/numbers/σ\n\ntheorem cantor\n".to_string()),
            ],
            "import definition stdlib/numbers/σ: stdlib/numbers holds no item σ",
        ),
        case(
            "import a name that is no item's name",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import mundane theorem stdlib/numbers/σ₁\n\ntheorem cantor\n".to_string()),
            ],
            "import mundane theorem stdlib/numbers/σ₁: 'σ₁' is not an item's name",
        ),
        case(
            "import a definition by a subscripted name the file does not define",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/wiedijk/tri/T₁\n\ntheorem cantor\n".to_string()),
            ],
            "defines no T₁ outside its theorems",
        ),
        case(
            "import a library function the file never applies",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition         stdlib/numbers/max\n\ntheorem cantor\n".to_string()),
            ],
            "imports max and never applies it",
        ),
        case(
            "import a library function with a label",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("import definition         stdlib/divisibility/gcd\n".to_string()), "import definition         stdlib/divisibility/gcd (D9)\n".to_string()),
            ],
            "import definition stdlib/divisibility/gcd: only a define of a proof file carries a label",
        ),
        case(
            "import a library function under another name",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("import definition         stdlib/divisibility/gcd\n".to_string()), "import definition         stdlib/divisibility/gcd as hcf\n".to_string()),
            ],
            "a library function is imported by its name alone, with no `as`",
        ),
        case(
            "name a library function with a word a notation writes",
            vec![
                edit("corpus/stdlib/divisibility.records", Some("definition gcd\n".to_string()), "definition divides\n".to_string()),
            ],
            "'divides' is a word a notation writes, so it cannot also name a function",
        ),
        // Every name on the page is a letter, so a longer name is several.
        case(
            "define a function with a name of several letters",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.replacen("define T(k)", "define tri(k)", 1)),
            ],
            "a define names one letter, perhaps with a subscript or a prime, and 'tri' is not one",
        ),
        case(
            "import a definition under a name of several letters",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/wiedijk/tri/T as tri\n\ntheorem cantor\n".to_string()),
            ],
            "a define is imported under one letter, perhaps with a subscript or a prime, and 'tri' is not one",
        ),
        case(
            "define one name twice outside the theorems",
            vec![
                edit("proofs/wiedijk/tri.proof", None, format!("{TRI}{}", "\ndefine T(k) := k, for k ∈ ℕ                                          (D2)\n       reads k itself\n")),
            ],
            "T is already defined at line",
        ),
        case(
            "define a name the file also imports",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/tri-use.proof", None, "import theorem proofs/wiedijk/tri/tri-one\nimport definition proofs/wiedijk/tri/T (D2)\n\ndefine T(k) := k, for k ∈ ℕ                                          (D1)\n       reads k itself\n\ntheorem use-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:tri-one\n".to_string()),
            ],
            "T is already defined at line",
        ),
        // A name one theorem gives is a let, and a name the file gives, which
        // another file may import, is a define (`SYNTAX.md`): each word stands
        // only where its name lives.
        case(
            "write define for a name one theorem gives",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("let B = {x ∈ A : x ∉ f(x)}".to_string()), "define B := {x ∈ A : x ∉ f(x)}".to_string()),
            ],
            "a define inside a theorem",
        ),
        case(
            "write let for a name the file gives",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.replacen("define T(k) := ", "let T(k) = ", 1)),
            ],
            "a let names a thing within a theorem",
        ),
        case(
            "say a let's name is a kind of number no record names",
            vec![
                edit("proofs/wiedijk/pythagorean-triples.proof", Some("let m = gcd(s, w), a positive integer".to_string()), "let m = gcd(s, w), a whole number".to_string()),
            ],
            "and the kinds of number are",
        ),
        case(
            "say what kind of number a let's name is with no reason under it",
            vec![
                edit("proofs/wiedijk/pythagorean-triples.proof", Some("    def:gcd a := s, b := w, from 4, 32\n    reads the number whose square is s".to_string()), "    reads the number whose square is s".to_string()),
            ],
            "the line under it gives no reason",
        ),
        case(
            "give a let a reason that shows another term in the set",
            vec![
                edit("proofs/wiedijk/pythagorean-triples.proof", Some("    def:gcd a := t, b := w, from 4, 29".to_string()), "    def:gcd a := s, b := w, from 4, 32".to_string()),
            ],
            "the reason under let D2 needs gcd(t, w) ∈ ℕ",
        ),
        case(
            "cite in a let's reason a step below the let",
            vec![
                edit("proofs/wiedijk/pythagorean-triples.proof", Some("    def:gcd a := t, b := w, from 4, 29".to_string()), "    def:gcd a := t, b := w, from 29, 55".to_string()),
            ],
            "the reason under let D2 cites 55, which is not above the let",
        ),
        case(
            "say what kind of number a let in a theorem's statement names",
            vec![
                edit("proofs/wiedijk/birthday.proof", Some("  let S = the functions from {1, …, 23} to {1, …, 365}                (D1)\n".to_string()), "  let S = |{1, …, 23}|, a natural number                              (D1)\n    mun:range-size a := 1, b := 23\n".to_string()),
            ],
            "a let in a theorem's statement says no kind of number",
        ),
        case(
            "say what kind of number a define's name is",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.replacen("k(k + 1)/2, for k ∈ ℕ", "1, a natural number", 1).replacen("T(k) :=", "T :=", 1)),
            ],
            "a define says no kind of number",
        ),
        case(
            "a let's function whose kind its reason does not show",
            vec![
                edit("proofs/wiedijk/wilson.proof", Some("membership, from 5.3\n        reads the inverse of a modulo p".to_string()), "membership\n        reads the inverse of a modulo p".to_string()),
            ],
            "the reason under let D1 does not show",
        ),
        case(
            "give a let's name with :=",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("let B = {x ∈ A : x ∉ f(x)}".to_string()), "let B := {x ∈ A : x ∉ f(x)}".to_string()),
            ],
            "a let names with `=`",
        ),
        case(
            "define inside a proof a name the file defines outside it",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "define B := {1}                                                    (D9)\n       reads the set holding 1\n\ntheorem cantor\n".to_string()),
            ],
            "B is already defined outside theorem cantor",
        ),
        case(
            "use a definition above the line that defines it",
            vec![
                edit("proofs/wiedijk/tri.proof", None, "define T(k) := k(k + 1)/2, for k ∈ ℕ                                  (D1)\n       reads the k-th triangular number\n\ntheorem tri-one\n  then T(1) = 1 + U(0)\n\n1.  T(1) = 1\n    calculation\n      T(1) = 1(1 + 1)/2        D1\n           = 1                 arithmetic\n\ndefine U(k) := k, for k ∈ ℕ                                          (D2)\n       reads k itself\n".to_string()),
            ],
            "U is defined at line 12, below theorem tri-one; a definition is used only below where it is written",
        ),
        // A plain name above its define parses, as a letter nobody introduced.
        case(
            "use a plain definition above the line that defines it",
            vec![
                edit("proofs/wiedijk/early.proof", None, "theorem early-use\n  then c = 5\n\n1.  c = 5\n    arithmetic\n\ndefine c := 5                                                         (D1)\n       reads five\n".to_string()),
            ],
            "c is defined at line 7, below theorem early-use",
        ),
        // A cited theorem's T is its own file's T, and a file with a T of its
        // own cannot cite it as one about that.
        case(
            "cite a theorem about another file's T as one about the file's own",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/tri-own.proof", None, "import theorem proofs/wiedijk/tri/tri-one\n\ndefine T(k) := k·k, for k ∈ ℕ                                         (D1)\n       reads the square of k\n\ntheorem own-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:tri-one\n".to_string()),
            ],
            "does not conclude",
        ),
        case(
            "cite a line inside a block that has closed",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("    16.2.  c < b\n           inequalities, from 12, 16.1".to_string()), "    16.2.  c < b\n           inequalities, from 12, 16.1.1".to_string()),
            ],
            "inside a block that has closed",
        ),
        // odd is about n, the proof has N and no n, and the fold from N = 2j + 1
        // gives n no value.
        case(
            "fold a definition about a letter the proof does not have",
            vec![edit(
                "proofs/wiedijk/odd-letter.proof",
                None,
                "import definition         stdlib/divisibility/odd\n\ntheorem odd-letter\n  let N ∈ ℤ            (H1)\n  let j ∈ ℤ            (H2)\n  assume N = 2j + 1    (H3)\n  then N is odd\n\n1.  N is odd\n    def:odd, from H3\n".to_string(),
            )],
            "def:odd is about n, and the step gives n no value and the proof has no n; write it, as n := t",
        ),
        // A mod 1 = A − 1·⌊A/1⌋ with its identity elements dropped is the
        // claim, and dropping 1· asks that ⌊A⌋ be a number, which only the
        // requires line says.
        case(
            "drop an identity element from what no line says is a number",
            vec![edit(
                "tests/elaborator/mod-on-the-reals.proof",
                Some("    requires 1 > 0: arithmetic\n    requires ⌊A⌋ ∈ ℤ: mun:floor-integer x := A\n".to_string()),
                "    requires 1 > 0: arithmetic\n".to_string(),
            )],
            "step 1 drops an identity element from what mun:mod-value concludes, and nothing says ⌊A⌋ is a number; a requires line says it",
        ),
        case(
            "restate a sentence the restated line does not say",
            vec![edit(
                "proofs/wiedijk/euclid.proof",
                Some("    3.3.  a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀\n          join 3.1, 3.2".to_string()),
                "    3.3.  a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀\n          restate 3.1".to_string(),
            )],
            "which no line it restates says",
        ),
        case(
            "join a line the claim says nothing of",
            vec![edit(
                "proofs/wiedijk/euclid.proof",
                Some("    3.3.  a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀\n          join 3.1, 3.2".to_string()),
                "    3.3.  a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀\n          join 1, 3.1, 3.2".to_string(),
            )],
            "step 3.3 joins 1, and claims nothing it says",
        ),
        // A letter introduced in a range is an integer said once, and a line
        // writing it says what the step's other lines already do.
        case(
            "a requires line writing a range member's integrality",
            vec![edit(
                "tests/elaborator/a-range-member-is-cited.proof",
                Some("    algebra\n".to_string()),
                "    algebra\n    requires k ∈ ℤ: membership\n".to_string(),
            )],
            "the requires line of step 1 says k ∈ ℤ, which the page says once, where k is introduced",
        ),
        // No function is typed over {0, …, N}, so H2 is cited for k ∈ ℤ, which
        // the range says once, and C(N, k) being a number asks nothing more.
        case(
            "a step naming a range let only for its integrality",
            vec![edit(
                "tests/elaborator/a-range-member-is-cited.proof",
                Some("    algebra\n".to_string()),
                "    algebra, from H2\n".to_string(),
            )],
            "step 1 cites H2 and uses nothing it says",
        ),
        // A letter introduced in an interval is a real number said once, open
        // or closed, and a line writing or citing it does no work.
        case(
            "a requires line writing an open interval member's realness",
            vec![edit(
                "tests/elaborator/an-interval-member-is-cited.proof",
                Some("  let x ∈ (a, b)    (H3)\n  then x² ≥ 0\n\n1.  x² ≥ 0\n    mun:square-nonneg\n".to_string()),
                "  let x ∈ (a, b)    (H3)\n  then x² ≥ 0\n\n1.  x² ≥ 0\n    mun:square-nonneg\n    requires x ∈ ℝ: from H3\n".to_string(),
            )],
            "the requires line of step 1 says x ∈ ℝ, which the page says once, where x is introduced",
        ),
        case(
            "an item citing a closed interval let only for its member's realness",
            vec![edit(
                "tests/elaborator/an-interval-member-is-cited.proof",
                Some("  let x ∈ [a, b]    (H3)\n  then x² ≥ 0\n\n1.  x² ≥ 0\n    mun:square-nonneg\n".to_string()),
                "  let x ∈ [a, b]    (H3)\n  then x² ≥ 0\n\n1.  x² ≥ 0\n    mun:square-nonneg, from H3\n".to_string(),
            )],
            "step 1 cites H3, and mun:square-nonneg asks for nothing it says",
        ),
        // [a, b] lies in ℝ only where its ends are real, so its member is a
        // real number said once only where they are numbers said once.
        case(
            "a closed interval member whose end is not said real",
            vec![edit(
                "tests/elaborator/an-interval-member-is-cited.proof",
                Some("  let b ∈ ℝ    (H2)\n  let x ∈ [a, b]    (H3)\n  then x² ≥ 0\n".to_string()),
                "  let b ∈ ℂ    (H2)\n  let x ∈ [a, b]    (H3)\n  then x² ≥ 0\n".to_string(),
            )],
            "step 1 cites mun:square-nonneg, which asks for x ∈ ℝ, and what it cites does not supply it",
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
        // A substitution's equation is part of the line it names.
        case(
            "substitute an equation from a line that does not say it",
            vec![edit(
                "tests/notations/integrals.proof",
                Some("    substitute F(1) = 1² (line 9) into line 6\n".to_string()),
                "    substitute F(1) = 1² (line 10) into line 6\n".to_string(),
            )],
            "step 11 takes F(1) = 1² from 10, which does not say it",
        ),
        // A define written in one case is no define of the next.
        case(
            "cite a define written in an earlier case",
            vec![edit(
                "tests/elaborator/textbook-exercise-shapes-two.proof",
                Some("    assume x = 2                                                      (C2)\n\n    1.5.  2 > 0\n          arithmetic\n\n    1.6.  x > 0\n          transitivity, from C2, 1.5\n".to_string()),
                "    assume x = 2                                                      (C2)\n\n    1.5.  y = x\n          D1\n\n    1.6.  2 > 0\n          arithmetic\n\n    1.7.  x > 0\n          transitivity, from C2, 1.6\n".to_string(),
            )],
            "step 1.5 cites D1, which is not in scope here",
        ),
        // What one case shows is no line of the next.
        case(
            "cite a step of an earlier case",
            vec![edit(
                "tests/elaborator/textbook-exercise-shapes-two.proof",
                Some("                  inequalities, from C2\n".to_string()),
                "                  inequalities, from 1.1.1\n".to_string(),
            )],
            "step 1.1.2 cites line 1.1.1, which is in another part of the block",
        ),
        // Step numbers are whole numbers joined by dots.
        case(
            "number a step with a letter",
            vec![edit(
                "tests/elaborator/textbook-exercise-shapes-two.proof",
                Some("2.  a < 2·√a\n".to_string()),
                "2a. a < 2·√a\n".to_string(),
            )],
            "`2a.` is no step number",
        ),
        // The item's domain is a's, {1, …, n}, though the step cites a's type:
        // k ∈ ℤ, said once, does not put k in it.
        case(
            "a function's value cited from its type without the point's line",
            vec![edit(
                "tests/elaborator/a-range-a-function-is-typed-over.proof",
                Some("    mun:function-value f := a, from H3\n".to_string()),
                "    mun:function-value f := a, from H2\n".to_string(),
            )],
            "step 1 cites mun:function-value, which asks for x ∈ {1, …, n}, and what it cites does not supply it",
        ),
        // A letter's membership is said once, so a line naming the let that
        // introduces it, for nothing more, names a line it uses nothing of.
        case(
            "a requires line from a function's type naming the let of its point",
            vec![edit(
                "proofs/wiedijk/reals-uncountable.proof",
                Some("          membership, from 16.3, 16.4\n          requires d(n) ∈ ℤ: from H1\n".to_string()),
                "          membership, from 16.3, 16.4\n          requires d(n) ∈ ℤ: from H1, K6\n".to_string(),
            )],
            "the requires line of step 16.5 cites K6, and d(n) ∈ ℤ needs nothing it says",
        ),
        case(
            "an instantiation naming the let of the letter it puts in",
            vec![edit(
                "tests/notations/calculus.proof",
                Some("                  instantiate x := x in H2\n".to_string()),
                "                  instantiate x := x in H2, from K2\n".to_string(),
            )],
            "step 1.2.1 cites K2, and no value it puts in line H2 needs what it says",
        ),
        case(
            "drop an identity element a substitution makes from what no line says is a number",
            vec![edit(
                "tests/elaborator/an-identity-a-substitution-makes.proof",
                Some("    substitute 1^k = 1 (H3)\n    requires b(0) ∈ ℝ: from H1\n".to_string()),
                "    substitute 1^k = 1 (H3)\n".to_string(),
            )],
            "step 1 drops an identity element from what the substitution makes, and nothing says b(0) is a number; a requires line says it",
        ),
        case(
            "a link dropping an identity element from what no line says is a number",
            vec![edit(
                "tests/elaborator/an-identity-a-link-drops.proof",
                Some("    requires b(k) ∈ ℝ: from H1\n".to_string()),
                String::new(),
            )],
            "a link of step 1 drops an identity element from b(k), which nothing the step names says is a number; a requires line of the step says it",
        ),
        case(
            "cite an item for a function whose let gives it no type, naming no line that does",
            vec![edit(
                "tests/elaborator/a-type-a-line-states.proof",
                Some("    mun:function-value f := F, from H4, H5\n".to_string()),
                "    mun:function-value f := F, from H5\n".to_string(),
            )],
            "step 1 cites mun:function-value, which asks F : A → B, and no line the step names gives F a type; cite the line stating it, or say it in a requires line",
        ),
        // A hypothesis not supplied is said at what the claim fixes, so the
        // instance shows the disjuncts the wrong way round.
        case(
            "cite disjunctive syllogism with its disjuncts the wrong way round",
            vec![edit(
                "proofs/wiedijk/sqrt2-irrational.proof",
                Some("2.  n is even or n is odd\n    mun:even-or-odd\n\n3.  n is even\n    mun:disjunctive-syllogism P := n is even, Q := n is odd, from 1, 2".to_string()),
                "2.  n is odd or n is even\n    mun:even-or-odd\n\n3.  n is even\n    mun:disjunctive-syllogism, from 1, 2".to_string(),
            )],
            "step 3 cites mun:disjunctive-syllogism, which asks for n is even or Q",
        ),
        // A case with no steps says it is the claim; one that does not is
        // reported where it is, not where the step after it lands.
        case(
            "a last case with no steps that does not say it is the claim",
            vec![edit(
                "proofs/euclid/hinge.proof",
                Some("assume B and C are on opposite sides of line AG, which is the claim (C2)".to_string()),
                "assume B and C are on opposite sides of line AG (C2)".to_string(),
            )],
            "this case of step 23 has no steps, and its assumption does not say it is the claim; write its steps, or end the line `, which is the claim`",
        ),
    ]
}
