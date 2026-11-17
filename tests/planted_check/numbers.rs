//! The planted cases about number systems and memberships: what is said once, divisors not zero, domains and codomains, ranges and counts.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
        // A letter of a range not starting at 1 or 0 is said once to be an
        // integer, and its being no zero is not: a divisor's `≠ 0` is written
        // where the page does not say once it is a positive integer.
        case(
            "leave out a divisor's ≠ 0 built from a letter said once",
            vec![edit(
                "proofs/wiedijk/harmonic.proof",
                Some("          requires k ≠ 0: weakening, from 10.2\n".to_string()),
                String::new(),
            )],
            "1/k ∈ ℝ is not built from what step 10.3 cites: nothing says k ≠ 0, which it needs to divide by it",
        ),
        // A membership step builds a typed value from the type it cites,
        // never one merely in scope: H1 types d, and with 16.22 left out the
        // line names nothing saying d(n) is a number.
        case(
            "a membership of a typed value citing nothing",
            vec![edit(
                "proofs/wiedijk/reals-uncountable.proof",
                Some("                    requires d(n) ∈ ℝ: membership, from 16.21\n\n           16.24.4.".to_string()),
                "                    requires d(n) ∈ ℝ: membership\n\n           16.24.4.".to_string(),
            )],
            "d(n) ∈ ℝ is not built from what step 16.24.3 cites: nothing says d(n) ∈ ℝ, which it needs",
        ),
        // Every atom an inequalities step combines is a real number by a
        // line it names: L(p) is, by line 5.2.3, which lines 5.2.1 and
        // 5.2.4 do not say.
        case(
            "an inequalities step combining an atom it names nothing real of",
            vec![edit(
                "proofs/wiedijk/reals-uncountable.proof",
                Some("    5.7.  L(p) ≤ L(p + g)\n          inequalities, from 5.2, 5.4, 5.5\n".to_string()),
                "    5.7.  L(p) ≤ L(p + g)\n          inequalities, from 5.2, 5.5\n".to_string(),
            )],
            "nothing says L(p) ∈ ℝ, which this step needs",
        ),
        // A requires line by a manipulation takes an atom's membership from
        // a requires line above it; with none it is told so, and with one
        // below it is told to move that one above.
        case(
            "leave out the membership a requires-line weakening needs",
            vec![edit(
                "tests/elaborator/a-requires-weakening-with-its-membership.proof",
                Some("    requires √(x + 1) ∈ ℝ: from 2\n    requires √x ∈ ℝ: from 3\n    requires √(x + 1) + √x ≠ 0: weakening, from 8\n".to_string()),
                "    requires √(x + 1) + √x ≠ 0: weakening, from 8\n".to_string(),
            )],
            "nothing says √(x + 1) ∈ ℝ, which this step needs; a requires line by weakening takes a membership from a requires line above it",
        ),
        // A distance between two points is real, said once where the points
        // are introduced (`READERS.md`), so a line writing it does nothing.
        case(
            "write a distance's membership",
            vec![edit(
                "proofs/wiedijk/pythagoras.proof",
                Some("    algebra, from 4, 7, 8\n".to_string()),
                "    algebra, from 4, 7, 8\n    requires |AC| ∈ ℝ: membership\n".to_string(),
            )],
            "the requires line of step 9 says |AC| ∈ ℝ, which the page says once",
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
        case(
            "a membership read into a smaller number system",
            vec![edit(
                "proofs/wiedijk/triangular-reciprocals.proof",
                Some("    let n ∈ ℕ                                                         (K5)\n\n    5.1.  Σ(k = 1 to n) 1/T(k) = 2 − 2/(n + 1)\n          calculation\n            Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))    mun:sum-termwise a := 1, b := n, from 1, 2, 4\n                                 = 2 − 2/(n + 1)                      thm:sum-telescopes a := 1, b := n, from 3\n          requires n + 1 ≥ 1: inequalities, from K5\n".to_string()),
                "    let n ∈ ℝ                                                         (K5)\n\n    5.1.  Σ(k = 1 to n) 1/T(k) = 2 − 2/(n + 1)\n          calculation\n            Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))    mun:sum-termwise a := 1, b := n, from 1, 2, 4\n                                 = 2 − 2/(n + 1)                      thm:sum-telescopes a := 1, b := n, from 3\n".to_string(),
            )],
            "the statement says n ranges over ℕ, and this line puts it in ℝ",
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
        case(
            "cite an item for a function whose let gives it no type, naming no line that does",
            vec![edit(
                "tests/elaborator/a-type-a-line-states.proof",
                Some("    mun:function-value f := F, from H4, H5\n".to_string()),
                "    mun:function-value f := F, from H5\n".to_string(),
            )],
            "step 1 cites mun:function-value, which asks F : A → B, and no line the step names gives F a type; cite the line stating it, or say it in a requires line",
        ),
        case(
            "chain congruences of terms nothing says are integers",
            vec![edit(
                "proofs/zz/congruence-real.proof",
                None,
                "theorem congruence-real\n  let a ∈ ℝ                                                           (H1)\n  let b ∈ ℝ                                                           (H2)\n  let c ∈ ℝ                                                           (H3)\n  assume a ≡ b (mod 3)                                                (H4)\n  assume b ≡ c (mod 3)                                                (H5)\n  then a ≡ c (mod 3)\n\n1.  a ≡ c (mod 3)\n    calculation\n      a ≡ b (mod 3)      H4\n        ≡ c (mod 3)      H5\n".to_string(),
            )],
            "nothing says a ∈ ℤ, which step 1 puts where its notation asks one",
        ),
        // A congruence outside a calculation asks its sides whole as a
        // chain's does (`SYNTAX.md`, a notation's places): a substitution
        // writing a^(p − 1) names the line making p − 1 a whole number.
        case(
            "substitute into a congruence a power nothing says is whole",
            vec![edit(
                "proofs/wiedijk/wilson.proof",
                Some("                    a^(p − 1) ≡ 1 (mod p)      thm:phi-prime, from H2\n                  requires p − 1 ∈ ℕ₀: mun:nat-minus-one n := p\n".to_string()),
                "                    a^(p − 1) ≡ 1 (mod p)      thm:phi-prime, from H2\n".to_string(),
            )],
            "nothing says a^(p − 1) ∈ ℤ, which step 5.7.2 puts where its notation asks one",
        ),
        // "is even" lets its number in ℤ, and a sequence's value is no number
        // by what the page says once.
        case(
            "substitute under \"is even\" a value nothing says is whole",
            vec![edit(
                "proofs/hammack/fibonacci-even-iff-three-divides.proof",
                Some("                  substitute n = 3q + 1 (line 5.14.5) into P1\n                  requires F(3q + 1) ∈ ℤ: from 5.14.7\n".to_string()),
                "                  substitute n = 3q + 1 (line 5.14.5) into P1\n".to_string(),
            )],
            "which step 5.14.8 puts where its notation asks one",
        ),
        // A function's type is a declaration, and a codomain the item names
        // is asked for: ℂ is not inside ℝ.
        case(
            "cite an item for a function declared into a wider codomain",
            vec![edit(
                "tests/elaborator/a-function-type-widened.proof",
                Some("  let t : {1, …, n} → ℕ                                               (H2)\n".to_string()),
                "  let t : {1, …, n} → ℂ                                               (H2)\n".to_string(),
            )],
            "step 1 cites mun:product-real, which asks t : {1, …, n} → ℝ, and t is declared t : {1, …, n} → ℂ, whose values need not be in ℝ",
        ),
        // A function's type is a declaration over its own domain: an item
        // asked over a range the domain does not hold asks the values
        // there, which the build needs and the type does not give.
        case(
            "cite an item over a range a declared function's domain does not hold",
            vec![edit(
                "tests/elaborator/a-function-on-a-longer-range.proof",
                Some("    mun:product-real a := 1, b := m, from H4\n".to_string()),
                "    mun:product-real a := 1, b := m\n".to_string(),
            )],
            "step 1 cites mun:product-real, which asks t : {1, …, m} → ℝ, and t is declared t : {1, …, n} → ℝ, whose domain does not hold {1, …, m}; say its values there in a requires line, for all k ∈ {1, …, m}, t(k) ∈ ℝ, from a line saying them",
        ),
        // A function a `let` declares has a type an item asks where its
        // declared codomain lies inside the one asked (`citing::codomain_reason`).
        case(
            "cite a function declared into a set not inside the codomain asked",
            vec![edit(
                "corpus/stdlib/divisibility.proof",
                Some("  let f : X → X                                                       (H5)".to_string()),
                "  let f : X → ℚ                                                       (H5)".to_string(),
            )],
            "step 2 cites thm:product-congruent-termwise, which asks f : X → ℤ, and f is declared f : X → ℚ, whose values need not be in ℤ",
        ),
        // A divisor of numerals alone is said once to be other than zero
        // only where its value is.
        case(
            "divide by a difference of numerals whose value is zero",
            vec![edit(
                "tests/elaborator/divisors-not-zero-by-their-factors.proof",
                Some("1.  x · ((c − c) / (2 − 5)) = (c − c) / (2 − 5) · x\n".to_string()),
                "1.  x · ((c − c) / (5 − 5)) = (c − c) / (5 − 5) · x\n".to_string(),
            )],
            "nothing says 5 − 5 ≠ 0, which this step needs to divide by it",
        ),
        // An image's points come from a part of the function's domain, and the
        // item asks the step to say it is one.
        case(
            "cite a value in an image with nothing saying the set is in the domain",
            vec![
                edit("proofs/wiedijk/schroeder-bernstein.proof", Some("          mun:value-in-image, from D1, K2\n          requires C ⊆ A: from 2\n".to_string()), "          mun:value-in-image, from D1, K2\n".to_string()),
            ],
            "step 4.2 cites mun:value-in-image, which asks for",
        ),
        // A requires line says what the step's other lines do not: m − k ∈ ℕ₀
        // above already says m − k is real.
        case(
            "repeat a fact a line above already says",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("          requires m − k ∈ ℕ₀: mun:range-difference a := 0, n := m, from J\n\n    8.4.".to_string()), "          requires m − k ∈ ℕ₀: mun:range-difference a := 0, n := m, from J\n          requires m − k ∈ ℝ: membership\n\n    8.4.".to_string()),
            ],
            "the requires line of step 8.3 says m − k ∈ ℝ, which the page says once, where k and m are introduced",
        ),
        case(
            "let a declared letter be in another set",
            vec![
                edit("proofs/wiedijk/triangular-reciprocals.proof", Some("    let ε ∈ ℝ ".to_string()), "    let ε ∈ ℚ ".to_string()),
            ],
            "the statement says ε ranges over ℝ, and this line puts it in ℚ",
        ),
        // A defined function standing alone is read as its rule, so what is
        // said of it and what is said of its values are about one thing; it
        // is still only what the lines say of those values.
        case(
            "say a defined function maps into a set its values were not shown to lie in",
            vec![
                edit("proofs/wiedijk/euler.proof", Some("8.  f : S → S\n".to_string()), "8.  f : S → ℕ\n".to_string()),
            ],
            "step 8 cites mun:function-into, which asks for for all x ∈ S, f(x) ∈ ℕ, and what it cites does not supply it",
        ),
        // A product over a set of anything puts its letter in no number
        // system, so its term is a number by a line saying so, as one over
        // a range is by the range.
        case(
            "split a product over a set of integers without a line saying its members are numbers",
            vec![
                edit("proofs/wiedijk/wilson.proof", Some("mun:product-split, from H1, H2, 1, 2".to_string()), "mun:product-split, from H2, 1, 2".to_string()),
            ],
            "step 21 cites mun:product-split, which asks that every term x is in ℝ, and it is no number by what the page says once",
        ),
        // A function declared on X says nothing of its values on a part of
        // X written as no range or number system: they are said by a line.
        case(
            "multiply out a product over a part of a function's domain without its values there",
            vec![
                edit("tests/elaborator/a-product-over-a-part-of-a-domain.proof", Some("from H3, H5, H6".to_string()), "from H3, H5".to_string()),
            ],
            "asks that every term f(k) is in ℝ, and it is no number by what the page says once",
        ),
        // A range is no number system, and a line putting r in one says
        // nothing past itself (`SYNTAX.md`): that r is whole is
        // `mun:range-integer`, cited.
        case(
            "read a member of a range as an integer without range-integer",
            vec![
                edit("proofs/wiedijk/euler.proof", Some("          requires r ∈ ℤ: mun:range-integer, from 6.1\n".to_string()), String::new()),
            ],
            "step 6.2 cites mun:coprime-product, which asks for r ∈ ℤ",
        ),
        // The edges of the rule that a membership is said once (`READERS.md`).
        // A quotient is in a number system only where its divisor is not
        // zero, and for a letter that is the step's to say: x/y is real only
        // with y ≠ 0 cited.
        case(
            "divide by a letter without saying it is not zero",
            vec![
                edit("proofs/wiedijk/quotient.proof", None, QUOTIENT.replacen("x := x/y, from H3", "x := x/y", 1)),
            ],
            "step 1 cites mun:square-nonneg, which asks for x / y ∈ ℝ",
        ),
        case(
            "a chain line resting on a requires line taken away",
            vec![
                edit("tests/elaborator/a-chain-showing-its-work.proof", Some("    requires b(n) ∈ ℝ: from H2\n".to_string()), String::new()),
            ],
            "nothing says b(n) ∈ ℝ or ∈ ℂ, which this step needs",
        ),
        // The item's `let f : D → E` asks for nothing a line writes, and D
        // is the set the citing proof gives v; 5 ∈ ℕ is no reason 5 is in it.
        case(
            "a function applied outside its domain",
            vec![edit(
                "proofs/wiedijk/outside.proof",
                None,
                "import mundane theorem    stdlib/functions/function-value\n\ntheorem outside\n  let v : {0, …, 1} → ℝ                                               (H1)\n  then v(5) ∈ ℝ\n\n1.  v(5) ∈ ℝ\n    mun:function-value f := v, x := 5\n"
                    .to_string(),
            )],
            "step 1 cites mun:function-value, which asks for 5 ∈ {0, …, 1}",
        ),
        // A term of numerals alone is said once only where arithmetic works
        // it out: 1/(1 − 1) divides by zero, and no line says its divisor
        // is not.
        case(
            "an atom of numerals alone that divides by zero",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  then x·(1/(1 − 1)) = (1/(1 − 1))·x\n\n1.  x·(1/(1 − 1)) = (1/(1 − 1))·x\n    algebra\n".to_string(),
            )],
            "nothing says 1 − 1 ≠ 0, which this step needs to divide by it",
        ),
        // An order of two roots asks each root be real, and the message names
        // that membership, not the one in ℂ an equation would ask.
        case(
            "an order whose atoms no line says are real",
            vec![edit(
                "tests/elaborator/an-atom-not-said-real.proof",
                Some("    requires √A ∈ ℝ: from 1\n    requires √B ∈ ℝ: from 2\n".to_string()),
                String::new(),
            )],
            "nothing says √B ∈ ℝ, which this step needs",
        ),
        // A map is its rule only on its domain: read at x, it asks x is
        // there, which ℝ's x is not said to be for a map on ℕ.
        case(
            "a map read at a value its domain is not said to hold",
            vec![edit(
                "tests/elaborator/a-map-applied.proof",
                Some("  assume (the map sending y ∈ ℝ to y + 1)(x) = 3    (H2)\n".to_string()),
                "  assume (the map sending y ∈ ℕ to y + 1)(x) = 3    (H2)\n".to_string(),
            )],
            "step 1 reads a map at a value, which asks for x ∈ ℕ",
        ),
        // A map given for a function letter has the type the item's let asks
        // where a line says it: what it sends each member to is the step's
        // to say, as the map's domain is not.
        case(
            "a map given for a function letter with no line saying its type",
            vec![edit(
                "tests/elaborator/a-map-applied.proof",
                Some("    requires (the map sending y ∈ ℝ to y + 1) : ℝ → ℝ: mun:function-into, from 1\n".to_string()),
                String::new(),
            )],
            "step 2 cites thm:a-value-assumed, which asks for (the map sending y ∈ ℝ to y + 1) : ℝ → ℝ, and nothing the step names says it; a requires line says it",
        ),
        // Each atom a method combines is real, and the step says so where
        // the atom is not a letter, a numeral or built from them by the
        // operations a membership said once covers: L(p) is a value of a
        // function the proof defines.
        case(
            "leave out the membership of an atom the method combines",
            vec![edit(
                "proofs/wiedijk/reals-uncountable.proof",
                Some("          transitivity, from 5.7, 5.8\n          requires L(p) ∈ ℝ: from 5.4\n".to_string()),
                "          transitivity, from 5.7, 5.8\n".to_string(),
            )],
            "nothing says L(p) ∈ ℝ, which this step needs; transitivity takes a membership from a requires line",
        ),
        // A divisor nothing says is not zero is named as the page writes it.
        case(
            "divide by a term no line says is not zero",
            vec![edit(
                "proofs/wiedijk/mean-value.proof",
                Some("    algebra, from D1, 24\n    requires b − a ≠ 0: weakening, from 1\n".to_string()),
                "    algebra, from D1, 24\n".to_string(),
            )],
            "nothing says b − a ≠ 0, which this step needs to divide by it",
        ),
        // `membership` builds from what the line cites: f(a) is real because
        // a is in f's domain [a, b], which line 2 says and no introducing
        // line says once. H3 says a < b, nothing of where a lies.
        case(
            "membership from a line that says nothing of the atom",
            vec![edit(
                "proofs/wiedijk/mean-value.proof",
                Some("    membership, from H1, H2, H4, 1, 2, 3\n".to_string()),
                "    membership, from H1, H2, H3, H4, 1, 3\n".to_string(),
            )],
            "the reason under let D1 does not show (f(a) − f(b))/(b − a) ∈ ℝ",
        ),
        // Line 4 says s(x) ∈ ℕ₀ of every x ∈ ℚ and is read at the step's
        // member; line 2 says something else of every pair of naturals, and
        // nothing read at a member of anything gives s(x) ∈ ℕ₀.
        case(
            "a requires line citing a line said of every member that does not say the fact",
            vec![edit(
                "proofs/wiedijk/rationals-countable.proof",
                Some("requires s(x) ∈ ℕ₀: from 4".to_string()),
                "requires s(x) ∈ ℕ₀: from 2".to_string(),
            )],
            "from 2 does not reach s(x) ∈ ℕ₀",
        ),
        // A sum's terms are said real at every point by step 2, of k ∈ ℕ, and
        // from 0 the first of them divides by T(0), which step 2 does not
        // speak of.
        case(
            "membership of a sum whose first term divides by zero",
            vec![edit(
                "proofs/wiedijk/triangular-reciprocals.proof",
                Some("                  requires Σ(k = 1 to n) 1/T(k) ∈ ℝ: mun:sum-real a := 1, b := n, from 2\n\n    6.3.".to_string()),
                "                  requires Σ(k = 0 to n) 1/T(k) ∈ ℝ: mun:sum-real a := 0, b := n, from 2\n\n    6.3.".to_string(),
            )],
            "the requires line of step 6.2.10 cites 2, and mun:sum-real asks for nothing it says",
        ),
        // A requires line citing a sum's item is read as a step citing it,
        // on a step citing no item itself: step 16 is a transitivity, and
        // its line saying the harmonic block's sum is real asks the terms
        // 1/k, k in a range from 2^j + 1, at every point.
        case(
            "a requires line on a method step citing a sum's item whose terms nothing says",
            vec![edit(
                "proofs/wiedijk/harmonic.proof",
                Some("    transitivity, from 15, 14, 11\n    requires for all k ∈ {2^j + 1, …, 2^(j + 1)}, 1/k ∈ ℝ: from 10\n".to_string()),
                "    transitivity, from 15, 14, 11\n".to_string(),
            )],
            "the requires line Σ(k = 2^j + 1 to 2^(j + 1)) 1/k ∈ ℝ of step 16 cites mun:sum-real, which asks that every term 1 / k is in ℝ",
        ),
        // A function the proof defines has its type said by a line the step
        // names, as any function's is: t is defined by D1, and its type is
        // step 2's.
        case(
            "cite a sum's item of a defined function no line types",
            vec![edit(
                "proofs/wiedijk/binomial.proof",
                Some("    mun:sum-termwise a := 0, b := m, from 28\n    requires t : {0, …, m} → ℝ: from 2\n".to_string()),
                "    mun:sum-termwise a := 0, b := m, from 28\n".to_string(),
            )],
            "step 29 cites mun:sum-termwise, which asks for t : {0, …, m} → ℝ, and nothing it cites or requires says it",
        ),
        // The same of a requires line citing the item, which sees only what
        // it cites.
        case(
            "a requires line citing a sum's item of a defined function it does not type",
            vec![edit(
                "proofs/wiedijk/binomial.proof",
                Some("(line 15) into line 14\n    requires Σ(k = 0 to m) t(k) ∈ ℝ: from 7\n".to_string()),
                "(line 15) into line 14\n    requires Σ(k = 0 to m) t(k) ∈ ℝ: mun:sum-real a := 0, b := m\n".to_string(),
            )],
            "the requires line of step 16 cites mun:sum-real, which asks for t : {0, …, m} → ℝ, and nothing it cites says it",
        ),
        // A divisor the page says once is a positive integer needs no line
        // saying it is not zero: D1 lets k be a positive integer.
        case(
            "say a divisor the page says once is a positive integer is not zero",
            vec![edit(
                "proofs/wiedijk/pythagorean-triples.proof",
                Some("11. (a/k)² + (b/k)² = (a² + b²)/k²\n    algebra\n".to_string()),
                "11. (a/k)² + (b/k)² = (a² + b²)/k²\n    algebra\n    requires k ≠ 0: inequalities, from D1\n".to_string(),
            )],
            "the requires line of step 11 says k ≠ 0, and the step neither uses nor asks for it",
        ),
        // A function's type gives a value only at a point of its domain, and a
        // requires line rests only on what it names, so a line citing the
        // type alone is reported.
        case(
            "a requires line citing a function's type for a value without the point's domain",
            vec![edit(
                "proofs/wiedijk/cauchy-schwarz.proof",
                Some("requires b(k) ∈ ℝ: from H3, K4".to_string()),
                "requires b(k) ∈ ℝ: from H3".to_string(),
            )],
            "from H3 does not reach b(k) ∈ ℝ",
        ),
        // f(x) ∈ ℝ is H4's to say, and a step that needs it names H4: a
        // function's type is cited for its values, outside a sum's terms.
        case(
            "a function's value from a type the step does not name",
            vec![edit(
                "proofs/wiedijk/mean-value.proof",
                Some("    requires f(x) ∈ ℝ: from H4\n".to_string()),
                String::new(),
            )],
            "is not built from what step 9 cites",
        ),
        // A membership a cited equation would carry names the part of the
        // equation's other side that nothing says, not the term itself.
        case(
            "leave out the type of a value an equation's other side holds",
            vec![edit(
                "tests/elaborator/a-membership-carried-by-an-equation.proof",
                Some("    membership, from H1, H2, H4\n".to_string()),
                "    membership, from H1, H4\n".to_string(),
            )],
            "nothing says b(0) ∈ ℝ, which it needs",
        ),
        // A claim the item concludes from a "there is" whose witness nothing
        // named puts in its set is told which membership is owed.
        case(
            "fold divides from an equation whose witness nothing says is an integer",
            vec![edit(
                "tests/elaborator/a-divides-fold-with-its-witness.proof",
                Some("    def:divides d := 3, n := p² + q², from H2, 1\n".to_string()),
                "    def:divides d := 3, n := p² + q², from 1\n".to_string(),
            )],
            "step 2 reads what def:divides concludes from a \"there is\", and nothing it names says m^2 ∈ ℤ",
        ),
        // Antisymmetry's cited lines are its two orders, so the membership
        // it owes is taken by a requires line, which the message says.
        case(
            "leave out the requires line an antisymmetry step's atom needs",
            vec![edit(
                "proofs/setmm/square-root-positive.proof",
                Some("          antisymmetry, from 2.1, 2.2\n          requires √a ∈ ℝ: from 1\n".to_string()),
                "          antisymmetry, from 2.1, 2.2\n".to_string(),
            )],
            "nothing says √a ∈ ℝ, which this step needs; antisymmetry takes a membership from a requires line",
        ),
        // 2·√a is a number once √a is, so it is √a whose membership is owed.
        case(
            "leave out the line saying a root is real from a bound on its multiple",
            vec![edit(
                "tests/elaborator/textbook-exercise-shapes-two.proof",
                Some("    inequalities, from H3, 1\n".to_string()),
                "    inequalities, from H3\n".to_string(),
            )],
            "nothing says √a ∈ ℝ, which this step needs",
        ),
        // A divisor that nothing says is not zero is named as the page
        // writes it.
        case(
            "leave out that a power to a letter is not zero",
            vec![edit(
                "tests/elaborator/a-power-said-not-zero.proof",
                Some("    requires x^n ≠ 0: weakening, from H4\n".to_string()),
                String::new(),
            )],
            "nothing says x^n ≠ 0, which this step needs to divide by it",
        ),
        // A number the step needs is named in ℝ or ℂ, either of which says
        // it: a root's record gives √A ∈ ℝ and never √A ∈ ℂ.
        case(
            "leave out that a root an order cites through an equation is real",
            vec![edit(
                "tests/elaborator/a-root-said-real.proof",
                Some("    requires √A ∈ ℝ: def:sqrt x := A, from H2\n".to_string()),
                String::new(),
            )],
            "nothing says √A ∈ ℝ, which this step needs",
        ),
        // A quotient is a number once its divisor is not zero, and that is
        // what is named where it is missing.
        case(
            "leave out that a quotient's divisor is not zero",
            vec![edit(
                "tests/elaborator/a-quotient-divisor-said-not-zero.proof",
                Some("    requires 2·d ≠ 0: from 1\n".to_string()),
                String::new(),
            )],
            "nothing says d ≠ 0, which this step needs to divide by it",
        ),
        // A define applied at a sum's index is applied at every number the
        // sum runs over: a sum from 0 of a function on ℕ applies it at 0,
        // which its rule says nothing of.
        case(
            "sum a function on ℕ from 0",
            vec![edit(
                "tests/elaborator/textbook-exercise-shapes.proof",
                Some(
                    "1.  Σ(k = 1 to n) t(k) = Σ(k = 1 to n) (k + 1)\n    algebra, from D1"
                        .to_string(),
                ),
                "1.  Σ(k = 0 to n) t(k) = Σ(k = 0 to n) (k + 1)\n    algebra, from D1"
                    .to_string(),
            )],
            "step 1 applies D1 at k, the index of a sum or a sequence whose range is not inside ℕ",
        ),
        // A negation is not zero by its part, which the step must name: a
        // line in scope saying −x ≠ 0 that the step does not cite says
        // nothing for it.
        case(
            "divide by a negation whose part the step does not name",
            vec![edit(
                "tests/elaborator/divisor-order.proof",
                Some("1.  1/(−x) = −(1/x)\n    algebra, from H2\n".to_string()),
                "1.  1/(−x) = −(1/x)\n    algebra\n".to_string(),
            )],
            "nothing says x ≠ 0, which this step needs to divide by it",
        ),
    ]
}
