//! Part 4 of 6 of the planted cases, in the order they are run.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
        // `mod-natural` asks b ∈ ℕ, and IH1 says b(k) ∈ ℕ₀: a function's
        // value is in what a line says it is in, and ℕ₀ holds 0.
        case(
            "supply a hypothesis with the wrong number system",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("mun:mod-natural, from 3.5.8\n".to_string()), "mun:mod-natural, from IH1\n".to_string()),
            ],
            "does not supply",
        ),
        case(
            "stop declaring which pattern is a negation of which",
            vec![
                edit("corpus/db/notation.records", Some("  level       predicate\n  negates     pattern 3 is logical-not of pattern 2".to_string()), "  level       predicate".to_string()),
            ],
            "does not supply",
        ),
        case(
            "drop a hole from the term a notation builds",
            vec![
                edit("corpus/db/notation.records", Some("  metamath-builds _1 _2 caddc co, _1 _2 cmin co".to_string()), "  metamath-builds _1 _1 caddc co, _1 _2 cmin co".to_string()),
            ],
            "leaves a hole out",
        ),
        case(
            "leave a notation without the sort its holes take",
            vec![
                edit("corpus/db/notation.records", Some("  pattern     _ is prime\n  sort        number → formula\n".to_string()), "  pattern     _ is prime\n".to_string()),
            ],
            "notation prime has no `sort` saying what its holes take and what it yields",
        ),
        case(
            "give a notation a sort for more holes than its pattern has",
            vec![
                edit("corpus/db/notation.records", Some("  pattern     _ is prime\n  sort        number → formula\n".to_string()), "  pattern     _ is prime\n  sort        number, number → formula\n".to_string()),
            ],
            "notation prime has a sort for 2 hole(s) but its pattern(s) have [1]",
        ),
        case(
            "write a binder whose binds line does not read",
            vec![
                edit("corpus/db/notation.records", Some("  binds       hole 1 over nothing".to_string()), "  binds       hole 1 above nothing".to_string()),
            ],
            "is not `hole N over hole M`",
        ),
        case(
            "give a notation fewer metamath-builds entries than it has patterns",
            vec![
                edit("corpus/db/notation.records", Some("  metamath-builds _1 _2 cmul co, _1 _2 cdiv co".to_string()), "  metamath-builds _1 _2 cmul co".to_string()),
            ],
            "metamath-builds entr",
        ),
        case(
            "give a notation fewer commutes entries than it has patterns",
            vec![
                edit("corpus/db/notation.records", Some("  commutes    yes, no".to_string()), "  commutes    yes".to_string()),
            ],
            "commutes entr",
        ),
        case(
            "say a notation commutes in a word the field does not have",
            vec![
                edit("corpus/db/notation.records", Some("  sort        α, α → set of α\n  commutes    any order".to_string()), "  sort        α, α → set of α\n  commutes    unordered".to_string()),
            ],
            "where each entry is `yes`, `any order`, `any order of holes I and J` or `no`",
        ),
        case(
            "name a hole in commutes that the pattern does not have",
            vec![
                edit("corpus/db/notation.records", Some("  commutes    any order of holes 1 and 2".to_string()), "  commutes    any order of holes 1 and 4".to_string()),
            ],
            "commutes names hole 4, and the pattern '_ ≡ _ (mod _)' has 3",
        ),
        // A product's two factors may be exchanged (`commutes yes`), and the
        // elaborator carries one order to the other; the page still writes
        // the one the item gives, since `yes` is not `any order`. The item
        // gives n·k, and the step claims k·n.
        case(
            "claim a product with its factors the other way round from the item",
            vec![edit(
                "proofs/wiedijk/product-turned.proof",
                None,
                "import mundane theorem stdlib/divisibility/even-product\n\ntheorem product-turned\n  let k ∈ ℤ                                                           (H1)\n  let n ∈ ℤ                                                           (H2)\n  assume n is even                                                    (H3)\n  then k·n is even\n\n1.  k·n is even\n    mun:even-product a := n, x := k, from H3\n".to_string(),
            )],
            "proofs/wiedijk/product-turned.proof:10  step 1 claims something that mun:even-product does not conclude",
        ),
        // A product over a range is compared as the one over the set of its
        // whole numbers, and only that one: the item split at a := 1 gives
        // the product from 1 to n, and the step claims it from 0.
        case(
            "claim a product over a range the item does not give",
            vec![edit(
                "tests/notations/sums.proof",
                Some("1.  ∏(k = 1 to n + 1) t(k) = (∏(k = 1 to n) t(k))·t(n + 1)\n".to_string()),
                "1.  ∏(k = 1 to n + 1) t(k) = (∏(k ∈ {0, …, n}) t(k))·t(n + 1)\n".to_string(),
            )],
            "step 1 claims something that mun:product-extended does not conclude",
        ),
        // A power whose exponent is whole is the product of copies, which
        // the principal power's item does not conclude.
        case(
            "cite a real power's item for a whole power",
            vec![edit(
                "tests/notations/powers.proof",
                Some("  let y ∈ ℝ                                                           (H3)\n  then x^y > 0\n".to_string()),
                "  let y ∈ ℕ                                                           (H3)\n  then x^y > 0\n".to_string(),
            )],
            "step 1 claims something that mun:real-power-positive does not conclude",
        ),
        // "for all f : X → Y" is said of the functions from X to Y, and a
        // function put for f is one where a line gives it that type.
        case(
            "instantiate a for-all over functions without the function's type",
            vec![edit(
                "tests/notations/for-all-functions.proof",
                Some("    instantiate f := g in line 1, from H4\n".to_string()),
                "    instantiate f := g in line 1\n".to_string(),
            )],
            "step 2 puts g for f in line 1, so it needs g ∈ (the functions from X to Y), and nothing it cites or requires says it",
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
        // √ is the square root, and a raised index before it is 3 or more.
        case(
            "write a root of index 2",
            vec![edit(
                "tests/notations/powers.proof",
                Some("  then x^(1/2) = √x\n\n1.  x^(1/2) = √x\n".to_string()),
                "  then x^(1/2) = ²√x\n\n1.  x^(1/2) = ²√x\n".to_string(),
            )],
            "a root's index is 3 or more, and this one is 2",
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
        // The same of a sum: the item gives a·x + b·y.
        case(
            "claim a sum with its terms the other way round from the item",
            vec![edit(
                "proofs/wiedijk/sum-turned.proof",
                None,
                "import mundane theorem stdlib/divisibility/divides-combination\n\ntheorem sum-turned\n  let e ∈ ℤ                                                           (H1)\n  let a ∈ ℤ                                                           (H2)\n  let b ∈ ℤ                                                           (H3)\n  let x ∈ ℤ                                                           (H4)\n  let y ∈ ℤ                                                           (H5)\n  assume e divides a                                                  (H6)\n  assume e divides b                                                  (H7)\n  then e divides b·y + a·x\n\n1.  e divides b·y + a·x\n    mun:divides-combination e := e, a := a, b := b, x := x, y := y, from H6, H7\n".to_string(),
            )],
            "proofs/wiedijk/sum-turned.proof:14  step 1 claims something that mun:divides-combination does not conclude",
        ),
        case(
            "point a requires line at an item that does not cover it",
            vec![
                edit("tests/elaborator/a-root-said-real.proof", Some("theorem a-root-said-real\n".to_string()), "import mundane theorem stdlib/numbers/square-nonneg\n\ntheorem a-root-said-real\n".to_string()),
                edit("tests/elaborator/a-root-said-real.proof", Some("    requires √A ∈ ℝ: def:sqrt x := A, from H2".to_string()), "    requires √A ∈ ℝ: mun:square-nonneg x := A".to_string()),
            ],
            "does not conclude",
        ),
        // `requires √A ∈ ℝ: def:sqrt x := A, from H2` rests on A ≥ 0, which
        // H2 says.
        case(
            "drop the dull fact a requires line leans on",
            vec![
                edit("tests/elaborator/a-root-said-real.proof", Some("    requires √A ∈ ℝ: def:sqrt x := A, from H2".to_string()), "    requires √A ∈ ℝ: def:sqrt x := A".to_string()),
            ],
            "the requires line of step 3 cites def:sqrt, which asks for 0 ≤ A, and what it cites does not supply it",
        ),
        case(
            "claim something the cited item does not conclude",
            vec![
                edit("proofs/wiedijk/infinitely-many-primes.proof", Some("4.  p > 1\n    def:prime, from 3".to_string()), "4.  p > 2\n    def:prime, from 3".to_string()),
            ],
            "does not conclude",
        ),
        case(
            "stop declaring that juxtaposition is the product",
            vec![
                edit("corpus/db/notation.records", Some("  assoc       left\n  spells      multiplicative ·".to_string()), "  assoc       left".to_string()),
            ],
            "does not conclude",
        ),
        case(
            "stop saying which variable the braces bind",
            vec![
                edit("corpus/stdlib/sets.records", Some("  then        u ∈ {t ∈ X : P(t)} ↔ u ∈ X and P(u)".to_string()), "  then        t ∈ {t ∈ X : P(t)} ↔ t ∈ X and P(t)".to_string()),
            ],
            "does not conclude",
        ),
        case(
            "say a property is a function into a formula",
            vec![
                edit("corpus/stdlib/sets.records", Some("mundane theorem set-builder-subset\n  let X be a set                                                      (H1)\n  let P be a property of the elements of X                            (H2)".to_string()), "mundane theorem set-builder-subset\n  let X be a set                                                      (H1)\n  let P : X → formula                                                 (H2)".to_string()),
            ],
            "which is a sort and not a set",
        ),
        // A define with an argument is a function, and a function is defined
        // somewhere: its rule alone says what it does and not where.
        case(
            "define a function and give no domain",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("let B = {x ∈ A : x ∉ f(x)}".to_string()), "let B(y) = {x ∈ A : x ∉ f(x)}".to_string()),
            ],
            "says no domain",
        ),
        // S is defined on ℕ, so what it is applied to is a number.
        case(
            "apply a defined function outside its domain's sort",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("    1.1.  S(1) = 1(1 + 1)/2".to_string()), "    1.1.  S({1}) = 1(1 + 1)/2".to_string()),
            ],
            "a set of numbers where a number is wanted",
        ),
        case(
            "give a domain to a define that takes no argument",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("let B = {x ∈ A : x ∉ f(x)}".to_string()), "let B = {x ∈ A : x ∉ f(x)}, for y ∈ A".to_string()),
            ],
            "gives a domain and takes no argument",
        ),
        case(
            "define a name and never say what it means",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("       reads the members of A that their own image leaves out\n".to_string()), "".to_string()),
            ],
            "carries no `reads` line",
        ),
        case(
            "note a step that opens no block",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("1.  B ⊆ A\n    mun:set-builder-subset, from D1".to_string()), "1.  B ⊆ A\n    mun:set-builder-subset, from D1\n    note this is where B becomes a part".to_string()),
            ],
            "opens no block",
        ),
        // An item's summand is whatever the sum it concludes sums, read where the
        // sum applies it to what it binds, and every other use of it must agree.
        case(
            "sum over a range the item does not conclude",
            vec![
                edit("proofs/wiedijk/divisibility-by-three.proof", Some("2.  3 divides Σ(k = 0 to n) (d(k)·10^k − d(k))".to_string()), "2.  3 divides Σ(k = 1 to n) (d(k)·10^k − d(k))".to_string()),
            ],
            "step 2 claims something that mun:sum-divisible does not conclude",
        ),
        case(
            "read an item's summand two ways",
            vec![
                edit("proofs/wiedijk/divisibility-by-three.proof", Some("      3 divides Σ(k = 0 to n) d(k)·10^k − Σ(k = 0 to n) d(k)      mun:sum-difference".to_string()), "      3 divides Σ(k = 0 to n) d(k) − Σ(k = 0 to n) d(k)      mun:sum-difference".to_string()),
            ],
            "step 3 claims something that mun:sum-difference does not conclude",
        ),
        // A congruence's two sides stand in no order, and its modulus where
        // it is written.
        case(
            "claim a congruence modulo another number",
            vec![
                edit("proofs/wiedijk/divisibility-by-three.proof", Some("    1.1.  10^k ≡ 1 (mod 3)\n          thm:ten-power-congruent".to_string()), "    1.1.  10^k ≡ 1 (mod 9)\n          thm:ten-power-congruent".to_string()),
            ],
            "step 1.1 claims something that thm:ten-power-congruent does not conclude",
        ),
        // A "for all" line cited inside a block is read at the block's
        // letter only where the sets are written the same, and only where
        // one block around the step lets a letter of the set.
        case(
            "cite a for-all line inside a block over another set",
            vec![
                edit("tests/elaborator/a-for-all-line-read-in-a-block.proof", Some("  assume for all x ∈ ℤ, x ≡ 1 (mod n)".to_string()), "  assume for all x ∈ ℕ, x ≡ 1 (mod n)".to_string()),
            ],
            "step 1.1 cites thm:congruent-times, which asks for y ≡ 1 (mod n), and what it cites does not supply it",
        ),
        case(
            "cite a for-all line inside two blocks letting letters of its set",
            vec![
                edit("tests/elaborator/a-for-all-line-read-in-a-block.proof", Some("    2.1.  z·1 = z\n          restate 1\n".to_string()), "    2.1.  For all w ∈ ℤ, z·1 = z.\n          proof\n          let w ∈ ℤ                                                   (K3)\n\n          2.1.1.  z·1 = z\n                  restate 1\n\n    2.2.  z·1 = z\n          instantiate w := z in line 2.1\n".to_string()),
            ],
            "step 2.1.1 restates 1 and claims z · 1 = z, which no line it restates says",
        ),
        case(
            "note a case part after its assumption",
            vec![
                edit("proofs/wiedijk/subsets.proof", Some("          note V is a subset without a, with a put back\n          assume a ∈ V                                                (C1)".to_string()), "          assume a ∈ V                                                (C1)\n          note V is a subset without a, with a put back".to_string()),
            ],
            "directly under its marker",
        ),
        case(
            "note a case part twice",
            vec![
                edit("proofs/wiedijk/subsets.proof", Some("          note V is a subset without a, with a put back\n".to_string()), "          note V is a subset without a, with a put back\n          note V holds a\n".to_string()),
            ],
            "already carries a note",
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
        case(
            "add a member to a part of a set from outside the rest",
            vec![edit(
                "tests/elaborator/induction-over-a-set.proof",
                Some("    let a ∈ X ∖ Y                                                     (K2)\n".to_string()),
                "    let a ∈ X                                                         (K2)\n".to_string(),
            )],
            "the step part of step 1 does not open with `let Y ⊆ X`, `assume step 1 is true for Y, the induction hypothesis` and `let a ∈ X ∖ Y`, a the member the step adds, those three lines in that order and no other",
        ),
        case(
            "end an induction over the parts of a set short of Y ∪ {a}",
            vec![edit(
                "tests/elaborator/induction-over-a-set.proof",
                Some("\n    1.5.  ∏(y ∈ Y ∪ {a}) 1 = 1\n          transitivity, from 1.4, IH\n".to_string()),
                String::new(),
            )],
            "step 1.4 ends the step part of step 1, which owes ∏(y ∈ Y ∪ {a}) 1 = 1",
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
        // Real arithmetic takes a root only because the square root's
        // record says it decides it.
        case(
            "a square root real arithmetic takes with its record not naming it",
            vec![
                edit("corpus/db/notation.records", Some("  decided     real arithmetic\n".to_string()), String::new()),
            ],
            "works out square-root, and real arithmetic works out an operation beyond arithmetic's only where the notation's record says so in a `decided` field",
        ),
        case(
            "a logarithm real arithmetic takes with its record not naming it",
            vec![edit(
                "corpus/stdlib/logarithms.records",
                Some("  reads       the natural logarithm of\n  decided     real arithmetic\n".to_string()),
                "  reads       the natural logarithm of\n".to_string(),
            )],
            "works out ln, and real arithmetic works out a function only where its record says so in a `decided` field",
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
        case(
            "say a case is the claim when it is not",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("assume f(c) = 0, which is the claim".to_string()), "assume f(c) = 1, which is the claim".to_string()),
            ],
            "case C2 says it is the claim of step 16, and it is not",
        ),
        case(
            "say a case with steps is the claim",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("assume 0 < f(c)                                                   (C3)".to_string()), "assume 0 < f(c), which is the claim                               (C3)".to_string()),
            ],
            "case C3 is the claim and has steps of its own",
        ),
        case(
            "say a line is the claim outside any cases block",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("    suppose f(x) = B                                                  (S)".to_string()), "    suppose f(x) = B, which is the claim                              (S)".to_string()),
            ],
            "a line saying it is the claim outside any `cases` block",
        ),
        case(
            "write a word predicate under a bare not",
            vec![
                edit("corpus/stdlib/geometry.records", Some("              not (P, Q, R are collinear)".to_string()), "              not P, Q, R are collinear".to_string()),
            ],
            "`not` and `,` are not ordered against each other",
        ),
        case(
            "state an item in a notation nobody declared",
            vec![
                edit("corpus/stdlib/sets.records", Some("mundane theorem subset-transitive\n  assume X ⊆ Y".to_string()), "mundane theorem subset-transitive\n  assume X is within Y".to_string()),
            ],
            "mundane theorem subset-transitive",
        ),
        case(
            "leave the name in an item statement with no sort",
            vec![
                edit("corpus/stdlib/sets.records", Some("mundane theorem set-builder-subset\n  let X be a set                                                      (H1)\n  let P be a property of the elements of X                            (H2)".to_string()), "mundane theorem set-builder-subset\n  let X be a set                                                      (H1)".to_string()),
            ],
            "mundane theorem set-builder-subset",
        ),
        case(
            "introduce a symbol and say nothing it stands for",
            vec![
                edit("corpus/stdlib/numbers.records", Some("definition irrational\n  then        x is irrational".to_string()), "definition irrational\n  symbol      irr\n  then        x is irrational".to_string()),
            ],
            "says nothing it stands for",
        ),
        case(
            "define a term and name no symbol for it",
            vec![
                edit("corpus/stdlib/numbers.records", Some("definition irrational\n  then        x is irrational".to_string()), "definition irrational\n  defines     cr cq cdif\n  then        x is irrational".to_string()),
            ],
            "names no symbol for it",
        ),
        case(
            "introduce a symbol nothing writes",
            vec![
                edit("corpus/stdlib/numbers.records", Some("definition irrational\n  then        x is irrational".to_string()), "definition irrational\n  symbol      irr\n  defines     cr cq cdif\n  then        x is irrational".to_string()),
            ],
            "cannot be reached",
        ),
        case(
            "introduce a symbol in more than one token",
            vec![
                edit("corpus/stdlib/numbers.records", Some("definition irrational\n  then        x is irrational".to_string()), "definition irrational\n  symbol      irr ational\n  defines     cr cq cdif\n  then        x is irrational".to_string()),
            ],
            "is not one token",
        ),
        case(
            "introduce one symbol from two definitions",
            vec![
                edit("corpus/stdlib/numbers.records", Some("definition irrational\n  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ".to_string()), "definition irrational\n  symbol      dup\n  defines     cr\n  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ\n\ndefinition twice\n  symbol      dup\n  defines     cq\n  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ".to_string()),
            ],
            "is already introduced by",
        ),
        case(
            "state a field twice, which reads as one field joined",
            vec![
                edit("corpus/stdlib/numbers.records", Some("definition irrational\n  then        x is irrational".to_string()), "definition irrational\n  metamath-proof eldif\n  then        x is irrational".to_string()),
            ],
            "a second time",
        ),
        // A field is read by its name, so a misspelt one is not the field: the
        // Archimedean item would have no metamath-proof, and Theorem 13's
        // citation of it would stop the build.
        case(
            "misspell a field name",
            vec![
                edit("corpus/stdlib/numbers.records", Some("  metamath-proof nnrecl\n".to_string()), "  metamath-prof nnrecl\n".to_string()),
            ],
            "theorem archimedean has a field 'metamath-prof', which a theorem record does not have",
        ),
        // Everything a citation names does work. The requires line says
        // a + b ∈ ℝ, which is what `mun:nonneg-or-neg` asks; H1 says a ∈ ℝ,
        // which it does not.
        case(
            "cite a line the cited item asks nothing of",
            vec![
                edit("proofs/wiedijk/triangle-inequality.proof", Some("    mun:nonneg-or-neg x := a + b\n".to_string()), "    mun:nonneg-or-neg x := a + b, from H1\n".to_string()),
            ],
            "step 1 cites H1, and mun:nonneg-or-neg asks for nothing it says",
        ),
        // A "there is" given by an instance is given only where the instance is
        // in the domain. The mean value theorem's step 26 exhibits c, and
        // without line 22, which says c ∈ (a, b), the witness could be
        // anywhere.
        case(
            "exhibit a witness without saying it is in the domain",
            vec![
                edit("proofs/wiedijk/mean-value.proof", Some("    exhibit, from 22, 25\n".to_string()), "    exhibit, from 25\n".to_string()),
            ],
            "step 26 exhibits c := c, so it needs c ∈ (a, b)",
        ),
        // A requires line rests on the lines above it, read top to bottom
        // (`SYNTAX.md`). Written first, |numer(x)| ∈ ℕ₀ asks for numer(x) ∈ ℤ,
        // which no line above it states.
        case(
            "a requires line resting on one written below it",
            vec![
                edit("proofs/wiedijk/rationals-countable.proof", Some("    membership, from D3\n    requires numer(x) ∈ ℤ: mun:lowest-terms-parts\n".to_string()), "    membership, from D3\n    requires |numer(x)| ∈ ℕ₀: mun:abs-integer z := numer(x)\n    requires numer(x) ∈ ℤ: mun:lowest-terms-parts\n".to_string()),
            ],
            "the requires line of step 5 cites mun:abs-integer, which asks for numer(x) ∈ ℤ, and what it cites does not supply it",
        ),
        // A sort is stated once, like a declared type, and a step does not cite
        // it to rely on it (`READERS.md`): citing one names a line that does no
        // work.
        case(
            "cite the line that says what sort of thing a name is",
            vec![
                edit("proofs/wiedijk/heron.proof", Some("    mun:sin-cos-squares a := ∠BCA\n".to_string()), "    mun:sin-cos-squares a := ∠BCA, from H1\n".to_string()),
            ],
            "step 4 cites H1, and mun:sin-cos-squares asks for nothing it says",
        ),
        // A count step's claim fixes the property it is applied to, and so
        // supplies its hypotheses with no search for them; a line named
        // beside them still has to do work. 1.2.12.3 says c(j, y) is not
        // odd, which count-step-holds does not ask.
        case(
            "cite a line a count step asks nothing of",
            vec![
                edit("tests/elaborator/induction-under-a-condition.proof", Some("mun:count-step-holds k := j, from D1, 1.2.12.7\n".to_string()), "mun:count-step-holds k := j, from D1, 1.2.12.3, 1.2.12.7\n".to_string()),
            ],
            "step 1.2.12.8 cites 1.2.12.3, and mun:count-step-holds asks for nothing it says",
        ),
        // A requires line citing a define is the step it would be, and has
        // each argument in its domain as a step does: c(j, y) is defined for
        // y ∈ V, which 1.2.1 says.
        case(
            "cite a define in a requires line without its argument's domain",
            vec![
                edit("tests/elaborator/induction-under-a-condition.proof", Some("requires c(j, y) ∈ ℕ₀: mun:count-nat0 k := j, from D1, 1.2.1\n".to_string()), "requires c(j, y) ∈ ℕ₀: mun:count-nat0 k := j, from D1\n".to_string()),
            ],
            "cites D1 at y, so it needs y ∈ V, and nothing it cites or the requires lines above it say it",
        ),
        // An obtain names its item after the word `obtain`, and the checks that
        // read an item citation read only a step the item heads. The three
        // below went unreported.
        case(
            "obtain from an item without what it asks for",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("    obtain c: axi:completeness, from 2, 5, 7".to_string()), "    obtain c: axi:completeness, from 5, 7".to_string()),
            ],
            "step 8 cites axi:completeness, which asks for",
        ),
        case(
            "obtain from an item and cite a line it does not ask for",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("    obtain c: axi:completeness, from 2, 5, 7".to_string()), "    obtain c: axi:completeness, from H3, 2, 5, 7".to_string()),
            ],
            "step 8 cites H3, and axi:completeness asks for nothing it says",
        ),
        // An item states what its metamath-proof proves of every value of its
        // names.
        // This one said |X| = k + 1 without saying what k was, and at k = −1
        // and X = ∅ it is false.
        case(
            "leave open a name an item uses as a number",
            vec![
                edit("corpus/stdlib/counting.records", Some("mundane theorem card-nonempty\n  let X be a set                                                      (H1)\n  let k ∈ ℕ₀                                                          (H2)\n".to_string()), "mundane theorem card-nonempty\n  let X be a set                                                      (H1)\n".to_string()),
            ],
            "mundane theorem card-nonempty: k stands where a number goes",
        ),
        // A set's sort says what it holds, and the page never writes it
        // (`READERS.md`); the checker reads it off the text. A sort that said
        // only "a set" would see none of the three below.
        case(
            "put a set of numbers inside a set of sets of numbers",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("3.  S ⊆ [a, b]\n".to_string()), "3.  S ⊆ 𝒫[a, b]\n".to_string()),
            ],
            "𝒫: a set of sets of numbers where a set of numbers is wanted",
        ),
        case(
            "say an element of a set of numbers exists as a set",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("    6.1.  s ∈ [a, b]\n          def:set-builder, from D1, K1\n".to_string()), "    6.1.  s ∈ [a, b]\n          def:set-builder, from D1, K1\n          requires s exists: from K1\n".to_string()),
            ],
            "the requires line of step 6.1: 's exists': s is a number, and `_ exists` wants a set",
        ),
        // A set declared of any sort stays of any sort. `let a be a set` makes
        // add-element-bijection's X a set of sets, and subsets-count, whose X
        // is a set of any sort, cites it: the counting proof would hold of
        // sets of sets only, and nothing would say so.
        // A citation checks what a proof's names are and does not say it:
        // the elaborator reads a proof's sorts from its own lines, so a name
        // only a citation settles would read differently there.
        case(
            "leave a name's sort to a citation",
            vec![
                edit("proofs/wiedijk/cites.proof", None, "import mundane theorem stdlib/numbers/int-real\n\ntheorem only-cited\n  then c = c\n\n1.  c = c\n    mun:int-real m := c\n".to_string()),
            ],
            "citing stdlib/numbers/int-real with m := c: only the citation says c is a number; say so where c is introduced",
        ),
        case(
            "cite a statement that narrows a set of any sort",
            vec![
                edit("proofs/wiedijk/subsets.proof", Some("  let a ∉ X                                                           (H2)\n".to_string()), "  let a ∉ X                                                           (H2)\n  let a be a set                                                      (H3)\n".to_string()),
            ],
            "citing proofs/wiedijk/subsets/add-element-bijection with X := X ∖ {a}: a set of things of any sort (X)",
        ),
        case(
            "obtain from a definition without the line it unfolds",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    obtain k: def:odd, from H2".to_string()), "    obtain k: def:odd".to_string()),
            ],
            "step 1 obtains from def:odd, which says there is one only from",
        ),
        // Pascal's rule pairs C(n, k) with C(n, k − 1). The other neighbour is
        // the mistake a reader makes when the index shift goes the wrong way.
        case(
            "Pascal with the shift going the wrong way",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("    27.3.  C(m, k) + C(m, k − 1) = C(m + 1, k)\n".to_string()), "    27.3.  C(m, k) + C(m, k + 1) = C(m + 1, k)\n".to_string()),
            ],
            "step 27.3 claims something that thm:pascal does not conclude",
        ),
        // Shifting the index moves the range with it.
        case(
            "a shifted sum left over the range it came from",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("= Σ(k = 1 to m + 1) C(m, k − 1)·x^(m − (k − 1))·y^((k − 1) + 1)        mun:sum-shift".to_string()), "= Σ(k = 0 to m) C(m, k − 1)·x^(m − (k − 1))·y^((k − 1) + 1)        mun:sum-shift".to_string()),
            ],
            "step 26 claims something that mun:sum-shift does not conclude",
        ),
        // A line saying something of every index from 0 to m says nothing of
        // the index m + 1, which the sum to m + 1 takes.
        case(
            "a term-by-term line over too short a range",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("mun:sum-termwise a := 0, b := m + 1, from 27\n".to_string()), "mun:sum-termwise a := 0, b := m + 1, from 8\n".to_string()),
            ],
            "step 30 cites mun:sum-termwise, which asks for",
        ),
        // C(n, k) is zero above n, and C(m + 1, m + 1) is not above it.
        case(
            "a coefficient called zero where k is not above n",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("    def:C n := m, k := m + 1, from 9".to_string()), "    def:C n := m + 1, k := m + 1, from 9".to_string()),
            ],
            "step 10 claims something that def:C does not conclude",
        ),
        // Every block of binomial-step fixes k under the label J, and J means
        // what the block around the citing step says: here k runs from 1. Read
        // theorem-wide, J was the last block's, from 0, and this edit passed.
        case(
            "a label read as a sibling block's",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("    20.1.  m − (k − 1) = (m + 1) − k\n           algebra\n".to_string()), "    20.1.  m − (k − 1) = (m + 1) − k\n           algebra\n           requires (m + 1) − k ∈ ℕ₀: mun:range-difference a := 0, n := m + 1, from J\n".to_string()),
            ],
            "the requires line of step 20.1 cites mun:range-difference",
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
        // Steps count 1, 2, 3 in the order they are written: a reader meeting 8
        // after 6 looks for a 7 that is not there.
        case(
            "a gap in the numbering",
            vec![
                edit("proofs/wiedijk/infinitely-many-primes.proof", Some("6.  There exists p ∈ ℕ such that p is prime and p > n.".to_string()), "7.  There exists p ∈ ℕ such that p is prime and p > n.".to_string()),
            ],
            "numbers run on without gaps",
        ),
        // `membership` claims a term is in a number system and nothing else.
        case(
            "membership named for a claim that is no membership",
            vec![
                edit("proofs/wiedijk/triangular-reciprocals.proof", Some("    def:series-sum L := 2, from 7\n".to_string()), "    membership, from 7\n".to_string()),
            ],
            "names membership for",
        ),
        // A line said of every k ∈ ℕ answers a hypothesis over {1, …, n}, and not
        // one over {0, …, n}: the table puts the first range inside ℕ and not
        // the second.
        case(
            "a for-every line over a set that does not hold the range",
            vec![
                edit("proofs/wiedijk/triangular-reciprocals.proof", Some("            Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))    mun:sum-termwise a := 1, b := n, from 1, 2, 4\n".to_string()), "            Σ(k = 0 to n) 1/T(k) = Σ(k = 0 to n) (2/k − 2/(k + 1))    mun:sum-termwise a := 0, b := n, from 1, 2, 4\n".to_string()),
            ],
            "step 5.1 cites mun:sum-termwise, which asks",
        ),
        // What a summand's function hypothesis asks is the membership of the
        // names the summand is built from, and asks nothing of 1 > 0.
        case(
            "a requires line the summand does not ask for",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("    mun:sum-real a := 0, b := m\n    requires t : {0, …, m} → ℝ: from 2\n".to_string()), "    mun:sum-real a := 0, b := m\n    requires t : {0, …, m} → ℝ: from 2\n    requires 1 > 0: arithmetic\n".to_string()),
            ],
            "says 1 > 0, and neither mun:sum-real nor",
        ),
        // A hypothesis asking a = b is answered by a line saying b = a, and by
        // nothing else: line 2 says |CB| = |BC|, which is neither way round the
        // |CB| = |CA| side-angle-side asks for.
        case(
            "answer an equation with one that says it neither way round",
            vec![
                edit("proofs/wiedijk/isosceles.proof", Some("      from H4, H5, 1\n".to_string()), "      from H4, 1\n".to_string()),
            ],
            "step 2 cites axi:side-angle-side, which asks for",
        ),
        // A step citing a define by cases says which case it is in, by a line
        // giving the condition or its negation, and claims that case's value.
        case(
            "cite a define by cases for the other case's value",
            vec![
                edit("proofs/wiedijk/schroeder-bernstein.proof", Some("    3.6.  h(t) = g⁻¹(t)\n".to_string()), "    3.6.  h(t) = f(t)\n".to_string()),
            ],
            "step 3.6 cites D2 and claims a value it does not give",
        ),
        case(
            "cite a define by cases from no line saying the case",
            vec![
                edit("proofs/wiedijk/schroeder-bernstein.proof", Some("          D2, from 3.1\n".to_string()), "          D2, from K1\n".to_string()),
            ],
            "no line it cites says whether a case's condition holds",
        ),
        case(
            "cite a define for a claim that does not name it",
            vec![
                edit("proofs/wiedijk/schroeder-bernstein.proof", Some("    3.6.  h(t) = g⁻¹(t)\n".to_string()), "    3.6.  g⁻¹(t) = g⁻¹(t)\n".to_string()),
            ],
            "step 3.6 cites D2 and its claim never names h",
        ),
        // A defined name is the term it names only where the step cites the
        // define (`SYNTAX.md`). Without D2 cited, x₁ ∈ ℝ is said of x₁, and
        // min-real concludes it only of min(b, c + δ/2).
        case(
            "lean on a define the line does not cite",
            vec![
                edit("proofs/wiedijk/konigsberg.proof", Some("requires S ⊆ {1, …, n}: mun:set-builder-subset, from D1\n".to_string()), "requires S ⊆ {1, …, n}: mun:set-builder-subset\n".to_string()),
            ],
            "the requires line of step 8 needs something that mun:set-builder-subset does not conclude",
        ),
        // So is a define from outside the theorem, here one imported: C(1)
        // is C applied, and tri-one concludes it of T's rule only where the
        // step cites C's define.
        case(
            "lean on an imported define the step does not cite",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit(
                    "proofs/wiedijk/tri-use.proof",
                    None,
                    "import theorem proofs/wiedijk/tri/tri-one\nimport definition proofs/wiedijk/tri/T as C (D1)\n\ntheorem use-one\n  then C(1) = 1\n\n1.  C(1) = 1\n    thm:tri-one\n".to_string(),
                ),
            ],
            "step 1 claims something that thm:tri-one does not conclude",
        ),
        // A `let` names a function's type and nothing more, unless `be` says a
        // property of it; a property slipped in as the codomain went unasked.
        case(
            "state a property in a let line as the codomain",
            vec![
                edit("corpus/stdlib/functions.records", Some("  let g : Y → X be one-to-one ".to_string()), "  let g : Y → X is one-to-one ".to_string()),
            ],
            "says more than a function's type",
        ),
        // What `be` says of a function is asked for, as a membership is.
        case(
            "cite an item without the line saying its function is one-to-one",
            vec![
                edit("proofs/wiedijk/schroeder-bernstein.proof", Some("          mun:inverse-value, from H4, 3.5\n".to_string()), "          mun:inverse-value, from 3.5\n".to_string()),
            ],
            "step 3.7 cites mun:inverse-value, which asks for",
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
        // An obtain states what its name is, and ⊆ says it of a part as ∈ 𝒫
        // would; with neither the name's sort is left to be inferred.
        case(
            "obtain a part without saying what it is a part of",
            vec![
                edit("proofs/wiedijk/schroeder-bernstein.proof", Some("2.  C ⊆ A. g[B ∖ f[C]] = A ∖ C.\n".to_string()), "2.  g[B ∖ f[C]] = A ∖ C.\n".to_string()),
            ],
            "step 2 obtains C without stating its sort",
        ),
        // Two sets sharing nothing keep a member of one out of the other, and
        // the member is asked for: here a is dropped.
        case(
            "keep a point out of a disjoint set without saying it is in the other",
            vec![
                edit("proofs/wiedijk/schroeder-bernstein.proof", Some("                  mun:disjoint-member, from K7, 7.2.2, contradicting 7.2.1\n".to_string()), "                  mun:disjoint-member, from 7.2.2, contradicting 7.2.1\n".to_string()),
            ],
            "step 7.2.3 cites mun:disjoint-member, which asks for",
        ),
        // A group is let with its operation and its identity; one without the
        // identity is no introduction at all.
        case(
            "let a group without naming its identity",
            vec![
                edit("proofs/wiedijk/lagrange.proof", Some("let G be a finite group with operation · and identity e".to_string()), "let G be a finite group with operation ·".to_string()),
            ],
            "is none of the 13 introductions",
        ),
        // gH is read as a coset of a subgroup, and the step cites the line
        // that says H is one.
        case(
            "read a coset without saying H is a subgroup",
            vec![
                edit("proofs/wiedijk/lagrange.proof", Some("    def:coset u := g, from H2, H3, 1, 2\n".to_string()), "    def:coset u := g, from H3, 1, 2\n".to_string()),
            ],
            "step 3 cites def:coset, which asks for H is a subgroup of G",
        ),
        // An equation names a witness read either way round, and only so: g
        // is in gH as g = g·h for some h ∈ H, and e·g = g fits that neither
        // way.
        case(
            "name a coset witness by an equation that does not fit either way",
            vec![
                edit("proofs/wiedijk/lagrange.proof", Some("\n2.  g·e = g\n".to_string()), "\n2.  e·g = g\n".to_string()),
            ],
            "step 3 claims something that def:coset does not conclude",
        ),
        // A claim may bind another letter than the definition it reads, and says
        // the same thing only where the letter it binds is the one it uses: with
        // b bound and a free, gH = aH is a claim about a, and 5.4 reads K's
        // condition from it.
        case(
            "read a definition with a bound letter the claim does not use",
            vec![
                edit("proofs/wiedijk/lagrange.proof", Some("    5.3.  There is a ∈ G with gH = aH.\n".to_string()), "    5.3.  There is b ∈ G with gH = aH.\n".to_string()),
            ],
            "step 5.4 claims something that def:part-builder does not conclude",
        ),
        // K binds g, and read at gH it is `there is a ∈ G with gH = aH`: the g
        // of gH is not caught by K's. So the sentence written with it caught
        // says something else, and does not put gH in K.
        case(
            "read a definition at a term its bound letter would catch",
            vec![
                edit("proofs/wiedijk/lagrange.proof", Some("    5.3.  There is a ∈ G with gH = aH.\n".to_string()), "    5.3.  There is g ∈ G with gH = gH.\n".to_string()),
            ],
            "step 5.4 claims something that def:part-builder does not conclude",
        ),
        // An obtain from part-builder finds its "there is" in the condition of
        // the set the cited line puts Y in; K4 says only x ∈ Y ∩ Z.
        case(
            "obtain from part-builder citing no line that puts the set in it",
            vec![
                edit("proofs/wiedijk/lagrange.proof", Some("obtain a: def:part-builder, from D1, K2".to_string()), "obtain a: def:part-builder, from D1, K4".to_string()),
            ],
            "step 8.1 obtains from def:part-builder, which says there is one only from something the step does not cite",
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
        // A line saying a term is not zero is asked for by a line below that
        // divides by it, and only by such a line: nothing in step 12 divides
        // by b − a.
        case(
            "a term said not zero that nothing below divides by",
            vec![
                edit("proofs/wiedijk/mean-value.proof", Some("    requires F : [a, b] → ℝ: from 10\n    requires g : [a, b] → ℝ: from 8\n".to_string()), "    requires b − a ≠ 0: weakening, from 1\n    requires F : [a, b] → ℝ: from 10\n    requires g : [a, b] → ℝ: from 8\n".to_string()),
            ],
            "the requires line of step 12 says b − a ≠ 0, and neither thm:continuous-sum nor the step's other lines ask for it",
        ),
        // Counting by parts asks that two parts which meet be one part.
        case(
            "count by parts without saying they do not overlap",
            vec![
                edit("proofs/wiedijk/lagrange.proof", Some("from H1, 7, 8, 9".to_string()), "from H1, 7, 9".to_string()),
            ],
            "step 10 cites mun:partition-count, which asks for",
        ),
        // A define by recursion gives each name a value at 0 and a rule at the
        // step, the rule naming the sequences only at k, and a citation of it
        // says which case it is in and that the index is one the rule covers.
        case(
            "define a sequence with no value at 0",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("let a(0) = M,  b(0) = N,".to_string()), "let a(0) = M,".to_string()),
            ],
            "b has no value at 0",
        ),
        case(
            "give a sequence its first value at 1",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("let a(0) = M,  b(0) = N,".to_string()), "let a(0) = M,  b(1) = N,".to_string()),
            ],
            "b(1) is neither b(0) nor b(k + 1)",
        ),
        case(
            "write a step rule that names the value it defines",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("  a(k + 1) = a(k)             if b(k) = 0".to_string()), "  a(k + 1) = a(k + 1)         if b(k) = 0".to_string()),
            ],
            "names a at a place other than k",
        ),
        case(
            "take cases from a disjunction in the other order",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("    3.4.  b(k) = 0 or b(k) ≠ 0".to_string()), "    3.4.  b(k) ≠ 0 or b(k) = 0".to_string()),
            ],
            "step 3.5 takes its cases from 3.4, which does not claim their assumptions joined by \"or\", in the order the cases take them",
        ),
        case(
            "give a first value in terms of the index",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("let a(0) = M,  b(0) = N,".to_string()), "let a(0) = k,  b(0) = N,".to_string()),
            ],
            "names k, which has no value at 0",
        ),
    ]
}
