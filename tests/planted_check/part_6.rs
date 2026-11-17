//! Part 6 of 6 of the planted cases, in the order they are run.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
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
        // A proof block assumes what its claim supposes.
        case(
            "a proof block assuming other than its claim supposes",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  then if x > 1 then x ≥ 1\n\n1.  If x > 1 then x ≥ 1.\n    proof\n    assume x ≥ 2    (A)\n\n    1.1.  x ≥ 1\n          inequalities, from A\n".to_string(),
            )],
            "step 1 opens a proof block assuming x ≥ 2, and its claim supposes 1 < x",
        ),
        // A let's kind is shown by its reason, a method's as an item's.
        case(
            "a let whose method reason does not show its kind",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  then x = x\n\nlet m = 2·x, a natural number    (D1)\n    membership\n    reads twice x\n\n1.  x = x\n    algebra\n".to_string(),
            )],
            "the reason under let D1 does not show 2·x ∈ ℕ",
        ),
        // An obtain from a definition unfolded claims its right side.
        case(
            "obtain from an unfolded definition other than its right side",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "import definition         stdlib/divisibility/even\n\ntheorem planted\n  let P ∈ ℤ    (H1)\n  assume P is even    (H2)\n  then P = P\n\n1.  k ∈ ℤ. P = 3k.\n    obtain k: def:even n := P, from H2\n\n2.  P = P\n    algebra\n".to_string(),
            )],
            "step 1 claims other than what it obtains, which says P = 2 · k",
        ),
        // A requires line other than a membership does work too.
        case(
            "a disequality an algebra step does not divide by",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  assume x > 0    (H2)\n  then x + x = 2·x\n\n1.  x + x = 2·x\n    algebra\n    requires x ≠ 0: weakening, from H2\n".to_string(),
            )],
            "the requires line of step 1 says x ≠ 0, and the step neither uses nor asks for it",
        ),
        // A pair naming a letter for itself is written only where matching
        // does not find the letter (`SYNTAX.md`); here the claim fixes f.
        case(
            "a pair naming a letter for itself that matching finds",
            vec![edit(
                "proofs/wiedijk/euler.proof",
                Some("    thm:product-congruent X := S, from 4, 5, 11".to_string()),
                "    thm:product-congruent X := S, f := f, from 4, 5, 11".to_string(),
            )],
            "cites with the pair f := f, and the theorem is checked without it",
        ),
        // The same of a requires line's citation: the line's claim fixes u.
        case(
            "a pair naming a letter for itself in a requires line",
            vec![edit(
                "proofs/wiedijk/wilson.proof",
                Some("          requires u ∈ ℤ: mun:in-subset, from H1, 12.1".to_string()),
                "          requires u ∈ ℤ: mun:in-subset u := u, from H1, 12.1".to_string(),
            )],
            "the requires line of step 12.4 cites with the pair u := u, and the theorem is checked without it",
        ),
        // A method step uses each line it cites: the certificate combines
        // lines 2 and 3, and line 1 says a + b is at least 0 or below it,
        // which the step does not combine.
        case(
            "cite a line a method step does not combine",
            vec![edit(
                "proofs/wiedijk/triangle-inequality.proof",
                Some("    4.1.  a + b ≤ |a| + |b|\n          inequalities, from 2, 3\n".to_string()),
                "    4.1.  a + b ≤ |a| + |b|\n          inequalities, from 1, 2, 3\n".to_string(),
            )],
            "step 4.1 cites 1 and uses nothing it says",
        ),
        // k's membership is said once, by J, and every step has it without
        // naming J. A method step citing J for it cites a line it uses
        // nothing of.
        case(
            "cite a let line only for the membership it says once, in a method step",
            vec![edit(
                "proofs/wiedijk/binomial.proof",
                Some("    20.2.  (k − 1) + 1 = k\n           algebra\n".to_string()),
                "    20.2.  (k − 1) + 1 = k\n           algebra, from J\n".to_string(),
            )],
            "step 20.2 cites J and uses nothing it says",
        ),
        // Inspection reads the facts of what it cites, and C's degree is
        // read off H1 and the degree's definition, not off A's.
        case(
            "cite a line an inspection does not read",
            vec![edit(
                "proofs/wiedijk/konigsberg.proof",
                Some("4.  deg(C) = 3\n    inspection, from H1, 1\n".to_string()),
                "4.  deg(C) = 3\n    inspection, from H1, 1, 2\n".to_string(),
            )],
            "step 4 cites 2 and uses nothing it says",
        ),
        // An exhibit cites what it says of its value; N/2 > M says nothing
        // of the sum the claim is about.
        case(
            "cite a line an exhibit says nothing of its value by",
            vec![edit(
                "proofs/wiedijk/harmonic.proof",
                Some("    exhibit, from 6\n".to_string()),
                "    exhibit, from 5, 6\n".to_string(),
            )],
            "step 7 cites 5 and uses nothing it says",
        ),
        // "There is a polynomial q with …" asks that q is a polynomial,
        // which line 1 says.
        case(
            "exhibit a polynomial nothing says is one",
            vec![edit(
                "proofs/wiedijk/factor.proof",
                Some("    exhibit, from 1, 2\n".to_string()),
                "    exhibit, from 2\n".to_string(),
            )],
            "step 3 exhibits q := q, so it needs",
        ),
        // "There is s ∈ S" binds s over nothing, and asks only that the
        // value is in S.
        case(
            "exhibit a member of a set nothing says one is in",
            vec![edit(
                "tests/docs/grammar.proof",
                Some("1.  There is s ∈ S.\n    exhibit, from H2\n".to_string()),
                "1.  There is s ∈ S.\n    exhibit, from H3\n".to_string(),
            )],
            "step 1 exhibits a value, and nothing it cites or requires says the claim's body of any one value",
        ),
        // A requires line's `from` names the lines it rests on, as a step's
        // does: d(k) ∈ ℝ rests on H2, d's type, at a k said once in ℕ₀,
        // read up into ℝ.
        case(
            "a requires line from a function's type naming the let of its point",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("      algebra\n          requires d(k) ∈ ℤ: from H2\n".to_string()),
                "      algebra\n          requires d(k) ∈ ℤ: from H2, K\n".to_string(),
            )],
            "the requires line of step 1.4 cites K, and d(k) ∈ ℤ needs nothing it says",
        ),
        // An item's hypothesis at a function's value reads the point as a
        // requires line does: said once, and a citation of it surplus.
        case(
            "an item at a function's value naming the let of its point",
            vec![edit(
                "tests/elaborator/a-value-at-a-point-said-once.proof",
                Some("    mun:abs-real x := a(n), from H1\n".to_string()),
                "    mun:abs-real x := a(n), from H1, H2\n".to_string(),
            )],
            "step 1 cites H2, and mun:abs-real asks for nothing it says",
        ),
        // A requires line's manipulation is of the one line it names.
        case(
            "a requires line naming a manipulation and no line",
            vec![edit(
                "tests/elaborator/a-power-said-not-zero.proof",
                Some("    requires x^n ≠ 0: weakening, from H4\n".to_string()),
                "    requires x^n ≠ 0: weakening\n".to_string(),
            )],
            "names weakening, which manipulates one line, and cites none: `weakening, from L`",
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
        // A formula that does not lex is a defect with a position, the line
        // it is written on, and not a route declining: taken for one, the
        // step would be assumed.
        case(
            "a requires line that does not lex",
            vec![edit(
                "proofs/wiedijk/geometric-series.proof",
                Some("substitute line 1.4\n          requires 1 − a ≠ 0: algebra, from H2\n".to_string()),
                "substitute line 1.4\n          requires 1 − a ¿ 0: algebra, from H2\n".to_string(),
            )],
            "the requires line of step 1.5: no token at '¿ 0' in '1 − a ¿ 0'",
        ),
        // Dropping the + 0 asks that what is left be a number, and q(x) ∈ ℂ is
        // a function's value, which the step says in a requires line: without
        // it nothing does.
        case(
            "drop a 0 from a term no line says is a number",
            vec![edit(
                "proofs/wiedijk/factor.proof",
                Some("          substitute p(a) = 0 (H3) into line 1\n          requires q(x) ∈ ℂ: mun:polynomial-value p := q, from 1\n".to_string()),
                "          substitute p(a) = 0 (H3) into line 1\n".to_string(),
            )],
            "drops an identity element from what the substitution makes, and nothing says (x − a) · q(x) is a number",
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
        // A function to a power is refused: its n-th derivative is written
        // with the order in parentheses, f^(n).
        case(
            "a function to a power without the parentheses",
            vec![edit(
                "tests/elaborator/an-nth-derivative.proof",
                Some("  assume f^(n)(c) = 0    (H4)\n".to_string()),
                "  assume f^n(c) = 0    (H4)\n".to_string(),
            )],
            "f is a function from numbers to numbers, and `_^_` wants a number",
        ),
        // The same with the claim's order written the other way round: the
        // substitution is read in the standard spelling, |x| < ε for ε > |x|,
        // and so is what it drops.
        case(
            "drop a 0 into a claim whose order is turned round",
            vec![
                edit(
                    "proofs/hammack/abs-limit-zero.proof",
                    Some("          1.4.1.  ||a(n)|| < ε\n".to_string()),
                    "          1.4.1.  ||a(n)| − 0| < ε\n".to_string(),
                ),
                edit(
                    "proofs/hammack/abs-limit-zero.proof",
                    Some("          1.4.6.  |a(n)| < ε\n".to_string()),
                    "          1.4.6.  ε > |a(n) − 0|\n".to_string(),
                ),
            ],
            "drops an identity element from what the substitution makes",
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
        // g(x) is real because of what g is, and a step that uses what a
        // define says cites it (`SYNTAX.md`). Without the define g stays a
        // name, and nothing the step cites says g(x) is real.
        case(
            "membership of a defined function's value without citing its define",
            vec![edit(
                "proofs/wiedijk/mean-value.proof",
                Some("    membership, from D2\n".to_string()),
                "    membership\n".to_string(),
            )],
            "is not built from what step 7 cites",
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
        // An identity element inside the place a substitution matches is
        // dropped there: 1.4.1 says ||a(n)| − 0| < ε, the equation's left
        // side ||a(n)|| stands at |a(n)| − 0 only once the − 0 goes, and
        // what is left, |a(n)|, is to be said a number, which it is once a
        // line says a(n) is.
        case(
            "drop an identity element inside the place a substitution matches",
            vec![
                edit(
                    "proofs/hammack/abs-limit-zero.proof",
                    Some("          1.4.1.  ||a(n)|| < ε\n".to_string()),
                    "          1.4.1.  ||a(n)| − 0| < ε\n".to_string(),
                ),
                edit(
                    "proofs/hammack/abs-limit-zero.proof",
                    Some("          1.4.6.  |a(n)| < ε\n".to_string()),
                    "          1.4.6.  |a(n) − 0| < ε\n".to_string(),
                ),
            ],
            "step 1.4.6 drops an identity element from what the substitution makes, and nothing says a(n) is a number",
        ),
        // A base that ends on its instance with an identity element dropped,
        // b(0) ≤ N for b(0) + 0 ≤ N, asks that b(0) be a number, which
        // nothing the step names says once its requires line goes.
        case(
            "end an induction's base by dropping an identity element from a value nothing says is a number",
            vec![edit(
                "proofs/wiedijk/euclid.proof",
                Some("          mun:or-left, from 5.1\n          requires b(0) ∈ ℝ: membership, from 2\n".to_string()),
                "          mun:or-left, from 5.1\n".to_string(),
            )],
            "step 5.2 ends the base part of step 5 by dropping an identity element, and nothing says b(0) is a number",
        ),
        // The statement is read before the proof, so a name only the proof
        // defines is no name there.
        case(
            "state a theorem of a name only its proof defines",
            vec![edit(
                "tests/elaborator/a-define-filling-a-cited-function.proof",
                Some("  let t(j) = j + 1, for j ∈ ℕ                                         (D1)\n         reads one more\n  then t(1) = 1 + 1\n".to_string()),
                "  then t(1) = 1 + 1\n\nlet t(j) = j + 1, for j ∈ ℕ                                           (D1)\n    reads one more\n".to_string(),
            )],
            "theorem a-define-filling-a-cited-function states t, which only its proof defines",
        ),
        // A step nothing cites, and that ends no part, says something the
        // proof never uses: 0 < 1 is true, and no line goes on from it.
        case(
            "write a step nothing cites",
            vec![edit(
                "proofs/hammack/abs-limit-zero.proof",
                Some("2.  a(n) → 0 as n → ∞\n    def:tends-to L := 0, from 1\n".to_string()),
                "2.  0 < 1\n    arithmetic\n\n3.  a(n) → 0 as n → ∞\n    def:tends-to L := 0, from 1\n".to_string(),
            )],
            "step 2 is cited by nothing, and is not the last step of its part",
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
        // A part of A is asked of M's argument, and the line named must say it:
        // A1 says X ⊆ Y, which is not that Y is a part of A.
        case(
            "a requires line for a part naming a line that does not say it",
            vec![edit(
                "proofs/wiedijk/schroeder-bernstein.proof",
                Some("          requires Y ⊆ A: from K4\n".to_string()),
                "          requires Y ⊆ A: from A1\n".to_string(),
            )],
            "from A1 does not reach Y ⊆ A",
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
        // What an obtain claims is the "there is" it obtains from: d ∈ ℕ is
        // not what the supposition gives, and the line is the page's claim,
        // never the existence's body in its place.
        case(
            "an obtain claiming more than the line it obtains from",
            vec![edit(
                "proofs/wiedijk/sqrt2-irrational.proof",
                Some("    2.1.  d ∈ ℤ. d > 1. d divides p. d divides q.".to_string()),
                "    2.1.  d ∈ ℕ. d > 1. d divides p. d divides q.".to_string(),
            )],
            "step 2.1 claims d ∈ ℕ, and what it obtains says d ∈ ℤ",
        ),
        // Dropping the 1 a substitution makes asks that what is left be a
        // number, and b(0) is one only by the line saying so.
        case(
            "drop an identity element a substitution makes from a value no line says is a number",
            vec![edit(
                "tests/elaborator/an-identity-a-substitution-makes.proof",
                Some("    substitute 1^k = 1 (H3)\n    requires b(0) ∈ ℝ: from H1\n".to_string()),
                "    substitute 1^k = 1 (H3)\n".to_string(),
            )],
            "step 1 drops an identity element from what the substitution makes, and nothing says b(0) is a number; a requires line says it",
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
        case(
            "a line number after into without the word line, in an induction",
            vec![edit(
                "tests/elaborator/induction-under-a-condition.proof",
                Some("(line 1.2.7) into line 1.2.6".to_string()),
                "(line 1.2.7) into 1.2.6".to_string(),
            )],
            "a line number after `into` carries the word \"line\": `into line 1.2.6`",
        ),
        // An item whose import is taken away is reported where it is cited.
        case(
            "cite an item whose import is taken away",
            vec![edit(
                "proofs/wiedijk/harmonic.proof",
                Some("import mundane theorem    stdlib/sums/sum-real\n".to_string()),
                String::new(),
            )],
            "mun:sum-real is neither imported nor a theorem of this file",
        ),
        // A requires line under a let's reason cites as any requires line
        // does: an item it names that nothing imports is reported.
        case(
            "cite an unknown item in a requires line under a let's reason",
            vec![edit(
                "proofs/wiedijk/liouville.proof",
                Some("    from 1\n    reads F on the real line\n".to_string()),
                "    from 1\n    requires x ∈ ℝ: mun:no-such-record\n    reads F on the real line\n"
                    .to_string(),
            )],
            "mun:no-such-record is neither imported nor a theorem of this file",
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
        // A theorem stated over a sequence by recursion is about that
        // sequence: a proof whose sequence of the name adds 2 does not have
        // what the cited theorem says of one that adds 1.
        case(
            "cite a theorem over another recursion of the same name",
            vec![edit(
                "tests/elaborator/citing-a-theorem-over-a-header-recursion.proof",
                Some("F(n + 1) = F(n) + 1,".to_string()),
                "F(n + 1) = F(n) + 2,".to_string(),
            )],
            "step 1 cites thm:counted-to-one, which is stated over F, defined by recursion there; there F(n + 1) is F(n) + 1, and D1 here says it is F(n) + 2",
        ),
        // The cited recursion with the citation's letters put in: M := N
        // makes its value at 0 N, and this proof's starts at N + 1.
        case(
            "cite a theorem over a recursion that starts elsewhere once its letters are put in",
            vec![edit(
                "tests/elaborator/citing-a-theorem-over-a-header-recursion.proof",
                Some("let F(0) = N,".to_string()),
                "let F(0) = N + 1,".to_string(),
            )],
            "there F(0) is N, and D1 here says it is N + 1",
        ),
        // Nothing says what a sequence by recursion's values are, so a sum of
        // their squares asks a line saying it at every point.
        case(
            "cite a sum's item over a compound of a recursion no line types",
            vec![edit(
                "tests/elaborator/a-sum-over-a-compound-of-a-defined-function.proof",
                Some("    mun:sum-single a := 1, from H1\n".to_string()),
                "    mun:sum-single a := 1\n".to_string(),
            )],
            "step 1 cites mun:sum-single, which asks that every term F(j)^2 is in ℝ, and it is no number by what the page says once",
        ),
        // The sequence itself, untyped, is told where its values are said.
        case(
            "cite a sum's item over a recursion no line types",
            vec![edit(
                "tests/elaborator/a-sum-over-a-compound-of-a-defined-function.proof",
                Some("    requires for all k ∈ {1, …, 1}, F(k) ∈ ℝ: from H1\n".to_string()),
                String::new(),
            )],
            "a requires line says it, as for all k ∈ {1, …, 1}, F(k) ∈ ℝ, from a line saying the values on a set holding {1, …, 1}",
        ),
        // A cited recursion is the citing proof's only with the same names in
        // the same order: the state is a pair in that order, and another
        // order is another term.
        case(
            "cite a theorem over two sequences named the other way round",
            vec![edit(
                "tests/elaborator/recursion-shapes-cited.proof",
                Some("  let F(0) = 0,  G(0) = 1,\n      F(n + 1) = G(n),  G(n + 1) = F(n) + G(n),  for n ∈ ℕ₀           (D1)\n".to_string()),
                "  let G(0) = 1,  F(0) = 0,\n      G(n + 1) = F(n) + G(n),  F(n + 1) = G(n),  for n ∈ ℕ₀           (D1)\n".to_string(),
            )],
            "D1 here gives G, F, and the theorem's define gives F, G",
        ),
        // A rule is the term it builds, as written: commuted, or with an
        // identity element added, it is another recursion.
        case(
            "cite a theorem over a recursion whose rule is written the other way",
            vec![edit(
                "tests/elaborator/recursion-shapes-cited.proof",
                Some("T(j + 1) = T(j) + (j + 1),".to_string()),
                "T(j + 1) = (j + 1) + T(j),".to_string(),
            )],
            "there T(j + 1) is T(j) + (j + 1), and D1 here says it is (j + 1) + T(j)",
        ),
        case(
            "cite a theorem over a recursion whose rule adds a zero",
            vec![edit(
                "tests/elaborator/recursion-shapes-cited.proof",
                Some("T(j + 1) = T(j) + (j + 1),".to_string()),
                "T(j + 1) = T(j) + (j + 1) + 0,".to_string(),
            )],
            "there T(j + 1) is T(j) + (j + 1), and D1 here says it is T(j) + (j + 1) + 0",
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
        // A requires line under a let's reason is checked as one under a
        // step: it does work for the reason, which the distance from A to C
        // does not.
        case(
            "a requires line under a let's reason that the reason does not use",
            vec![edit(
                "tests/elaborator/a-naming-let-with-a-requires-line.proof",
                Some("P := A, Q := B\n".to_string()),
                "P := A, Q := B\n    requires |AC| ≥ 0: mun:distance-nonneg P := A, Q := C\n".to_string(),
            )],
            "the requires line of let D1 says |AC| ≥ 0, and neither def:sqrt nor the let's other lines ask for it",
        ),
        case(
            "a let's reason without the requires lines its item asks for",
            vec![edit(
                "tests/elaborator/a-naming-let-with-a-requires-line.proof",
                Some("    requires |AB| ≥ 0: mun:distance-nonneg P := A, Q := B\n    requires √|AB| ∈ ℝ and √|AB| ≥ 0: def:sqrt x := |AB|\n".to_string()),
                String::new(),
            )],
            "the reason under let D1 cites def:sqrt, which asks for √|AB| ∈ ℝ; 0 ≤ √|AB|, and what it cites does not supply them",
        ),
        // A let's requires line answers to the item it cites as a step's
        // does: the root of |AB| asks that |AB| is at least 0, which the
        // line above it says.
        case(
            "a requires line under a let citing an item without a fact it asks for",
            vec![edit(
                "tests/elaborator/a-naming-let-with-a-requires-line.proof",
                Some("    requires |AB| ≥ 0: mun:distance-nonneg P := A, Q := B\n".to_string()),
                String::new(),
            )],
            "the requires line of let D1 cites def:sqrt, which asks for 0 ≤ |AB|, and what it cites does not supply it",
        ),
        // An angle is written only where its three points are said to
        // differ (`SYNTAX.md`, Formulas): in a statement, by its hypotheses.
        case(
            "write an angle in a statement whose hypotheses leave two of its points unsaid apart",
            vec![edit(
                "tests/elaborator/a-naming-let-with-a-requires-line.proof",
                Some("  assume A ≠ C                                                        (H6)\n".to_string()),
                String::new(),
            )],
            "the statement of a-naming-let-with-a-requires-line writes ∠ABC, and nothing where it is written says A ≠ C",
        ),
        case(
            "write an angle in a library item whose hypotheses leave two of its points unsaid apart",
            vec![edit(
                "corpus/stdlib/geometry.records",
                Some("  assume P ≠ R                                                        (H6)\n  then        ∠PQR = ∠RQP".to_string()),
                "  then        ∠PQR = ∠RQP".to_string(),
            )],
            "mundane theorem angle-turned writes ∠PQR, and its hypotheses do not say P ≠ R",
        ),
        // The let's requires lines are its own, and rest on nothing below
        // it, the let included.
        case(
            "a requires line under a let citing the let",
            vec![edit(
                "tests/elaborator/a-naming-let-with-a-requires-line.proof",
                Some("    def:sqrt x := √|AB|\n".to_string()),
                "    def:sqrt x := √|AB|\n    requires r ∈ ℝ: from D1\n".to_string(),
            )],
            "the requires line under let D1 cites D1, which is not above the let",
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
        // A nested block's step numbered as its owner's sibling is read as
        // the enclosing block's, and the numbering is what is named.
        case(
            "number a nested case's step at the outer level",
            vec![edit(
                "proofs/setmm/prime-two-or-odd.proof",
                Some("          2.6.1.  2 ≠ 1\n".to_string()),
                "          2.7.    2 ≠ 1\n".to_string(),
            )],
            "step 2.6 is justified by cases, which needs a block, and has no sub-steps: the step below it is numbered 2.7, so what stands under it is read as part of step 2's block; a step of 2.6's block is numbered 2.6.1",
        ),
        // A cited line that applies a defined function is read with the
        // function's rule where the step cites its define, and the rule
        // holds only inside the domain: T ∈ G(m − 1, n) unfolds only where
        // m − 1 ∈ ℕ₀, which line 1 says.
        case(
            "unfold a define applied in a cited line without its domain",
            vec![edit(
                "proofs/wiedijk/ballot.proof",
                Some("def:set-builder u := T, from D2, K3, 1\n".to_string()),
                "def:set-builder u := T, from D2, K3\n".to_string(),
            )],
            "cites D2 at m − 1, so it needs m − 1 ∈ ℕ₀, and nothing it cites or requires says it",
        ),
        // A hypothesis applying a define is written out in the statement,
        // and a step reading it reads the name as its rule, which holds only
        // inside the domain: K(m − 1, n) asks m − 1 ∈ ℕ₀ of the step.
        case(
            "substitute into a hypothesis applying a define without its domain",
            vec![edit(
                "tests/elaborator/a-define-applied-in-a-hypothesis.proof",
                Some("into H3\n    requires m − 1 ∈ ℕ₀: from 1\n".to_string()),
                "into H3\n".to_string(),
            )],
            "step 3 reads a hypothesis applying the define D1 at m − 1, which the statement writes out, so it needs m − 1 ∈ ℕ₀, and nothing it cites or requires says it",
        ),
        // The conclusion applying a define is written out, and the last
        // step's claim is carried to it with what the proof holds at its
        // outermost level: G(m − 1, n) asks a line saying m − 1 ∈ ℕ₀ there.
        case(
            "state a define at a term no line of the proof puts in its domain",
            vec![edit(
                "proofs/wiedijk/ballot.proof",
                Some("3.  m − 1 ∈ ℕ₀\n    mun:nat-minus-one n := m\n\n4.  There is a bijection from G(m − 1, n) to {T ∪ {m + n} : T ∈ G(m − 1, n)}.\n    mun:image-of-injection, from 2, 3\n".to_string()),
                "3.  There is a bijection from G(m − 1, n) to {T ∪ {m + n} : T ∈ G(m − 1, n)}.\n    mun:image-of-injection, from 2\n".to_string(),
            )],
            "the conclusion of add-last-place applies the define D2 at m − 1 and is written out, so it needs m − 1 ∈ ℕ₀, and neither a hypothesis nor a line of its proof outside a block says it",
        ),
        // A theorem stated over a define writes it out, so a step citing it
        // meets its hypotheses only where each argument is in the define's
        // domain: ballot-recurrence asks for the formula at G(m − 1, n), and
        // without the lines saying m − 1 and n − 1 are in ℕ₀ nothing does.
        case(
            "cite a theorem stated over a define at a term the step does not put in its domain",
            vec![edit(
                "proofs/wiedijk/ballot.proof",
                Some("from C3, 1.16.2, 1.16.4.5, 1.16.4.6, 1.16.4.7,\n                               1.16.4.11, 1.16.4.16".to_string()),
                "from C3, 1.16.2, 1.16.4.5, 1.16.4.11, 1.16.4.16".to_string(),
            )],
            "step 1.16.4.17 cites thm:ballot-recurrence, whose statement applies the define D2 at m − 1 and is written out, so it needs m − 1 ∈ ℕ₀, and nothing it cites or requires says it",
        ),
        // A theorem proved `by` a method is that method's step, which the
        // page gives no number, whose block holds every step of the proof
        // (`SYNTAX.md`, a theorem proved by a method).
        case(
            "prove a theorem by a method that opens no block",
            vec![edit(
                "proofs/setmm/subset-of-union-and-difference.proof",
                Some("  by          both directions".to_string()),
                "  by          algebra".to_string(),
            )],
            "`by` names a method that opens a block: both directions, contradiction, proof, induction or cases; algebra proves a step",
        ),
        case(
            "write by twice",
            vec![edit(
                "proofs/setmm/subset-of-union-and-difference.proof",
                Some("  by          both directions\n".to_string()),
                "  by          both directions\n  by          both directions\n".to_string(),
            )],
            "`by` comes once, under `then`, before the proof",
        ),
        case(
            "a step above the first part of a theorem proved by both directions",
            vec![edit(
                "proofs/setmm/subset-of-union-and-difference.proof",
                Some("  by          both directions\n\ndirection\n".to_string()),
                "  by          both directions\n\n1.  A ⊆ A\n    mun:subset-reflexive X := A\n\ndirection\n".to_string(),
            )],
            "step 1 stands outside the theorem's block; under `by` every step is in one of its parts",
        ),
        case(
            "an induction hypothesis naming a step of a theorem proved by induction",
            vec![edit(
                "proofs/wiedijk/liouville-number.proof",
                Some("assume the theorem is true for j, the induction hypothesis            (IH)".to_string()),
                "assume step 1 is true for j, the induction hypothesis                 (IH)".to_string(),
            )],
            "the theorem has no step 1; its induction hypothesis says `assume the theorem is true for j, the induction hypothesis`",
        ),
        case(
            "a theorem proved by contradiction whose block ends on no contradiction",
            vec![edit(
                "proofs/hammack/rational-squares-sum-not-three.proof",
                Some("    inequalities, from H2, contradicting 1\n".to_string()),
                "    inequalities, from H2\n".to_string(),
            )],
            "step 2 ends a contradiction block and does not say which line it contradicts",
        ),
        case(
            "a theorem proved by contradiction with no steps",
            vec![edit(
                "proofs/hammack/rational-squares-sum-not-three.proof",
                Some("  by          contradiction\n\nsuppose 3 divides r                                                   (S)\n\n1.  3 ≤ r\n    mun:divides-le e := 3, m := r, from S\n\n2.  not 3 ≤ r\n    inequalities, from H2, contradicting 1\n".to_string()),
                "  by          contradiction\n".to_string(),
            )],
            "the theorem is proved `by contradiction` and its block has no steps",
        ),
        // A part of a block names the method of its own block on a `by` line
        // after its openers: `by proof` or `by contradiction` (`SYNTAX.md`,
        // Blocks).
        case(
            "a part proved by cases",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    by          proof\n    assume P divides Q^(m + 1)".to_string()),
                "    by          cases\n    assume P divides Q^(m + 1)".to_string(),
            )],
            "`by` inside a block names proof or contradiction, whose blocks open with lines; cases opens parts",
        ),
        case(
            "a part that says by twice",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    base\n    by          proof\n".to_string()),
                "    base\n    by          proof\n    by          proof\n".to_string(),
            )],
            "a part says `by` once, after its openers and before its first step",
        ),
        case(
            "a part's by line after its first step",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    3.1.  Q^0 = 1\n          algebra\n".to_string()),
                "    3.1.  Q^0 = 1\n          algebra\n    by          proof\n".to_string(),
            )],
            "`by` in a block comes after its part's openers, before its first step",
        ),
        case(
            "a part's by line with a part marker after it",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    base\n    by          proof\n".to_string()),
                "    base\n    by          proof\n    step\n".to_string(),
            )],
            "has no steps before the next part",
        ),
        case(
            "an induction hypothesis after the part's by line",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    assume step 3 is true for m, the induction hypothesis             (IH)\n    by          proof\n".to_string()),
                "    by          proof\n    assume step 3 is true for m, the induction hypothesis             (IH)\n".to_string(),
            )],
            "the induction hypothesis comes before the part's `by` line",
        ),
        case(
            "a part proved by proof that lets and assumes nothing",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    by          proof\n    assume P divides Q^0                                              (C1)\n".to_string()),
                "    by          proof\n".to_string(),
            )],
            "the base part of step 3 is proved by `proof` and does not open with `let` or `assume` after its `by` line",
        ),
        case(
            "a part proved by proof assuming what it does not owe",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    assume P divides Q^(m + 1)                                        (C2)".to_string()),
                "    assume P divides Q^m                                              (C2)".to_string(),
            )],
            "the step part of step 3 opens a proof block assuming",
        ),
        case(
            "a part proved by proof ending on what it does not owe",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("          inequalities, contradicting 3.3\n".to_string()),
                "          inequalities\n".to_string(),
            )],
            "step 3.4 ends the base part of step 3, which owes P = Q",
        ),
        case(
            "a part proved by contradiction that assumes",
            vec![edit(
                "proofs/setmm/contrapositive.proof",
                Some("suppose a = 0                                                         (S)".to_string()),
                "assume a = 0                                                          (S)".to_string(),
            )],
            "the proof block of the theorem is proved by contradiction and does not open with `suppose` after its `by` line",
        ),
        case(
            "a part proved by contradiction supposing what it does not deny",
            vec![edit(
                "proofs/setmm/contrapositive.proof",
                Some("suppose a = 0                                                         (S)".to_string()),
                "suppose a = 1                                                         (S)".to_string(),
            )],
            "the proof block of the theorem supposes something that is neither what it owes negated nor the thing it owes negates",
        ),
        case(
            "a part proved by contradiction ending on no contradiction",
            vec![edit(
                "proofs/setmm/contrapositive.proof",
                Some("    restate K2, contradicting 1".to_string()),
                "    restate K2".to_string(),
            )],
            "step 2 ends the proof block of the theorem, proved by contradiction, and does not say which line it contradicts",
        ),
        case(
            "a part proved by contradiction that never uses its supposition",
            vec![edit(
                "proofs/setmm/contrapositive.proof",
                Some("    mun:modus-ponens, from K1, S".to_string()),
                "    mun:modus-ponens, from K1".to_string(),
            )],
            "the proof block of the theorem is proved by contradiction and never uses its supposition S",
        ),
        case(
            "a proof block that says by proof",
            vec![edit(
                "proofs/setmm/contrapositive.proof",
                Some("by          contradiction\nsuppose a = 0".to_string()),
                "by          proof\nassume a = 0".to_string(),
            )],
            "the proof block of the theorem says `by proof`; its let and assume lines go on without it",
        ),
        case(
            "a contradiction block that says by",
            vec![edit(
                "proofs/hammack/rational-squares-sum-not-three.proof",
                Some("suppose 3 divides r                                                   (S)\n".to_string()),
                "suppose 3 divides r                                                   (S)\nby          proof\n".to_string(),
            )],
            "the theorem is a contradiction, whose block owes no claim for `by` to prove",
        ),
        // Two functions compared whole are refused. The Lean build relies on
        // it: a Lean function has values off the set the page gives it, so
        // f(x) = x and g(x) = x² on X = {0} are equal on the page and not in
        // Lean. A language that lets `=` compare functions needs the Lean
        // writer to refuse or bridge such a comparison first.
        case(
            "compare two maps with = (the Lean writer must refuse it before the language allows it)",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let X be a set    (H1)\n  let Y be a set    (H2)\n  let f : X → Y    (H3)\n  let g : X → Y    (H4)\n  assume f = g    (H5)\n  then f = g\n\n1.  f = g\n    restate H5\n".to_string(),
            )],
            "and `_ = _` wants a term",
        ),
        // A define's values are in the number system it gives them where it
        // is made: Lean fixes a function's type there, so a later line that
        // puts them in a narrower one is refused and the define says it.
        case(
            "a later line narrowing a define's values to ℝ",
            vec![
                edit(
                    "proofs/wiedijk/liouville.proof",
                    Some("let f(x) = F(x), a real number, for x ∈ ℝ                             (D1)\n    from 1\n".to_string()),
                    "let f = (x ∈ ℝ ↦ F(x))                                                (D1)\n".to_string(),
                ),
                edit(
                    "proofs/wiedijk/liouville.proof",
                    Some("2.  For all x ∈ ℝ, f(x) = F(x).\n    D1".to_string()),
                    "2.  f : ℝ → ℝ\n    mun:function-into, from D1, 1".to_string(),
                ),
            ],
            "step 2 puts f's values in ℝ, which its define does not; the define says it, as its kind",
        ),
    ]
}
