//! The planted cases about citing items and lines: hypotheses supplied, requires lines, values given, conclusions met and lines that do no work.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
        // A step's proof rests only on what it names (`GOALS.md` decision 9).
        // Without its requires line, the calculation combines s(n), and the
        // scope holds s(n) ∈ ℝ from line 2, which step 3.23 does not cite. A
        // value of a defined sequence is not a membership said once, so only
        // a line can give it.
        case(
            "lean on a line the step does not name",
            vec![edit(
                "proofs/wiedijk/liouville-number.proof",
                Some("                                  = 2/2^A − 2/2^(A + (j + 1))               algebra, from 3.19\n          requires s(n) ∈ ℝ: from 2\n".to_string()),
                "                                  = 2/2^A − 2/2^(A + (j + 1))               algebra, from 3.19\n".to_string(),
            )],
            "proofs/wiedijk/liouville-number.proof:202  nothing says s(n) ∈ ℝ or ∈ ℂ, which this step needs",
        ),
        // Where the proof has no letter of the subject's name in scope, the
        // pair is the only thing that says what the definition is about:
        // even-leg has no d, and its step claims an impossible fold.
        case(
            "leave out a definition's subject where the proof has no such letter",
            vec![edit(
                "proofs/wiedijk/pythagorean-triples.proof",
                Some("def:divides d := 4, n := 2, from 2.2.9".to_string()),
                "def:divides n := 2, from 2.2.9".to_string(),
            )],
            "def:divides is about d, and the step gives d no value and the proof has no d; write it, as d := t",
        ),
        // abs asks that x be real, at x := ⌊A + 1/2⌋ − A. A line saying the
        // floor is an integer would make the difference a number, as what
        // − builds from a part a line states is; citing neither that line
        // nor the difference's own, the step has nothing to build it from.
        case(
            "a hypothesis about a term whose parts no line the step names states",
            vec![edit(
                "tests/elaborator/floor-in-a-bound.proof",
                Some("    def:abs x := ⌊A + 1/2⌋ − A, from H2, 2\n".to_string()),
                "    def:abs x := ⌊A + 1/2⌋ − A, from H2\n".to_string(),
            )],
            "step 3 cites def:abs, which asks for ⌊A + 1 / 2⌋ − A ∈ ℝ, and what it cites does not supply it",
        ),
        // A join takes what the lines write, and nothing else a line says
        // (`SYNTAX.md`, What a cited line says): not a chain's other
        // equations, a range's bound or what a membership implies. A
        // define it cites reads a name as what it names, and one whose name
        // no sentence needs read is a line the join does not use.
        case(
            "restate citing a define no sentence needs read",
            vec![edit(
                "tests/elaborator/reading-defines.proof",
                Some("theorem a-define-read-in-a-case-split\n".to_string()),
                "theorem an-unneeded-define-in-a-join\n  let a ∈ ℝ    (H1)\n  assume a + 1 > 0    (H2)\n  then a + 1 > 0\n\nlet e = a + 1, a real number    (D1)\n    membership\n    reads one more than a\n\n1.  a + 1 > 0\n    restate D1, H2\n\ntheorem a-define-read-in-a-case-split\n".to_string(),
            )],
            "step 1 restates D1, and claims nothing it says",
        ),
        case(
            "write the membership a requires-line weakening needs below it",
            vec![edit(
                "tests/elaborator/a-requires-weakening-with-its-membership.proof",
                Some("    requires √(x + 1) ∈ ℝ: from 2\n    requires √x ∈ ℝ: from 3\n    requires √(x + 1) + √x ≠ 0: weakening, from 8\n".to_string()),
                "    requires √(x + 1) + √x ≠ 0: weakening, from 8\n    requires √(x + 1) ∈ ℝ: from 2\n    requires √x ∈ ℝ: from 3\n".to_string(),
            )],
            "nothing above says √(x + 1) ∈ ℝ, which this step needs; the requires line √(x + 1) ∈ ℝ below says it, and a requires line takes only what the lines above it state: move it above",
        ),
        // A requires line of a closure step says a membership of a term the
        // step combines: step 17 combines no power of 3.
        case(
            "a requires line of an inequalities step about a term it never combines",
            vec![edit(
                "proofs/wiedijk/harmonic.proof",
                Some("    requires Σ(k = 2^j + 1 to 2^(j + 1)) 1/k ∈ ℝ: mun:sum-real a := 2^j + 1, b := 2^(j + 1)\n\n18.".to_string()),
                "    requires Σ(k = 2^j + 1 to 2^(j + 1)) 1/k ∈ ℝ: mun:sum-real a := 2^j + 1, b := 2^(j + 1)\n    requires 3^j ∈ ℝ: membership\n\n18.".to_string(),
            )],
            "says 3^j ∈ ℝ, and the step neither uses nor asks for it",
        ),
        // A library function an item applies is no letter of the item's:
        // lowest-terms-parts says denom(x) ∈ ℕ, which is not numer(x) ∈ ℕ.
        case(
            "a requires line narrowing what a record says of a library function",
            vec![edit(
                "proofs/wiedijk/rationals-countable.proof",
                Some("def:abs x := numer(x), from C1\n                  requires numer(x) ∈ ℤ: mun:lowest-terms-parts\n".to_string()),
                "def:abs x := numer(x), from C1\n                  requires numer(x) ∈ ℕ: mun:lowest-terms-parts\n".to_string(),
            )],
            "the requires line of step 4.3.2 needs something that mun:lowest-terms-parts does not conclude",
        ),
        // What a line says at the values may be an implication, whose
        // condition a line the step cites meets: line 13 asks that U(k) be
        // an upper bound of S, which line 10 says at k and 15.1 does not.
        case(
            "instantiate an implication whose condition no cited line meets",
            vec![edit(
                "proofs/wiedijk/reals-uncountable.proof",
                Some("instantiate u := U(k) in line 13, from 10".to_string()),
                "instantiate u := U(k) in line 13, from 15.1".to_string(),
            )],
            "instantiating at that term wants U(k) is an upper bound of S, which step 15.2 does not supply",
        ),
        // An instantiation claims what its line says at the values: H2 says
        // 0 ≤ d(n) for every n, and so 0 ≤ d(k + 1), not 0 ≥ d(k + 1).
        case(
            "instantiate a line for what it does not say there",
            vec![edit(
                "proofs/wiedijk/reals-uncountable.proof",
                Some("    3.3.  0 ≤ d(k + 1) and d(k + 1) ≤ 9\n          instantiate n := k + 1 in H2, from 3.2\n".to_string()),
                "    3.3.  0 ≥ d(k + 1) and d(k + 1) ≤ 9\n          instantiate n := k + 1 in H2, from 3.2\n".to_string(),
            )],
            "H2 at those terms says 0 ≤ d(k + 1) and d(k + 1) ≤ 9, and the step claims 0 ≥ d(k + 1) and d(k + 1) ≤ 9",
        ),
        // A requires line of `from` alone rests on the lines it names: f(b)
        // is real by f's type H4 and b's place in its domain, and with H4
        // left out nothing it names types f, the type in scope being no
        // line it names.
        case(
            "a from line that leaves out the type its value needs",
            vec![edit(
                "proofs/wiedijk/mean-value.proof",
                Some("    requires f′(c) ∈ ℝ: mun:derivative-real x := c, from H6, 22\n    requires f(a) ∈ ℝ: from H4, 2\n    requires f(b) ∈ ℝ: from H4, 3\n".to_string()),
                "    requires f′(c) ∈ ℝ: mun:derivative-real x := c, from H6, 22\n    requires f(a) ∈ ℝ: from H4, 2\n    requires f(b) ∈ ℝ: from 3\n".to_string(),
            )],
            "from 3 does not reach f(b) ∈ ℝ, which this line claims it supplies",
        ),
        // A define gives its function on its domain and nothing more: the
        // type p : X → ℝ is a step citing `function-into`, and a requires
        // line naming the define and the values' line in its place is not
        // read as that step.
        case(
            "a function's type from its define and its values, in place of the step proving it",
            vec![edit(
                "proofs/wiedijk/binomial.proof",
                Some("mun:sum-termwise a := 0, b := m + 1, t := p, from 17\n    requires p : {0, …, m + 1} → ℝ: from 4\n".to_string()),
                "mun:sum-termwise a := 0, b := m + 1, t := p, from 17\n    requires p : {0, …, m + 1} → ℝ: from D2, 3\n".to_string(),
            )],
            "from D2, 3 does not reach p : {0, …, m + 1} → ℝ, which this line claims it supplies",
        ),
        // A step claims of a definition something it does not say.
        case(
            "claim of a definition what it does not say",
            vec![edit(
                "proofs/wiedijk/triangle-inequality.proof",
                Some("    2.6.  |x| = −x".to_string()),
                "    2.6.  |x| = x".to_string(),
            )],
            "step 2.6 claims something that def:abs does not conclude",
        ),
        // A conclusion is matched with an identity element dropped where the
        // instance has one, and with nothing else changed: the shifted sum
        // starts at 0 + 1, which is 1 and not 2.
        case(
            "claim a lemma's conclusion with more than an identity element dropped",
            vec![edit(
                "proofs/wiedijk/binomial.proof",
                Some("= Σ(k = 1 to m + 1) C(m, k − 1)·x^(m − (k − 1))·y^((k − 1) + 1)        mun:sum-shift".to_string()),
                "= Σ(k = 2 to m + 1) C(m, k − 1)·x^(m − (k − 1))·y^((k − 1) + 1)        mun:sum-shift".to_string(),
            )],
            "step 26 claims something that mun:sum-shift does not conclude",
        ),
        // 0 is an identity on the right of a difference and not on its left:
        // C(m, 0 − 1) is not C(m, −1) by any identity law.
        case(
            "drop a 0 from the side of a difference where it is no identity",
            vec![edit(
                "proofs/wiedijk/binomial.proof",
                Some("= C(m, 0 − 1)·x^(m + 1)·y^0 + Σ(k = 1 to m + 1)".to_string()),
                "= C(m, −1)·x^(m + 1)·y^0 + Σ(k = 1 to m + 1)".to_string(),
            )],
            "step 23 claims something that mun:sum-first does not conclude",
        ),
        // A `requires` line has a claim and a reason, and the reason is what
        // proves it. Here H6 does not say `C ≠ B`, and the step no longer
        // cites H5, which does.
        case(
            "name a line that does not state the side condition",
            vec![
                edit(
                    "proofs/euclid/thales.proof",
                    Some("import theorem            stdlib/geometry/angle-sum\n".to_string()),
                    "import theorem            stdlib/geometry/angle-sum\nimport definition         stdlib/geometry/triangle\n".to_string(),
                ),
                edit(
                    "proofs/euclid/thales.proof",
                    Some("    mun:angle-along-segment P := A, Q := B, R := C, S := M, from H5, H6, 1\n".to_string()),
                    "    mun:angle-along-segment P := A, Q := B, R := C, S := M, from H6, 1\n    requires C ≠ B: def:triangle P := A, Q := B, R := C, from H6\n".to_string(),
                ),
            ],
            "the requires line of step 7 needs something that def:triangle does not conclude",
        ),
        // The same, where the step already holds the claim for another reason:
        // it cites H5, which says A, B, C form a triangle, so `C ≠ B` is held
        // before the line is read, and H6 does not say it.
        case(
            "name a line that does not state a claim the scope already holds",
            vec![
                edit(
                    "proofs/euclid/thales.proof",
                    Some("import theorem            stdlib/geometry/angle-sum\n".to_string()),
                    "import theorem            stdlib/geometry/angle-sum\nimport definition         stdlib/geometry/triangle\n".to_string(),
                ),
                edit(
                    "proofs/euclid/thales.proof",
                    Some("    mun:angle-along-segment P := A, Q := B, R := C, S := M, from H5, H6, 1\n".to_string()),
                    "    mun:angle-along-segment P := A, Q := B, R := C, S := M, from H5, H6, 1\n    requires C ≠ B: def:triangle P := A, Q := B, R := C, from H6\n".to_string(),
                ),
            ],
            "the requires line of step 7 needs something that def:triangle does not conclude",
        ),
        // A requires line below that cites an item asks for that item's
        // hypotheses, and only those: mun:sum-real asks nothing of x^m, and
        // nothing asks x^m ∈ ℝ of a substitution that drops the 0 before the
        // sum. A power to a letter is written where it is needed, so the line
        // is not one the step is spared; it is one nothing needs.
        case(
            "a requires line above an item's line that the item does not ask for",
            vec![
                edit(
                    "proofs/wiedijk/binomial.proof",
                    Some("import mundane theorem    stdlib/numbers/exponent-step\n".to_string()),
                    "import mundane theorem    stdlib/numbers/exponent-step\nimport mundane theorem    stdlib/numbers/power-real\n".to_string(),
                ),
                edit(
                    "proofs/wiedijk/binomial.proof",
                    Some("    substitute C(m, 0 − 1)·x^(m + 1)·y^0 = 0 (line 22) into line 23\n    requires Σ(k = 1 to m + 1)".to_string()),
                    "    substitute C(m, 0 − 1)·x^(m + 1)·y^0 = 0 (line 22) into line 23\n    requires x^m ∈ ℝ: mun:power-real a := x, m := m, from H1\n    requires Σ(k = 1 to m + 1)".to_string(),
                ),
            ],
            "the requires line of step 24 cites H1, and mun:power-real asks for nothing it says",
        ),
        // A requires line rests only on its reason. Line 2 does not say ⌊A⌋
        // is an integer, and `mun:int-real` asks it; the scope has it from
        // line 1, which the line does not cite, so the item it names reaches
        // nothing.
        case(
            "give a requires line a reason that is not where its proof comes from",
            vec![
                edit(
                    "proofs/setmm/floor-add-integer.proof",
                    Some("import mundane theorem    stdlib/numbers/floor-integer\n".to_string()),
                    "import mundane theorem    stdlib/numbers/floor-integer\nimport mundane theorem    stdlib/numbers/int-real\n".to_string(),
                ),
                edit(
                    "proofs/setmm/floor-add-integer.proof",
                    Some("      ⌊A⌋ + N ≤ A + N          adding N\n    requires ⌊A⌋ ∈ ℝ: from 1\n".to_string()),
                    "      ⌊A⌋ + N ≤ A + N          adding N\n    requires ⌊A⌋ ∈ ℝ: mun:int-real, from 2\n".to_string(),
                ),
            ],
            "the requires line of step 4 cites mun:int-real, which asks for ⌊A⌋ ∈ ℤ, and what it cites does not supply it",
        ),
        // Everything a step names does work. A numeral's membership is said
        // once (`SYNTAX.md`), so the line is true, well formed, and does
        // nothing.
        case(
            "write a requires line nothing asks for",
            vec![edit(
                "proofs/wiedijk/sum-formula.proof",
                Some("= (k + 1)((k + 1) + 1)/2       algebra\n".to_string()),
                "= (k + 1)((k + 1) + 1)/2       algebra\n          requires 2 ∈ ℝ: arithmetic\n".to_string(),
            )],
            "the requires line of step 1.3 says 2 ∈ ℝ, which the page says once",
        ),
        // A side condition is supplied by what the step names, not by
        // everything in scope: the scope holds |T| = 2^k, and with 1.2.5 no
        // longer cited nothing the step names says it.
        case(
            "settle a side condition from a line the step does not cite",
            vec![edit(
                "proofs/wiedijk/subsets.proof",
                Some("n := 2^k, from 1.8, 1.10, 1.11".to_string()),
                "n := 2^k, from 1.8, 1.11".to_string(),
            )],
            "step 1.13 cites mun:card-disjoint-union, which asks for |T| = 2^k, and what it cites does not supply it",
        ),
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
            "join a line the claim says nothing of",
            vec![edit(
                "proofs/wiedijk/euclid.proof",
                Some("    3.3.  a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀\n          join 3.1, 3.2".to_string()),
                "    3.3.  a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀\n          join 1, 3.1, 3.2".to_string(),
            )],
            "step 3.3 joins 1, and claims nothing it says",
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
        case(
            "instantiate an item instead of a line",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("    instantiate u := b in line 9, from 7".to_string()), "    instantiate u := b in def:least-upper-bound, from 7".to_string()),
            ],
            "never an item",
        ),
        // A conclusion is matched with an identity element dropped where the
        // instance has one, and with nothing else changed: the shifted sum
        // starts at 0 + 1, which is 1 and not 2.
        case(
            "claim a lemma's conclusion with more than an identity element dropped",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("= Σ(k = 1 to m + 1) C(m, k − 1)·x^(m − (k − 1))·y^((k − 1) + 1)        mun:sum-shift".to_string()), "= Σ(k = 2 to m + 1) C(m, k − 1)·x^(m − (k − 1))·y^((k − 1) + 1)        mun:sum-shift".to_string()),
            ],
            "step 26 claims something that mun:sum-shift does not conclude",
        ),
        // 0 is an identity on the right of a difference and not on its left:
        // C(m, 0 − 1) is not C(m, −1) by any identity law.
        case(
            "drop a 0 from the side of a difference where it is no identity",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("= C(m, 0 − 1)·x^(m + 1)·y^0 + Σ(k = 1 to m + 1)".to_string()), "= C(m, −1)·x^(m + 1)·y^0 + Σ(k = 1 to m + 1)".to_string()),
            ],
            "step 23 claims something that mun:sum-first does not conclude",
        ),
        // A set-builder's equation needs no line where it is the same on both
        // sides once its witnesses are read off, and one where it is not:
        // a·x + b·y + 1 = a·m + b·n has no m and n of that shape.
        case(
            "a set-builder's equation that no witness makes the same on both sides",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("    8.1.  a·x + b·y ∈ S\n          def:set-builder u := a·x + b·y, from D1, K3\n".to_string()), "    8.1.  a·x + b·y + 1 ∈ S\n          def:set-builder u := a·x + b·y + 1, from D1, K3\n".to_string()),
            ],
            "step 8.1",
        ),
        // A requires line's item asks for what the lines it cites supply:
        // `mod-natural` asks b ∈ ℕ, and without 4.3.6, which says b(k) ∈ ℕ,
        // the line says what is missing rather than that the item concludes
        // something else.
        case(
            "a requires line whose item's hypothesis nothing supplies",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("requires a(k) mod b(k) ∈ ℕ₀: mun:mod-natural, from 4.3.6, 4.3.7\n".to_string()), "requires a(k) mod b(k) ∈ ℕ₀: mun:mod-natural, from 4.3.7\n".to_string()),
            ],
            "the requires line of step 4.3.8 cites mun:mod-natural, which asks for",
        ),
        // What an obtain claims is the "there is" it obtains from, the line
        // it names or what the item gives (`SYNTAX.md`), and no more.
        case(
            "an obtain from a line that claims more than the line's there is",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    2.1.  d ∈ ℤ. d > 1. d divides p. d divides q.".to_string()), "    2.1.  d ∈ ℤ. d > 2. d divides p. d divides q.".to_string()),
            ],
            "step 2.1 claims other than what it obtains, which says",
        ),
        case(
            "an obtain from an item that claims more than the item's there is",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("4.  d ∈ S. For all s ∈ S, d ≤ s.".to_string()), "4.  d ∈ S. For all s ∈ S, d < s.".to_string()),
            ],
            "step 4 claims other than what it obtains, which says",
        ),
        case(
            "an obtain whose membership is not the one its there is gives",
            vec![
                edit("proofs/wiedijk/harmonic.proof", Some("    1.2.  B ∈ ℝ. For all m ∈ ℕ, Σ(k = 1 to m) 1/k ≤ B.".to_string()), "    1.2.  B ∈ ℚ. For all m ∈ ℕ, Σ(k = 1 to m) 1/k ≤ B.".to_string()),
            ],
            "step 1.2 claims B ∈ ℚ, and what it obtains says B ∈ ℝ",
        ),
        case(
            "an obtain from a line that says no there is",
            vec![
                edit("proofs/wiedijk/pythagorean-triples.proof", Some("    obtain k, m, n from line 2".to_string()), "    obtain k, m, n from H1".to_string()),
            ],
            "step 3 obtains k, m, n from a line, which says no \"there is\" of as many",
        ),
        case(
            "an obtain of more names than the item's there is binds",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "import definition         stdlib/divisibility/odd\n\ntheorem planted\n  let b ∈ ℤ    (H1)\n  assume b is odd    (H2)\n  then b = b\n\n1.  j ∈ ℤ. i ∈ ℤ. b = 2j + 1.\n    obtain j, i: def:odd n := b, from H2\n\n2.  b = b\n    algebra\n".to_string(),
            )],
            "step 1 obtains j, i from def:odd, which says no \"there is\" of as many",
        ),
        case(
            "obtain from a line of several sentences a body it does not say",
            vec![edit(
                "proofs/zz/obtain-several.proof",
                None,
                "theorem obtain-several\n  assume 1 = 1                                                        (H1)\n  assume there is n ∈ ℕ with n = 1                                    (H2)\n  then 2 ∈ ℕ\n\n1.  1 = 1. There is n ∈ ℕ with n = 1.\n    join H1, H2\n\n2.  P ∈ ℕ. P = 2.\n    obtain P from line 1\n\n3.  2 ∈ ℕ\n    substitute P = 2 (line 2) into line 2\n".to_string(),
            )],
            "step 2 claims other than what it obtains, which says P = 1",
        ),
        case(
            "obtain from a line of several sentences none of them a there is",
            vec![edit(
                "proofs/zz/obtain-none.proof",
                None,
                "theorem obtain-none\n  assume 1 = 1                                                        (H1)\n  assume 2 = 2                                                        (H2)\n  then 1 ∈ ℕ\n\n1.  1 = 1. 2 = 2.\n    join H1, H2\n\n2.  P ∈ ℕ. P = 1.\n    obtain P from line 1\n\n3.  1 ∈ ℕ\n    substitute P = 1 (line 2) into line 2\n".to_string(),
            )],
            "step 2 obtains P from a line, which says no \"there is\"",
        ),
        case(
            "exhibit from a line that says nothing of the value",
            vec![edit(
                "proofs/zz/exhibit-unrelated.proof",
                None,
                "theorem exhibit-unrelated\n  let n ∈ ℤ                                                           (H1)\n  let M ∈ ℤ                                                           (H2)\n  assume M = 2                                                        (H3)\n  then there is q ∈ ℤ with q = n\n\n1.  there is q ∈ ℤ with q = n\n    exhibit, from H3\n".to_string(),
            )],
            "step 1 cites H3 and uses nothing it says",
        ),
        case(
            "instantiate a part of a line at more values than it quantifies",
            vec![edit(
                "proofs/zz/instantiate-over.proof",
                None,
                "theorem instantiate-over\n  assume (for all x ∈ ℝ, for all y ∈ ℝ, x + y = y + x) and (for all x ∈ ℝ, x + 0 = x)   (H1)\n  then 1 + 0 = 1\n\n1.  1 + 0 = 1\n    instantiate x := 1, y := 2 in H1\n".to_string(),
            )],
            "H1 at those terms says 1 + 2 = 2 + 1, and the step claims 1 + 0 = 1",
        ),
        case(
            "obtain a part of a set the there is does not give",
            vec![edit(
                "proofs/zz/obtain-part.proof",
                None,
                "theorem obtain-part\n  let A be a set                                                      (H1)\n  let B be a set                                                      (H2)\n  assume there is X ⊆ A with X = A                                    (H3)\n  then A ⊆ B\n\n1.  X ⊆ B. X = A.\n    obtain X from H3\n\n2.  A ⊆ B\n    substitute X = A (line 1) into line 1\n".to_string(),
            )],
            "step 1 claims X ⊆ B, and what it obtains says X ⊆ A",
        ),
        case(
            "obtain from a line saying two there is",
            vec![edit(
                "proofs/zz/obtain-two.proof",
                None,
                "theorem obtain-two\n  assume there is n ∈ ℕ with n = 1                                    (H1)\n  assume there is m ∈ ℕ with m = 2                                    (H2)\n  then 1 ∈ ℕ\n\n1.  There is n ∈ ℕ with n = 1. There is m ∈ ℕ with m = 2.\n    join H1, H2\n\n2.  P ∈ ℕ. P = 1.\n    obtain P from line 1\n\n3.  1 ∈ ℕ\n    substitute P = 1 (line 2) into line 2\n".to_string(),
            )],
            "step 2 obtains P from a line, which says more than one \"there is\"",
        ),
        // `divides-difference` asks that d divide b, which line 5.2 says.
        case(
            "drop a line a citation needs for a hypothesis",
            vec![
                edit("proofs/wiedijk/infinitely-many-primes.proof", Some("mun:divides-difference d := p, a := n! + 1, b := n!, from 3, 5.2".to_string()), "mun:divides-difference d := p, a := n! + 1, b := n!, from 3".to_string()),
            ],
            "does not supply",
        ),
        // `mod-natural` asks b ∈ ℕ, and IH1 says b(k) ∈ ℕ₀: a function's
        // value is in what a line says it is in, and ℕ₀ holds 0.
        case(
            "supply a hypothesis with the wrong number system",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("mun:mod-natural, from 3.5.8\n".to_string()), "mun:mod-natural, from IH1\n".to_string()),
            ],
            "does not supply",
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
                edit("proofs/wiedijk/rationals-countable.proof", Some("def:abs x := numer(x), from C1\n                  requires numer(x) ∈ ℤ: mun:lowest-terms-parts\n".to_string()), "def:abs x := numer(x), from C1\n                  requires |numer(x)| ∈ ℕ₀: mun:abs-integer z := numer(x)\n                  requires numer(x) ∈ ℤ: mun:lowest-terms-parts\n".to_string()),
            ],
            "the requires line of step 4.3.2 cites mun:abs-integer, which asks for numer(x) ∈ ℤ, and what it cites does not supply it",
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
        // What `be` says of a function is asked for, as a membership is.
        case(
            "cite an item without the line saying its function is one-to-one",
            vec![
                edit("proofs/wiedijk/schroeder-bernstein.proof", Some("          mun:inverse-value, from H4, 3.5\n".to_string()), "          mun:inverse-value, from 3.5\n".to_string()),
            ],
            "step 3.7 cites mun:inverse-value, which asks for",
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
        case(
            "reorder a product by a map not shown to be one-to-one",
            vec![
                edit("proofs/wiedijk/euler.proof", Some("thm:product-reorder, from 4, 5, 9".to_string()), "thm:product-reorder, from 4, 5, 8".to_string()),
            ],
            "step 10 cites thm:product-reorder, which asks for",
        ),
        // `let p be a polynomial` says p is one, and an item asking that of
        // what it is cited at asks it of the lines the step names.
        case(
            "divide by x − a without saying p is a polynomial",
            vec![
                edit("proofs/wiedijk/factor.proof", Some("thm:remainder, from H1".to_string()), "thm:remainder".to_string()),
            ],
            "step 1 cites thm:remainder, which asks for p is a polynomial",
        ),
        // `inequalities` takes two terms differing only from a line it cites:
        // r ≠ 0 written above for 0 < r to rest on is asked for by nothing.
        case(
            "write r ≠ 0 above an inequalities line instead of citing it",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("          requires 0 < r: inequalities, from S, 1\n".to_string()), "          requires r ≠ 0: from S\n          requires 0 < r: inequalities, from 1\n".to_string()),
            ],
            "the requires line of step 3.1 says r ≠ 0, and neither mun:pos-int-nat nor the step's other lines ask for it",
        ),
        // An exhibit's lines say each part of its body at the value, a
        // numeral's facts among them, and what is missing is named.
        case(
            "exhibit 2 for a d > 1 without saying 2 > 1",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("          requires 2 > 1: arithmetic\n".to_string()), String::new()),
            ],
            "step 2.14 exhibits d := 2, so it needs 2 > 1, and nothing it cites or requires says it",
        ),
        // An instantiation's value is in what its letter ranges over, as a
        // line the step names says: −f(c) > 0 says nothing of ℝ, and without
        // line 13, which puts c in f's domain, nothing says f(c) is real.
        case(
            "instantiate ε := −f(c) without saying −f(c) is real",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("ε := −f(c) in line 15, from H4, 13, 16.3\n".to_string()), "ε := −f(c) in line 15, from H4, 16.3\n".to_string()),
            ],
            "step 16.4 puts −f(c) for ε in line 15, so it needs −f(c) ∈ ℝ, and nothing it cites or requires says it",
        ),
        // `let k ∈ ℕ` says k ≥ 1 beyond the membership, and a step using it
        // cites the line: sum-extended asks n ≥ a at n := k, a := 1.
        case(
            "lean on let k ∈ ℕ for k ≥ 1 without citing it",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("          requires k ≥ 1: from K\n".to_string()), String::new()),
            ],
            "step 1.2 cites mun:sum-extended, which asks for",
        ),
        // A letter's membership is said where it is introduced, and a line
        // cited only for it does no work: H2 says c ∈ ℝ, and abs-nonneg asks
        // nothing else of it.
        case(
            "cite a let line only for the membership it introduces",
            vec![
                edit("proofs/hammack/constant-multiple-limit.proof", Some("1.  |c| ≥ 0\n    mun:abs-nonneg x := c\n".to_string()), "1.  |c| ≥ 0\n    mun:abs-nonneg x := c, from H2\n".to_string()),
            ],
            "step 1 cites H2, and mun:abs-nonneg asks for nothing it says",
        ),
        // The same of an obtain's sentence `p ∈ ℤ`: even-square asks
        // p ∈ ℤ at n := p, which 2.1 says once, where it obtains p.
        case(
            "cite an obtain only for the membership it states",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("          thm:even-square n := p, from 2.4\n".to_string()), "          thm:even-square n := p, from 2.1, 2.4\n".to_string()),
            ],
            "step 2.5 cites 2.1, and thm:even-square asks for nothing it says",
        ),
        case(
            "an exhibit citing nothing that says the claim of a value",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("    exhibit, from 19\n".to_string()), "    exhibit, from 17\n".to_string()),
            ],
            "step 20 exhibits a value, and nothing it cites or requires says the claim's body of any one value",
        ),
        case(
            "an identity element dropped from the middle with nothing saying what is left is a number",
            vec![
                edit("tests/elaborator/textbook-exercise-shapes.proof", Some("    requires b(k) ∈ ℝ: from H1\n".to_string()), String::new()),
            ],
            "step 2 drops an identity element from what the substitution makes, and nothing says b(k) is a number",
        ),
        // An instantiation's values are for the line's leading "for all"
        // letters, outermost first.
        case(
            "instantiate a line no for-all of which binds the name",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  assume x > 0    (H2)\n  then x > 0\n\n1.  x > 0\n    instantiate y := x in H2\n".to_string(),
            )],
            "step 1 instantiates H2, which claims nothing of every such name",
        ),
        case(
            "instantiate a line with more values than it binds",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  assume for all y ∈ ℝ, y² ≥ 0    (H1)\n  let x ∈ ℝ    (H2)\n  then x² ≥ 0\n\n1.  x² ≥ 0\n    instantiate y := x, z := x in H1\n".to_string(),
            )],
            "step 1 instantiates H1, which quantifies fewer names than the step gives values",
        ),
        case(
            "instantiate a line's inner letter and not its outer one",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  assume for all y ∈ ℝ, for all z ∈ ℝ, y + z = z + y    (H1)\n  let x ∈ ℝ    (H2)\n  then for all y ∈ ℝ, y + x = x + y\n\n1.  For all y ∈ ℝ, y + x = x + y.\n    instantiate z := x in H1\n".to_string(),
            )],
            // H1 read at the header's x gives z its value and none other.
            "H1 at those terms says x + x = x + x",
        ),
        // A cited item's group identity is the citing proof's, and no letter
        // a hypothesis on it can be met by.
        case(
            "cite an item whose hypothesis on the identity nothing says",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "import axiom              stdlib/groups/group-identity\n\ntheorem planted-lemma\n  let G be a group with operation · and identity e    (H1)\n  let x ∈ G    (H2)\n  assume x = e    (H3)\n  then x·x = x\n\n1.  x·e = x\n    axi:group-identity, from H2\n\n2.  x·x = x\n    substitute x = e (H3) into line 1\n\ntheorem planted\n  let G be a group with operation · and identity e    (H1)\n  let a ∈ G    (H2)\n  then a·a = a\n\n1.  a·a = a\n    thm:planted-lemma x := a, from H2\n".to_string(),
            )],
            "step 1 cites thm:planted-lemma, which asks for a = e, and what it cites does not supply it",
        ),
        // A hypothesis an obtain's item asks and nothing supplies is named
        // once, and alone: d ∈ ℤ at d := 2 is said once.
        case(
            "an obtain whose item asks a membership nothing says",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "import definition         stdlib/divisibility/divides\n\ntheorem planted\n  let A ∈ ℤ    (H1)\n  let B = 2A + 1    (D1)\n      reads the odd number after 2A\n  assume 2 divides B    (H2)\n  then B = B\n\n1.  k ∈ ℤ. B = 2·k.\n    obtain k: def:divides d := 2, n := B, from H2\n\n2.  B = B\n    algebra\n".to_string(),
            )],
            "step 1 cites def:divides, which asks for B ∈ ℤ, and what it cites does not supply it",
        ),
        // An exhibit gives a value of a "there is".
        case(
            "exhibit what is no there is",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  assume x > 0    (H2)\n  then x > 0\n\n1.  x > 0\n    exhibit, from H2\n".to_string(),
            )],
            "step 1 is an exhibit, and x > 0 is no \"there is\" for it to give a value of",
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
    ]
}
