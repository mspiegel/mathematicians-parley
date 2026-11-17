//! The planted cases about calculations: rows, chains and links, substitute, restate, transitivity and antisymmetry.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
        // An inequalities step's rows: the cited line written out, then the
        // row above with the manipulation each reason names, the last the
        // claim.
        case(
            "an inequality row with no reason",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      2·A < A + B          algebra\n".to_string()),
                "      2·A < A + B          because\n".to_string(),
            )],
            "a row gives no reason",
        ),
        case(
            "an inequality row that is no single relation",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      x = y                restate\n".to_string()),
                "      x = y and y = x      restate\n".to_string(),
            )],
            "a row of step 1 is no single relation of =, ≠, <, ≤, > or ≥",
        ),
        // `symmetry` is kept back for later: a row turning a relation round
        // says `restate`.
        case(
            "turn an inequality row round with symmetry",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      x = y                restate\n".to_string()),
                "      x = y                symmetry\n".to_string(),
            )],
            "`symmetry` is kept back for later; a row turning a relation round is `restate`",
        ),
        case(
            "inequality rows starting from no cited line",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      A < B                H3\n".to_string()),
                "      A < B                H2\n".to_string(),
            )],
            "the first row of step 1 is not a line the step cites, written out with its label as its reason",
        ),
        case(
            "an inequality row that is not the manipulation it names",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      2·A < A + B          algebra\n".to_string()),
                "      3·A < A + B          algebra\n".to_string(),
            )],
            "a row of step 1 is not the row above with a side written as the same number another way",
        ),
        case(
            "inequality rows ending other than on the claim",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      0 < x                H2\n      0 ≠ x                weakening\n      x ≠ 0                restate\n".to_string()),
                "      0 < x                H2\n      0 ≤ x                weakening\n".to_string(),
            )],
            "the last row of step 1 is not its claim",
        ),
        case(
            "restate an equation of a chain its neighbours do not write",
            vec![edit(
                "tests/elaborator/reading-equations.proof",
                Some("theorem a-chain-pair-substituted\n".to_string()),
                "theorem a-chain-pair-joined\n  let a ∈ ℝ    (H1)\n  let b ∈ ℝ    (H2)\n  let c ∈ ℝ    (H3)\n  assume a = b = c    (H4)\n  then a = c\n\n1.  a = c\n    restate H4\n\ntheorem a-chain-pair-substituted\n".to_string(),
            )],
            "step 1 restates H4 and claims a = c, which no line it restates says",
        ),
        case(
            "restate a bound a range line says without writing it",
            vec![edit(
                "tests/elaborator/reading-memberships.proof",
                Some("theorem a-range-bound-in-a-requires-line\n".to_string()),
                "theorem a-range-bound-joined\n  let n ∈ ℤ    (H1)\n  let k ∈ {1, …, n}    (H2)\n  then k ≤ n\n\n1.  k ≤ n\n    restate H2\n\ntheorem a-range-bound-in-a-requires-line\n".to_string(),
            )],
            "step 1 restates H2 and claims k ≤ n, which no line it restates says",
        ),
        case(
            "restate a bound a membership implies",
            vec![edit(
                "tests/elaborator/reading-memberships.proof",
                Some("theorem a-range-bound-in-a-requires-line\n".to_string()),
                "theorem a-membership-bound-joined\n  let k ∈ ℕ    (H1)\n  then k ≥ 1\n\n1.  k ≥ 1\n    restate H1\n\ntheorem a-range-bound-in-a-requires-line\n".to_string(),
            )],
            "step 1 restates H1 and claims k ≥ 1, which no line it restates says",
        ),
        case(
            "restate the members a subset line says without writing them",
            vec![edit(
                "tests/elaborator/reading-memberships.proof",
                Some("theorem a-range-bound-in-a-requires-line\n".to_string()),
                "theorem a-subset-joined-as-its-members\n  let X ⊆ ℤ    (H1)\n  then for all x ∈ X, x ∈ ℤ\n\n1.  For all x ∈ X, x ∈ ℤ.\n    restate H1\n\ntheorem a-range-bound-in-a-requires-line\n".to_string(),
            )],
            "step 1 restates H1 and claims",
        ),
        // A calculation claims its first term by the chain's relation to
        // its last: a chain with a `>` link claims `>`.
        case(
            "a calculation claiming a weaker relation than its chain gives",
            vec![edit(
                "tests/elaborator/reading-equations.proof",
                Some("theorem a-chain-pair-in-a-calculation-link\n".to_string()),
                "theorem a-weaker-calculation-claim\n  let a ∈ ℝ    (H1)\n  let b ∈ ℝ    (H2)\n  let c ∈ ℝ    (H3)\n  assume a = b    (H4)\n  assume b > c    (H5)\n  then a ≥ c\n\n1.  a ≥ c\n    calculation\n      a = b    H4\n        > c    H5\n\ntheorem a-chain-pair-in-a-calculation-link\n".to_string(),
            )],
            "step 1 claims a ≥ c, and its chain gives a > c",
        ),
        case(
            "a calculation claiming other than its chain's ends",
            vec![edit(
                "tests/elaborator/reading-equations.proof",
                Some("theorem a-chain-pair-in-a-calculation-link\n".to_string()),
                "theorem a-calculation-claiming-other-ends\n  let a ∈ ℝ    (H1)\n  let b ∈ ℝ    (H2)\n  let c ∈ ℝ    (H3)\n  assume a = b    (H4)\n  assume b > c    (H5)\n  then a > b\n\n1.  a > b\n    calculation\n      a = b    H4\n        > c    H5\n\ntheorem a-chain-pair-in-a-calculation-link\n".to_string(),
            )],
            "step 1 claims a > b, and its chain gives a > c",
        ),
        case(
            "a calculation claiming a congruence modulo another number",
            vec![edit(
                "tests/elaborator/reading-equations.proof",
                Some("theorem a-chain-pair-in-a-calculation-link\n".to_string()),
                "theorem a-congruence-claimed-modulo-another\n  let a ∈ ℤ    (H1)\n  let b ∈ ℤ    (H2)\n  let c ∈ ℤ    (H3)\n  assume a = b    (H4)\n  assume b ≡ c (mod 3)    (H5)\n  then a ≡ c (mod 6)\n\n1.  a ≡ c (mod 6)\n    calculation\n      a = b    H4\n        ≡ c (mod 3)    H5\n\ntheorem a-chain-pair-in-a-calculation-link\n".to_string(),
            )],
            "step 1 claims a ≡ c (mod 6), and its chain gives a ≡ c (mod 3)",
        ),
        // A line saying several relations gives a chain the one that makes
        // a chain to the claim, and one saying two that both do gives the
        // chain nothing.
        case(
            "chain a line two of whose relations both reach the claim",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("  assume 0 < a and a ≤ b    (H4)\n".to_string()),
                "  assume a < b and a ≤ b    (H4)\n".to_string(),
            )],
            "step 1 cites lines by transitivity that say several relations, and more than one choice of them reaches the claim",
        ),
        // A requires line naming a manipulation is its one line with it: q >
        // 0 weakened is q ≠ 0, and no weakening of it is q ≠ 1.
        case(
            "a requires line naming a manipulation its line does not take",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("    requires q ≠ 0: weakening, from H3\n".to_string()),
                "    requires q ≠ 1: weakening, from H3\n".to_string(),
            )],
            "the requires line q ≠ 1 of step 1 is not H3 with its relation weakened",
        ),
        // In rows, turning a relation round is a restate row of its own: the
        // first row is the cited line as written, each row keeps its sides
        // where its manipulation leaves them, and the last row is the claim
        // as written. A row that turns as well as manipulates is told which.
        case(
            "write the first row as the line it cites turned round",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      A < B                H3\n".to_string()),
                "      B > A                H3\n".to_string(),
            )],
            "the first row of step 1 is the line it cites turned round; write the line as it is written, and turn it with a restate row",
        ),
        case(
            "turn a row round as well as multiplying it",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      −x > 0               multiplying by −1\n      0 < −x               restate\n".to_string()),
                "      0 < −x               multiplying by −1\n".to_string(),
            )],
            "a row of step 1 is the row above with both sides multiplied by −1, a numeral other than 0, turned round; turning it round is a restate row of its own",
        ),
        case(
            "end the rows on the claim turned round",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      0 ≠ x                weakening\n      x ≠ 0                restate\n".to_string()),
                "      0 ≠ x                weakening\n".to_string(),
            )],
            "the last row of step 1 is its claim turned round; end with a restate row that writes the claim as it is written",
        ),
        case(
            "turn a requires line round as well as weakening it",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("    requires 0 ≠ q: weakening, from H3\n".to_string()),
                "    requires q ≠ 0: weakening, from H3\n".to_string(),
            )],
            "the requires line q ≠ 0 of step 2 is H3 with its relation weakened, turned round; a requires line names one manipulation, so write it as the manipulation leaves it: 0 ≠ q",
        ),
        // A transitivity step chains relations, each line's right side the
        // next one's left, and claims the ends by the chain's relation;
        // antisymmetry takes an order and its converse to an equation.
        case(
            "transitivity citing a line that is no relation",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("    transitivity, from H4, H5\n".to_string()),
                "    transitivity, from H1, H5\n".to_string(),
            )],
            "step 1 cites H1 by transitivity, and H1 states no relation of =, <, ≤, > or ≥",
        ),
        case(
            "transitivity chaining orders going both ways",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("  assume b ≥ a    (H5)\n".to_string()),
                "  assume b ≤ a    (H5)\n".to_string(),
            )],
            "step 1 chains orders going up and going down, which say nothing of its ends",
        ),
        case(
            "transitivity over lines that do not meet",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("  assume b < c    (H5)\n".to_string()),
                "  assume c < c + 1    (H5)\n".to_string(),
            )],
            "the lines step 1 chains do not meet: H4 ends at b, and H5 starts from c",
        ),
        case(
            "transitivity claiming other than the chain's ends",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("1.  a < c\n    transitivity, from H4, H5\n".to_string()),
                "1.  a ≤ c\n    transitivity, from H4, H5\n".to_string(),
            )],
            "step 1 claims a ≤ c, and the chain it cites gives a < c",
        ),
        case(
            "antisymmetry of a strict order",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("  assume a ≥ b    (H4)\n".to_string()),
                "  assume a > b    (H4)\n".to_string(),
            )],
            "step 1 cites by antisymmetry what is not two lines a ≤ b and b ≤ a, an order and its converse",
        ),
        case(
            "antisymmetry claiming other than the equation of its sides",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("1.  b = a\n    antisymmetry".to_string()),
                "1.  b = b\n    antisymmetry".to_string(),
            )],
            "step 1 claims b = b, and its lines give a = b",
        ),
        // A calculation's row citing a define is what the define makes its
        // name: D1 makes G(a, 0) the sum to 0, and G(a, 1) the sum to 1.
        case(
            "a calculation row citing a define for what it does not make",
            vec![edit(
                "proofs/wiedijk/geometric-series.proof",
                Some("            G(a, 0) = ".to_string()),
                "            G(a, 1) = ".to_string(),
            )],
            "a^j is not what D1 makes it",
        ),
        // `substitute` walks its equation both ways and each sentence of the
        // line it names, trying the next where one declines. A name the proof
        // never introduced is not one of those: it is a defect.
        case(
            "substitute a name the proof never introduced",
            vec![edit(
                "proofs/wiedijk/pythagorean-triples.proof",
                Some("                  substitute c = 2r (line 2.2.7) into line 2.2.3".to_string()),
                "                  substitute c = z (line 2.2.7) into line 2.2.3".to_string(),
            )],
            "step 2.2.8 takes c = z from 2.2.7, which does not say it",
        ),
        // A substitution's line may leave out the + 0 it makes, and nothing
        // else: the product written the other way round is a reordering, which
        // no identity law gives.
        case(
            "a substitution that reorders where it drops a 0",
            vec![edit(
                "proofs/wiedijk/factor.proof",
                Some("    2.1.  p(x) = (x − a)·q(x)\n".to_string()),
                "    2.1.  p(x) = q(x)·(x − a)\n".to_string(),
            )],
            "step 2.1 claims p(x) = q(x) · (x − a), which putting one side of p(a) = 0 for the other does not make",
        ),
        // `join` infers nothing: a chain is the equations between its
        // neighbouring terms, and from x = y and x = z the neighbour y = z
        // is a deduction.
        case(
            "join a chain from equations that are not its links",
            vec![edit(
                "tests/elaborator/chains.proof",
                Some("  assume x = y                                                        (H5)\n  assume y = z                                                        (H6)\n  assume z = w                                                        (H7)".to_string()),
                "  assume x = y                                                        (H5)\n  assume x = z                                                        (H6)\n  assume z = w                                                        (H7)".to_string(),
            )],
            "step 1 joins H5, H6, H7 and claims y = z, which no line it joins says",
        ),
        // Only a chain supplies the equation between terms that are not
        // neighbours: two sentences saying x = y and y = z supply those two.
        case(
            "take a pair from two sentences that are not a chain",
            vec![edit(
                "tests/elaborator/chains.proof",
                Some("  assume x = y = z. x + 1 = 5.                                        (H4)".to_string()),
                "  assume x = y. y = z. x + 1 = 5.                                     (H4)".to_string(),
            )],
            "step 1 takes x = z from H4, which does not say it",
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
        case(
            "restate a sentence the restated line does not say",
            vec![edit(
                "proofs/wiedijk/euclid.proof",
                Some("    3.3.  a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀\n          join 3.1, 3.2".to_string()),
                "    3.3.  a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀\n          restate 3.1".to_string(),
            )],
            "which no line it restates says",
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
        // A substitution puts one side for the other and reorders nothing.
        case(
            "substitute into a line, claiming its product the other way round",
            vec![edit(
                "proofs/wiedijk/bezout.proof",
                Some("4.  c = q·d\n    substitute r = 0 (line 3) into line 1".to_string()),
                "4.  c = d·q\n    substitute r = 0 (line 3) into line 1".to_string(),
            )],
            "step 4 claims c = d · q, which putting one side of r = 0 for the other does not make",
        ),
        case(
            "substitute with no line, claiming more than the equation puts in",
            vec![edit(
                "proofs/wiedijk/liouville.proof",
                Some("10. |q^N|·|F(p/q)| = q^N·|F(p/q)|\n".to_string()),
                "10. |q^N|·|F(p/q)| = q^(N + 1)·|F(p/q)|\n".to_string(),
            )],
            "step 10 claims |q^N| · |F(p / q)| = q^(N + 1) · |F(p / q)|, which putting one side of |q^N| = q^N for the other does not make",
        ),
        // A requires line whose reason is `substitute` is checked as the step
        // it would be. H16, ∠QHS = 90°, has no line XY for an equation of
        // lines to be put into.
        case(
            "a requires line putting an equation into a line without its side",
            vec![edit(
                "corpus/stdlib/geometry.proof",
                Some("    requires Q is not on line HK: mun:off-line-along A := H, B := S, X := K, P := Q, from H15, 6, 8\n".to_string()),
                "    requires Q is not on line HK: substitute line HK = line XY (line 7) into H16\n".to_string(),
            )],
            "step 9 claims Q is not on line HK, which putting one side of line HK = (line XY) for the other does not make",
        ),
        // A point on a line is a member of the line, the set
        // (`rules::OTHER_FORMS`), so an equation of lines is put into "H is
        // on line QR" to make "H is on line QS". Put into a line about
        // another point, S, it makes no claim about H.
        case(
            "substitute an equation of lines whose side the line does not write",
            vec![edit(
                "corpus/stdlib/geometry.proof",
                Some("    substitute line QS = line QR (line 2) into H10\n".to_string()),
                "    substitute line QS = line QR (line 2) into H8\n".to_string(),
            )],
            "step 3 claims H is on line QS, which putting one side of line QS = (line QR) for the other does not make",
        ),
        // One substitution takes one equation from one source: a second
        // would be read as part of the first equation.
        case(
            "two substitutions in one step",
            vec![
                edit("proofs/wiedijk/angle-sum.proof", Some("      substitute line 2\n".to_string()), "      substitute ∠DBA = ∠BAC (line 2), ∠EBC = ∠BCA (line 3)\n".to_string()),
            ],
            "matches no production",
        ),
        // Line 15 of intermediate-value still binds δ once c′ and ε are given,
        // so a value naming δ would be caught by it.
        case(
            "substitute a term that captures a bound variable",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("           instantiate c′ := c, ε := −f(c) in line 15, from H4, 13, 16.3".to_string()), "           instantiate c′ := c, ε := −f(δ) in line 15, from H4, 13, 16.3".to_string()),
            ],
            "may not capture",
        ),
        // The same, with a comma inside the value: the pair is read whole.
        case(
            "substitute a term with a comma that captures a bound variable",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("           instantiate c′ := c, ε := −f(c) in line 15, from H4, 13, 16.3".to_string()), "           instantiate c′ := c, ε := −f(c)·|[δ, c]| in line 15, from H4, 13, 16.3".to_string()),
            ],
            "may not capture",
        ),
        // A calculation's link cites the line that says it, and a line saying
        // a(0) = M does not say what substituting it inside a gcd gives.
        case(
            "cite an equation for a link that substitutes it inside a term",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("            gcd(a(0), b(0)) = gcd(M, b(0))     substitute line 1".to_string()), "            gcd(a(0), b(0)) = gcd(M, b(0))     1".to_string()),
            ],
            "cites 1, which does not say gcd(a(0), b(0)) = gcd(M, b(0))",
        ),
        case(
            "a chain link saying a modulus after a relation that is not ≡",
            vec![
                edit("proofs/wiedijk/divisibility-by-three.proof", Some("                 ≡ 1 (mod 3)      arithmetic".to_string()), "                 = 1 (mod 3)      arithmetic".to_string()),
            ],
            "says (mod 3) after a relation that is not ≡",
        ),
        // A calculation joins lines; the reasoning is in the lines it cites.
        case(
            "a calculation with no chain",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("    calculation\n      Σ(k = 1 to n) k = S(n)              D1\n                      = n(n + 1)/2        instantiate k := n in line 1".to_string()), "    calculation".to_string()),
            ],
            "step 2 is a calculation with no chain",
        ),
        case(
            "a chain line substituting a line that says no equation",
            vec![
                edit("tests/elaborator/a-chain-showing-its-work.proof", Some("      f(2) = 2 + 1      instantiate x := 2 in H2".to_string()), "      f(2) = 2 + 1      substitute H1".to_string()),
            ],
            "substitutes H1, which says no equation to put",
        ),
        case(
            "a chain line substituting an equation that does not make its link",
            vec![
                edit("tests/elaborator/a-chain-showing-its-work.proof", Some("      n² = (2k + 1)²           substitute line 1".to_string()), "      n² = (2k + 2)²           substitute line 1".to_string()),
            ],
            "is not one side of an equation 1 says put for the other",
        ),
        case(
            "a substitute's first row that its line does not say",
            vec![
                edit("tests/elaborator/substitute-rows.proof", Some("      d divides (n + 1) − n      1".to_string()), "      d divides (n + 2) − n      1".to_string()),
            ],
            "the first row of step 2 writes d divides (n + 2) − n, which 1 does not say",
        ),
        case(
            "a substitute's last row that is not its claim",
            vec![
                edit("tests/elaborator/substitute-rows.proof", Some("1.  12 < y\n    substitute".to_string()), "1.  12 ≤ y\n    substitute".to_string()),
            ],
            "the last row of step 1 writes 12 < y, and the step claims 12 ≤ y",
        ),
        case(
            "a substitute that writes neither an equation nor rows",
            vec![
                edit("tests/elaborator/substitute-rows.proof", Some("    substitute\n      x·x + x < y      H4\n      3·3 + 3 < y      substitute H3\n      12 < y           arithmetic\n".to_string()), "    substitute\n".to_string()),
            ],
            "step 1 substitutes nothing",
        ),
        case(
            "a substitute's row that changes nothing",
            vec![
                edit("tests/elaborator/substitute-rows.proof", Some("      3·3 + 3 < y      substitute H3".to_string()), "      x·x + x < y      substitute H3".to_string()),
            ],
            "the row is the row above it, and changes nothing",
        ),
        case(
            "a substitute's row that makes two changes",
            vec![
                edit("tests/elaborator/substitute-rows.proof", Some("      3·3 + 3 < y      substitute H3".to_string()), "      3·3 + 3 < 2·y    substitute H3".to_string()),
            ],
            "the row makes more than one change to the row above it",
        ),
        case(
            "a substitute's row whose reason does not give its change",
            vec![
                edit("tests/elaborator/substitute-rows.proof", Some("      d divides 1                algebra".to_string()), "      d divides 2                algebra".to_string()),
            ],
            "is not an identity",
        ),
        case(
            "a substitute's later row citing a line",
            vec![
                edit("tests/elaborator/substitute-rows.proof", Some("      3·3 + 3 < y      substitute H3".to_string()), "      3·3 + 3 < y      H3".to_string()),
            ],
            "one that uses H3's equation is `substitute H3`",
        ),
        case(
            "a chain line with no relation",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("                 = 1                     mun:sum-single a := 1".to_string()), "                 1                       mun:sum-single a := 1".to_string()),
            ],
            "chain line carries no relation",
        ),
        case(
            "a chain line citing two lines",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("            S(k + 1) = S(k) + (k + 1)               1.2".to_string()), "            S(k + 1) = S(k) + (k + 1)               D1, 1.2".to_string()),
            ],
            "a calculation line cites one line or label, and this one cites D1, 1.2",
        ),
        case(
            "a chain that turns round",
            vec![
                edit("tests/elaborator/a-chain-going-down.proof", Some("        > c       H5".to_string()), "        < c       H5".to_string()),
            ],
            "a chain goes one way, and this line says < after one saying ≥",
        ),
        case(
            "substitute into a define",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  assume x = 1    (H2)\n  then x + 1 = 2\n\nlet y = x + 1, a real number    (D1)\n    membership\n    reads one more than x\n\n1.  y = 1 + 1\n    substitute x = 1 (H2) into D1\n\n2.  x + 1 = 2\n    algebra, from H2\n".to_string(),
            )],
            "step 1 puts its equation into D1, which is a define and no line; a step citing D1 writes the line it gives",
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
    ]
}
