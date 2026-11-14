//! Part 3 of 6 of the planted cases, in the order they are run.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
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
        case(
            "cite a line that comes after the step",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("    16.2.  c < b\n           inequalities, from 12, 16.1".to_string()), "    16.2.  c < b\n           inequalities, from 12, 16.3".to_string()),
            ],
            "step 16.2 cites line 16.3, which comes after it",
        ),
        case(
            "cite a line that does not exist",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    2.5.  p is even\n          thm:even-square n := p, from 2.4".to_string()), "    2.5.  p is even\n          thm:even-square n := p, from 2.99".to_string()),
            ],
            "does not exist",
        ),
        case(
            "cite the assumption of another case",
            vec![
                edit("proofs/wiedijk/triangle-inequality.proof", Some("    2.9.  x < |x|\n          transitivity, from C2, 2.8, 2.6".to_string()), "    2.9.  x < |x|\n          transitivity, from C2, 2.8, 2.6, C1".to_string()),
            ],
            "not in scope",
        ),
        case(
            "a justification that matches no production",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("         = 4k² + 4k + 1        algebra\n".to_string()), "         = 4k² + 4k + 1        algebra from 1 and 2\n".to_string()),
            ],
            "matches no production",
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
        case(
            "import an item that is not in the database",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("import mundane theorem    stdlib/sets/set-builder-subset\n".to_string()), "import mundane theorem    stdlib/sets/set-builder-nonesuch\n".to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("    mun:set-builder-subset, from D1".to_string()), "    mun:set-builder-nonesuch, from D1".to_string()),
            ],
            "import mundane theorem stdlib/sets/set-builder-nonesuch: stdlib/sets holds no item set-builder-nonesuch",
        ),
        case(
            "import an item from a library file that does not exist",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("import mundane theorem    stdlib/sets/set-builder-subset\n".to_string()), "import mundane theorem    stdlib/nonesuch/set-builder-subset\n".to_string()),
            ],
            "import mundane theorem stdlib/nonesuch/set-builder-subset: stdlib/nonesuch is no file",
        ),
        case(
            "cite an item the file does not import",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("    mun:set-builder-subset, from D1".to_string()), "    mun:subset-transitive, from D1".to_string()),
            ],
            "mun:subset-transitive is neither imported nor a theorem of this file",
        ),
        // An import says where an item comes from, so a citation does not.
        case(
            "cite an item by its path",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("    mun:set-builder-subset, from D1".to_string()), "    mun:stdlib/sets/set-builder-subset, from D1".to_string()),
            ],
            "mun:stdlib/sets/set-builder-subset is cited by its path",
        ),
        case(
            "use def: for something that is mundane",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    mun:even-or-odd\n".to_string()), "    def:even-or-odd\n".to_string()),
            ],
            "def:even-or-odd names a mundane",
        ),
        case(
            "cite a mundane item as a theorem",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    mun:even-or-odd\n".to_string()), "    thm:even-or-odd\n".to_string()),
            ],
            "thm:even-or-odd names a mundane",
        ),
        case(
            "cite an axiom as a theorem",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("obtain c: axi:completeness".to_string()), "obtain c: thm:completeness".to_string()),
            ],
            "thm:completeness names an axiom",
        ),
        case(
            "number a step under a parent that does not exist",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("1.  B ⊆ A\n    mun:set-builder-subset, from D1".to_string()), "1.9.4.  B ⊆ A\n    mun:set-builder-subset, from D1".to_string()),
            ],
            "does not exist",
        ),
        case(
            "use a part marker the method does not declare",
            vec![
                edit("proofs/wiedijk/triangle-inequality.proof", Some("    case\n    assume x ≥ 0".to_string()), "    base\n    assume x ≥ 0".to_string()),
            ],
            "is not one of the parts",
        ),
        case(
            "instantiate an item instead of a line",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("    instantiate u := b in line 9, from 7".to_string()), "    instantiate u := b in def:least-upper-bound, from 7".to_string()),
            ],
            "never an item",
        ),
        case(
            "a character that is in no notation record",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("= 1(1 + 1)/2            arithmetic".to_string()), "= 1(1 ⊕ 1)/2            arithmetic".to_string()),
            ],
            "is in no record",
        ),
        // U+2208 followed by a combining solidus looks like the not-an-element sign
        // and composes to it under NFC, so it is the decomposed form the rule bans.
        case(
            "text that is not in Normalisation Form C",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("2.  √2 ∉ ℚ".to_string()), "2.  √2 ∈\u{0338} ℚ".to_string()),
            ],
            "Normalisation Form C",
        ),
        case(
            "an item that says nothing about where it comes from",
            vec![
                edit("corpus/stdlib/sets.records", Some("mundane theorem powerset-empty\n  then        𝒫∅ = {∅}\n  metamath-proof pw0".to_string()), "mundane theorem powerset-empty\n  then        𝒫∅ = {∅}".to_string()),
            ],
            "powerset-empty has no `metamath-proof`",
        ),
        case(
            "a block whose method takes none",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("11. (m + 1) − (m + 1) = 0\n    algebra\n".to_string()), "11. (m + 1) − (m + 1) = 0\n    algebra\n\n    11.1.  m = m\n           algebra\n".to_string()),
            ],
            "takes no block",
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
        // `requires C ≠ B: def:triangle` unfolds a line saying A, B, C form a
        // triangle; cited, that line is what it rests on, and without it
        // nothing is.
        case(
            "unfold a triangle no line above says",
            vec![
                edit("proofs/euclid/thales.proof", Some("import theorem            stdlib/geometry/angle-sum\n".to_string()), "import theorem            stdlib/geometry/angle-sum\nimport definition         stdlib/geometry/triangle\n".to_string()),
                edit("proofs/euclid/thales.proof", Some("    mun:angle-along-segment P := A, Q := B, R := C, S := M, from H5, H6, 1\n".to_string()), "    mun:angle-along-segment P := A, Q := B, R := C, S := M, from H6, 1\n    requires C ≠ B: def:triangle P := A, Q := B, R := C\n".to_string()),
            ],
            "the requires line of step 7 needs something that def:triangle does not conclude",
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
        // A define of two arguments gives each one's domain in the order
        // the brackets name them (`SYNTAX.md`).
        case(
            "a define of two whose domains are out of order",
            vec![
                edit("proofs/wiedijk/geometric-series.proof", Some("for a ∈ ℝ, n ∈ ℕ₀".to_string()), "for n ∈ ℕ₀, a ∈ ℝ".to_string()),
            ],
            "define G(a, n) gives the domain of n",
        ),
        // An induction's step part assumes its own claim's statement, and
        // names that claim by the induction's number (`SYNTAX.md`).
        case(
            "an induction hypothesis naming another step",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("assume step 1 is true for k".to_string()), "assume step 2 is true for k".to_string()),
            ],
            "the induction hypothesis names step 2, and the induction is step 1",
        ),
        // It is for the letter the claim binds, and no other.
        case(
            "an induction hypothesis for another letter",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("assume step 1 is true for k".to_string()), "assume step 1 is true for j".to_string()),
            ],
            "the induction hypothesis is for j, and step 1 is said for all k",
        ),
        // The hypothesis is the claim's words where they stand; written out
        // again, the step part does not say it is the induction hypothesis.
        case(
            "a step part that writes its hypothesis out",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("    assume step 1 is true for k, the induction hypothesis             (IH)".to_string()), "    assume S(k) = k(k + 1)/2                                          (IH)".to_string()),
            ],
            "the step part of step 1 does not open with `let k ∈ ℕ` and `assume step 1 is true for k, the induction hypothesis`, those two lines in that order and no other",
        ),
        case(
            "a step part that assumes something besides its hypothesis",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("    assume step 1 is true for k, the induction hypothesis             (IH)".to_string()), "    assume step 1 is true for k, the induction hypothesis             (IH)\n    assume k = k                                                      (A1)".to_string()),
            ],
            "the step part of step 1 does not open with `let k ∈ ℕ` and `assume step 1 is true for k, the induction hypothesis`, those two lines in that order and no other",
        ),
        case(
            "split into one case",
            vec![edit(
                "proofs/zz/one-case.proof",
                None,
                "theorem one-case\n  let a ∈ ℝ                                                           (H1)\n  assume a = 0                                                        (H2)\n  then a = 0\n\n1.  a = 0\n    cases, from H2\n\n    case\n    assume a = 0                                                      (C1)\n\n    1.1.  a = 0\n          restate C1\n".to_string(),
            )],
            "step 1 takes one case, and a case split takes two or more; prove the one case as a plain step",
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
        case(
            "define a function whose values are statements",
            vec![edit(
                "proofs/zz/define-statement.proof",
                None,
                "theorem define-statement\n  let a ∈ ℝ                                                           (H1)\n  then a = a\n\n  let Q(x) = x < 1, for x ∈ ℝ                                         (D1)\n      reads a statement of x\n\n1.  a = a\n    algebra\n".to_string(),
            )],
            "define D1 says each value of Q is x < 1, a statement, and a define names a thing",
        ),
        case(
            "claim nothing but a full stop",
            vec![edit(
                "proofs/zz/claim-stop.proof",
                None,
                "theorem claim-stop\n  let x ∈ ℝ                                                           (H1)\n  assume x + 0 = x                                                    (H2)\n  then x + 0 = x\n\n1.  .\n    restate H2\n\n2.  x + 0 = x\n    join H2, 1\n".to_string(),
            )],
            "step 1 says nothing",
        ),
        case(
            "assume nothing but a full stop",
            vec![edit(
                "proofs/zz/assume-stop.proof",
                None,
                "theorem assume-stop\n  let x ∈ ℝ                                                           (H1)\n  assume .                                                            (H2)\n  then x = x\n\n1.  x = x\n    algebra\n".to_string(),
            )],
            "the `assume` line says nothing",
        ),
        case(
            "a let line of two sentences",
            vec![edit(
                "proofs/zz/let-two.proof",
                None,
                "theorem let-two\n  let x ∈ ℝ. x > 0.                                                   (H1)\n  then x = x\n\n1.  x = x\n    algebra\n".to_string(),
            )],
            "the `let` line: \"x ∈ ℝ. x > 0.\" is 2 sentences where one formula is written",
        ),
        case(
            "a let in a set listing names nothing introduces",
            vec![edit(
                "proofs/zz/let-listed.proof",
                None,
                "theorem let-listed\n  let x ∈ {a, b}                                                      (H1)\n  then x = x\n\n1.  x = x\n    algebra\n".to_string(),
            )],
            "the statement writes a, which it does not introduce",
        ),
        case(
            "a theorem introducing a property",
            vec![edit(
                "proofs/zz/let-property.proof",
                None,
                "theorem let-property\n  let A be a set                                                      (H1)\n  let P be a property of the elements of A                            (H2)\n  then A = A\n\n1.  A = A\n    algebra\n".to_string(),
            )],
            "`let P be a property of the elements of A` introduces a property, which only a library item may",
        ),
        case(
            "a value that does not read",
            vec![edit(
                "proofs/zz/value-unread.proof",
                None,
                "theorem value-unread\n  let x ∈ ℝ                                                           (H1)\n  assume for all y ∈ ℝ, y = y                                         (H2)\n  then x = x\n\n1.  x = x\n    instantiate y := x + + in line H2, from H1\n".to_string(),
            )],
            "a value step 1 gives: 'x + +' has 2 token(s) left over",
        ),
        case(
            "a substitute equation that does not read",
            vec![edit(
                "proofs/zz/equation-unread.proof",
                None,
                "theorem equation-unread\n  let x ∈ ℝ                                                           (H1)\n  assume x = 0                                                        (H2)\n  then x + 1 = 0 + 1\n\n1.  x + 1 = 0 + 1\n    substitute x = + (H2)\n".to_string(),
            )],
            "the equation of step 1: ",
        ),
        case(
            "a substitute equation of two sentences",
            vec![edit(
                "proofs/zz/equation-two.proof",
                None,
                "theorem equation-two\n  let x ∈ ℝ                                                           (H1)\n  assume x = 0                                                        (H2)\n  then x + 1 = 0 + 1\n\n1.  x + 1 = 0 + 1\n    substitute x = 0. x = 0 (H2)\n".to_string(),
            )],
            "the equation of step 1: \"x = 0. x = 0\" is 2 sentences where one formula is written",
        ),
        case(
            "a requires fact of two sentences",
            vec![edit(
                "proofs/zz/requires-two.proof",
                None,
                "import mundane theorem stdlib/numbers/square-nonneg\n\ntheorem requires-two\n  let x ∈ ℝ                                                           (H1)\n  then x² ≥ 0\n\n1.  x² ≥ 0\n    mun:square-nonneg x := x\n    requires x ∈ ℝ. x = x: from H1\n".to_string(),
            )],
            "the requires line of step 1: \"x ∈ ℝ. x = x\" is 2 sentences where one formula is written",
        ),
        case(
            "a calculation term that does not read",
            vec![edit(
                "proofs/zz/chain-unread.proof",
                None,
                "theorem chain-unread\n  let x ∈ ℝ                                                           (H1)\n  then x + 0 = x\n\n1.  x + 0 = x\n    calculation\n      x + 0 = x + +     H1\n            = x         H1\n".to_string(),
            )],
            "the calculation of step 1: ",
        ),
        case(
            "a proof block claiming two sentences",
            vec![edit(
                "proofs/zz/proof-two.proof",
                None,
                "theorem proof-two\n  let a ∈ ℝ                                                           (H1)\n  then if a = 0 then a = 0\n\n1.  If a = 0 then a = 0. If a = 0 then a = 0.\n    proof\n    assume a = 0                                                      (K1)\n\n    1.1.  a = 0\n          restate K1\n\n2.  If a = 0 then a = 0.\n    restate 1\n".to_string(),
            )],
            "step 1 opens a proof block and claims 2 sentences; the block proves one, and each other sentence is a step of its own",
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
        // Each part of a block ends on what it owes (`SYNTAX.md`): the base
        // on the claim's statement at the start, the step on it at k + 1, a
        // case on the block's claim, a proof block on its claim with what
        // its openers took off it. Each of these stops one line short.
        case(
            "an induction's base that stops short of the claim's first instance",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("    1.1.  S(1) = 1(1 + 1)/2\n          calculation\n            S(1) = Σ(j = 1 to 1) j       D1\n                 = 1                     mun:sum-single a := 1\n                 = 1(1 + 1)/2            arithmetic".to_string()), "    1.1.  S(1) = 1\n          calculation\n            S(1) = Σ(j = 1 to 1) j       D1\n                 = 1                     mun:sum-single a := 1".to_string()),
            ],
            "step 1.1 ends the base part of step 1, which owes",
        ),
        case(
            "an induction's step that stops short of the next instance",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("    1.3.  S(k + 1) = (k + 1)((k + 1) + 1)/2\n          calculation\n            S(k + 1) = S(k) + (k + 1)               1.2\n                     = k(k + 1)/2 + (k + 1)         substitute IH\n                     = (k + 1)((k + 1) + 1)/2       algebra".to_string()), "    1.3.  S(k + 1) = k(k + 1)/2 + (k + 1)\n          calculation\n            S(k + 1) = S(k) + (k + 1)               1.2\n                     = k(k + 1)/2 + (k + 1)         substitute IH".to_string()),
            ],
            "step 1.3 ends the step part of step 1, which owes",
        ),
        case(
            "a case that stops short of the block's claim",
            vec![
                edit("proofs/wiedijk/triangle-inequality.proof", Some("    2.5.  x ≤ |x|. −x ≤ |x|.\n          join 2.2, 2.4\n\n    case\n    assume x < 0".to_string()), "    case\n    assume x < 0".to_string()),
            ],
            "step 2.4 ends case 1 of step 2, which owes",
        ),
        case(
            "a proof block that stops short of its claim",
            vec![
                edit("proofs/wiedijk/reals-uncountable.proof", Some("    4.6.  L(k) ∈ ℝ. U(k) ∈ ℝ. L(k) ≤ U(k).\n          join 4.2, 4.3, 4.5".to_string()), "    4.6.  L(k) ∈ ℝ. U(k) ∈ ℝ.\n          join 4.2, 4.3".to_string()),
            ],
            "step 4.6 ends the proof block of step 4, which owes",
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
            "a contradiction whose block does not suppose anything",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    contradiction\n    suppose √2 ∈ ℚ                                                    (S)".to_string()), "    contradiction".to_string()),
            ],
            "does not open with `suppose`",
        ),
        case(
            "cite another proof file's theorem without importing it",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("import theorem            proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()), "".to_string()),
            ],
            "thm:abs-bounds is neither imported nor a theorem of this file",
        ),
        // An import names one item, and its keyword is the kind of the item.
        case(
            "import without saying what is imported",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("import theorem            proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()), "import proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()),
            ],
            "an import says `import <kind> <file>/<name>`",
        ),
        case(
            "import a whole proof file",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("import theorem            proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()), "import proof proofs/wiedijk/triangle-inequality\n".to_string()),
            ],
            "import proof: an import says the header of the item it names",
        ),
        // A theorem taken for granted is imported as mundane, and every other
        // item by its kind. An import says its record's header: the mark and
        // the kind both.
        case(
            "import an item as mundane without its kind",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("import axiom              stdlib/reasoning/excluded-middle\n".to_string()), "import mundane stdlib/reasoning/excluded-middle\n".to_string()),
            ],
            "import mundane: an import says the header of the item it names",
        ),
        case(
            "import an axiom as a mundane theorem",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("import axiom              stdlib/reasoning/excluded-middle\n".to_string()), "import mundane theorem    stdlib/reasoning/excluded-middle\n".to_string()),
            ],
            "import mundane theorem stdlib/reasoning/excluded-middle: stdlib/reasoning/excluded-middle is an axiom; import it as `import axiom stdlib/reasoning/excluded-middle`",
        ),
        case(
            "import a proof's define as mundane",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import mundane definition proofs/wiedijk/tri/T\n\ntheorem cantor\n".to_string()),
            ],
            "import mundane definition proofs/wiedijk/tri/T: an axiom or a definition gives meaning, and a pedantic textbook cites it, so it is never mundane",
        ),
        case(
            "import an axiom as mundane",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("import axiom              stdlib/reasoning/excluded-middle\n".to_string()), "import mundane axiom      stdlib/reasoning/excluded-middle\n".to_string()),
            ],
            "import mundane axiom stdlib/reasoning/excluded-middle: an axiom or a definition gives meaning, and a pedantic textbook cites it, so it is never mundane",
        ),
        case(
            "cite an axiom as mundane",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("axi:excluded-middle".to_string()), "mun:excluded-middle".to_string()),
            ],
            "mun:excluded-middle names an axiom",
        ),
        case(
            "cite a definition as mundane",
            vec![
                edit("proofs/wiedijk/isosceles.proof", Some("def:congruent".to_string()), "mun:congruent".to_string()),
            ],
            "mun:congruent names a definition",
        ),
        // `mundane` is a mark before a kind, and only before a theorem.
        case(
            "mark a record mundane and give it no kind",
            vec![
                edit("corpus/stdlib/sets.records", Some("mundane theorem powerset-empty\n".to_string()), "mundane powerset-empty\n".to_string()),
            ],
            "mundane powerset-empty has no kind",
        ),
        case(
            "mark a definition mundane",
            vec![
                edit("corpus/stdlib/sets.records", Some("\ndefinition subset\n".to_string()), "\nmundane definition subset\n".to_string()),
            ],
            "mundane definition: an axiom or a definition gives meaning, and a pedantic textbook cites it, so it is never mundane",
        ),
        case(
            "mark an axiom mundane",
            vec![
                edit("corpus/stdlib/reasoning.records", Some("\naxiom excluded-middle\n".to_string()), "\nmundane axiom excluded-middle\n".to_string()),
            ],
            "mundane axiom: an axiom or a definition gives meaning, and a pedantic textbook cites it, so it is never mundane",
        ),
        case(
            "mark a method mundane",
            vec![
                edit("corpus/db/methods.records", Some("\nmethod arithmetic\n".to_string()), "\nmundane method arithmetic\n".to_string()),
            ],
            "mundane method: a method is named on the line that uses it, so it is never mundane",
        ),
        case(
            "mark a notation mundane",
            vec![
                edit("corpus/db/notation.records", Some("\nnotation ".to_string()), "\nmundane notation ".to_string()),
            ],
            "mundane notation: a notation is never cited, so nothing takes it for granted",
        ),
        case(
            "import a proof's theorem as a library kind",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("import theorem            proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()), "import mundane theorem proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()),
            ],
            "proofs/wiedijk/triangle-inequality/abs-bounds is a theorem",
        ),
        case(
            "import a theorem and cite nothing by it",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import theorem proofs/wiedijk/bezout/bezout\n\ntheorem cantor\n".to_string()),
            ],
            "imports bezout and cites nothing by it",
        ),
        case(
            "cite a library item without importing it",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("import axiom              stdlib/reasoning/excluded-middle\n".to_string()), String::new()),
            ],
            "axi:excluded-middle is neither imported nor a theorem of this file",
        ),
        case(
            "import a library item nothing cites",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import mundane theorem stdlib/sets/subset-transitive\n\ntheorem cantor\n".to_string()),
            ],
            "imports subset-transitive and cites nothing by it",
        ),
        case(
            "import from a proof file that is not there",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import theorem proofs/wiedijk/nonesuch/lemma\n\ntheorem cantor\n".to_string()),
            ],
            "import theorem proofs/wiedijk/nonesuch/lemma: proofs/wiedijk/nonesuch is no file",
        ),
        case(
            "import a theorem a proof file does not prove",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import theorem proofs/wiedijk/bezout/nonesuch\n\ntheorem cantor\n".to_string()),
            ],
            "import theorem proofs/wiedijk/bezout/nonesuch: proofs/wiedijk/bezout holds no item nonesuch",
        ),
        case(
            "import the same item twice",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("import theorem            proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()), "import theorem            proofs/wiedijk/triangle-inequality/abs-bounds\nimport theorem            proofs/wiedijk/triangle-inequality/abs-bounds\n".to_string()),
            ],
            "proofs/wiedijk/triangle-inequality/abs-bounds is imported twice",
        ),
        // A forbid names an item the file does not import, after the words
        // its record's header says, once, and after the imports.
        case(
            "import an item the file forbids",
            vec![
                edit("proofs/wiedijk/ptolemy.proof", Some("import mundane theorem    stdlib/numbers/multiply-cancel\n".to_string()), "import mundane theorem    stdlib/numbers/multiply-cancel\nforbid theorem            stdlib/geometry/law-of-cosines\n".to_string()),
            ],
            "imports stdlib/geometry/law-of-cosines, which this file forbids at line 19",
        ),
        case(
            "forbid an item with words that are not its header",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "forbid mundane theorem stdlib/geometry/law-of-cosines\n\ntheorem cantor\n".to_string()),
            ],
            "forbid mundane theorem stdlib/geometry/law-of-cosines: stdlib/geometry/law-of-cosines is a theorem; forbid it as `forbid theorem stdlib/geometry/law-of-cosines`",
        ),
        case(
            "forbid an item that is not there",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "forbid theorem stdlib/geometry/nonesuch\n\ntheorem cantor\n".to_string()),
            ],
            "forbid theorem stdlib/geometry/nonesuch: stdlib/geometry holds no item nonesuch",
        ),
        case(
            "forbid the same item twice",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "forbid theorem stdlib/geometry/law-of-cosines\nforbid theorem stdlib/geometry/law-of-cosines\n\ntheorem cantor\n".to_string()),
            ],
            "stdlib/geometry/law-of-cosines is forbidden twice",
        ),
        case(
            "an import below a forbid",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("import definition         stdlib/sets/set-builder\n".to_string()), "forbid theorem            stdlib/geometry/law-of-cosines\nimport definition         stdlib/sets/set-builder\n".to_string()),
            ],
            "an import below a forbid",
        ),
        case(
            "a forbid below a define",
            vec![
                edit("proofs/wiedijk/ballot.proof", Some("theorem good-finite\n".to_string()), "forbid theorem stdlib/geometry/law-of-cosines\n\ntheorem good-finite\n".to_string()),
            ],
            "a forbid below a define",
        ),
        // Every name a file cites is distinct within it.
        case(
            "import an item under the name of a theorem of the file",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("import mundane theorem    stdlib/sets/set-builder-subset\n".to_string()), "import mundane theorem    stdlib/sets/set-builder-subset as cantor\n".to_string()),
                edit("proofs/wiedijk/cantor.proof", Some("    mun:set-builder-subset, from D1".to_string()), "    mun:cantor, from D1".to_string()),
            ],
            "cantor is already the name of theorem cantor of this file; import one of them under another name with `as`",
        ),
        case(
            "import two items under one name",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import mundane theorem stdlib/sets/subset-transitive as set-builder-subset\n\ntheorem cantor\n".to_string()),
            ],
            "set-builder-subset is already the name of the import at line",
        ),
        case(
            "a proof file that imports its own theorem",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("theorem cantor\n".to_string()), "import theorem proofs/wiedijk/cantor/cantor\n\ntheorem cantor\n".to_string()),
            ],
            "proofs/wiedijk/cantor/cantor is a theorem of this file, which is cited with no import",
        ),
        case(
            "two proof files that import each other",
            vec![
                edit("proofs/wiedijk/triangle-inequality.proof", Some("theorem abs-bounds\n".to_string()), "import theorem proofs/wiedijk/intermediate-value/intermediate-value\n\ntheorem abs-bounds\n".to_string()),
            ],
            "closes a cycle",
        ),
        case(
            "a theorem that cites itself",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("          thm:odd-square, from S".to_string()), "          thm:even-square, from S".to_string()),
            ],
            "theorem even-square cites itself",
        ),
        case(
            "two theorems of one file that cite each other",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    def:odd n := n², from 2".to_string()), "    thm:even-square n := n², from 2".to_string()),
            ],
            "closes a cycle of citations: even-square → odd-square → even-square",
        ),
        // A library theorem proved in Parley is stated by its record, which
        // names the proof; the two state one thing, and a proof reaches no
        // record that rests on it.
        case(
            "a record that states less than its proof",
            vec![
                edit("corpus/stdlib/numbers.records", Some("  then        x ≤ |x|. −x ≤ |x|.\n  metamath-proof stdlib/numbers/abs-bounds".to_string()), "  then        x ≤ |x|.\n  metamath-proof stdlib/numbers/abs-bounds".to_string()),
            ],
            "mundane theorem abs-bounds does not state what stdlib/numbers/abs-bounds proves: it concludes something else than the proof",
        ),
        case(
            "a library proof no record names",
            vec![
                edit("corpus/stdlib/numbers.records", Some("  metamath-proof stdlib/numbers/abs-bounds\n  lean-proof  stdlib/numbers/abs-bounds".to_string()), "  metamath-proof not yet implemented\n  lean-proof  not yet implemented".to_string()),
            ],
            "theorem abs-bounds proves a library item, and no record names it",
        ),
        case(
            "a record proved by a proof nothing proves",
            vec![
                edit("corpus/stdlib/numbers.records", Some("  metamath-proof stdlib/numbers/abs-bounds\n".to_string()), "  metamath-proof stdlib/numbers/abs-bound\n".to_string()),
            ],
            "is proved by stdlib/numbers/abs-bound, which no proof of the standard library proves",
        ),
        case(
            "a record proved by a proof that cites it",
            vec![
                edit("corpus/stdlib/numbers.records", Some("  lean-proof  stdlib/numbers/abs-bounds".to_string()), "  lean-proof  stdlib/calculus/convergent-bounded".to_string()),
            ],
            "theorem convergent-bounded cites itself",
        ),
        case(
            "a mundane theorem outside the standard library",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("theorem even-square\n".to_string()), "mundane theorem even-square\n".to_string()),
            ],
            "mundane theorem even-square: only a theorem of the standard library is taken for granted",
        ),
        case(
            "a library proof of an item a record proves otherwise",
            vec![
                edit("corpus/stdlib/sets.proof", None, "theorem powerset-empty\n  then 1 = 1\n\n1.  1 = 1\n    arithmetic\n".to_string()),
            ],
            "theorem powerset-empty proves a library item, and no record names it",
        ),
        case(
            "two theorems of one name in one file",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("theorem even-square\n".to_string()), "theorem odd-square\n".to_string()),
            ],
            "theorem odd-square is already proved",
        ),
        case(
            "two items of one name in one library file",
            vec![
                edit("corpus/stdlib/sets.records", Some("mundane theorem powerset-empty\n".to_string()), "mundane theorem powerset-monotone\n".to_string()),
            ],
            "mundane theorem powerset-monotone is already defined",
        ),
        case(
            "an item stated outside the standard library",
            vec![
                edit("corpus/db/methods.records", Some("method algebra\n".to_string()), "theorem stray\n  then        P\n  metamath-proof exmid\n  lean-proof  not yet implemented\n\nmethod algebra\n".to_string()),
            ],
            "stray is outside stdlib/",
        ),
        case(
            "a theorem field said twice",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("  note        Let B be".to_string()), "  note        twice.\n  note        Let B be".to_string()),
            ],
            "says note twice",
        ),
        case(
            "a let line that asserts instead of introducing",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("  let A be a set                                                      (H1)".to_string()), "  let A ≠ B                                                           (H1)".to_string()),
            ],
            "none of the 13 introductions",
        ),
        // Renaming the isosceles points to a and n makes the distance |an| spell
        // the declared word `an`, which is what the capital-letter convention has
        // been quietly preventing.
        case(
            "two names run together into a declared word",
            vec![
                edit("proofs/wiedijk/pythagoras.proof", Some("8.  |AD| + |DB| = |AB|".to_string()), "8.  |an| + |DB| = |AB|".to_string()),
            ],
            "run together",
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
        case(
            "obtain a name without stating its sort",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("1.  k ∈ ℤ. n = 2k + 1.\n    obtain k: def:odd, from H2".to_string()), "1.  n = 2k + 1.\n    obtain k: def:odd, from H2".to_string()),
            ],
            "without stating its sort",
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
            "open a block under a calculation",
            vec![edit(
                "proofs/zz/calculation-block.proof",
                None,
                "theorem calculation-block\n  let a ∈ ℝ                                                           (H1)\n  assume a = 1                                                        (H2)\n  then a = 1\n\n1.  a = 1\n    calculation\n      a = 1          H2\n    assume a = a                                                      (A1)\n\n    1.1.  a = 1\n          restate H2\n".to_string(),
            )],
            "step 1 is a calculation, which writes its chain and opens no block of steps",
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
        case(
            "write a vertex's degree where no graph is let",
            vec![edit(
                "proofs/zz/degree-no-graph.proof",
                None,
                "theorem degree-no-graph\n  let V be a set                                                      (H1)\n  let v ∈ V                                                           (H2)\n  assume deg(v) = 2                                                   (H3)\n  then deg(v) = 2\n\n1.  deg(v) = 2\n    restate H3\n".to_string(),
            )],
            "deg(v) is said of a graph, and no `let` line of the theorem introduces one",
        ),
        case(
            "assume a fact of a letter nothing introduces",
            vec![edit(
                "proofs/zz/assume-unknown.proof",
                None,
                "theorem assume-unknown\n  let x ∈ ℝ                                                           (H1)\n  assume y = x                                                        (H2)\n  then x = x\n\n1.  x = x\n    algebra\n".to_string(),
            )],
            "the statement writes y, which it does not introduce",
        ),
        case(
            "give an item's letter a value of a letter nothing introduces",
            vec![edit(
                "proofs/zz/value-unknown.proof",
                None,
                "import definition         stdlib/divisibility/divides\n\ntheorem value-unknown\n  let a ∈ ℤ                                                           (H1)\n  then a divides a\n\n1.  a = a·1\n    algebra\n\n2.  a divides a\n    def:divides d := a, n := a, k := y, from 1\n".to_string(),
            )],
            "step 2: y in k := y is not introduced here",
        ),
        case(
            "say a define gives its function on a domain it does not write",
            vec![edit(
                "proofs/zz/define-domain.proof",
                None,
                "import mundane theorem    stdlib/functions/function-into\n\ndefine f(n) := n, for n ∈ ℕ                                           (D1)\n       reads each natural number, as a rational\n\ntheorem define-domain\n  assume for all n ∈ ℤ, f(n) ∈ ℚ                                      (H1)\n  then f : ℤ → ℚ\n\n1.  f : ℤ → ℚ\n    mun:function-into, from H1\n    requires f is a function on ℤ: from D1\n".to_string(),
            )],
            "from D1 does not give f is a function on ℤ: D1 gives f on ℕ",
        ),
        case(
            "substitute from a define an equation it does not say",
            vec![edit(
                "proofs/zz/substitute-define.proof",
                None,
                "theorem substitute-define\n  let x ∈ ℝ                                                           (H1)\n  let y = x + 1                                                       (D1)\n      reads one more than x\n  assume x > 0                                                        (H2)\n  then y > 0\n\n1.  y > 0\n    substitute x = y (D1) into H2\n".to_string(),
            )],
            "step 1 takes x = y from D1, which does not say it",
        ),
        case(
            "let a kind be shown from a line that does not give it",
            vec![edit(
                "proofs/zz/let-from.proof",
                None,
                "theorem let-from\n  let N ∈ ℤ                                                           (H1)\n  assume N = 1                                                        (H2)\n  then N/2 ∈ ℤ\n\nlet k = N/2, an integer                                               (D1)\n    from H2\n    reads half of N\n\n1.  k = N/2\n    D1\n\n2.  k ∈ ℤ\n    join D1\n\n3.  N/2 ∈ ℤ\n    substitute k = N/2 (line 1) into line 2\n".to_string(),
            )],
            "from H2 does not reach N/2 ∈ ℤ, which this line claims it supplies",
        ),
        case(
            "let a kind be shown by arithmetic that finds it false",
            vec![edit(
                "proofs/zz/let-arithmetic.proof",
                None,
                "theorem let-arithmetic\n  then 3/2 ∈ ℤ\n\nlet k = 3/2, an integer                                               (D1)\n    arithmetic\n    reads three halves\n\n1.  k = 3/2\n    D1\n\n2.  k ∈ ℤ\n    join D1\n\n3.  3/2 ∈ ℤ\n    substitute k = 3/2 (line 1) into line 2\n".to_string(),
            )],
            "the reason under let D1 does not show 3/2 ∈ ℤ: arithmetic finds it is false",
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
        case(
            "write a contradiction in prose after a claim",
            vec![
                edit("proofs/wiedijk/infinitely-many-primes.proof", Some("4.  p > 1\n    def:prime, from 3".to_string()), "4.  p > 1, which contradicts p ≤ 1\n    def:prime, from 3".to_string()),
            ],
            "does not read past 'which', a word no notation in scope writes; a step reaching the opposite",
        ),
        case(
            "write a claim in a notation nobody declared",
            vec![
                edit("proofs/wiedijk/infinitely-many-primes.proof", Some("4.  p > 1\n    def:prime, from 3".to_string()), "4.  p exceeds 1\n    def:prime, from 3".to_string()),
            ],
            "'p exceeds 1' does not read past 'exceeds', a word no notation in scope writes",
        ),
        case(
            "close a bracket nothing opened",
            vec![
                edit("proofs/wiedijk/infinitely-many-primes.proof", Some("4.  p > 1\n    def:prime, from 3".to_string()), "4.  p > 1)\n    def:prime, from 3".to_string()),
            ],
            "token(s) left over, starting at ')'",
        ),
        case(
            "write a formula that reads two ways because nothing says what a name is",
            vec![
                edit("proofs/wiedijk/subsets.proof", Some("1.10. |T| = 2^k".to_string()), "1.10. |W| = 2^k".to_string()),
            ],
            "'|W| = 2^k' reads as absolute-value or as cardinality, and nothing says what W is",
        ),
        // `divides-difference` asks that d divide b, which line 5.2 says.
        case(
            "drop a line a citation needs for a hypothesis",
            vec![
                edit("proofs/wiedijk/infinitely-many-primes.proof", Some("mun:divides-difference d := p, a := n! + 1, b := n!, from 3, 5.2".to_string()), "mun:divides-difference d := p, a := n! + 1, b := n!, from 3".to_string()),
            ],
            "does not supply",
        ),
    ]
}
