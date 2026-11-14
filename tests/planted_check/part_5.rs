//! Part 5 of 6 of the planted cases, in the order they are run.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
        case(
            "give a first value in terms of a sequence",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("let a(0) = M,  b(0) = N,".to_string()), "let a(0) = b(0),  b(0) = N,".to_string()),
            ],
            "names b, which has no value before 0",
        ),
        // n − 1 for n ∈ ℕ is an integer by what the page says once, and in ℕ₀
        // only by a line saying so.
        case(
            "cite a step rule without saying the index is in ℕ₀",
            vec![
                edit("proofs/wiedijk/reals-uncountable.proof", Some("          D3\n          requires n − 1 ∈ ℕ₀: from 16.1\n".to_string()), "          D3\n".to_string()),
            ],
            "no line it cites says the index is in ℕ₀",
        ),
        case(
            "claim the value of the other case",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("3.5.1.  a(k + 1) = a(k)".to_string()), "3.5.1.  a(k + 1) = b(k)".to_string()),
            ],
            "step 3.5.1 cites D1 and claims a value it does not give",
        ),
        case(
            "cite a step rule by cases without saying which case",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("3.5.7.  b(k + 1) = a(k) mod b(k)\n                  D1, from C2".to_string()), "3.5.7.  b(k + 1) = a(k) mod b(k)\n                  D1".to_string()),
            ],
            "says whether a case's condition holds",
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
            "define a sequence by recursion outside any theorem",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("theorem euclid".to_string()), "define c(0) := 1, c(k + 1) := c(k), for k ∈ ℕ₀                     (D9)\n       reads a constant sequence\n\ntheorem euclid".to_string()),
            ],
            "is written in the theorem that uses it",
        ),
        // Levels the precedence order leaves unrelated need brackets whichever
        // side each stands on: a trailing "for all" takes one relation, and
        // "and" and "or" are not ordered against each other.
        case(
            "write a trailing for all over an and",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("3.  There exists B ⊆ A such that f(x) ≠ B for all x ∈ A.".to_string()), "3.  There exists B ⊆ A such that f(x) ≠ B and x ∈ A for all x ∈ A.".to_string()),
            ],
            "`and` and `for all` are not ordered against each other",
        ),
        // The universal is written "for all"; "for every" is no spelling of it.
        case(
            "write for every where for all is meant",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("2.  For all x ∈ A, f(x) ≠ B.".to_string()), "2.  For every x ∈ A, f(x) ≠ B.".to_string()),
            ],
            "for-all does not fit",
        ),
        case(
            "mix and with or without brackets",
            vec![
                edit("proofs/hammack/consecutive-coprime.proof", Some("1.  n = 0 or n ≠ 0".to_string()), "1.  n = 0 or n ≠ 0 and n ∈ ℕ".to_string()),
            ],
            "`or` and `and` are not ordered against each other",
        ),
        // "P is between A and B" writes an "and" of its own, so where it
        // stands in a sentence joined by "and" or "or" it is bracketed.
        case(
            "write a betweenness after an or without brackets",
            vec![
                edit("proofs/wiedijk/law-of-cosines.proof", Some("1.  H = Q or (H is between Q and R) or".to_string()), "1.  H = Q or H is between Q and R or".to_string()),
            ],
            "`or` and `is between` are not ordered against each other",
        ),
        case(
            "write a betweenness before an and without brackets",
            vec![
                edit("tests/stdlib/geometry.proof", Some("1.  there is X ∈ 𝔼² with (X is between A and B) and |AX| = r".to_string()), "1.  there is X ∈ 𝔼² with X is between A and B and |AX| = r".to_string()),
            ],
            "`is between` and `and` are not ordered against each other",
        ),
        // A define of a phrase: `define <name>: <phrase> means <meaning>`,
        // the phrase's letters the meaning's free letters, each slot's sort
        // settled by the meaning, written only where defined or imported.
        case(
            "write a phrase define without means",
            vec![
                edit("tests/elaborator/a-phrase-with-and.proof", Some("d is a common divisor of a and b means".to_string()), "d is a common divisor of a and b says".to_string()),
            ],
            "says no `means`",
        ),
        case(
            "open a phrase with no letter it is said of",
            vec![
                edit("tests/elaborator/a-phrase-with-and.proof", Some("d is a common divisor of a and b means".to_string()), "common divisors of a and b means".to_string()),
            ],
            "is not a phrase of the form `<letter> is a …`",
        ),
        case(
            "mark a phrase define mundane",
            vec![
                edit("tests/elaborator/a-phrase-with-and.proof", Some("define common-divisor:".to_string()), "mundane define common-divisor:".to_string()),
            ],
            "a define gives a name its meaning, and a pedantic textbook cites it, so it is never mundane",
        ),
        case(
            "give a phrase a slot its meaning does not use",
            vec![
                edit("tests/elaborator/a-phrase-with-and.proof", Some("       d ∈ ℤ and d divides a and d divides b".to_string()), "       d ∈ ℤ and d divides a".to_string()),
            ],
            "b stands in its phrase, and its meaning does not use it",
        ),
        case(
            "give a phrase a meaning with a letter no slot holds",
            vec![
                edit("tests/elaborator/a-phrase-with-and.proof", Some("       d ∈ ℤ and d divides a and d divides b".to_string()), "       d ∈ ℤ and d divides a and d divides b and d divides c".to_string()),
            ],
            "its meaning writes c, which is no letter of its phrase",
        ),
        case(
            "give a phrase a meaning that says no slot's sort",
            vec![
                edit("tests/elaborator/a-phrase-with-and.proof", Some("       d ∈ ℤ and d divides a and d divides b".to_string()), "       d = a and d = b".to_string()),
            ],
            "its meaning does not say what d is",
        ),
        case(
            "give a phrase define no reads line",
            vec![
                edit("tests/elaborator/a-phrase-with-and.proof", Some("       reads d divides both a and b\n".to_string()), String::new()),
            ],
            "carries no `reads` line",
        ),
        case(
            "give a phrase four slots",
            vec![
                edit("tests/elaborator/a-phrase-with-and.proof", Some("d is a common divisor of a and b means".to_string()), "d is a common divisor of a and b in c means".to_string()),
            ],
            "has 4 slots, and a phrase has one, two or three",
        ),
        case(
            "write a phrase another notation already writes",
            vec![
                edit("tests/elaborator/a-phrase-with-and.proof", Some("d is a common divisor of a and b means".to_string()), "d is a point means".to_string()),
            ],
            "its phrase is written `_ is a point` as notation is-a-point is",
        ),
        case(
            "write a phrase whose words say and beside an and without brackets",
            vec![
                edit("tests/elaborator/a-phrase-with-and.proof", Some("  assume (d is a common divisor of a and b) and d > 0".to_string()), "  assume d is a common divisor of a and b and d > 0  ".to_string()),
            ],
            "`is a common divisor of` and `and` are not ordered against each other",
        ),
        case(
            "write a phrase the file does not import",
            vec![
                edit("tests/elaborator/a-phrase-imported.proof", Some("import definition         tests/elaborator/a-phrase-defined/triangular-number\n".to_string()), String::new()),
            ],
            "is the phrase tests/elaborator/a-phrase-defined/triangular-number defines, which this file does not import",
        ),
        // A phrase's `where` part says a slot is a set or a function, a kind
        // and no fact, for a slot its meaning leaves open.
        case(
            "leave out a where part the meaning needs",
            vec![
                edit("tests/elaborator/a-phrase-with-a-where-part.proof", Some(", where W is a set   (D1)".to_string()), "   (D1)".to_string()),
            ],
            "reads as absolute-value or as cardinality, and nothing says what W is",
        ),
        case(
            "name a letter in a where part that is no slot",
            vec![
                edit("tests/elaborator/a-phrase-with-a-where-part.proof", Some("where W is a set   (D1)".to_string()), "where X is a set   (D1)".to_string()),
            ],
            "its `where` part names X, which is no slot of its phrase",
        ),
        case(
            "say a kind a where part does not know",
            vec![
                edit("tests/elaborator/a-phrase-with-a-where-part.proof", Some("a is a function from numbers to numbers".to_string()), "a is a function from sets to numbers".to_string()),
            ],
            "'a is a function from sets to numbers' after `where` is neither",
        ),
        case(
            "name one slot twice in a where part",
            vec![
                edit("tests/elaborator/a-phrase-with-a-where-part.proof", Some("where W is a set   (D1)".to_string()), "where W is a set, W is a set   (D1)".to_string()),
            ],
            "its `where` part names W twice",
        ),
        case(
            "say in a where part what the meaning already says",
            vec![
                edit("tests/elaborator/a-phrase-with-a-where-part.proof", Some("       n ≤ |W| and for all Y ⊆ W".to_string()), "       W ⊆ ℕ and n ≤ |W| and for all Y ⊆ W".to_string()),
            ],
            "its `where` part says what W is, which its meaning already says",
        ),
        case(
            "import a phrase and neither cite it nor write it",
            vec![
                edit("tests/elaborator/a-phrase-with-and.proof", Some("define common-divisor:".to_string()), "import definition         tests/elaborator/a-phrase-defined/triangular-number\n\ndefine common-divisor:".to_string()),
            ],
            "imports triangular-number and neither cites it nor writes its phrase",
        ),
        case(
            "fill an attached slot with more than a letter",
            vec![
                edit("tests/elaborator/a-phrase-of-three-slots.proof", Some("  then 2 is an 3-th root of 8".to_string()), "  then 2 is an (1 + 2)-th root of 8".to_string()),
            ],
            "wants a letter or a numeral before its hyphen",
        ),
        // A quantifier may write a bound where its set stands, "for all ε >
        // 0", only where the statement says what the letter ranges over.
        case(
            "write a bound in place of a set nothing declares",
            vec![
                edit("proofs/wiedijk/triangular-reciprocals.proof", Some("  ε ranges over ℝ\n".to_string()), String::new()),
            ],
            "nothing says what set ε belongs to",
        ),
        case(
            "write a bound in place of a set in an item that declares none",
            vec![
                edit("corpus/stdlib/calculus.records", Some("  ε, δ range over ℝ\n".to_string()), String::new()),
            ],
            "nothing says what set δ belongs to",
        ),
        case(
            "let a declared letter be in another set",
            vec![
                edit("proofs/wiedijk/triangular-reciprocals.proof", Some("    let ε ∈ ℝ ".to_string()), "    let ε ∈ ℚ ".to_string()),
            ],
            "the statement says ε ranges over ℝ, and this line puts it in ℚ",
        ),
        case(
            "declare a letter's range twice",
            vec![
                edit("proofs/wiedijk/triangular-reciprocals.proof", Some("  n ranges over ℕ\n".to_string()), "  n ranges over ℕ\n  n ranges over ℤ\n".to_string()),
            ],
            "the statement already says what n ranges over",
        ),
        case(
            "declare a range no quantifier leans on",
            vec![
                edit("proofs/wiedijk/triangular-reciprocals.proof", Some("  n ranges over ℕ\n".to_string()), "  n ranges over ℕ\n  x ranges over ℝ\n".to_string()),
            ],
            "the statement says what x ranges over, and no quantifier leaves x's set out",
        ),
        case(
            "declare a range over something that is not a set",
            vec![
                edit("proofs/wiedijk/triangular-reciprocals.proof", Some("  ε ranges over ℝ\n".to_string()), "  ε ranges over 2\n".to_string()),
            ],
            "'2' is not a set, so nothing can range over it",
        ),
        case(
            "give the type of a define the citation does not bind",
            vec![
                edit("proofs/wiedijk/mean-value.proof", Some("requires g : [a, b] → ℝ: from 8".to_string()), "requires F : [a, b] → ℝ: from 10".to_string()),
            ],
            "says F : [a, b] → ℝ, and neither thm:continuous-linear nor the step's other lines ask for it",
        ),
        case(
            "give a bound define a type other than the item asks",
            vec![
                edit("proofs/wiedijk/mean-value.proof", Some("requires g : [a, b] → ℝ: from 8".to_string()), "requires g : ℕ → ℝ: from 8".to_string()),
            ],
            "says g : ℕ → ℝ, and neither thm:continuous-linear nor the step's other lines ask for it",
        ),
        case(
            "name a number with the derivative's spelling",
            vec![
                edit("proofs/wiedijk/mean-value.proof", Some("  assume a < b ".to_string()), "  let f′ ∈ ℝ                                                          (H9)\n  assume a < b ".to_string()),
            ],
            "f′ is how the derivative of the function f is written, so it cannot name anything else: call it f₁",
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
        case(
            "reorder a product by a map not shown to be one-to-one",
            vec![
                edit("proofs/wiedijk/euler.proof", Some("thm:product-reorder, from 4, 5, 9".to_string()), "thm:product-reorder, from 4, 5, 8".to_string()),
            ],
            "step 10 cites thm:product-reorder, which asks for",
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
        // A define used for what it is has its argument in its domain: c(j, y)
        // is defined for y ∈ V, which no line introduces y in.
        case(
            "unfold c(0, y) without saying y ∈ V",
            vec![
                edit("tests/elaborator/induction-under-a-condition.proof", Some("                  D1\n                  requires y ∈ V: from 1.1.1\n".to_string()), "                  D1\n".to_string()),
            ],
            "step 1.1.2 cites D1 at y, so it needs y ∈ V, and nothing it cites or requires says it",
        ),
        // A recursion's domain is its index: N((n − 1) + 1) asks n − 1.
        case(
            "unfold N((n − 1) + 1) without saying n − 1 ∈ ℕ₀",
            vec![
                edit("proofs/wiedijk/reals-uncountable.proof", Some("          D3\n          requires n − 1 ∈ ℕ₀: from 16.1\n".to_string()), "          D3\n".to_string()),
            ],
            "step 16.2 cites D3 at n − 1 + 1, so it needs n − 1 ∈ ℕ₀, and nothing it cites or requires says it",
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
        // A define's name is not a letter introduced in a number system:
        // that x₁ is real rests on min-real, and abs-difference-lt asks it.
        case(
            "leave out a define's membership where an item asks it",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("    let x₁ = min(b, c + δ/2), a real number                            (D2)\n           mun:min-real x := b, y := c + δ/2\n".to_string()), "    let x₁ = min(b, c + δ/2)                                           (D2)\n".to_string()),
            ],
            "step 16.19 cites mun:abs-difference-lt, which asks for",
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
        // A record states what it says; one with nothing to say is a
        // record of nothing.
        case(
            "a theorem record with no then line",
            vec![
                edit("corpus/stdlib/sums.records", Some("  then        Σ(k = 0 to n) t(k) ∈ ℤ\n  metamath-proof fsumzcl".to_string()), "  metamath-proof fsumzcl".to_string()),
            ],
            "sum-integer has no `then` line",
        ),
        // A paragraph after a blank line continues the field above it, so
        // a `none` written above a note's second paragraph runs on into it.
        case(
            "a lean-proof that says none and then more",
            vec![
                edit("corpus/stdlib/geometry.records", Some("  metamath-proof none\n  lean-proof  none\n\nmundane theorem angle-real".to_string()), "  metamath-proof none\n  lean-proof  none\n\n              A second paragraph.\n\nmundane theorem angle-real".to_string()),
            ],
            "angle's `lean-proof` says `none` and then more",
        ),
        case(
            "a method declaring a part that is no part marker",
            vec![
                edit("corpus/db/methods.records", Some("  parts       base, step\n".to_string()), "  parts       basis, step\n".to_string()),
            ],
            "method induction declares part",
        ),
        // A notation record says what it writes, what each hole takes, and
        // what its metamath-builds makes of the holes.
        case(
            "a notation with no pattern",
            vec![
                edit("corpus/db/notation.records", Some("notation sum\n  pattern     Σ(_ = _ to _) _\n".to_string()), "notation sum\n".to_string()),
            ],
            "notation sum declares no pattern",
        ),
        case(
            "a notation whose sort does not read",
            vec![
                edit("corpus/db/notation.records", Some("  sort        number, number, number, number → number\n  level       summation".to_string()), "  sort        number number\n  level       summation".to_string()),
            ],
            "notation sum: sort",
        ),
        case(
            "a notation's metamath-builds naming a hole it does not have",
            vec![
                edit("corpus/db/notation.records", Some("  metamath-builds _2 _3 cfz co _4 _1 csu".to_string()), "  metamath-builds _2 _3 cfz co _5 _1 csu".to_string()),
            ],
            "notation sum metamath-builds",
        ),
        case(
            "a notation that can nest in itself with no assoc",
            vec![
                edit("corpus/db/notation.records", Some("  assoc       left\n  identity    0 on either side, 0 on the right".to_string()), "  identity    0 on either side, 0 on the right".to_string()),
            ],
            "notation additive has a hole at each edge",
        ),
        case(
            "a notation with an assoc it does not need",
            vec![
                edit("corpus/db/notation.records", Some("  level       summation\n".to_string()), "  level       summation\n  assoc       left\n".to_string()),
            ],
            "notation indexed-union declares an assoc it does not need",
        ),
        // arithmetic works out + − · / and powers of numerals, and another
        // operation only where its record says so: mod's does.
        case(
            "arithmetic working out an operation its record does not give it",
            vec![
                edit("corpus/db/notation.records", Some("  reads       the remainder on dividing by\n  decided     arithmetic\n".to_string()), "  reads       the remainder on dividing by\n".to_string()),
                edit("proofs/wiedijk/sum-formula.proof", Some("= (k + 1)((k + 1) + 1)/2       algebra\n".to_string()), "= (k + 1)((k + 1) + 1)/2       algebra\n          requires 7 mod 3 = 1: arithmetic\n".to_string()),
            ],
            "7 mod 3 = 1 works out",
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
            "a chain link saying a modulus after a relation that is not ≡",
            vec![
                edit("proofs/wiedijk/divisibility-by-three.proof", Some("                 ≡ 1 (mod 3)      arithmetic".to_string()), "                 = 1 (mod 3)      arithmetic".to_string()),
            ],
            "says (mod 3) after a relation that is not ≡",
        ),
        case(
            "algebra giving a claim of numerals alone",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("11. (m + 1) − (m + 1) = 0\n    algebra".to_string()), "11. 2 + 2 = 4\n    algebra".to_string()),
            ],
            "step 11 gives algebra for 2 + 2 = 4, which arithmetic can work out",
        ),
        // A step citing a define is the define at its values: one equation,
        // or that its name is a function on a set.
        case(
            "a step citing a define for another function on a set",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("    8.1.  t(k) = C(m, k)·x^(m − k)·y^k\n          D1, from J".to_string()), "    8.1.  p is a function on {0, …, m}\n          D1, from J".to_string()),
            ],
            "and claims that something other than t is a function on a set",
        ),
        case(
            "a step citing a define for no equation",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("    8.1.  t(k) = C(m, k)·x^(m − k)·y^k\n          D1, from J".to_string()), "    8.1.  t(k) ≠ C(m, k)·x^(m − k)·y^k\n          D1, from J".to_string()),
            ],
            "step 8.1 cites D1 and claims no one equation",
        ),
        // The steps are numbered as a reader counts them.
        case(
            "a step number written twice",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("    1.3.  S(k + 1) = (k + 1)((k + 1) + 1)/2".to_string()), "    1.2.  S(k + 1) = (k + 1)((k + 1) + 1)/2".to_string()),
            ],
            "step 1.2 is numbered twice",
        ),
        // A method that opens a block has one, with the parts its record
        // declares, each opening as the record says.
        case(
            "a method that needs a block with none",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("2.  Σ(k = 1 to n) k = n(n + 1)/2\n    calculation\n      Σ(k = 1 to n) k = S(n)              D1\n                      = n(n + 1)/2        instantiate k := n in line 1".to_string()), "2.  Σ(k = 1 to n) k = n(n + 1)/2\n    contradiction".to_string()),
            ],
            "step 2 is justified by contradiction, which needs a block, and has no sub-steps",
        ),
        case(
            "an induction block with no part markers",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("\n    base\n    1.1.".to_string()), "\n    1.1.".to_string()),
                edit("proofs/wiedijk/sum-formula.proof", Some("\n    step\n    let k ∈ ℕ".to_string()), "\n    let k ∈ ℕ".to_string()),
            ],
            "step 1 cites induction, whose block carries the parts",
        ),
        case(
            "a part marker in a block that has no parts",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    2.1.  d ∈ ℤ. d > 1. d divides p. d divides q.".to_string()), "    base\n    2.1.  d ∈ ℤ. d > 1. d divides p. d divides q.".to_string()),
            ],
            "under a contradiction block, which declares no parts",
        ),
        case(
            "a proof block that opens with neither let nor assume",
            vec![
                edit("proofs/wiedijk/reals-uncountable.proof", Some("    let k ∈ ℕ₀                                                        (K1)\n".to_string()), String::new()),
            ],
            "is a proof whose block does not open with `let` or `assume`",
        ),
        case(
            "a case that does not open with an assumption",
            vec![
                edit("proofs/wiedijk/triangle-inequality.proof", Some("    case\n    assume x ≥ 0                                                      (C1)\n".to_string()), "    case\n".to_string()),
            ],
            "part of step 2 does not open with a labelled `assume`",
        ),
        case(
            "an induction's base that opens with a let",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("\n    base\n    1.1.".to_string()), "\n    base\n    let j ∈ ℕ                                                         (J)\n\n    1.1.".to_string()),
            ],
            "the base part of step 1 opens with a",
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
            "a chain line whose algebra does not hold",
            vec![
                edit("tests/elaborator/a-chain-showing-its-work.proof", Some("         = 4k² + 4k + 1        algebra".to_string()), "         = 4k² + 4k + 2        algebra".to_string()),
            ],
            "(2k + 1)² = 4k² + 4k + 2 is not an identity",
        ),
        case(
            "a chain line citing an item with no import",
            vec![
                edit("tests/elaborator/a-chain-showing-its-work.proof", Some("import mundane theorem    stdlib/numbers/multiply-cancel\n".to_string()), String::new()),
            ],
            "mun:multiply-cancel is neither imported nor a theorem of this file",
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
            "a chain line resting on a requires line taken away",
            vec![
                edit("tests/elaborator/a-chain-showing-its-work.proof", Some("    requires b(n) ∈ ℝ: from H2\n".to_string()), String::new()),
            ],
            "nothing says b(n) ∈ ℝ or ∈ ℂ, which this step needs",
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
            "a line number after into without the word line",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("(line 2) into line 3.1".to_string()), "(line 2) into 3.1".to_string()),
            ],
            "a line number after `into` carries the word \"line\": `into line 3.1`",
        ),
        case(
            "a chain that turns round",
            vec![
                edit("tests/elaborator/a-chain-going-down.proof", Some("        > c       H5".to_string()), "        < c       H5".to_string()),
            ],
            "a chain goes one way, and this line says < after one saying ≥",
        ),
        case(
            "an identity element dropped from the middle with nothing saying what is left is a number",
            vec![
                edit("tests/elaborator/textbook-exercise-shapes.proof", Some("    requires b(k) ∈ ℝ: from H1\n".to_string()), String::new()),
            ],
            "step 2 drops an identity element from what the substitution makes, and nothing says b(k) is a number",
        ),
        case(
            "two memberships claimed by one membership step",
            vec![
                edit("proofs/hammack/constant-multiple-limit.proof", Some("    4.2.  ε/(|c| + 1) ∈ ℝ\n          membership".to_string()), "    4.2.  ε/(|c| + 1) ∈ ℝ. |c| + 1 ∈ ℝ.\n          membership".to_string()),
            ],
            "step 4.2 claims 2 sentences by membership, which says one term is in a number system; each is a step of its own",
        ),
        case(
            "a substitute's source label written with the word line",
            vec![
                edit("tests/elaborator/textbook-exercise-shapes.proof", Some("substitute K = a/2 (D1) into H4".to_string()), "substitute K = a/2 (line D1) into H4".to_string()),
            ],
            "a label never carries the word \"line\": `(D1)`",
        ),
        case(
            "a requires line under a naming let",
            vec![
                edit("tests/elaborator/textbook-exercise-shapes.proof", Some("    reads half of a\n".to_string()), "    reads half of a\n    requires a ∈ ℝ: from H1\n".to_string()),
            ],
            "requires line under let D1, which carries none",
        ),
        case(
            "a proof block letting a letter other than the claim's",
            vec![
                edit("tests/elaborator/a-for-all-relating-two-sets.proof", Some("    let u ∈ A ".to_string()), "    let v ∈ A ".to_string()),
                edit("tests/elaborator/a-for-all-relating-two-sets.proof", Some("    1.1.  u ∈ B ∪ A".to_string()), "    1.1.  v ∈ B ∪ A".to_string()),
            ],
            "the block of step 1 lets v, and the claim it proves is about every u; the block opens with the claim's own letter",
        ),
        // `join` puts two lines or more together and `restate` says one
        // again (`SYNTAX.md`): each refused with the other's count.
        case(
            "join one line",
            vec![edit(
                "proofs/setmm/divisor-of-power.proof",
                Some("          restate H4".to_string()),
                "          join H4".to_string(),
            )],
            "joins one line; a step citing one line is written `restate H4`",
        ),
        case(
            "restate two lines",
            vec![edit(
                "proofs/setmm/halves-series.proof",
                Some("                  join 3.2.7, 3.2.10".to_string()),
                "                  restate 3.2.7, 3.2.10".to_string(),
            )],
            "restates 3.2.7, 3.2.10; a step putting several lines together is written `join 3.2.7, 3.2.10`",
        ),
        case(
            "an induction whose base part has no steps",
            vec![edit(
                "proofs/setmm/divisor-of-power.proof",
                Some("    base\n    1.1.  K divides M^1\n          restate H4\n".to_string()),
                "    base\n".to_string(),
            )],
            "has no steps, so nothing shows what it owes",
        ),
        case(
            "an obtain naming no item, its line number without the word line",
            vec![
                edit("proofs/wiedijk/konigsberg.proof", Some("obtain i from line 6.2".to_string()), "obtain i from 6.2".to_string()),
            ],
            "an obtain naming no item takes its line with the word \"line\": `from line 6.2`",
        ),
        case(
            "the word line before a label",
            vec![
                edit("proofs/wiedijk/fundamental-calculus.proof", Some("instantiate x := c in H7, from 3".to_string()), "instantiate x := c in line H7, from 3".to_string()),
            ],
            "a label never carries the word \"line\": `in H7`",
        ),
        case(
            "a method no record declares",
            vec![
                edit("corpus/db/methods.records", Some("method join\n".to_string()), "method joins\n".to_string()),
            ],
            "join is in no record of corpus/db/methods.records",
        ),
        case(
            "a requires line whose reason is neither a method, an item, nor a line",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("          requires k ≥ 1: from K".to_string()), "          requires k ≥ 1: because K".to_string()),
            ],
            "which is neither a method, an item, nor a line",
        ),
        case(
            "a theorem with no steps",
            vec![edit("proofs/wiedijk/empty.proof", None, "theorem empty\n  then 1 = 1\n".to_string())],
            "theorem empty has no steps",
        ),
        // A last step that proves one sentence of a conclusion of two is
        // correct as far as it goes, and every other check passes it.
        case(
            "a last step claiming less than the conclusion",
            vec![edit(
                "proofs/wiedijk/short.proof",
                None,
                "theorem short\n  then 1 + 1 = 2. 2 + 2 = 4.\n\n1.  1 + 1 = 2\n    arithmetic\n"
                    .to_string(),
            )],
            "step 1 is the last, and does not claim what short states",
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
        // A label outside a file's theorems is one label for every theorem
        // below it, and a define says what its name means.
        case(
            "a label given twice outside the theorems",
            vec![
                edit("proofs/wiedijk/geometric-series.proof", Some("       reads the geometric series: the powers of a, from a^0 up to a^n\n".to_string()), "       reads the geometric series: the powers of a, from a^0 up to a^n\n\ndefine H(n) := n + 1, for n ∈ ℕ                                    (D1)\n       reads one more than n\n".to_string()),
            ],
            "label D1 is already used at line 5",
        ),
        case(
            "a define with no reads line",
            vec![
                edit("proofs/wiedijk/geometric-series.proof", Some("       reads the geometric series: the powers of a, from a^0 up to a^n\n".to_string()), String::new()),
            ],
            "carries no `reads` line",
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
        case(
            "a hyphen for the minus sign inside brackets",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let N ∈ ℕ₀    (H1)\n  then N·(N − 1) = N·N − N\n\n1.  N·(N - 1) = N·N − N\n    algebra\n".to_string(),
            )],
            "the `-` at '·(N - 1) ' is a hyphen, and the minus sign is `−`",
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
            "a calculation link working out a floor by arithmetic",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  assume x = ⌊5/2⌋    (H2)\n  then x = 2\n\n1.  x = 2\n    calculation\n      x = ⌊5/2⌋            H2\n        = 2                arithmetic\n".to_string(),
            )],
            "a link of step 1 names arithmetic for ⌊5/2⌋ = 2, which works out floor",
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
        case(
            "a false factorial by arithmetic",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  then 4! = 20\n\n1.  4! = 20\n    arithmetic\n".to_string(),
            )],
            "step 1 claims 4! = 20, which is false",
        ),
        case(
            "a requires line under a join",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  assume x > 0    (H2)\n  assume x < 2    (H3)\n  then x > 0 and x < 2\n\n1.  x > 0 and x < 2\n    join H2, H3\n    requires x ≠ 0: weakening, from H2\n".to_string(),
            )],
            "step 1 is a join, which asks nothing of the lines it puts together, and carries a requires line",
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
        case(
            "a last case with no steps",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  assume x > 2 or x > 1    (H2)\n  then x > 0\n\n1.  x > 0\n    cases, from H2\n\n    case\n    assume x > 2    (C1)\n\n    1.1.  x > 0\n          inequalities, from C1\n\n    case\n    assume x > 1    (C2)\n".to_string(),
            )],
            "this case has no steps, and the theorem ends under it; write its steps, or end its assumption `, which is the claim`",
        ),
        case(
            "a proof block with no steps under its let",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  then for all y ∈ ℝ, y = y\n\n1.  For all y ∈ ℝ, y = y.\n    proof\n    let y ∈ ℝ    (K1)\n".to_string(),
            )],
            "K1 opens a part with no steps, and the theorem ends under it",
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
        // A define names a thing, and a name the theorem has not given.
        case(
            "define a name as a statement",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  then x = x\n\nlet P = x > 0    (D1)\n    reads x is positive\n\n1.  x = x\n    algebra\n".to_string(),
            )],
            "define D1 says P is x > 0, a statement, and a define names a thing: a number, a set or a map",
        ),
        case(
            "define a letter the theorem already introduces",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  then x = x\n\nlet x = 1, a real number    (D1)\n    arithmetic\n    reads one\n\n1.  x = x\n    algebra\n".to_string(),
            )],
            "define D1 names x, which theorem planted already introduces",
        ),
    ]
}
