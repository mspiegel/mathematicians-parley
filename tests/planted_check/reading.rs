//! The planted cases about how text is read: characters, notations, bound letters, phrases, names and sorts.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
        // Two pairs are compared coordinate by coordinate (`METHODS.md`,
        // Pairs): equal pairs said to differ are false by arithmetic, a
        // difference by algebra rescales one a step cites, and inspection
        // finds a pair among listed ones by its coordinates.
        // A value runs to the comma that opens the next naming or the
        // `from` list (`GRAMMAR.md`, Justifications), so a naming written
        // without its `:=` is read as more of the value before it, and the
        // message names what was taken into it: here a chain of equations,
        // which stands inside the value's formula.
        case(
            "a naming written without its :=",
            vec![edit(
                "tests/elaborator/a-value-with-a-comma.proof",
                Some("Q := x = 1, from H5, H6".to_string()),
                "Q = x = 1, from H5, H6".to_string(),
            )],
            "a value step 1 gives: the chain of equations Q = x = 1 stands inside another formula, and a chain is a whole sentence",
        ),
        // A chain of equations is a whole sentence (`SYNTAX.md`), never a
        // part of another formula.
        case(
            "a chain of equations inside another formula",
            vec![edit(
                "tests/elaborator/chains.proof",
                Some("  assume x = y = z                                                    (H4)\n  then y + 1 = z + 1".to_string()),
                "  assume if x = 1 then x = y = z                                      (H4)\n  then y + 1 = z + 1".to_string(),
            )],
            "the chain of equations x = y = z stands inside another formula, and a chain is a whole sentence",
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
        case(
            "a justification that matches no production",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("         = 4k² + 4k + 1        algebra\n".to_string()), "         = 4k² + 4k + 1        algebra from 1 and 2\n".to_string()),
            ],
            "matches no production",
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
        case(
            "obtain a name without stating its sort",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("1.  k ∈ ℤ. n = 2k + 1.\n    obtain k: def:odd, from H2".to_string()), "1.  n = 2k + 1.\n    obtain k: def:odd, from H2".to_string()),
            ],
            "without stating its sort",
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
        case(
            "say a property is a function into a formula",
            vec![
                edit("corpus/stdlib/sets.records", Some("mundane theorem set-builder-subset\n  let X be a set                                                      (H1)\n  let P be a property of the elements of X                            (H2)".to_string()), "mundane theorem set-builder-subset\n  let X be a set                                                      (H1)\n  let P : X → formula                                                 (H2)".to_string()),
            ],
            "which is a sort and not a set",
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
        // A `let` names a function's type and nothing more, unless `be` says a
        // property of it; a property slipped in as the codomain went unasked.
        case(
            "state a property in a let line as the codomain",
            vec![
                edit("corpus/stdlib/functions.records", Some("  let g : Y → X be one-to-one ".to_string()), "  let g : Y → X is one-to-one ".to_string()),
            ],
            "says more than a function's type",
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
        // A group is let with its operation and its identity; one without the
        // identity is no introduction at all.
        case(
            "let a group without naming its identity",
            vec![
                edit("proofs/wiedijk/lagrange.proof", Some("let G be a finite group with operation · and identity e".to_string()), "let G be a finite group with operation ·".to_string()),
            ],
            "is none of the 13 introductions",
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
        case(
            "write a phrase whose words say and beside an and without brackets",
            vec![
                edit("tests/elaborator/a-phrase-with-and.proof", Some("  assume (d is a common divisor of a and b) and d > 0".to_string()), "  assume d is a common divisor of a and b and d > 0  ".to_string()),
            ],
            "`is a common divisor of` and `and` are not ordered against each other",
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
            "name a number with the derivative's spelling",
            vec![
                edit("proofs/wiedijk/mean-value.proof", Some("  assume a < b ".to_string()), "  let f′ ∈ ℝ                                                          (H9)\n  assume a < b ".to_string()),
            ],
            "f′ is how the derivative of the function f is written, so it cannot name anything else: call it f₁",
        ),
        case(
            "a line number after into without the word line",
            vec![
                edit("proofs/wiedijk/bezout.proof", Some("(line 2) into line 3.1".to_string()), "(line 2) into 3.1".to_string()),
            ],
            "a line number after `into` carries the word \"line\": `into line 3.1`",
        ),
        case(
            "a substitute's source label written with the word line",
            vec![
                edit("tests/elaborator/textbook-exercise-shapes.proof", Some("substitute K = a/2 (D1) into H4".to_string()), "substitute K = a/2 (line D1) into H4".to_string()),
            ],
            "a label never carries the word \"line\": `(D1)`",
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
            "a hyphen for the minus sign inside brackets",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let N ∈ ℕ₀    (H1)\n  then N·(N − 1) = N·N − N\n\n1.  N·(N - 1) = N·N − N\n    algebra\n".to_string(),
            )],
            "the `-` at '·(N - 1) ' is a hyphen, and the minus sign is `−`",
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
        case(
            "a line number after into without the word line, in an induction",
            vec![edit(
                "tests/elaborator/induction-under-a-condition.proof",
                Some("(line 1.2.7) into line 1.2.6".to_string()),
                "(line 1.2.7) into 1.2.6".to_string(),
            )],
            "a line number after `into` carries the word \"line\": `into line 1.2.6`",
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
    ]
}
