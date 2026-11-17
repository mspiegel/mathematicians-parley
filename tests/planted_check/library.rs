//! The planted cases about the records database and the library: records, notation records, method records and library proofs.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
        // A method decides a word only where the word's record names it
        // (`DATABASE.md`, `decided`). With `arithmetic` struck from
        // `divides`, every divisibility of numerals it settles is refused.
        case(
            "a divisibility arithmetic decides with its record not naming it",
            vec![edit(
                "corpus/stdlib/divisibility.records",
                Some("  then        d divides n ↔ there is k ∈ ℤ with n = d·k\n  decided     arithmetic, inspection".to_string()),
                "  then        d divides n ↔ there is k ∈ ℤ with n = d·k\n  decided     inspection".to_string(),
            )],
            "4 divides 2 is a word divides defines, and arithmetic decides a word only where its record says so in a `decided` field",
        ),
        // `card-remove` loses its metamath-proof, and the edit to its record
        // changes what it concludes, so the step citing it claims what it
        // does not.
        case(
            "cite a theorem the database gives no metamath-proof for",
            vec![edit(
                "corpus/stdlib/counting.records",
                Some("  then        |X ∖ {a}| = k\n  metamath-proof hashdifsnp1 with V := X, N := a, Y := k\n".to_string()),
                "  then        |X ∖ {a}| ≤ k\n  metamath-proof not yet implemented\n".to_string(),
            )],
            "step 1.7 claims something that mun:card-remove does not conclude",
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
            "name a library function with a word a notation writes",
            vec![
                edit("corpus/stdlib/divisibility.records", Some("definition gcd\n".to_string()), "definition divides\n".to_string()),
            ],
            "'divides' is a word a notation writes, so it cannot also name a function",
        ),
        case(
            "an item that says nothing about where it comes from",
            vec![
                edit("corpus/stdlib/sets.records", Some("mundane theorem powerset-empty\n  then        𝒫∅ = {∅}\n  metamath-proof pw0".to_string()), "mundane theorem powerset-empty\n  then        𝒫∅ = {∅}".to_string()),
            ],
            "powerset-empty has no `metamath-proof`",
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
            "a method no record declares",
            vec![
                edit("corpus/db/methods.records", Some("method join\n".to_string()), "method joins\n".to_string()),
            ],
            "join is in no record of corpus/db/methods.records",
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
    ]
}
