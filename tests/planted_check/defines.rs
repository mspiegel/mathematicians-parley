//! The planted cases about defines: functions by a rule, by cases or by recursion, a define's kind and reason, its domain, and definitions written out.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
        // A step citing a theorem of its own file reads the defines that
        // theorem is stated over, those above it, and no other: D2 is
        // written below `above`, so `below` claims R(k) = k + 1 of a theorem
        // that says nothing of R, and does not cite D2.
        case(
            "read a define written below the theorem of the file a step cites",
            vec![edit(
                "proofs/wiedijk/stated-over.proof",
                None,
                "define S(k) := k + 1, for k ∈ ℕ                                      (D1)\n       reads one more than k\n\ntheorem above\n  let k ∈ ℕ                                                           (H1)\n  then S(k) = k + 1\n\n1.  S(k) = k + 1\n    D1\n\ndefine R(k) := k + 1, for k ∈ ℕ                                      (D2)\n       reads also one more than k\n\ntheorem below\n  let k ∈ ℕ                                                           (H1)\n  then R(k) = k + 1\n\n1.  R(k) = k + 1\n    thm:above\n".to_string(),
            )],
            "proofs/wiedijk/stated-over.proof:19  step 1 claims something that thm:above does not conclude",
        ),
        // A sum of squares of reals is not shown to be a natural number by
        // the let's reason. The checker does not judge a let's kind against
        // its reason; it reports what the planted kind makes surplus below.
        case(
            "a let saying a kind of number its reason does not show",
            vec![edit(
                "proofs/wiedijk/cauchy-schwarz.proof",
                Some("    let A = Σ(k = 1 to n) a(k)², a real number                        (D1)".to_string()),
                "    let A = Σ(k = 1 to n) a(k)², a natural number                     (D1)".to_string(),
            )],
            "the requires line of step 5.10 says A > 0, which the step's other lines already say",
        ),
        // A definition with no metamath-proof concludes only what its record
        // says, and a step claiming something else of it is refused.
        case(
            "unfold a definition with no metamath-proof into what it does not say",
            vec![edit(
                "proofs/wiedijk/intermediate-value.proof",
                Some("10. For all s ∈ S, s ≤ c.".to_string()),
                "10. For all s ∈ S, s < c.".to_string(),
            )],
            "step 10 claims something that def:upper-bound does not conclude",
        ),
        // Continuity unfolds into what its definition says: with δ where ε
        // belongs, or with δ ≥ 0 where the definition says δ > 0, it is not
        // what the definition concludes.
        case(
            "unfold continuity into what it does not say",
            vec![edit(
                "proofs/wiedijk/intermediate-value.proof",
                Some("|f(x) − f(c′)| < ε for all x".to_string()),
                "|f(x) − f(c′)| < δ for all x".to_string(),
            )],
            "step 15 claims something that def:continuous-on does not conclude",
        ),
        case(
            "unfold continuity with a weaker bound than it gives",
            vec![edit(
                "proofs/wiedijk/intermediate-value.proof",
                Some("there exists δ > 0 such that".to_string()),
                "there exists δ ≥ 0 such that".to_string(),
            )],
            "step 15 claims something that def:continuous-on does not conclude",
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
        // Every name on the page is a letter, so a longer name is several.
        case(
            "define a function with a name of several letters",
            vec![
                edit("proofs/wiedijk/tri.proof", None, TRI.replacen("define T(k)", "define tri(k)", 1)),
            ],
            "a define names one letter, perhaps with a subscript or a prime, and 'tri' is not one",
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
        // A define of two arguments gives each one's domain in the order
        // the brackets name them (`SYNTAX.md`).
        case(
            "a define of two whose domains are out of order",
            vec![
                edit("proofs/wiedijk/geometric-series.proof", Some("for a ∈ ℝ, n ∈ ℕ₀".to_string()), "for n ∈ ℕ₀, a ∈ ℝ".to_string()),
            ],
            "define G(a, n) gives the domain of n",
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
        // A define with an argument is a function, and a function is defined
        // somewhere: its rule alone says what it does and not where.
        case(
            "define a function and give no domain",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("let B = {x ∈ A : x ∉ f(x)}".to_string()), "let B(y) = {x ∈ A : x ∉ f(x)}".to_string()),
            ],
            "says no domain",
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
        // A define's kind says its function's type once (`SYNTAX.md`): a
        // requires line saying it again does no work.
        case(
            "say a kinded define's type again on a requires line",
            vec![
                edit("proofs/wiedijk/mean-value.proof", Some("let F(x) = f(x) + g(x), for x ∈ [a, b]                                (D3)\n       reads".to_string()), "let F(x) = f(x) + g(x), a real number, for x ∈ [a, b]                 (D3)\n    membership, from D2, H4\n    reads".to_string()),
            ],
            "the requires line of step 12 says F : [a, b] → ℝ, and neither thm:continuous-sum nor the step's other lines ask for it",
        ),
        // A kinded define's values are in its kind by name: a membership
        // built from f(x) asks for f(x), not for the rule f stands for.
        case(
            "give a define built from a kinded one no reason",
            vec![
                edit("proofs/wiedijk/liouville.proof", Some("    reads F on the real line\n".to_string()), "    reads F on the real line\n\nlet k(x) = f(x) + 1, a real number, for x ∈ ℝ                         (D9)\n    membership\n    reads f raised by 1\n".to_string()),
            ],
            "is not built from what let D9 cites: nothing says f(x) ∈ ℝ, which it needs",
        ),
        // A define's reason is the define's own, and the message names the
        // define, not the step below it.
        case(
            "leave out the line a define's reason builds its kind from",
            vec![
                edit("proofs/setmm/rounding-error.proof", Some("    membership, from 1\n    reads the error".to_string()), "    membership\n    reads the error".to_string()),
            ],
            "⌊A + 1/2⌋ − A ∈ ℝ is not built from what let D1 cites",
        ),
        // A rule by cases is said in a message on one line, as a sentence
        // writes it.
        case(
            "give a define by cases a kind its cases are not in",
            vec![
                edit("proofs/wiedijk/rationals-countable.proof", Some("           1    otherwise,  for x ∈ ℚ                                 (D2)\n       reads".to_string()), "           1    otherwise,  a positive integer, for x ∈ ℚ             (D2)\n    membership\n    reads".to_string()),
            ],
            "for all x ∈ ℚ, 0 if numer(x) ≥ 0, 1 otherwise ∈ ℕ is not built from what let D2 cites",
        ),
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
        case(
            "define a sequence by recursion outside any theorem",
            vec![
                edit("proofs/wiedijk/euclid.proof", Some("theorem euclid".to_string()), "define c(0) := 1, c(k + 1) := c(k), for k ∈ ℕ₀                     (D9)\n       reads a constant sequence\n\ntheorem euclid".to_string()),
            ],
            "is written in the theorem that uses it",
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
        // A define's name is not a letter introduced in a number system:
        // that x₁ is real rests on min-real, and abs-difference-lt asks it.
        case(
            "leave out a define's membership where an item asks it",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("    let x₁ = min(b, c + δ/2), a real number                            (D2)\n           mun:min-real x := b, y := c + δ/2\n".to_string()), "    let x₁ = min(b, c + δ/2)                                           (D2)\n".to_string()),
            ],
            "step 16.19 cites mun:abs-difference-lt, which asks for",
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
        case(
            "a define with no reads line",
            vec![
                edit("proofs/wiedijk/geometric-series.proof", Some("       reads the geometric series: the powers of a, from a^0 up to a^n\n".to_string()), String::new()),
            ],
            "carries no `reads` line",
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
