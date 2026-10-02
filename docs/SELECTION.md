# Selection of the theorems

The theorems for the example corpus, chosen by the coverage rule in
`GOALS.md`: each stresses one thing the readable layer has to handle. All
candidates are on Wiedijk's list of 100 theorems, all are proved in
set.mm, and all have Mizar and Isabelle versions, so those criteria did
not discriminate and are not shown. The informal source is Hammack's Book
of Proof where it has the theorem and ProofWiki otherwise; entries marked
"verify" are from memory and have not been checked against the book.

Measurements are from set.mm as of 2026-09-17, made with a script that
decodes each stored compressed proof and counts the steps whose result is
a `|-` statement. Baggage columns record what the up direction has to hide
for that theorem: whether the statement is in deduction form (`ph ->`
throughout), the class variables in the statement, set-existence
hypotheses (`A e. _V`), and the number of disjoint-variable pairs among the
statement's variables.

## The ten

| # | theorem | feature stressed | set.mm | essential steps | deduction form | class vars | set-existence hyps | dv pairs | informal source | state |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | √2 is irrational | contradiction; definition unfolding; calculation chain | sqrt2irr | 99 (+69 in sqrt2irrlem, 74 in zesq) | no | none | none | 0 | Hammack ch. 6 | pilot written |
| 2 | 1 + 2 + ... + n = n(n + 1)/2 | induction | arisum | 73 | no | N | none | 1 | Hammack ch. 10 | pilot written |
| 3 | triangle inequality, real case | proof by cases | abstri | 78 | no | A, B | none | 0 | ProofWiki; Hammack exercise (verify) | pilot written |
| 4 | infinitely many primes | existence by construction | infpn, infpnlem1, infpnlem2 | 2 + 58 + 38 | no | K, M, N | none | 3 to 5 | Hammack ch. 6 | pilot written |
| 5 | Bezout's identity | existence via a least element; definition of gcd | bezout | 47 | no | A, B | none | 5 | Hammack ch. 7 | draft written |
| 6 | Cantor's theorem | set-theoretic argument | canth | 21 | no | A, F | `A e. _V` | 0 | Hammack ch. 14 (verify); ProofWiki | draft written |
| 7 | a set with n elements has 2ⁿ subsets | counting | hashpw | 25 | no | A | none | 0 | Hammack ch. 1 and 10 (verify) | draft written |
| 8 | intermediate value theorem | quantifier alternation; completeness of ℝ | ivth, ivthle | 16 + 69 | yes | A, B, D, F, U | none | 13 | ProofWiki | draft written |
| 9 | isosceles triangle theorem | geometry | isosctr | 40 | no | A, B, C, F | none | 7 | ProofWiki | draft written |
| 10 | sum of a geometric series | calculation chain in deduction form; induction | geoser | 18 | yes | A, N | none | 3 | ProofWiki; Hammack ch. 10 exercise (verify) | draft written |

## Notes on each choice

1. **√2.** No baggage at all in the statement, which is why it was the
   right first pilot. The pilot's proof elaborates to a different kernel
   proof from set.mm's, which descends by induction.
2. **Arithmetic series.** set.mm states it for N ∈ ℕ₀ with Σ notation; the
   pilot defines the sum by recursion and starts at 1. The elaborator will
   have to bridge Σ over an interval to the recursive definition.
3. **Triangle inequality.** set.mm's abstri is over ℂ and proved through
   the complex absolute value. The readable proof is the school one over
   ℝ, by cases on the signs of a and b, using |x| defined by cases. That
   makes it the first user of a `cases` method with part markers, which
   is why it is next. Its kernel proof will differ from set.mm's, as √2's
   did.
4. **Infinitude of primes.** set.mm's infpn says every N has a prime above
   it, in two steps from its lemmas, which is where the content is. The
   readable proof is Euclid's: given primes p₁ ... pₙ, the number
   p₁·...·pₙ + 1 has a prime factor not among them. That is an existence
   proof by exhibiting a construction, and it needs a product over a
   finite list or the factorial, which the database must define. Hammack
   uses the factorial form, N! + 1.
5. **Bezout.** Existence of x and y with ax + by = gcd(a, b). Hammack's
   proof takes the least positive element of {ax + by}, which needs the
   well-ordering of ℕ as a cited principle, and unfolds the definition of
   gcd. It is the second existence proof, chosen because its witness comes
   from a least element rather than a construction.
6. **Cantor's theorem.** The one statement among the ten with a
   set-existence hypothesis, `A e. _V`, which READERS.md says is hidden
   entirely. It is therefore the test of that rule. set.mm's canth is 21
   steps; the readable proof is the diagonal set {x ∈ A : x ∉ f(x)}.
7. **Subsets.** set.mm's hashpw states ♯𝒫A = 2^♯A for finite A. Hammack
   proves it by induction on n, so this is a second induction, but the
   feature it stresses is counting: what "has n elements" means, and how a
   bijection or a count is written for Reader A.
8. **Intermediate value theorem.** The heaviest baggage of the ten:
   deduction form, five class variables, thirteen disjointness pairs, and
   a statement in terms of continuous functions on a subset D of ℂ. The
   readable proof needs the least upper bound property of ℝ, which is
   above the school ceiling and will have to be introduced through a
   pointer. It is on the list because quantifier alternation is the
   feature most likely to break the syntax, and this is the smallest
   theorem on Wiedijk's list that has it.
9. **Isosceles triangle.** set.mm's plane geometry is the complex plane,
   and angles are the function F defined through the complex logarithm,
   which appears as a hypothesis of every geometry theorem. isosctr is the
   lightest of them at 40 steps; the law of cosines is 88, Pythagoras in
   set.mm's form (cphpyth) is stated in pre-Hilbert spaces and is far from
   school geometry. The readable proof will have to hide the encoding of
   the plane entirely, which is the point of including one geometry
   theorem.
10. **Geometric series.** In deduction form with a `ph` context, and a
    short proof by induction whose step is a calculation. Chosen over the
    binomial theorem (83 steps, three class variables) as the smaller test
    of the same things.

## Considered and not chosen

| theorem | set.mm | essential steps | why not |
|---|---|---|---|
| 2 + 2 = 4 | 2p2e4 | 11 | one line in the readable language; its interest is the expansion of `arithmetic`, which is open question 6, not a corpus item |
| principle of induction | nnind | 24 | it is a method, not a theorem to render; the induction pilot cites it |
| Schröder–Bernstein | sbth | 29 | a good set-theoretic proof, but Cantor is shorter and carries the set-existence hypothesis |
| ℚ is countable | qnnen | 39 | no class variables and no baggage, but the set.mm proof goes through a pairing function far from Hammack's grid argument |
| ℝ is uncountable | ruc | 12 | set.mm uses nested intervals; Hammack uses decimals; either readable proof needs machinery a school reader has not seen |
| binomial theorem | binom | 83 | covered by the geometric series at a third of the size |
| number of combinations | hashbc | 118 | covered by hashpw at a fifth of the size |
| inclusion–exclusion | incexc | 134 | set.mm's is the general form over a family; the two-set form is a corollary |
| law of cosines | lawcos | 88 | same angle encoding as isosctr, twice the size |
| Pythagorean theorem | cphpyth | 74 | stated in pre-Hilbert spaces with seven class variables |
| fundamental theorem of arithmetic | 1arith2 | 13 | the statement uses a function into prime-count sequences; the school statement is not what set.mm proves |
| Euclid's algorithm | eucalg | 72 | stated through `seq`; Bezout covers the gcd material |
| divisibility by 3 rule | 3dvds | 122 | stated for digit sequences via sums, heavy |
| mean value theorem | mvth | 108 | derivatives; IVT covers quantifier alternation at a sixth of the size |

## Recommended third pilot

The triangle inequality for reals, by cases. It is the first use of a
`cases` method, which will use the part markers decided for induction,
and it is small: two variables, no deduction form, no disjointness. Its
definition of |x| is itself by cases, so the pilot also tests a
definition whose unfolding branches. After it, the infinitude of primes,
for the existence-by-construction feature.

## Open items the table raises

- Four of the ten will elaborate to kernel proofs different from set.mm's
  (√2, triangle inequality, infinitude of primes, subsets). The archive
  then holds two proofs of the same statement, and the checker of decision
  10 in `GOALS.md` compares statements, not proofs, so this is allowed.
- Three of the ten need a principle beyond algebra: well-ordering for
  Bezout, the least upper bound property for IVT, and the existence of a
  prime factor for the infinitude of primes. Each will be a database item
  with a pointer, and each is above what Reader A's school background
  provides, which is what the pointer rule was designed for.
- The informal-source entries marked "verify" should be checked against
  the book before any of those pilots is written.

## The next five

The ten are written and every theorem the corpus proves elaborates from
set.mm with nothing assumed. The next five are chosen by the same coverage
rule, now asking what none of the ten exercises. All five are on Wiedijk's
list and in set.mm's main body, not a mathbox. Measured on the same set.mm
with a one-off script that is not kept.

| # | theorem | feature stressed | set.mm | essential steps | deduction form | class vars | set-existence hyps | dv pairs | informal source |
|---|---|---|---|---|---|---|---|---|---|
| 11 | divisibility by 3 rule | congruence; a sum whose terms a function gives | 3dvds | 122 | no | F, N | none | 2 | ProofWiki; Hammack defines congruence (Definition 5.1) but not the rule |
| 12 | binomial theorem | a finite sum split and reindexed; binomial coefficients | binom | 83 | no | A, B, N | none | 3 | ProofWiki; Hammack states it as Theorem 3.1 (§3.6) and leaves the induction to exercise 10.23, with Pascal's rule as Equation (3.3) |
| 13 | sum of the reciprocals of the triangular numbers | an infinite series: a limit of partial sums, telescoping | trirecip | 42 | no | none | none | 0 | ProofWiki |
| 14 | Schröder–Bernstein | comparing sizes by injection; a fixed point, built as a union rather than by recursion; a function defined piecewise | sbth | 29 | no | A, B | none | 0 | Hammack ch. 14 (verify); ProofWiki |
| 15 | Lagrange's theorem | an algebraic structure, which set.mm encodes through `Base`, `+g` and `SubGrp` | lagsubg | 27 | no | G, X, Y | none | 0 | ProofWiki |

Three of these were set aside when the ten were chosen: Schröder–Bernstein
because Cantor was shorter and carried the set-existence hypothesis, the
binomial theorem because the geometric series covered induction at a third
of the size, and the divisibility rule as heavy. Those were reasons to prefer
another theorem for the same feature. The question now is which features are
still untested, and a reindexed sum, a congruence and an injection-built
bijection are among them.

1. **Divisibility by 3.** Written: `proofs/divisibility-by-three.proof`, with
   its design record in `docs/pilot/divisibility-by-three.md`, and both of its
   theorems elaborate with nothing assumed. The first congruence in the
   corpus: 10ᵏ leaves
   remainder 1 on division by 3, so a number and its digit sum leave the
   same remainder. set.mm states it for a digit function F : (0…N) → ℤ,
   and the readable statement is about the digits of a number, so the
   statement itself is the first thing to settle. Its 122 steps are what
   the up direction would hide; the readable proof is a few lines.
2. **Binomial theorem.** Written: `proofs/binomial.proof`, with its design
   record in `docs/pilot/binomial.md`, and both of its theorems elaborate with
   nothing assumed. Induction again, but the step shifts a sum's index,
   extends two sums by a zero term and applies Pascal's rule, where the
   geometric series only adds a term at the end (`fsump1`).
3. **Triangular reciprocals.** Written: `proofs/triangular-reciprocals.proof`,
   with its design record in `docs/pilot/triangular-reciprocals.md`, and it
   elaborates with nothing assumed. No class variables and nothing to hide in
   the statement. The first limit of a sequence and the first sum over all
   of ℕ: the partial sums telescope to 2 − 2/(n + 1), and the ε-style
   argument the intermediate value theorem made for functions is made for
   a sequence.
4. **Schröder–Bernstein.** Short in set.mm and long on the page. The
   readable proof follows the chain of repeated images and defines the
   bijection by cases on it, so it needs a set defined by recursion and a
   function defined piecewise, neither of which the corpus has.
5. **Lagrange's theorem.** set.mm's group is a structure, a function from
   slot indices to its base set and operation, and the essential hypothesis
   `X = ( Base ` G )` is how every group theorem names its set. A reader
   never sees that encoding, which makes this the algebraic counterpart of
   the geometry theorem. The argument reuses the corpus's counting: the
   cosets partition the group and each has the size of the subgroup.

Order: 11 and 12 first, since each extends machinery the corpus already
has (divisibility and sums); then 13, which extends the analysis; 14 and 15
bring the most that is new. Before each pilot, its informal source is
checked and the entries marked "verify" confirmed or replaced.

Considered for these five and not chosen: the mean value theorem (`mvth`),
which rests on Rolle's theorem and the extreme value theorem, a chain of
three large proofs stated in deduction form; the countability of ℚ
(`qnnen`), for the reason in the table above; Wilson's theorem (`wilth`)
and Fermat's little theorem (`fermltl`), which would be a second congruence
proof after 11; and Königsberg, Ramsey and Bertrand, each of which depends
on a great deal of set.mm before its argument starts.

## Theorem 16: recursion

The corpus leans on recursion already: Σ, n! and aⁿ are each defined in
set.mm by `seq`, and the library names them, so a reader never meets it.
What no proof can yet do is define a sequence of its own by a first term
and a step. A proof that says "and so on", "repeat" or "the n-th" needs
that, and recursion and iteration are one feature, since set.mm builds
both with `seq`. Theorem 16 is chosen to be the test of it, so that the
feature is tested where it is the whole argument rather than beside a
theorem's other new features.

| # | theorem | feature stressed | set.mm | essential steps | deduction form | class vars | set-existence hyps | dv pairs | informal source |
|---|---|---|---|---|---|---|---|---|---|
| 16 | the greatest common divisor algorithm (Euclid's algorithm) | a sequence defined by recursion; a step defined by cases | eucalg | 72 | no | A, E, M, N, R | none | 8 | Wiedijk #69; ProofWiki |

set.mm states it as a sequence of pairs: `R = seq 0 ( ( E o. 1st ) ,
( NN0 X. { A } ) )`, starting at A = ⟨M, N⟩, where the step E sends
⟨x, y⟩ to ⟨y, x mod y⟩, or leaves it where y = 0; and it proves that after
N steps the first of the pair is gcd(M, N). Three lemmas are the proof's
parts: `eucalgval`, what one step does; `eucalginv`, that a step keeps the
gcd; and `eucalglt`, that the second number shrinks until it is 0. gcd,
divisibility and division with a remainder are in the library from Bezout
and the primes proof, so what is new is the recursion, and the step, a
function defined by cases, shares its form with the bijection of 14.

One thing to settle before the pilot: set.mm steps through pairs and reads
them with `1st` and `2nd`, where a textbook writes two sequences side by
side, a(k + 1) = b(k) and b(k + 1) = a(k) mod b(k). Either the language
gains notation for a pair, or a `define` may state two sequences together.

Settled for the second: the page writes the two sequences, and the pairs
are the elaborator's, since set.mm's storage is not what a reader should
have to read (`docs/pilot/euclid.md`). The informal source was checked against
ProofWiki's Euclidean algorithm before the pilot: the same update, the same
three facts (the remainder is below the divisor, gcd(a, b) = gcd(b, r),
gcd(r, 0) = r), and the same termination by falling remainders.

Considered and not chosen: the derangements formula (#88), where set.mm
defines a derangement by counting permutations and the recurrence
`subfacp1` is a result about them, not a definition; the sum of k-th powers
(#77), which goes through Bernoulli polynomials; Pell's equation (#39),
where recursion describes the solutions but the proof is number theory; and
the principle of induction (#74), a method the corpus already has.

## The next four

The sixteen are written and elaborate with nothing assumed. The next four
are chosen by the same coverage rule, asking what none of the sixteen
exercises. All four are on Wiedijk's list and in set.mm's main body.
Measured on the same set.mm with a one-off script that is not kept; it
reproduces every count in the tables above except ivth's disjoint pairs,
which it makes 11, so that column may read low.

| # | theorem | feature stressed | set.mm | essential steps | deduction form | class vars | set-existence hyps | dv pairs | informal source |
|---|---|---|---|---|---|---|---|---|---|
| 17 | Euclid–Euler theorem (perfect numbers) | a function defined by a sum over a set given by a condition, σ; multiplicativity | perfect (Euclid's half: perfect1) | 98 (perfect1: 75) | no | N | none | 1 | Wiedijk #70; ProofWiki |
| 18 | De Moivre's formula | complex numbers and the trigonometric functions | demoivre | 20 | no | A, N | none | 0 | Wiedijk #17; ProofWiki |
| 19 | mean value theorem | the derivative; a function the proof defines to cite a theorem at | mvth, citing rolle | 108 (rolle: 259) | yes | A, B, F | none | 3 | Wiedijk #75; ProofWiki |
| 20 | ℚ is countable | countability; a proof built mostly on the corpus's own theorems | qnnen | 39 | no | none | none | 0 | Wiedijk #3; Hammack ch. 14 (verify) |

17. **Perfect numbers.** The first function a proof reads as a sum over a
    set picked out by a condition: σ(n), the sum of the divisors of n. The
    library needs σ and its multiplicativity, and the divisors of a prime
    power written as a set, 1, 2, …, 2ᵏ, whose sum is a geometric series the
    corpus already proves. `perfect` is the full equivalence; Euclid's half,
    `perfect1`, that 2ᵖ⁻¹(2ᵖ − 1) is perfect when 2ᵖ − 1 is prime, tests the
    same feature at three quarters of the size, and Euler's half adds a
    longer argument about the odd part rather than anything new.
18. **De Moivre's formula.** The first complex numbers on the page, and the
    first cos and sin: (cos x + i sin x)ⁿ = cos nx + i sin nx. set.mm proves
    it through the exponential function for every integer n; the textbook
    proof is induction on n with the angle-addition formulas, so like √2 it
    elaborates to a proof other than set.mm's, and the readable statement
    is for n ∈ ℕ₀, citing the stronger item. Smallest of the four.
19. **Mean value theorem.** The first derivative. It was set aside when the
    ten were chosen as the last of a chain of three large proofs, Rolle's
    theorem on the extreme value theorem. Taken instead as a library item
    with a pointer, as completeness is for the intermediate value theorem,
    `rolle` leaves a short readable proof: g(x) = f(x) − (f(b) − f(a))/(b −
    a)·(x − a) has g(a) = g(b), and Rolle's theorem applied to g gives the
    point. Deduction form, as the intermediate value theorem is, and it
    needs notation for the derivative and a function the proof defines.
20. **ℚ is countable.** Set aside when the ten were chosen because set.mm's
    pairing function is far from Hammack's grid argument. The corpus now
    proves Schröder–Bernstein and that a rational is p/q in lowest terms,
    so a readable proof can inject ℕ into ℚ, inject ℚ into ℕ, and cite
    both: the first theorem built mainly on the corpus's own results. What
    injects ℚ into ℕ is to be settled first, through unique factorisation
    or a pairing.

Order: 17 and 18 first, since each adds one object to machinery the corpus
has (sums over a range, induction); then 19, which extends the analysis;
then 20, once its injection is settled. Before each pilot, its informal
source is checked and the entry marked "verify" confirmed or replaced.

Theorem 17 is written, as Euclid's half (`perfect1`), and elaborates with
nothing assumed: `proofs/perfect-numbers.proof`, with
`docs/pilot/perfect-numbers.md`. ProofWiki's proof matched set.mm's step
for step.

Theorem 18 is written and elaborates with nothing assumed:
`proofs/de-moivre.proof`, with `docs/pilot/de-moivre.md`. ProofWiki proves a
form with a modulus r, from n = 1, through the product of complex numbers in
polar form; the corpus proves the textbook form planned above, for
n ∈ ℕ₀ by induction with the angle-addition formulas.

Theorem 19 is written and elaborates with nothing assumed:
`proofs/mean-value.proof`, with `docs/pilot/mean-value.md`. It follows
ProofWiki's proof 1, adding a line h·x to f rather than subtracting the
chord through (a, f(a)); Rolle's theorem and the sum rules are named
library items.

Theorem 20 is written and elaborates with nothing assumed:
`proofs/rationals-countable.proof`, with `docs/pilot/rationals-countable.md`.
ℚ injects into ℕ by x ↦ 2^|p|·3^q·5^s for x = p/q in lowest terms, s
recording the sign, and Schröder–Bernstein, which the corpus proves, gives
the bijection. Unique factorisation is the one new named item.

Considered for these four and not chosen: Wilson's theorem (#51), a pairing
argument mod p close to divisibility by 3 and Lagrange; the factor theorem
(#89), where set.mm's `Poly` encoding would have to be hidden as groups
were; the inequality of arithmetic and geometric means (#38), stated
through `gsum` in the multiplicative monoid; the fundamental theorem of
arithmetic (#80), still stated through a function into prime-count
sequences; and the sum of the angles of a triangle (#27), which set.mm's
signed angles make π or −π rather than 180°.
