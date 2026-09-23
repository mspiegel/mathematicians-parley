# Selection of the ten theorems

The ten theorems for the example corpus, chosen by the coverage rule in
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
list and in set.mm's main body, not a mathbox. Measured with
`parley/mmstats.py` on the same set.mm.

| # | theorem | feature stressed | set.mm | essential steps | deduction form | class vars | set-existence hyps | dv pairs | informal source |
|---|---|---|---|---|---|---|---|---|---|
| 11 | divisibility by 3 rule | congruence; a sum whose terms a function gives | 3dvds | 122 | no | F, N | none | 2 | ProofWiki; Hammack on congruence (verify) |
| 12 | binomial theorem | a finite sum split and reindexed; binomial coefficients | binom | 83 | no | A, B, N | none | 3 | ProofWiki; Hammack ch. 3 (verify) |
| 13 | sum of the reciprocals of the triangular numbers | an infinite series: a limit of partial sums, telescoping | trirecip | 42 | no | none | none | 0 | ProofWiki |
| 14 | Schröder–Bernstein | comparing sizes by injection; a set defined by recursion; a function defined piecewise | sbth | 29 | no | A, B | none | 0 | Hammack ch. 14 (verify); ProofWiki |
| 15 | Lagrange's theorem | an algebraic structure, which set.mm encodes through `Base`, `+g` and `SubGrp` | lagsubg | 27 | no | G, X, Y | none | 0 | ProofWiki |

Three of these were set aside when the ten were chosen: Schröder–Bernstein
because Cantor was shorter and carried the set-existence hypothesis, the
binomial theorem because the geometric series covered induction at a third
of the size, and the divisibility rule as heavy. Those were reasons to prefer
another theorem for the same feature. The question now is which features are
still untested, and a reindexed sum, a congruence and an injection-built
bijection are among them.

1. **Divisibility by 3.** The first congruence in the corpus: 10ᵏ leaves
   remainder 1 on division by 3, so a number and its digit sum leave the
   same remainder. set.mm states it for a digit function F : (0…N) → ℤ,
   and the readable statement is about the digits of a number, so the
   statement itself is the first thing to settle. Its 122 steps are what
   the up direction would hide; the readable proof is a few lines.
2. **Binomial theorem.** Induction again, but the step splits a sum,
   shifts its index and applies Pascal's rule, where the geometric series
   only adds a term at the end (`fsump1`).
3. **Triangular reciprocals.** No class variables and nothing to hide in
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
