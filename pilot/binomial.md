# Pilot: the binomial theorem

Twelfth pilot, the second of the five chosen for what the first ten did not
exercise (`SELECTION.md`, "The next five"). Number 44 on Wiedijk's list,
`binom` in set.mm (83 essential steps). Its purpose is a sum re-indexed,
two sums added term by term, and binomial coefficients.

The theorem: for real x and y and n ∈ ℕ₀,
(x + y)^n = Σ(k = 0 to n) C(n, k)·x^(n − k)·y^k.

The informal source is ProofWiki's induction proof of the binomial theorem
for an integral index. Hammack's Book of Proof (third edition) states it as
Theorem 3.1 (§3.6), accepts it there without proof, and asks for the
induction as exercise 23 of chapter 10, pointing to Pascal's rule, its
Equation (3.3), which it gives for 1 ≤ k ≤ n.

---

## Decisions

- **C(n, k)** is the notation. The `C` is a literal of the pattern, as the
  `S` of `S(n)` is.
- **The factorial formula** is the definition, `def:stdlib/counting/binomial-coefficient`,
  with set.mm's `bcval2` as its target. The proof never unfolds it: it rests
  on Pascal's rule and on the values at the edges, which are set.mm theorems
  proved from the definition.
- **Induction on n**, as Hammack's exercise asks.
- **x and y are real**, where set.mm's `binom` takes complex numbers. The
  corpus's `algebra` works over ℝ, and every pilot before this one is real.

---

## Theorems binomial-step and binomial

The skeleton is `proof/binomial.proof`. `binomial-step` is the induction
step's algebra: the sum for m, times x + y, is the sum for m + 1.
`binomial` is the induction, whose base case is the one-term sum at 0 and
whose step cites `binomial-step` after (x + y)^(m + 1) = (x + y)^m·(x + y)
and the induction hypothesis.

The step does not follow ProofWiki's. ProofWiki peels the first and last
terms off each sum, uses C(n, 0) = C(n, n) = 1, and puts them back. Here
each of x·Σ and y·Σ is extended to the range 0 to m + 1 by a term that is
zero — C(m, m + 1) in the first, C(m, −1) in the second — so the two sums
run over the same range and add term by term, and Pascal's rule, which
holds at every integer k, joins each pair of coefficients. Every exponent
that appears, (m + 1) − k and k for k from 0 to m + 1, is a whole number.

---

## Database items

This pilot introduced, in the database, `def:stdlib/counting/binomial-coefficient`,
`thm:stdlib/counting/pascal`, `thm:stdlib/counting/binomial-zero-index`, `thm:stdlib/counting/binomial-above`,
`thm:stdlib/counting/binomial-below`, `thm:stdlib/counting/binomial-nat0`, the sum items `thm:stdlib/sums/sum-single`,
`thm:stdlib/sums/sum-last`, `thm:stdlib/sums/sum-first`, `thm:stdlib/sums/sum-shift`, `thm:stdlib/sums/sum-scaled`,
`thm:stdlib/sums/sum-add`, `thm:stdlib/sums/sum-termwise` and `thm:stdlib/sums/sum-real`, the range items
`thm:stdlib/sums/range-difference`, `thm:stdlib/sums/range-integer` and `thm:stdlib/sums/range-nat0`, and
`thm:stdlib/numbers/exponent-zero`, `thm:stdlib/numbers/nat0-int` and `thm:stdlib/numbers/below-successor`, with
`thm:proof/binomial/binomial-step` and `thm:proof/binomial/binomial` proved here. In `db/notation.records`
it added `binomial`, C(n, k), and `integer-range`, {a, …, b}.

---

## What the pilot reveals

1. **A sum's range is a set a line can speak of.** Rewriting a sum a term
   at a time needs a line saying something of every index it takes, and
   x^(m − k) is a power with a whole exponent only when k ≤ m. So the range
   is a notation, `{0, …, m}`, and "for every k ∈ {0, …, m}, …" is the line
   `sum-termwise` reads at each index. A `let k ∈ {a, …, b}` gives k the
   sort of what the range holds, which the kinds now settle for an item's
   own lines as they did for a proof's.
2. **A summand's function hypothesis asks for its numbers.** A sum item
   says `let t : {a, …, b} → ℝ`, and where t stands for the step's summand
   that is a claim about every term. The page does not write it; it writes
   the memberships of the names the summand is built from that the sum does
   not bind — x ∈ ℝ, y ∈ ℝ, m ∈ ℕ₀ — as `requires` lines, and the checker
   takes those as what the hypothesis asks. What involves k comes from k
   being in the range. It is the rule `algebra` already follows for its
   atoms, and the alternative, a line saying each summand is real in a
   block of its own, would have added some forty lines of closure.
3. **An item reads its summand anywhere, not only at the index.**
   `sum-last` says the sum to n + 1 is the sum to n plus t(n + 1), and
   `sum-shift` rewrites t(k) as t(k − c). The checker filled t's argument
   only where it was a bare name; it now fills every name the match has
   bound.
4. **A compound's membership is read off its operation.** The summand
   C(m, k)·x^(m − k)·y^k is two products, a power and a coefficient complex
   through ℕ₀. Searched for, each product spent a lemma of the depth before
   the atoms were reached. The side-condition search now walks a sum,
   difference, product, power or negation by the closure table, spending
   no depth, as it already did for sethood and for numerals. Eight other
   theorems' kernel proofs changed with this pilot's elaborator changes,
   to shorter ones in seven, their statements the same and each still
   assuming nothing.
5. **A closed number is placed by its value.** The base case's term has
   x^(0 − 0), and nothing builds 0 − 0 ∈ ℕ₀ from its parts. It is 0, and
   the membership is the digit's, carried across the equation `arithmetic`
   proves.
6. **Two letters a lemma keeps apart may be one on the page.** `fsumshft`
   binds j on one side and k on the other and forbids them equal; the page
   writes k on both. The elaborator renames the right-hand sum to a letter
   nothing holds and says the two are one with `cbvsumv`. An induction over
   a claim holding a sum now rewrites the summand as well as the limit
   (`sumeq2sdv`), and `calculation` finds a chain's relation outside the
   brackets a sum's `=` sits in.
7. **The induction step's algebra is its own theorem, and why.** Stated
   inside the step, the hypothesis is in scope and names the sum's index,
   and `sumeq2dv`, which rewrites a sum term by term, forbids that. The
   elaborator moved the lemma one frame out, as it does for `fsump1`, and
   handed it a line proved in the inner frame: a proof of another
   statement. `mmverify` refused it; the elaborator had reported nothing
   assumed. It now offers an outer frame only the lines that frame holds,
   so the case is reported at the step, and the proof puts the algebra in
   `binomial-step`, where nothing in scope names k.
8. **A fact that cites nothing.** m < m + 1 is `inequalities` with no
   cited fact: what the combination leaves over is 1 > 0, a closed numeral
   fact the method may use unwritten. The method's proofs once combined only
   cited facts, and the step cited `thm:stdlib/numbers/below-successor`
   (`ltp1`) so that nothing was stated; the triangular reciprocals pilot is
   where the method learned to write the number left over.

9. **A label means its own block's line.** The four `fix` blocks of
   `binomial-step` each fix k as `(J)`, which the grammar allows, since a
   label is in scope only inside its block. The checker kept what each
   label says theorem-wide, so the last block's J, k from 0 to m + 1, stood
   for all four: the first two were reported for defects they did not have,
   and an edit to the third that read its k from 0 rather than 1 passed.
   It now reads a label as the block around the citing step writes it.

Numbers, for the record: 98 numbered steps, 84 in `binomial-step` and 14
in `binomial`, and 99 requires lines, 91 of them in `binomial-step`, most
of them the memberships of x, y and m that the sum items ask and the
integer memberships of the ranges' ends. Each theorem elaborates in under
four seconds and 0.6 GB. set.mm's `binom` has 83 essential steps.
