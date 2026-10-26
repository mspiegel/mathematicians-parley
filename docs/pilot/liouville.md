# Pilot: Liouville's approximation theorem

Theorem 50 of `SELECTION.md`, set.mm's `aaliou`, the first half of
Metamath 100 #18 (the second half is theorem 51, `liouville-number`):

  if α is a real root of a polynomial F with integer coefficients and
  degree N, there is c > 0 such that for all p ∈ ℤ and q ∈ ℕ,
  α = p/q or c/q^N < |α − p/q|.

---

## Theorems mean-value-bound, value-at-a-fraction, near-a-root and liouville

The proof is `proofs/wiedijk/liouville.proof`, four theorems. All elaborate
to `corpus/elaboration/proofs/wiedijk/liouville/`, assume nothing, and
verify.

Numbers: `mean-value-bound` is 35 steps, `value-at-a-fraction` 14,
`near-a-root` 42, `liouville` 61.

---

## Rendered view

**Theorem (a bound from the mean value theorem).** If |f′| ≤ M on [a, b],
then |f(b) − f(a)| ≤ M·(b − a).

**Theorem (the value at a fraction).** If F(p/q) ≠ 0 then
|F(p/q)| ≥ 1/q^N, since q^N·F(p/q) is a nonzero integer.

**Theorem (near a root).** If F(α) = 0 and |F′| ≤ K within 1 of α, then
|F(x)| ≤ K·|α − x| for x within 1 of α.

**Theorem (Liouville).** Let δ keep the other roots of F away from α, K ≥ 1
bound |F′| near α, and c = min(1, δ, 1/(2K)). A fraction p/q further than c
from α is further than c/q^N. One nearer is α itself, or F(p/q) ≠ 0, and
then 1/q^N ≤ |F(p/q)| ≤ K·|α − p/q|, so |α − p/q| ≥ 1/(K·q^N) > c/q^N. ∎

---

## Database items

In `corpus/stdlib/polynomials.records`: `integer-polynomial-at-a-fraction`,
`roots-isolated` and `polynomial-on-the-reals`, which a proof names, and the
mundane `integer-polynomial-real`. In `corpus/stdlib/calculus.records`:
`continuous-bounded`, which a proof names, and the mundane
`map-continuous-on-part`. In `corpus/stdlib/numbers.records`, mundane:
`abs-difference-le`, `power-at-least-one` and `nonzero-integer-abs`. Each
has its lemma in `proved.mm`.

The notations "F is a polynomial with integer coefficients", deg(F), and
"α is algebraic" with its negation "α is transcendental" are new for this
theorem (`GRAMMAR.md`).

---

## What the pilot reveals

1. **A map for a function letter.** The mean value theorem is applied to F
   cut down to an interval, written as the map t ∈ [a, b] ↦ f(t): the first
   proof to give a map where a theorem has a function letter.

2. **A derivative's type.** f′ : ℝ → ℝ is read as a claim about the
   derivative of f, not a new name, and f′ has f's sort, so |f′(t)| reads as
   an absolute value. A derivative given for a function letter has its type
   asked, as a map's is.

3. **A map's letter kept apart.** A map given for a lemma's function may
   bind the letter the lemma keeps apart from it, as `ffnfv` keeps x apart
   from F; the build gives the lemma's letter a spare one, so the map is
   spelt with x as the page writes it.
