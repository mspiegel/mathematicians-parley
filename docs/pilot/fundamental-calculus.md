# Pilot: the fundamental theorem of calculus

Theorem 30 of `SELECTION.md`, set.mm's `ftc2`, Wiedijk #15:

  if f is continuous on [a, b] and F is an antiderivative of f, then
  ∫(a to b) f(t) dt = F(b) − F(a).

The argument is ProofWiki's first proof, and set.mm's: the area function
G(x) = ∫(a to x) f(t) dt has derivative f by part one of the theorem, so
G − F has derivative 0 and takes one value at a and at b, by the mean value
theorem; and G(a) = 0.

---

## Theorems

The proof is `proofs/fundamental-calculus.proof`, two theorems of 34
numbered steps, 42 with those inside blocks. Both elaborate to
`corpus/elaboration/proofs/fundamental-calculus/`, assume nothing, and
verify.

- `zero-derivative-ends`: a function continuous on [a, b] whose derivative
  is 0 on (a, b) takes the same value at a and b. From `mean-value`,
  theorem 19.
- `fundamental-calculus`: the theorem. G and H = G − F are defines.

Part one, that G is continuous on [a, b] and has derivative f on (a, b), is
the library item `area-function`; the integral being a real number is
`integral-real`, and the integral from a point to itself being 0 is
`integral-point`.

---

## Rendered view

**Lemma (zero-derivative-ends).** Let a < b, and H : [a, b] → ℝ be
continuous on [a, b] and differentiable on (a, b), with H′(x) = 0 for all
x ∈ (a, b). Then H(b) = H(a).

*Proof.* By the mean value theorem there is c ∈ (a, b) with
H′(c) = (H(b) − H(a))/(b − a). H′(c) = 0, so H(b) − H(a) = 0. ∎

**Theorem (fundamental-calculus).** Let a < b, f : [a, b] → ℝ be continuous
on [a, b], and F : [a, b] → ℝ be continuous on [a, b] and differentiable on
(a, b), with F′(x) = f(x) for all x ∈ (a, b). Then
∫(a to b) f(t) dt = F(b) − F(a).

*Proof.* Let G(x) = ∫(a to x) f(t) dt and H(x) = G(x) − F(x) on [a, b]. G
is real-valued, continuous on [a, b], and G′ = f on (a, b), by part one; so
H is continuous on [a, b] and H′ = f − f = 0 on (a, b). By
zero-derivative-ends, H(b) = H(a), so G(b) − F(b) = G(a) − F(a). G(a) is
the integral from a to a, which is 0, so
∫(a to b) f(t) dt = G(b) = F(b) − F(a). ∎

---

## Decisions made with the reader

1. **The textbook statement:** f continuous on [a, b] and F an
   antiderivative of f, rather than set.mm's integrable derivative.
   "Integrable" stays off the page; a continuous function on [a, b] being
   integrable is inside the library items.
2. **F is continuous on [a, b] and differentiable on (a, b),** with
   F′ = f on (a, b): set.mm takes derivatives only inside an interval, and
   the mean value theorem's statement already says it this way.
3. **The notation ∫(a to b) f(t) dt** for set.mm's directed integral
   (`cdit`). The letter of integration is any letter; `dt` is read as the
   letters d and t, and nothing names t.
4. **"Zero derivative means constant" is proved on the page,** from the mean
   value theorem, in the endpoint form the main proof uses.
5. **Part one is a library item,** `area-function`, as completeness was:
   set.mm's integral is Lebesgue's, and its proof is not the reader's.

---

## What the pilot reveals

1. **The integral in the library:** the notation record, its rule-table
   entries (bound letter, sethood, congruence in both ends), and the items
   `area-function`, `integral-real`, `integral-point`,
   `derivative-difference` and `continuous-difference`, with their bridges
   in `calculus.proved`.
2. **Testing first worked.** The test proofs of `tests/stdlib/calculus.proof`
   and `tests/elaborator/integral.proof`, written before the theorem, met
   four faults in a few lines each: congruence applied by position rather
   than by fit, a universal instance required to match letter for letter,
   no congruence entry for the integral's ends, and the invariance rewriter
   renaming the d of dt. Each was fixed in the tool.
3. **The theorem's own proof met one fault:** `algebra` clearing a division
   required each side of the claim to match a side of the crossed equation,
   so (H(b) − H(a))/(b − a) = 0 could not give H(b) = H(a). It now compares
   the differences, which the polynomial guard had already found equal.
