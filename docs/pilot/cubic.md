# Pilot: the solution of the cubic

Wiedijk #37, set.mm's `cubic` (with `cubic2`, `mcubic`, `dcubic`, `1cubr`):

  for a ≠ 0, a·x³ + b·x² + c·x + d = 0 just when
  x = −(b + r·T + M/(r·T))/(3·a) for a cube root r of 1, where
  M = b² − 3ac, N = 2b³ − 9abc + 27a²d, G² = N² − 4M³ and
  T³ = (N + G)/2, T ≠ 0.

The square root G and the cube root T are given as letters with the
equation each satisfies, as `cubic2` gives them. A cube root cannot be
written yet: `^` with an exponent that is not a whole number does not mean a
complex power on the page.

---

## Theorem cubic

The proof is `proofs/wiedijk/cubic.proof`. It elaborates to
`corpus/elaboration/proofs/wiedijk/cubic/cubic.mm`, which assumes nothing
and verifies. It cites none of set.mm's cubic theorems.

---

## Rendered view

Let a, b, c, d, x ∈ ℂ with a ≠ 0. Let M = b² − 3ac and
N = 2b³ − 9abc + 27a²d. Let G² = N² − 4M³, and let T³ = (N + G)/2 with
T ≠ 0.

**Theorem.** ax³ + bx² + cx + d = 0 ↔ there is
r ∈ {1, (−1 + i√3)/2, (−1 − i√3)/2} with x = −(b + rT + M/(rT))/(3a).

*Proof.*

1. (i√3)² = −3, from i·i = −1 and (√3)² = 3.
2. Let ω₁ = (−1 + i√3)/2 and ω₂ = (−1 − i√3)/2. Then ω₁ω₂ = 1, so neither
   is 0.
3. T³ + M³/T³ = N, by algebra from the equations of T and G.
4. Let y = 3ax + b. Then ax³ + bx² + cx + d = (y³ − 3My + N)/(27a²).
5. (y + ω₁T + M/(ω₁T))(y + ω₂T + M/(ω₂T)) =
   y² − (T + M/T)y + T² − M + M²/T², multiplying out with (i√3)² = −3.
6. Times y + T + M/T that is y³ − 3My + N, by line 3. So y³ − 3My + N is
   the product of y + rT + M/(rT) over the three values of r.
7. If the cubic is 0, so is y³ − 3My + N, and by the zero product one
   factor is 0. That factor's r gives x = −(b + rT + M/(rT))/(3a), and r is
   in the set.
8. If such an r is given, it is one of the three. Its factor is 0, so the
   product is 0, so the cubic is 0.

∎

---

## Database items

In `corpus/stdlib/sets.records`:
- `triple`: what is in a set of three listed things.
- `triple-members`: each thing a set lists is in it.

In `corpus/proved/sets.proved`: `geltpg`. It is `eltpg` with its three-way
"or" read as two, since the page's "or" pairs from the left.

---

## What the pilot reveals

1. **The roots factor the cubic, so both directions are one identity.**
   Cardano's argument, run backwards, needs a complex square root to split
   a root y into u + M/u, and a separate case where M = 0. Writing the
   depressed cubic as the product of its three factors needs neither. The
   zero product gives one direction, and a zero factor gives the other.

2. **i·√3 is one atom's square.** Multiplying out the factors with
   (−1 ± i√3)/2 in them needs only (i·√3)² = −3. That is one cited
   equation, multiplied by a polynomial, which is what `algebra` allows.

3. **A divisor can be a product with a quotient inside it.** M/(ω₁·T), with
   ω₁ written out, divides by ((−1 + i·√3)/2)·T. The checker decided the
   step, but the build read only a plain divisor, c/e or −(c/e). It now
   reads a product part by part, and the sides are multiplied by
   (−1 + i·√3)·T, which is not 0 because each part is not. Test:
   `tests/elaborator/a-divisor-multiplying-a-quotient.proof`.

4. **An exhibit at 1 leaves the 1 unwritten.** "x = −(b + T + M/T)/(3a)"
   shows r := 1 for "x = −(b + r·T + M/(r·T))/(3a)", since 1·T is T. The
   checker read it so, but recorded no value for the build. The build now
   exhibits the value the checker accepted. Test:
   `tests/elaborator/an-exhibit-at-an-identity-element.proof`.

5. **Multiplying out is two steps.** The two complex factors first, which
   leaves the quadratic y² − (T + M/T)y + T² − M + M²/T², then the third.
   One step would build as well, but the quadratic, where the ω terms
   cancel, is what a reader checks by hand.

Numbers, for the record: 48 numbered steps and 4 requires lines. The
elaborated proof is 1.9 MB.
