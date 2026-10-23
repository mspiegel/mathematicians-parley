# Pilot: the solution of the quartic

Wiedijk #46, set.mm's `quart` (with `quart1`, `dquart`, `quartlem1`–`4`):

  x⁴ + ax³ + bx² + cx + d = 0 just when x is −a/4 − S ± I or
  −a/4 + S ± J, with P, Q, R, U, V, W, T, M, S, I and J as in `quart`.

As in the cubic, every root the formula takes is a letter with the equation
it satisfies: W² = V² − 4U³, T³ = (V + W)/2, 4·S² = M, and I² and J² as
`quart` defines them. M ≠ 0 and T ≠ 0 are hypotheses, as in set.mm.

---

## Theorem quartic

The proof is `proofs/wiedijk/quartic.proof`. It elaborates to
`corpus/elaboration/proofs/wiedijk/quartic/quartic.mm`, which assumes
nothing and verifies.

---

## Rendered view

Let a, b, c, d, x ∈ ℂ, and:
- P = b − (3/8)a², Q = c − ab/2 + a³/8,
  R = d − ca/4 + a²b/16 − (3/256)a⁴;
- U = P² + 12R, V = −2P³ − 27Q² + 72PR, W² = V² − 4U³;
- T³ = (V + W)/2 with T ≠ 0, and M = −(2P + T + U/T)/3 with M ≠ 0;
- 4S² = M, I² = −S² − P/2 + (Q/4)/S, and J² = −S² − P/2 − (Q/4)/S.

**Theorem.** x⁴ + ax³ + bx² + cx + d = 0 ↔
(x = −a/4 − S + I or x = −a/4 − S − I) or
(x = −a/4 + S + J or x = −a/4 + S − J).

*Proof.*

1. S ≠ 0, since S = 0 would make M = 4S² = 0.
2. T³ + U³/T³ = V, as in the cubic, so z = T + U/T has z³ − 3Uz − V = 0.
3. At z = −3M − 2P, 27(M(P + M)² − Q² − 4RM) = −z³ + 3Uz + V, by the
   equations of U and V. And −3M − 2P = T + U/T. So
   M(P + M)² − Q² − 4RM = 0: M solves Ferrari's resolvent.
4. Let y = x + a/4. By the equations of I and J:
   - (y + S − I)(y + S + I) = y² + 2Sy + 2S² + P/2 − (Q/4)/S;
   - (y − S − J)(y − S + J) = y² − 2Sy + 2S² + P/2 + (Q/4)/S.
5. Their product is y⁴ + Py² + Qy + R, by 4S² = M and the resolvent.
6. The quartic is y⁴ + Py² + Qy + R: algebra in y, then P, Q and R put in.
   So it is the product of the four factors.
7. If the quartic is 0, the zero product, three times, makes one factor 0,
   and each factor gives one of the four values of x. If x is one of them,
   its factor is 0, and so is the product.

∎

---

## Database items

None new. It cites `zero-product`, `or-left` and `or-right`.

---

## What the pilot reveals

1. **The resolvent is the cubic again.** T + U/T solves z³ − 3Uz − V for
   the same reason the cubic's T + M/T solves its depressed cubic. The two
   lines that say so are written here rather than imported from the cubic:
   the cubic's theorem speaks of a·x³ + … and its roots, not of T + U/T.

2. **Ferrari's factorization is one algebra step.** The product of the two
   quadratics is y⁴ + Py² + Qy + R once its constant term is checked. That
   combines the resolvent with 4S² = M, which is one equation multiplied by
   a polynomial.

3. **Depressing the quartic is one identity and three substitutions.** With
   P, Q and R as letters, the identity needs P times y² and Q times y: two
   equations multiplied by terms, which `algebra` refuses in one step. So it
   is proved with P, Q and R written out, and each is then put in by a
   substitution.

Numbers, for the record: 50 numbered steps, no requires lines. The
elaborated proof is 0.95 MB.
