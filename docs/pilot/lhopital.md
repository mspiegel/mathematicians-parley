# Pilot: L'Hôpital's rule

Theorem 48 of `SELECTION.md`, set.mm's `lhop`, Metamath 100 #64:

  if f and g are differentiable on (a, b) ∖ {c}, both tend to 0 at c, g′ is
  nonzero there, and f′/g′ tends to L at c, then f/g tends to L at c.

set.mm's `lhop` also asks that g be nonzero off c, and says the limit on any
open set holding c. The page proves g nonzero, and says it on (a, b) ∖ {c}.

---

## Theorems cauchy-quotient, quotient-two-points, quotient-between and lhopital

The proof is `proofs/wiedijk/lhopital.proof`, four theorems. All elaborate
to `corpus/elaboration/proofs/wiedijk/lhopital/`, assume nothing, and verify.

Numbers: `cauchy-quotient` is 16 steps, `quotient-two-points` 42,
`quotient-between` 62, `lhopital` 23.

---

## Rendered view

**Theorem (Cauchy's quotient).** Let F and G be continuous on [p, q] and
differentiable inside, with G′ never 0. Then G(p) ≠ G(q), and for some
ξ ∈ (p, q), (F(q) − F(p))/(G(q) − G(p)) = F′(ξ)/G′(ξ).

*Proof.* Cauchy's mean value theorem gives
(F(q) − F(p))·G′(ξ) = (G(q) − G(p))·F′(ξ). By Rolle's theorem G(p) = G(q)
would make G′ zero somewhere, so G(p) ≠ G(q), and dividing gives the
quotient. ∎

**Theorem (between two points).** For u and v in (a, b) ∖ {c}, on either
side of each other, the same holds with ξ nearer u than v is.

**Theorem (the quotient near c).** For x in (a, b) ∖ {c}, g(x) ≠ 0 and
f(x)/g(x) = f′(ξ)/g′(ξ) for some ξ with |ξ − c| < |x − c|.

*Proof.* Extended by 0 at c, f and g are continuous there, since they tend
to 0. The quotient between the two points c and x gives ξ between them. ∎

**Theorem (L'Hôpital).** f/g tends to L at c.

*Proof.* Given ε > 0, a δ keeps f′/g′ within ε of L near c. For x within δ
of c, ξ is nearer c than x is, so f(x)/g(x) = f′(ξ)/g′(ξ) is within ε of
L. ∎

---

## Database items

In `corpus/stdlib/calculus.records`, each with its lemma in `proved.mm`:
`rolle-on-part`, `cauchy-mean-value` and `continuous-extension`, which a
proof names; and `open-interval`, `open-interval-real`,
`closed-within-open`, `open-without-point`, `derivative-real-on`,
`differentiable-on-part` and `derivative-local`, which are mundane.

---

## What the pilot reveals

1. **A letter introduced in an interval is a real number said once.** A
   letter introduced in (a, b), in [a, b] whose ends are numbers said once,
   or in either with points taken out, is in ℝ with no line saying so, in
   the checker and the build alike. `mean-value` and `image-of-parabola`
   dropped the lines that wrote it.

2. **Tool faults met on the way.** A define's domain is read where a set
   is wanted; the parts of a cited line that says several things are
   supplied to an unfolding; an `instantiate` step's condition is settled
   from the lines it cites; and a define's name is kept as a name in
   matching.
