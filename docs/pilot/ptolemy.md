# Pilot: Ptolemy's theorem

Theorem 33 of `SELECTION.md`, set.mm's `ptolemy`, Metamath 100 #95:

  if a + b + c + d = π then sin a·sin b + sin c·sin d = sin(b + c)·sin(a + c).

set.mm states Ptolemy's theorem through the angles the sides of a cyclic
quadrilateral subtend, which makes it a sine identity, and the pilot proves
that statement. The statement about the sides and diagonals needs inscribed
angles, which set.mm does not have, and is left for later.

---

## Theorem ptolemy

The proof is `proofs/wiedijk/ptolemy.proof`. It elaborates to
`corpus/elaboration/proofs/wiedijk/ptolemy/ptolemy.mm`, which assumes nothing
and verifies.

---

## Rendered view

Let a, b, c, d be real numbers with a + b + c + d = π.

**Theorem.** sin a·sin b + sin c·sin d = sin(b + c)·sin(a + c).

*Proof.*

1. d = π − (a + b + c), so sin d = sin(a + b + c), with sin π = 0 and
   cos π = −1.
2. The addition formulas write sin(a + b + c), sin(b + c) and sin(a + c) in
   sines and cosines of a, b and c.
3. The two sides then differ by sin a·sin b·(1 − sin²c − cos²c), which is 0.

∎

---

## Database items

None new.

---

## What the pilot reveals

Nothing new of the tools. Every substitution is its own step, since a chain
cites one line per link, which comes to 23 steps.
