# Pilot: Ptolemy's theorem

Theorem 33 of `SELECTION.md`, set.mm's `ptolemy`, Metamath 100 #95:

  if a + b + c + d = π then sin a·sin b + sin c·sin d = sin(b + c)·sin(a + c).

set.mm states Ptolemy's theorem through the angles the sides of a cyclic
quadrilateral subtend, which makes it a sine identity, and the pilot proves
that statement. The statement about the sides and diagonals is the second
theorem, `cyclic-ptolemy`.

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

---

## Theorem cyclic-ptolemy

The second theorem of `proofs/wiedijk/ptolemy.proof`, 66 steps. It
elaborates to `corpus/elaboration/proofs/wiedijk/ptolemy/cyclic-ptolemy.mm`,
which assumes nothing and verifies.

---

## Rendered view

Let A, B, C, D lie on a circle with centre O, in that order, so that the
diagonals AC and BD cross at a point P.

**Theorem.** |AC|·|BD| = |AB|·|CD| + |AD|·|BC|.

*Proof.* Write p, q, r, s for |PA|, |PB|, |PC|, |PD|.

1. The chords cross at P, so p·r = q·s.
2. P is between A and C and between B and D, so the angles at P are θ,
   180° − θ, θ and 180° − θ, with cosines c, −c, c and −c.
3. The law of cosines in the four triangles at P gives
   |AB|² = p² + q² − 2pqc, |BC|² = q² + r² + 2qrc,
   |CD|² = r² + s² − 2rsc and |DA|² = s² + p² + 2spc.
4. With p·r = q·s, |CD|²·p² = s²·|AB|² and |BC|²·p² = q²·|AD|², and
   lengths are not negative, so |CD|·p = s·|AB| and |BC|·p = q·|AD|.
5. Then (|AB|·|CD| + |AD|·|BC|)·p = s·|AB|² + q·|AD|², in which the cosine
   terms cancel, leaving (q + s)·(p² + q·s) = (q + s)·(p + r)·p.
6. |AC| = p + r and |BD| = q + s, and p ≠ 0.

∎

---

## Database items

None new: the intersecting chords, supplementary angles, the law of
cosines, segment addition, `square-equal` and `multiply-cancel`.

---

## What the pilot reveals

1. **A proof from the library alone.** It needs neither the inscribed angle
   theorem nor the sine form: the intersecting chords and the law of
   cosines carry it.

2. **One equation to an algebra step.** Each algebra step multiplies one
   cited equation by one factor, so the squares in step 4 are compared
   through calculations whose links are steps of their own.
