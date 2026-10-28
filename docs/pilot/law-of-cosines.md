# Pilot: the law of cosines

Theorem 47 of `SELECTION.md`, set.mm's `lawcos`, Metamath 100 #94:

  in a triangle PQR, |RP|² = |PQ|² + |QR|² − 2·|PQ|·|QR|·cos∠PQR.

The library already held it as a record, `law-of-cosines`, from `lawcos`,
and Heron, the power of a point and thirteen exercises in `proofs/euclid/`
cite it. The pilot is the reader's proof, Euclid II.12 and II.13, which
cites neither: it cites Pythagoras as the corpus proves it (Theorem 22, by
similar triangles).

---

## Theorems pythagoras-at-foot, foot-on-ray, distance-from-foot, law-of-cosines

The proof is `proofs/wiedijk/law-of-cosines.proof`, four theorems. All
elaborate to `corpus/elaboration/proofs/wiedijk/law-of-cosines/`, assume
nothing, and verify.

Numbers: `pythagoras-at-foot` 9 steps, `foot-on-ray` 8,
`distance-from-foot` 44 (its five cases 9, 6, 7, 6 and 12),
`law-of-cosines` 7.

---

## Rendered view

**Theorem (the law of cosines).** If P, Q, R form a triangle, then
|RP|² = |PQ|² + |QR|² − 2·(|PQ|·|QR|·cos∠PQR).

*Proof.* Drop the perpendicular from P to line QR, with foot H. By
Pythagoras |PQ|² = |PH|² + |HQ|² and |PR|² = |PH|² + |HR|², which hold
when H is Q or R too, the leg being 0 (`pythagoras-at-foot`). From where H
lies, |HR|² = |HQ|² + |QR|² − 2·(|PQ|·|QR|·cos∠PQR)
(`distance-from-foot`). Then
|RP|² = |PH|² + |HR|² = |PQ|² − |HQ|² + |HR|², which is the claim. ∎

**Where H lies** (`distance-from-foot`). H is Q, between Q and R, R, beyond
R, or beyond Q.

- At Q the angle at Q is right, its cosine is 0, and |HR| is |QR|.
- On the ray from Q through R (`foot-on-ray`), the angle at Q is the angle
  PQH of a right triangle, so |QH| = |QP|·cos∠PQR, and |HR|² is
  (|QR| − |QH|)² expanded.
- Beyond Q, ∠PQH is the supplement of ∠PQR, so |QH| = −|QP|·cos∠PQR, and
  |HR| = |HQ| + |QR|.

---

## Database items

In `corpus/stdlib/geometry.records`:

- `perpendicular-foot`, a theorem: for a triangle PQR there is a point H on
  line QR, not P, with ∠PHQ = 90° if H is not Q and ∠PHR = 90° if H is not
  R. Proved on the page, Euclid I.12, in `corpus/stdlib/geometry.proof`.
- `on-line-cases`, mundane: a point of line QR is Q, between Q and R, R,
  beyond R or beyond Q (`gonline`).
- `cosine-right-triangle`, mundane: in a triangle right-angled at R,
  |QR| = |QP|·cos∠RQP, the cosine as adjacent over hypotenuse (`gcosrt`,
  from `glawcos`: the library may prove what the page may not cite).
- `between-ends-apart` (`gbetends`) and `right-angle-triangle` (`grttri`),
  mundane.

---

## What the pilot reveals

1. **Five cases where a textbook draws two.** II.12 and II.13 are the obtuse
   and acute figures; the foot at Q, at R, and beyond R are cases a figure
   does not separate. Three of them share `foot-on-ray`, and
   `pythagoras-at-foot` keeps the main theorem free of cases.

2. **One set in the kernel is two on the page.** set.mm's `CC` is ℂ and 𝔼²,
   and the build's reading back of "there is H ∈ 𝔼² with H is on line QR"
   took the domain's first reading, ℂ, under which "H is on line QR" says
   nothing. A binder's domain is now read every way it reads, and the first
   under which the claim reads back is taken.

3. **The cosine in a right triangle is mundane.** It carries the
   trigonometry of the proof, but to a school reader it is what cosine
   means.
