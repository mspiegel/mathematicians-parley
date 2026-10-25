# Pilot: the intersecting chords theorem

Theorem 45 of `SELECTION.md`, set.mm's `chordthm`, Metamath 100 #55:

  if chords AB and CD of a circle meet at P, then |PA|·|PB| = |PC|·|PD|.

The library already held it as a record, `intersecting-chords`, cited by
`proofs/euclid/chords-through-circle.proof`. The pilot is the reader's
proof, which cites neither that record nor set.mm's `chordthm`.

---

## Theorems power-of-a-point and intersecting-chords

The proof is `proofs/wiedijk/chords.proof`, two theorems. Both elaborate to
`corpus/elaboration/proofs/wiedijk/chords/`, assume nothing, and verify.

Numbers: `power-of-a-point` is 26 steps, 20 of them in the case where P is
not the centre; `intersecting-chords` is 5.

---

## Rendered view

**Theorem (power of a point).** Let P lie between A and B, with
|AO| = |BO|. Then |PA|·|PB| = |AO|² − |PO|².

*Proof.* If P is O, both parts are radii. Otherwise the law of cosines at P
in the triangles APO and OPB gives |AO|² and |BO|². The angles APO and OPB
are supplementary, so their cosines are opposite, and eliminating the
cosine between the two equations leaves
|PA|·|PB|·(|PA| + |PB|) = (|AO|² − |PO|²)·(|PA| + |PB|). The factor
|PA| + |PB| is positive and cancels. ∎

**Theorem (intersecting chords).** If P lies between A and B and between C
and D, and A, B, C, D are all at distance |AO| from O, then
|PA|·|PB| = |PC|·|PD|.

*Proof.* Each product is |AO|² − |PO|² by the power of a point, which does
not depend on the chord. ∎

---

## Database items

None. The proof cites `law-of-cosines`, `supplementary-angles` and
`cos-supplement`, which the library held.

---

## What the pilot reveals

1. **The route is the power of a point.** Euclid III.35 as it is commonly
   taught goes by similar triangles, which needs equal angles in one
   segment of the circle, and the library holds no such theorem. The
   power of a point needs only the law of cosines, and states the fact the
   theorem rests on: the product does not depend on the chord.

2. **A distance's two points stand in no order.** The law of cosines gave
   |AP| where the claim wrote |PA|, and each turn was a step citing
   `distance-symmetric`, which no textbook writes. The distance notation now
   `commutes any order` (`GEOMETRY.md`, "A distance is its two points, in no
   order"): the checker reads |AB| and |BA| as one term, and every route of
   the build takes a distance either way round, a substitution carrying an
   untouched distance written the other way among them. About 75 steps
   across 20 geometry proofs that only turned a distance were removed, and
   no proof cites `distance-symmetric` now. An angle keeps its order:
   ∠PQR = ∠RQP is still a cited step.
