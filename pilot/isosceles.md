# Pilot: the isosceles triangle theorem

Ninth pilot, first draft. Its purpose is one geometry theorem, chosen
because set.mm's plane is the complex numbers and its angles are a
function through the complex logarithm, both far from how a school reader
thinks. Number 65 on Wiedijk's list, `isosctr` in set.mm.

The readable proof is the one attributed to Pappus: the triangle is
congruent to itself read backwards, by side-angle-side, so its base
angles are equal. It is four steps. Everything of interest is in the
database items: points, distance, angle, triangle, congruence and the
side-angle-side theorem, none of which the earlier pilots had.

Provisional forms, listed in the batch report: `let A be a point`;
|AB| for distance; ∠ABC for the angle at B; "A, B, C form a triangle";
"triangle ABC ≅ triangle A′B′C′".

---

## Theorem isosceles

The skeleton is `proof/isosceles.proof`. The items it cites are in `db/`.

The draft's chain cited a theorem on its last line instead of a step, which
the calculation rule forbids. A three-line chain with one cited theorem is
tempting to write and reads perfectly well, which is why the rule has to be
mechanical rather than a matter of taste. The conforming form is a step
"|CB| = |BC|" before the chain, which the proof now has as step 2.

---

## Database items

This pilot introduced `def:point`, `def:triangle`, `def:congruent`,
`thm:distance-symmetric`, `thm:angle-symmetric`, `thm:triangle-permute`,
`thm:side-angle-side` and `thm:isosceles` in `db/items.db`, and the point,
distance, angle and congruence rows in `db/notation.db`. The table that used
to stand here was merged into those files.

Seven of the eight are open items, which is what finding 1 below says. Three
further things the merge found. `def:angle` is needed by the ∠ notation and
appeared only in the findings, so it was added as an open item.
`thm:triangle-permute`'s conclusion is not a formula and has to be restated.
And `thm:side-angle-side` names its variables P, Q, R while step 7 of the
proof instantiates A, B, C; one of the two must change, and the merge changed
neither.

---

## What the pilot reveals

1. **The proof is trivial and the database is not.** Eleven steps, six
   of them symmetries and permutations, and one citation of
   side-angle-side that does all the work. Every item in the database
   table is new, and the last three have no set.mm counterpart. This is
   the theorem where the up direction has the most to hide and the down
   direction has the most to build.
2. **Angles need an orientation convention.** set.mm's angle function
   gives a signed angle, and ∠PQR = −∠RQP up to a multiple of 2π. The
   school reader's angle is unsigned. def:angle must take the absolute
   value or the pilot's thm:angle-symmetric is false in set.mm's terms.
3. **Side-angle-side is an axiom or a theorem depending on the
   foundation.** Euclid and Hilbert take it as an axiom; over ℂ it is a
   theorem about distances and arguments. The pointer does not care which,
   and that is the point of pointers. But it means the corpus's geometry
   rests on a proof of SAS from complex arithmetic that no school reader
   would recognise as geometry.
4. **Symmetry facts dominate.** |AC| = |CA| and ∠CAB = ∠BAC are dull by
   any standard, but they are not dull facts in the role sense, since
   they feed calculations rather than discharge hypotheses. They are
   steps. A viewer rule for collapsing "steps by symmetry theorems" would
   be another mechanical criterion.
5. **Euclid's own proof is not available.** Elements I.5 extends the
   sides and uses two congruences. It needs "extend a segment", a
   construction the database would have to define. Pappus's proof was
   chosen because it needs nothing but the triangle itself.

Numbers, for the record: 11 numbered steps, 0 requires lines. set.mm's
isosctr has 40 essential steps.
