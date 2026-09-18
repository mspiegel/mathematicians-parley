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

```
theorem isosceles
  let A be a point                                                    (H1)
  let B be a point                                                    (H2)
  let C be a point                                                    (H3)
  assume A, B, C form a triangle                                      (H4)
  assume |CA| = |CB|                                                  (H5)
  then ∠CAB = ∠CBA

1.  |AC| = |CA|
    thm:distance-symmetric P := A, Q := C, from H1, H3

2.  |AC| = |BC|
    calculation
      |AC| = |CA|       1
           = |CB|       H5
           = |BC|       thm:distance-symmetric P := C, Q := B, from H3, H2

3.  ∠ACB = ∠BCA
    thm:angle-symmetric P := A, Q := C, R := B, from H1, H3, H2

4.  |CB| = |CA|
    calculation
      |CB| = |CA|       H5, right to left

5.  A, C, B form a triangle
    thm:triangle-permute, from H4

6.  B, C, A form a triangle
    thm:triangle-permute, from H4

7.  triangle ACB ≅ triangle BCA
    thm:side-angle-side A := A, B := C, C := B, A′ := B, B′ := C, C′ := A,
      from 5, 6, 2, 3, 4

8.  ∠BAC = ∠ABC
    def:congruent, from 7

9.  ∠CAB = ∠BAC
    thm:angle-symmetric P := C, Q := A, R := B, from H3, H1, H2

10. ∠ABC = ∠CBA
    thm:angle-symmetric P := A, Q := B, R := C, from H1, H2, H3

11. ∠CAB = ∠CBA
    calculation
      ∠CAB = ∠BAC       9
           = ∠ABC       8
           = ∠CBA       10
```

Step 2's chain cites a theorem on its last line instead of a step, which
the calculation rule forbids; it is left so in the draft as a reminder
that a two-line chain with a cited theorem is tempting. The conforming
form is a step "|CB| = |BC|" before the chain.

---

## Database items

| symbols | what they are | set.mm |
|---|---|---|
| point | a point of the plane | an element of ℂ |
| \|PQ\| | distance between P and Q | ( abs ` ( P − Q ) ) |
| ∠PQR | the angle at Q from P to R | ( ( P − Q ) F ( R − Q ) ), with F the angle function |
| triangle PQR ≅ triangle P′Q′R′ | congruence | (no single set.mm notion) |

| pointer | statement | set.mm |
|---|---|---|
| def:point | Let A be a point. (The plane is a set of points with distance and angle defined on it.) | A ∈ ℂ |
| thm:distance-symmetric | Let P, Q be points. Then \|PQ\| = \|QP\|. | abssub |
| thm:angle-symmetric | Let P, Q, R be points. Then ∠PQR = ∠RQP. | (angle function is antisymmetric up to sign; the unsigned angle is symmetric; needs a lemma) |
| def:triangle | P, Q, R form a triangle ↔ P, Q, R are points, no two equal, not on one line. | (P ≠ Q ∧ Q ≠ R ∧ P ≠ R, plus non-collinearity) |
| thm:triangle-permute | If P, Q, R form a triangle then so does any ordering of them. | (from the definition) |
| def:congruent | triangle PQR ≅ triangle P′Q′R′ ↔ \|PQ\| = \|P′Q′\|, \|QR\| = \|Q′R′\|, \|RP\| = \|R′P′\|, ∠PQR = ∠P′Q′R′, ∠QRP = ∠Q′R′P′, ∠RPQ = ∠R′P′Q′. | (six equations; no set.mm item) |
| thm:side-angle-side | Let P, Q, R form a triangle and P′, Q′, R′ form a triangle. Assume \|PQ\| = \|P′Q′\|. Assume ∠PQR = ∠P′Q′R′. Assume \|QR\| = \|Q′R′\|. Then triangle PQR ≅ triangle P′Q′R′. | (a theorem over ℂ, to be proved; an axiom in Euclid and in Hilbert) |
| thm:isosceles | proved above | isosctr |

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
