# Pilot: the angle sum of a triangle

Theorem 21 of `SELECTION.md`, set.mm's `ang180`, Wiedijk #27:

  the angles of a triangle add up to 180°.

The proof is the school one: through one vertex draw the parallel to the
opposite side, read off two pairs of alternate angles, and see the three
angles at that vertex make a straight line. Euclid's own proof (I.32)
extends one side beyond a vertex and draws the parallel to another side
through that vertex; the school form needs one parallel and no extension. No textbook was fetched for it,
so the source is the proof as it is commonly taught, not a checked page.

---

## Theorem angle-sum

The proof is `proofs/angle-sum.proof`. It elaborates to
`corpus/elaboration/proofs/angle-sum/angle-sum.mm`, assumes nothing, and
verifies. set.mm's `ang180` states the sum of the signed angles as π or −π;
this statement is the unsigned one, 180°.

Numbers: 9 numbered steps and no blocks. Steps 1 and 2 reorder the triangle
for the items' hypotheses; 3 draws the parallel; 4 and 5 are the alternate
angles; 6 the straight line; 7 to 9 substitute and add.

---

## Rendered view

**Theorem.** If A, B and C form a triangle, then ∠BAC + ∠ABC + ∠BCA = 180°.

*Proof.* Draw the line DE through B parallel to AC, with D on A's side and
E on C's. Then ∠DBA = ∠BAC and ∠EBC = ∠BCA, as alternate angles. The angles
∠DBA, ∠ABC and ∠EBC make up the straight line DE, so they add to 180°, and
therefore ∠BAC + ∠ABC + ∠BCA = 180°. ∎

---

## Decisions made with the reader

1. **Degrees on the page, radians underneath.** The statement says 180°,
   which is how a school reader knows the theorem. ° is a notation, x° being
   x·π/180, and the angle stays the number from 0 to π that
   `mun:stdlib/geometry/angle` defines.
2. **The textbook proof, not set.mm's.** `ang180` is proved through the
   complex logarithm, a product of three quotients that is −1. The readable
   proof uses a parallel and alternate angles, which the library did not
   have, so three items were added: `parallel-through`, `alternate-angles`
   and `angles-on-a-line`.
3. **The parallel goes through B,** not C, so that the theorem reads in the
   order a reader says it, the angles at A, B and C, with no symmetry steps.
4. **What the figure shows is written.** "D on A's side" is three sentences:
   D and C are on opposite sides of line BA, E and A on opposite sides of
   line BC, and A and C on the same side of line BD. The items need them to
   know which way round the angles lie, since the angle is unsigned.
   `GEOMETRY.md` weighs that cost.
5. **angles-on-a-line states no distinctness.** Its three side and between
   conditions force every point apart from the vertex, which is all the
   three angles need; `alternate-angles` cannot derive Q ≠ P or R ≠ P, and
   states them.

---

## Database items

New notations: `plane` (𝔼²), `parallel` (line PQ ∥ line RS), `between`,
`same-side`, `opposite-sides`, `pi` (π) and `degrees` (x°). New records in
`corpus/stdlib/geometry.records`: the definitions `parallel`, `between` and
`same-side`, which the readable layer cannot state, as `collinear` is; the
axiom `parallel-through`; and the theorems `alternate-angles` and
`angles-on-a-line`. The three items are proved in `proved.mm`, by `gparthru`,
`galtang` and `gline`; `GEOMETRY.md` lists the lemmas under them.

---

## What the pilot reveals

1. **A pattern cannot open on two juxtaposed holes.** `BD ∥ AC` does not
   parse: |CA| has its bars and ∠BAC its ∠ to start from, and `PQ ∥ RS` has
   nothing. The notation is `line BD ∥ line AC`, after the "line BD" the
   side notations already write.
2. **An `obtain` said only four sentences deep.** The elaborator took the
   obtained claim apart four conjunctions deep, so of the parallel's eight
   sentences the first two stayed joined and step 4 could not cite one of
   them. It now takes the claim apart as deep as its sentences, as it does
   any line saying several things.
3. **Two congruences were missing.** Re-proving the parallel's existence,
   as the gate's restatement of each item does, carries a change through ≠
   and through two of a three-way conjunction, and the table had neither:
   `neeq1d`, `neeq2d`, `neeq12d` and `3anbi12d`, `3anbi13d`, `3anbi23d` now
   stand beside the others like them.
4. **Every inequality is checked as written.** The checker meets a
   `requires C ≠ A` only with a line saying C ≠ A, so `alternate-angles`
   takes Q ≠ P and R ≠ P, which the triangle states in one order or the
   other, and step 2 rotates it for the first use.
