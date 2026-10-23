# Pilot: inclusion–exclusion for two and three sets

Wiedijk #96, set.mm's `hashun3` for two sets:

  |A ∪ B| = |A| + |B| − |A ∩ B|,
  |A ∪ B ∪ C| = |A| + |B| + |C| − |A ∩ B| − |A ∩ C| − |B ∩ C| + |A ∩ B ∩ C|.

The general principle, set.mm's `incexc`, sums over every family of the
sets, which the page cannot yet say. The two- and three-set forms are what a
reader meets first, and the second follows from the first.

---

## Theorems inclusion-exclusion-two and inclusion-exclusion-three

The proof is `proofs/wiedijk/inclusion-exclusion.proof`. It elaborates to
`corpus/elaboration/proofs/wiedijk/inclusion-exclusion/`, one file per
theorem, each assuming nothing and verifying.

---

## Rendered view

**Theorem.** If A and B are finite, |A ∪ B| = |A| + |B| − |A ∩ B|.

*Proof.*

1. A ∪ B is A together with B ∖ A, and the two share nothing, so
   |A ∪ B| = |A| + |B ∖ A|.
2. B is B ∩ A together with B ∖ A, and the two share nothing. B ∩ A is
   A ∩ B, so |B| = |A ∩ B| + |B ∖ A|.
3. Subtract: |A ∪ B| = |A| + |B| − |A ∩ B|.

That B ∖ A and A ∩ B are finite, as parts of B and of A, and so have sizes
in ℕ₀, is written as steps, since counting the disjoint unions asks for it. ∎

**Theorem.** If A, B and C are finite, |A ∪ B ∪ C| = |A| + |B| + |C| −
|A ∩ B| − |A ∩ C| − |B ∩ C| + |A ∩ B ∩ C|.

*Proof.*

1. By the two-set theorem for A ∪ B and C:
   |A ∪ B ∪ C| = |A ∪ B| + |C| − |(A ∪ B) ∩ C|.
2. By it for A and B: |A ∪ B| = |A| + |B| − |A ∩ B|.
3. (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C), and by the two-set theorem once more,
   with (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C:
   |(A ∪ B) ∩ C| = |A ∩ C| + |B ∩ C| − |A ∩ B ∩ C|.
4. Put 2 and 3 into 1. ∎

---

## Database items

In `corpus/stdlib/sets.records`, each mundane:

- `intersection-distributes-right` (`indir`)
- `intersection-distributes-over-intersection` (`inindir`)
- `intersection-subset` (`inss1`)
- `intersection-and-difference` (`inundif`)
- `intersection-and-difference-disjoint` (`inindif`)

Cited from the library as it stood: `card-disjoint-union`, `card-nat0`,
`finite-part`, `union-finite`, `difference-subset`, `disjoint-difference`,
`union-difference`, `intersection-commutes`.

---

## What the pilot reveals

1. **An intersection is a set.** The build reads a set's finiteness off its
   size being a whole number (`hashvnfin`), and that asks the set to be a
   set. Its table of lemmas making a term a set by its head had difference
   and union but not intersection. So |A ∩ B| ∈ ℕ₀ did not give A ∩ B
   finite, and the checker accepted what the build could not prove. The
   table now holds `inex1g`, and `tests/elaborator/an-intersection-counted.proof`
   holds it to that.

2. **The three-set form is the two-set one three times.** Nothing about
   families of sets is needed for three. What makes the general `incexc`
   wait is a sum over every subfamily, not the counting.

3. **A distributive law is cited in the order the reader writes it.**
   `intersection-distributes` states X ∩ (Y ∪ Z), and the proof meets
   (A ∪ B) ∩ C. Reaching it by commuting takes three substitutions a reader
   never writes, so set.mm's `indir` is an item of its own.

4. **Memberships come from cited equations.** The closing `algebra` of the
   two-set theorem cites the three ℕ₀ lines and the two equations. |A ∪ B|
   and |B| need no line of their own, since a cited equation says they are
   numbers.
