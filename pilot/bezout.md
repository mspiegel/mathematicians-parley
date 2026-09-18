# Pilot: Bezout's identity

Fifth pilot, first draft, written to `SYNTAX.md`. Its purpose is an
existence proof whose witness comes from a least element rather than a
construction: the gcd of a and b is the smallest positive number of the
form ax + by. Number 60 on Wiedijk's list, `bezout` in set.mm, and
Hammack's chapter on non-conditional statements.

Provisional forms introduced here, all listed in the batch report:

- `define S := {...} (D1)`: an unnumbered, labelled line that names an
  object built from things already in scope. Cited by label.
- Set-builder notation {t ∈ X : ...}, with the convention `def:set-builder`
  that t ∈ {t ∈ X : P(t)} ↔ t ∈ X and P(t).
- `instantiate v := t in line L, from L2`: line L claims "for every
  v ∈ X, ..."; the step claims the body with t for v, and L2 supplies
  t ∈ X. This is taking one case of a "for every" sentence that a line
  states, as `thm:X v := t` takes one case of a theorem.

The textbook proof shows "d divides a" and then says "similarly, d
divides b". There is no "similarly" in this language, so the argument is
a lemma applied twice.

---

## Theorem least-combination-divides

```
theorem least-combination-divides
  let a ∈ ℕ                                                           (H1)
  let b ∈ ℕ                                                           (H2)
  let c ∈ ℕ                                                           (H3)
  let d ∈ ℕ                                                           (H4)
  let u ∈ ℤ                                                           (H5)
  let v ∈ ℤ                                                           (H6)
  let x₀ ∈ ℤ                                                          (H7)
  let y₀ ∈ ℤ                                                          (H8)
  assume c = a·u + b·v                                                (H9)
  assume d = a·x₀ + b·y₀                                              (H10)
  assume for every x ∈ ℤ, for every y ∈ ℤ,
         if a·x + b·y ∈ ℕ then d ≤ a·x + b·y                          (H11)
  then d divides c

1.  q ∈ ℤ. r ∈ ℤ. c = q·d + r. 0 ≤ r. r < d.
    obtain q, r: thm:division-algorithm n := c, d := d, from H3, H4

2.  r = a·(u − q·x₀) + b·(v − q·y₀)
    algebra, from 1, H9, H10

3.  r = 0
    contradiction
    suppose not r = 0                                                 (S)

    3.1.  0 < r
          inequalities, from 1, S

    3.2.  r ∈ ℕ
          thm:pos-int-nat m := r, from 1, 3.1

    3.3.  a·(u − q·x₀) + b·(v − q·y₀) ∈ ℕ
          substitute r = a·(u − q·x₀) + b·(v − q·y₀) (line 2) into line 3.2

    3.4.  d ≤ a·(u − q·x₀) + b·(v − q·y₀)
          instantiate x := u − q·x₀, y := v − q·y₀ in H11, from 3.3
          requires u − q·x₀ ∈ ℤ: thm:int-closure, from H5, 1, H7
          requires v − q·y₀ ∈ ℤ: thm:int-closure, from H6, 1, H8

    3.5.  d ≤ r
          substitute r = a·(u − q·x₀) + b·(v − q·y₀) (line 2) into line 3.4

    3.6.  not d ≤ r
          inequalities, from 1

    3.7.  d ≤ r. not d ≤ r.
          lines 3.5, 3.6

4.  c = q·d + 0
    substitute r = 0 (line 3) into line 1

5.  c = d·q
    algebra, from 4

6.  d divides c
    def:divides d := d, n := c, from 1, 5
    requires d ∈ ℤ: thm:nat-int, from H4
    requires c ∈ ℤ: thm:nat-int, from H3
```

---

## Theorem bezout

```
theorem bezout
  let a ∈ ℕ                                                           (H1)
  let b ∈ ℕ                                                           (H2)
  then there are x ∈ ℤ and y ∈ ℤ with a·x + b·y = gcd(a, b)

define S := {t ∈ ℕ : there are x ∈ ℤ and y ∈ ℤ with t = a·x + b·y}   (D1)

1.  a = a·1 + b·0
    algebra

2.  a ∈ S
    def:set-builder t := a, from H1, 1
    requires 1 ∈ ℤ: arithmetic
    requires 0 ∈ ℤ: arithmetic

3.  S ⊆ ℕ
    thm:set-builder-subset, from D1

4.  d ∈ S. For every s ∈ S, d ≤ s.
    obtain d: thm:well-ordering S := S, from 3, 2

5.  d ∈ ℕ
    def:subset, from 3, 4

6.  x₀ ∈ ℤ. y₀ ∈ ℤ. d = a·x₀ + b·y₀.
    obtain x₀, y₀: def:set-builder t := d, from 4

7.  For every x ∈ ℤ, for every y ∈ ℤ,
    if a·x + b·y ∈ ℕ then d ≤ a·x + b·y.
    fix
    let x ∈ ℤ                                                         (K1)
    let y ∈ ℤ                                                         (K2)
    assume a·x + b·y ∈ ℕ                                              (K3)

    7.1.  a·x + b·y ∈ S
          def:set-builder t := a·x + b·y, from K3

    7.2.  d ≤ a·x + b·y
          instantiate s := a·x + b·y in line 4, from 7.1

8.  a = a·1 + b·0
    algebra

9.  d divides a
    thm:least-combination-divides c := a, u := 1, v := 0, from H1, H2,
      H1, 5, 6, 8, 7
    requires 1 ∈ ℤ: arithmetic
    requires 0 ∈ ℤ: arithmetic

10. b = a·0 + b·1
    algebra

11. d divides b
    thm:least-combination-divides c := b, u := 0, v := 1, from H1, H2,
      H2, 5, 6, 10, 7
    requires 0 ∈ ℤ: arithmetic
    requires 1 ∈ ℤ: arithmetic

12. gcd(a, b) ∈ ℕ. gcd(a, b) divides a. gcd(a, b) divides b.
    For every e ∈ ℕ, if e divides a and e divides b then e ≤ gcd(a, b).
    def:gcd a := a, b := b, from H1, H2

13. d ≤ gcd(a, b)
    instantiate e := d in line 12, from 5, 9, 11

14. gcd(a, b) divides a·x₀ + b·y₀
    thm:divides-combination e := gcd(a, b), from 12, 6
    requires gcd(a, b) ∈ ℤ: thm:nat-int, from 12

15. gcd(a, b) divides d
    substitute d = a·x₀ + b·y₀ (line 6) into line 14

16. gcd(a, b) ≤ d
    thm:divides-le e := gcd(a, b), m := d, from 12, 5, 15

17. d = gcd(a, b)
    inequalities, from 13, 16

18. a·x₀ + b·y₀ = gcd(a, b)
    calculation
      a·x₀ + b·y₀ = d               6, right to left
                  = gcd(a, b)       17

19. There are x ∈ ℤ and y ∈ ℤ with a·x + b·y = gcd(a, b).
    exhibit, from 6, 18
```

---

## Database items

| symbols | what they are | set.mm |
|---|---|---|
| {t ∈ X : ...} | set-builder notation | crab |
| ⊆ | subset | wss |
| gcd(a, b) | greatest common divisor | cgcd |

| pointer | statement | set.mm |
|---|---|---|
| def:set-builder | Let X be a set. t ∈ {t ∈ X : P(t)} ↔ t ∈ X and P(t). | rabid, elrab |
| def:subset | X ⊆ Y ↔ for every t ∈ X, t ∈ Y. | df-ss, ssel |
| thm:set-builder-subset | {t ∈ X : P(t)} ⊆ X | ssrab2 |
| def:gcd | Let a ∈ ℕ, b ∈ ℕ. gcd(a, b) ∈ ℕ. gcd(a, b) divides a. gcd(a, b) divides b. For every e ∈ ℕ, if e divides a and e divides b then e ≤ gcd(a, b). | gcdcl, gcddvds, dvdslegcd |
| thm:well-ordering | Let S ⊆ ℕ. Assume there is s ∈ S. Then there is d ∈ S with for every s ∈ S, d ≤ s. | nnwo |
| thm:division-algorithm | Let n ∈ ℕ, d ∈ ℕ. Then there are q ∈ ℤ and r ∈ ℤ with n = q·d + r, 0 ≤ r, and r < d. | divalg |
| thm:pos-int-nat | Let m ∈ ℤ. Assume 0 < m. Then m ∈ ℕ. | elnnz |
| thm:divides-combination | Let e ∈ ℤ, a ∈ ℤ, b ∈ ℤ, x ∈ ℤ, y ∈ ℤ. Assume e divides a. Assume e divides b. Then e divides a·x + b·y. | dvds2ln |
| thm:divides-le | Let e ∈ ℕ, m ∈ ℕ. Assume e divides m. Then e ≤ m. | dvdsle |
| thm:least-combination-divides, thm:bezout | proved above | bezout |

Provisional methods.

| pointer | what the reader checks | set.mm |
|---|---|---|
| define | the label names the object written after :=; nothing is claimed | (a class abbreviation hypothesis, as in bezout's own lemmas) |
| instantiate v := t in line L, from L2 | line L claims "for every v ∈ X, B"; L2 claims t ∈ X; the claim is B with t for v | rspcv, rspccva |

---

## What the pilot reveals

1. **"Similarly" is a lemma.** The textbook proves d divides a and says
   the same argument gives d divides b. Here the argument is the theorem
   least-combination-divides with eleven hypotheses, applied at steps 9
   and 11 with (c, u, v) = (a, 1, 0) and (b, 0, 1). The lemma's statement
   is ugly because it carries everything the argument uses. That is the
   honest cost of "similarly".
2. **Naming an object needs a line.** S is built from a and b and used in
   six steps. `define S := ... (D1)` names it once. It is not a claim and
   not a hypothesis; it is a third kind of unnumbered line. Lamport's
   proofs have DEFINE for the same purpose.
3. **Instantiating a line.** Step 4 claims "for every s ∈ S, d ≤ s", and
   step 7.2 needs it for one s. So far only theorems and definitions could
   be instantiated, with `thm:X v := t`. `instantiate s := ... in line
   4, from 7.1` does the same for a line. It is a quantifier move and so, by
   READERS.md, a method.
4. **A hypothesis can be a "for every" sentence.** H11 quantifies over x
   and y. Citing it is an `instantiate`, at step 3.4. A `let`/`assume`
   statement can therefore contain quantifiers, which the earlier pilots
   did not need.
5. **Set-builder membership is a definition used both ways.** Step 2 puts
   a into S with the witnesses read off line 1; step 6 takes d out of S by obtaining
   them. Both are the ↔ convention on def:set-builder with the ∃ inside.
6. **An item is not a line.** The first draft cited "def:gcd" in `from`
   at three steps, as if it were a line, because its sentences about
   gcd(a, b) are facts once a and b are fixed. Decided: `from` lists
   lines and labels only. The four sentences are now step 12, citing
   def:gcd once with a and b filled in, and the later steps cite line 12.
   One step more, and nothing after `from` that is not on the page.
7. **Twelve requires lines for ℤ and numerals.** 1 ∈ ℤ, 0 ∈ ℤ, and
   nat-int appear repeatedly. This is the divides-on-ℤ decision paying
   as expected, and it shows why the viewer's collapse-by-role matters.

Numbers, for the record: the lemma has 13 numbered steps and 4 requires
lines; the theorem has 21 numbered steps and 7 requires lines. set.mm's
bezout has 47 essential steps.
