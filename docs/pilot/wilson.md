# Pilot: Wilson's theorem

Theorem 44 of `SELECTION.md`, Wiedijk #51:

  if p is prime then (p − 1)! ≡ −1 (mod p).

set.mm's `wilth` is the biconditional, and `wilthimp` is this direction.
Both rest on `wilthlem2`, an induction over sets closed under taking
inverses that takes out one pair at a time, with products written as group
sums. Neither is cited. The proof here is the textbook's. Each a from 2 to
p − 2 has an inverse modulo p, a^(p − 2) by Fermat. That inverse is again
from 2 to p − 2, and it is not a. So the inverses pair those numbers off,
and their product is 1. (p − 1)! is that product times 1 and p − 1.

---

## Theorems

The proof is `proofs/wiedijk/wilson.proof`, three theorems:

- `paired-product` (26 numbered steps, 58 with those inside blocks).
- `coprime-below-prime` (4 steps): gcd(a, p) = 1 for a natural number a
  below a prime p.
- `wilson` (5 steps, 110 with those inside blocks).

Each elaborates to `corpus/elaboration/proofs/wiedijk/wilson/`, assumes
nothing, and verifies. Fermat's little theorem is Euler's theorem
(`proofs/wiedijk/euler`) with φ(p) = p − 1. `congruent-times` is reused
from `proofs/wiedijk/divisibility-by-three`.

---

## Rendered view

**Theorem (pairing).** Let X ⊆ ℤ be finite, n ∈ ℕ, and f : X → X, with
f(f(x)) = x, f(x) ≠ x and x·f(x) ≡ 1 (mod n) for every x ∈ X. Then
∏(x ∈ X) x ≡ 1 (mod n).

*Proof.* Let L be the x ∈ X with x < f(x), and U the rest. X is L ∪ U, and
the two share nothing. For x ∈ L, f(f(x)) = x < f(x), so f(x) ∈ U. Let g
be f on L. g is one-to-one, since f undoes itself. g is also onto U: for
u ∈ U, f(u) ≠ u and not u < f(u), so f(u) < u = f(f(u)). Then f(u) ∈ L
and g(f(u)) = u. So

  ∏(x ∈ X) x = ∏(x ∈ L) x · ∏(x ∈ U) x = ∏(x ∈ L) x · ∏(x ∈ L) f(x)
             = ∏(x ∈ L) x·f(x) ≡ ∏(x ∈ L) 1 = 1 (mod n). ∎

**Lemma (coprime-below-prime).** Let p be prime and a ∈ ℕ with a < p. Then
gcd(a, p) = 1.

*Proof.* p does not divide a, which is below it, and a prime that does not
divide a number is coprime to it. ∎

**Theorem (Wilson).** Let p ∈ ℕ be prime. Then (p − 1)! ≡ −1 (mod p).

*Proof.* p > 1, so p = 2 or p > 2. For p = 2, (2 − 1)! = 1 ≡ −1 (mod 2).
Let p ≥ 3, and for a ∈ {2, …, p − 2} let f(a) = a^(p − 2) mod p.

1. a < p, so gcd(a, p) = 1. By Euler's theorem with φ(p) = p − 1,
   a^(p − 1) ≡ 1 (mod p). Since f(a) ≡ a^(p − 2), a·f(a) ≡ a^(p − 1) ≡ 1.
2. f(a) is a remainder, from 0 to p − 1. It is not 0, since a·0 ≡ 1 would
   make 0 and 1 congruent. It is not 1, since then a ≡ 1 and so a = 1. It
   is not p − 1, since then p would divide p·a − (a(p − 1) − 1) = a + 1,
   which is below p. So f(a) ∈ {2, …, p − 2}.
3. f(a) ≠ a. Otherwise a·a ≡ 1, so p divides (a − 1)(a + 1), and so p
   divides a − 1 or a + 1. Both are between 1 and p − 1.
4. f(f(a)) = a. We have f(f(a))·f(a) ≡ 1 ≡ a·f(a). f(a) is coprime to p
   and cancels, and two congruent remainders are equal.

By the pairing theorem, ∏(a ∈ {2, …, p − 2}) a ≡ 1 (mod p), and

  (p − 1)! = ∏(k = 1 to p − 1) k = (∏(k = 2 to p − 2) k)·(p − 1)
           ≡ p − 1 ≡ −1 (mod p). ∎

---

## Decisions made with the reader

1. **The pairing is a theorem of the proof file, not a lemma of
   `proved.mm`.** A reader sees "the numbers pair off with their inverses".
   The theorem says this of any finite set of integers and any f that
   undoes itself and has no fixed point. It splits X into the members
   below their partners and those above (`set-builder-split`). It does not
   induct on |X| as set.mm does. So there is no induction over sets, and
   each step is one fact about products.
2. **f is a power modulo p, as Euler's proof defines its map.** Each of
   its properties is a "for all" line over {2, …, p − 2}. Inside a block
   over that set, such a line is cited at the block's letter. It is
   instantiated at f(a) only where f(a) is the point (step 5.16).
3. **The set {2, …, p − 2} is written out and not named.** A range letter
   is an integer said once, and its bounds come with it. So `let a ∈
   {2, …, p − 2}` gives `inequalities` 0 < a, a < p and a + 1 < p without
   a line.
4. **p = 2 is a case of its own.** It is worked out by `arithmetic` and
   put back by substituting 2 = p. p = 3 needs no case: {2, …, 1} is
   empty, and the pairing theorem holds of the empty set.
5. **Facts a reader does not name are library records.** "n does not
   divide a natural number below it" and "n − 1 ≡ −1 (mod n)" are mundane
   records, not theorems of the page. `coprime-below-prime` stays a theorem
   of the file, since it puts three such facts together.

---

## Database items

These are the records the proof imports that this branch added. All
eleven were added for it, unless noted.

In `corpus/stdlib/sums.records`, each mundane:
- `product-first` (`fprod1p`)
- `product-split` (`fprodsplit`)
- `product-reindex` (`fprodf1o`, through `gfprodf1o` in `proved.mm`)
- `product-of-products` (`fprodmul`)
- `product-of-ones` (`prod1`)
- `range-inside` (`fzss1` and `fzss2`, joined as `gfzss` in `proved.mm`)

In `corpus/stdlib/counting.records`, mundane: `factorial-product`
(`fprodfac`).

In `corpus/stdlib/divisibility.records`:
- named: `phi-prime` (`phiprm`), and `product-congruent-termwise`, which
  `corpus/stdlib/divisibility.proof` proves on the page by induction over
  the finite set.
- mundane: `below-not-divisible` (`fzm1ndvds` read over x ∈ ℕ below n,
  through `gnndvdslt`), and `minus-one-congruent` (`iddvds`, through
  `gm1cong`).

The proof also cites `set-builder-split` and `set-builder-split-disjoint`,
which the Ramsey pilot added.

The lemmas behind these are in `corpus/proved/`. `totient.proved` has
`gfprodf1o`. `divisors.proved` has `gnndvdslt` and
`gm1cong`, and also `gcongcomd`, which puts a congruence's two sides in
order (point 6 below). `ranges.proved` has `gfzss`. In
`corpus/db/notation.records`, `congruent-mod` says `commutes any order of
holes 1 and 2`.

---

## What the pilot reveals

1. **A product over a set of anything asked nothing of its term.** The
   checker took ∏(x ∈ X) x over X ⊆ ℤ to be a number by what the page
   says once, and the build could not settle x ∈ ℂ. A set that is no range
   and no number system puts its letter in no system. So the term is said
   by a line saying every member is a number, unless it is a value of a
   function typed on that very set. The line here is H1, X ⊆ ℤ, which says
   its members (point 9) (`citations::said_over_any_set`; planted case
   "split a product over a set of integers without a line saying its
   members are numbers").
2. **A function on X applied over a part of X was read as the item's
   function itself.** `product-of-products` is cited over L ⊆ X, with
   f : X → X. The match made u the page's f and took the item's set from
   f's let, X, so the claim over L did not match. Now the match also tries
   the rule k ↦ f(k) (`matching::applied_as_rule`). A let's set is not
   used where the claim says another set. The type is asked at every point
   of the part, by a line (`on_a_part`;
   `tests/elaborator/a-product-over-a-part-of-a-domain`).
3. **An item over a set could not be cited at a product from a to b.** The
   standard form reads ∏(k ∈ {a, …, b}) as ∏(k = a to b), so a pattern over
   a set X met only the range form. The ground is now read back over the
   set where the pattern's set is still to be bound (`matching::unfilled`;
   `a-product-from-a-to-b-cited-over-a-set`).
4. **A congruence chain opening with an equation took its first term's
   integrality from a line the step does not name.** The checker reads the
   first term as an integer next to the other side of the equation that
   the first link cites. The build searched instead, found f(a) ∈ ℤ in
   scope, and provenance then refused it. The build now carries the
   membership across the equation (`Equated`;
   `a-congruence-chain-opening-with-an-equation`). `ten-power-congruent`'s
   kernel proof changed with it, and it verifies.
5. **`fprodf1o` names a term its conclusion does not.** Its G, the image
   of each index, is fixed only by a hypothesis, and a target's `with`
   cannot name a product's own letter. So `gfprodf1o` writes G as F ` n.
6. **A congruence's two sides stand in no order.** The checker reads
   a ≡ b (mod n) and b ≡ a (mod n) as one claim, as it does an equation's
   two sides. The build's standard form puts the two in order by
   `gcongcomd`. An item's hypothesis, a claim and a calculation's link each
   take a congruence either way round, so step 5.16.5 cites a·f(a) ≡ 1 as
   1 ≡ a·f(a) (`tests/elaborator/a-congruence-read-either-way`).
7. **A citation through a define binds the item's function to the
   define's rule.** g(x) = f(x) on L. Citing the define, `product-reindex`
   is matched with its g as the rule x ↦ f(x), so step 16 claims
   ∏(x ∈ U) x = ∏(x ∈ L) f(x), as a reader writes it. `g : L → U` says
   f(x) ∈ U at a point of L (`a-product-reindexed-through-a-define`,
   `a-value-through-a-define`).
8. **A line saying a term is in a range says its bounds**, as k ∈ ℕ says
   k ≥ 1. `inequalities, from K1` reads 2 ≤ a and a ≤ p − 2 from
   `let a ∈ {2, …, p − 2}`. A range inside another, {2, …, p − 2} ⊆
   {0, …, p − 1}, is the record `range-inside` (step 5.13)
   (`a-range-line-gives-its-bounds`).
9. **A subset line says its members.** X ⊆ ℤ says "for all x ∈ X,
   x ∈ ℤ" to every route but `join` and `restate` (`SYNTAX.md`, What a
   cited line says). So `product-split` cites H1 directly, and no line
   restates L ⊆ ℤ or U ⊆ ℤ.
10. **A "for all" line is read at a block's letter.** Inside a block that
    opened with `let a ∈ {2, …, p − 2}`, a line above it saying "for all
    a ∈ {2, …, p − 2}, P(a)" says P(a). So 5.8.1 cites 5.5 and 5.14.4.7
    restates 5.10, each with no instantiate step
    (`tests/elaborator/a-for-all-line-read-in-a-block`).
11. **A cited line can supply an identity element.** `congruent-times` at
    ∏·(p − 1) ≡ 1·(p − 1), claimed as ≡ p − 1, needs `b := 1`. The claim is
    matched first and does not fix b.

Numbers, for the record: 35 numbered steps at the left margin, 172 with
those inside blocks, over three theorems, and 30 requires lines.
