# Pilot: the harmonic series diverges

Theorem 24 of `SELECTION.md`, Wiedijk #34:

  1 + 1/2 + 1/3 + … has no limit.

set.mm's `harmonic` says the partial sums are not in the domain of `~~>`. The
proof here is the textbook one, Oresme's: group the terms in blocks that
double in length, 1/2, then 1/3 + 1/4, then 1/5 + … + 1/8, each worth at least
1/2, so the partial sums pass every bound, and a sequence with a limit is
bounded. ProofWiki gives the same argument.

---

## Theorems harmonic-block, harmonic-unbounded and harmonic

The proof is `proofs/harmonic.proof`, three theorems. `harmonic-block` is one
block: Σ(k = 1 to 2^(j + 1)) 1/k ≥ Σ(k = 1 to 2^j) 1/k + 1/2. `harmonic-unbounded`
adds the blocks up by induction and passes any bound M. `harmonic` is set.mm's
statement, by contradiction. All three elaborate to
`corpus/elaboration/proofs/harmonic/`, assume nothing, and verify.

Numbers: `harmonic-block` is 15 numbered steps, 23 with those inside blocks;
`harmonic-unbounded` 6 and 15; `harmonic` 2 and 8.

---

## Rendered view

**Theorem (a block).** For j ∈ ℕ₀, 1 + 1/2 + … + 1/2^(j+1) ≥
1 + 1/2 + … + 1/2^j + 1/2.

*Proof.* The sum to 2^(j+1) is the sum to 2^j and the sum of 1/k for k from
2^j + 1 to 2^(j+1). Each of those 2^j terms is at least 1/2^(j+1), so their
sum is at least 2^j · 1/2^(j+1) = 1/2. ∎

**Theorem (unbounded).** For every M ∈ ℝ there is n ∈ ℕ with
1 + 1/2 + … + 1/n > M.

*Proof.* By induction on m, the sum to 2^m is at least m/2: it is 1 at m = 0,
and each block adds at least 1/2. Choose N ∈ ℕ with N > 2M; the sum to 2^N
is at least N/2 > M. ∎

**Theorem (harmonic).** There is no L ∈ ℝ with 1 + 1/2 + … + 1/n → L as
n → ∞.

*Proof.* Suppose there were. A sequence with a limit is bounded, so some B
is at least every partial sum; but some partial sum exceeds B. ∎

---

## Decisions made with the reader

1. **Both statements.** The reader chose to prove that the partial sums pass
   every bound and, from it, set.mm's statement that they have no limit, so
   this is the corpus's first proof that a limit does not exist.
2. **The bound is m/2, not the textbook's 1 + m/2.** Both hold and either
   finishes the proof. With 1 + m/2 the induction step's arithmetic reaches
   3/2, and the coefficient arithmetic names a lemma only for one-digit
   products, so the step was taken as stated; m/2 keeps every constant a
   half. The limit is recorded below.
3. **The block is a theorem of its own,** as `binomial-step` is: inside the
   induction step the hypothesis is in scope and its sum binds k, which
   set.mm's sum lemmas keep out of the scope.

---

## What the pilot reveals

1. **An `obtain` could not read an item whose letter is a function.**
   `convergent-bounded` says there is a B with every x(m) ≤ B, and the
   elaborator read that existential in the proof's own names, where x is
   nothing. It now reads it in the item's names and fills in what the step's
   lines fix: `item_binding` matches the item's hypotheses against the cited
   lines, now with the places a binder applies a function letter marked, so
   `x(n) → L` cited at the partial sums makes x their rule (`ELABORATION.md`).
   An item taken as stated (`assume_item`) reads its letters the same way.
2. **The checker asked a function letter's values only of what a step
   claims.** An `obtain` claims the witness, so `requires for all n ∈ ℕ,
   Σ(k = 1 to n) 1/k ∈ ℝ` was refused as asked by nothing. Its values are now
   also read where the item's hypotheses meet the cited lines.
3. **`inequalities` decided a claim with a constant to spare and did not
   prove it.** From s = 1, s ≥ 0 was taken as stated: a certificate using
   one equation went to a route that writes the equation scaled and nothing
   else. That route is now taken only where nothing is left over;
   `tests/elaborator/constant-left-over.proof` keeps it so.
4. **An `obtain` from an item was judged twice for what its lines do.** The
   elaborator leaves a step citing an item to the checker, and now an
   `obtain` citing one too: `gclimbdd` does not need the limit to be real,
   which the item's `let L ∈ ℝ` says and the restated test cites.
5. **The `$d` trap again, three times.** `gclimbdd` first renamed its index
   inside the map, which binds n, and violated its own conditions; it now
   asks, as set.mm's lemmas do, for (n = m → B = C) and never renames. The
   item's conclusion uses m and its limit n, so a scope holding the limit
   does not meet a condition on n. And `membership` proved Σ ∈ ℝ inside the
   induction step and the contradiction with `fsumrecl`, whose index the
   scope there binds; the verifier refused it. `membership` now shows such a
   sum over a letter nothing holds and renames it back, as a lemma citation
   moves to other letters, so the page writes `membership` there as anywhere
   (`tests/elaborator/sum-letter-in-scope.proof`).
6. **What is still a limit.** A term like 1/k is real only where something
   says k ≠ 0, so a sum over {2^j + 1, …, 2^(j + 1)} needs its terms said
   real in a line of its own (`harmonic-block` step 7). The coefficient
   arithmetic stops at one digit.
