# Pilot: a Liouville number is transcendental

Theorem 51 of `SELECTION.md`, set.mm's `aaliou3`, the second half of
Metamath 100 #18 (the first half is theorem 50, `liouville`):

  Σ(k = 1 to ∞) 1/2^(k!) is transcendental.

---

## Theorems factorial-gap to liouville-number

The proof is `proofs/wiedijk/liouville-number.proof`, ten theorems over the
partial sums s(n) = Σ(k = 1 to n) 1/2^(k!), defined for n ∈ ℕ₀. All
elaborate to `corpus/elaboration/proofs/wiedijk/liouville-number/`, assume
nothing, and verify.

Numbers: `factorial-gap` is 14 steps, `terms-real` 4, `partial-sum-real` 4,
`tail-bound` 36, `partial-sum-step` 6, `partial-sums-increase` 15,
`later-at-least` 6, `later-at-most` 13, `scaled-sum-integer` 21,
`liouville-number` 84.

---

## Rendered view

1. (n + 1)! + j ≤ (n + 1 + j)!, so the terms after the n-th are at most
   1/2^A, 1/2^(A + 1), … with A = (n + 1)!, and they add to at most 2/2^A.
2. The partial sums rise and stay below 1, so they tend to a limit L, with
   s(n) < L ≤ s(n) + 2/2^((n + 1)!).
3. 2^(n!)·s(n) is an integer, so s(n) is a fraction p/q with q = 2^(n!).
4. If L were algebraic, of degree N, Liouville's theorem would give c > 0
   with c/q^N < |L − p/q| for every such fraction. Take n = m + N with
   m > 2/c: then |L − s(n)| ≤ 2/2^((n + 1)!) = 2/(q^N·2^(n!·(m + 1))), which
   is below c/q^N since 2^(n!·(m + 1)) > m > 2/c.

So L is transcendental. ∎

---

## Database items

In `stdlib/calculus`: `monotone-limit`, `limit-at-most` and
`limit-at-least`, which a proof names, each proved on the page in
`corpus/stdlib/calculus.proof`. In `corpus/stdlib/polynomials.records`:
`algebraic-root`, which a proof names. Mundane: `factorial-at-most` in
`counting.records`, and `power-exponent-le` and `nat-plus-nat0` in
`numbers.records`. Each record has its lemma in `proved.mm` or is a set.mm
label.

---

## What the pilot reveals

1. **A sequence given as a map.** The limit theorems are cited with the
   sequence as the map n ∈ ℕ ↦ s(n). Each of a theorem's hypotheses binds
   its own letter, so "s(n) → L as n → ∞" and "s(i) ≤ B for all i ≥ N"
   match lines that bind n in one and i in the other. In the build a map
   applied is read as its rule under a binder, a map's rule is carried
   under its letter (`mpteq2dva`), moving a letter leaves a map that binds
   its own alone, and an inner map is renamed apart before a renaming that
   would break a lemma's distinct-variable pairs.

2. **The domain of s.** The statements write s(n + j) with j ∈ ℕ₀, and the
   build places n + j in ℕ₀ but not in ℕ, so s is defined from 0, where it
   is the empty sum.

3. **A bound passes to the limit.** `limit-at-most` and `limit-at-least`
   name x and N in their `with` lines, since neither appears in the
   conclusion a lemma is matched to.
