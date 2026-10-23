# Pilot: the sum of k-th powers

Wiedijk #77, set.mm's `fsumkthpow`:

  Σ(n = 0 to m) n^k = (B(k + 1, m + 1) − B(k + 1, 0))/(k + 1)

for k, m ∈ ℕ₀, where B(n, x) is the n-th Bernoulli polynomial at x. The
first proof in the corpus over a function the library defines by a
recursion through a sum.

---

## Theorem sum-of-powers

The proof is `proofs/wiedijk/sum-of-powers.proof`. It elaborates to
`corpus/elaboration/proofs/wiedijk/sum-of-powers/sum-of-powers.mm`, which
assumes nothing and verifies.

---

## Rendered view

B(n, x) is the Bernoulli polynomial: x^n less
Σ(k = 0 to n − 1) C(n, k)·B(k, x)/((n − k) + 1).

**Theorem.** For k, m ∈ ℕ₀,
Σ(n = 0 to m) n^k = (B(k + 1, m + 1) − B(k + 1, 0))/(k + 1).

*Proof.*

1. For every n ∈ {0, …, m}, B(k + 1, n + 1) − B(k + 1, n) = (k + 1)·n^k,
   by the difference property of the Bernoulli polynomials.
2. So Σ(n = 0 to m) (B(k + 1, n + 1) − B(k + 1, n)) =
   Σ(n = 0 to m) (k + 1)·n^k, term by term.
3. The left side telescopes to B(k + 1, m + 1) − B(k + 1, 0).
4. The right side is (k + 1)·Σ(n = 0 to m) n^k.
5. So (k + 1)·Σ(n = 0 to m) n^k = B(k + 1, m + 1) − B(k + 1, 0), and
   dividing by k + 1, which is not 0, gives the theorem. ∎

---

## Database items

In `corpus/stdlib/polynomials.records`:

- `definition B`: sort number, number → number; builds `_1 _2 cbp co`; its
  `then` is `bpolyval`.
- `mundane theorem bernoulli-complex` (`bpolycl`).
- `theorem bernoulli-difference` (`bpolydif`).

In `corpus/stdlib/sums.records`:

- `theorem sum-telescopes-up` (`telfsum2`).
- `mundane theorem sum-termwise-complex` (`sumeq2dv`).

Cited from the library as it stood: `sum-scaled`, `nat0-successor`.
`tests/stdlib/polynomials.proof` tests `B`'s definition, which no proof
unfolds.

---

## What the pilot reveals

1. **A recursive function is a library function like any other.** B is a
   definition with a `sort` line, like C and gcd, applied as B(n, x). Its
   defining clause names B again, inside a sum over the earlier indices,
   and reads and builds as it stands. No notation was needed, and the
   subscript Bₙ(x) a textbook writes is not one.

2. **set.mm says only that B's values are complex.** Bernoulli polynomials
   have rational coefficients, but set.mm has `bpolycl` and no lemma
   putting B(n, x) in ℝ at a real x. So the two sum items the proof cites
   are stated over ℂ, beside their real forms: `sum-telescopes-up` and
   `sum-termwise-complex`. `algebra` takes B(k + 1, m + 1) as an atom given
   a requires line putting it in ℂ, as it does i.

3. **A function letter is read off the occurrence that decides it,
   wherever it is written.** `sum-telescopes-up` writes t(k + 1) before
   t(k), and the checker paired a formula's parts left to right. So it met
   t(k + 1), which cannot decide t, before t(k), which can, and refused
   every upward telescoping sum, (n + 1)^2 − n^2 among them. Parts holding
   an occurrence that decides a letter are now paired first
   (`matching::fit`), and `tests/elaborator/a-telescoping-sum-read-upward.proof`
   holds it to that.

4. **A cited function's type is the build's to settle.** The checker does
   not ask a citation for an item's `let t : D → E` line, so the build
   proves each term's membership itself. For B's values it now uses
   `bpolycl`, as it uses `bccl` for C.

5. **The reader's direction of telescoping is an item.** The library's
   `sum-telescopes` takes each term less the next. The argument here takes
   each value less the one before, set.mm's `telfsum2`, and stating it as
   the reader does keeps signs out of the proof.
