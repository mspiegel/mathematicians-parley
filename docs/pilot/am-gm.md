# Pilot: the arithmetic and geometric means

Theorem 43 of `SELECTION.md`, Wiedijk #38:

  if n numbers are none of them negative, their geometric mean is at most
  their arithmetic mean.

set.mm's `amgm` states it for a finite set, with the product and the sum
written as group sums. It proves it through Jensen's inequality for the
logarithm (`amgmlem`, `jensen`, `logccv`). It is not cited. The proof here
is the one a first course gives without convexity. By induction on the
number of terms, the product is at most the mean to the n-th power. Each
step is one use of Bernoulli's inequality. Taking n-th roots then gives
the theorem.

---

## Theorems

The proof is `proofs/wiedijk/am-gm.proof`, three theorems:

- `first-terms` (4 numbered steps, 6 with those inside blocks): what is
  said of every a(k) for k up to n is said of every a(k) for k up to any
  m ≤ n.
- `am-gm-power` (4 steps, 49 with those inside blocks): ∏ a(k) ≤
  ((Σ a(k))/n)^n.
- `am-gm` (7 steps, 11 with those inside blocks): the theorem.

Each elaborates to `corpus/elaboration/proofs/wiedijk/am-gm/`, assumes
nothing, and verifies.

---

## Rendered view

**Lemma (first-terms).** Let n ∈ ℕ, a : {1, …, n} → ℝ with a(k) ≥ 0 for
every k, and m ≤ n. Then a(k) ∈ ℝ and a(k) ≥ 0 for every k ∈ {1, …, m}.

*Proof.* {1, …, m} ⊆ {1, …, n}. ∎

**Lemma (am-gm-power).** Let n ∈ ℕ and a : {1, …, n} → ℝ with a(k) ≥ 0 for
every k. Then

  ∏(k = 1 to n) a(k) ≤ ((Σ(k = 1 to n) a(k))/n)^n.

*Proof.* We show, by induction on j ≥ 1, that if j ≤ n then
∏(k = 1 to j) a(k) ≤ ((Σ(k = 1 to j) a(k))/j)^j. Then we take j = n.

1. j = 1: both sides are a(1).
2. From j to j + 1, where j + 1 ≤ n. Let x = a(j + 1), let A be the mean
   of the first j terms, and let B be the mean of the first j + 1. Then
   B·(j + 1) = A·j + x. By the hypothesis and x ≥ 0,

     ∏(k = 1 to j + 1) a(k) = (∏(k = 1 to j) a(k))·x ≤ A^j·x.

   A ≥ 0 and B ≥ 0, since no term is negative. It remains to show
   A^j·x ≤ B^(j + 1).
   - If A > 0, let r = B/A. Then r ≥ 0, so r − 1 ≥ −1, and Bernoulli's
     inequality gives 1 + (r − 1)(j + 1) ≤ r^(j + 1). Multiply both sides
     by A^(j + 1) > 0. On the left, A·(1 + (r − 1)(j + 1)) =
     A + (B − A)(j + 1) = x, so the left side is A^j·x. On the right,
     A^(j + 1)·r^(j + 1) = (A·r)^(j + 1) = B^(j + 1).
   - If A = 0, then A^j·x = 0 ≤ B^(j + 1). ∎

**Theorem (AM–GM).** Let n ∈ ℕ and a : {1, …, n} → ℝ with a(k) ≥ 0 for
every k. Then

  (∏(k = 1 to n) a(k))^(1/n) ≤ (Σ(k = 1 to n) a(k))/n.

*Proof.* Let P be the product and M the mean. P ≤ M^n by the lemma, and
P ≥ 0 and M ≥ 0. Let r = P^(1/n), a real number since P ≥ 0, with
r^n = P. If r > M, then M^n < r^n = P, which contradicts P ≤ M^n. So
r ≤ M. ∎

---

## Decisions made with the reader

1. **The power form first, then the roots.** The induction proves
   ∏ ≤ M^n, which needs no roots. The n-th root is taken only once, at the
   end. The root step is a contradiction: if r > M, then M^n < r^n, since
   for numbers that are not negative a larger number has a larger n-th
   power (`power-less`).
2. **Bernoulli's inequality, not Cauchy's induction or convexity.**
   Cauchy's argument goes up through powers of 2 and back down. set.mm's
   argument needs the logarithm to be concave. The Bernoulli step is one
   ordinary induction, and each step names one inequality, at r = B/A.
3. **The geometric mean is a real power.** The statement writes
   (∏ a(k))^(1/n), as set.mm's `amgm` does. The exponent 1/n is not a whole
   number, so the power is read as a real power. `real-power-real` gives
   r ∈ ℝ, and `root-power` gives r^n = P.
4. **The induction runs over j ≤ n.** a is given on {1, …, n} only. So
   the claim is "if j ≤ n then …" for every j ∈ ℕ, and `modus-ponens`
   takes off the condition each time it is used. `first-terms` says, in
   one place, that the first m values are real and not negative. Each
   step that needs this for m = 1, j or j + 1 cites it.
5. **A = 0 is a case of its own.** Bernoulli is applied at B/A, which
   needs A ≠ 0. When A = 0, both sides are worked out instead.
6. **A, B, x and r are names.** Each is a naming `let`, "a real number",
   with the lines that make it one, and a `reads` line saying what it is.
   This keeps the step's algebra at the size a reader writes it.

---

## Database items

In `corpus/stdlib/numbers.records`: `bernoulli-inequality` (`bernneq`),
named. Each of these is mundane: `multiply-le-nonneg` (`lemul1a`),
`power-nonneg` (`expge0`), `zero-power` (`0exp`) and `power-less`
(`expmordi`). In `corpus/stdlib/sums.records`, mundane:
`product-range-nonneg` (`fprodge0`, through `gfprodge0` in `proved.mm`,
from `corpus/proved/ranges.proved`). `fprodge0` asks that k is not free in
the context, and `gfprodge0` gives this by `nfv`.

The proof also cites `real-power-real` (`recxpcl`) and `root-power`
(`cxproot`), which the real powers added (c7021c1f). It also cites
`range-within`, which the Erdős–Szekeres pilot added. `integral-point` in
`calculus.records` now takes f on any set X, not only on ℝ.
fundamental-calculus cites it with f given on [a, b], and the check in
point 1 below asks about exactly that.

---

## What the pilot reveals

1. **A function's type does not give its values outside its domain.**
   `product-real` at b := j asks t : {1, …, j} → ℝ. The checker took a's
   type, a : {1, …, n} → ℝ, as the answer, and the build refused it. The
   checker now asks for a line that gives the values on the range the item
   is cited over, such as `for all k ∈ {1, …, j}, a(k) ∈ ℝ`. This is why
   `first-terms` exists. (`tests/elaborator/a-function-on-a-longer-range`;
   planted case "cite an item over a range a declared function's domain
   does not hold".)
2. **`inequalities` drops identity elements from its claim.** The base
   case claims ∏ ≤ ((Σ)/1)^1, and its rows end on ∏ ≤ Σ. The method now
   proves a claim written with /1 or ^1 as the same claim without them
   (`an-order-claimed-with-an-identity`).
3. **A naming let's reason may be the lines it cites.** `let x = a(j + 1),
   a real number` gives `from H2, 1.2.5`, the type of a and a point of its
   domain, as a requires line would (`a-named-value-of-a-function`).
4. **Real powers and n-th roots.** P^(1/n) is read as a real power, since
   1/n is not a whole number. Every other power reads as before
   (c7021c1f, `tests/notations/powers.proof`).
5. **A product over a range is written as a sum is.** The page writes
   ∏(k = 1 to n). `product-single`, `product-extended`, `product-real` and
   `product-range-nonneg` are stated over {a, …, b}, and a product written
   either way is compared in the range form (b81883e1).
6. **A subset line's members are read at a block's letter.** Inside a
   block that lets k ∈ {1, …, m}, line 1, {1, …, m} ⊆ {1, …, n}, says
   k ∈ {1, …, n}, just as a written "for all x ∈ A, x ∈ B" would.
   `first-terms`' two blocks cite line 1 directly, and no step restates
   the subset as a "for all" (`SYNTAX.md`, What a cited line says).
7. **`instantiate` takes t ∈ X from what its from-lines supply.** Step 3.1
   instantiates H3 at k, `from 1`. Line 1 supplies k ∈ {1, …, n} at the
   block's letter.

Numbers, for the record: 15 numbered steps at the left margin, 66 with
those inside blocks, over three theorems, and 11 requires lines.
