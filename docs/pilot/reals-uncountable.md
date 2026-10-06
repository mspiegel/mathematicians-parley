# Pilot: ℝ is uncountable

Theorem 27 of `SELECTION.md`, Wiedijk #22:

  there is no bijection from ℕ to ℝ.

set.mm's `ruc` says ℕ ≺ ℝ, which also says ℕ is no larger than ℝ, and
proves it by nesting closed intervals, each avoiding the next term of the
sequence (`ruclem1` to `ruclem13`). The proof here is Cantor's diagonal
argument in decimals instead. ProofWiki's "Real Numbers are Uncountable"
gives it, and was checked for this pilot: it takes the n-th digit of the
n-th number plus one modulo 10, as here, and works in [0, 1) with the
decimals ending in endless 9s left out, so that each number has one
expansion. Here the digits are read off any real, and the number made from
the new digits may have d(n) + 1 in a place where d(n) was asked, as
0.4999… = 0.5 does; adding one twice is not the old digit either, so the
argument goes through without leaving anything out.

---

## Theorems

The proof is `proofs/reals-uncountable.proof`, seven theorems of 42
numbered steps, 194 with those inside blocks, and four defines. All seven
elaborate to `corpus/elaboration/proofs/reals-uncountable/`, assume nothing,
and verify.

- `digit-range`: 0 ≤ s(t) ≤ 9 for t ∈ ℤ, where s(t) = (t + 1) mod 10.
- `digit-step-divides`: 10 divides (t + 1) − s(t).
- `digit-step`: s(t) ≠ t.
- `digit-step-twice`: s(s(t)) ≠ t.
- `decimal-number`: digits d(1), d(2), … from 0 to 9 make a real x whose
  n-th digit D(x, n) is d(n) or s(d(n)).
- `sequence-misses-real`: for f : ℕ → ℝ there is x ∈ ℝ that no f(n) is,
  set.mm's `ruclem12`.
- `reals-uncountable`: there is no bijection from ℕ to ℝ.

---

## Rendered view

D(r, n) = ⌊10ⁿr⌋ mod 10 is the n-th digit of r after the decimal point, and
s(a) = (a + 1) mod 10 is the digit after a, so s(9) = 0.

**Lemma (digit-range, digit-step-divides, digit-step, digit-step-twice).**
For t ∈ ℤ, 0 ≤ s(t) ≤ 9, and s(t) ≠ t and s(s(t)) ≠ t.

*Proof.* s(t) is a remainder on division by 10, so 0 ≤ s(t) < 10. And
t + 1 ≡ s(t) (mod 10), so 10 divides (t + 1) − s(t). If s(t) = t, 10 divides
1. Applying the same to s(t), 10 divides (s(t) + 1) − s(s(t)); if
s(s(t)) = t, adding the two gives that 10 divides 2. ∎

**Lemma (decimal-number).** Let d : ℕ → ℤ with 0 ≤ d(n) ≤ 9 for all n.
Then there is a real x with D(x, n) = d(n) or D(x, n) = s(d(n)) for all n.

*Proof.* Let N(0) = 0 and N(k + 1) = 10·N(k) + d(k + 1), the whole number
with digits d(1) … d(k), so N(k)/10ᵏ is the decimal cut off after k digits.
Each cut-off is at most the next, and (N(k) + 1)/10ᵏ is at least the next
one's, so every cut-off lies below every (N(k) + 1)/10ᵏ. The cut-offs are
bounded, so they have a least upper bound c, and
N(n)/10ⁿ ≤ c ≤ (N(n) + 1)/10ⁿ. Then N(n) ≤ 10ⁿc ≤ N(n) + 1, so ⌊10ⁿc⌋ is
N(n) or N(n) + 1, which end in the digits d(n) and s(d(n)). ∎

**Lemma (sequence-misses-real).** For f : ℕ → ℝ there is x ∈ ℝ with
f(n) ≠ x for every n.

*Proof.* Let e(n) = s(D(f(n), n)), a digit. By decimal-number there is x
whose n-th digit is e(n) or s(e(n)), and neither is D(f(n), n) by the first
lemma. So x and f(n) differ in their n-th digit. ∎

**Theorem (reals-uncountable).** There is no bijection from ℕ to ℝ.

*Proof.* Suppose there is one. Then there is f : ℕ → ℝ reaching every
real. The real x the last lemma gives is f(m) for some m, and f(m) ≠ x. ∎

---

## Decisions made with the reader

1. **The digit step is three theorems.** `digit-step` first said s(t) ∈ ℤ,
   its bounds, and s(t) ≠ t. The reader asked whether s(t) ∈ ℤ could be
   left out of the statement, and chose to make `membership` build a
   remainder, so that each caller writes it in one line, by
   `membership, from D2`. The reader then asked for the bounds and the
   inequality apart, and chose the cut at `digit-step-divides`, which
   `digit-step` and `digit-step-twice` both cite; `digit-step-twice` went
   from 11 steps to 4.

---

## What the pilot reveals

1. **Numerals of any length.** A sum, product or order of whole numbers is
   worked from set.mm's digit tables, the last digit first with a carry,
   and a decimal on the page is read as its value; 10 − 1 = 9 is
   `arithmetic`'s, and the record that stated it went.
2. **A recursion's rule at k + 1 may name k**, as N(k + 1) does.
3. **Floor and remainder.** A notation ⌊x⌋ with `floor-integer`,
   `floor-below` and `floor-above`; `mod-remainder`, `mod-multiple`,
   `divide-le`, `le-antisymmetric` and `divides-sum` in the library.
4. **A theorem of the same file stated over the file's defines** is cited
   without citing them (`SYNTAX.md`), and a domain the define gives is
   still written where the step applies it to a term it builds.
5. **`membership` reads a cited equation** (a(0) = 0 says a(0) is real),
   reads its claim with defined names written out, and builds a remainder:
   a mod b is in ℕ₀ when a ∈ ℤ and b ∈ ℕ (`zmodcl`), beside the binomial
   coefficient in the table `WHOLE`, which `algebra` and `inequalities`
   read as well.
6. **`join` takes a cited line apart.** It matched a cited line only where
   the claim grouped its sentences the same way, which METHODS.md never
   said; each sentence of a cited conjunction is now supplied
   (`simpld`, `simprd`).
7. **A function is obtained from "there is f : X → Y with …"**, a new
   binder over the functions from X to Y (set.mm's Y ↑m X), as "there is a
   polynomial q with …" is over the polynomials. f : X → Y is then a sort,
   as an obtained point is, and a step asking it has it by `elmapi`. The
   way back from a bijection is the new item `bijection-onto`, proved in
   `proved.mm` as `gbijonto`; DATABASE.md had recorded the missing binder as
   the gap. A first version of `gbijonto` discharged f from a formula that
   binds it, and the verifier refused it; the existential is now carried
   whole and turned into the bounded one by `df-rex`.
8. **The checker and the elaborator spell a define-bearing answer alike**,
   so `tests/agree.rs` compares one fact as one.
9. **The first version nested intervals**, as `ruc` does, cutting each in
   thirds to miss the next term and closing on the least upper bound of
   the left ends. The diagonal argument replaced it.
