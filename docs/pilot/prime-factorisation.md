# Pilot: every number is a product of primes

Wiedijk #80, the fundamental theorem of arithmetic, existence half only;
set.mm's `1arith2` states both halves through prime counts:

  every n ≥ 2 is a product of primes.

Strong induction, written as an ordinary induction on a bound: n has a
prime factor p, n/p is smaller, and a factorisation of n/p gains p as one
more factor. Uniqueness needs a language change and is not attempted.

---

## Theorem prime-factorisation

The proof is `proofs/wiedijk/prime-factorisation.proof`. It elaborates to
`corpus/elaboration/proofs/wiedijk/prime-factorisation/prime-factorisation.mm`,
which assumes nothing and verifies.

---

## Rendered view

**Theorem.** Let n ∈ ℕ with n ≥ 2. There is k ∈ ℕ and f : {1, …, k} → ℕ
with n = ∏(i ∈ {1, …, k}) f(i) and every f(i) prime.

*Proof.* By induction on N ∈ ℕ, every m ∈ {2, …, N} is such a product. For
N = 1 there is no such m. Let m ∈ {2, …, N + 1}.

1. m has a prime factor p, and r = m/p is a positive integer with m = p·r.
2. Since p > 1, m − r = (p − 1)·r > 0, so r < m ≤ N + 1, and r ≤ N.
3. If r = 1, m = p, and the list holding p alone is a factorisation.
4. Otherwise r ∈ {2, …, N}, so r = ∏(i ∈ {1, …, j}) g(i) with every g(i)
   prime. Let h(i) = g(i) for i ≤ j and h(j + 1) = p.
5. Every h(i) is prime, h agrees with g on {1, …, j}, and
   ∏(i ∈ {1, …, j + 1}) h(i) = r·p = m.

Taking N = n gives the theorem. ∎

---

## Database items

In `corpus/stdlib/sums.records`: `product-termwise` (`prodeq2dv`), two
products over one range equal where their factors are. Its functions are
typed over sets the citation leaves free, since the extended list is
defined beyond the range it is compared on.

---

## What the pilot reveals

1. **Strong induction is ordinary induction on a bound.** The claim at N is
   said of every m ∈ {2, …, N}. The base runs over the empty range
   {2, …, 1}, and its block ends on the contradiction its range's bounds
   give. Closing the induction rewrites the set a "for all" runs over, which
   the elaborator did by position and now does by name
   (`an-induction-over-a-range-it-ends`).
2. **A list is a function on {1, …, k}, and one more place is a define by
   cases.** h(i) = g(i) if i ≤ j, p otherwise, on {1, …, j + 1}:
   `product-extended` takes the last factor off, and `product-termwise`
   says the rest are g's. The record does not type its functions over the
   range, which h is not.
3. **A function is exhibited by its type.** "there is f : X → Y with …"
   runs over the functions from X to Y, and the exhibited h is shown a
   member of them from h : {1, …, j + 1} → ℕ (`elmapg`). That path exposed
   an `mpbird` taking its letters in the wrong order, which no proof had
   reached (`a-function-exhibited-by-its-type`).
4. **A define's type is said once, and a lemma's own hypotheses now see
   it.** e(i) = p on {1, …, 1} is a function into ℝ because p is a number.
   `product-single` asks e(1) ∈ ℂ, which the build now reads from the type
   the citation proves where the define's line is in hand
   (`a-product-of-a-define-said-once`). A product's factor is carried under
   its index as a sum's term was.
5. **Two types for one function.** h is typed into ℕ for the claim and into
   ℝ for `product-extended`: a type into ℕ is not read as one into ℝ, so
   each is a step citing `function-into`. Each also needs a case split of
   its own, since `prime-nat` asks the value to be an integer first.
6. **The checker took a define's requires line on trust.** A requires line
   naming a define was accepted whatever it claimed; it now reads only "is
   a function on" apart, as the build does.
7. **The statement's order matters.** "with for all i, f(i) is prime, and
   n = ∏ …" reads the "for all" over both clauses, so the theorem says the
   product first.
