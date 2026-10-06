# Pilot: ℚ is countable

Theorem 20 of `SELECTION.md`, set.mm's `qnnen`, Wiedijk #3:

  there is a bijection from ℕ to ℚ.

Hammack's Theorem 14.4 (§14.2, p. 276 of edition 3.4) puts the fractions in
lowest terms in a grid, a column for each numerator, and snakes a path
through it; that is a picture of a list, not a function a proof can name,
and was not taken as the source. The proof is the one `SELECTION.md`
planned: inject ℕ into ℚ, inject ℚ into ℕ, and cite Schröder–Bernstein,
which the corpus proves. ProofWiki's second proof is the nearest: it
injects ℚ by lowest terms into ℤ × ℕ, where this one goes on into ℕ by
powers of primes.

---

## Theorem rationals-countable

The proof is `proofs/rationals-countable.proof`, one theorem with three
defines. It elaborates to
`corpus/elaboration/proofs/rationals-countable/rationals-countable.mm`,
assumes nothing, and verifies. Its statement in set.mm is `NN ~~ QQ`.

Numbers: 10 numbered steps at the top and 39 inside blocks. Steps 1 to 4
show f(n) = n is one-to-one from ℕ into ℚ; 5 says the numerator is its size
with its sign; 6 and 7 that g maps ℚ into ℕ; 8 and 9 that g is one-to-one;
10 cites Schröder–Bernstein.

---

## Rendered view

**Theorem.** There is a bijection from ℕ to ℚ.

*Proof.* The map f(n) = n sends ℕ into ℚ and is one-to-one.

For x ∈ ℚ write x = p/q in lowest terms with q > 0, let s(x) be 0 if p ≥ 0
and 1 otherwise, and let g(x) = 2^|p|·3^q·5^s(x), a natural number. Since
p = (1 − 2s(x))·|p|, the numbers |p|, q and s(x) determine x. If g(x) = g(y),
unique factorisation gives that x and y have the same |p|, q and sign, so
x = y: g is one-to-one from ℚ into ℕ.

By the Schröder–Bernstein theorem there is a bijection from ℕ to ℚ. ∎

---

## Decisions made with the reader

1. **The injection is by powers of primes.** x = p/q goes to 2^|p|·3^q·5^s,
   s recording the sign, rather than to the pair (p, q): `(p, q)` already
   reads as the open interval, and a pair would need a rule telling the two
   apart by context.
2. **numer and denom, set.mm's names, are library functions.** A define
   needs a rule in x, so "write x = p/q in lowest terms" cannot be obtained
   inside it. They are mundane definitions that state only what they build,
   as cos and sin do; `lowest-terms-parts` says the numerator is an integer,
   the denominator a natural number, and x their quotient.
3. **Unique factorisation is a named theorem,** `prime-powers-unique`: the
   exponents of 2, 3 and 5 in 2^a·3^b·5^c are a, b and c. A reader cites it
   as the fundamental theorem of arithmetic.
4. **The sign is read back by a formula,** p = (1 − 2s)·|p|, proved once for
   every x by cases, so that the injectivity argument is one calculation
   rather than four cases.

---

## What the pilot reveals

1. **A function applied had no sort.** `|cos(x)|` read as an absolute value
   or as the size of a set, since application yields whatever its function
   maps to and the parser kept that as any sort. It now takes the sort the
   function's own sort gives, so `|numer(x)|` is an absolute value.
2. **A define by cases is decided by the condition or its negation as
   written.** `numer(x) < 0` does not decide the case `numer(x) ≥ 0` fails,
   so the split is excluded middle, "≥ 0 or not ≥ 0", as Schröder–Bernstein
   splits on t ∈ C.
3. **Three gaps in `membership`.** ℤ, ℚ, ℝ and ℂ were not known to be sets
   (`zex`, `qex`, `reex`, `cnex`), so a map on ℚ could not be shown to be
   one; a power of a natural number was not known to be natural
   (`nnexpcld`); and a value by cases was not built from its cases
   (`ifcld`). Each was a table entry or a branch beside the others like it.
4. **`algebra` needs names.** With s(x) and |numer(x)| in a claim it cannot
   put the cited values in, and its search for their memberships runs on.
   The values are substituted first, so `algebra` sees only numer(x), as the
   mean value theorem found.
5. **A lemma letter only the hypotheses hold needs a `with` here too.** In
   each of the three targets four of the six exponents appear only in the
   hypotheses, so the record names all six.
6. **A Metamath comment is ASCII.** A `·` in the header of the new
   `proved.mm` block crashed the verifier's report, as σ did in a label.

---

## Status

Checker clean, elaborated with nothing assumed, verified.
