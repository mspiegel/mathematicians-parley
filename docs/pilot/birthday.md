# Pilot: the birthday problem

Theorem 31 of `SELECTION.md`, set.mm's `birthday`, Wiedijk #93:

  of the functions from 23 people to 365 days, fewer than half are
  one-to-one: among 23 people, the chance that no two share a birthday is
  below 1/2.

The argument is ProofWiki's, with the arithmetic it leaves out done: the
one-to-one functions number 365·364·…·343, all the functions 365^23, and
twice the first is less than the second. set.mm argues otherwise, bounding
each factor by e^(−k/365) and comparing with log 2 (`log2ub`); the reader
chose the count.

---

## Theorem

The proof is `proofs/birthday.proof`, one theorem of 17 steps. It elaborates
to `corpus/elaboration/proofs/birthday/`, assumes nothing, and verifies. Its
statement is set.mm's: S, the functions from {1, …, 23} to {1, …, 365}, and
T, those of them that are one-to-one, are defines in its header, and the
theorem is |T|/|S| < 1/2.

The library gains `count-functions`, |the functions from X to Y| = |Y|^|X|
(`hashmap`), `count-one-to-one`, the one-to-one ones counted as
∏(k ∈ {0, …, |X| − 1}) (|Y| − k) (`hashf1`, `bcfallfac`, `fallfacval`), and
the mundane `range-size`, |{1, …, n}| = n (`hashfz1`).

---

## Rendered view

**Theorem (birthday).** Let S be the functions from {1, …, 23} to
{1, …, 365}, and T those of them that are one-to-one. Then |T|/|S| < 1/2.

*Proof.* {1, …, 23} and {1, …, 365} are finite, of 23 and 365 elements. So
|S| = 365^23, and since 23 ≤ 365, |T| = ∏(k ∈ {0, …, 22}) (365 − k). Working
the product out, 2·∏(k ∈ {0, …, 22}) (365 − k) < 365^23, so
|T|/|S| = (∏(k ∈ {0, …, 22}) (365 − k))/365^23 < 1/2. ∎

---

## Decisions made with the reader

1. **ProofWiki's argument, its arithmetic done,** rather than set.mm's bound
   by e^(−k/365): no exponential or logarithm on the page. The comparison
   needs the factor of 2, and no simpler bound reaches it; 1 − x ≤ e^(−x)
   clears 1/2 by four parts in a million.
2. **set.mm's statement:** the ratio of two counts, with S and T named in
   the header.
3. **The count of one-to-one functions as a product,**
   ∏(k ∈ {0, …, |X| − 1}) (|Y| − k), the textbook's n(n − 1)…(n − m + 1);
   23!·C(365, 23), set.mm's count, stays in the bridge.
4. **The product written with ∏,** not as 23 factors.
5. **2·∏ < 365^23 as its own line,** and the fraction from it after, which
   the reader finds easier to follow than the fraction alone.
6. **|{1, …, n}| = n is mundane,** a dull fact a reader takes as read.

---

## What the pilot reveals

1. **`arithmetic` at size.** It held numbers as machine integers; it now
   works whole numbers of any length, a product over a range of numerals, a
   difference that stays whole, and an order between fractions by their
   cross products, and decides a false claim about a product as false.
   `tests/elaborator/large-arithmetic.proof` writes each shape.
2. **`inequalities` and the normaliser at size.** Both spelt coefficients
   from 32-bit integers, which past four billion were wrong; they hold them
   as big integers now, and `inequalities` reads a whole power of a numeral
   as a number, so it scales by 365^23.
3. **Faults met in the proof and fixed in the tools:** the checker called
   |{1, …, 23}| ≤ |{1, …, 365}| a claim of numerals alone, whose size
   arithmetic cannot work out; `substitute` could change a product's range
   but not its term, which sums could; and a closed product's membership of
   ℝ was not arithmetic's.
4. **The proof is large,** 627 KB: the 59-digit products are proved digit
   by digit, and the compressed format writes each once, wherever step 13
   compares them and step 16 scales by 365^23. The normaliser cancels a
   number common to a numerator and a denominator before multiplying out
   (`gdivcanx`), as a page would; multiplied out, step 16 alone was 1.5 MB
   of products of 119 digits.
