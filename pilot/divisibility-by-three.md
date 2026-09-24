# Pilot: divisibility by 3

Eleventh pilot, the first of the five chosen for what the first ten did not
exercise (`SELECTION.md`, "The next five"). Number 85 on Wiedijk's list,
`3dvds` in set.mm (122 essential steps). Its purpose is congruence, and a
sum whose terms a function gives.

The theorem: for any integers d(0), …, d(n), 3 divides
Σ(k = 0 to n) d(k)·10^k exactly when it divides Σ(k = 0 to n) d(k). A
reader's decimal digits are the case where each d(k) is between 0 and 9.

The informal source is ProofWiki's "Divisibility by 3", whose one proof shows
the number and its digit sum congruent modulo 9 — 10 ≡ 1 (mod 9) — and then
modulo 3, a divisor of 9. Hammack's Book of Proof (third edition) does not
state the rule; it defines congruence (Definition 5.1, §5.2: "a and b are
congruent modulo n if n | (a − b)"), and its induction chapter asks for
3 | (5²ⁿ − 1), the shape of this pilot's lemma.

---

## Theorems ten-power-congruent and divisibility-by-three

The skeleton is `proof/divisibility-by-three.proof`. `ten-power-congruent`
says 10^k ≡ 1 (mod 3) for every k ∈ ℕ₀, by induction from 0, since
10^(k + 1) − 1 = (10^k − 1)·10 + (10 − 1). `divisibility-by-three` then
shows each term d(k)·10^k − d(k) divisible by 3, so the sum of them, which
is the number less its digit sum, so the two are congruent, so divisible
together.

---

## Database items

This pilot introduced, in the database, `def:stdlib/divisibility/congruent-mod`,
`thm:stdlib/divisibility/divides-multiple`, `thm:stdlib/divisibility/congruent-divides`, `thm:stdlib/numbers/power-integer`,
`thm:stdlib/numbers/ten-minus-one`, `thm:stdlib/sums/sum-divisible`, `thm:stdlib/sums/sum-integer`,
`thm:stdlib/sums/sum-difference`, `thm:proof/divisibility-by-three/ten-power-congruent` and
`thm:proof/divisibility-by-three/divisibility-by-three`, and widened `thm:stdlib/functions/function-value` from functions
into ℝ to functions into any set. In `db/notation.records` it added `sum` and
`congruent-mod`, and a precedence level, `summation`.

---

## What the pilot reveals

1. **Σ is a notation, where every sum before it was a definition.** The
   arithmetic and geometric series define S(n) and G(n) by recursion,
   because "1 + 2 + ... + n" has no formula behind the dots. Σ has one: its
   target is set.mm's sum over the whole numbers from one bound to the
   other, so nothing is hidden, and the proof is the textbook's direct one
   rather than an induction the recursion would have forced. It is written
   on one line, `Σ(k = 0 to n) t`, because the notation grammar's `_` is
   its hole marker and `Σ_{k=0}^{n}` cannot be a pattern; and it binds
   tighter than + and −, so a sum less a sum needs no brackets and a sum of
   a difference writes its own.
2. **Congruence is divisibility, and the kernel says so.** `a ≡ b (mod n)`
   is a notation whose target is n ∣ (a − b), Hammack's definition, so a
   congruence and the divisibility it abbreviates are one formula and every
   lemma about the one is about the other. `def:stdlib/divisibility/congruent-mod` is still an
   item, with no target, so that a step can say which way it is reading:
   its two sides are one kernel formula, and unfolding it hands on the
   cited line's own proof.
3. **The digits are any integers.** set.mm's `3dvds` takes a function into
   ℤ, and so does the pilot: `let d : ℕ₀ → ℤ`. The restriction to 0–9
   plays no part in the proof, and writing it would need a notation for the
   whole numbers from 0 to 9 that nothing else wants.
4. **An item's summand is read where the sum applies it.** `sum-divisible`
   and `sum-difference` speak of any term t(k). The checker already bound a
   property P at the one place a binder applies it to what it binds; it now
   does the same for a function t, binding it to the step's summand with k
   as the hole, except where that summand is itself a function applied to
   k, where t is simply that function. Hypotheses are matched with the same
   binding sites as conclusions, which they were not.
5. **"Every term" is asked of every k ∈ ℕ₀.** set.mm asks it only of the k
   the sum takes, but a `fix` introduces k by `let k ∈ ℕ₀`, and there is no
   introduction for a whole number between two bounds. So `sum-divisible`
   asks more than `fsumdvds` does, and the elaborator reads the cited
   universal at the index (`at_the_index`, `rspcv`), once k is in ℕ₀ by
   `elfznn0`.
6. **10 is the first number past a digit.** set.mm writes it as the decimal
   `; 1 0`. The methods read a digit as its value and anything longer as a
   number they know nothing about, so what depends on 10 being ten is
   cited: `thm:stdlib/numbers/ten-minus-one`, and the step case is arranged so that
   `algebra` never needs the value — (10^m − 1)·10 + (10 − 1)·1 is
   10^m·10 − 1 whatever 10 is. A decimal's membership of a number system is
   built from its digits (`decimal_within`), not searched for.
7. **`arithmetic` states nothing.** Elaborating this pilot found a false
   `arithmetic` claim of digits alone crashing the normaliser, and, with
   that fixed, being stated as an axiom, as a false claim with 10 in it
   already was. `arithmetic` now works a closed claim out exactly first
   (`field.decide_closed`), refusing a division by zero, a number too large
   to work out and a power that is not rational, and reports what it cannot
   prove rather than stating it. METHODS.md records the rule.
8. **The proof is not ProofWiki's.** ProofWiki goes through 9 and down to 3;
   the pilot works modulo 3 throughout, with the lemma 10^k ≡ 1 (mod 3)
   proved by induction. The kernel proof is not set.mm's either: `3dvds`
   is not cited, as `arisum` is not for the arithmetic series.

Numbers, for the record: 34 numbered steps, 19 in `ten-power-congruent` and
15 in `divisibility-by-three`, and 37 requires lines, 23 of them in the
lemma, most of them integer memberships that `def:stdlib/divisibility/divides` and
`def:stdlib/divisibility/congruent-mod` ask. set.mm's `3dvds` has 122 essential steps.
