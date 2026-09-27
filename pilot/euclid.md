# Pilot: Euclid's algorithm

Theorem 16 of `SELECTION.md`, set.mm's `eucalg`, Wiedijk #69:

  start with the pair M, N; while the second number is not 0, replace the
  pair a, b by b, a mod b. After N steps the first number is gcd(M, N).

The proof is ProofWiki's, checked against it before the pilot: the
remainder is less than the divisor, gcd(a, b) = gcd(b, a mod b), and
gcd(r, 0) = r. Its termination argument, a strictly falling sequence of
remainders, is part 3 here, said as a bound one induction can carry.

---

## Theorem euclid

The proof is `proof/euclid.proof`, one theorem. It elaborates to
`elaboration/proof/euclid/euclid.mm`, assumes nothing, and verifies.

Numbers: 81 numbered steps, 13 of them at the top. Steps 1 and 2 are the
start, 3 to 5 are the three inductions, and 6 to 13 put them together at
k = N.

---

## Rendered view

Let M, N ∈ ℕ₀, and define two sequences by a(0) = M, b(0) = N and, for
each k ∈ ℕ₀,

  a(k + 1) = a(k) if b(k) = 0, and b(k) otherwise;
  b(k + 1) = 0 if b(k) = 0, and a(k) mod b(k) otherwise.

**Theorem.** a(N) = gcd(M, N).

*Proof.* Three things hold for every k, each by induction on k, each step
split on whether b(k) is 0.

1. a(k) and b(k) are in ℕ₀. At 0 they are M and N. Where b(k) = 0 the next
   pair is a(k), 0; otherwise it is b(k), a(k) mod b(k), and a remainder on
   dividing by a natural number is in ℕ₀.
2. gcd(a(k), b(k)) = gcd(M, N). Where b(k) = 0 nothing changes. Otherwise
   gcd(b(k), a(k) mod b(k)) = gcd(a(k) mod b(k), b(k)) = gcd(a(k), b(k)).
3. b(k) + k ≤ N, or b(k) = 0. At 0, b(0) = N. Where b(k) = 0 so is
   b(k + 1). Otherwise b(k + 1) = a(k) mod b(k) < b(k), so b(k + 1) + 1 ≤
   b(k) between whole numbers, and b(k + 1) + (k + 1) ≤ b(k) + k ≤ N.

At k = N, the third says b(N) + N ≤ N or b(N) = 0, and b(N) ≥ 1 would make
the first impossible; so b(N) = 0. Then a(N) = gcd(a(N), 0) = gcd(a(N),
b(N)) = gcd(M, N) by the second. ∎

---

## Decisions made with the reader

1. **Two sequences side by side, as the textbook writes them.** set.mm
   steps through pairs and reads them with `1st` and `2nd`; the page does
   not. One define gives both names, each with a value at 0 and a rule at
   k + 1, and the pairs are the elaborator's (`ELABORATION.md`, sequences
   defined by recursion).
2. **The define is in the statement,** between the `let` lines and `then`,
   as a textbook says "let M, N ∈ ℕ₀ and define …; then …". The theorem is
   about the sequences, so its statement names them.
3. **The claim is `eucalg`'s: a(N) = gcd(M, N).** It says the algorithm has
   finished by step N, which part 3 is for.
4. **The cases test b(k) = 0 first,** as set.mm's `if` and ProofWiki's
   "if b = 0 the task is complete" do. A line saying b(k) = 0 then takes
   the first case and one saying b(k) ≠ 0 the second, each read directly.
5. **Part 3 is a disjunction,** "b(k) + k ≤ N or b(k) = 0", rather than
   b(k) ≤ N − k, which goes below zero once the algorithm has stopped. Its
   base and step introduce the "or" by `or-left` and `or-right`, two
   reasoning items added for it.

---

## What the pilot reveals

1. **A proof can define sequences by recursion.** `parse.Recursion` reads
   the define; the checker never unfolds a sequence into its rule, reads a
   citation of D1 as one of its equations, and rejects a rule naming a
   value other than at k, or k itself (`check_recursions`). The elaborator
   writes one set.mm recursion over a state (`recursion_terms`) and reads
   a citation at 0 or at J + 1 through `algr0` and `algrp1`
   (`recursion_value`). One rule serves one sequence and several:
   `tests/elaborator/recursion.proof` defines c(k + 1) := 2·c(k) and cites
   both rules.
2. **A cited conjunction supplies each part.** A line of two sentences
   always did; `a(j) ∈ ℕ₀ and b(j) ∈ ℕ₀`, written as one formula because
   an induction carries one formula, now does too, in the checker
   (`with_parts`), in a substitution, and in what a `requires` line cites.
3. **A hypothesis line can be substituted into,** as the checker already
   allowed: `substitute a(0) = M (line 1) into H1`.
4. **`a mod b` is a notation,** beside the congruence's `(mod m)`.
5. **A calculation link cites the line that says it.** The first draft
   wrote `gcd(a(0), b(0)) = gcd(M, b(0))` citing `a(0) = M`, a substitution
   inside a term, which `SYNTAX.md` does not allow a link and the
   elaborator refused. The checker had read only a link's form, so it
   passed; it now reads each link against the line it cites
   (`check_chain_links`), and the draft's link is a planted defect.
6. **set.mm says a numeral is a set only for 0 to 3** (`c0ex` to `3ex`) and
   for a decimal numeral (`decex`); a recursion starting at 4 would stop at
   "cannot settle 4 ∈ V".

---

## Status

Checker clean, elaborated with nothing assumed, verified. Planted checker
defects: a name with no value at 0, a first value at 1, a rule naming the
value it defines, a rule naming the index itself, a first value naming a
sequence, a step cited without its index in ℕ₀, the other case's value
claimed, a case not said, and a recursion outside any theorem.
