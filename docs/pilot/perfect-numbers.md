# Pilot: perfect numbers

Theorem 17 of `SELECTION.md`, Euclid's half of the Euclid–Euler theorem,
set.mm's `perfect1`, Wiedijk #70:

  if 2^p − 1 is prime, then 2^(p − 1)·(2^p − 1) is perfect.

The proof is ProofWiki's ("Theorem of Even Perfect Numbers/Sufficient
Condition"), checked against it before the pilot: 2^(p − 1) and 2^p − 1
share no factor, σ is multiplicative, σ of a prime q is q + 1, and σ of a
power of 2 is a geometric series. It follows `perfect1` step for step.

---

## Theorem euclid-perfect

The proof is `proofs/perfect-numbers.proof`, one theorem. It elaborates to
`corpus/elaboration/proofs/perfect-numbers/euclid-perfect.mm`, assumes
nothing, and verifies.

Numbers: 35 numbered steps, 25 of them at the top. Steps 1 to 7 are
memberships and 2^p = 2^(p − 1)·2; 8 is one contradiction showing that
2^p − 1 does not divide 2^(p − 1); 9 to 11 make the two coprime; 12 to 24
compute σ; 25 says the number is perfect.

---

## Rendered view

Let p ∈ ℕ with 2^p − 1 prime, and write q = 2^p − 1.

**Theorem.** 2^(p − 1)·q is perfect.

*Proof.* q does not divide 2^(p − 1): if it did, it would divide
2^(p − 1)·2 = 2^p, and also q itself, so it would divide 2^p − q = 1, and
then q = 1, which no prime is. So, q being prime, gcd(2^(p − 1), q) = 1, and
since σ is multiplicative

  σ(2^(p − 1)·q) = σ(2^(p − 1))·σ(q).

σ(q) = q + 1 = 2^p, since q is prime. The divisors of 2^(p − 1) are 1, 2,
…, 2^(p − 1), so σ(2^(p − 1)) = Σ(j = 0 to p − 1) 2^j, a geometric series,
whose sum is (1 − 2^p)/(1 − 2) = 2^p − 1. So

  σ(2^(p − 1)·q) = (2^p − 1)·2^p = 2·(2^(p − 1)·q),

and 2^(p − 1)·q is perfect, by definition. ∎

---

## Decisions made with the reader

1. **σ is a definition, by a sum over a set:** σ(n) = Σ(d ∈ {e ∈ ℕ : e
   divides n}) d. The theorem was chosen to test exactly this, a function
   defined by a sum over a set given by a condition, so the sum over a set
   is a notation, `Σ(_ ∈ _) _`, and not only facts about σ.
2. **σ is named, not mundane.** Reader A has not met σ, so a proof using it
   names it. Its three facts, multiplicativity, its value at a prime and at
   a prime's power, are named theorems, as ProofWiki names them.
3. **"Perfect" is a named definition,** n is perfect ↔ σ(n) = 2n, and the
   last step cites it, as ProofWiki's last line does.
4. **σ of a power of 2 is the corpus's own geometric series.** Steps 16 to
   20 read σ(2^(p − 1)) as Σ(j = 0 to p − 1) 2^j and cite
   `thm:proofs/geometric-series/geometric-sum`, where set.mm has
   `1sgm2ppw` in one label.
5. **p ∈ ℕ,** as ProofWiki writes it, where `perfect1` allows any integer:
   2^p − 1 is prime only for p ≥ 2.
6. **Coprimality is argued as `perfect1` argues it,** by q dividing 1 if it
   divided 2^(p − 1), and not through q being odd, so no fact about odd
   numbers is added.

---

## What the pilot reveals

1. **A sum over a set is a notation,** `Σ(_ ∈ _) _`, built to set.mm's
   `csu`. Σ(k = a to b) stays as it is, the same sum over {a, …, b}
   written the way a reader writes a range.
2. **An item's name may open with a Greek letter,** so σ's record is
   `definition σ`, a step cites `def:σ` and a proof imports
   `stdlib/divisibility/σ`. Metamath reads ASCII only, in labels, file
   names and comments, so wherever the elaborator writes a name into a
   Metamath file it spells a Greek letter by its English name
   (`spelt_in_ascii`): σ's restatement is `tests/restated/divisibility/
   sigma.mm`. Before this, the gate's verifier was handed `σ.mm` and
   crashed while reporting it.
3. **set.mm's σ takes a power first.** σ(n) is `1 sigma n`, and set.mm
   states its value and its value at a prime's power with the power left
   in, k^1 and P^c 1. Two lemmas in `proved.mm` write the power away,
   `g1sgmval` and `g1sgmppw` (`src/proofs/stdlib/divisors.rs`).
   Multiplicativity needs none: `sgmmul with A := 1`.
4. **A definition's letters keep set.mm's apart.** `sgmval2` keeps its two
   bound letters distinct, so σ's definition binds d in the sum and e in
   the set, {e ∈ ℕ : e divides n}, and not d in both.
5. **`membership` does not give n − 1 ∈ ℕ₀ from n ∈ ℕ,** so the library has
   `nat-minus-one` (`nnm1nn0`). The other new mundane items are what the
   proof cites in passing: `power-nat`, `prime-nat`, `two-prime`,
   `divides-self` and `prime-coprime`.

---

## Status

Checker clean, elaborated with nothing assumed, verified. Planted checker
defects: a Greek-named item imported from a file that does not hold it, and
a name that is no item's name.
