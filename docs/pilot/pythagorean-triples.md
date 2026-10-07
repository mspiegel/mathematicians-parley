# Pilot: Pythagorean triples

Theorem 28 of `SELECTION.md`, set.mm's `pythagtrip`, Wiedijk #23:

  a² + b² = c² exactly when there are k, m, n ∈ ℕ with c = k(m² + n²) and
  a, b being k(m² − n²) and 2kmn, in one order or the other.

The proof is ProofWiki's ("Solutions of Pythagorean Equation"), read for
this pilot: a primitive triple is (2mn, m² − n², m² + n²) with m > n,
coprime and of opposite parity, found by halving c + b and c − b, whose
halves share no factor and multiply to a square; and every triple is k times
a primitive one. Hammack's Book of Proof does not classify the triples; its
nearest is the exercise "if a² + b² = c², then a or b is even" (chapter 6),
which is `even-leg` here. set.mm follows the Isabelle proof.

---

## Theorems

The proof is `proofs/pythagorean-triples.proof`, seven theorems of 115
numbered steps, 185 with those inside blocks. All seven elaborate to
`corpus/elaboration/proofs/pythagorean-triples/`, assume nothing, and verify.

- `even-leg`: in a triple, a or b is even.
- `leg-hypotenuse-coprime`: where gcd(a, b) = 1, gcd(b, c) = 1.
- `primitive-triple`: where gcd(a, b) = 1 and a is even, there are m, n ∈ ℕ
  with n < m, gcd(m, n) = 1, m + n odd, a = 2mn, b = m² − n² and
  c = m² + n². ProofWiki's main theorem.
- `triple-scaled`: there is k ∈ ℕ with a/k, b/k, c/k ∈ ℕ, gcd(a/k, b/k) = 1
  and (a/k)² + (b/k)² = (c/k)²; k is gcd(a, b).
- `triple-parameters`: every triple has the form, the legs in one order or
  the other, by cases on which leg of the primitive triple is even.
- `triple-from-parameters`: the form is a triple.
- `pythagorean-triples`: set.mm's statement, the two directions joined.

---

## Rendered view

**Lemma (even-leg).** If a² + b² = c², then a or b is even.

*Proof.* If both were odd, a² + b² would be 4(…) + 2, so c² even, so c even
and c² a multiple of 4, and 4 would divide 2. ∎

**Lemma (leg-hypotenuse-coprime).** If a² + b² = c² and gcd(a, b) = 1, then
gcd(b, c) = 1.

*Proof.* gcd(b, c) divides c² − b² = a², and shares no factor with a, since
a common factor would divide gcd(a, b) = 1; so it divides 1. ∎

**Theorem (primitive-triple).** If a² + b² = c², gcd(a, b) = 1 and a is
even, there are m > n > 0, coprime, with m + n odd, a = 2mn, b = m² − n² and
c = m² + n².

*Proof.* Write a = 2w. b is odd, else 2 divides gcd(a, b) = 1; so c is odd,
else 2 would divide 1. So c + b = 2s and c − b = 2t, with s + t = c,
s − t = b, and w² = st. A common factor of s and t divides c and b, and
gcd(b, c) = 1, so s and t share none; their product is a square, so each is
one: s = m², t = n². Then w = mn, a = 2mn, b = m² − n², c = m² + n². b > 0
gives n < m; a common factor of m and n divides s and t, so gcd(m, n) = 1;
and m + n even would make b = (m + n)(m − n) even. ∎

**Lemma (triple-scaled).** Every triple is k times a primitive one, k being
gcd(a, b).

*Proof.* k divides a and b, so k² divides a² + b² = c², so k divides c.
Dividing by k leaves a triple whose legs share no factor. ∎

**Theorem (pythagorean-triples).** a² + b² = c² exactly when there are
k, m, n ∈ ℕ with c = k(m² + n²) and a, b being k(m² − n²), 2kmn in one order
or the other.

*Proof.* Forward: scale down by triple-scaled; one leg is even by even-leg;
primitive-triple gives m and n, the order depending on which leg; scale back
up. Backward: (k(m² − n²))² + (2kmn)² = (k(m² + n²))². ∎

---

## Decisions made with the reader

1. **ProofWiki's shape.** A primitive triple first, then every triple as a
   multiple of one, then set.mm's statement as the two joined, rather than
   one theorem in set.mm's form.
2. **The legs' order is an "or", written out.** "In some order" as a new
   notation, and set.mm's {a, b} = {…}, which reads as an ordered equality,
   were both set aside; mathlib states it the same way.
3. **Three names at once, "there are k, m, n ∈ ℕ with …",** one notation
   record built as nested "there is" by the existing `nests` field, and
   obtained in one line, `obtain k, m, n`.
4. **"If and only if" is proved a direction at a time,** by a new block,
   `both directions`, with a `direction` part for each.
5. **The coprime-square item says gcd(s, t) = 1,** as a textbook does;
   set.mm's form asks that s, t and the root share no factor all three, and
   `proved.mm` bridges the two.
6. **A contradiction ends on "2 ≤ 1, which is impossible",** not on a further
   step `not 2 ≤ 1` written only to be contradicted.
7. **i is a letter where a line introduces it,** and the imaginary unit
   otherwise.

---

## What the pilot reveals

1. **`both directions`** is a `cases` of two parts closed by `impbida`
   (`ELABORATION.md`), with its record in `methods.records` and its check
   that each direction assumes one side and ends on the other.
2. **`obtain` takes any number of names.** set.mm discharges one or two with
   one lemma; three or more are discharged a name at a time (`anassrs`,
   `rexlimdva`).
3. **A citation's values are read before any is given.** `a := b/k,
   b := a/k`, which `triple-parameters` writes to apply `primitive-triple`
   with the legs swapped, read the second value in the first's new name,
   (b/k)/k; the values are now read together, in the step's names.
4. **A cited line is read a sentence at a time** by the single-name exhibit
   and by `algebra` taking a cited equation that is the claim divided, as the
   other routes already read it: `obtain` lines say many things.
5. **A lemma's bound letter is kept apart from the values it is given,** so
   `even` unfolded at m + n does not capture the proof's n; and a several-name
   exhibit whose witness is the claim's own letter is shown under fresh
   letters and renamed back.
6. **`arithmetic` proves denials of an order,** and a claim of numerals alone
   is `arithmetic`'s, which the checker now asks.
7. **The checker read a several-name "there is" one layer deep.** It reads
   nested "there is" now, which the three-name spelling builds.
8. **Library items:** coprime-square, divides-transitive, divides-square,
   divides-quotient, gcd-quotients-coprime, square-equal, square-less and
   square-positive, each set.mm's, coprime-square through `proved.mm`.
9. **A letter that is a constant.** The first draft wrote `obtain i`, and the
   elaborator read i as the imaginary unit while the checker read it as the
   letter; the elaborator now reads it as the checker does.
10. **The last direction was first written k(2mn)** to get past a step
    `algebra` could not build; the fault was item 4, and 2kmn reads as a
    textbook has it.
