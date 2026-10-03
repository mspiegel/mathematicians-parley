# Pilot: the Pythagorean theorem

Theorem 22 of `SELECTION.md`, Wiedijk #4:

  in a triangle with a right angle at C, |AB|² = |AC|² + |BC|².

The Metamath 100 page lists `cphpyth`, stated in pre-Hilbert spaces; set.mm's
`pythag` is the theorem in the complex plane, proved from the law of cosines.
This proof is neither. A school reader learned the law of cosines as a
consequence of Pythagoras, so a proof citing it would read as circular, and
the corpus takes the textbook proof by similar triangles instead. No textbook
was fetched for it; the source is the proof as it is commonly taught.

---

## Theorems similar-triangles and pythagoras

The proof is `proofs/pythagoras.proof`, two theorems. `similar-triangles` is
the angle-angle criterion, proved in the readable layer from the angle sum
(Theorem 21) and the law of sines; `pythagoras` drops the altitude from C and
cites it twice. Both elaborate to `corpus/elaboration/proofs/pythagoras/`,
assume nothing, and verify.

Numbers: `similar-triangles` is 30 steps, most of them saying that an angle
or a distance is a real number; `pythagoras` is 21.

---

## Rendered view

**Theorem (similar triangles).** If triangles PQR and P′Q′R′ have
∠QPR = ∠Q′P′R′ and ∠PQR = ∠P′Q′R′, then |PQ|·|P′R′| = |P′Q′|·|PR|.

*Proof.* By the angle sum the third angles are equal too. By the law of
sines |PQ|·sin∠PQR = |PR|·sin∠QRP in one triangle, and the same with primes
in the other, where the sines are the same. The sine of an angle of a
triangle is not 0, so it cancels. ∎

**Theorem (Pythagoras).** If A, B, C form a triangle with ∠ACB = 90°, then
|AB|² = |AC|² + |BC|².

*Proof.* Let D be the foot of the altitude from C; it lies between A and B,
and ∠ADC = ∠BDC = 90°. Triangles ADC and ACB share the angle at A and have
a right angle each, so |AD|·|AB| = |AC|². In the same way |DB|·|AB| = |BC|².
Since |AD| + |DB| = |AB|, adding gives |AC|² + |BC|² = |AB|². ∎

---

## Decisions made with the reader

1. **Similar triangles, not the law of cosines.** The reader's choice, for
   the reason above.
2. **Similarity is a theorem of the corpus, in the readable layer.** It is
   proved from the angle sum and the law of sines, both cited items, so the
   argument a reader would check is on the page. Its conclusion is a product,
   |PQ|·|P′R′| = |P′Q′|·|PR|, the proportion PQ/P′Q′ = PR/P′R′ with nothing
   divided.
3. **The library gained what the textbook cites:** the law of sines, the
   foot of the altitude from a right angle, that a point between two others
   divides the distance between them and lies on the ray from either through
   the other, that between reads either way, that the sine of an angle of a
   triangle is positive, that a distance is a real number, and cancelling a
   factor that is not 0. Each is proved in `proved.mm` or by set.mm.

---

## What the pilot reveals

1. **A theorem whose letters are points could not be cited from another
   file.** Citing `angle-sum` bound its `let` lines only where they were
   memberships, sets or functions; `let A be a point` is now one of them.
2. **An item applying a library function read the function as a name to
   bind.** `law-of-sines` writes sin(∠PQR), and the citation looked for a
   value of `sin`. A function's name where it is applied is the library's;
   only there, since a letter such as C names both a point and a function.
3. **A point obtained is a point.** The checker reads `D ∈ 𝔼²` from an
   `obtain` as a sort, as it reads `let A be a point`, and refuses a citation
   made only for it; the elaborator now does the same. A number obtained is
   still cited for its membership in a `requires` line, as eight proofs do.
4. **`algebra` takes one cited equation off at a time, by its leading
   term.** It found no combination for a step that was |P′R′| times one
   equation minus |PR| times another, because the leading terms did not line
   up; written as two steps and a calculation, as a reader would, it does.
5. **Two distances were taken for one renamed.** `membership` proves a
   product real in its standard order, |PR|·|P′Q′|, and then carries that
   back to the order written, |P′Q′|·|PR|, by swapping the factors. It never
   swapped them: `rebound` counted the points in P − R as bound letters, so
   |PR| and |P′Q′| looked like one term renamed, and the comparison went
   inside the product instead. A class variable is bound by nothing, as
   `letters_bound` already said; `rebound` now says so too, and
   `tests/elaborator/product-order.proof` writes a product of two distances
   out of order.
