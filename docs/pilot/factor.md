# Pilot: the factor theorem

Theorem 25 of `SELECTION.md`, Wiedijk #89:

  if p is a polynomial and p(a) = 0, then p(x) = (x − a)·q(x) for some
  polynomial q.

set.mm's `facth` says it of functions: F = G ∘f· (F quot G), with G the
polynomial x − a and `quot` polynomial division. The proof here is the
textbook one: by the remainder theorem p(x) = (x − a)·q(x) + p(a), and p(a)
is 0.

---

## Theorem factor

The proof is `proofs/factor.proof`, one theorem of 3 numbered steps, 8 with
those inside the block. It elaborates to `corpus/elaboration/proofs/factor/`,
assumes nothing, and verifies.

---

## Rendered view

**Theorem (factor).** Let p be a polynomial and a ∈ ℂ with p(a) = 0. Then
there is a polynomial q with p(x) = (x − a)·q(x) for all x ∈ ℂ.

*Proof.* By the remainder theorem there is a polynomial q with
p(x) = (x − a)·q(x) + p(a) for all x ∈ ℂ. Since p(a) = 0, p(x) = (x − a)·q(x). ∎

---

## Decisions made with the reader

1. **A polynomial is said in words.** `let p be a polynomial`, "q is a
   polynomial", "there is a polynomial q with …". set.mm's `Poly`, a set of
   functions picked out by coefficient sequences, stays out of sight, as the
   plane does in geometry.
2. **The proof is by division**, citing the remainder theorem, the order a
   school text takes. The theorem was chosen to test hiding the encoding,
   and the work of that is in the library: the page never writes a
   coefficient.
3. **q is a polynomial** in the statement, as the textbook says it.

---

## What the pilot reveals

1. **A notation could not name a set the page never writes.** "There is a
   polynomial q with …" has no hole for a set, and the existential the
   checker and elaborator know is "there is q ∈ S with …". A notation may
   now say `fills hole 2 with polynomials`: the node built is that
   existential, with the polynomials as its set, so obtaining and
   exhibiting work as for any "there is" (`GRAMMAR.md`). "p is a
   polynomial" is a membership the same way.
2. **A name a binder introduces had no sort unless written `x ∈ S`.** The
   parser now gives the name in "a polynomial q" the sort the filled set
   holds, a function, so q(x) is q applied to x.
3. **`let p be a polynomial` is an eleventh form of `let`.** It introduces a
   function and asserts that it is a polynomial, as `let f : A → B be
   one-to-one` asserts that f is one-to-one, and a citation of an item
   written so must supply it; a planted case drops it and is refused.
4. **The congruence walk could not rewrite a function applied.** Carrying
   the obtained q through a line needed `fveq1d`, whose variables set.mm
   declares in another order than the walk fills them, so it is given its
   parts by name as `mpteq1d` is; `fveq12d` fits the walk and is a row of
   the table. The verifier caught the first attempt, a row for `fveq1d`
   that filled its variables in the wrong places.
5. **The remainder theorem is set.mm's `plyrem` read a value at a time.**
   set.mm says p less (x − a) times the quotient is the constant function
   p(a); `gplyrem` reads that at each x, with the quotient a polynomial
   because x − a has degree 1 and so is not the zero polynomial.
