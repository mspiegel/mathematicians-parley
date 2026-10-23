# Pilot: Heron's formula

Theorem 32 of `SELECTION.md`, set.mm's `heron`, Metamath 100 #57:

  the area of a triangle with sides a, b, c is √(s(s − a)(s − b)(s − c)),
  with s = (a + b + c)/2.

The library already held it as a record, cited by
`proofs/euclid/heron-formula.proof`. The pilot is the reader's proof, which
cites neither that record nor set.mm's `heron`.

---

## Theorem heron

The proof is `proofs/wiedijk/heron.proof`. It elaborates to
`corpus/elaboration/proofs/wiedijk/heron/heron.mm`, which assumes nothing and
verifies.

---

## Rendered view

Let A, B, C form a triangle, and s = (|BC| + |CA| + |AB|)/2.

**Theorem.** The area of △ABC = √(s(s − |BC|)(s − |CA|)(s − |AB|)).

*Proof.*

1. The area is ½·|BC|·|AC|·sin∠BCA, and the law of cosines at C gives |AB|²
   from |BC|, |AC| and cos∠BCA.
2. With sin² + cos² = 1, 16·area² = 4|BC|²|AC|² − (|BC|² + |AC|² − |AB|²)².
3. That is 16·s(s − |BC|)(s − |CA|)(s − |AB|), by algebra from the definition
   of s.
4. The area is positive, so it is the square root.

∎

---

## Database items

In `corpus/stdlib/geometry.records`: `area-real`, that the area of a triangle
is a number, proved in `proved.mm` as `gareacl` from `gsangcl`.

---

## What the pilot reveals

1. **A weakening in the build took its terms apart.** "area ≥ 0" from
   "area > 0" went through the comparison of two polynomials, which
   multiplied the area's formula out and asked a membership of each factor,
   the size of a sine among them. A weakening of a cited line as it stands
   is `ltled` of that line, its terms whole.

2. **A distance said once read its points only from the facts.** Comparing
   the last step with the statement proves a standard form, which has no
   facts, and |BC| being real asked for B ∈ ℂ there. A point's line is kept
   as a number letter's is, and read there.

3. **Each algebra step multiplies at most one equation by a term.** The
   square of the area by the sine, its sin² replaced, and its cosine term
   replaced from the law of cosines are separate steps, joined by a
   calculation.
