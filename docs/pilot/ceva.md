# Pilot: Ceva's theorem

Theorem 46 of `SELECTION.md`, set.mm's `cevath`, Metamath 100 #61:

  if lines from the vertices A, B, C of a triangle through a point O meet
  the opposite sides at D, E, F, then |AF|·|BD|·|CE| = |FB|·|DC|·|EA|.

set.mm states it of the differences of the points rather than their
lengths, and says the three lines meet by signed areas. The page states it
of distances, with O between each vertex and the point on the opposite
side.

---

## Theorems cevian-ratio and ceva

The proof is `proofs/wiedijk/ceva.proof`, two theorems. Both elaborate to
`corpus/elaboration/proofs/wiedijk/ceva/`, assume nothing, and verify.

Numbers: `cevian-ratio` is 33 steps, `ceva` 33, of which 9 say that an
angle, a sine or one of the three ratios is a real number.

---

## Rendered view

**Theorem (the ratio at O).** Let A, B, C form a triangle, D lie between B
and C, and O between A and D. Then
|DC| = |BD|·|OC|·sin∠AOC / (|OB|·sin∠BOA).

*Proof.* The law of sines in OBD and in ODC gives |BD| against |OB| and
|DC| against |OC|. The angles at D are supplementary, and so are ∠DOB and
∠BOA, and ∠COD and ∠AOC; the sine of an angle is the sine of its
supplement. Dividing one equation by the other gives the ratio. ∎

**Theorem (Ceva).** With D, E, F on the sides and O between each vertex
and the point opposite, |AF|·|BD|·|CE| = |FB|·|DC|·|EA|.

*Proof.* Let x = |OC|·sin∠AOC/(|OB|·sin∠BOA), and y and z the same ratios
taken round the triangle. By the ratio at O, |DC| = |BD|·x,
|EA| = |CE|·y and |FB| = |AF|·z, and x·y·z = 1 since every distance and
sine appears once above and once below. So
|FB|·|DC|·|EA| = |AF|·|BD|·|CE|·x·y·z = |AF|·|BD|·|CE|. ∎

---

## Database items

In `corpus/stdlib/geometry.records`: `triangle-on-side`, that a vertex and
a point of the opposite side with one end of it form a triangle, proved in
`proved.mm` as `gtriside`. In `corpus/stdlib/trigonometry.records`:
`sin-supplement`, sin(180° − x) = sin x, proved as `gsinsupp` from
`sinpim`. Both are mundane.

---

## What the pilot reveals

1. **The ratio at O, not nine laws of sines.** The proof first planned took
   the law of sines in the six small triangles and the three at the
   vertices and cancelled a product of six factors, which needed about 18
   steps only to put angles in order. The ratio at O is the textbook
   lemma, and with the angles named the same way in each use the three
   cancel with no angle turned.

2. **A lemma's hypothesis may hold a letter its conclusion does not.**
   `triangle-on-side` has a point R in its hypotheses only, and the build
   took it from the wrong cited line; a whole cited line now fixes the
   letters of the hypothesis it fits, and a triangle cited in another
   order still fits.

3. **Naming the ratios.** Three substitutions into the product wrote out
   the whole product each time, lines of up to 244 characters. A naming
   `let` for each ratio makes each line a few terms, at the cost of steps
   saying x, y and z are real, which the last algebra step needs.
