# Pilot: a long rising or falling run

Theorem 41 of `SELECTION.md`, Wiedijk #73, the Erdős–Szekeres theorem: N
different numbers with N > (r − 1)(s − 1) hold a rising run of r or a
falling run of s. set.mm's `erdsze`, in a mathbox, states it with order
isomorphisms; the page states it as a textbook does, and does not cite it.

---

## Theorem erdos-szekeres

The proof is `proofs/wiedijk/erdos-szekeres.proof`. It elaborates to
`corpus/elaboration/proofs/wiedijk/erdos-szekeres/`, `longest-runs.mm` and
`erdos-szekeres.mm`, which assume nothing and verify.

---

## Rendered view

**Lemma (longest-runs).** Let N, r ∈ ℕ and c : {1, …, N} → ℝ, with no
S ⊆ {1, …, N} of r or more places on which c rises. There is
L : {1, …, N} → {1, …, r − 1} with L(i) < L(j) whenever i < j and
c(i) < c(j).

*Proof.* Let U(k) be the S ⊆ {1, …, k} holding k on which c rises, I(k)
their sizes, and L(k) = sup I(k).
1. {k} ∈ U(k), so 1 ∈ I(k).
2. Each T ∈ U(k) is a part of {1, …, N} on which c rises, so |T| < r: I(k)
   is a set of whole numbers at most r − 1.
3. A set of whole numbers with an element and an upper bound holds its
   least upper bound: L(k) ∈ I(k), and 1 ≤ L(k) ≤ r − 1.
4. For i < j with c(i) < c(j), take T ∈ U(i) of size L(i). j ∉ T, and
   T ∪ {j} ∈ U(j), so L(i) + 1 = |T ∪ {j}| ≤ L(j). ∎

**Theorem.** Let r, s, N ∈ ℕ and a : {1, …, N} → ℝ one-to-one, with
(r − 1)(s − 1) < N. There is S ⊆ {1, …, N} with r ≤ |S| on which a
rises, or with s ≤ |S| on which a falls.

*Proof.* Suppose not. The lemma gives L for a and r, and M for b = −a and
s, since a fall in a is a rise in b. f(i) = (L(i), M(i)) lies in
{1, …, r − 1} × {1, …, s − 1}. For i < j, a(i) ≠ a(j): a rise makes
L(i) < L(j), a fall M(i) < M(j), and either way f(i) ≠ f(j). So f is
one-to-one, and by the pigeonhole principle N ≤ (r − 1)(s − 1). ∎

---

## Database items

In `corpus/stdlib/counting.records`: `pigeonhole` (named), `card-product`
and `card-add-one`, each with its set.mm label (`hashxp`, `hashunsng`). In
`calculus.records`: `integer-sup-member` (`suprzcl2`) and
`integer-sup-above` (`suprzub`). In `numbers.records`: `unequal-cases`
(`lttri2`). In `elaboration/stdlib/proved.mm`: `gf1hashle` for the
pigeonhole principle, from `f1domg` and `hashdomi`, and `gsupex`, that a
supremum over the reals is a set. The proof also cites `range-within`,
which the ballot pilot added.

---

## What the pilot reveals

1. **"The longest" is a least upper bound.** L(k) = sup I(k), with a
   reads line saying it is the longest run's length; that a bounded set of
   whole numbers holds its sup is one library fact. A max of a set would
   be a notation of its own.
2. **"Similarly" is the lemma at −a.** The falling half is longest-runs
   applied to b(i) = −a(i), and one block turns a rise in b into a fall
   in a.
3. **A bound letter's sort comes from its set however that set is
   written.** {|S| : S ∈ U(k)} reads |S| as a size where U(k) holds sets,
   and so does |S| for S over 𝒫{1, …, n}
   (`a_bound_letter_takes_its_sort_from_a_set_written_out`).
4. **A claim takes a conjunct of a set-builder's condition** as it takes a
   conjunct of any conclusion: "k ∈ T" from T ∈ U(k).
5. **A value in a range is in the system the range lies in.** L(i) ∈ ℝ from
   L : {1, …, N} → {1, …, r − 1}, by the table.
6. **A cited line read through a define asks its argument's domain**, as a
   claim that writes the define does: u ∈ I(k) asks k ∈ {1, …, N}.
7. **The negated "there is no X ⊆ A with …" has no pattern**; the page
   writes not (there is S ⊆ … with …).

Numbers, for the record: 182 numbered steps and 23 requires lines over
the two theorems.
