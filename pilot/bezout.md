# Pilot: Bezout's identity

Fifth pilot, first draft, written to `SYNTAX.md`. Its purpose is an
existence proof whose witness comes from a least element rather than a
construction: the gcd of a and b is the smallest positive number of the
form ax + by. Number 60 on Wiedijk's list, `bezout` in set.mm, and
Hammack's chapter on non-conditional statements.

Provisional forms introduced here, all listed in the batch report:

- `define S := {...} (D1)`: an unnumbered, labelled line that names an
  object built from things already in scope. Cited by label.
- Set-builder notation {t ∈ X : ...}, with the convention `def:set-builder`
  that t ∈ {t ∈ X : P(t)} ↔ t ∈ X and P(t).
- `instantiate v := t in line L, from L2`: line L claims "for every
  v ∈ X, ..."; the step claims the body with t for v, and L2 supplies
  t ∈ X. This is taking one case of a "for every" sentence that a line
  states, as `thm:X v := t` takes one case of a theorem.

The textbook proof shows "d divides a" and then says "similarly, d
divides b". There is no "similarly" in this language, so the argument is
a lemma applied twice.

---

## Theorem least-combination-divides

In `proof/bezout.proof`, first of the two.

---

## Theorem bezout

In `proof/bezout.proof`, second of the two.

---

## Database items

This pilot introduced `def:set-builder`, `def:subset`,
`thm:set-builder-subset`, `def:gcd`, `thm:well-ordering`,
`thm:division-algorithm`, `thm:pos-int-nat`, `thm:divides-combination`,
`thm:divides-le`, `thm:least-combination-divides` and `thm:bezout` in
`db/items.db`, the set-builder, subset and gcd rows in `db/notation.db`, and
the `instantiate` method in `db/methods.db`. The table that used to stand
here was merged into those files; `DATABASE.md` records what the merge
decided.

`define` was listed here as a provisional method. It is not one: `SYNTAX.md`
makes it the third kind of unnumbered line beside `let` and `assume`, so it
belongs to the grammar and not to the justification vocabulary. It is
described in `DATABASE.md` rather than in `db/methods.db`.

`thm:well-ordering` is stated with `assume S ⊆ ℕ` and no `let S be a set`,
because that is what this table said and what step 4 discharges. Whether a
set-existence hypothesis belongs there is open, and the same question applies
to `thm:completeness` in the intermediate value pilot and to two counting
lemmas in the subsets pilot.

---

## What the pilot reveals

1. **"Similarly" is a lemma.** The textbook proves d divides a and says
   the same argument gives d divides b. Here the argument is the theorem
   least-combination-divides with eleven hypotheses, applied at steps 9
   and 11 with (c, u, v) = (a, 1, 0) and (b, 0, 1). The lemma's statement
   is ugly because it carries everything the argument uses. That is the
   honest cost of "similarly".
2. **Naming an object needs a line.** S is built from a and b and used in
   six steps. `define S := ... (D1)` names it once. It is not a claim and
   not a hypothesis; it is a third kind of unnumbered line. Lamport's
   proofs have DEFINE for the same purpose.
3. **Instantiating a line.** Step 4 claims "for every s ∈ S, d ≤ s", and
   step 7.2 needs it for one s. So far only theorems and definitions could
   be instantiated, with `thm:X v := t`. `instantiate s := ... in line
   4, from 7.1` does the same for a line. It is a quantifier move and so, by
   READERS.md, a method.
4. **A hypothesis can be a "for every" sentence.** H11 quantifies over x
   and y. Citing it is an `instantiate`, at step 3.4. A `let`/`assume`
   statement can therefore contain quantifiers, which the earlier pilots
   did not need.
5. **Set-builder membership is a definition used both ways.** Step 2 puts
   a into S with the witnesses read off line 1; step 6 takes d out of S by obtaining
   them. Both are the ↔ convention on def:set-builder with the ∃ inside.
6. **An item is not a line.** The first draft cited "def:gcd" in `from`
   at three steps, as if it were a line, because its sentences about
   gcd(a, b) are facts once a and b are fixed. Decided: `from` lists
   lines and labels only. The four sentences are now step 12, citing
   def:gcd once with a and b filled in, and the later steps cite line 12.
   One step more, and nothing after `from` that is not on the page.
7. **Twelve requires lines for ℤ and numerals.** 1 ∈ ℤ, 0 ∈ ℤ, and
   nat-int appear repeatedly. This is the divides-on-ℤ decision paying
   as expected, and it shows why the viewer's collapse-by-role matters.

Numbers, for the record: the lemma has 13 numbered steps and 21 requires
lines; the theorem has 21 numbered steps and 15 requires lines. set.mm's
bezout has 47 essential steps. The requires counts are dominated by
membership of ℝ, which `READERS.md` settles as a written dull fact: the
lemma's step 2 has ten atoms and so carries ten such lines by itself.
