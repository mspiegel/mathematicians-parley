# Pilot: Cantor's theorem

Sixth pilot, first draft. Its purpose is a set-theoretic argument and the
one statement among the ten with a set-existence hypothesis, which
`READERS.md` says is hidden entirely. Number 63 on Wiedijk's list, `canth`
in set.mm, in Hammack's chapter on cardinality.

Provisional forms, listed in the batch report: `let A be a set` and
`let f : A → B` as hypothesis lines; `define` and set-builder as in the
Bezout pilot; and the power set 𝒫A.

The theorem is stated without "onto": no function from A to 𝒫A reaches
every subset, written as the existence of a subset it misses.

---

## Theorem cantor

The skeleton is `proof/cantor.proof`. The items it cites are in `db/`.

---

## Database items

This pilot introduced `def:powerset`, `def:function`, `thm:excluded-middle`
and `thm:cantor` in `db/items.db`, and the power set and function rows in
`db/notation.db`. The table that used to stand here was merged into those
files; `DATABASE.md` records what the merge decided.

Two things the merge changed. `def:function` as written here was truncated
and is now an open item, and the intermediate value pilot's item of the same
name, which was a different statement, became `thm:function-value`. The rows
reading "as in the Bezout pilot" are written out once in `db/items.db`.

The hypothesis `let A be a set` is set.mm's `A e. _V`. The hypothesis
`let f : A → 𝒫A` is `F : A --> ~P A`. def:function is not cited in the
proof, since nothing about f is used except that f(x) is something x may
or may not belong to.

---

## What the pilot reveals

1. **"Let A be a set" is the set-existence hypothesis.** READERS.md says
   these are hidden entirely. That cannot be right for this theorem: A
   has to be named, and "let A be a set" is how a school reader names an
   arbitrary set. The first session already suggested rendering `A e. _V`
   as exactly this line. Decided: READERS.md now says a set-existence
   hypothesis is written as "Let A be a set", and SYNTAX.md lists the
   form beside `let n ∈ ℕ`, `let A be a point` and `let f : A → B`.
2. **Double negation is literal and costs a step.** The claim at 3.1 is
   "not f(x) = B", so by the literal-negation rule the supposition is
   "not not f(x) = B", and step 3.1.1 removes the double negation by
   `lines`. Ugly on the page, and correct; it is where the classical
   step sits.
3. **Excluded middle is a cited theorem.** 3.1.2 claims "x ∈ B or not
   x ∈ B" from thm:excluded-middle with P := x ∈ B. The first draft wrote
   it as `lines` with nothing cited, a tautology; that was rejected
   because nothing is assumed, and a school reader has never been told
   that "P or not P" is a law. The citation is also the first to
   substitute a formula for a variable rather than a term, which set.mm
   does routinely with its wff variables. It is the second place the
   classical logic shows.
4. **The diagonal argument is a cases block inside a contradiction block
   inside a fix block.** Four levels of numbering, 3.1.3.6. The shape is
   right; the numbers are getting long, and that is a viewer problem
   before it is a text problem.
5. **f(x) is used as a set with no unfolding.** Steps 3.1.3.1 and 3.1.3.4
   ask whether x ∈ f(x). Nothing says f(x) is a set except that it is in
   𝒫A, which is never cited. set.mm needs `F : A --> ~P A` to know that
   `( F ` x )` is a class it can talk about; the readable text does not,
   because Reader A does not ask. The elaborator will need H2 for this
   even though no step cites it.
6. **The textbook says "no onto function".** The pilot says "there is a
   subset every f(x) misses", which is the same thing without defining
   "onto". "Onto" and "infinite" are two words the corpus will need
   definitions for if the textbook statements are to be written.

Numbers, for the record: 14 numbered steps, 0 requires lines. set.mm's
canth has 21 essential steps.
