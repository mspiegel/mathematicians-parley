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

```
theorem cantor
  let A be a set                                                      (H1)
  let f : A → 𝒫A                                                      (H2)
  then there is B ∈ 𝒫A with for every x ∈ A, not f(x) = B

define B := {x ∈ A : not x ∈ f(x)}                                    (D1)

1.  B ⊆ A
    thm:set-builder-subset, from D1

2.  B ∈ 𝒫A
    def:powerset S := B, from H1, 1

3.  For every x ∈ A, not f(x) = B.
    fix
    let x ∈ A                                                         (K)

    3.1.  not f(x) = B
          contradiction
          suppose not not f(x) = B                                    (S)

          3.1.1.  f(x) = B
                  lines S

          3.1.2.  x ∈ B or not x ∈ B
                  thm:excluded-middle P := x ∈ B

          3.1.3.  x ∈ B. not x ∈ B.
                  cases, from 3.1.2

                  case
                  assume x ∈ B                                        (C1)

                  3.1.3.1.  not x ∈ f(x)
                            def:set-builder, from C1

                  3.1.3.2.  not x ∈ B
                            substitute f(x) = B (line 3.1.1) into line 3.1.3.1

                  3.1.3.3.  x ∈ B. not x ∈ B.
                            lines C1, 3.1.3.2

                  case
                  assume not x ∈ B                                    (C2)

                  3.1.3.4.  not x ∈ f(x)
                            substitute f(x) = B (line 3.1.1) into C2

                  3.1.3.5.  x ∈ B
                            def:set-builder, from K, 3.1.3.4

                  3.1.3.6.  x ∈ B. not x ∈ B.
                            lines 3.1.3.5, C2

4.  There is B ∈ 𝒫A with for every x ∈ A, not f(x) = B.
    exhibit, from 2, 3
```

---

## Database items

| symbols | what they are | set.mm |
|---|---|---|
| 𝒫A | power set | cpw |
| f : A → B, f(x) | function from A to B, application | wf, cfv |

| pointer | statement | set.mm |
|---|---|---|
| def:powerset | Let A be a set. S ∈ 𝒫A ↔ S ⊆ A. | elpw, elpwg |
| def:function | f : A → B ↔ for every x ∈ A, f(x) ∈ B, and ... | df-f |
| def:set-builder, thm:set-builder-subset | as in the Bezout pilot | elrab, ssrab2 |
| thm:excluded-middle | P or not P. | exmid |
| thm:cantor | proved above | canth |

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
