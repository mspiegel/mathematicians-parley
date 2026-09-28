# Pilot: the intermediate value theorem

Eighth pilot. Its purpose is quantifier alternation: the definition of
continuity is "for every ε there is δ such that for every x", and the
proof both unfolds it and instantiates it. It also needs the least upper
bound property of ℝ, which is above the school ceiling and is cited by
pointer. Number 79 on Wiedijk's list, `ivth` in set.mm.

The statement is the zero-crossing form, f(a) < 0 < f(b), rather than
set.mm's general u between f(a) and f(b), to keep the proof to one sign
change. The general form follows by applying this one to f − u.

The proof finds c as the least upper bound of the set where f is
negative and shows f(c) = 0 by cases on the sign of f(c): the negative
and positive cases each end in a contradiction, and each impossible case
is closed by the theorem that a contradiction implies anything.

---

## Theorem intermediate-value

The skeleton is `proof/intermediate-value.proof`. The items it cites are in
`db/`.

The merge renamed three of its citations. Steps 14, 17.13 and 17.25.5.5 cited
`def:stdlib/functions/function` for the fact that f(x) is real, while the Cantor pilot used the
same name for a definition of what `f : A → B` means. The fact is now
`thm:stdlib/functions/function-value` and those three steps name it.


---

## Database items

This pilot introduced `def:stdlib/calculus/interval`, `thm:stdlib/calculus/interval-real`,
`thm:stdlib/sets/subset-transitive`, `thm:stdlib/functions/function-value`, `def:stdlib/calculus/continuous-on`,
`def:stdlib/calculus/upper-bound`, `def:stdlib/calculus/least-upper-bound`, `thm:stdlib/calculus/completeness`,
`thm:stdlib/numbers/trichotomy`, `thm:stdlib/reasoning/from-contradiction`, `thm:proof/intermediate-value/point-right`,
`thm:stdlib/numbers/abs-difference-lt` and `thm:proof/intermediate-value/intermediate-value` in the database, and
the closed interval row in `db/notation.records`. The table that used to stand
here was merged into those files; `DATABASE.md` records what the merge
decided.

Three things the merge changed. The row called `def:stdlib/functions/function` here is a
derived fact, not a definition, and collided with the Cantor pilot's
definition of that name; it is now `thm:stdlib/functions/function-value`, and the three steps
citing it name it. `thm:stdlib/numbers/real-closure` was stated here with two sentences and
in the triangle inequality pilot with one; the merged item carries both.
`thm:proof/triangle-inequality/abs-bounds` read "from the triangle inequality pilot" and is now
recorded as proved in that pilot's proof file.

`thm:proof/intermediate-value/point-right` is one of the twelve open items, and the only one that
exists purely because the language has no `min` notation.

---

## What the pilot reveals

1. **Quantifier alternation is handled, at a price in lines.** Continuity
   is unfolded once, at step 16, into a sentence with four quantifiers,
   and each impossible case instantiates the outer two at once, obtains
   δ, and later instantiates the inner one. `instantiate` with two
   variables and `obtain` from a line both read naturally. The price is
   that every quantifier move is a step, so the negative case is 21 steps
   and the positive case is 9 steps around a 15-step sub-block.
2. **Impossible cases close by a cited theorem.** The first draft put the
   sign split inside a contradiction block and left the cases step
   without a claim, because the two cases reached different
   contradictions. Three alternatives were compared: refuting each sign
   in its own contradiction block and citing trichotomy, with no cases
   block; widening the contradiction rule to accept a claimless cases
   block whose cases end in different pairs; and, chosen, splitting on
   all three signs by trichotomy and closing each impossible case with
   thm:stdlib/reasoning/from-contradiction, "if P and not P then Q", so that every case
   ends in the common claim f(c) = 0. The chosen form keeps every step
   with a claim, needs no new rule, keeps the textbook's "negative, zero
   or positive" narrative, and scales in the viewer. Its cost is the
   pointer to pm2.21, which a school reader finds strange and which is
   therefore exactly the kind of thing to point to. It is the third
   place, after excluded middle and double negation, where the logic
   itself is a cited item.
3. **Requires lines that needed proofs became steps.** The first draft
   wrote f(x₁) ∈ ℝ as a requires line and then had to prove it under the
   step, with an improvised number. It is now step 17.13, an ordinary
   step before the one that needs it, as are s ∈ ℝ at 17.25.3 and the two
   real-closure facts. SYNTAX.md now says a requires line has one
   citation and does not nest.
4. **Nothing after `from` but lines.** The first draft wrote step 3 as
   "S ⊆ ℝ, from thm:stdlib/sets/set-builder-subset, thm:stdlib/calculus/interval-real", citing two
   theorems as if they were lines. They are now steps 3 and 4, each
   citing its theorem, and step 5 joins them.
5. **Numbering reaches four levels.** The deepest step is 17.25.5.10. The
   first draft went one level deeper and used two improvised devices to
   cope; both are gone. Four levels is the honest depth of a fix inside a
   case inside a cases block with a contradiction inside it. The numbers
   are long, and that is a viewer problem before it is a text problem.
6. **Completeness of ℝ is above the ceiling and is a pointer.** Step 8
   cites thm:stdlib/calculus/completeness. A school reader has never seen it, and
   READERS.md's answer is that the pointer leads to a definition and a
   statement, both readable. Whether the *proof* of completeness is ever
   in the corpus is a question about the foundation, since in set.mm it
   is an axiom of the real numbers, ax-pre-sup.
7. **A lemma that exists only to avoid min.** thm:proof/intermediate-value/point-right is cited to
   get a point x₁ just right of c, within δ and not past b. Textbooks
   write "take x₁ = min(b, c + δ/2)". Without a min notation and its
   case split, the lemma is the honest form; it is one more item the
   database must hold.
8. **The two impossible cases are not symmetric and cannot share a
   lemma.** Unlike Bezout's "similarly", the two cases here use the least
   upper bound in different ways, one through "c is an upper bound" and
   one through "c is the least". No factoring is available; the length is
   real.
9. **The statement is narrower than set.mm's.** ivth has f(a) < u < f(b)
   and concludes f(c) = u; the pilot fixes u = 0. The general theorem is
   this one applied to f − u, which needs a theorem that f − u is
   continuous, another database item.

Numbers, for the record: 71 numbered steps, 41 requires lines. set.mm's
ivth has 16 essential steps on top of ivthle's 69, but the continuity in
set.mm is topological and its unfolding to ε and δ is elsewhere.
