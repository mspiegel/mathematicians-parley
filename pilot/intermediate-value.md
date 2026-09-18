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

```
theorem intermediate-value
  let a ∈ ℝ                                                           (H1)
  let b ∈ ℝ                                                           (H2)
  assume a < b                                                        (H3)
  let f : [a, b] → ℝ                                                  (H4)
  assume f is continuous on [a, b]                                    (H5)
  assume f(a) < 0                                                     (H6)
  assume 0 < f(b)                                                     (H7)
  then there is c ∈ [a, b] with f(c) = 0

define S := {x ∈ [a, b] : f(x) < 0}                                   (D1)

1.  a ∈ [a, b]
    def:interval x := a, from H1
    requires a ≤ a: inequalities
    requires a ≤ b: inequalities, from H3

2.  a ∈ S
    def:set-builder x := a, from 1, H6

3.  S ⊆ [a, b]
    thm:set-builder-subset, from D1

4.  [a, b] ⊆ ℝ
    thm:interval-real, from H1, H2

5.  S ⊆ ℝ
    thm:subset-transitive, from 3, 4

6.  For every s ∈ S, s ≤ b.
    fix
    let s ∈ S                                                         (K1)

    6.1.  s ∈ [a, b]
          def:set-builder, from K1

    6.2.  s ≤ b
          def:interval, from 6.1

7.  b is an upper bound of S
    def:upper-bound, from 6

8.  c ∈ ℝ. c is a least upper bound of S.
    obtain c: thm:completeness S := S, from 5, 2, 7

9.  c is an upper bound of S
    def:least-upper-bound, from 8

10. For every s ∈ S, s ≤ c.
    def:upper-bound, from 9

11. a ≤ c
    instantiate s := a in line 10, from 2

12. c ≤ b
    instantiate u := b in def:least-upper-bound, from 8, 7

13. c ∈ [a, b]
    def:interval x := c, from 8, 11, 12

14. f(c) ∈ ℝ
    def:function, from H4, 13

15. f(c) < 0 or f(c) = 0 or 0 < f(c)
    thm:trichotomy x := f(c), from 14

16. For every c′ ∈ [a, b], for every ε ∈ ℝ with ε > 0,
    there is δ ∈ ℝ with δ > 0 and
    for every x ∈ [a, b], if |x − c′| < δ then |f(x) − f(c′)| < ε.
    def:continuous-on, from H5

17. f(c) = 0
    cases, from 15

    case
    assume f(c) < 0                                                   (C1)

    17.1.  not c = b
           contradiction
           suppose not not c = b                                      (S1)

           17.1.1.  c = b
                    lines S1

           17.1.2.  f(b) < 0
                    substitute c = b (line 17.1.1) into C1

           17.1.3.  not f(b) < 0
                    inequalities, from H7

           17.1.4.  f(b) < 0. not f(b) < 0.
                    lines 17.1.2, 17.1.3

    17.2.  c < b
           inequalities, from 12, 17.1

    17.3.  −f(c) > 0
           inequalities, from C1

    17.4.  There is δ ∈ ℝ with δ > 0 and
           for every x ∈ [a, b], if |x − c| < δ then |f(x) − f(c)| < −f(c).
           instantiate c′ := c, ε := −f(c) in line 16, from 13, 14, 17.3

    17.5.  δ ∈ ℝ. δ > 0.
           For every x ∈ [a, b], if |x − c| < δ then |f(x) − f(c)| < −f(c).
           obtain δ from line 17.4

    17.6.  x₁ ∈ ℝ. c < x₁. x₁ ≤ b. x₁ − c < δ.
           obtain x₁: thm:point-right c := c, b := b, δ := δ, from 8, H2, 17.5, 17.2

    17.7.  a ≤ x₁
           inequalities, from 11, 17.6

    17.8.  x₁ ∈ [a, b]
           def:interval x := x₁, from 17.6, 17.7

    17.9.  c − δ < x₁
           inequalities, from 17.6, 17.5

    17.10. x₁ < c + δ
           inequalities, from 17.6

    17.11. |x₁ − c| < δ
           thm:abs-difference-lt x := x₁, c := c, δ := δ, from 17.6, 8, 17.5, 17.9, 17.10

    17.12. |f(x₁) − f(c)| < −f(c)
           instantiate x := x₁ in line 17.5, from 17.8, 17.11

    17.13. f(x₁) ∈ ℝ
           def:function, from H4, 17.8

    17.14. f(x₁) − f(c) ∈ ℝ
           thm:real-closure, from 17.13, 14

    17.15. f(x₁) − f(c) ≤ |f(x₁) − f(c)|
           thm:abs-bounds x := f(x₁) − f(c), from 17.14

    17.16. f(x₁) < 0
           inequalities, from 17.15, 17.12

    17.17. x₁ ∈ S
           def:set-builder x := x₁, from 17.8, 17.16

    17.18. x₁ ≤ c
           instantiate s := x₁ in line 10, from 17.17

    17.19. not x₁ ≤ c
           inequalities, from 17.6

    17.20. x₁ ≤ c. not x₁ ≤ c.
           lines 17.18, 17.19

    17.21. f(c) = 0
           thm:from-contradiction P := x₁ ≤ c, Q := f(c) = 0, from 17.20

    case
    assume f(c) = 0                                                   (C2)

    17.22. f(c) = 0
           lines C2

    case
    assume 0 < f(c)                                                   (C3)

    17.23. There is δ ∈ ℝ with δ > 0 and
           for every x ∈ [a, b], if |x − c| < δ then |f(x) − f(c)| < f(c).
           instantiate c′ := c, ε := f(c) in line 16, from 13, 14, C3

    17.24. δ ∈ ℝ. δ > 0.
           For every x ∈ [a, b], if |x − c| < δ then |f(x) − f(c)| < f(c).
           obtain δ from line 17.23

    17.25. For every s ∈ S, s ≤ c − δ.
           fix
           let s ∈ S                                                  (K2)

           17.25.1.  s ∈ [a, b]
                     def:set-builder, from K2

           17.25.2.  f(s) < 0
                     def:set-builder, from K2

           17.25.3.  s ∈ ℝ
                     def:interval, from 17.25.1

           17.25.4.  s ≤ c
                     instantiate s := s in line 10, from K2

           17.25.5.  s ≤ c − δ
                     contradiction
                     suppose not s ≤ c − δ                            (S2)

                     17.25.5.1.  c − δ < s
                                 inequalities, from S2

                     17.25.5.2.  s < c + δ
                                 inequalities, from 17.25.4, 17.24

                     17.25.5.3.  |s − c| < δ
                                 thm:abs-difference-lt x := s, c := c, δ := δ,
                                   from 17.25.3, 8, 17.24, 17.25.5.1, 17.25.5.2

                     17.25.5.4.  |f(s) − f(c)| < f(c)
                                 instantiate x := s in line 17.24, from 17.25.1, 17.25.5.3

                     17.25.5.5.  f(s) ∈ ℝ
                                 def:function, from H4, 17.25.1

                     17.25.5.6.  f(s) − f(c) ∈ ℝ
                                 thm:real-closure, from 17.25.5.5, 14

                     17.25.5.7.  −(f(s) − f(c)) ≤ |f(s) − f(c)|
                                 thm:abs-bounds x := f(s) − f(c), from 17.25.5.6

                     17.25.5.8.  0 < f(s)
                                 inequalities, from 17.25.5.7, 17.25.5.4

                     17.25.5.9.  not f(s) < 0
                                 inequalities, from 17.25.5.8

                     17.25.5.10. f(s) < 0. not f(s) < 0.
                                 lines 17.25.2, 17.25.5.9

    17.26. c − δ is an upper bound of S
           def:upper-bound, from 17.25

    17.27. c ≤ c − δ
           instantiate u := c − δ in def:least-upper-bound, from 8, 17.26

    17.28. not c ≤ c − δ
           inequalities, from 17.24

    17.29. c ≤ c − δ. not c ≤ c − δ.
           lines 17.27, 17.28

    17.30. f(c) = 0
           thm:from-contradiction P := c ≤ c − δ, Q := f(c) = 0, from 17.29

18. There is c ∈ [a, b] with f(c) = 0.
    exhibit, from 13, 17
```

---

## Database items

| symbols | what they are | set.mm |
|---|---|---|
| [a, b] | closed interval | cicc |
| f : D → ℝ, f(x) | function, application | wf, cfv |

| pointer | statement | set.mm |
|---|---|---|
| def:interval | Let a ∈ ℝ, b ∈ ℝ. x ∈ [a, b] ↔ x ∈ ℝ and a ≤ x and x ≤ b. | elicc2 |
| thm:interval-real | Let a ∈ ℝ, b ∈ ℝ. Then [a, b] ⊆ ℝ. | iccssre |
| thm:subset-transitive | Let X ⊆ Y. Let Y ⊆ Z. Then X ⊆ Z. | sstr |
| def:function | Let f : D → ℝ. For every x ∈ D, f(x) ∈ ℝ. | ffvelcdm |
| def:continuous-on | f is continuous on D ↔ for every c ∈ D, for every ε ∈ ℝ with ε > 0, there is δ ∈ ℝ with δ > 0 and for every x ∈ D, if \|x − c\| < δ then \|f(x) − f(c)\| < ε. | cncfi, elcncf2 |
| def:upper-bound | u is an upper bound of S ↔ for every s ∈ S, s ≤ u. | (ub as in df-sup) |
| def:least-upper-bound | c is a least upper bound of S ↔ c is an upper bound of S, and for every u ∈ ℝ, if u is an upper bound of S then c ≤ u. | df-sup, suprub, suprleub |
| thm:completeness | Let S ⊆ ℝ. Assume there is s ∈ S. Assume there is an upper bound of S. Then there is c ∈ ℝ with c a least upper bound of S. | sup2, ax-pre-sup |
| thm:trichotomy | Let x ∈ ℝ. Then x < 0 or x = 0 or 0 < x. | lttri4, 0re |
| thm:from-contradiction | If P and not P then Q. | pm2.21 |
| thm:point-right | Let c ∈ ℝ, b ∈ ℝ, δ ∈ ℝ. Assume c < b. Assume δ > 0. Then there is x ∈ ℝ with c < x, x ≤ b, and x − c < δ. | (a lemma to prove: take the smaller of b and c + δ/2, then the midpoint) |
| thm:abs-difference-lt | Let x, c, δ ∈ ℝ. \|x − c\| < δ ↔ c − δ < x and x < c + δ. | absdiflt, abslt |
| thm:real-closure | Let x ∈ ℝ, y ∈ ℝ. Then x + y ∈ ℝ. x − y ∈ ℝ. | readdcl, resubcl |
| thm:abs-bounds | from the triangle inequality pilot | leabs, absneg |
| thm:intermediate-value | proved above | ivth (general form) |

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
   thm:from-contradiction, "if P and not P then Q", so that every case
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
   "S ⊆ ℝ, from thm:set-builder-subset, thm:interval-real", citing two
   theorems as if they were lines. They are now steps 3 and 4, each
   citing its theorem, and step 5 joins them.
5. **Numbering reaches four levels.** The deepest step is 17.25.5.10. The
   first draft went one level deeper and used two improvised devices to
   cope; both are gone. Four levels is the honest depth of a fix inside a
   case inside a cases block with a contradiction inside it. The numbers
   are long, and that is a viewer problem before it is a text problem.
6. **Completeness of ℝ is above the ceiling and is a pointer.** Step 8
   cites thm:completeness. A school reader has never seen it, and
   READERS.md's answer is that the pointer leads to a definition and a
   statement, both readable. Whether the *proof* of completeness is ever
   in the corpus is a question about the foundation, since in set.mm it
   is an axiom of the real numbers, ax-pre-sup.
7. **A lemma that exists only to avoid min.** thm:point-right is cited to
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

Numbers, for the record: 69 numbered steps, 2 requires lines. set.mm's
ivth has 16 essential steps on top of ivthle's 69, but the continuity in
set.mm is topological and its unfolding to ε and δ is elsewhere.
