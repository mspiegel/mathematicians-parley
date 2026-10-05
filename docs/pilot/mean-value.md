# Pilot: the mean value theorem

Theorem 19 of `SELECTION.md`, set.mm's `mvth`, Wiedijk #75:

  for a < b and f : [a, b] → ℝ continuous on [a, b] and differentiable on
  (a, b), there is c ∈ (a, b) with f′(c) = (f(b) − f(a))/(b − a).

The source is ProofWiki's "Mean Value Theorem", proof 1: add to f the line
h·x with h = −(f(b) − f(a))/(b − a), so that the sum F takes one value at a
and at b, and Rolle's theorem gives a point where F′ is 0. set.mm's `mvth`
proves it otherwise, as the case g(x) = x of Cauchy's mean value theorem
(`cmvth`), so the elaborated proof is the corpus's own, citing `rolle`.

---

## Theorem mean-value

The proof is `proofs/mean-value.proof`, one theorem with two defines. It
elaborates to `corpus/elaboration/proofs/mean-value/mean-value.mm`, assumes
nothing, and verifies.

Numbers: 33 numbered steps at the top and 6 inside blocks. Steps 1 to 5 say
what is real; 6 to 11 what g and F are and that both are real-valued; 12 to
17 apply the sum rules; 18 to 25 show F(a) = F(b); 26 is Rolle's theorem;
27 to 33 solve for f′(c). f(a) and f(b) are real by H4 with steps 1 and 2,
which the steps needing it cite (`READERS.md`, a function's type cited for
its values).

---

## Rendered view

Let a < b be real and f : [a, b] → ℝ continuous on [a, b] and
differentiable on (a, b).

**Theorem.** There is c ∈ (a, b) with f′(c) = (f(b) − f(a))/(b − a).

*Proof.* Let g(x) = ((f(a) − f(b))/(b − a))·x and F(x) = f(x) + g(x) for
x ∈ [a, b]. Both are real-valued. g is continuous and differentiable, with
derivative (f(a) − f(b))/(b − a), so F is continuous on [a, b] and
differentiable on (a, b), with F′ = f′ + g′.

F(a) = F(b), since

  f(a) + ((f(a) − f(b))/(b − a))·a = f(b) + ((f(a) − f(b))/(b − a))·b.

By Rolle's theorem there is c ∈ (a, b) with F′(c) = 0, that is
f′(c) + (f(a) − f(b))/(b − a) = 0, and so
f′(c) = (f(b) − f(a))/(b − a). ∎

---

## Decisions made with the reader

1. **f′ is notation** for the derivative of f, and f′(x) is it applied to x.
   The sort of the stem decides: where f is a function and nothing declares
   f′, it is the derivative, and c′ and P′ stay names. f′ alone and f′′ read
   the same way.
2. **(a, b) is the open interval,** and "f is differentiable on (a, b)"
   says the derivative is defined at every point of it,
   `( A (,) B ) C_ dom ( RR _D F )`, as a textbook means it of a function
   differentiable on a larger set as well. set.mm's `rolle` and `mvth` ask
   the derivative be defined on exactly (a, b); for f on [a, b] the two
   agree, since no derivative is taken at an end (`gdvdmicc`), and `grolle`
   is Rolle's theorem in the page's form.
3. **Rolle's theorem and the sum rules are named theorems:** continuity of
   a sum and of a line, the derivative of a sum and of a line. A textbook
   cites each. That a real function's derivative is real is mundane.
4. **The types are steps.** That g and F map [a, b] into ℝ is proved once
   each, by `function-into` from a line saying every value is real, and
   each citation of a rule asks it in a requires line citing that step.
   The other way, a requires line citing the define and the lines its rule
   needs, would have broken the rule that a requires line cites one thing,
   and said the same two facts nine times.

---

## What the pilot reveals

1. **A citation says which defined function it binds.** The checker reads
   an item's `let g : D → ℝ` as a declaration, so it asks for nothing. Where
   the citation fills g with a function the proof defines, `g := g`, the
   type is a fact the kernel needs, and a requires line giving it is one the
   item asks. The checker takes the function from the written instantiation
   rather than from matching the claim, since an `obtain` claims its
   witness and not the item's conclusion.
2. **A lemma letter only the hypotheses hold needs a `with`.** `gdvlin`'s
   D and M, `gdvre`'s A and B, and the D, F and G of the sum rules appear in
   no conclusion, so the elaborator would take the first fact that fits.
   The records say which they are, `with M := m`, as completeness says its
   witness.
3. **One target to a sentence.** The derivative rules conclude two
   sentences, and each has a lemma of its own, as completeness does. The
   sum's both read off one point (`gdvaddbr`), the line's off its
   derivative restricted to U (`gdvlinres`).
4. **`membership` reads a define as its rule, all the way down.** F(x) is
   read as f(x) + slope·x, so the requires lines of step 8 name the
   slope and x, which F's rule never writes, and the step cites the
   defines of F and g.
5. **An `inequalities` defect.** A claim b − a ≠ 0 from a < b was given the
   proof of b ≠ a, which the build accepted and the verifier refused. The
   route now takes only a claim that names the bound's two sides, and the
   order proves the rest. No earlier proof wrote the shape.
6. **The library proves the sum rules below the readable layer, on any
   D ⊆ ℝ.** The derivative rules say f on D is differentiable on a set U.
   A sum is differentiable at each point both its parts are (`dvaddbr`), so
   U is any set; a line is differentiable only where a neighbourhood lies
   in D, so its rule asks U be open, a notation of its own. The mean value
   theorem cites them with D := [a, b] and U := (a, b), and says (a, b) is
   open and inside [a, b] by two mundane items. `addcncf`, `mulcncf`,
   `dvmptcmul` and `dvres` do the rest, in `src/proofs/stdlib/calculus.rs`.

---

## Status

Checker clean, elaborated with nothing assumed, verified.
