# Pilot: Euler's theorem

Theorem 23 of `SELECTION.md`, Wiedijk #10:

  if gcd(a, n) = 1 then a^φ(n) ≡ 1 (mod n).

The Metamath 100 page lists `eulerth`. ProofWiki's "Euler's Theorem (Number
Theory)" gives only the proof by Lagrange's theorem in the group of units
modulo n, which asks the reader for that group. The proof here is the
rearrangement argument instead, the one `eulerth` itself follows and the one
an elementary number theory course gives: multiplying each remainder coprime
to n by a, and reducing, gives the same remainders in another order.

---

## Theorem euler

The proof is `proofs/euler.proof`, one theorem of 29 numbered steps, 60 with
those inside blocks. It elaborates to `corpus/elaboration/proofs/euler/`,
assumes nothing, and verifies.

---

## Rendered view

**Theorem (Euler).** Let n ∈ ℕ and a ∈ ℤ with gcd(a, n) = 1. Then
a^φ(n) ≡ 1 (mod n).

*Proof.* Let S be the remainders r ∈ {0, …, n − 1} with gcd(r, n) = 1, and
f(r) = (r·a) mod n for r ∈ S. Each f(r) is in S: r·a is coprime to n, and so
is its remainder. If f(s) = f(t) then s·a ≡ t·a (mod n), and a is coprime to
n, so s ≡ t (mod n), and two remainders that are congruent are equal. So f is
a one-to-one map of the finite set S to itself, and the product of the f(r)
is the product of the r. Each r·a ≡ f(r) (mod n), so

  a^|S| · ∏ r = ∏ r·a ≡ ∏ f(r) = ∏ r (mod n),

and |S| = φ(n). Write P for ∏ r. Then n divides a^φ(n)·P − P = (a^φ(n) − 1)·P,
and P is coprime to n, being a product of numbers coprime to n, so n divides
a^φ(n) − 1. ∎

---

## Decisions made with the reader

1. **The rearrangement argument, not Lagrange's theorem.** The reader's
   choice: it needs only congruences and a finite product, where the other
   needs the group of units.
2. **S is the remainders 0 to n − 1, not 1 to n − 1.** For n = 1 the only
   remainder is 0, gcd(0, 1) = 1, and φ(1) = 1, so S is never empty and the
   statement holds for every n ∈ ℕ without a case. It is also set.mm's
   `dfphi2`.
3. **φ is a named definition** with the count as its value, as σ is.

---

## What the pilot reveals

1. **A hole between literals ended at the first of them.** In `x·c ≡ f(x)
   (mod n)` the middle hole of `_ ≡ _ (mod _)` stopped at the bracket of
   f(x), taking it for the start of `(mod n)`. A hole now ends where every
   literal after it follows, `( mod` here (`GRAMMAR.md`).
2. **A defined function standing alone stayed a name, while applied it was
   its rule.** With S a define, the claim `f : S → S` wrote S out and kept
   f, and the line it came from, every f(r) in S, wrote f(r) out; neither
   met the other. A defined function standing alone is now its rule, so all
   three readings agree (`SYNTAX.md`). The checker's second reading of each
   fact, as written, existed only to bridge that gap and is gone.
3. **A function said of was read as a function applied.** The matcher took
   any notation whose first hole is a function to apply it, so `E is a
   function on X` and `E : X → Y` read E's rule at X once E stood for one.
   A notation applies its first hole only where its second takes what that
   applies to, as `f(x)` and `P(x)` do, which is read from the sorts. Two
   planted cases check that the reading still refuses what the lines do not
   say.
4. **A define's domain named by another define was refused.** `define f(r)
   := …, for r ∈ S` gives f on S written out, and the claim says S. The
   elaborator now carries one to the other in standard form, through
   `fneq2d`, a congruence row it lacked (`ELABORATION.md`).
5. **Distinct-variable conditions among classes sent a lemma to the wrong
   scope.** The new `proved.mm` group first held every class variable apart
   from every other. The elaborator picks the scope where a lemma's
   conditions hold, found none inside the block, and settled the lemma's
   hypotheses at the theorem's outer scope, where the block's lines are not.
   The group now holds bound letters apart and nothing else.
6. **set.mm has no "a product of numbers coprime to n is coprime to n".**
   `coprmprod` asks the factors to be coprime to each other as well, which
   remainders are not. `gfprodrp` proves it by induction on the finite set
   (`findcard2d`), a factor at a time.
7. **The finish is by divisibility.** A substitution rewrites every
   occurrence, so ∏ r could not be written 1·∏ r on one side only, to cancel
   it as a common factor. The proof does as a textbook does instead: n
   divides (a^φ(n) − 1)·P and is coprime to P, so it divides a^φ(n) − 1, by
   the general form of Euclid's lemma, `coprime-divides` (`coprmdvds`).
8. **A restated item may not use one letter for two binders.** The items
   for products first wrote x for both the "for all" and the product, and
   their lemmas hold those letters apart, so the restated test failed; the
   "for all" now binds y.
9. **What is still a limit.** The `membership` method does not reach a
   product over a defined set, so steps 25 and 26 cite `int-real` and
   `int-closure` for ∏ r ∈ ℝ and a^φ(n)·∏ r ∈ ℤ.
