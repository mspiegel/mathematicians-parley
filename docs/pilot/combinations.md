# Pilot: the number of combinations

Theorem 39 of `SELECTION.md`, Wiedijk #58, set.mm's `hashbc`:

  a set with n elements has C(n, k) parts with k elements, for every k ∈ ℤ.

By induction on the size: take one element a out of the set, and split the
parts with k elements by whether they hold a. Those that leave a out are
the parts of the rest with k elements; those that hold a are the parts of
the rest with k − 1 elements, each with a put back. Pascal's rule adds the
two counts.

---

## Theorem combinations

The proof is `proofs/wiedijk/combinations.proof`: `choose-from-none` (the
base), `add-element-bijection`, `add-element-disjoint` and `choose-split`
(the step's three facts about sets), and `combinations`. Each elaborates
to `corpus/elaboration/proofs/wiedijk/combinations/`, assumes nothing and
verifies.

---

## Rendered view

**Theorem.** Let n ∈ ℕ₀, k ∈ ℤ and A a set with |A| = n. Then
|{S ⊆ A : |S| = k}| = C(n, k).

*Proof.* By induction on m, for every set X with |X| = m and every j ∈ ℤ,
|{S ⊆ X : |S| = j}| = C(m, j).

1. m = 0: X = ∅. If j = 0, the one part of X is ∅, which has 0 elements,
   so the family is {∅} and has 1 = C(0, 0) member. If j ≠ 0, no part of ∅
   has j elements, so the family is empty, and C(0, j) = 0 since j is not
   in {0, …, 0}.
2. m + 1: X has an element a, and X ∖ {a} has m elements. Let U be the
   parts of X ∖ {a} with j elements, V those with j − 1, and W the sets
   T ∪ {a} for T ∈ V.
   - |U| = C(m, j) and |V| = C(m, j − 1) by the hypothesis.
   - T ↦ T ∪ {a} is one-to-one on V, since a is in no T: |W| = |V|.
   - U and W share nothing: every set in W holds a, no set in U does.
   - Every part R of X with j elements is in U or in W: if a ∉ R, R ⊆
     X ∖ {a}; if a ∈ R, then |R| ≥ 1, so j − 1 ∈ ℕ₀, |R ∖ {a}| = j − 1,
     and R = (R ∖ {a}) ∪ {a}. Conversely every set in U or W is a part of X
     with j elements; |T ∪ {a}| = |T| + 1 since T is finite and a ∉ T.
   - So the family has C(m, j) + C(m, j − 1) = C(m + 1, j) members, by
     Pascal's rule. ∎

---

## Database items

In `corpus/stdlib/counting.records`, each mundane: `card-finite`
(`hashvnfin`), a set whose size is a whole number is finite;
`card-at-least-one` (`hashge1`), a set that is not empty has at least one
element. The proof also cites `card-add-one` (`hashunsng`), which the
Ramsey and Erdős–Szekeres pilots added too.

In `corpus/stdlib/sets.records`, each mundane: `part-builder-empty`
(`rabeq0`), the parts of X with a property are none exactly when no part
has it; `empty-subset` (`0ss`).

`mun:stdlib/functions/added-elements-are-new` now says its sets with a
added are outside any set Z, not only outside the set Y they are built
from; the subsets proof's citation is unchanged and builds the same file.

---

## What the pilot reveals

1. **A part of a set is said two ways, and a substitution reads both.**
   `let R ⊆ X` holds R ∈ 𝒫X; putting X = ∅ into it, a reader writes
   R ⊆ ∅. The checker's substitute compared only the line's own form, and
   the build put the equation into it only as written. Both now offer the
   other form of a part as well (`rules::PARTS`)
   (`tests/elaborator/a-part-substituted-into.proof`).
2. **A define says its equation to a substitute.** `substitute F = {…}
   (D1) into line 3` takes the equation from the define, as `SYNTAX.md`
   allows and the checker accepted; the build looked for it among the lines
   in scope only. It now proves it from the define as a step citing the
   define would (`tests/elaborator/a-define-put-into-a-line.proof`).
3. **A pair may name a define.** `mun:image-of-injection Y := F, from D1, 1`
   was accepted by the checker, which reads F as what it names, and the
   build made the target's map over the name F while the claim wrote the
   set out. The build now fills a value the checker read through a define
   with what it read (`tests/elaborator/a-pair-naming-a-define.proof`). The
   proof itself writes no pair, since matching fixes Y.
4. **The family is a part-builder with a size in it.** {S ⊆ X : |S| = j}
   reads S as a set from its binder: a letter bound over a set written as
   a term takes its sort from that term (the Erdős–Szekeres pilot, point 3).
5. **The base case is a case split on j.** C(0, j) is 1 or 0, and the
   family {∅} or ∅. Each set equation is two inclusions; the empty one is
   `part-builder-empty`, the reader's "no part of ∅ has j elements".

Numbers, for the record: 116 numbered steps over five theorems, 5 requires
lines. set.mm's `hashbc` is proved by induction on a finite set
(`findcard2`), with Pascal's rule likewise.
