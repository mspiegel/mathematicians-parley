# Pilot: a set with n elements has 2ⁿ subsets

Seventh pilot, first draft. Its purpose is a counting argument: what "has
n elements" means and how a count is carried through a construction.
Number 52 on Wiedijk's list, `hashpw` in set.mm, stated in Hammack's
chapter on sets and proved in his chapter on induction.

Provisional forms, listed in the batch report: cardinality written |A|
with `def:card`; induction from 0, written `induction on n starting at
0, from H`; `define` inside a block; ∪, ∖, ∩, ∅ and {a}.

The counting facts the argument rests on are cited, not proved: removing
an element lowers the count by one, disjoint unions add, bijections
preserve the count, and the power set splits by whether a subset contains
a chosen element.

---

## Theorem subsets-count

```
theorem subsets-count
  let n ∈ ℕ₀                                                          (H1)
  let A be a set                                                      (H2)
  assume |A| = n                                                      (H3)
  then |𝒫A| = 2^n

1.  For every set X, if |X| = n then |𝒫X| = 2^n.
    induction on n starting at 0, from H1

    base
    1.1.  For every set X, if |X| = 0 then |𝒫X| = 2^0.
          fix
          let X be a set                                              (K1)
          assume |X| = 0                                              (C1)

          1.1.1.  X = ∅
                  thm:card-zero, from K1, C1

          1.1.2.  𝒫X = 𝒫∅
                  substitute X = ∅ (line 1.1.1)

          1.1.3.  𝒫∅ = {∅}
                  thm:powerset-empty

          1.1.4.  |{∅}| = 1
                  thm:card-singleton x := ∅

          1.1.5.  1 = 2^0
                  arithmetic

          1.1.6.  𝒫X = {∅}
                  calculation
                    𝒫X = 𝒫∅        1.1.2
                       = {∅}       1.1.3

          1.1.7.  |𝒫X| = 1
                  substitute 𝒫X = {∅} (line 1.1.6) into line 1.1.4

          1.1.8.  |𝒫X| = 2^0
                  calculation
                    |𝒫X| = 1        1.1.7
                         = 2^0      1.1.5

    step
    1.2.  For every k ∈ ℕ₀, if (for every set X, if |X| = k then |𝒫X| = 2^k)
          then (for every set X, if |X| = k + 1 then |𝒫X| = 2^(k + 1)).
          fix
          let k ∈ ℕ₀                                                  (K2)
          assume for every set X, if |X| = k then |𝒫X| = 2^k          (IH)

          1.2.1.  For every set X, if |X| = k + 1 then |𝒫X| = 2^(k + 1).
                  fix
                  let X be a set                                      (K3)
                  assume |X| = k + 1                                  (C2)

                  1.2.1.1.  a ∈ X
                            obtain a: thm:card-nonempty, from K3, C2

                  1.2.1.2.  |X ∖ {a}| = k
                            thm:card-remove, from K3, 1.2.1.1, C2

                  1.2.1.3.  |𝒫(X ∖ {a})| = 2^k
                            instantiate X := X ∖ {a} in IH, from 1.2.1.2
                            requires X ∖ {a} is a set: thm:difference-set, from K3

                  define T := {S ∪ {a} : S ∈ 𝒫(X ∖ {a})}                 (D1)

                  1.2.1.4.  There is a bijection from 𝒫(X ∖ {a}) to T.
                            thm:add-element-bijection, from D1

                  1.2.1.5.  |T| = 2^k
                            thm:card-bijection, from 1.2.1.3, 1.2.1.4

                  1.2.1.6.  𝒫(X ∖ {a}) ∩ T = ∅
                            thm:powerset-split-disjoint, from 1.2.1.1

                  1.2.1.7.  𝒫X = 𝒫(X ∖ {a}) ∪ T
                            thm:powerset-split, from K3, 1.2.1.1

                  1.2.1.8.  |𝒫(X ∖ {a}) ∪ T| = 2^k + 2^k
                            thm:card-disjoint-union, from 1.2.1.3, 1.2.1.5, 1.2.1.6

                  1.2.1.9.  |𝒫X| = 2^k + 2^k
                            substitute 𝒫X = 𝒫(X ∖ {a}) ∪ T (line 1.2.1.7) into line 1.2.1.8

                  1.2.1.10.  2^k + 2^k = 2^(k + 1)
                            algebra

                  1.2.1.11. |𝒫X| = 2^(k + 1)
                            calculation
                              |𝒫X| = 2^k + 2^k      1.2.1.9
                                   = 2^(k + 1)      1.2.1.10

2.  |𝒫A| = 2^n
    instantiate X := A in line 1, from H2, H3
```

---

## Database items

| symbols | what they are | set.mm |
|---|---|---|
| \|A\| | number of elements | chash |
| ∅, {a}, ∪, ∖, ∩ | empty set, singleton, union, difference, intersection | c0, csn, cun, cdif, cin |
| {S ∪ {a} : S ∈ Y} | set-builder by image | cmpt / crab with a witness |

| pointer | statement | set.mm |
|---|---|---|
| def:card | Let A be a set, n ∈ ℕ₀. \|A\| = n ↔ there is a bijection from {i ∈ ℕ : i ≤ n} to A. | hashen, hashfz1 |
| thm:card-zero | Let X be a set. Assume \|X\| = 0. Then X = ∅. | hasheq0 |
| thm:powerset-empty | 𝒫∅ = {∅} | pw0 |
| thm:card-singleton | \|{x}\| = 1 | hashsng |
| thm:card-nonempty | Let X be a set. Assume \|X\| = k + 1. Then there is a ∈ X. | hashnncl, n0 |
| thm:card-remove | Let X be a set, a ∈ X. Assume \|X\| = k + 1. Then \|X ∖ {a}\| = k. | hashdifsn |
| thm:difference-set | Let X be a set. Then X ∖ {a} is a set. | difexg |
| thm:add-element-bijection | Let X be a set, a with not a ∈ X... the map S ↦ S ∪ {a} is a bijection from 𝒫X to {S ∪ {a} : S ∈ 𝒫X} | (to be found or proved) |
| thm:card-bijection | Let \|X\| = m and g a bijection from X to Y. Then \|Y\| = m. | hashen |
| thm:powerset-split | Let X be a set, a ∈ X. Then 𝒫X = 𝒫(X ∖ {a}) ∪ {S ∪ {a} : S ∈ 𝒫(X ∖ {a})}. | (to be found or proved; pwdif and pwsn are nearby) |
| thm:powerset-split-disjoint | the two parts above are disjoint | (to be proved) |
| thm:card-disjoint-union | Let \|X\| = m, \|Y\| = n, X ∩ Y = ∅. Then \|X ∪ Y\| = m + n. | hashun |
| thm:subsets-count | proved above | hashpw |

---

## What the pilot reveals

1. **Induction from 0.** The claim is about n ∈ ℕ₀, and the base case is
   P(0). Decided: the starting point is written on the method line,
   `induction on n starting at 0`, in every induction; see the geometric
   series pilot. set.mm has nnind, nn0ind and the general uzind.
2. **The induction is over a "for every" sentence.** P(n) is "for every
   set X, if |X| = n then |𝒫X| = 2^n", so the step case is a fix inside
   a fix, and the proof reaches numbering depth 1.2.1.11. Textbooks
   induct on n "for a set with n elements" without saying that the
   statement being inducted on is universally quantified over sets; the
   language has to say it.
3. **Quantifying over sets.** "for every set X" and `let X be a set`
   inside a block: the same form as the theorem hypothesis in the Cantor
   pilot, now inside a proof. In set.mm this is `A. x` with x a set
   variable; the class/set distinction READERS.md hides is what makes
   "for every set" mean anything.
4. **The counting content is all in cited lemmas.** Eight theorems are
   cited and none proved. Three of them, add-element-bijection,
   powerset-split and its disjointness, have no ready set.mm label and
   would be new. The readable proof is short because the database is
   asked to be large. That is the trade GOALS.md anticipated, but this is
   the first pilot where the cited lemmas are the whole argument.
5. **A bijection is a cited fact, not a named map.** Step 1.2.1.4 states
   "there is a bijection from 𝒫(X ∖ {a}) to T" by citing the theorem, and
   1.2.1.5 uses that line. The first draft put the theorem in `from`
   directly; decided against, since `from` lists lines only. The language
   has no way yet to name a function built on the spot, as `define` names
   a set; `define g := (S ↦ S ∪ {a})` would be the analogue and is not
   used here.
6. **"X ∖ {a} is a set" is a requires line.** At 1.2.1.3 the induction
   hypothesis is instantiated at X ∖ {a}, whose `let X be a set`
   hypothesis has to be discharged. It is the first requires line whose
   fact is set-existence, which set.mm proves with difexg and READERS.md
   wants hidden. As a requires line it is exactly a dull fact.

Numbers, for the record: 24 numbered steps, 1 requires line. set.mm's
hashpw has 25 essential steps.
