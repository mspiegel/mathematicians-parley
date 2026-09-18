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

The skeleton is `proof/subsets.proof`. The items it cites are in `db/`.

---

## Database items

This pilot introduced `def:card`, `thm:card-zero`, `thm:powerset-empty`,
`thm:card-singleton`, `thm:card-nonempty`, `thm:card-remove`,
`thm:difference-set`, `thm:add-element-bijection`, `thm:card-bijection`,
`thm:powerset-split`, `thm:powerset-split-disjoint`,
`thm:card-disjoint-union` and `thm:subsets-count` in `db/items.db`, and the
cardinality, set-operation and set-image rows in `db/notation.db`. The table
that used to stand here was merged into those files; `DATABASE.md` records
what the merge decided.

Three of these are open items, as finding 4 below says. Two of the three had
rows that were not statements: `thm:add-element-bijection`'s row trailed off
mid-sentence and `thm:powerset-split-disjoint`'s read only "the two parts
above are disjoint". `db/items.db` carries the merge's reading of each, which
should be checked before either is proved.

`def:set-image` was named in `SYNTAX.md` for the `{E(s) : s ∈ Y}` notation
this pilot uses, and no table carried a row for it. The merge added one.

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

Numbers, for the record: 25 numbered steps, 3 requires lines. set.mm's
hashpw has 25 essential steps.
