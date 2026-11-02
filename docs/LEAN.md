# The Lean backend

`parley build lean` writes the corpus as Lean files over Mathlib, beside the
Metamath files `parley build metamath` writes. Both start from the checker's
record of the page (`GOALS.md` decision 19), and neither reads what the other
wrote. Two backends proving one page against two libraries check each other
(`GOALS.md`, "Comparison with Lean 4").

```
parley build lean [<name>]
```

writes every file and says which changed. Mathlib itself is not committed:
`lean/` holds the Lake project, pinned by `lakefile.toml`, `lean-toolchain`
and `lake-manifest.json`, and `lake exe cache get` in `lean/` downloads
Mathlib into `lean/.lake/`, which git ignores. The build needs no Lean
installed; the gate does.

## What the build writes

- `lean/Parley/Items/<module>.lean`: each library item whose `lean-proof` is
  Mathlib's proof or a bridge, one Lean theorem for each sentence it concludes. The statement is printed
  from the record as the checker read it, and the proof is the `lean-proof` field's
  entry for that sentence. `def:divides` is
  `theorem def_divides (d n : ℤ) : d ∣ n ↔ ∃ k : ℤ, n = d * k := Iff.rfl`.
- `lean/Parley/<path>.lean`: each theorem the build covers, one file each,
  importing the items and theorems it cites.
- `lean/Parley.lean`, which imports them all.

The Lean bridges are written by hand in `corpus/lean-bridges/`, a Lake
library of their own that every generated file imports, and the build never
touches them. `Tactics.lean` holds the tactics the files share (below);
`Counting.lean` and `Sums.lean` hold the bridges. A bridge states its item
exactly as the build writes it, with the item's letters and hypotheses in
the same order, so a record names it in full, `lean-proof
lean-bridges/counting/pascal`, and the build writes
`LeanBridges.Counting.pascal n k`. A generated file the build no longer
makes is removed.

## Which theorems are in

A theorem is in the Lean build when every notation its page uses, every
library function it applies and every item it cites has a Lean form: a
notation with a `lean-builds` field; a record whose `lean-proof` is Mathlib's
proof, a bridge or `none`, or names a Parley proof that is itself in; a
function whose definition has a `lean-builds` field; or a theorem of the
corpus that is itself in. A record whose `lean-proof` is `not yet
implemented` keeps out every theorem that cites it. A theorem is in, too, only
when
every letter it writes is a number, the one sort the writer gives a Lean type
to so far. Nothing lists the theorems; the build grows as fields are added. A
theorem left out is printed with what keeps it out, `it writes notation
set-operations, which has no lean-builds field`. A theorem that is in and that the
writer cannot write, or Lean refuses, is a gap of the Lean build and the gate
is red.

## Number types

On the page every number is a number. In Lean each has a type, and three
traps follow: subtraction in ℕ stops at 0, division in ℤ rounds down, and
Lean's ℕ starts at 0 where the page's starts at 1.

- A letter keeps its own type. `let n ∈ ℕ` is `(n : ℕ) (H1 : 0 < n)`;
  `let n ∈ ℕ₀` is `(n : ℕ)`; `let a ∈ ℤ` is `(a : ℤ)`, and so for ℚ, ℝ, ℂ;
  `let k ∈ {1, …, n}` is `(k : ℤ) (H1 : k ∈ Finset.Icc 1 n)`.
- Each formula is computed in the least of ℤ, ℚ, ℝ and ℂ that holds every
  letter and operation in it, never in ℕ. The two sides of a relation share
  one type, and a narrower letter is cast up. `7 divides 4a` is `7 ∣ 4 * a`;
  `f(n) = ((−1)^n·(2n − 1) + 1)/4` with n ∈ ℕ is written in ℚ.
- A power whose exponent is no natural number, `x^(−1)`, is Lean's integer
  power, taken in ℚ at least.
- A claim of numerals alone reached from lines is written in the type of
  those lines, and a cited line of a narrower type than the claim is cast up
  to the claim's type before it is used.
- The index of a sum or product, and its ends, are in ℤ, so that a range
  means what the page says: 0 to n − 1 at n = 0 is empty.
- A notation of number theory takes the type it is about: `divides`, `mod`
  and congruence take ℤ, `prime` and factorial take ℕ. A term too wide for
  it is not cast down. Where a line has said the term is an integer, `(N −
  1)/2 ∈ ℤ`, the integer that line gives is used; otherwise the writer
  reports the term.
- `t ∈ ℤ` for a rational t is `∃ m : ℤ, (m : ℚ) = t`; a membership the
  letter's type already gives says nothing and is left out.

An item whose letters the record puts in ℂ or ℝ, and whose sentence uses
only arithmetic, order and connectives, is a theorem about any commutative
ring `K`: a field where it divides, ordered where it orders, as Mathlib
states such facts. A citation applies it in the citing claim's own type.

## Fields

A notation's `lean-builds` field has one entry for each of its patterns, set
apart by ` ; `: what each hole takes, what it yields, and the Lean text.

```
lean-builds α, α → α: _1 + _2 ; α, α → α: _1 - _2
lean-builds α, α → α: _1 * _2 ; α≥ℚ, α≥ℚ → α≥ℚ: _1 / _2
lean-builds ℤ, ℤ → Prop: _1 ∣ _2
```

`α` is the formula's type and `α≥ℚ` that type raised to ℚ at least. An entry
`-` is a pattern the parser folds into another. An item's `lean-proof` field
has one Lean proof for each sentence it concludes, a term or `by …`. A record
the standard library proves on the page, in `corpus/stdlib/<subject>.proof`,
gives either a Mathlib proof, as any item does, or `on the page`, which
writes the page's proof in Lean, as `metamath-proof` does for the Metamath build. A library
function's definition says what the function is in Lean with `lean-builds`,
a template of the same form, beside `metamath-builds`:
`lean-builds ℤ, ℤ → ℕ: Int.gcd _1 _2`.

## What each method is

Each step is a `have` whose type is its claim. Tactics see every line above
them, as Mathlib's own proofs do.

| method | Lean |
|---|---|
| a citation | the item's theorem at the citation's values, its hypotheses by `parley_side`; `.mp` or `.mpr` for a definition |
| obtain | `obtain ⟨k, …⟩ :=` the item's or the line's "there is" |
| exhibit | `⟨w, by parley_side⟩` |
| instantiate | the line at the values given, a letter given none at the block's letter |
| algebra | `ring`; from cited lines, `linear_combination` with the multipliers the method's decision finds |
| arithmetic, real arithmetic | `parley_arith` |
| inequalities, transitivity, antisymmetry, rows | linear arithmetic, `parley_side` |
| membership, restate, join, inspection | `parley_side`; an integer the cited lines give, as a witness |
| substitute | `parley_subst`, the equation either way round; rows one at a time |
| calculation | `calc`, each link by its reason |
| proof | `intro` |
| contradiction | `by_contra`, the suppose line from it |
| cases | `rcases` on the line that says "or" |
| both directions | `constructor` |
| induction | from 0 over ℕ₀, Lean's induction; from 1 over ℕ, `Nat.le_induction` |

A requires line is a `have` proved by its own reason, and a define is
`set m : ℝ := … with D1`. A define the statement is read with is written out
in Lean's statement and named again by `set` at the head of the proof.

## The gate

- The eighth stage builds every Lean file afresh in memory and compares it
  with the file in the tree.
- The ninth runs `lake build` in `lean/` and says each error against the
  theorem, the step and the line of the proof file it was written for. It
  then reads back each statement Lean accepted, through lean4export: the
  statement does the page's arithmetic, as many operations of each kind,
  none in a type that computes otherwise, and it rests on no axiom beyond
  Lean's own (`propext`, `Classical.choice`, `Quot.sound`), so a `sorry` is
  red. Without Mathlib downloaded the stage is red and says how to get it.
