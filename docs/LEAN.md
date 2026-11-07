# The Lean backend

`parley build lean` writes the corpus as Lean files over Mathlib, beside the
Metamath files `parley build metamath` writes. Both start from the checker's
record of the page (`GOALS.md` decision 19), and neither reads what the other
wrote. Two backends proving one page against two libraries check each other
(`GOALS.md`, "Comparison with Lean 4").

The writer follows the Metamath backend's strategy wherever Lean allows it
(`GOALS.md` decision 20). Each term has one Lean form. What the writer needs
to know about a term, that it is an integer or at least 0, it takes from the
page's lines and from the checker's record, never from a reading of its own.
Where Lean's types force a difference, this document says so where it
describes it: a rational's membership in ℤ as a witness, `∃ m : ℤ, (m : ℚ) =
t`, or a real power of a base not shown at least 0 as the complex principal
value.

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
touches them. `Tactics.lean` holds `parley_side` and `parley_norm`, which
nearly every file calls; each other family of tactics is a module of its own
(`AlgebraTactics`, `SubstTactics`, `OrderTactics`, `PowerTactics`,
`ComplexTactics`, `ArithTactics`, `SetTactics`, `RealTactics`), imported
only by the files that call it, since a change to a module rebuilds every
file that imports it. `Counting.lean` and `Sums.lean` hold the bridges. A bridge states its item
exactly as the build writes it, with the item's letters and hypotheses in
the same order, so a record names it in full, `lean-proof
lean-bridges/counting/pascal`, and the build writes
`LeanBridges.Counting.pascal n k`. A generated file the build no longer
makes is removed.

## How a file is made

The writer builds each file as a tree, not as text (`src/lean/doc/`). Every
term carries its Lean type, and every constant and tactic carries its source:
Mathlib, a bridge module or an item module. The printer is the one place text
is made. A file's imports are read from the tree: the bridge and item modules
it names, and for each constant, term and tactic it uses, the Mathlib modules
Lean gives. Lean is asked once per name, by `lean/scripts/ModulesOf.lean`. The
answers are kept in `lean/mathlib-modules.jsonl`, whose first line names the
Mathlib revision and the hash of the script they came from, and the build asks
again for any name that is missing or out of date.

Where a citation's item, with its letters given, meets the line it proves, the
two trees are compared (`doc::forms`). Casts are first pushed down, as
`push_cast` pushes them, and a relation in a narrower type is cast up to the
other's. What is left is a form the writer chose: a count in ℕ beside one in
ℕ∞, a `toNat` on one side, or a cast to another type. A count is converted as
described under "Sets and functions", and any other difference fails the
build. An item that Lean writes exactly as it writes the line closes the step
by `exact` alone.

## Which theorems are in

A theorem is in the Lean build when every notation its page uses, every
library function it applies and every item it cites has a Lean form: a
notation with a `lean-builds` field; a record whose `lean-proof` is Mathlib's
proof, a bridge or `none`, or names a Parley proof that is itself in; a
function whose definition has a `lean-builds` field; or a theorem of the
corpus that is itself in. A record whose `lean-proof` is `not yet
implemented` keeps out every theorem that cites it. A theorem is in, too, only when every letter it writes has a Lean type: a
number, a set, a member of one, a map or function between sets, a property, a
group or one of its elements, or a polynomial. Nothing lists the theorems; the build grows as fields are added. A
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
  `let k ∈ {1, …, n}` is `(k : ℤ) (H1 : k ∈ Finset.Icc 1 n)`. A letter a
  library item puts in a range without letting it, the k of `range`'s "k ∈
  {1, …, n} ↔ k ∈ ℕ and k ≤ n", is `(k : ℤ)` too: of any other k both sides
  are false.
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

## Sets and functions

A theorem's sets hold one type of things, `α`, as set.mm's sets all hold
sets: `let A be a set` is `(A : Set α)`, `let x be an element` is `(x : α)`,
and 𝒫A's members are `Set α`. A set of numbers is a set of the type that holds
them, `{2n : n ∈ ℤ}` a `Set ℤ`, and ℚ among the reals is
`{x : ℝ | ∃ m : ℚ, (m : ℝ) = x}`. A set a line puts among numbers,
`let D ⊆ ℝ`, is a set of those numbers; a letter that is only an element,
`let A be an element`, takes the type of the sets later lines put it in.

`let f : A → B` is `(f : α → α)` with `Set.MapsTo f A B` beside it, and
between sets of numbers `(f : ℝ → ℝ)` with the same. A library item's map
takes things of one type to things of another, `(E : α → β)`, wherever nothing
the item says makes the two one, so that a citation may give it integers and
take rationals, n ↦ 2ⁿ; an item that applies g⁻¹ to a point keeps g's two sides
one type, since the bridges' g⁻¹(y) is y itself where g sends nothing to y. One-to-one is
`Set.InjOn f A` and onto `Set.SurjOn f A B`. A map's domain is the set its line
gives it, or all of its type where it is given between number systems other
than ℕ and ℕ₀; its image and preimage are taken within that domain, `f '' (A ∩ Y)`
and `A ∩ f ⁻¹' Z`, as set.mm takes them, since Lean's `f` is total. f⁻¹(y) is
the bridges' inverse on the domain. f is a function on A is `True` of a Lean
function of A's type. The page's ℕ and ℕ₀, standing as a set, are the integers
above and from 0, `{n : ℤ | 0 < n}` and `{n : ℤ | 0 ≤ n}`, so that a map from
them into ℤ, or a set of them an integer is said to be in, has one type in and
out; a letter of ℕ stays a natural number, cast up where it meets them.

A count is a natural number, `A.ncard`, where the lines in scope show its set
finite, and otherwise `Set.encard`, in ℕ∞, as set.mm's ♯ counts an infinite
set as ∞; a set has one count form in each theorem. A set is finite where a
hypothesis, or a line in scope in words (`A is finite`, `B ⊆ A` of a finite
A), says so, and where it is ∅, listed, a range, or made by ∖, ∩, ∪, 𝒫,
{x ∈ A : …} or {E(s) : s ∈ A} from finite sets. A count given as a number,
|Y| = 2, makes its set finite only as a hypothesis: a line cannot vouch for
itself, so a step's |Y| = 2 is written in ℕ∞, and so are the lines after it. A
citation whose item counts a set in the other form converts it: each count in
ℕ∞ of a finite set is taken to its count in ℕ by `Set.Finite.cast_ncard_eq`,
then `exact_mod_cast`. Where a set is not finite by these, a
relation that computes with its count is not written. A step that computes by a
ring or an order with counts in ℕ∞, or whose lines say one set's count both
ways, first takes each count in ℕ∞ of a finite set standing outside any binder
to the integer it is (`parley_count_int`). A property, `let P be a property of the elements of X`, is
`(P : α → Prop)` and P(t) is `P t`; a citation gives it `fun t => …`. A group
is `{G : Type*} [Group G]`, its operation `*`, its identity `1`; a polynomial
is a function from ℂ to ℂ among the bridges' polynomials.

## Defines and recursions

A define in a proof is Lean's `set`: `let m = (a + b)/2` is
`set m : ℚ := … with D1`, and a function of one argument,
`let q(j) = F(j)², for j ∈ ℕ₀`, is `set q : ℤ → ℤ := fun j => …`. A function
on ℕ, ℕ₀ or a range takes integers, as the build's sequences do, so that q(j)
of a sum's index is written as it stands. A define of a kind of number,
`let e = p/d, a positive integer`, names a number of that kind from the kind's
fact, whatever the type of its value, as `let m ∈ ℕ` does.

A function the header lets is read as the page reads a let: a letter, with
its definition as a hypothesis. `let f(x) = 2x + 1, for x ∈ ℝ` is
`(f : ℝ → ℝ) (hD1 : ∀ x : ℝ, f x = 2 * x + 1)`, guarded by the domain where
that is a set, which is then its domain. A recursion,
`let F(0) = 0, G(0) = 1, F(k + 1) = G(k), G(k + 1) = F(k) + G(k), for k ∈ ℕ₀`,
is `(F G : ℤ → ℤ)` with its starts and its step for k ≥ 0 as one hypothesis. A
step citing the define, or a calculation row citing it, rewrites with that
hypothesis; a step citing F(k + 1) by the recursion is its step at k. A
theorem that cites another theorem over the same recursion gives it its own F
and G.

## Analysis

√x, π, ln, exp, sin and cos are Mathlib's `Real.sqrt`, `Real.pi`, `Real.log`,
`Real.exp`, `Real.sin` and `Real.cos`, and e is `Real.exp 1`. Their
arithmetic, √8 = 2√2 or sin(9π/4) = √2/2, is `parley_real`, and an item
stated over ℂ cited at reals is read back in ℝ (`parley_of_complex`).
x(n) → L as n → ∞ is `Filter.Tendsto (fun n : ℕ => x n) Filter.atTop (nhds L)`;
f tends to L at c is `Filter.Tendsto f (nhdsWithin c (D \ {c})) (nhds L)`, over
f's domain D with c left out; continuity on D is `ContinuousOn f D`; [a, b] is
`Set.Icc a b`. Each definition is proved from Mathlib's ε–δ form in
`Calculus.lean`. Floor takes ℝ, as set.mm's does, and a term the theorem takes
the floor of is a real wherever it is written. A claim about natural numbers
inside a limit's proof is written in ℝ from the start.

## Fields

A notation's `lean-builds` field has one entry for each of its patterns, set
apart by ` ; `: what each hole takes, what it yields, and the Lean text.

```
lean-builds α, α → α: _1 + _2 ; α, α → α: _1 - _2
lean-builds α, α → α: _1 * _2 ; α≥ℚ, α≥ℚ → α≥ℚ: _1 / _2
lean-builds ℤ, ℤ → Prop: _1 ∣ _2
```

An entry may give the pattern a form for each type its holes take, set apart
by ` | `. The writer takes the form whose holes are of the terms' own types,
and failing that the first whose holes hold them, a number held in a fixed
hole of a wider type:

```
lean-builds ℤ, ℤ → ℤ: _1 % _2 | ℝ, ℝ → ℝ: LeanBridges.Divisibility.mod _1 _2
lean-builds α → α: abs _1 | ℂ → ℝ: ‖_1‖
lean-builds ℕ → Prop: Nat.Prime _1 | ℤ → Prop: Nat.Prime _1.toNat
```

set.mm's mod is of real numbers, a − b·⌊a/b⌋; Mathlib's `%` is of integers,
and the bridges define the other as set.mm does, with a lemma that the two
agree for a divisor not negative. |x| of a complex number is its norm. A
prime of the integers is a natural prime, as set.mm's ℙ is.

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
| induction | from 0 over ℕ₀, Lean's induction; from 1 over ℕ, `Nat.le_induction`; on the parts of a finite set from ∅, `LeanBridges.Sets.subset_induction` |

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
