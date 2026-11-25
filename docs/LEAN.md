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
Which line a step names puts a part in a number system, the letter a cited
"for all" is read at, what the lines in scope, a claim's other sentences,
the requires lines above and a step's own lines bound below and make
finite, and the page with outside defines written out are the record's
(`docs/CHECKER.md`). The writer keeps the choices that are Lean's own: the
Lean type of an item's untyped letter, and how a fact is written, a range
line's integer `∃ m : ℤ, ↑m = k ∧ m ∈ …` among them. Inside one formula,
the writer reads its earlier parts through the shared bounds and finiteness
rules as it writes, from the recorded facts, to choose a term's Lean type
(`docs/CHECKER.md`, `bounds`).
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
library of their own, and the build never touches them. The bridges
define no tactic: a generated proof calls Lean's and Mathlib's own, and
cites the bridges' definitions and one-fact lemmas (`PowerTactics`,
`Logarithms`, `Sums`, …). Each module is imported only by the files that
name one of its lemmas or definitions, since a change to a module rebuilds
every file that imports it. `Counting.lean` and `Sums.lean` hold the bridges. A bridge states its item
exactly as the build writes it, with the item's letters and hypotheses in
the same order, so a record names it in full, `lean-proof
lean-bridges/counting/pascal`, and the build writes
`LeanBridges.Counting.pascal n k`. A generated file the build no longer
makes is removed.

## How a file is made

Every term the writer builds is a tree (`doc::Term`) with no text in it. A
binder is a node that holds its letter, the letter's type, what it runs over
and its body: sums and products, `⋃`, integrals, set-builders, `∀ x ∈ S`,
`fun` and `if h :`. So are `⟨…⟩`, `{a, b}`, `show`, `''`, `⁻¹'`, `𝒫` and
`⁻¹`. Only the printer makes text. Substituting, renaming and comparing all go
through the nodes, so a letter a binder binds is never touched by a value put
in from outside.

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
other's, each part of an "and", "or", ↔ or → beside its own. A row of a
calculation is compared as the calculation states it. What is left is a form
the writer chose: a count in ℕ beside one in
ℕ∞, a `toNat` on one side, or a cast to another type. A count is converted as
described under "Sets and functions", and a power as described under "Number
types"; any other difference fails the build. An item that Lean writes exactly as it writes the line closes the step
by `exact` alone.

How a line proves a statement elsewhere comes from the record. A block's last
step meets what it owes, a supposition what it denies, a contradicting step
its line, and an instance its claim, in the way the checker found them alike.
Each meeting gives one tactic: the line itself, its `.symm` or `Ne.symm`, or
`simpa only [add_zero, …] using` it; or, where the line writes a range as
`Finset.Icc` and the statement as `Set.Icc`, `simpa only [Finset.mem_Icc,
Set.mem_Icc] using` it. The writer decides only what comes from
its own choice of casts and `toNat`. Two statements apart only there close by
`exact_mod_cast`, or by `simpa using` where neither type is narrower.

A cited fact is found where the checker placed it (`FirstAt`). That place is a
sentence by its place on the page, a part of it, a "for all" read at the
block's letter, or what it implies. A range's bound is
`(Finset.mem_Icc.mp h).1` or `.2`. `0 < n` of `n ∈ ℕ` is the hypothesis
itself, and `n ≠ 0` is its `.ne'`. `X ⊆ A` of `X ∈ 𝒫A` is the hypothesis as it
stands.

A line in a narrower number type than the statement it supplies,
`10·N(k) ≤ N(k + 1)` in ℤ for a hypothesis in ℚ, is taken across by
`exact_mod_cast`, where the cast table says `norm_cast` moves a cast of the
two types through the relation, every cast of the statement moves, and the
two are alike once their casts are dropped. A line saying `>` where Lean
asks `<` is turned first (`gt_iff_lt`). ℚ's order is not taken to ℝ's,
which `norm_cast` does not do for a fact of numerals.

**A citation.** The writer writes the cited item's sentence at the
citation's values as it writes the step's own lines: the item's tree with the
values put in (`matching::substitute_apart`, a function or property given as
a value applied where the sentence applies it), written by the theorem's
writer. It states it as `have hI : … := by …` and closes the step's claim
from `hI` as the checker met the two (`exact`, `.symm`, or the identities
the meeting names). The item's Lean statement, written once over any ring
or set, is read in that spelling by what Lean knows of the two forms
(`spelling`): the item itself where Lean takes the two as one term;
`push_cast` first where the item, its functions applied, casts a numeral or
arithmetic to another type; `simp only` with the library's fact for each
form the item writes and the step does not (`∀ x ∈ Set.univ`, a set built
from `Set.univ`, an integer said as some `(m : K)` at ℤ, a range as a set,
the reals' `mod` beside `%`); and `exact_mod_cast` where the item is in a
wider type, after `rify` where it is in ℝ and the step in ℚ.

**A substitution.** Where the checker recorded how a `substitute` step or
calculation row makes its claim (`CheckedTheorem::substituted`), the writer
puts the equation in exactly there. It writes what the equation is put into
with each recorded place as one fresh letter, the motive, its letter of the
type its places are written in: the line's, for a term of the line's
arithmetic (a hole its template computes in the formula's type, or a
relation's side), and its own, for a hole of a fixed type, a function's
argument or an exponent (`Writer::in_formula_type`). Places
of different kinds written in one type take one motive. Put into a line,
`Eq.subst` along the
motive takes the line to the claim; put into a side of the claim `t = t′`,
`congrArg` of the motive is the claim, turned where the side is its right.
An equation in a narrower type than a claim side whose places are all of
its arithmetic is first stated in the wider, as a line's is, cast up with
`push_cast` and `linear_combination`, and the motive's letter is of the
wider. Each row of a `substitute` step is put into the row above the same
way, its change proved by its reason (`substituted_rows`). An equation no
line says is proved where it is put: by the tactic an `arithmetic` step's
claim takes (the method table) where the step works it out, by real arithmetic's proof (the method table) where real arithmetic does, and by the define's
hypothesis, turned where the step writes the
name on the right. Identity elements the record says the claim drops are
rewritten away by `push_cast` with their lemmas, `push_cast [one_mul] at h
⊢`.
A line that says something of the whole number a term is, `∃ m : ℤ, (m :
ℚ) = t ∧ Even m`, is put into with a motive of that same form. Where the
claim says it of the whole number the new term is, `Even (3 ^ q.toNat)`,
the result is said of that number by `parley_witness_at`, its equation by
`norm_cast`, or by the step's named numbers' equations. Where the record
takes the substitution sentence by sentence, each sentence is put into its
own (`substituted_sentences`). Places of two types, a function's argument
in the equation's type and a term of the line's wider arithmetic, take the
equation in two stages, as it is and then widened. An equation of natural
numbers put at exponents is stated in ℕ first (`e_nat`), the motive's
letter of ℕ. A range member Lean computes wider, made at the member alone,
is `⟨_, equation, line⟩`. A substitution the record makes into a line's
"for all" as a whole is written over the whole "for all", the claim not
peeled. A row's change goes in as stated where every recorded place is
written in its own type.
The equation's line is turned with `.symm` where the record puts its left
side for its right, read from the line as the page writes it, with its
defines kept (`FirstAt::written`). The result is the proof itself where the
motive states the claim as the step states it. Otherwise it is stated by a
`have`, so that a numeral exponent defaults to ℕ, and closed by `revert h;
norm_num` where the claim names no letter, else by `push_cast at h ⊢` and
`exact_mod_cast h`. At a place that is an exponent, the motive's letter is
written as Lean writes the exponents at both its values
(`Writer::natural_form`): as its `toNat` where both are written so, a
numeral put counting so; else an integer, its powers converted to the
claim's after, the exponent's fact from the record, as a citation's is (see
"Number types").
Where the record gives a substitution no way, it declines, as any step does.
The route also takes:
- a term that is no number, a set or a group's element: the motive's letter
  of its type, and a count of it in ℕ∞ met with the claim's natural counts
  (`counted_between`);
- a putting that meets the claim turned round, by turning the goal first
  (`symm`); respelled, `0 < x` of `x > 0`, as it stands; a listed set in
  another order, by `reordered`;
- a fact the line implies, `k ≤ n` of `k ∈ {1, …, n}`, proved from the line
  first (`line_says`);
- a line in a narrower type than the equation, stated in the equation's type
  first, an order of ℚ by ℚ's cast lemmas;
- a line of the whole number a term is, put into where the equation puts an
  integer: the line's m, which is that integer by the cast being one to one;
- a count or an exponent Lean writes as a natural number: the equation
  stated in ℕ (`e_nat`), by `omega` where a side is an integer the step's
  lines show at least 0;
- a natural number put for a letter written by its `toNat`, whose `toNat`
  of its cast is it (`Int.toNat_natCast`);
- a side holding a cast of a `toNat`: the casts back of the whole numbers
  the step names, `rw [Int.toNat_of_nonneg h]`, then the motive.

The motive's letter is told what the lines say of both terms it stands for:
finite where the set put for is, and at least the lesser of their bounds, so
`√t` is Lean's real root of t ≥ 0.

**Casts.** Where two statements are alike but for casts, the closer comes
from the cast table (`src/lean/casts.rs`). For each operation the writer
writes and each widening between ℕ, ℤ, ℚ, ℝ and ℂ, and from ℕ to ℕ∞ where a
calculation's rows take counts, the table says whether `push_cast` moves a
cast through the operation and whether `norm_cast` does. A cast inside an
argument of a function the table does not know stands under it alone, as
under a norm.
`parley build lean` writes `lean/Parley/Tests/CastTable.lean` from it, with
an example for each entry, so `lake build` holds every entry true. A
calculation's row is met with what it cites as the calculation states it,
its counts in the form the rows take them.

The closer is chosen as follows:
- `exact_mod_cast` where `norm_cast` moves every cast in both statements and
  they are stated in one type;
- `exact_mod_cast` where the two are stated in different types, the checker
  met them as written (`Cited::meetings`), no form stands apart, and
  `norm_cast` moves every cast of both; not of a fact of numerals alone,
  which `norm_cast` does not take across every order;
- `push_cast at h ⊢; exact h` where only `push_cast` moves them all and the
  line is in no narrower type;
- otherwise, each side rewritten by the `set` equations its letters name,
  `push_cast at h ⊢` and then `exact h`, or `exact_mod_cast h` where the
  line is in a narrower type; lifting where neither is would read a
  division of casts one way on one side and another on the other.

Before any of these, the step reads how the checker met the item with the
claim (`Cited::meetings`, `Cited::facings`):
- where the identity elements the checker dropped are all that stands
  apart, the conversion of those alone: `simp only [their rewrites] at h ⊢`,
  then `exact_mod_cast h`, or `h.symm` where the record has the item turned.
  A `0` or `1` Lean writes cast up, `((1 : ℤ) : ℚ)` where a function applied
  puts a numeral in for a letter it casts, is first taken to the numeral
  (`Int.cast_one`), so the rewrite meets it;
- where the checker paired the parts of a notation whose parts stand in any
  order out of their places (`permuted`), took nothing else, and the claim
  lists a set's members: the item taken in the claim's order. An equation of
  sets is taken member by member (`ext`, `Set.ext_iff`, then `tauto`); a
  membership or subset is read as the equations of members it says, then
  `tauto`;
- where the item is worked in a wider field than the claim's: read down to
  the claim's, from ℂ by each complex operation read as the real one cast
  (`Complex.ofReal_*`, a complex power's base shown not below 0 by
  `positivity`); an item in ℝ for a claim in ℚ is met by the step's other
  ways;
- where the step goes through named numbers its proof puts first, as the
  casts of those numbers (`Classical.choose_spec`), and the checker met the
  item as written: an equation or order is then the item's relation with
  each side cast up as a whole, `exact_mod_cast` of the item where the cast
  table says `norm_cast` moves a cast through that relation
  (`casts::norm_cast_lifts_relation`); a range member Lean writes as the
  integer that is it, `⟨_, rfl, item⟩`. A step that goes through named
  numbers puts each into the goal, and into each line it cites where Lean
  writes the number's term at the type the rewrite states it in, `rw [← …]
  at s3; norm_cast at s3`. A remainder whose parts are then named numbers
  or integer letters is taken as the integers' `%` (`mod_intCast`);
- where the claim is an "and" the checker met as written, part by part, the
  item named once, `have h := …`: "and" stands in no other order, so part j
  of the item is part j of the claim. A membership of ℕ or ℕ₀ Lean writes as
  an integer of a wider term, `∃ m : ℤ, 0 < m ∧ ↑m = t`, beside the item's
  `0 < v` is `⟨_, h.j, rfl⟩`; an equation or order whose casts `norm_cast`
  all moves is `by exact_mod_cast h.j`.

A step the writer could close several ways, with no fact to choose one by,
is declined with that reason; a generated proof tries no ways in turn.
`tests/lean_closers.rs` names a step where each rule decides.

## Every theorem is in

Every theorem of the corpus is in the Lean build, as every one is in the
Metamath build. A theorem the writer cannot write is a gap: `parley build
lean` lists it with the reason and exits 1, and the gate is red. That
includes a theorem that cites an item whose `lean-proof` is `not yet
implemented`, writes a notation with no `lean-builds` field, or writes a
letter Lean has no type for. A theorem the checker refuses, or a file Lean
does not read, is a failure: it is not built, nor is what cites it, every
such failure is reported in one run, and the build exits 1
(`ELABORATION.md`). The gate's planted cases hold both builds to this: a
record whose `metamath-proof` or `lean-proof` is taken away turns the gate
red.

## Number types

On the page every number is a number. In Lean each has a type, and three
traps follow: subtraction in ℕ stops at 0, division in ℤ rounds down, and
Lean's ℕ starts at 0 where the page's starts at 1.

- A letter of ℕ or ℕ₀ is an integer with its fact, as Metamath has n ∈ ℕ
  as a fact about a number: `let n ∈ ℕ` is `(n : ℤ) (hH1 : 0 < n)` and
  `let n ∈ ℕ₀` is `(n : ℤ) (hH1 : 0 ≤ n)`. Any other letter keeps its own
  type: `let a ∈ ℤ` is `(a : ℤ)`, and so for ℚ, ℝ, ℂ; `let k ∈ {1, …, n}`
  is `(k : ℤ) (hH1 : k ∈ Finset.Icc 1 n)`. A letter a
  library item puts in a range without letting it, the k of `range`'s "k ∈
  {1, …, n} ↔ k ∈ ℕ and k ≤ n", is `(k : ℤ)` too: of any other k both sides
  are false. Inside a proof, where the goal's "for all" puts the letter in a
  range, its bounds are named beside it, `have hK1_bounds :=
  Finset.mem_Icc.mp hK1`, for linear arithmetic.
- An exponent that a phrase define's meaning puts in ℕ, ℕ₀ or ℤ, the n of
  "z is an n-th root of w means n ∈ ℕ and z^n = w", is `(n : ℤ)` for the
  same reason: of any other n the meaning is false. A letter put in ℕ that
  is no exponent may be cited at a real, and keeps ℂ.
- A count is in ℤ, or in any wider number system, exactly where it is some
  natural number. So `|S| ∈ ℤ` is written as `|S| ∈ ℕ₀` is.
- Each formula is computed in the least of ℤ, ℚ, ℝ and ℂ that holds every
  letter and operation in it, never in ℕ. The two sides of a relation share
  one type, and a narrower letter is cast up. `7 divides 4a` is `7 ∣ 4 * a`;
  `f(n) = ((−1)^n·(2n − 1) + 1)/4` with n ∈ ℕ is written in ℚ.
- A power whose exponent is no natural number, `x^(−1)`, is Lean's integer
  power, taken in ℚ at least.
- A power whose exponent the page says once is in ℕ₀, `2^n` of n ∈ ℕ, is the
  natural power `2 ^ n.toNat`. Any other integer exponent, `2^(n − 1)`, gives
  the integer power, even after a line says the exponent is in ℕ₀, so that
  every line writes one term one way.

  A step may write a power one way while what it reads writes it the other.
  What it reads is an item it cites as written or forward, a line it
  instantiates, or the line a calculation row is read off. A part an
  `obtain` takes from an item holds the part as the item's Lean statement
  gives it, paired with the page's sentence as the checker paired them
  (`CheckedTheorem::obtained_parts`), and a step citing that line reads that
  statement. The step then converts the power, as a count is converted:
  - each integer power `a ^ e` whose exponent is shown at least 0 is
    rewritten as `a ^ e.toNat` by `parley_zpow_toNat`;
  - an integer power of a natural number cast up, `a ^ (k : ℤ)`, is
    rewritten as `a ^ k` by `zpow_natCast`;
  - each identity element the checker dropped meeting the two
    (`Cited::meetings`) is rewritten away, `sub_zero` of x − 0, and a
    numeral's `toNat` is worked out (`Int.reduceToNat`);
  - then `exact_mod_cast` closes the step.

  A membership `t ∈ ℕ`, `ℕ₀` or `ℤ` of a t that Lean computes in ℚ only for
  its integer powers, `2^|numer(x)|·5^s(x) ∈ ℕ`, has t written in ℤ as its
  witness, each such power made natural: `2 ^ (abs (Rat.num x)).toNat * 5
  ^ (s x).toNat`. Each exponent's bound comes from the step's lines, and the
  witness's equation with t from `parley_zpow_toNat`.

  The proof of `0 ≤ e` is written from why the said-once walk puts e in ℕ₀
  (`citing::reason_within`), the reasons the Metamath build proves
  memberships from:
  - a part the walk does not take apart: from a line the step names, or from
    the line the checker found the item's `m ∈ ℕ₀` supplied by, with
    `le_of_lt` for a line of ℕ;
  - a term a line in scope bounds below at 0 or above
    (`CheckedTheorem::bounds`): from that line, `0 < e` by `le_of_lt`;
  - a letter: from the line that introduces it, which is its `let`, an
    induction's step case, a define of a kind, or a range from a numeral;
  - a numeral, by `norm_num`; a factorial, by `Nat.cast_nonneg`;
  - a sum or product of such parts, by `add_nonneg` or `mul_nonneg`.

  A power under a sum whose exponent names the sum's letter, `y^((k − 1) +
  1)` over k from 1, is at least 0 only for k in the range. The step states
  the rewrite for each k in the range, from the range's lower bound, and
  `simp +contextual` takes it under the sum. An exponent shown in none of
  these ways fails the build.
- A claim of numerals alone reached from lines is written in the type of
  those lines, and a cited line of a narrower type than the claim is cast up
  to the claim's type before it is used.
- The index of a sum or product, and its ends, are in ℤ, so that a range
  means what the page says: 0 to n − 1 at n = 0 is empty.
- A notation of number theory takes the type it is about: `divides`, `mod`
  and congruence take ℤ, `prime` and factorial take ℕ. A term too wide for
  it is not cast down. Where a line has said the term is an integer, `(N −
  1)/2 ∈ ℤ`, the integer that line gives is used; otherwise the writer
  reports the term. How such a term is shown is the checker's
  (`places_shown`, `members_shown`), and the writer proves it that way: a
  term beside an equation is named by the other side's number, the equation
  turning one into the other.

  A function a define gives is built in the numbers its rule computes in, or
  in the widest numbers a line of the page gives it as its type, `f n = (n :
  ℚ)` of `let f(n) = n` beside `f : ℕ → ℚ` (`define_values`). A line saying
  its values are among narrower numbers than Lean computes them in, `for all
  x ∈ ℚ, g(x) ∈ ℕ` of a rule in ℚ, narrows it there: the function chosen
  from the line's witnesses takes the define's name from that line on,
  `obtain ⟨g, s5_pos, s5_eq⟩ : ∃ g' : ℚ → ℤ, (∀ x, 0 < g' x) ∧ ∀ x, ↑(g' x)
  = g x`, the bound the line says kept beside its equation, and the define's
  equation is said again of it, `hD3_g : ∀ x, ↑(g x) = v`, which a step
  citing the define reads. Every line from there writes the narrowed
  function. A line above it that names the function is read through the
  equation where a later step cites it, `simp only [← s5_eq] at h`, with
  `+contextual` where the equation holds on a set. Outside the block the
  narrowing stands in, the function is the define's again.
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

`let f : A → B` is `(f : α → β)` with `Set.MapsTo f A B` beside it, and
between sets of numbers `(f : ℝ → ℝ)` with the same. A theorem's or an item's
sets hold things of one type where something it says makes them one, `C ⊆ A`,
`x ∈ A ∩ B`, f(x) ∈ B, and things of two types where nothing does: f takes
A's things to B's, so schroeder-bernstein is stated over `{α β : Type*}`, and
a citation may give it integers and take rationals. A product `X × Y` holds
pairs of X's things and Y's, `X ×ˢ Y : Set (α × β)`, and a pair `(a, b)` is of
a's type and b's. The two places are of two types where nothing joins them, as
a map's sides are, so pair-in-product and card-product are stated over `{α β :
Type*}`, and a set of pairs, S of `S ⊆ X × Y`, is a `Set (α × β)`. The checker records which
sets share a type (`thing_types`), and the type variables follow the order
the sets are let. Each type variable is `[Nonempty α]`: it stands for set.mm's
universe of sets, which holds ∅, so a function from A to B exists whatever A
and B are, and g⁻¹ has a value where g reaches nothing. One-to-one is
`Set.InjOn f A` and onto `Set.SurjOn f A B`. A map's domain is the set its line
gives it, or all of its type where it is given between number systems other
than ℕ and ℕ₀; its image and preimage are taken within that domain, `f '' (A ∩ Y)`
and `A ∩ f ⁻¹' Z`, as set.mm takes them, since Lean's `f` is total. f⁻¹(y) is
the bridges' inverse on the domain, Mathlib's `Function.invFunOn`, from B's
type back to A's. f is a function on A is `True` of a Lean
function of A's type. The page's ℕ and ℕ₀, standing as a set, are the integers
above and from 0, `{n : ℤ | 0 < n}` and `{n : ℤ | 0 ≤ n}`, so that a map from
them into ℤ, or a set of them an integer is said to be in, has one type in and
out; a letter of ℕ stays a natural number, cast up where it meets them.

A count is a natural number, `A.ncard`, where the lines in scope show its set
finite, and otherwise `Set.encard`, in ℕ∞, as set.mm's ♯ counts an infinite
set as ∞; a set has one count form in each theorem. A set is finite where a
hypothesis, or a line in scope in words (`A is finite`, `B ⊆ A` of a finite
A), says so, and where it is ∅, listed, a range, or made by ∖, ∩, ∪, 𝒫,
{x ∈ A : …} or {E(s) : s ∈ A} from finite sets. A count given as a number
the page shows positive, |Y| = 2 or |Y| = n of an n ∈ ℕ, makes its set
finite, in its own line and the lines after it: `Y.ncard = 2` holds of no
infinite set, whose `ncard` is 0. A count given as a number that may be 0,
|Y| = m, makes its set finite for the lines after it too, since
`Y.encard = m` says Y has m elements; the line itself is written in ℕ∞,
`Y.encard = m`, since `Y.ncard = 0` holds of every infinite set too. A
citation whose item counts a set in the other form converts it: each count in
ℕ∞ of a finite set is taken to its count in ℕ by `Set.Finite.cast_ncard_eq`,
then `exact_mod_cast`. Where a set is not finite by these, a
relation that computes with its count is not written. A step that computes by a
ring or an order (`algebra`, `arithmetic`, `inequalities`) first takes each
line it cites that counts a finite set in ℕ∞ to the integers: the count
rewritten by `Set.Finite.cast_ncard_eq`, the equation read in ℕ
(`norm_cast`) and said of integers (`zify`). A calculation worked in a wider
field than its claim, whose terms count a set built by a condition, is built
as written and met with the claim by `exact_mod_cast`, since `qify` and
`rify` would rewrite the condition under its binder. A property, `let P be a property of the elements of X`, is
`(P : α → Prop)` and P(t) is `P t`; a citation gives it `fun t => …`. A group
is `{G : Type*} [Group G]`, its operation `*`, its identity `1`; a polynomial
is a function from ℂ to ℂ among the bridges' polynomials. One with integer
coefficients is among the bridges' `integerPolynomials`, set.mm's Poly ℤ:
the functions a polynomial over ℤ gives. deg(F) is the bridges' `degree F`,
a natural number. It is the degree of the polynomial over ℂ that gives F
(there is only one, as ℂ is infinite), and 0 where no polynomial gives F, as
set.mm's deg is.

`for all sets X, P` is `∀ X : Set α, P`, X a set of the theorem's things. A
chain of equations, a = b = c, is the conjunction of its neighbouring
equations, `a = b ∧ b = c`. Where a step cites two terms of a chain that are
not neighbours, the checker records which links join them, and the build
proves the equation by `Eq.trans` of those links. A map given by its values,
`the map sending y ∈ A to E`, is `fun y : T => E`, T the type of A's members:
a function on all of T, as a map letter is. Applied, it is its rule at the
argument. A pair `(a, b)` is a member of Lean's product type,
`((1, 1) : ℤ × ℤ)`. Two pairs are equal by `Prod.ext` of their coordinates,
and unequal at the coordinate the checker records them apart at. The page's
nth root is the bridges' `root n x`, set.mm's real root read as written:
x^(1/n) for x ≥ 0, and −(−x)^(1/n) below 0. `⋂(x ∈ D) E` is `⋂ x ∈ D, E`,
which over an empty D is all of the type, as set.mm's is. `sup S` is
`sSup S`. Every statement that uses it says S is non-empty and bounded above,
so Mathlib's value elsewhere is never read.

`A × B` is Mathlib's `A ×ˢ B`, a set of Lean's pairs. A function whose values
are sets or pairs is a map into them: `let I(k) = {|x| : x ∈ 𝒫{1, …, k}}, for
k ∈ {1, …, N}` is `I : ℤ → Set ℤ`, and `let f(i) = (L(i), M(i))` is
`f : ℤ → ℤ × ℤ`, whichever the record's sort of the define says. `for X ⊆ A`
takes X over `Set α`. A set of functions between finite sets, and a product
of finite sets, is finite (`functions_from_finite`, `Set.Finite.prod`), so
their counts are natural numbers.

`X exists` is `LeanBridges.ZF.IsSet X`: X is one of ZF's sets
(`corpus/lean-bridges/ZF.lean`). The bridge's class `Sets α` says which
things of a type are sets, and which of Mathlib's `ZFSet`s each one is. Every
`ZFSet` is one. Every integer is one, coded by a set of its own, as set.mm
builds the numbers from sets. A set of things is one where all its members
are and their codes make a `ZFSet`. A statement that says a collection exists
takes `{α : Type*} [LeanBridges.ZF.Sets α]`. Each letter its `let` lines
introduce gets the hypothesis that it is a set, `hX_set`, as set.mm's reading
of a `let` gives `X ∈ V`. A citation meets that hypothesis with the citing
statement's own fact for the letter it gives. The axioms that say a
collection exists are proved once each in the bridge from Mathlib's ZF sets,
and `ℕ exists` is said of the page's ℕ, the positive integers. Sets of reals
and complex numbers are not yet among ZF's sets, so the writer declines a
page that says one exists, and the build fails on it.

f(x, y) of a function on pairs is `f (x, y)`, each coordinate at the type
f's domain gives it. Σ(d ∈ ℕ : d divides n) d is the sum over the set the
condition makes, `∑ᶠ d ∈ {d : ℤ | 0 < d ∧ d ∣ n}, d`.

## Graphs

`let G be an undirected multigraph with vertices V and edges E` is three
letters and a class: `(V : Set α) (E : Set β) (G : β → Sym2 α)
[LeanBridges.Graphs.Multigraph V E G]`. G is the function sending each edge
to its two ends, as set.mm's iEdg is. The class says each edge's ends are
among V, and that no edge has one vertex for both ends. α and β are the
checker's thing types of V and E. A graph given in full also names each
vertex and edge, `(A : α)`, `(b₁ : β)`, and states what its line asserts:
`V = {A, B, C, D}`, the names different from each other, and `G b₁ =
Sym2.mk A B` for each edge.

"a joins u and w" is `G a = Sym2.mk u w`, and "x is incident with a" is
`x ∈ G a`. Every other notion of a graph (deg, walk, Euler path,
traversable) is written out as its definition says (`checker::written`).
deg(x) is the count `{a ∈ E | x ∈ G a}`, ncard where the lines show it
finite and encard where they don't, as every count is. The definitions are
then true as they stand, `Iff.rfl` and `rfl`. The small lemmas are bridges
in `corpus/lean-bridges/Graphs.lean`.

A set every member of which is e(i) for some i in a range of integers, "for
all a ∈ E, there is i ∈ {1, …, n} with a = e(i)", is finite
(`LeanBridges.Sets.finite_of_covered_by_range`). The edges of an Euler path
are such a set.

`inspection` over a graph given in full is handed the line's facts: its
sets' equations, the joins, and each "different" fact both ways round. A set
taken by a property from a listed set is written member by member, as the
checker recorded which members are kept (`Inspection::Taken { kept }`). Each
member gets `LeanBridges.Sets.sep_insert_of` or `sep_insert_of_not`, with
its property stated of that member and proved from the facts. A count of the
members kept is then worked out by `norm_num`.

## Geometry

A point is a complex number, `(A : ℂ)`, as in the Metamath kernel. Each
geometry notation's `lean-builds` names Mathlib's term: |AB| is `dist A B`,
∠PQR is `EuclideanGeometry.angle P Q R`, ∡PQR is
`Complex.arg ((R - Q) / (P - Q))`, "Q is between P and R" is `Sbtw ℝ P Q R`,
and collinear is `Collinear ℝ {A, B, C}`. A triangle is
`LeanBridges.Geometry.Triangle P Q R`: its points apart and not collinear.
Same side, opposite sides, parallel and perpendicular are the page's
formulas in the imaginary or real part of a quotient of differences.
`line AB` and `ray AB` are sets in `corpus/lean-bridges/Geometry.lean`,
empty when A = B, since a line through one point is no line. x° is
`x * Real.pi / 180`.

The notations that stand in no order (|AB| and |BA|, a triangle or a
collinearity named in any order) are one term on the page and two in Lean.
The checker records each place it met them in the other order
(`Meeting::flips`, `place_flips`, `equation_flips`, `commuted_by_lines`).
Lean turns a line at each by an exact instance of the notation's swap
lemma, `rw [dist_comm C A] at h` or
`LeanBridges.Geometry.triangle_rot_231 A B C`, never a list for `simp` to
search. An algebra, inequalities or transitivity reason, which reads |AB|
and |BA| as one term, first takes every line it cites and its goal to one
order that way.

The geometry library's axioms and theorems are proved from Mathlib, by
short proofs in their records or by bridges in `Geometry.lean`.

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
that is a set, which is then its domain. A step that applies such a function
puts in its equation at the argument, `hD1 _ h`, h what the record found puts
the argument in the domain (`applied_domains`). An order step adds it as a
fact, a citation of an item or an algebra rewrites the goal by it, and at a
sum's index it is used term by term,
`Finset.sum_congr rfl (by intro k h; exact hD1 k (…))`, the index's fact read
off the range. A limit of such a function is taken across from where the
domain starts, `h.congr' (Filter.eventually_atTop.mpr ⟨1, …⟩)`. A recursion,
`let F(0) = 0, G(0) = 1, F(k + 1) = G(k), G(k + 1) = F(k) + G(k), for k ∈ ℕ₀`,
is `(F G : ℤ → ℤ)` with its starts and its step for k ≥ 0 as one hypothesis. A
step citing the define, or a calculation row citing it, rewrites with that
hypothesis; a step citing F(k + 1) by the recursion is its step at k. A
theorem that cites another theorem over the same recursion gives it its own F
and G.

A function the header lets of more than one argument, `let c(j, y) = …, for
j ∈ ℕ₀, y ∈ V`, is written out where it is applied, as a file's defines are.
It has no letter or hypothesis of its own.

## Analysis

√x, π, ln, exp, sin and cos are Mathlib's `Real.sqrt`, `Real.pi`, `Real.log`,
`Real.exp`, `Real.sin` and `Real.cos`, and e is `Real.exp 1`. Their
arithmetic, √8 = 2√2 or sin(9π/4) = √2/2, is proved value by value as the
method table says, and an item
stated over ℂ cited at reals is read back in ℝ (each complex operation read
as the real one cast, as a citation is).
x(n) → L as n → ∞ is `Filter.Tendsto (fun n : ℕ => x n) Filter.atTop (nhds L)`;
f tends to L at c is `Filter.Tendsto f (nhdsWithin c (D \ {c})) (nhds L)`, over
f's domain D with c left out; continuity on D is `ContinuousOn f D`; [a, b] is
`Set.Icc a b`. Each definition is proved from Mathlib's ε–δ form in
`Calculus.lean`. Floor takes ℝ, as set.mm's does, and a term the theorem takes
the floor of is a real wherever it is written. A claim about natural numbers
inside a limit's proof is written in ℝ from the start.

f is differentiable on U is `∀ x ∈ U, D ∈ nhds x ∧ DifferentiableAt ℝ f x`,
with D f's domain where a line gives one. Of f between number systems, only
the derivative is said. f′ is `deriv f`, and stands wherever a function of
reals does: continuous, differentiable, or applied. Its domain is where f
has a derivative, so "f′ is differentiable on U" says `{y | …f at y…} ∈ nhds
x ∧ DifferentiableAt ℝ (deriv f) x`. A line that says the derivative alone
meets an item that asks it over a domain that is all of ℝ, by
`Filter.univ_mem`. f^(n) is `iteratedDeriv n f`, with n as a natural number.
"g is defined at c" is `c ∈ LeanBridges.Calculus.derivDomain k f`, for g the
k-th derivative of f, where set.mm takes it to be defined: the 0th
everywhere, and the (k + 1)-th at a point that the k-th's domain contains a
neighbourhood of and where the k-th is differentiable.

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

No theorem is given more than Lean's default budget of 200,000 heartbeats.
A step proves what it can from the record, so a search is left only where
no line states the fact.

Where the record gives a step no way, the writer declines, and the theorem
is a gap: `parley build lean` lists it with the reason, and the build fails.
No proof is left to a general search tactic.

| method | Lean |
|---|---|
| a citation | the item's theorem at the citation's values, each hypothesis by the line the checker found it supplied by (`Cited::supplied`), the number-system fact of an item letter's binder among them, the line's fact met as Lean states it: casts taken across (ℚ to ℝ by ℚ's cast lemmas, a negated equation by `Rat.cast_inj.not`), a listed set's membership read as its equations, a number a step names put back by its own equation, a range crossing between `Finset` and `Set` by `Finset.mem_Icc`; a hypothesis whose set the citation gives as all of ℝ or a range is taken from its line all the same; `.mp` from the line the reading starts from, `.mpr` with the right side built from its parts (`Cited::unfolded`): each witness, and each fact by the line that states it, as Lean states the part; a define the step cites written out in the goal only where the checker read it out in the claim to meet the item (`Meeting::unfolded`), so a value that names it keeps it, `(s := s)`; a hypothesis met through a define as an identity, `rw [hD1, dist_comm C A]`, its equation and then each flip |
| obtain | `obtain ⟨k, …⟩ :=` the item's or the line's "there is"; a part the checker met otherwise than as written, or that Lean casts otherwise, is obtained under a name of its own and stated after as the page says it |
| exhibit | `⟨w, h⟩`, each fact of the values by the line the checker found it stated by (`Exhibit::shown`) |
| instantiate | the sentence the checker instantiated, at the values given, a letter given none at the block's letter, each guard and condition by the line the checker found it supplied by (`Instantiated::guards`, `Instantiated::conditions`); closed by the instance's meeting with the claim, or, where Lean states the two otherwise, by `linear_combination`, `linarith` or `exact` |
| algebra | `ring1`, or `ring_nf` where the checker read two terms as one that differ inside a function's argument or an exponent; a step joining finite sums gathers each side into one sum (`Finset.mul_sum`, `Finset.sum_add_distrib`, …) and compares them term by term; from cited lines, `linear_combination` with the multipliers the checker recorded (`CheckedTheorem::combinations`), each a page term written as Lean writes it; a disequality, by the rescaling recorded; a multiplier's divisor written as the product of the parts the step divides by; where the step divides by a term, `field`, after a fact `hz` for each part it divides by, proved from the line the checker found (`CheckedTheorem::divided_by`), taken apart into its factors, a positive integer of letters alone by `positivity`; each fact written with its factors in the order `field` writes them back, which numbers the goal's parts as it first meets them, and turned from the page's order by `ring` where the two differ; every define the record lists for the reason written out (`defines_read`), one of a wider-typed value after `qify` or `rify` at its places, and only at the lines it cites and at its goal (`Proof::rewritten_at`), so a line it does not cite keeps its letters; at each place, only the defines its statement names or a define written out there brings in, then `push_cast` at each place that holds a cast or is given one by a define's value |
| arithmetic | by what the claim holds: `norm_num`; a factorial, `norm_num [Nat.factorial]`; a sum or product over a range of numerals, `decide`, or `field_simp; norm_cast` where it divides; a fraction denied to be a whole number, `rintro ⟨m, _, h⟩; field_simp at h; norm_cast at h; omega`; a binomial coefficient of numerals declines |
| real arithmetic | as the Metamath elaborator proves it (`reals`): each special value a `have` proved by its law, from the value the checker's decider works out (`methods::reals`, `methods::surds`): a root of a rational, its square part taken off (`Real.sqrt_mul`, `Real.sqrt_sq`); a quotient by a root, its divisor not 0 by its cofactor and the divisor times the value compared (`div_eq_iff`); a logarithm of q·eᵏ, its primes' (`Real.log_div`, `Real.log_mul`, `Real.log_pow`); an exponential of k + Σ nₚ·ln p (`Real.exp_add`, `Real.exp_nat_mul`, `Real.exp_log`); a sine or cosine of q·π, its whole turns, π and π/2 taken off and then the value Mathlib names; a power below 0, its value times the power above 0 being 1. An equation is then `linear_combination` of those facts and the multiples of (√p)² = p the sides differ by; a disequality, the difference times its cofactor a rational not 0, or of logarithms n times it ln r for r not 1; an order, `linarith only` over the difference's value and its sign as the decider shows it: a rational, ln r above 1 (`Real.log_pos`), or the bounds of its roots, π, e and logarithms (`Logarithms.log_above`, `Logarithms.log_below`) and of their products; a membership, the whole number; a link with letters, each part holding a letter an atom both sides share; a link of a chain in ℂ shown in ℝ and taken up by `exact_mod_cast` |
| transitivity | the links the checker placed (`CheckedTheorem::links`), each read the way the chain goes and from the side Lean states it, `.symm` of an equation it reads turned, joined by the lemma for each pair of relations (`le_trans`, `lt_of_le_of_lt`, `Eq.trans_le`, …), a chain going down taken up from its last link, a chain of equations the claim turns taken `.symm`; a chain of equations of things other than numbers, sets `A = B = C`, composed as it stands; a link in a narrower type taken up by `show … by exact_mod_cast`; `exact`, or `exact_mod_cast` where the claim is in another type; `linarith only` over the links where the checker met them only with identities dropped; a link of ℚ taken to ℝ as an order step's fact is |
| inequalities, rows | `linarith only` over the facts recorded in `orders`, or plain `linarith` where they are none; a disequality taken both ways split first by `Ne.lt_or_gt`; a `≠` a fact says, that fact (or `fun h => fact (by linarith only [h])` where Lean writes the two otherwise); one a `weakening` makes, `ne_of_lt`/`ne_of_gt`; a fact in a narrower type taken up by `show … by exact_mod_cast`, a claim in a narrower one proved in the wider and taken down; from ℚ to ℝ by the relation's lemma (`Rat.cast_le`, `Rat.cast_lt`, `Rat.cast_inj`) and `simp only` with ℚ's cast lemmas, which never goes through ℕ as `exact_mod_cast` does with a power of a numeral; `div_eq_mul_one_div` beside quotients the checker reads as one atom; a line stated under the claim's binders is read at them, `r1 x h_x`, and a bound the member implies is its guard; a define's equation in a wider type than every other fact is left out |
| antisymmetry | `le_antisymm` of the two lines in `antisymmetric` |
| restate | the line the checker found the claim in (`CheckedTheorem::restated`), a "for all" read at a block's letter with its `let` line as the guard (`ReadAt::opened_by`) |
| join | each part of the claim the line the checker found it in (`joined`), in `⟨…⟩` as the sentence joins them; a part Lean's types make true, `trivial`; a line Lean states under the claim's binders read at them |
| membership | a membership Lean's types give, `trivial`; one of ℕ₀ or ℕ, its bound by the said-once walk's reason, or beside a cited equation, the other side's bound carried along it (`le_of_le_of_eq`); a define's value, `rw [hD1]` and the value's bound; a function's value, its type applied to the point's membership; the other side of an equation put in ℕ₀ by the closure table, `Int.emod_nonneg` or `Nat.cast_nonneg`; an integer the cited lines give, as a witness |
| inspection | by the case recorded (`inspected`): one of a range, read from where the record places the membership (`OneOf::at`), its bounds worked out (`norm_num … at h; norm_cast at h; omega`); one of a listed set, its members' equations and `tauto`; nothing in ∅, `Set.notMem_empty`; a listed set's membership or size, `simp`; a set taken by a property from a listed set, `ext x; simp only […]; omega`, and its size, `rw [Set.ncard_eq_toFinset_card']; decide`; a set of things taken by a property from a listed set, member by member, as recorded, with `sep_insert_of` and `sep_insert_of_not`; a prime, `norm_num` |
| substitute | `Eq.subst` along the motive the checker's record gives, or `congrArg` of it for a side of the claim (**A substitution**); `exact` of the line where the record puts the equation at no place; rows one at a time |
| calculation | `calc`, each link by its reason; a link citing a line met as a cited hypothesis is (`said_proof`): turned, across casts, a congruence with its modulus; sides Lean writes alike, `rfl`; numerals alone, the line put in the goal and worked out; a chain worked in a wider type than its claim moves the goal there first, `qify` or `rify`, unless the claim is stated there already or the chain's counts are taken to integers after it |
| proof | `intro` |
| contradiction | `by_contra hS` where the supposition is the claim negated, `intro hS` where the claim is the supposition negated, the supposition ascribed or turned where Lean writes it otherwise |
| cases | `rcases` on the line that says "or" |
| both directions | `constructor` |
| induction | from 0 over ℕ₀, Lean's induction; from 1 over ℕ, `Nat.le_induction`; on the parts of a finite set from ∅, `LeanBridges.Sets.subset_induction` |

A requires line is a `have` proved by its own reason, and a define is
`set m : ℝ := … with D1`. A define the statement is read with is written out
in Lean's statement and named again by `set` at the head of the proof.
A step the checker read at a member (`at_member`) opens the claim's one
binder, `intro k h_k`, and proves the body at k. Any other step claiming a
"for all" proves it whole: a `join` or `restate` by the line itself, `:= s1`.
An instantiation leaving a letter open gives it the claim's letter
(`Instantiated::at_claim`), and its guard is `h_k`.

A requires line of a step that says "for all x" is stated under the claim's
binders, `have r102_3 : ∀ x : ℚ, 0 ≤ s x`. Inside its step it is the fact
at the step's x, `r102_3 x`. It says nothing of a later step's x, which is
another letter.

A step or a calculation row a define proves is `simp only [hD]`, with
`push_cast; norm_num` after it where the checker met the two sides otherwise
than as written, or where Lean casts a set's letter and the sides are not
alike once it is read as its value. A function the header lets is put in
the same way, by its hypothesis, and in a claim "for all" by `intro j h_j;
simp only [hD1 j h]`, h as the record says (`define_domains`). A
define by cases is put at the case the checker took (`define_cases`):
`simp only [hD, if_pos h₁, if_neg h₂]`, each condition by the line that
says it, and `push_cast; norm_num` after it where the case's value meets the
other side otherwise than as written. A function the header lets by cases
on a domain is put at the argument the record places in the domain
(`define_domains`), `simp only [hD1 _ h, if_pos h₁]`. A condition a line
states in a narrower type than the claim's is restated in it: by
`exact_mod_cast` of the line, or, of numerals alone, by `norm_num`. A
definition read backwards is `(…).mpr w` alone where Lean states its left
side as it writes the claim. The comparison reads an integer's `toNat` of
naturals cast up as that natural; inside a witness's `refine` the claim is
the goal left open.

## How a block ends

A block, a part of one, or the theorem ends on its last step. Where that step
says what is owed as Lean writes both, its proof is the goal's: its `have`
goes, a term proves the goal by `exact`, and a block's tactics stand in its
place. Where the checker met them otherwise than as written (`ends_met`),
the step's name closes it by the one tactic that meeting gives, `⟨a, b⟩` for what is owed as an
"and" of its sentences and `trivial` for a part Lean's types make true. What a
block owes is the record's (`Owed::written`). An induction's part owes the
motive Lean makes at the start or at k + 1, the cast of the letter a cast of
that value, `↑(k + 1)`, with the binders its own lines introduce taken off.

A step written `contradicting N` closes on the two lines: the one that says
the other negated, applied to it, `exact h₁ h₂`, where the goal is False, and
`exact absurd h₂ h₁` in a case or a proof block whose assumption cannot hold.
A step shown impossible closes its block itself. A case that says it is the
claim closes by its assumption.

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
