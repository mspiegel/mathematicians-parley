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
"for all" is read at, what the lines in scope bound below and make finite,
and the page with outside defines written out are the record's
(`docs/CHECKER.md`). The writer keeps the choices that are Lean's own: the
Lean type of an item's untyped letter, and how a fact is written, a range
line's integer `∃ m : ℤ, ↑m = k ∧ m ∈ …` among them.
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
writer. It states it as `have hI : … := by parley_instance (item …)` and
closes the step's claim from `hI` as the checker met the two (`exact`,
`.symm`, or the identities the meeting names). `parley_instance`
(`InstanceTactics`) reads the item's Lean statement, written once over any
ring or set, in that spelling by the simp set `parley_spelling`, whose every
rule is one representation fact, then moves the casts of the two alike
(`exact_mod_cast`). A fact found missing is tagged into the set, never added
at a step.

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
line says is proved where it is put: by `parley_arith` where the step works
it out, and by the define's hypothesis, turned where the step writes the
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
defines kept (`FirstAt::written`). The result is stated by a `have`, so that
a numeral exponent defaults to ℕ, and closed by `push_cast at h ⊢` and
`exact_mod_cast h`. At a place that is an exponent, the motive's letter is
written as Lean writes the exponents at both its values
(`Writer::natural_form`): as its `toNat` where both are written so, a
numeral put counting so; else an integer, its powers converted to the
claim's after, the exponent's fact from the record, as a citation's is (see
"Number types"). A
substitution keeps the earlier ways, registered as "substitute: equation put
in", where the record has none or the motive does not state it as written:
- a place that is an exponent in a type with no integer powers, ℤ;
- a fact the line implies and does not write;
- a line, or a motive, of a term written as the whole number it is;
- a line in a narrower type than the equation; in a wider one, the equation
  is first stated in the type its place is written in;
- places of more than two types, or of two where an exponent's form or a
  whole-number line is among them;
- an equation of rationals put into a wider field at a place written in its
  own type;
- an equation with a side holding a cast of a `toNat`.

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
  the claim's, by `parley_of_complex` from ℂ and `parley_rat_of_real` from ℝ,
  as an instance is;
- where the step goes through named numbers its proof puts first, as the
  casts of those numbers (`Classical.choose_spec`), and the checker met the
  item as written: an equation or order is then the item's relation with
  each side cast up as a whole, `exact_mod_cast` of the item where the cast
  table says `norm_cast` moves a cast through that relation
  (`casts::norm_cast_lifts_relation`); a range member Lean writes as the
  integer that is it, `⟨_, rfl, item⟩`;
- where the claim is an "and" the checker met as written, part by part, the
  item named once, `have h := …`: "and" stands in no other order, so part j
  of the item is part j of the claim. A membership of ℕ or ℕ₀ Lean writes as
  an integer of a wider term, `∃ m : ℤ, 0 < m ∧ ↑m = t`, beside the item's
  `0 < v` is `⟨_, h.j, rfl⟩`; an equation or order whose casts `norm_cast`
  all moves is `by exact_mod_cast h.j`.

A step no rule decides keeps its `first |` list, and `tests/first_lists.txt`
keeps each such list with its reason; it holds none at present.
`tests/lean_closers.rs` names a step where each rule decides.

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
writer cannot write is a gap of the Lean build, and the gate is red. A
theorem the checker refuses, or a file Lean does not read, is a failure: it
is not built, nor is what cites it, every such failure is reported in one
run, and the build exits 1 (`ELABORATION.md`).

The Lean build is to build every theorem the Metamath build does. Leaving
theorems out (`lean::coverage`) is scaffolding for the build while it grows
by fields, and goes once nothing is left out. Its rules are lookups of
fields: a notation's `lean-builds`, an item's `lean-proof`, a function's
definition. A limit of the writer's own is a decline the writer gives at the
step, from the checker's record, not a reading coverage makes of the page.

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
  are false.
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
  turning one into the other. A function's define that says its values are
  integers is a function to ℤ whose values are its kind's witnesses,
  `obtain ⟨f, hD1⟩ : ∃ g : ℤ → ℤ, ∀ a ∈ X, ↑(g a) = v`, its equation said
  at each member.
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

No theorem is given more than Lean's default budget of 200,000 heartbeats.
A step proves what it can from the record, so a search is left only where
no line states the fact.

| method | Lean |
|---|---|
| a citation | the item's theorem at the citation's values, each hypothesis by the line the checker found it supplied by (`Cited::supplied`), the number-system fact of an item letter's binder among them, `parley_side` where none states it; a hypothesis whose set the citation gives as all of ℝ or a range is taken from its line all the same, and only where none states it read by `parley_whole_side`; `.mp` from the line the reading starts from, `.mpr` with the right side built from its parts (`Cited::unfolded`): each witness, and each fact by the line that states it, as Lean states the part; the side whole by `parley_side` where Lean's statement does not take apart as the page's does |
| obtain | `obtain ⟨k, …⟩ :=` the item's or the line's "there is"; a part the checker met otherwise than as written, or that Lean casts otherwise, is obtained under a name of its own and stated after as the page says it |
| exhibit | `⟨w, h⟩`, each fact of the values by the line the checker found it stated by (`Exhibit::shown`); `parley_side` where none does |
| instantiate | the sentence the checker instantiated, at the values given, a letter given none at the block's letter, each guard and condition by the line the checker found it supplied by (`Instantiated::guards`, `Instantiated::conditions`), `parley_side` where none states it; closed by the instance's meeting with the claim, or, where Lean states the two otherwise, by `linear_combination`, `linarith` or `exact`, and `parley_side` where the instance is in a field the claim is not |
| algebra | `ring`; from cited lines, `linear_combination` with the multipliers the method's decision finds, the defines written out only at the lines it cites and at its goal (`Proof::rewritten_at`), so a line it does not cite keeps its letters |
| arithmetic, real arithmetic | `parley_arith` |
| transitivity | the links the checker placed (`CheckedTheorem::links`), each read the way the chain goes and from the side Lean states it, `.symm` of an equation it reads turned, joined by the lemma for each pair of relations (`le_trans`, `lt_of_le_of_lt`, `Eq.trans_le`, …), a chain going down taken up from its last link, a chain of equations the claim turns taken `.symm`; a link in a narrower type taken up by `show … by exact_mod_cast`; `exact`, or `exact_mod_cast` where the claim is in another type; `linarith only` over the links where the checker met them only with identities dropped; a link of ℚ taken to ℝ as an order step's fact is |
| inequalities, rows | `linarith only` over the facts recorded in `orders`; a disequality taken both ways split first by `Ne.lt_or_gt`; a `≠` a fact says, that fact (or `fun h => fact (by linarith only [h])` where Lean writes the two otherwise); one a `weakening` makes, `ne_of_lt`/`ne_of_gt`; a fact in a narrower type taken up by `show … by exact_mod_cast`, a claim in a narrower one proved in the wider and taken down; from ℚ to ℝ by the relation's lemma (`Rat.cast_le`, `Rat.cast_lt`, `Rat.cast_inj`) and `simp only` with ℚ's cast lemmas, which never goes through ℕ as `exact_mod_cast` does with a power of a numeral; `div_eq_mul_one_div` beside quotients the checker reads as one atom; `parley_order` where the record has no entry |
| antisymmetry | `le_antisymm` of the two lines in `antisymmetric` |
| restate | the line the checker found the claim in (`CheckedTheorem::restated`), a "for all" read at a block's letter with its `let` line as the guard (`ReadAt::opened_by`); `parley_side` where no one line states it |
| membership, join, inspection | `parley_side`; an integer the cited lines give, as a witness |
| substitute | `Eq.subst` along the motive the checker's record gives, or `congrArg` of it for a side of the claim (**A substitution**); `exact` of the line where the record puts the equation at no place; else `parley_subst` from the equation and the line the record names, the equation either way round; rows one at a time |
| calculation | `calc`, each link by its reason |
| proof | `intro` |
| contradiction | `by_contra hS` where the supposition is the claim negated, `intro hS` where the claim is the supposition negated, the supposition ascribed or turned where Lean writes it otherwise |
| cases | `rcases` on the line that says "or" |
| both directions | `constructor` |
| induction | from 0 over ℕ₀, Lean's induction; from 1 over ℕ, `Nat.le_induction`; on the parts of a finite set from ∅, `LeanBridges.Sets.subset_induction` |

A requires line is a `have` proved by its own reason, and a define is
`set m : ℝ := … with D1`. A define the statement is read with is written out
in Lean's statement and named again by `set` at the head of the proof.

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
