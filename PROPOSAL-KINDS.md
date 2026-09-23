# Proposal: sets have kinds, and the page never writes them

A proposal for `READERS.md` and `GRAMMAR.md`, for review. Nothing here is
decided until it is moved into those documents.

## The question

`ELABORATION.md` records one case as open: `thm:powerset-split-disjoint` needs
`a ∈ S ∪ {a}`, which set.mm proves only for an `a` that is a set, and the kernel
gets that from `a ∈ X` by `elex`. A reader told `let a ∈ X`, with X a set of
numbers, does not think a is a set. The proof is held out of `proof/` until it
is decided which gives way.

The case is wider than `elex`. A name a step introduces — by `fix`, a
quantifier, or `obtain` — becomes a kernel setvar, and the kernel has it as a
set for nothing (`vex`), whatever the page says it is. Neither is recorded as a
rule anywhere.

The page-level policy is already settled: `GRAMMAR.md` gives numbers the sort
*number* and sets the sort *set*, and a number is never a set on the page. What
is open is the reader's model of a set, and what the kernel may use behind it.

## The reader's model

A reader thinks of a set as having a kind. A set of numbers is a different thing
from a set of points, and a set of sets of numbers is different again. The one
escape from the hierarchy is a statement about every set, which is about a set
of any kind.

This is consistent. It is the simple theory of types — the hierarchy that avoids
the set of all sets — with the escape as parametric polymorphism, and it is how
set theory is presented in Isabelle/HOL and Lean (`Set α`) and how most
textbooks speak whatever their foundation.

It does not contradict "math is not a typed system" (2026-09-18). That was about
numbers: ℕ, ℤ and ℝ are not different types with casts between them, and they
stay that way. *Number* is one kind, ℕ ⊆ ℤ ⊆ ℝ is an inclusion, and ℕ is a set
of numbers rather than a kind. What gets a kind is a set, by what it holds.

## The rules proposed

1. **A set has the kind of its elements, and kinds nest.** The kinds of things
   are *number*, *point*, *function* and *set of k* for any kind k. `𝒫X` is a set
   of sets of X's kind; `X ∪ Y` and `X ∩ Y` join two sets of one kind; `{t ∈ X :
   P(t)}` has X's kind; `ran f` has the kind of f's values.

2. **Nobody writes a kind.** Mathematics does not say "X and Y are sets of the
   same kind", and neither does the page. Kinds are read off how the text uses
   its names: `X ∪ Y` makes X and Y one kind, `a ∉ X` makes a the kind of X's
   elements, `let s ∈ S` makes s the kind of S's elements. What the text does
   not link stays independent. Each name gets the most general kind the text
   allows, which is unique, so two implementations reading the same statement
   agree.

3. **"A set of any kind" is a kind variable.** `let X be a set` says X is a set
   of some kind, one kind throughout. Two such lines are independent unless the
   text links them: `thm:card-bijection` relates a set to a set of another kind,
   `thm:card-disjoint-union` writes `X ∪ Y` and so relates two of one kind.

4. **A clash is a defect.** A statement that joins a set of numbers to a set of
   points is reported where it is written, as a notation given the wrong sort is
   today.

5. **Being a set, in set.mm's sense, is the kernel's.** The kernel distinguishes
   sets from proper classes, and uses `elex`, `vex` and their kind to say that a
   thing is not a proper class. On the page an element of a set of any declared
   kind is a legitimate thing of that kind and nothing more needs saying. This
   is the same category as class variables and set-existence apparatus, which
   `READERS.md` already hides from Reader A, and the same move as its existing
   rule that "a set built from sets is a set … which is the sort again": an
   element of a set is a thing of its kind, which is the type again.

## What it reverses

- **`GRAMMAR.md`, "Sorts": "Every sort is written on the page, and a parser
  infers none."** Declarations stay written; what is inferred is how the kinds
  of the names relate. The rule's stated reason — a parser chasing a cited
  item's conclusion to learn a name's sort, and two implementations stopping at
  different depths — does not apply: inference reads only the text in front of
  it, and its answer is unique.
- **The 2026-09-19 decision that sorts stay flat and a set does not carry the
  kind of its elements.** That was decided because no notation in the corpus
  needed element kinds to be told apart. This proposal reverses it for the
  reader's sake, not the parser's.
- **`GRAMMAR.md`, "What flat sorts cost in set theory"** is rewritten. Its
  conclusion survives: on the page a number is not a set, and theorems whose
  content is the von Neumann encoding still want a declared coercion.

## What stays

- Sorts pick notations and never meanings; `|x|` is still decided by what x is.
- *Number* is one kind; ℕ ⊆ ℤ ⊆ ℝ is an inclusion.
- Points are their own kind, as `GEOMETRY.md` already has them over ℂ.
- The parser checks every hole.
- A declaration (`let X be a set`, `let n ∈ ℤ`, `let f : A → B`) is still a
  sort stated once, and a step does not cite it.
- Nothing is assumed: a membership a cited item demands is still written.

## What it touches

| where | today | under the proposal |
|---|---|---|
| `proof/subsets.proof`, `add-element-bijection` | `let a be a set`, `assume a ∉ X`, then `S ∪ {a}` with `S ⊆ X` | `let a ∉ X`: a has the kind of X's elements |
| `db/items.records`, `card-singleton` | `let x be a set` for `\|{x}\| = 1` | `let x be an element`: x of any kind |
| `difference-set`, `not-in-difference`, `added-elements-are-new` | `a` used and never introduced | `let a be an element`; its kind follows from `X ∖ {a}` or `s ∪ {a}` |
| `card-disjoint-union`, `card-bijection` | two `let … be a set` lines each | unchanged: the text already says which kinds are linked |
| `proof/subsets.proof` step 1.2.1.3 | `requires X ∖ {a} is a set` | removed: the type again, and already against `READERS.md` as written |
| `thm:powerset-split-disjoint` | held out of `proof/`, item `open` | returns: `a ∈ S ∪ {a}` needs nothing on the page |
| `ELABORATION.md`, "That an element is a set" (two places) | open | resolved by rule 5 |
| `proof/intermediate-value.proof` | five uses of `s` of no known sort | s is a number from `let s ∈ S` |

## What it asks of the tools

- **Parser and checker:** kinds with parameters and variables, and inference by
  unification over each statement and each proof. This is the "small type system
  with parameters" the flat design avoided; the corpus gives it a bounded job.
- **Elaborator:** the structural "is a set" rule gets its leaves — any name of a
  declared kind — so the chain behind the side-condition depth loses its four
  sethood levels, and `settle`'s bound can fall from five to about two.

## Decisions

1. **How a name is introduced without claiming a kind — decided (2026-09-23).**
   `let a be a set` claims too much for `add-element-bijection` and
   `card-singleton`. Two introductions are added:
   - `let a ∉ X`, as `let a ∈ X` is allowed: a is a thing of the kind of X's
     elements, not in X. `add-element-bijection` reads `let X be a set`,
     `let a ∉ X`.
   - `let x be an element`, which claims nothing, and x's kind comes from the
     text. `card-singleton` reads `let x be an element`, then `|{x}| = 1`.
2. **Sets mixing kinds are refused — decided (2026-09-23).** `{3, P}` for a
   number and a point, or `{1, {1}}` for a number and a set of numbers, has no
   kind, and the page reports it as it reports any clash (rule 4). The school
   reader never forms one, "a set of any kind" keeps meaning one kind
   throughout, and no statement or proof in the corpus forms one. Where
   mathematics does want one — `{∅, {∅}}`, a tuple encoded as a set — it is the
   encoding `GRAMMAR.md` already sends to a declared coercion, and the remedy is
   the same: a database addition that makes the mixing visible.
3. **`∅` takes whatever kind its context gives it — decided (2026-09-23).** Each
   `∅` is read off its use, as any name is under rule 2: in `X = ∅` it is the
   empty set of X's kind, in `U ∩ T = ∅` an empty set of subsets, and in
   `𝒫∅ = {∅}` the two are related kinds fixed by the line. A bare `|∅| = 0`
   holds at every kind. "The empty set of points is the empty set of numbers"
   is a clash and cannot be written; no reader writes it and nothing in the
   corpus does. The kernel has one `∅` and is unaffected: kinds are the page's.
4. **"For every set X" inside a proof reads at one kind — decided (2026-09-23).**
   A quantifier over sets inside a proof ranges over sets of one kind, the kind
   the text fixes; the subsets induction is about sets of A's kind throughout,
   and its hypothesis is applied only to `X ∖ {a}`, of the same kind. A
   theorem is general in its kinds when cited, so each citing step picks the
   kind it needs. A lemma a proof needs at two kinds is stated as its own
   theorem. Quantifying over kinds inside a formula is what inference cannot
   recover without the writer naming the kind, which rule 2 does not ask; the
   kernel's "for every set" is stronger and proves the stronger thing.

## Measured (2026-09-23)

A scratch checker inferred kinds under these rules over every statement and
proof: a signature for each of the 27 notations with a set, function, property
or variable hole, the rest from their declared sorts, and unification over each
theorem's hypotheses, defines, openers, claims and requires lines in order, and
across each citation that writes `v := t`.

- **No clash** in 16 proofs and 108 statements, and no line unread. Every name a
  proof introduces gets a consistent kind; IVT's `s` is a number from
  `let s ∈ S`.
- **Names used and never introduced are all in items**, none in proofs:
  statement letters, definitions' subjects, sets assumed with no `let`, and a
  free `a` in nine items — `difference-set`, `subset-of-difference`,
  `difference-of-union`, `difference-absent`, `not-in-subset`,
  `in-union-singleton`, `added-elements-are-new`, `not-in-difference`,
  `image-of-injection`. Each `a` is inferred the kind of the set it is taken
  from, and each group of sets one kind.
- **One statement narrows another.** Citing `add-element-bijection`, whose
  `let a be a set` makes its X a set of sets, turns `subsets-count`'s X from a
  set of any kind into a set of sets. A kind variable can always be narrowed,
  so this is silent: read typed, the counting proof would prove its result for
  sets of sets only. `let a ∉ X` removes it.
- **The kernel uses "is a set" in three theorems** — `cantor`,
  `add-element-bijection`, `subsets-count` — and never uses `elex`. Every use
  is of a declared set, a construction (`pwexg`, `difexg`, `rnexg`, `mptexg`,
  `unexg`, `snex`, `rabexg`, `0ex`), or a name ranging over subsets (`vex`),
  except one: `subsets-count` step 1.2.1.4 proves by `vex` that `a`, obtained
  from X, is a set, because `add-element-bijection` asks it. That is the
  setvar case, in the corpus once. Under rule 5 the kernel still needs it
  behind `S ∪ {a}`, as apparatus rather than as a claim on the page.
