# The database and the proof files

`SYNTAX.md` fixes how a proof is written. This document fixes where proofs and
the items they point to are stored, what a stored record looks like, and what
the merge of the ten pilots' item tables decided.

## Layout

```
db/notation.db      symbols a claim may use
db/methods.db       the justification vocabulary
db/items.db         definitions and theorems
proof/*.proof       the proof skeletons, one file per pilot
pilot/*.md          the design commentary for each pilot
```

A `.proof` file holds only the skeleton. `SYNTAX.md` says the stored text is
every line a field the elaborator reads and nothing else, so the commentary that
used to surround these proofs in markdown stays in `pilot/`, which now points at
the proof file rather than containing it.

Getting out of markdown also repaired the database. Inside a markdown table a
vertical bar has to be escaped, so absolute value, cardinality and distance were
all stored with backslashes inside the formula. The `.db` files store them
plainly.

## Record format

A record begins at column 0 with its kind and name. Its fields are indented two
spaces, one field per line, the field name then its value, continuation lines
indented further. A line beginning with `#` is a comment.

An item's statement is written in the theorem form of `SYNTAX.md`: labelled
`let` and `assume` lines, then a `then` line. The database and the proof files
therefore share one grammar, and one parser reads both.

Every item in `db/items.db` carries exactly one of three fields saying where it
comes from:

| field | meaning | count |
|---|---|---|
| `proved-in` | a proof file in this corpus proves it | 14 |
| `metamath` | a set.mm label or labels supply it | 60 |
| `open` | neither; it is cited but unproved and unbridged | 12 |

An item with `proved-in` carries no statement here. The statement lives at the
head of its proof file, so that it has one home and cannot drift. This is the
rule that the collisions below were caused by breaking.

The corpus holds 86 items, 26 definitions and 60 theorems, 24 notation records
and 14 methods. The ten proofs make 128 citations to 68 distinct items. Every
pointer resolves, and every `def:` or `thm:` prefix matches the kind of the item
it names.

## What the merge decided

**`def:function` was two items under one name.** The Cantor pilot stated it as a
biconditional defining `f : A → B`; the intermediate value pilot stated it as
the derived fact that a function's values land in its codomain, and cited it
three times for exactly that. The fact is now `thm:function-value` and those
three citations are renamed. `def:function` keeps the name for the definition,
which is `open` because the Cantor pilot's row is truncated and no proof cites
it.

**`thm:real-closure` had two statements.** The triangle inequality pilot gave
addition, the intermediate value pilot gave addition and subtraction. Merged to
both sentences, which is the shape `thm:int-closure` and `thm:nat-closure`
already have. Neither proof changes.

**Five statements were cross-references.** `def:set-builder` and
`thm:set-builder-subset` read "as in the Bezout pilot" and are now written out
once. `thm:abs-bounds` read "from the triangle inequality pilot" and is now
`proved-in` that file.

**Theorems are stored in dependency order.** A pointer must resolve to something
earlier, as `READERS.md` requires. Only the √2 file needed reordering: it now
runs odd-square, even-square, sqrt2-irrational, where the pilot put the main
theorem first. Nothing else moved.

**Six items had no row anywhere.** `thm:sqrt2-irrational` was the only pilot's
main theorem missing from its own table. `def:set-image` is named in `SYNTAX.md`
and was in no table. `def:angle` appears only in the isosceles findings, though
the ∠ notation needs it. Notation for ℕ₀, for the general power `^` and for
binary − was used by five pilots and declared by none.

**`def:` says what an item is to Reader A, not what set.mm calls it.** Several
definitions name a word for a construct set.mm already has: even is divisibility
by two, irrational is membership of the reals minus the rationals, and absolute
value elaborates to a pair of theorems rather than a definition. The triangle
inequality pilot already settled the naming. What is not settled is decision 12
of `GOALS.md`, which wants a definitional axiom checked for introducing one new
symbol and being eliminable. These items introduce no symbol, so that check does
not apply to them as written, and what it should say instead is open.

## What the merge found and left alone

These are for the checker to flag or for a later decision. None was silently
repaired.

- **Three notations collide on the vertical bar.** `|x|` is absolute value,
  `|A|` is cardinality and `|PQ|` is distance. Telling them apart needs the kind
  of the argument, which the readable layer does not track. The formula parser
  will have to face this.
- **Recursive definitions do not fit the theorem form.** `def:S`, `def:G` and
  `def:factorial` have a base sentence with no hypothesis and a step sentence
  with one, and the form puts all hypotheses before all conclusions. They are
  written with two `then` groups, which no other record uses.
- **`thm:side-angle-side` and its one citation disagree on variable names.** The
  statement uses P, Q, R, P′, Q′, R′ and the isosceles proof instantiates A, B,
  C, A′, B′, C′. One of the two must change.
- **`thm:triangle-permute`'s conclusion is not a formula.** "Any ordering of P,
  Q, R forms a triangle" needs either one theorem per ordering or a form the
  language does not have.
- **Set-existence hypotheses are inconsistent.** `thm:well-ordering`,
  `thm:completeness`, `thm:card-bijection` and `thm:card-disjoint-union` are
  stated with `assume S ⊆ ℕ` and no `let S be a set`, because that is what the
  pilot tables said and what the proofs discharge. Whether the set-existence
  hypothesis belongs there is open.
- **The isosceles proof has one step that breaks the calculation rule.** Step 2
  cites a theorem on a chain line where the rule allows only a cited line. The
  pilot left it deliberately as a reminder, and so does the proof file. It should
  be the checker's first true positive.
- **The hypotheses of `algebra` and `inequalities` are still unwritten**, as
  `SYNTAX.md` records.

## Twelve open items

`def:angle`, `def:congruent`, `def:function`, `def:point`, `def:triangle`,
`thm:add-element-bijection`, `thm:angle-symmetric`, `thm:point-right`,
`thm:powerset-split`, `thm:powerset-split-disjoint`, `thm:side-angle-side`,
`thm:triangle-permute`.

Seven of the twelve are geometry, which is what the isosceles pilot predicted:
the proof is trivial and the database is not. Three are the counting lemmas the
subsets pilot leaned on. One is the lemma the intermediate value pilot needs
only because the language has no `min`.
