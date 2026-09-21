# The database and the proof files

`SYNTAX.md` fixes how a proof is written. This document fixes where proofs and
the items they point to are stored, what a stored record looks like, and what
the merge of the ten pilots' item tables decided.

## Layout

```
db/notation.records      symbols a claim may use
db/methods.records       the justification vocabulary
db/items.records         definitions and theorems
proof/*.proof       the proof skeletons, one file per pilot
pilot/*.md          the design commentary for each pilot
```

A `.proof` file holds only the skeleton. `SYNTAX.md` says the stored text is
every line a field the elaborator reads and nothing else, so the commentary that
used to surround these proofs in markdown stays in `pilot/`, which now points at
the proof file rather than containing it.

Getting out of markdown also repaired the database. Inside a markdown table a
vertical bar has to be escaped, so absolute value, cardinality and distance were
all stored with backslashes inside the formula. The `.records` files store them
plainly.

## Record format

A record begins at column 0 with its kind and name. Its fields are indented two
spaces, one field per line, the field name then its value, continuation lines
indented further. A line beginning with `#` is a comment.

An item's statement is written in the theorem form of `SYNTAX.md`: labelled
`let` and `assume` lines, then a `then` line. The database and the proof files
therefore share one grammar, and one parser reads both.

Every item in `db/items.records` carries exactly one of three fields saying where it
comes from:

| field | meaning | count |
|---|---|---|
| `proved-in` | a proof file in this corpus proves it | 14 |
| `metamath` | a set.mm label or labels supply it | 60 |
| `open` | neither; it is cited but unproved and unbridged | 14 |

An item with `proved-in` carries no statement here. The statement lives at the
head of its proof file, so that it has one home and cannot drift. This is the
rule that the collisions below were caused by breaking.

A definition may also carry a `target`, which says which set.mm theorem
unfolds it, or, for one stated as an equation, one theorem per `then` group:
`def:S` names `fsum1, fsump1`, and which clause a step uses is decided by
which one's conclusion is what the step claims. That is not what `metamath` says: `metamath` says what the
definition means, and `def:odd` gives `not 2 ∥ n`, where unfolding it to the
existential the `then` line states is `odd2np1`. An elaborator needs the
second and cannot derive it from the first. A second entry, `equation
reversed`, says the theorem writes its equation the other way round from the
`then` line, which `odd2np1` and `divides` both do. `db/notation.records` documents
the same field on the notation side.

The corpus holds 97 items, 27 definitions and 70 theorems, 56 notation records
declaring 74 patterns, and 14 methods. The ten proofs make 193 citations to 76
distinct items. Every pointer resolves, and every `def:` or `thm:` prefix
matches the kind of the item it names.

A notation record declares how its notation parses: the mixfix pattern with `_`
for each hole, the sort each hole takes, what the pattern yields, its
precedence level, its associativity where one is needed, and whether one of its
patterns is the negation of another. There are two
shapes only, a mixfix pattern and juxtaposition, and a binder is a mixfix with
a hole marked as binding. `db/notation.records` describes the fields, and one
`precedence` record declares the order between levels as a partial order, so a
formula mixing two levels that convention does not relate is rejected rather
than guessed at.

Two things about a notation are then mechanical and the checker enforces both:
that the holes a record declares match the holes its patterns have, and that a
pattern declares an associativity exactly when it can nest in itself, meaning
both edges are holes and what it yields fits those holes. Ten of the 55 records
meet that condition.

## The character set

The files are UTF-8 in Normalisation Form C. **An implementation works in
Unicode scalar values. UTF-16 is not used anywhere in this project**, neither
as a file encoding nor as the internal string representation of a tool that
reads these files. Three facts about what the corpus actually contains explain
the rule and constrain what else a reader must do, and the checker enforces all
three rather than trusting them.

- **One character lies outside the Basic Multilingual Plane.** The script
  capital P of the power set notation, 44 uses. In UTF-16 it is two code units,
  so lengths, column positions and any character-by-character scan go wrong
  silently on exactly the notation the set-theoretic proofs are written in.
  That is the reason for the rule above, and it rules out the languages whose
  strings are UTF-16, Java, JavaScript and C# among them.
- **Two characters have decomposed forms.** Not-an-element and not-equal can
  each be written as a base character plus a combining slash. An editor that
  normalises differently would change the archive without anyone editing it.
  Input is normalised on read and anything not already in Form C is rejected.
- **Four look-alike pairs are in use.** The minus sign appears 141 times, the
  prime 53, the middle dot 88 and the set-minus 18. Each has an ASCII twin that
  renders almost identically. The notation database lists every symbol a claim
  may use, so it doubles as a whitelist, and a character outside it is an error
  wherever it appears.

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
  `|A|` is cardinality and `|PQ|` is distance. Settled since: each is its own
  notation record and they are told apart by the sort of the hole, which
  `GRAMMAR.md` describes. It is the only overloaded pattern of the 63 declared.
- **Recursive definitions do not fit the theorem form.** `def:S`, `def:G` and
  `def:factorial` have a base sentence with no hypothesis and a step sentence
  with one, and the form puts all hypotheses before all conclusions. They are
  written with two `then` groups, which no other record uses.
- **`thm:side-angle-side` and its one citation disagree on variable names.** The
  statement uses P, Q, R, P′, Q′, R′ and the isosceles proof instantiates A, B,
  C, A′, B′, C′. One of the two must change. Settled since: the proof changed,
  because every other geometry item names its points P, Q and R.
- **`thm:triangle-permute`'s conclusion was not a formula.** "Any ordering of P,
  Q, R forms a triangle" is replaced by `thm:triangle-swap` and
  `thm:triangle-rotate`, which generate all six orderings and are the two the
  isosceles proof cites.
- **Set-existence hypotheses are inconsistent.** `thm:well-ordering` and
  `thm:completeness` are stated with `assume S ⊆ ℕ` and no `let S be a set`,
  because that is what the pilot tables said and what the proofs discharge.
  Whether the set-existence hypothesis belongs there is open.
  `thm:card-bijection` and `thm:card-disjoint-union` were the same and now
  carry the `let` lines, because without them their statements could not be
  read: `|Y| = m` fits both cardinality and absolute value.
- **The isosceles proof had one step that broke the calculation rule.** A chain
  line cited a theorem where the rule allows only a cited line. It was the
  checker's first true positive and is repaired: the theorem is now step 2 and
  the chain cites that number.
- **`parley/gate.py` is what must be green before a commit.** Five stages: ruff
  over the tools, the checker over the corpus, the planted defects that prove
  the checker still catches things, every set.mm label the database names, and
  a verifier over all 23 proofs the elaborator has written. The lint settings
  are in `ruff.toml`, which turns off the ambiguous-character rules because
  this corpus is written in the characters they object to. Nothing the gate
  leans on is vendored: ruff is looked for on PATH, and set.mm and mmverify.py
  belong to metamath and are found by `SET_MM` and `MMVERIFY` or by a copy or
  link at the root. Each missing one fails the gate and says how to supply it,
  because a gate that skipped a stage would be saying green about something it
  had not looked at.
- **The hypotheses of `algebra` and `inequalities` are still unwritten**, as
  `SYNTAX.md` records.
- **Every formula in the corpus parses, and none is ambiguous.** That is 313
  sentences in the ten proofs and 131 statements and assumptions here, and the
  checker parses all of them on every run. Getting there took six notations
  nobody had declared, eight records that never said what their names were, and
  three defects in the parser itself.
- **Every citation's claim is what the item it cites concludes.** All 109 of
  them, under the moves `SYNTAX.md` states: a sentence claimed as it stands, a
  biconditional read in either direction when a fact gives the other side, a
  conditional giving its consequent, a claim taking one conjunct, and a "there
  is" supplied by a fact giving an instance. The set-builder needed one more
  rule, which is that a property is worked out from the occurrence inside the
  braces, where the answer is forced, and only checked outside.
- **Every citation supplies the hypotheses of what it cites.** All 106 of them,
  checked by matching the item as a pattern against the facts the step names,
  so the 37 citations that write no instantiation are read like the 69 that do.
  Eleven citations were short of a hypothesis when the check first ran: six
  interval citations missing a bound, two recursive definitions missing the
  line that types their parameter, Bezout's step 14 missing two integer
  memberships, a disjunctive syllogism whose two spellings of one negation did
  not match, and a bijection that adds an element without saying it was absent.
  The last needed a new item, `thm:not-in-difference`.

## Nine open items

`def:collinear`, `def:congruent`, `def:function`, `def:point`, `def:triangle`,
`thm:add-element-bijection`, `thm:point-right`, `thm:powerset-split`,
`thm:powerset-split-disjoint`.

Four of the nine are geometry, which is what the isosceles pilot predicted:
the proof is trivial and the database is not. Three are the counting lemmas the
subsets pilot leaned on. One is the lemma the intermediate value pilot needs
only because the language has no `min`, and one is what `def:function` would
have to say about a map.

Five more were open and are not. `thm:angle-symmetric`, `thm:side-angle-side`,
`thm:triangle-swap` and `thm:triangle-rotate` are proved in
`elaboration/geometry.mm`, which is a third way to supply an item: neither a
set.mm label nor a proof file in the readable layer, but a Metamath proof
below it, for what set.mm does not state and the readable layer cannot.
`def:angle` closed differently — it carries a `symbol` and a `defines` now,
and is the one definition in this corpus that introduces a constant.

The four that remain open in the geometry are open for a reason rather than
for want of work. Incidence is a primitive, and `def:collinear` says so: in
the plane collinearity is (R − P)/(Q − P) being real, and subtraction takes
numbers while P, Q and R are points, so the sorts that stop |CA| reading as a
product stop this too. The notation carries a target, so a claim of
collinearity elaborates; what has no readable statement is the equivalence.
