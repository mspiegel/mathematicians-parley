# The database and the proof files

`SYNTAX.md` fixes how a proof is written. This document fixes where proofs and
the items they point to are stored, what a stored record looks like, and what
the merge of the ten pilots' item tables decided.

## Layout

```
corpus/db/notation.records   symbols a claim may use
corpus/db/methods.records    the justification vocabulary
corpus/stdlib/*.records      the standard library: axioms, theorems and
                             definitions, some marked mundane
corpus/elaboration/          what parley build writes from all of it
proofs/*.proof               the proof skeletons, one file per pilot
tests/stdlib/*.proof         a test for each library item no proof cites
docs/*.md                    the design documents, this one among them
docs/pilot/*.md              the design commentary for each pilot
```

Everything is read from the directory `parley` is run in. A name is read from
inside `corpus/`, so that directory's name is in none: the records of
`corpus/stdlib/numbers.records` are the module `stdlib/numbers`.

## Names and the standard library

An item is named by the file that holds it and then its own name:
`stdlib/divisibility/odd`, `stdlib/numbers/int-real`,
`proofs/triangle-inequality/abs-bounds`. The file is its path without the
extension, so the full name says where to look. A proof file imports each item
it cites from another file by that full name, one to a line, after the words
its record's header says before its name, `import mundane theorem
stdlib/numbers/int-real`; a step then cites it by its name and the prefix
those words give, `mun:` for an item taken for granted and the kind's
otherwise, `mun:int-real`. A theorem of the citing file is
cited the same way, `thm:odd-square`, and has no import. `GRAMMAR.md` gives
the rules under "Names". Prose outside a proof, as in this document and the
records' notes, names an item by its prefix and full name,
`mun:stdlib/divisibility/odd`, since it has no imports to say where to look.

The standard library is every item a set.mm label supplies or that is still
open: what a proof cites, or may, and this corpus does not prove.

An item's statement is written by hand beside the lemma it names, and only a
citation that elaborates asks whether the two agree: the elaborator applies
the lemma to what the item says, and the result verifies or it does not. So
every item is cited by a proof, or by its test in `tests/stdlib/<subject>.proof`,
a theorem whose one step cites it: the item's hypotheses, and its conclusion,
or for a definition its right side from its left. One direction is enough,
since the lemma applied either way has the whole statement to match. The
gate's cited-or-tested stage is red for an item neither cites; an `open` item
has no lemma and is not asked. An item may be added before a proof needs it,
and its test is what checks it until one does.

Which items are added ahead is chosen, not swept. They come from the set.mm
sections the library already cites from, and only facts with one natural
statement: what it means to belong to a set or range, and the value of an
operation at a point or its identities. Facts set.mm states in several ways
— the Archimedean property is `arch`, `nnrecl`, `nnunb` and `btwnz` — wait
for the proof that says which one it needs. Field and order identities are
not items at all: `algebra` and `inequalities` prove them, as `membership`
proves closure.

The library is split by subject, in words a reader of `READERS.md` already
has, and a subject is one file:

| file | holds | items |
|---|---|---|
| `corpus/stdlib/reasoning.records` | the laws of logic a proof cites by name | 5 |
| `corpus/stdlib/numbers.records` | the number systems, closure, order, powers, roots, absolute value | 67 |
| `corpus/stdlib/divisibility.records` | even and odd, divisors, primes, gcd, division, congruence, Euler's φ | 43 |
| `corpus/stdlib/sums.records` | sums over a range, and the ranges; products over a finite set | 34 |
| `corpus/stdlib/sets.records` | subsets, set-builder, union, intersection, difference, power set | 51 |
| `corpus/stdlib/functions.records` | functions, their values, images, and inverses | 15 |
| `corpus/stdlib/counting.records` | the size of a set, factorials, binomial coefficients, counting by parts | 20 |
| `corpus/stdlib/calculus.records` | intervals, bounds and completeness, continuity, derivatives, bounded sequences | 18 |
| `corpus/stdlib/geometry.records` | points, distance, angles, triangles, congruence, parallels and sides of a line, the law of sines | 24 |
| `corpus/stdlib/groups.records` | groups, their laws, subgroups, cosets | 11 |
| `corpus/stdlib/trigonometry.records` | cos and sin, and their addition formulas | 8 |
| `corpus/stdlib/polynomials.records` | polynomials with complex coefficients, their values, and division by x − a | 2 |

A proof imports each library item it cites, as it imports each theorem of
another proof file it cites, so its head says where everything it cites comes
from and of what kind it is. The library is the one directory the tools know
by name, and a module anywhere else is a proof file. The library's own records
import nothing: they cite no item, and every library function is in scope in
them.

A `.proof` file holds only the skeleton. `SYNTAX.md` says the stored text is
every line a field the elaborator reads and nothing else, so the commentary that
used to surround these proofs in markdown stays in `docs/pilot/`, which now points at
the proof file rather than containing it.

Getting out of markdown also repaired the database. Inside a markdown table a
vertical bar has to be escaped, so absolute value, cardinality and distance were
all stored with backslashes inside the formula. The `.records` files store them
plainly.

## Record format

A record begins at column 0 with its kind and name, and `mundane` before the
kind where a proof takes the item for granted. Its fields are indented two
spaces, one field per line, the field name then its value, continuation lines
indented further. A line beginning with `#` is a comment.

An item's statement is written in the theorem form of `SYNTAX.md`: labelled
`let` and `assume` lines, any `ε, δ range over ℝ` lines its quantifiers lean
on, then a `then` line. The database and the proof files therefore share one
grammar, and one parser reads both.

A function a proof may apply is a definition with a `sort` line: its name is
the function's, its `sort` line gives one place before the arrow for each
argument, its `builds` line gives the set.mm term an application stands for,
and its `reads` line says it in words. A proof file that applies it imports
it as it imports any item, `import mundane definition stdlib/divisibility/gcd`, and the
name is then read
wherever the file applies it, as a proof's own `T(k)` is; nothing about it is
notation (`GRAMMAR.md`, "Database records").

Every item in the standard library carries a field saying where it comes from:

| field | meaning | count |
|---|---|---|
| `metamath` | a set.mm label or labels supply it | 291 |
| `open` | it is cited but unproved and unbridged | 8 |

`mun:stdlib/geometry/point` carries both. A theorem this corpus proves has no
record: it is its proof, and its statement is the head of the proof file, so
that it has one home and cannot drift. This is the rule that the collisions
below were caused by breaking. What a record would say beside the statement,
the set.mm theorem it answers to and a note, the proof says in `metamath` and
`note` lines under its `theorem` line; 29 of the 40 name a set.mm
counterpart.

A definition may also carry a `target`, which says which set.mm theorem
unfolds it, or, for one stated as an equation, one theorem per clause:
`mun:stdlib/numbers/abs` names `absid, absnid`, and which clause a step uses is decided by
which one's conclusion is what the step claims. That is not what `metamath` says: `metamath` says what the
definition means, and `mun:stdlib/divisibility/odd` gives `not 2 ∥ n`, where unfolding it to the
existential the `then` line states is `odd2np1`. An elaborator needs the
second and cannot derive it from the first. A second entry, `equation
reversed`, says the theorem writes its equation the other way round from the
`then` line, which `odd2np1` and `divides` both do. `corpus/db/notation.records`
documents the same field on the notation side.

A target may end `with v := t, …`, saying what the lemma's variables stand
for where the claim does not fix them: `divalg with N := n, D := d`. A name
there that is none of the lemmas' variables is the claim's own binder, and
what it is given is the witness: `axi:stdlib/calculus/completeness` targets `suprcl,
suprub, suprleub with c := sup S`, and the least upper bound it promises is
the supremum, which each of the three lemmas says one thing about.

**A `target` that never fires is an error, not a shrug.** An item with no
`target` builds nothing, and a step citing it stops the build, except a
definition read off a line the step cites that already says the claim. An
item that has one and whose every clause misses the claim is a different
thing: the field says where the claim lands and it does not land there. The
elaborator names the item, the labels it tried and the step, and stops, so a
wrong target cannot sit in this file unnoticed.

**Nothing compares an item's hypotheses with its target's.** A citation is
built from the set.mm theorem the target names, with that theorem's own
hypotheses, so a record whose `let` lines say less than the theorem asks
still builds and every proof citing it verifies: `mun:stdlib/counting/card-nonempty`
with `let k ∈ ℤ` in place of `let k ∈ ℕ₀`, where `hashgt0elex` asks k ∈ ℕ₀,
passes every stage of the gate. The proofs are sound and the record misstates
the lemma. The checker reports a name the item says nothing of where a number goes
(`check_unsorted`), not a name it says too little of. Closing this means
reading each target's hypotheses from set.mm and requiring the item's to
imply them.

Every pointer from a proof resolves, every `def:` or `thm:` prefix matches the
kind of the item it names, and every proof file imports exactly the files it
cites, the definitions it uses from other proof files and the library
functions it applies; `parley check` checks all three.

A notation record declares how its notation parses: the mixfix pattern with `_`
for each hole, the sort each hole takes and the sort the pattern produces
(`sort`, `α, set of α → formula` for membership), its precedence level, its
associativity where one is needed, and whether one of its patterns is the
negation of another. There are two
shapes only, a mixfix pattern and juxtaposition, and a binder is a mixfix with
a hole marked as binding. `corpus/db/notation.records` describes the fields, and one
`precedence` record declares the order between levels as a partial order, so a
formula mixing two levels that convention does not relate is rejected rather
than guessed at.

Three things about a notation are then mechanical and the checker enforces all
three: that every record says its `sort`, readable; that it gives one sort
per hole its patterns have; and that a pattern declares an associativity
exactly when it can nest in itself, meaning both edges are holes and what it
produces fits those holes.

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

**`mun:stdlib/functions/function` was two items under one name.** The Cantor pilot stated it as a
biconditional defining `f : A → B`; the intermediate value pilot stated it as
the derived fact that a function's values land in its codomain, and cited it
three times for exactly that. The fact is now `mun:stdlib/functions/function-value` and those
three citations are renamed. A function's type is now cited for its values
(`READERS.md`), so `function-value` is cited only where the value is a step
of the argument, Schröder–Bernstein's f(s) ∈ B. `mun:stdlib/functions/function` keeps the name for the definition,
which is `open` because the Cantor pilot's row is truncated and no proof cites
it.

**`mun:stdlib/numbers/real-closure` had two statements.** The triangle inequality pilot gave
addition, the intermediate value pilot gave addition and subtraction. Merged to
both sentences, which is the shape `mun:stdlib/numbers/int-closure` and `mun:stdlib/numbers/nat-closure`
already have. Neither proof changes.

**Five statements were cross-references.** `mun:stdlib/sets/set-builder` and
`mun:stdlib/sets/set-builder-subset` read "as in the Bezout pilot" and are now written out
once. `thm:proofs/triangle-inequality/abs-bounds` read "from the triangle inequality pilot" and is now
proved in that file.

**Theorems are stored in dependency order.** A pointer must resolve to something
earlier, as `READERS.md` requires. Only the √2 file needed reordering: it now
runs odd-square, even-square, sqrt2-irrational, where the pilot put the main
theorem first. Nothing else moved.

**Six items had no row anywhere.** `thm:proofs/sqrt2-irrational/sqrt2-irrational` was the only pilot's
main theorem missing from its own table. `mun:stdlib/functions/set-image` is named in `SYNTAX.md`
and was in no table. `mun:stdlib/geometry/angle` appears only in the isosceles findings, though
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
- **Recursive definitions do not fit the theorem form.** `mun:stdlib/counting/factorial` has a
  base sentence with no hypothesis and a step sentence with one, and the form
  puts all hypotheses before all conclusions. It is written with two `then`
  groups, which no other record uses. The sum of the first m numbers and the
  sum of the first powers of a were written that way too, as S and G with a
  notation each; they are functions their proofs define now (`define S(m) :=
  …, for m ∈ ℕ`), which took two global letters out of the notation file.
- **`axi:stdlib/geometry/side-angle-side` and its one citation disagree on variable names.** The
  statement uses P, Q, R, P′, Q′, R′ and the isosceles proof instantiates A, B,
  C, A′, B′, C′. One of the two must change. Settled since: the proof changed,
  because every other geometry item names its points P, Q and R.
- **`thm:triangle-permute`'s conclusion was not a formula.** "Any ordering of P,
  Q, R forms a triangle" is replaced by `mun:stdlib/geometry/triangle-swap` and
  `mun:stdlib/geometry/triangle-rotate`, which generate all six orderings and are the two the
  isosceles proof cites.
- **Set-existence hypotheses are inconsistent.** `axi:stdlib/numbers/well-ordering` and
  `axi:stdlib/calculus/completeness` are stated with `assume S ⊆ ℕ` and no `let S be a set`,
  because that is what the pilot tables said and what the proofs discharge.
  Whether the set-existence hypothesis belongs there is open.
  `mun:stdlib/counting/card-bijection` and `mun:stdlib/counting/card-disjoint-union` were the same and now
  carry the `let` lines, because without them their statements could not be
  read: `|Y| = m` fits both cardinality and absolute value.
- **The isosceles proof had one step that broke the calculation rule.** A chain
  line cited a theorem where the rule allows only a cited line. It was the
  checker's first true positive and is repaired: the theorem is now step 2 and
  the chain cites that number.
- **`scripts/precommit.sh` is what must be green before a commit.** It runs
  `cargo fmt --check`, clippy, `cargo test`, `parley build` and `parley gate`.
  `cargo test` is whether the tool is right: the planted defects the checker
  must catch, the planted defects the elaborator must report, the planted
  defects each of the gate's other stages must catch, and that a compressed
  proof is the proof it was made from. `parley gate` is whether
  the corpus is right,
  in eight stages: the checker over the corpus; every artifact built afresh and
  compared with the file in the tree, so that a broken elaborator with its old
  files left in place fails here; every set.mm label the database names; that
  every library item is cited by a proof or has a test; that no elaborated
  proof takes a step as stated that `ELABORATION.md` does not record; a
  verifier not written for this project, `metamath-rs`, over every proof the
  elaborator has written; every library item with a target restated by a
  theorem citing it, built and verified; and every requires line needed, each
  taken away in turn and its theorem checked and elaborated without it. set.mm belongs to metamath and is not vendored: it
  is found by `SET_MM` or by a copy or link at the root, and without it the
  gate fails and says how to supply it, because a gate that skipped a stage
  would be saying green about something it had not looked at.
- **The hypotheses of `algebra` and `inequalities` are written.** Each method
  record carries a `hypotheses` field — `algebra`'s reads "every atom is a real
  number, and every denominator is nonzero" — and `SYNTAX.md` has moved the
  question off its unsettled list: a membership is a `requires` line, and the
  corpus complies throughout.
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
  The last needed a new item, `mun:stdlib/sets/not-in-difference`.

## Eight open items

`mun:stdlib/geometry/collinear`, `def:stdlib/geometry/congruent`, `mun:stdlib/functions/function`, `mun:stdlib/geometry/point`, `mun:stdlib/geometry/triangle`,
`thm:proofs/subsets/add-element-bijection`, `thm:proofs/subsets/powerset-split`,
`thm:proofs/subsets/powerset-split-disjoint`.

Four of the eight are geometry, which is what the isosceles pilot predicted:
the proof is trivial and the database is not. Three are the counting lemmas the
subsets pilot leaned on, and one is what `mun:stdlib/functions/function` would
have to say about a map.

Six more were open and are not. `thm:proofs/intermediate-value/point-right`
existed only because the language had no `min`; with the `min` notation the
proof defines x₁ := min(b, c + δ/2) as a textbook does, and the lemma is gone. `mun:stdlib/geometry/angle-symmetric`, `axi:stdlib/geometry/side-angle-side`,
`mun:stdlib/geometry/triangle-swap` and `mun:stdlib/geometry/triangle-rotate` are proved in
`corpus/elaboration/stdlib/proved.mm`, which is a third way to supply an item: neither a
set.mm label nor a proof file in the readable layer, but a Metamath proof
below it, for what set.mm does not state and the readable layer cannot.
`mun:stdlib/geometry/angle` closed differently — it carries a `symbol` and a `defines` now,
and is the one definition in this corpus that introduces a constant.

**That third way is a last resort, and a new one needs a reason of the same
kind.** An item proved there is an item a reader cannot read: the proof is
cited from the readable layer and answered in Metamath, which is the split
this corpus exists to close. The four that take it earn it on their content —
saying what they say means dividing one point by another and naming the branch
cut of the complex logarithm, and `GEOMETRY.md` chose the ℂ encoding on the
understanding that those would reach the reader as dull facts rather than as
case splits inside an argument. An item whose content a reader would follow
does not earn it, however awkward the elaborator finds it. Where the obstacle
is that the readable layer cannot yet *say* something, the thing to weigh is
teaching it to say that, or teaching the elaborator to work it out, and a
hand proof is what is left when neither is worth its price.

The four that remain open in the geometry are open for a reason rather than
for want of work. Incidence is a primitive, and `mun:stdlib/geometry/collinear` says so: in
the plane collinearity is (R − P)/(Q − P) being real, and subtraction takes
numbers while P, Q and R are points, so the sorts that stop |CA| reading as a
product stop this too. The notation carries a target, so a claim of
collinearity elaborates; what has no readable statement is the equivalence.

## Record kinds

`GRAMMAR.md`, "Names" and "Database records", gives the imports, citations
and record grammar that go with this section.

**A record answers two questions, and its header says both.** What the item
is: an `axiom`, given and not proved; a `theorem`, proved; or a `definition`,
where a word or a symbol gets its meaning. And whether a human proof takes it
for granted, using it without naming it: if it does, the header opens with
`mundane`.

```
theorem pascal
mundane theorem int-closure
axiom completeness
mundane axiom trichotomy
definition C
mundane definition difference
```

| header | items |
|---|---|
| `axiom` | 4 |
| `mundane axiom` | 7 |
| `theorem` | 33 |
| `mundane theorem` | 201 |
| `definition` | 7 |
| `mundane definition` | 46 |

The two questions are independent, so no rule is needed to say which wins:
trichotomy is an axiom and is taken for granted, and its header says both.
`mundane` is not a kind. A bare `mundane int-closure` is a defect, and so is
`mundane` before `notation` or `precedence`, which nothing cites. The mark
decides the prefix a citation writes, `mun:`, and an import repeats the
header, `import mundane theorem stdlib/numbers/int-closure`; it changes
nothing else: a mundane definition is still written out where it is used
and is still unfolded, because the elaborator reads the kind from the record
and not from the line.

Every item is supplied by a set.mm label or is `open`, and the ten axioms are
supplied the way every other item is: by a lemma set.mm proves,
or for `side-angle-side` by one `corpus/elaboration/stdlib/proved.mm` proves.
So an axiom's kind is the reader's view of it and not the kernel's. Notation
and methods keep their own records in `corpus/db/`.

**A definition is where a word or symbol gets its meaning,** which is what
Reader A means by "by definition". It is not a statement whose two sides may
be put for each other. It may be an iff, `n is even ↔ there is k ∈ ℤ with n =
2k`; an equation; a set of cases, as `abs` and `C` are; or a description, as
`sqrt` is, the number that is at least 0 and whose square is x. A statement is
a clause of a definition when the definition could have said otherwise.
C(n, k) = 0 for n < k is a convention a writer chooses, so it is a clause of
C's definition. 𝒫∅ = {∅} is forced once 𝒫 is defined, so it is a theorem,
though it takes one step.

**Clauses with different conditions are cases of one sentence.** A `then`
group takes every hypothesis written above it, which is what `int-closure`'s
second group needs of its first integer. So C states its value at −1 as a
group of its own, and its value inside 0 … n and its zero above n as cases
under `let k ∈ ℤ`, as `abs` states its two:

```
definition C
  let n ∈ ℕ₀                                                          (H1)
  then        C(n, −1) = 0
  let k ∈ ℤ                                                           (H2)
  then        if k ∈ {0, …, n} then C(n, k) = n!/((n − k)!·k!).
              if n < k then C(n, k) = 0.
```

A step citing it gives the line that says which case it is in, as the binomial
proof's step 6 cites `m < m + 1`. The formula's (n − k)! is said only where
k ∈ {0, …, n}, so it is never said where it has no value.

**A function is a definition with a `sort` line.** The four are `gcd`, `C`,
`min` and `max`. They take `sort`, `builds` and `reads` beside the fields
every definition takes, and a `then` line is optional: `min` and `max` have
none, and what a proof needs of them is in items of their own. There is no
field for the applied form. The name is the record's and the number of holes
is the number of places `sort` gives before its arrow, so `definition gcd` with
`sort number, number → number` is applied as `gcd(_, _)`, and such a
definition's name is therefore one a formula can write. A function's syntax is
in its record and a notation's is in `corpus/db/notation.records`. That is why
a proof imports one and not the other: a function's name is a letter or word a
proof might give something of its own, and a notation's tokens are not.
Whether a name reaches a formula through a definition or through a notation is
the parser's concern, and a reader sees a definition either way.

**The kind and the mark are told apart by how a human proof treats the
item.**

- An **axiom** is what Reader A (`READERS.md`) takes as given rather than
  proved. Several laws of logic can be proved from one another, so one is
  chosen: excluded middle is the axiom, as textbooks present it, and the laws
  proved from it are theorems.
- A **theorem** is a result proved from the axioms and definitions.
- A **definition** is where a word or a symbol gets its meaning, as above.
- **Mundane** marks an item of any kind that a human proof takes for granted
  without naming it. That covers membership and closure, symmetry, the
  bookkeeping of sets and of logic, rearranging a sum, counting by a bijection
  or by disjoint parts, and most definitions: a textbook writes "so p = 2r for
  some integer r" and "since p is prime, p > 1" without naming the definition,
  and the word is the reason. What such a proof states is the fact the item is
  applied to, the bijection or the disjointness, and not the item.

**Mundane is the dull-fact idea of `READERS.md` applied to an item.** Both pick
out what a human proof leaves unsaid. The dull-fact test does it by a step's
role in one proof, and decides whether the step is written as a `requires`
line. The mark does it by the item, once for every proof that cites it, and
says whether a reader needs to see the step. `READERS.md`, after its
paragraphs on dull facts, says how the two relate and where they differ: every
requires line in the corpus that cites a library item cites a mundane one, and
a numbered step that cites a mundane item may be one the argument uses, which
no dull fact is.

**A method may carry the mark too.** `arithmetic` is the only one marked,
`mundane method arithmetic`: a proof never says it is using it, and it never
justifies a numbered step (`SYNTAX.md`). The mark on a method is for the
reader, and no tool reads it.

**Every symbol a proof writes is primitive or has one definition.** The
primitive symbols are the logical words (not, and, or, if … then, ↔, for all,
there is), = and ∈, ℝ with + − · / < ≤, and the numerals. ℝ has no definition:
its axioms, completeness and trichotomy with the field and order laws
`algebra` and `inequalities` apply, are what a textbook defines it by. Every
other symbol has exactly one definition, and where the library states its
meaning more than once, one statement is chosen and the others are theorems.
A notation record says how a symbol is written and what set.mm term it
builds; its meaning is in the definition. The symbols that have none yet are
the first follow-up below.

**The named items, checked against the proofs.** Each was read at every step
that cites it, asking whether a textbook names it there. Every item not in
this table is mundane.

| item | header | where it is named |
|---|---|---|
| completeness | `axiom` | "by the completeness of ℝ", intermediate-value step 8 |
| well-ordering | `axiom` | "by the well-ordering principle", bezout step 4 |
| side-angle-side | `axiom` | "by SAS", isosceles step 5 |
| pascal, division-algorithm, prime-factor, gcd-mod, divides-gcd, group-cancel, archimedean, sum-telescopes | `theorem` | "by Pascal's rule", "by the division algorithm" |
| sigma-multiplicative, sigma-prime, sigma-prime-power | `theorem` | "σ is multiplicative", "the divisor sum of a prime", perfect-numbers steps 8, 9 and 12 |
| cos-add, sin-add | `theorem` | "by the angle-addition formulas", de-moivre steps 2.15 and 2.16 |
| rolle | `theorem` | "by Rolle's theorem", mean-value step 24 |
| remainder | `theorem` | "by the remainder theorem", factor step 1 |
| convergent-bounded, archimedean-natural | `theorem` | "a convergent sequence is bounded", harmonic step 1.2; "by the Archimedean property, choose N > 2M", harmonic-unbounded step 2 |
| prime-powers-unique | `theorem` | "by unique factorisation", rationals-countable step 7.8 |
| continuous-sum, continuous-linear, derivative-sum, derivative-linear | `theorem` | "a sum of continuous functions is continuous", "the derivative of a sum is the sum of the derivatives", mean-value steps 10 to 15 |
| congruent-cancel, product-reorder, product-congruent, product-factor, product-coprime, coprime-divides | `theorem` | "cancel a, which is coprime to n", "the same remainders in another order", "congruences multiply", "a comes out once per factor", "a product of numbers coprime to n is coprime to n", "n divides the product and is coprime to one factor", euler steps 7.7, 10, 12, 13, 19 and 23 |
| continuous-on | `definition` | "by the continuity of f at c", intermediate-value step 15 |
| tends-to | `definition` | the partial sums shown to tend to 2 from the ε–N definition, triangular-reciprocals step 4 |
| congruent | `definition` | "corresponding angles of congruent triangles are equal", isosceles step 6 |
| C | `definition` | "by convention C(m, m + 1) = 0", binomial steps 6 and 25 |
| σ | `definition` | a word Reader A has not met, the sum of the divisors |
| φ | `definition` | Euler's φ, how many remainders are coprime to n, euler step 14 |
| perfect | `definition` | "so it is perfect, by definition", perfect-numbers step 21 |

Some mundane items are worth a word, since a reader might expect otherwise:

| item | header | why |
|---|---|---|
| trichotomy, excluded-middle, the five group axioms | `mundane axiom` | a split into three cases, "x ∈ B or x ∉ B", the chain a·h·h⁻¹ = a: never named |
| difference, intersection, union, range, range0, nat0, rational | `mundane definition` | the meaning of ∖, ∩, ∪, {1, …, n}, {0, …, n}, ℕ₀ and ℚ, each the membership statement the library held as a theorem |
| bijection, series-sum | `mundane definition` | "so it is a bijection", lagrange 8.6; the sum of a series as the limit of its partial sums, triangular-reciprocals step 5 |
| gcd, min, max | `mundane definition` | functions, applied and seldom unfolded: "g = gcd(a, b) divides a and b", bezout step 13 |
| cos, sin, i | `mundane definition` | known from school: cos and sin state only what they build, as min and max do, and i is i·i = −1 |
| numer, denom | `mundane definition` | the numerator and denominator in lowest terms, under set.mm's names; what a proof needs of them is in `lowest-terms-parts` |
| powerset-empty, or-left, or-right | `mundane theorem` | the definition applied, not the definition |
| derivative-real | `mundane theorem` | a real function's derivative is real, which no textbook says aloud: a requires line of mean-value step 29 |

`divides-gcd` is a theorem because the definition of gcd says a common divisor
is at most the gcd, and that it divides the gcd takes Bézout's identity or
Euclid's algorithm to show. `well-ordering` and `side-angle-side` are proved in
some presentations, and are axioms here because Reader A meets them as the
Well-Ordering Principle and the SAS postulate.

Counted this way, 346 of the 395 numbered steps that cite a library item cite
a mundane one. `def:` is rare: seven steps cite a named definition.

### Follow-ups

1. **Symbols with no definition are to get one where a proof needs it:** ∅,
   {x}, |X|, "is finite", ℕ, ℤ and ℂ. No proof unfolds any of them: a proof
   about ℕ argues by `induction`, which set.mm proves from ℕ's definition
   below the readable layer, and a proof about ℂ asks of it only that i·i =
   −1 and that ℝ lies inside it. Their honest definitions are harder than
   what Reader A brings. |X| = n means there is a bijection from X to
   {1, …, n}. set.mm's ℕ (`dfnn3`) is the intersection of every set of reals
   that holds 1 and is closed under adding 1, which needs a notation for the
   intersection of a set of sets, and ℤ (`elz`) is defined from ℕ.
2. **"Every unfolding of a definition, marked as such"** (`READERS.md`) is
   met by the pointer and not by the line for a mundane definition: the line
   writes `mun:difference`, and it is the record that says `definition`.
3. **`bijection` and `series-sum` state one direction of their meaning.**
   `bijection` says a map that is one-to-one and onto gives a bijection, and
   `notation bijection` reads "there is a bijection from X to Y" as set.mm's
   equinumerosity, with no word for "onto". A definition saying there is a
   bijection from X to Y exactly when some f : X → Y is one-to-one and onto
   needs the formula language to say "there is f : X → Y". `series-sum`
   likewise says the partial sums' limit is the sum, and not the other way.
