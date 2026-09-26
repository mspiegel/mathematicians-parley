# The database and the proof files

`SYNTAX.md` fixes how a proof is written. This document fixes where proofs and
the items they point to are stored, what a stored record looks like, and what
the merge of the ten pilots' item tables decided.

## Layout

```
db/notation.records      symbols a claim may use
db/methods.records       the justification vocabulary
stdlib/*.records         the standard library: definitions and theorems
proof/*.proof            the proof skeletons, one file per pilot
pilot/*.md               the design commentary for each pilot
```

## Names and the standard library

A definition or theorem is named by the file that holds it and then its own
name, and a citation writes both: `def:stdlib/divisibility/odd`,
`thm:stdlib/numbers/int-real`, `thm:proof/triangle-inequality/abs-bounds`. The
file is its path without the extension, so the name says where to look. A
theorem of the citing file is written bare, `thm:proof/sqrt2-irrational/odd-square`, and that is the
only shorter form. `GRAMMAR.md` gives the rules under "Names", with the
`import proof` line a proof file writes for each other proof file it cites
and the `import definition` line for each definition it uses from one.

The standard library is every item a set.mm label supplies or that is still
open: what a proof cites and this corpus does not prove. It is split by
subject, in words a reader of `READERS.md` already has, and a subject is one
file:

| file | holds | items |
|---|---|---|
| `stdlib/reasoning.records` | the laws of logic a proof cites by name | 4 |
| `stdlib/numbers.records` | the number systems, closure, order, powers, roots, absolute value | 31 |
| `stdlib/divisibility.records` | even and odd, divisors, primes, gcd, division, congruence | 17 |
| `stdlib/sums.records` | sums over a range, and the ranges | 16 |
| `stdlib/sets.records` | subsets, set-builder, union, difference, power set | 24 |
| `stdlib/functions.records` | functions, their values, and images | 7 |
| `stdlib/counting.records` | the size of a set, factorials, binomial coefficients | 16 |
| `stdlib/calculus.records` | intervals, bounds and completeness, continuity | 6 |
| `stdlib/geometry.records` | points, distance, angles, triangles, congruence | 10 |

The library is never imported: every proof may cite it. It is the one
directory the tools know by name, and a module anywhere else is a proof file.

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

Every item in the standard library carries a field saying where it comes from:

| field | meaning | count |
|---|---|---|
| `metamath` | a set.mm label or labels supply it | 127 |
| `open` | it is cited but unproved and unbridged | 5 |

`def:stdlib/geometry/point` carries both. A theorem this corpus proves has no
record: it is its proof, and its statement is the head of the proof file, so
that it has one home and cannot drift. This is the rule that the collisions
below were caused by breaking. What a record would say beside the statement,
the set.mm theorem it answers to and a note, the proof says in `metamath` and
`note` lines under its `theorem` line; 14 of the 23 name a set.mm
counterpart.

A definition may also carry a `target`, which says which set.mm theorem
unfolds it, or, for one stated as an equation, one theorem per clause:
`def:stdlib/numbers/abs` names `absid, absnid`, and which clause a step uses is decided by
which one's conclusion is what the step claims. That is not what `metamath` says: `metamath` says what the
definition means, and `def:stdlib/divisibility/odd` gives `not 2 ∥ n`, where unfolding it to the
existential the `then` line states is `odd2np1`. An elaborator needs the
second and cannot derive it from the first. A second entry, `equation
reversed`, says the theorem writes its equation the other way round from the
`then` line, which `odd2np1` and `divides` both do. `db/notation.records`
documents the same field on the notation side.

A target may end `with v := t, …`, saying what the lemma's variables stand
for where the claim does not fix them: `divalg with N := n, D := d`. A name
there that is none of the lemmas' variables is the claim's own binder, and
what it is given is the witness: `thm:stdlib/calculus/completeness` targets `suprcl,
suprub, suprleub with c := sup S`, and the least upper bound it promises is
the supremum, which each of the three lemmas says one thing about.

**A `target` that never fires is an error, not a shrug.** An item with no
`target` is assumed, and the elaborated file says so at its head. An item that
has one and whose every clause misses the claim is a different thing: the
field says where the claim lands and it does not land there. The elaborator
names the item, the labels it tried and the step, and stops. Without that the
two are indistinguishable — same file, same assumption count, no message — so
a wrong target could sit in this file for as long as nobody happened to probe
it by hand.

Every pointer from a proof resolves, every `def:` or `thm:` prefix matches the
kind of the item it names, and every proof file imports exactly the proof
files it cites and the definitions it uses from other files; `check.py`
checks all three.

A notation record declares how its notation parses: the mixfix pattern with `_`
for each hole, the sort each hole takes, what the pattern yields, how the kinds
of its holes relate where a hole holds sets or functions (`kinds`, `α, set of α
→ formula` for membership), its precedence level, its associativity where one
is needed, and whether one of its patterns is the negation of another. There are two
shapes only, a mixfix pattern and juxtaposition, and a binder is a mixfix with
a hole marked as binding. `db/notation.records` describes the fields, and one
`precedence` record declares the order between levels as a partial order, so a
formula mixing two levels that convention does not relate is rejected rather
than guessed at.

Three things about a notation are then mechanical and the checker enforces all
three: that the holes a record declares match the holes its patterns have, that
a pattern declares an associativity exactly when it can nest in itself, meaning
both edges are holes and what it yields fits those holes, and that a record
with a set, function, property, variable or any hole or result says its
`kinds`, readable and one per hole. Of the 57 records, ten meet the second
condition and 27 the third.

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

**`def:stdlib/functions/function` was two items under one name.** The Cantor pilot stated it as a
biconditional defining `f : A → B`; the intermediate value pilot stated it as
the derived fact that a function's values land in its codomain, and cited it
three times for exactly that. The fact is now `thm:stdlib/functions/function-value` and those
three citations are renamed. `def:stdlib/functions/function` keeps the name for the definition,
which is `open` because the Cantor pilot's row is truncated and no proof cites
it.

**`thm:stdlib/numbers/real-closure` had two statements.** The triangle inequality pilot gave
addition, the intermediate value pilot gave addition and subtraction. Merged to
both sentences, which is the shape `thm:stdlib/numbers/int-closure` and `thm:stdlib/numbers/nat-closure`
already have. Neither proof changes.

**Five statements were cross-references.** `def:stdlib/sets/set-builder` and
`thm:stdlib/sets/set-builder-subset` read "as in the Bezout pilot" and are now written out
once. `thm:proof/triangle-inequality/abs-bounds` read "from the triangle inequality pilot" and is now
proved in that file.

**Theorems are stored in dependency order.** A pointer must resolve to something
earlier, as `READERS.md` requires. Only the √2 file needed reordering: it now
runs odd-square, even-square, sqrt2-irrational, where the pilot put the main
theorem first. Nothing else moved.

**Six items had no row anywhere.** `thm:proof/sqrt2-irrational/sqrt2-irrational` was the only pilot's
main theorem missing from its own table. `def:stdlib/functions/set-image` is named in `SYNTAX.md`
and was in no table. `def:stdlib/geometry/angle` appears only in the isosceles findings, though
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
- **Recursive definitions do not fit the theorem form.** `def:stdlib/counting/factorial` has a
  base sentence with no hypothesis and a step sentence with one, and the form
  puts all hypotheses before all conclusions. It is written with two `then`
  groups, which no other record uses. The sum of the first m numbers and the
  sum of the first powers of a were written that way too, as S and G with a
  notation each; they are functions their proofs define now (`define S(m) :=
  …, for m ∈ ℕ`), which took two global letters out of the notation file.
- **`thm:stdlib/geometry/side-angle-side` and its one citation disagree on variable names.** The
  statement uses P, Q, R, P′, Q′, R′ and the isosceles proof instantiates A, B,
  C, A′, B′, C′. One of the two must change. Settled since: the proof changed,
  because every other geometry item names its points P, Q and R.
- **`thm:triangle-permute`'s conclusion was not a formula.** "Any ordering of P,
  Q, R forms a triangle" is replaced by `thm:stdlib/geometry/triangle-swap` and
  `thm:stdlib/geometry/triangle-rotate`, which generate all six orderings and are the two the
  isosceles proof cites.
- **Set-existence hypotheses are inconsistent.** `thm:stdlib/numbers/well-ordering` and
  `thm:stdlib/calculus/completeness` are stated with `assume S ⊆ ℕ` and no `let S be a set`,
  because that is what the pilot tables said and what the proofs discharge.
  Whether the set-existence hypothesis belongs there is open.
  `thm:stdlib/counting/card-bijection` and `thm:stdlib/counting/card-disjoint-union` were the same and now
  carry the `let` lines, because without them their statements could not be
  read: `|Y| = m` fits both cardinality and absolute value.
- **The isosceles proof had one step that broke the calculation rule.** A chain
  line cited a theorem where the rule allows only a cited line. It was the
  checker's first true positive and is repaired: the theorem is now step 2 and
  the chain cites that number.
- **`parley/build.py` and then `parley/gate.py` is what must be green before a
  commit.** Build first, every time: no stage of the gate runs the elaborator
  over the corpus, and the last one verifies the files it *has written*, so
  those files have to have been written from the corpus as it stands. Break
  the elaborator and leave the built files alone and the gate passes while
  nothing elaborates. Eight stages: ruff over the tools, that no caller hands
  on a decline without asking whether it has one, the checker over the corpus,
  the planted defects that prove the checker still catches things, the planted
  defects that prove the elaborator still reports things, every set.mm label
  the database names, that a compressed proof is the proof it was made from,
  and a verifier over all 23 proofs the elaborator has written. The lint settings
  are in `ruff.toml`, which turns off the ambiguous-character rules because
  this corpus is written in the characters they object to. Nothing the gate
  leans on is vendored: ruff is looked for on PATH, and set.mm and mmverify.py
  belong to metamath and are found by `SET_MM` and `MMVERIFY` or by a copy or
  link at the root. Each missing one fails the gate and says how to supply it,
  because a gate that skipped a stage would be saying green about something it
  had not looked at.
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
  The last needed a new item, `thm:stdlib/sets/not-in-difference`.

## Eight open items

`def:stdlib/geometry/collinear`, `def:stdlib/geometry/congruent`, `def:stdlib/functions/function`, `def:stdlib/geometry/point`, `def:stdlib/geometry/triangle`,
`thm:proof/subsets/add-element-bijection`, `thm:proof/subsets/powerset-split`,
`thm:proof/subsets/powerset-split-disjoint`.

Four of the eight are geometry, which is what the isosceles pilot predicted:
the proof is trivial and the database is not. Three are the counting lemmas the
subsets pilot leaned on, and one is what `def:stdlib/functions/function` would
have to say about a map.

Six more were open and are not. `thm:proof/intermediate-value/point-right`
existed only because the language had no `min`; with the `min` notation the
proof defines x₁ := min(b, c + δ/2) as a textbook does, and the lemma is gone. `thm:stdlib/geometry/angle-symmetric`, `thm:stdlib/geometry/side-angle-side`,
`thm:stdlib/geometry/triangle-swap` and `thm:stdlib/geometry/triangle-rotate` are proved in
`elaboration/stdlib/geometry.mm`, which is a third way to supply an item: neither a
set.mm label nor a proof file in the readable layer, but a Metamath proof
below it, for what set.mm does not state and the readable layer cannot.
`def:stdlib/geometry/angle` closed differently — it carries a `symbol` and a `defines` now,
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
for want of work. Incidence is a primitive, and `def:stdlib/geometry/collinear` says so: in
the plane collinearity is (R − P)/(Q − P) being real, and subtraction takes
numbers while P, Q and R are points, so the sorts that stop |CA| reading as a
product stop this too. The notation carries a target, so a claim of
collinearity elaborates; what has no readable statement is the equivalence.
