# Elaborating the corpus

A readable proof becomes a Metamath proof that verifies. That is what the
elaborator in `src/elab/` does, and everything in this repository rests on it
working.

```
parley build [<name>] [<set.mm>]
```

run from the working tree, writes every generated file, or the one named,
and says which changed. A
theorem is named in full, by its proof file and its own name:
`proofs/sqrt2-irrational/odd-square`. `parley gate` checks what was built, and
its second stage builds everything afresh in memory and compares it with the
files in the tree, so an elaborator broken while the built files are left
alone fails the gate.

Every theorem in `proofs/` elaborates, and `parley build` writes one artifact
for each, one for the definitions, one for the library's own proofs, and one
for each proof worked out by hand: 99 in all. Nothing lists them: the build
reads the theorems off the proof files, and a file's path under
`corpus/elaboration/` is its name. `corpus/elaboration/proofs/bezout/bezout.mm` is the
theorem `proofs/bezout/bezout`, and a file citing it includes it by that path.
`corpus/elaboration/stdlib/` holds the library's side: `definitions.mm`, which the
elaborator writes, and `proved.mm`, written from `src/proofs/stdlib/`, one
module per group of proofs (`geometry.rs`), and the only statement of what it
proves. `src/proofs/comparison/` holds the hand elaborations kept for
comparison, each written to `corpus/elaboration/<name>.mm`.

Two things shape the whole design. A step is elaborated in deduction form, so
every line is an implication whose antecedent is the scope it sits in, and a
step's expansion is a function of the step *and of the scopes it sits inside*
rather than of the step alone. And the readable layer writes which side
condition a step needs but never how to prove it, so what the text leaves out
is settled from a declared list of library lemmas.

## How the elaborator is built

The elaborator is six parts, each given one thing and producing one thing.
The page's language is not one of the things any part may change: every
difference between how the page says something and how set.mm says it is
bridged on set.mm's side, and a proof reads as a mathematician writes it.

1. **Reading.** Given a line of the page and the notation records, it produces
   kernel terms, with each name the page uses standing for a kernel variable.
   The sections on names and on the statement a theorem becomes describe it.
2. **Scopes.** Given the blocks, hypotheses, cases and `define` lines, it
   produces the context each line is proved under, carries a fact into an
   inner scope, and closes a block into the claim it owns. This is working in
   deduction form, and the section on scopes describes it.
3. **The matcher.** Given a lemma's statement, a claim, and the facts a step
   names, it produces what the lemma's variables stand for and the antecedents
   left to discharge. It matches modulo declared rules, each a set.mm
   theorem, as decision 5 of `GOALS.md` asks, and each application a step of
   the proof. Two things written differently are the same claim when they
   reach one standard form (`same` in `src/elab/matcher.rs`):
   - a one-way rule (`rules::STANDARD`) rewrites toward the side whose
     variables all appear on the other, which is what makes rewriting end
     and have one answer: `df-3or`, `df-ne`, the ℝ⁺ spellings, `rextru`;
   - a symmetric one (`rules.SYMMETRIC`: `eqcom`, and the commuting pairs)
     puts its two sides in a fixed order, read with the letters the
     statement binds as blanks;
   - a rule that asks something first (`exp0`, `nn0absid`, `rexss`) holds
     only where that is so, and is applied only where it closes a difference,
     with what it asks settled there;
   - a name a `define` introduced is what it names (`named_body`), the one
     rule that is not a set.mm lemma: the define's own equation proves it;
   - a map applied to a value is its rule at that value (`applied_body`,
     `fvmptd3`), so a function a `define` introduced is evaluated where it
     is applied;
   - letters bound under other names are one claim by a renaming, and one
     class by `rules.CLASS_BOUND` (`cbvmptv`, `cbvrabv`, `cbvsumv`).

   The walk proves it at the smallest places the two differ. A lemma whose
   conclusion, or the near side of a biconditional it states, does not match
   the claim as written is read through the same rules to fix its variables,
   proved at that, and carried to the claim; so is a definition unfolded, an
   `instantiate` and a corpus theorem cited (`fits_as`). As written is always
   tried first.
4. **Rule tables.** Data, not code: which lemma lifts an equation through each
   constructor; which lemma carries a membership from one number system to
   another, or through an operation; what a closed numeral is; and the
   spellings, such as ε ∈ ℝ⁺ read as ε ∈ ℝ with ε > 0.
5. **The calculators.** `algebra`, `inequalities` and `arithmetic`: given a
   claim and the lines a step cites, each decides whether the claim follows
   and produces its proof. `METHODS.md` specifies each.
6. **The proof rules.** Given a finished step's proof and what the step names,
   it refuses a proof that rests on anything the step does not name, a
   `requires` line or a named line that does no work, and a `requires` line
   whose proof does not come from its reason. The section on provenance
   states the rules.

**Growth goes into the tables first.** A pilot that meets a new difference
between the page and set.mm adds a rule or a table entry. A new part is for a
new kind of reasoning that no part covers, and a special case written into a
part is what this shape exists to prevent.

**The families are what the corpus has needed, not a complete list.**
Twenty-three proofs are too few to know how many kinds of translation there
are. Each family is one table, so the next one is added in one place, and each
pilot is the test of whether the list still holds.

**What is true of the code today.** Each part is a module, and each is an
`impl` block on the one `Elaborator` in `src/elab/state.rs` (517 lines),
which holds the state they share:

| part | module | lines |
|---|---|---|
| reading | `src/elab/reading.rs` | 768 |
| scopes | `src/elab/scopes.rs` | 1,837 |
| the matcher | `src/elab/matcher.rs` | 4,525 |
| rule tables, as data | `src/rules.rs` | 873 |
| rule tables, read | `src/elab/tables.rs` | 1,345 |
| the calculators | `src/elab/calculators.rs`, deciding in `field.rs`, `normal.rs`, `linear.rs` | 7,223 |
| the proof rules | `src/elab/provenance.rs` | 878 |

What `src/elab/elaborate.rs` keeps (3,483 lines) is the step loop, the handler
for each kind of step, citing an item or a corpus theorem, the definition
readings, and writing the file. Each part changes the shared state only
through its own methods: the frames through the scopes (`frames_kept`,
`open_outermost`), what names stand for through reading (`names_kept`), what
a step's lines wrote through the tables (`writing`), and a step's proof
through the proof rules (`check_step`). Every table is in `src/rules.rs`.

The matcher compares through one standard form (above). What it keeps as
named operations, because none is a rewrite of one statement into another,
is ∃-introduction and elimination (`witnessed`, `introduced`,
`through_existential`, `from_lemmas`), a lemma's implicit substitution
(`instanced`, `substituted_slot`, `as_class`), taking one half of a
conjunction (`as_conjunct`), a lemma said of every such name
(`as_generalised`), a lemma at its own value (`at_its_own_value`), and
re-indexing a sum (`letters_apart`). `settle`'s search for side conditions
reads the declared lemmas through an index built from their statements.

Measured on 2026-09-25, on the Python implementation the Rust one was ported
from line for line, every proof, the definitions and the planted cases
between them ran 1,271 of the 1,445 executable lines of its calculators. What none runs is a route declining, a refusal no
planted case reaches, a case of a method no proof has needed yet (`3 ≤ 3`),
and `assume` with `stated`: no step in the corpus is taken as stated any
longer, and the two stay, because taking a decided step as stated and
listing it is what the methods promise where the proof cannot yet be
written.

### What the corpus asks of it

Measured again on 2026-09-25, after the refactor, over the 23 theorems and
the 37 planted elaborator cases, by recording each line of the eight modules
of the Python implementation as it first runs, what each route returns, and
every lemma in the expanded proofs. What the proofs are made of is a property
of the output, which the Rust implementation matched byte for byte; the line
counts are the Python modules'.

**The proofs are almost all translation.** The 23 proofs expand to 958,486
logical steps. 17,133 of them, under 2%, apply a lemma the page names. The
rest come from 244 set.mm lemmas in nine families (the one lemma added,
`bicomd`, turns `rexss` round in the infinitely-many-primes proof):

| family | share of those steps | lemmas |
|---|---|---|
| working in deduction form | 75.2% | 30 |
| rewriting equals inside a term | 8.7% | 49 |
| membership of a number system or of the sets | 7.7% | 38 |
| facts about particular numerals | 5.3% | 31 |
| the `algebra` calculator | 2.6% | 38 |
| the `inequalities` calculator | 0.3% | 23 |
| using and proving "for all" and "there is" | 0.2% | 10 |
| induction and cases | under 0.1% | 9 |
| spellings between set.mm and the page | under 0.1% | 14 |

**The code is load-bearing.** Of the 5,625 executable lines of the eight
modules, 87% run in some proof, 3% only in the planted cases, and 10% in
nothing, in scattered branches rather than whole functions:

| module | run in a proof | only in planted cases | in nothing |
|---|---|---|---|
| `reading.py` | 92.7% | 2.0% | 5.2% |
| `scopes.py` | 90.5% | 0.0% | 9.5% |
| `matcher.py` | 90.5% | 1.3% | 8.2% |
| `rules.py` | 100.0% | 0.0% | 0.0% |
| `tables.py` | 91.6% | 1.3% | 7.0% |
| `calculators.py` | 87.1% | 0.9% | 12.0% |
| `provenance.py` | 82.1% | 5.8% | 12.0% |
| `elaborate.py` | 78.5% | 7.7% | 13.8% |

**It hardly searches.** Of the 3,983 side conditions `settle` answered, 73.7%
were a fact already in hand and 22.0% came from structure (a conjunction
split, a membership carried between number systems or through an operation, a
digit, sethood). The search through declared lemmas answered 4.2%, with 45
pairings of what was wanted and which lemma gave it, from 36 lemmas. Of the
items whose target names several lemmas, only `mun:stdlib/sets/set-builder`
names two, and `elrab` fitted all ten times.

**What comparing through one standard form changed.** Four of the thirty
elaborated files: the ten-power congruence, √2's irrationality and the
intermediate value theorem take the same lemmas in another order, and the
infinitely-many-primes proof applies `rexss` where the two statements differ
rather than searching the declared equivalences for it. The largest grew by
0.7%; every one verifies, and none states an axiom.

## The statement a theorem becomes

Hypotheses are conjoined into an antecedent. `thm:proofs/sqrt2-irrational/odd-square` —

```
theorem odd-square
  let n ∈ ℤ                                                           (H1)
  assume n is odd                                                     (H2)
  then n² is odd
```

becomes

```
$p |- ( ( A e. ZZ /\ -. 2 || A ) -> -. 2 || ( A ^ 2 ) )
```

and not the obvious reading, with each hypothesis a `$e` statement of its own
and the conclusion standing alone. That form verifies but cannot be cited: a
Metamath essential hypothesis has to be discharged by a proved statement, and
a step citing the theorem from inside a `contradiction`, `cases` or `obtain`
block has nothing proved to discharge it with — every line there is an
implication out of a supposition.

So the form is decided by where the theorem may be used, which the theorem
itself cannot know. Every theorem gets the same one.

A step citing a theorem this corpus proves conjoins what the step supplies for
its hypotheses and applies it with `syl` to its whole conclusion. A step may
claim one sentence of a conclusion that says several — `intermediate-value`
cites `thm:proofs/triangle-inequality/abs-bounds` for `x ≤ |x|` alone — and that sentence is taken out of
the whole. The conclusion is read in the sorts the cited theorem's own
hypotheses state, since `|x|` is absolute value only where x is a number.

**A group is a structure the page never writes.** `let G be a finite group
with operation · and identity e` is set.mm's `W e. Grp` for a class W, with
`( Base ` W ) e. Fin` conjoined where the group is finite. G names
`( Base ` W )` and e names `( 0g ` W )`. The notations that need the group's
operation, inverse, subgroups or cosets write `@op`, `@inv`, `@subgroups` and
`@lsm` in their targets, and `Reading.pattern` fills them from the names the
`let` line gave, so `a·b` is `( a ( +g ` W ) b )` and `gH` is
`( { g } ( LSSum ` W ) H )`. A notation that needs a group where no `let`
line gives one is a defect at the line writing it. `assume H is a subgroup
of G` introduces H as a `let` would, with a class variable of its own, and
is a sort: a step may rest on it uncited, as a lemma asking that H be a set
does.

## Scopes

All four block forms widen the antecedent by what they assume and close with
one lemma:

| block | closes with |
|---|---|
| `obtain` | `rexlimdva`, indexed by how many names it introduces |
| `contradiction` | `pm2.65d` |
| `fix` | `ex`, or nothing when it is the step of an induction |
| `cases` | `mpjaodan` |

`cases` differs in one way: it opens a scope for each of its parts rather than
one for all its children, so the scope changes between siblings and not only
on the way in and out. An `obtain` inside a case is discharged where that case
ends, since `mpjaodan` wants each case over the scope the case opened: the
first case of `intermediate-value` obtains δ and then x₁. More than two cases
follow the disjunction the block cites, which is built from the left:
`jaodan` makes one case of the first two, over their disjunction, and
`mpjaodan` closes on the last. The cases must be that disjunction's, in its
order.

An `obtain` of two names at once is `rexlimdvva` — one lemma, not two nested
discharges. The existential the kernel supplies carries the kernel's own bound
variable, so every obtain alpha-converts it with `cbvrexv` to the name the text
uses. Two obtains from one definition in nested scopes make that compulsory
rather than cosmetic: the second scope's antecedent already carries the first
name free.

An `obtain` that renames — `even` says there is k, the proof obtains r —
gives the name a letter of its own rather than the one the existential binds,
by the same respelling: holding k's letter, r would be captured by a later
"there is k". And a step claiming a definition's "there is" itself, from a
line saying its left side, unfolds that line (`unfolded`) as the obtain would;
a definition reaches a claim by a witness (`conclude`) only where the claim is
its left side, which is never a "there is".

An obtained name may stand for the very letter the goal binds. `obtain N from
line 5.2` in the triangular reciprocals takes N as the letter the line's "there
is N" binds, inside a block claiming "there is N ∈ ℕ with …", and
`rexlimdva` keeps the obtained letter out of the goal. The goal is renamed
apart for the discharge and renamed back afterwards, which says nothing new:
the two are one claim with different bound letters.

A standalone `fix` gives back everything it took — `ex` for what it supposed,
then one `ralrimiva` per name it fixed, innermost first. Inside an induction
it is one part of the induction, which takes it as it stands.

**Where a step is proved is not always where the text puts it.** A kernel
disjointness condition can make a step's expansion illegal under the antecedent
the readable proof states it under while the same step is provable one scope
out. `fsump1` forbids its summation variable in the antecedent, and
`sum-formula`'s induction hypothesis is an equation between sums, so it holds
that variable; step 1.3.1 is written inside the `fix` block and cannot be
proved there.

`allowed` picks the innermost frame the lemma's disjointness conditions permit,
before anything is built, and `carry` brings the result back in with `adantr`.
Each frame keeps the facts known at it, because a hoisted step is proved from
those rather than from the innermost ones, and that holds for the lines the
step cites as well: a line proved inside the frame is not offered to a lemma
proved outside it (`with_cited`). Its proof states it under the inner scope,
and handed to the lemma it is a proof of another statement, which the
verifier refuses and the elaborator did not; now the lemma declines and the
step is reported. The binomial theorem's induction step met this, and states
its sum algebra as a theorem of its own, `binomial-step`, where no
hypothesis in scope names the sum's index. The readable order is still
correct — the reader needs the step where it stands — so what moves is the
elaborator's order and not the author's.

Which letter a statement binds is no part of what it says, and a lemma's
disjointness conditions are about letters, so the letters a lemma keeps apart
from its scope are chosen by one rule rather than searched for. A hypothesis
saying Σ(k = 1 to n) … → 1 as n → ∞ binds k and n in the theorem's own scope,
and `sersumlim`, which `mun:stdlib/calculus/series-sum` targets, keeps both
apart from any scope it is used under; `gpartsfin`, which
`mun:stdlib/counting/parts-finite` targets, keeps its y apart from a scope
that may itself say "for all Y ∈ K", binding the same letter. So:

- every letter the lemma binds and keeps apart from its scope, and the claim
  does not fix, is given one nothing in the proof holds, whether or not a
  frame spells the lemma's own, and never the one a cited line happens to
  bind (`letters_unheld`). What the lemma's other variables stand for is
  still read off the lines, fitted with the fresh letters left open
  (`fit_respelt`). The rule applies where it is redundant too: a lemma whose
  own letter nothing spells still takes a fresh one, so no step depends on
  which letter a line happened to bind;
- a fact answers a claim that says the same over other bound letters,
  whatever the binder — a "for all", a "there is", a union, a map, a
  set-builder or a sum — and however deep it stands. Every letter the fact
  binds is moved to one nothing holds, and renamed from there to the
  claim's (`renaming_apart`), so no letter is caught on the way; a renamed
  part is carried up through each constructor above it by the closed lemma
  for that place (`rules::RENAMED`, `rules::PREDICATE_LIFT`), and a class
  renamed by the lemma for its binder (`rules::CLASS_BOUND`);
- the claim's own bound letters are moved to such letters, the claim proved
  over them, and `respelt` carries it back (`over_other_letters`);
- a definition's lemma in deduction form is unfolded at the innermost scope
  its disjointness conditions allow (`allowed`, as for any lemma applied)
  and carried in; where none does, the letters it keeps apart from its scope
  and the scope spells are moved to letters nothing holds, the lemma applied
  over them, and the side the step holds renamed to them, closed
  (`unfolding`);
- a change carried under a binder whose letter the scope spells — a "for
  every", a "there is", a set-builder or a sum — is carried over a letter
  nothing holds: both sides' letter is moved there, closed, the change
  carried, and the result moved back (`over_spare_letter`), since the lemma
  that carries it keeps its letter apart from the scope;
- a "for all" the elaborator generalises itself is proved over a spare
  letter where the scope spells its own, and `cbvralvw` renames it back
  (`for_every`);
- the hypothesis the lemma then asks for, spelt over the new letters, is the
  scope's own spelt over the old, and where one binder sits inside another,
  as a sum inside a sequence, the inner is renamed first and carried up
  through the outer (`class_renamed_within`);
- a map's rule read at a value that spells the rule's own bound letters,
  bound there or not, is read in a second spelling of them, fixed once per
  map (`rule_apart`), and the value taken from the map over that spelling,
  shown the same map closed (`class_alpha`, `mpteq12i`). Schröder–Bernstein
  reads M at C, and C written out is a union over sets whose condition is
  M's rule, so a map over its own letter would stand in the proof, which no
  lemma for maps may rewrite: they keep the letter apart from the domain;
- a value a reading wrote out, where written out it would sit under a
  binder of one of its own letters, is put back as the line writes it
  (`refolded`), so `A ∖ M(C) ∈ D` is taken into D's condition with M(C)
  folded;
- a "for all" whose body changes only for a member of its domain, as
  h(e) is h's rule only for e ∈ A, is carried with the member in scope
  (`ralbidva`), over a spare where the scope spells its letter
  (`under_member`).

`tests/elaborator/bound-names.proof` holds a proof of each shape but the
last three, which `proofs/schroeder-bernstein.proof` is the proof of.

This is the only rule anywhere in the expansion that is about *where* a step
may be emitted rather than about which lemma it emits.

**What a scope owns, in the code.** `src/elab/scopes.rs` keeps the frames, and
nothing outside it pushes or drops one: a route that widens the scope for a
moment — a binder's membership while `settle` proves a universal, each side of
an `inequalities` split — opens it inside `frames_kept`, which gives the frames
back when the route ends. An `obtain` is a scope too, of another shape: it
pushes no block, and hands the step loop a closer, a function that discharges
its existential around whatever proof it is given. The closers form a stack
beside the blocks, and a block spends the ones raised inside it when it
closes.

A block gives back its frames, the names it bound and the letters they took.
It does not give back `sets`, what each name was let into: a name fixed or
obtained inside a block keeps its set after the block closes. No proof reads
one there, because the name is no longer bound, and this is recorded as found
rather than relied on.

## What each step becomes

**`obtain`** is not a step. There is no kernel move that hands you a name.
Everything below is proved out of the obtained facts conjoined onto the
antecedent, and the existential is discharged at the end. The obtained claim
is taken apart as deep as the sentences its line writes, as any line saying
several things is, so each sentence is a fact a later step cites on its own:
the angle sum's parallel says eight. A point obtained is a point as `let A be
a point` says it is: what it is in is a sort, which a step rests on without
citing the line, and the checker refuses a citation made only for it. A
number obtained is cited for its membership in a `requires` line, from the
obtain. So one readable step
changes which lemma every step after it uses, and an elaborator cannot expand
a step in isolation and concatenate the results.

An `obtain` from a definition obtains the existence its claim states
(`existence_claimed`): `a ∈ G. Y = aH.` obtaining a is there is a ∈ G with
Y = aH, each membership sentence giving a name's domain, over letters
nothing else holds. That is reached as a step claiming it would reach it
(`one_unfolded`): the definition is read from the lines the step cites, a
define's name read as what it names, whether the definition's right side is
the "there is", as `even`'s is, or holds it inside, as `part-builder`'s P(u)
does. Where nothing reaches it the step is a defect naming the existence. A
lemma binding its letter on both sides, as `eliun` does in the union and in
the existence, keeps the letter the step's term fixes, and `bridging`
carries the existence to the obtain's own.

**`substitute`** walks the path from the root of the claim to the occurrence
being replaced and emits one congruence lemma per step of that path. The base
of a power is the first argument of `^`, so `oveq1`; the exponent would be
`oveq2`, and inside a function application `fveq2`. Nothing is searched for;
the tree decides. It takes a target — `into line 1` replaces a subterm of a
cited line rather than of the step's own claim, and the claim is the default
rather than the only choice.

A claim may hold its variable in several places at once, so the congruence
machinery changes more than one operand at a time: `eqeq12d` and `oveq12d`
where `eqeq1d` and `oveq1d` change one. A quantifier's domain and body may
change together, as `for all x ∈ aH, xH ⊆ aH` does at a := b, and
`raleqbidv` carries both.

**`calculation`** folds a chain of n relations into n−1 transitivity steps.
The lemma is chosen by the pair of relations either side of each join rather
than fixed for the chain, since a chain may fold equalities into a `≤`. In
deduction form each is the `d`-suffixed variant.

**`join`** is `jca`, and it pairs its cited lines by what they claim rather
than by the order the line lists them, because the readable order is the order
they were derived and the conclusion's order is the theorem's.

**A step `contradicting` a line** is what closes a `contradiction`:
`pm2.21dd` takes the step's line and the line it names to the block's claim,
and `pm2.65d` drops the supposition. Ending a case, it takes the two to the
formula every case claims, so a case that cannot occur needs no step of its
own to reach that formula. A join of one line is that line, and the line must
be what the step claims. A case whose assumption line says `, which is the
claim` has no steps; what it gives the block is its assumption, under the
case's own scope, and the elaborator requires that to be the block's claim.

**`exhibit`, and a definition used to conclude an existence claim,** are
`rspcev`: restricted existential introduction. The witness comes either from a
cited line, which determines it, or from the `requires` lines that name it.
The membership those lines carry is exactly `rspcev`'s side condition.
`rspcev` keeps its bound letter out of the witness, and a witness obtained
from a line binding the same name is that letter; the claim is then exhibited
over a letter nothing holds and renamed to the claim's own.

One reader recovers the witnesses for both (`witnessed`), however many the
claim quantifies over: a definition concluded is its right side proved as
`exhibit` proves one and folded, its bound names given letters nothing holds
and the subject does not spell (`unheld`) before it is read. The body is
matched against each sentence of the lines the step cites and then of its
`requires` lines, taking all the marked places together, and a body that
says nothing of its one variable takes a member of the domain a line names.
The introduction is built from the innermost quantifier out. The witness is read against the whole of what the
claim asks of it, that it is in the domain and the body, with a defined
function applied read as its rule on both sides alike, so a line saying
either names it: `there is a ∈ G with gH = aH` takes g from g ∈ G, and its
body at g, a term equal to itself, is `settle`'s by `eqidd`. An equation
names its witness read either way round, as `g·e = g` does for g = g·h. A witness is taken from the lines a step cites and
never searched for among the facts in scope, so this runs only where a step is
there to have cited one.

**`induction`** is one lemma whose two hypotheses are the two blocks the text
writes: `base`, which stands alone, and `step`, an implication out of a `let`
and an `assume`. `INDUCTION` chooses `nnindd` or `nn0indd` by the set the name
runs over, which the `let` line already says.

The claim has to be abstracted over the induction variable, which the text
never does: the lemma wants the claim general, at the base, at the variable, at
its successor, and at what the theorem is about. The elaborator reads the claim
with the induction variable rebound to a variable of the kernel and ties each
instance to the general one by congruence. Every other method consumes a claim
whole; this one takes one apart and rebuilds it.

**`define`** introduces a name and the equation saying what it is, as a
textbook's "let x₁ = min(b, c + δ/2)" does, and the steps after it are about
the name. It is taken the way an `obtain` is: `elisset` gives `∃x x = E` once E
is a set (`rules.SETHOOD`), the scope is widened by `x = E`, and `exlimdv`
discharges it where the scope ends (`scopes.define`). The variable is a spare,
never the name's own letter, which keeps Cantor's defined B apart from the B
its conclusion binds. A body naming an earlier define is held written out:
kept over U, the subsets proof's T would meet a theorem about 𝒫(X ∖ {a}) only
by a change of a map's domain, which `mpteq1d` makes with its parts in an
order the congruence walk does not push.

A lemma speaks of the body and a line of the name, and the standard form
reads the name as the body wherever two things are compared (`named_body`),
so the matcher meets the two as it meets `k · 2` and `2 · k`: every route
that fits a lemma matches as written and then in standard form, and `same`
carries the lemma's instance to the line through the equation. Nothing
rewrites a claim itself, so a calculator still sees x₁ as a name. A step may
rest on a define without citing it, as on a sort: the checker reads a defined
name as its body wherever it compares two formulas (`SYNTAX.md`).

A step may also cite a define as its head, `D2, from 4.1` (`by_define`). One
side of its equation is read once as the define says, by the define's own
equation or `fvmptd3`, as the standard form reads it. Where that is a rule by
cases, each case is taken by `iftrue` where `settle` finds its condition among
what the step names, or by `iffalse` where it finds the negation. `same`
carries what is left to the other side, and `eqtrd` joins them.

**A definition is a theorem, not a replacement.** `mun:stdlib/divisibility/odd` targets `2 ∥ n`
negated, so unfolding it is citing a set.mm theorem — it costs a step and it
can fail, where a definitional replacement could not.

A definition is read whichever of three ways the claim asks for: it may reach
an existence claim by supplying a witness, be read right to left from lines the
step already holds, or be unfolded left to right and taken apart. Which one
applies is settled by what the lemma states and what the step claims, not by
how the readable right side is phrased. A definition reaching its left side
from a line that states the existence itself — `g ∈ ⋃(Y ∈ K) Y` from
`there is Y ∈ K with g ∈ Y` — is read right to left as any other is, and
one reached from lines naming the witness takes the witness route; which of
the two is decided once, by whether a cited line states the existence
(`reading`). A definition's target may name more
than one lemma — `rabid` and `elrab` say the same thing of a set-builder and
differ only in what they ask — and a definition stated in clauses is one
theorem per clause, as `mun:stdlib/numbers/abs` names `absid, absnid`.

**The kernel writes equations the other way round.** `odd2np1` writes
`( 2 x. n ) + 1 = N` where the corpus writes `n = 2k + 1`, and `divides` does
the same. Each use pays a flip and a commutation — `eqcomd` and `mulcomd` —
that appear nowhere in the readable proof. A `target` says `equation reversed`
where the orientation is neither the readable line's nor the label's.

## Names

A name a proof introduces becomes a variable of the kernel, and it cannot be
one a notation's own target binds, nor a letter the proof writes as a name: a
binder takes its own letter where it can, so the binomial proof's
`Σ(k = 0 to m)` is over k, and a spare handed out as k before that sum is read
would be one variable for two things.

The kernel has to see two names where the text writes one — `prime-above`
obtains a p and concludes that there is a p. Three places choose a variable and
all three must agree: what an `obtain` introduces, what a `fix` fixes, and what
a claim quantifies over. A binder's name may also be one set.mm declares as a
class, as Cantor's `B` is, and then no letter will do.

set.mm has 26 lettered setvars, and a letter the proof writes is never handed
out as a spare. Lagrange's theorem writes fifteen, fixes some twenty names in
its blocks, and takes one more for each `obtain` from an item, so
`SPARE_VARS` goes on into set.mm's primed and double-primed setvars, a′, a″
and the rest, which no reader writes. They come after every letter, so a
proof that does not use up the letters never reaches them.

Block scope is a snapshot. A block records the names before it opens anything
and gives them back where it gives back its frames — in `close_block`, and in
`enter_case`, which resets a `cases` block between its parts. A `define` is
read where it stands rather than all of them at the top, which is what lets
`subsets` write `define U := 𝒫(X ∖ {a})` eighteen columns in, with `X` from a
`fix` and `a` from an `obtain`.

**A defined function is a map and its equation.** `define G(m) := Σ(j = 0 to
m) a^j, for m ∈ ℕ₀` is read as the map sending each m ∈ ℕ₀ to that sum, which
is what set.mm has a function be, and `define` gives it a name and an equation
as it gives any define. `a` in the rule is the theorem's own `a`, a name in
scope like any other. `G(n)` is the map applied to n: the calculators see it
as one atom, and the standard form reads it as the rule at n wherever two
things are compared (`applied_body`), proved by `fvmptd3` once the name is
carried to its map by `fveq1d`. `fvmptd` would take the define's equation at
once, but it forbids the map's letter in the scope, and the scope holds that
very equation. What the rule asks, that n is in the domain, is the step's to
supply in a `requires` line.

A define with a parameter also says what its function is on: `define t(c) :=
g·c, for c ∈ H` cited for `t is a function on H` is read as the map being a
function on its domain, which it is where each value its rule gives is a set
(`mptfng`), settled as any sethood is, and carried from the map to the name
by the define's equation (`fneq1d`). A `requires` line resting `from` the
define alone is proved the same way (`define_on`). The domain is the one the
define gives. A claim naming it by another define, as Euler's f is on S, is
that set written out in standard form, and `same` carries the map's domain
to the name (`fneq2d`); a claim naming another set is not what the define
says.

**A definition from outside the theorem is written out in the statement and
a name in the proof.** What a theorem sees from outside it, a define its
file writes above it or one its file imports (`parse.FileScope`), is read in
the file that wrote it and written out there (`sorts.file_definitions`).
The statement is read with those written out (`from_outside`), so its set.mm
form never names them and a theorem citing it needs none of them. The proof
introduces them at its first step, as any define above the first step is,
and its steps are about the names; the last step's claim is carried to the
written-out statement by `same`. A cited theorem's own lines are read in its
own file's definitions (`in_its_names`), so its T is its file's T whatever
the citing proof calls T.

**Sequences defined by recursion are one recursion over a state.** Euclid's
`define a(0) := M, b(0) := N, a(k + 1) := …, b(k + 1) := …, for k ∈ ℕ₀`
gives two sequences, and set.mm has one way to define by recursion: `seq`,
stepping one value. So the n values at k are held as one state, the value
itself for one sequence and a pair for two (for more, a pair whose second is
the rest), and `recursion_terms` writes out three things once per define:

- the step E, the map from `_V` sending a state to the tuple of the rules
  at k + 1, each rule read with a name at k as its part of the state:
  `(m ∈ _V ↦ ⟨if(2nd(m) = 0, 1st(m), 2nd(m)), if(2nd(m) = 0, 0, 1st(m) mod
  2nd(m))⟩)`;
- the recursion R, `seq 0 ((E ∘ 1st), (ℕ₀ × {⟨M, N⟩}))`, which is set.mm's
  own form for an algorithm (`eucalg` states Euclid's this way);
- each name, the map from ℕ₀ sending k to its part of R(k).

The names share the one R, written with spare letters once and never
renamed apart, since two spellings of R would be two recursions. A
recursion in the statement is written out there, as a definition from
outside the theorem is; the proof names the maps as any define's.

A step citing the define is read as a define by cases is (`define_value`),
with one more link where the value is a part of R at 0 or at J + 1
(`recursion_value`): at 0, `algr0` says R(0) is the start; at J + 1,
`algrp1` says R(J + 1) is E(R(J)), which needs J ∈ ℕ₀ from the step's lines
and E : _V ⟶ _V, which holds because each state E gives is a set with
nothing assumed (`closed_set`): a pair always, a single value by what it is
built from; `fvmptd3` takes E at R(J), over E respelt with a letter of its own
(`cbvmptv`), because R(J) holds E and with it E's letter, which `fvmptd3`
keeps apart from where the map is taken. `op1stg` and `op2ndg` take the part
out, each component shown a set by `settle`. What is left is the rule at J
written over 1st(R(J)) and 2nd(R(J)), and the case the step's lines say and
`same` finish as for any define: a(J) reads as 1st(R(J)) in standard form,
so the rule's parts and the page's names meet there.

The state space is `_V` and not ℕ₀ × ℕ₀, so a define carries no claim about
where its values lie: that every a(k) is a whole number is the proof's to
show, and Euclid's shows it by induction. A rule names the sequences only at
k and never k itself (`check_recursions`), because the step sees only the
values.

## The closure methods

`METHODS.md` specifies these; what follows is how each is expanded.

**`arithmetic` decides closed numeral facts** — claims with no atom in them.
Two shapes, and both are tried before anything generic:

- *A relation between two numerals.* Each side must **be** its digit, not merely
  come to it; a side that works out to one is a computation and belongs to the
  other half. Saying it rests on the one thing set.mm names for every pair,
  that one number is below another, and everything else is that weakened or
  turned — `ltle` for *at most*, `ltne` for *not equal*, `leid` and `eqid`
  where the two are the same.
- *A numeral in a number system.* `2 ∈ ℤ`, `1 ∈ ℕ`, `0 ∈ ℝ`. set.mm names the
  fact for each digit and system and the label is the digit and a suffix
  throughout — `2z`, `1nn`, `0re` — with `ax-1cn` the one place it spells such
  a label otherwise. Where the library names none, the fact is one it does not
  state: `0 ∈ ℕ` is false and `2 ∈ ℚ` unwritten, and both decline.

A closed value is an identity of the field with no atoms in it, so it goes
where identities go rather than wanting a procedure of its own.

The page names `arithmetic` where a closed fact is used, not only as a step,
and each place is expanded by one routine, `closed_fact`: work the claim out
(`worked_out`, which refuses a false one), then prove it as above. A
`substitute` whose source is `(arithmetic)` proves its equation in place
instead of looking for a line that states it; a chain line whose reason is
`arithmetic` proves its link in place — where its terms have letters in them
and only pieces of numerals alone change, each piece is proved so and carried
up to the term it stands in by `congruence`, as `2/1 − 2/(n + 1) = 2 −
2/(n + 1)` is from `2/1 = 2`; and a requires line reading
`arithmetic` supplies what an item's hypothesis asks, including the line a
definition like `divides` reads its witness from. The kernel proofs are the
ones the separate steps built: when the corpus's eight such steps were
folded into their uses, every elaborated file came out byte for byte the
same.

**`algebra` has a normal form and a fixed order**: carry the atoms into ℂ,
apply the one structural lemma the shape calls for, then reduce the numerals.
Nothing is searched. `field.rs` decides a step and `normal.rs` proves it, and
a numeral exponent is expanded while any other leaves the whole power an atom.

What the method may do with a disequality is one thing: a *rescaled denial*.
`1 − a ≠ 0` and `a ≠ 1` deny the same number, because what one says does not
vanish is −1 times what the other does. The polynomials decide that, nothing
declares it, and the proof is `subeq0` either side of an identity the
normaliser already builds.

**`inequalities` decides linear arithmetic over an ordered field.** What picks
which cited facts a claim is built from, and in what multiple, is
`linear.certificate` — a Farkas certificate read off Fourier–Motzkin. A
negation is a fact rather than a special case: `not ( d ≤ r )` is `r < d`. A
disequality splits, since `a ≠ b` is `a < b or b < a`, and solving it means
solving twice; the certificate returns both halves and each is the same claim
one scope wider.

The method also needs to rewrite by a cited equation, because a step may
conclude something about `|x|` from a line saying what `|x|` equals, and
forward chaining from facts reaches neither side. That is `from_equation` —
the equality-aware rewriting `substitute` has, pointed at a relation.

A claim built from bounds is built by adding them, as the certificate below
says. A number is at most itself by `leidd`, citing nothing. A cited bound
stated as a denial is turned round first: `not A < B` is `B ≤ A` by `lenlt`,
and `not A ≤ B` is `B < A` by `ltnle`.

A claim about a quotient is built the same way: the normaliser brings a sum,
a difference or a product of quotients to one numerator over one denominator
(`divadddiv`, `divsubdiv`, `divmuldiv`), so the intermediate value proof's
`c < c + δ/2` comes from `δ/2 > 0` like any other bound.

**`membership`** is the membership lookup `algebra` and `inequalities`
already make for every atom (`part`), made a step's claim. The claim is read
in standard form, so T(k) is k(k + 1)/2; that is built from its parts by the
closure table, each atom's membership from a line the step cites or writes,
carried by one lemma (`bridged`); and `same` carries it back to the claim as
written. A divisor is not zero by a line, by being a digit, by a membership
that says so (`let k ∈ ℕ`), by being built in ℕ (`nnne0`), or as a product or
quotient of such (`mulne0d`, `divne0d`). A requires line may name it too, and
is proved the same way from the lines it cites (`member_of`). A claim said of
every member is proved of one fixed by `widen`, with what its membership says
laid beside it (`fixed`), and closed by `ralrimiva`; a sum over a range is
`fsumrecl` or `fsumcl` over its term, proved with the index fixed in the
range the same way (`summed`), and `fzfid` says the range is finite.

The normaliser reads only the arithmetic it normalises, and a division
inside anything else — the summand of Σ(k = 1 to n) 1/T(k) — belongs to that
atom and is no denominator of the term the atom stands in.

A quotient by a quotient, `a / (c/d)`, is first `(a·d) / c` by `divdiv2`, and
that is normalised as any quotient is. The law asks that `c` is not zero, and
that is asked of `c` as the page writes it, not of its canonical form: a
product is not zero when its factors are not (`mulne0d`), and each factor's
disequality is the page's own. The triangular reciprocals divide 1 by
`k(k + 1)/2` and say `k ≠ 0` and `k + 1 ≠ 0`; the canonical form of `k(k + 1)`
is `k² + k`, of which the page says nothing.

The certificate is written as it stands: any number of cited facts, each
scaled by the weight the certificate gives it, and a number left over. The weights are brought to whole numbers by
multiplying the claim through by a positive whole number `W`. Each fact is
said as its difference against zero and scaled by `lemul2`, or by `ltmul2`
for a strict one, which keeps it strict. The number left over is one more
fact, `−n < 0` from `0 < n` (`lt0neg2d`), a closed numeral fact the step does
not cite, as `METHODS.md` allows. The facts are added two at a time by
`le2add`, `ltleadd`, `leltadd` or `lt2add`. The normaliser says the sum is `W`
times the claim's difference, and `W > 0` gives back the claim.
`n ≥ 1` gives `0 < n + 1` so, with 2 left over, and the triangular
reciprocals' `2 − ε < 2 − 2/(n + 1)` takes two bounds each scaled by 2.

A disequality `a ≠ b` that is not one strict bound turned round is proved as
the strict bound between the two that the cited facts give, `b < a` or
`a < b`, and turned into the disequality by `gtned` or `ltned`: `k ≥ 1` gives
`k ≠ 0` by way of `0 < k`. A claim of two sentences joined by "and" is each
of them proved in turn and joined by `jca`.

### What algebra costs

| | | tokens | compressed |
| --- | --- | --- | --- |
| `salg2` | `( A · 2 )² = 4A²` | 167 | 229 B |
| `oalg1` | `( 2n + 1 )² = 4n² + 4n + 1` | 558 | 519 B |
| `oalg2` | `4n² + 4n + 1 = 2( 2n² + 2n ) + 1` | 613 | 454 B |
| `salg3` | from `2A² = 4B²`, that `A² = 2B²` | 855 | 417 B |
| `salg1` | from `( A / B )² = 2`, that `A² = 2B²` | 945 | 466 B |
| `balg1` | Bezout's three equations, coefficients −1, 1, −q | 19670 | 1564 B |

One readable word costs a few hundred to a couple of thousand kernel tokens,
and the split is the one the method's specification predicts. The first three
are normalisations with no cited equation. The next two each take a cited
equation and multiply through by a coefficient — ideal membership with a single
generator — and cost about half as much again, most of it in carrying atoms
into ℂ.

`balg1` is the only step in the corpus whose coefficients are not constants,
and it is the case that would have decided whether `algebra` needs a search. It
does not: the order the five smaller steps follow carries it unchanged, with
`mul12` and `addsub4` rearranging and `subdi` read backwards factoring. Its
token count looks like a different animal and the compressed column says it is
not — ten atoms all of which go into ℂ, and normal format writes that
ten-conjunct antecedent into every line.

**The price of an `algebra` step is set by how many atoms it has to place in
ℂ, not by how hard the identity is.**

## Side conditions

A `requires` line has two halves — the claim, and the reason the page gives for
it. `GOALS.md` decision 9 says the readable text is canonical and the kernel
proof is derived from it, so **both halves are used**: the fact a line asks for
is proved by the reason that line gives, or the elaborator says it cannot.

`side` is where one line is discharged, and it tries, in order:

1. the lines the page cites, taken apart, where the reason is those lines — a
   `from H1`, or a definition with no `target`. Such a definition is one the
   notation folds away, so there is nothing in the library to cite and the
   unfolding is the cited line itself: `A, B, C form a triangle` is four claims
   conjoined, and a line asking for one of them is asking for a conjunct of the
   line it names. This comes before the scope, because the scope may hold the
   same claim for another reason;
2. the facts already in scope;
3. the method the line names, both halves of it, where it names a method;
4. the item the line names, where the item has a `target` — the same citation a
   step naming it makes.

A line the page cites says what it states and what a membership among its
sentences implies (`SYNTAX.md`): `let k ∈ ℕ` gives `k ∈ ℝ` by `nnre`,
`k ≥ 1` by `nnge1` and `k ≠ 0` by `nnne0`, from the table in `rules.rs`
(`implied`). An `obtain`'s names count as their line's: the scope holds
`N ∈ ℕ` with line 5.3 as its origin, and `requires N ≠ 0: from 5.3` reads it
there (`stated_by`). `inequalities` is offered the bounds, with the facts as
written, and not the disequalities: `k ≠ 0` would split every certificate it
stood in.

Nothing generic stands after those. A claim that none of them supplies is
either a method stated at the head of the file as unexpanded, or an error
naming the line:

```
proofs/isosceles.proof:48  def:triangle, from 5 does not reach -. C = A,
                          which this line claims it supplies
```

The item branch is guarded on the `target` because citing an item without one
runs `assume_item`, which would turn proved facts into assumed ones. The name
ends at the first space, since what follows it is the instantiation:
`mun:abs-real x := a, from H1` names `abs-real`.

A lemma may ask its side conditions as one conjunction where the text writes a
line each — `divides` is `( ( M e. ZZ /\ N e. ZZ ) -> ... )` — so a conjunction
the lines name between them is answered a part at a time. `SPLIT` says how a
fact one holds comes apart, `JOIN` how a goal one wants goes together, and
`conjoined` is the three moves both callers share.

The variables of a cited item are fixed by the lemma the target names rather
than by the item's own letters, which is why a `requires` line needs no
`v := t` of its own, though a few write one.

A naming hypothesis fixes its variable from either side. `ralrnmpt` names a
map and the claim fixes the map, so the map's parts are read out of it;
`grplcan` names its operation, `.+ = ( +g ` G )`, and writes it only in the
side of its biconditional the step supplies, so once G is fixed the
hypothesis says what `.+` is (`read_off`). An antecedent's conjuncts are
matched against the step's lines one at a time, and a bare `Z e. B` whose Z
nothing has fixed is matched after the rest: any line putting anything in B
answers it, and `grplcan`'s `( Z .+ X ) = ( Z .+ Y )` is what says which
member Z is. A deduction's hypotheses may bind letters its conclusion never
names, each hypothesis its own — `gpartcnt` binds one letter in the union it
is told of and another in the sizes — and each is the letter the line cited
for that hypothesis binds.

**Every `requires` line is proved from its reason, once, when its step
starts.** `step` proves them all before the step's method runs and offers them
to the whole of the step as `written`, so a membership wanted while turning
`mun:stdlib/divisibility/divides`' equation round is the step's as much as one its lemma asks for.
Where the step opens a narrower scope inside itself, a line is carried in by
`lifted_to` — one `simpl` and `syl` per assumption, the way `widen` carries
every fact. `supplied` runs more than once for a step and passes on what each
pass proves; a claim already held is taken as it stands only where the proof
held is this line's own, which its origin says, and otherwise the line is
proved again from its reason. `run` ends by asking which lines were never
proved from their reasons, and one that was not is a defect.

### Facts the text never writes

What no `requires` line spells out is settled from `rules.MEMBERSHIP`: which
set.mm lemma puts a sum of integers in ℤ, which moves an integer into ℂ, which
puts a set-builder over a set in `_V`. That is a fact about the library rather
than about the readable corpus, so no field of a readable database is its home.
It is one list tried by matching, because putting a sum of integers in ℤ and
putting a summation index in ℂ are one question asked twice.

The list is read through an index the matcher builds from each lemma's own
statement (`declared` in `src/elab/matcher.rs`): what each reading of it can
conclude, and a membership's class where it fixes one. `settle` tries, in the
declared order, only the lemmas that could conclude what is wanted, which is
every lemma that would have matched. The same reading gives each lemma its
role — of the 90 declared today, 12 are carriers `bridged` moves a
membership between number systems with, and the rest side conditions — so a
lemma is declared once, in the list, and nothing kept by hand says what it
is for. What says one thing two ways, set.mm's form and the page's, is a
rule of the standard form (`rules.STANDARD`), and the matcher compares
through it (`same`).

`READERS.md` weighed dropping the `requires` lines and leaving all of this to
be found — the fact never fails, the `let` line is in view, the price is 97
lines — and rejected the exemption, because whether a fact can fail is not the
test and whether the cited item demands it is.

A membership a step needs is looked for in a fixed order, which `part` holds:
the step's own line for exactly that claim; that line carried to another
number system by one of the twelve lemmas `rules.MEMBERSHIP` declares for it
(`bridged` — `recn` takes `k ∈ ℝ` to `k ∈ ℂ`); a compound built from its parts
by the closure lemma for its operator (`built` — `readdcld` from `a ∈ ℝ` and
`b ∈ ℝ`); a numeral from the library; and last, the scope's own copy of the
claim. Only then is it searched for, with the step's lines laid over the
scope's copies of the same claims.

The order is the point. Searched for first, `settle` tries its lemmas in the
order the list gives them, and `zcn` stands before `recn` and before `mulcl`, so
a claim came from whichever hypothesis happened to fit rather than from the
line the page wrote. The search is not widened by this: `written` adds almost
nothing to what it looks at, where handing `prove_order` every fact `supplied`
proves put `abs-bounds` past ten million `fits` calls in a proof that takes
five seconds.

What the search is offered is only what the proof being built may rest on:
inside a step, what R1 allows it; while a requires line is proved, what R2
allows the line. The scope holds more, and a side condition answered from a
line the step does not cite is one R1 would refuse afterwards — so offered
it, which route the lemma list reached first decided whether a correct page
was reported. Step 1.2.1.8 of the subsets proof cites that T has 2^k
elements; a shallower search found T finite through the bijection of line
1.2.1.4 instead. Filtered, it cannot: the search finds a route through what
the step names, or says that nothing the step names reaches the claim.

That a term is a set, in set.mm's sense, is not searched for: `made_a_set`
reads it off the constructor at the term's head — `pwexg` for a power set,
`difexg` for a difference, `rnexg` for a range, and so on (`SETHOOD`) — and
asks the same of the parts, down to a kernel variable (`vex`) or a class the
statement introduced. Each `let` line's class is a set by a fact `run` seals
as a sort (`sethood@H2`): `let a ∈ X` by `elex`, `let a ∉ X` and `let x be an
element` by the conjunct `hypothesis_body` adds. A step rests on it without
naming it, as on `let X be a set`, since `READERS.md` makes it apparatus.

A number's membership of a number system is worked out, not searched for,
and spends none of the depth. A digit's is set.mm's label for it (`9cn`, or
`9nn0` carried by `nn0zi` where set.mm puts no `9z`). A numeral of several
digits is set.mm's decimal, `; 1 0` for 10, and is put in ℕ₀ by `deccl` from
its digits' own labels and carried to ℤ, ℝ or ℂ by `nn0zi`, `nn0rei` or
`nn0cni` (`decimal_within`) — never by the search, because `deccl` asks its
parts as closed facts and the search proves everything under a scope. A term
built from numerals alone, `10^0 − 1`, is settled from the closure lemmas
with the numerals inside it looked up, and what it comes to is kept for the
file when it rests on nothing on the page. One the closure lemmas cannot
place — `0 − 0 ∈ ℕ₀`, since a difference of whole numbers need not be whole —
is placed through the digit it works out to: the equation is proved as
`arithmetic` proves one, and `eqeltrd` carries the digit's membership across
it (`by_value`).

A compound's membership of a number system is read off its operation the
same way, and spends none of the depth: a product of reals is real by
`remulcld` from its factors, each settled in turn with the depth the whole
was given (`closed_under`, from the `CLOSED` table `part` also uses). The
binomial theorem's summand C(m, k)·x^(m − k)·y^k is two products, a power and
a coefficient complex through ℕ₀, and searched for, each product was a lemma
spent before the atoms were reached.

A sum's lemmas ask things of each index: `fsumdvds` that N divide the term
for k in the range it sums over, `fsumzcl` that the term be an integer. The
first is a line the step cites read at the index (`at_the_index`, by
`rspcv`), since the page says it of every k ∈ ℕ₀ and k is in ℕ₀ by `elfznn0`.
The second is settled one level deeper than elsewhere, because it is asked
through the range: `d(k)·10^k − d(k) ∈ ℤ` is `zsubcl`, `zmulcl`, `ffvelcdm`,
then `elfznn0`. `ffvelcdm` asks `F : A --> B` and `C e. A` as one
antecedent, and only a line saying what F maps between says what A is, so an
antecedent no fact matches whole is matched a conjunct at a time — after
every antecedent has been matched whole, and after what a lemma's naming
hypothesis decides, since a conjunct matched alone can otherwise bind a class
another antecedent or the naming fixes (`f1mpt`'s map, `hashvnfin`'s size).

A lemma that re-indexes a sum binds two letters and keeps them apart:
`fsumshft` writes j on one side and k on the other. The page writes k on
both, as a reader does, since what a sum binds is no part of what it is. So
where two letters a lemma keeps apart are bound to one, the sum on the right
of the claim is renamed to a letter nothing holds, the lemma proves that, and
`cbvsumv` says the two sums are one (`letters_apart`). An induction over a
claim holding a sum rewrites its variable in the summand as well as the
limit, which `sumeq2sdv` does from an equation with no index in it and only
where the scope does not mention the index, as the induction's `x = y` does
not (`summand_changed`). And a rewrite walking into a sum reads the summand
with the sum's own letter in hand, as reading a claim does.

A rewrite that changes only a sum's summand is carried under the sum's range
by `sumeq2dv`, with the index's membership of the range added to the scope,
as `rexbidva` carries one under a restricted "there is". The triangular
reciprocals need it at the last step: the proof's sum holds T(k), the
statement writes T's rule, and T(k) is its rule only for k in T's domain,
which the range is what says.

A lemma may name its summand only in its hypotheses. `telfsum` concludes
about B, C, D and E, the summand read at j, at j + 1 and at the two ends, and
names the summand A and its letter k only in the hypotheses tying them
together. A hypothesis `k = j -> A = B` read the usual way says what B is from
A; here the claim has fixed B, so it is read the other way: A is B with the
claim's index moved to a letter nothing holds, which the lemma keeps apart
from j (`instanced`). The other three are then read the usual way and must
agree with the claim.

The line may be said of a larger set than the range, as `SYNTAX.md` allows:
the triangular reciprocals' `sum-termwise` step cites line 1, said of every
k ∈ ℕ, for a hypothesis over {1, …, n}, and the index is in ℕ by `elfznn`
once it is in the range. The checker reads the same inclusion from the
table in `rules.rs` (`set_within`).

A line said of every index answers a lemma's hypothesis about each index
whether the step cites it or writes it as a requires line: `climnnre` asks
each partial sum to be real, and the triangular reciprocals write "for all
n ∈ ℕ, Σ(k = 1 to n) 1/T(k) ∈ ℝ" on the step. Where the line binds the
index's own letter, its body at the index is its body, and `rsp` reads it
there; `rspcv` would keep the letter apart from what it substitutes.

A side condition's quotient is placed in ℂ or ℝ by `divcld` or `redivcld`
from its parts and its divisor not being zero, which is settled like any
side condition: `telfsum` asks each 2/k to be complex for k from 1 to n + 1,
and k ≠ 0 there because k ∈ ℕ (`elfznn`, `nnne0`). A quotient a method reads
is built the same way from what the step writes (`part`), and its divisor
not being zero is the step's to write too, except where the divisor is a
digit other than zero, which says so itself (`2ne0`): the intermediate value
proof's `δ/2` is real because `δ` is, with no line saying so.

The rest of the search is bounded by how many lemmas one chain applies on top
of one another, and three is the deepest chain the corpus needs: step 2.1 of
the geometric series needs `A^0 ∈ ℂ`, by `recn` from `A^0 ∈ ℝ`, by `reexpcl`
asking `0 ∈ ℕ₀`, by `0nn0`. Splitting a conjunction applies no lemma and
spends none of it; nor does going under a "for all". What a lemma asks of
a sum's index is the one place a chain of four is allowed, as above.

## What a file states rather than proves

The head of each file says what is not expanded: a closure method, or an item
the database gives no target for. A method step becomes an axiom claiming
exactly what the readable line claims, under the `requires` lines that line
carries **and** the lines it cites — both, or the axiom says more than the
method does and the proof above it goes unused.

`arithmetic` is the exception: it states nothing. Its claims are closed, so
it works each one out exactly before proving it (`field.decide_closed`), and
what it cannot prove is reported — false, dividing by zero, too large to
work out, not rational, or true and past what it can show, which is cited
instead. Stated, a false one was an axiom the kernel accepted, and
`9 = 3·4` was stated so once the normaliser stopped crashing on it.

A definition with no target is not stated where a line the step cites already
says the claim: as one of its conjuncts, which `def:stdlib/geometry/congruent` relies on, or
with another letter bound, since the notation reads "b is an upper bound of S"
as every s in S being at most b and the block that proved that fixed a
variable of its own. Otherwise it is stated as an item is, below: the
definition as the database says it, at the step's terms, and the claim read
off one side. The cited line on the other side is what says which terms:
"b is an upper bound of S" is what says the definition's u is b.

A lemma may conclude a three-way disjunction with one constructor, `w3o`,
where the readable "a or b or c" is built from the left: `lttri4` is
trichotomy, and `df-3or` carries it across.

An item becomes an axiom claiming what the item states, under its hypotheses,
and the step owes those hypotheses like any others. What the item states and
what the step claims must be one statement up to the letters they bind, or one
side of it where the item states a biconditional; then the other side is what
the step cites. `mun:stdlib/numbers/abs-difference-lt` says |x − c| < δ exactly when
c − δ < x and x < c + δ, and step 17.11 of `intermediate-value` claims the
first from lines saying the second. Stated with the step's claim under the
item's hypotheses, the axiom would say that every |x − c| is below every δ,
and the kernel accepts whatever is assumed. Anything else is a defect naming
both statements.

Stated as it says, an item is only as true as what it says, and a name it
leaves open is read as anything at all. `mun:stdlib/counting/card-nonempty` said `assume
|X| = k + 1` without saying what k was, and at k = −1 and X = ∅ the axiom was
false. So `parley check` refuses a name of no known sort standing where a notation
wants a number, in any item's assumptions and any theorem's conclusion; a
bound name is spoken for, and so is the name a definition defines over.
Nothing checks that an item's statement is true beyond that. The list at the
head of each file is what to read when it changes.

Every written file but one assumes nothing. What is left:

| file | `$a` | what |
|---|---|---|
| `definitions.mm` | 2 | `ang`, the angle constant this corpus declares |

Completeness is not one lemma away. set.mm's `sup3` says its witness is
never exceeded and that anything below it is exceeded, where
`axi:stdlib/calculus/completeness` says its witness is an upper bound and at most every
other; between the two is a contrapositive and trichotomy, which is logic
and not a spelling. set.mm also names the witness, the supremum, and says
each thing the page asks of it in a lemma of its own: `suprcl` that it is
real, `suprub` that each member of S is at most it, `suprleub` that it is at
most any B exactly when every member is. So the target names the witness,
`with c := sup S`: a `with` name that is none of the lemmas' variables can
only be the claim's own binder. The supremum is put in for c, each part of
what the claim then says is proved by the first of the three that reaches
it — the two said of one member or one bound at a time are said of every
one by fixing it — and the claim is introduced at the supremum. What the
three lemmas ask, S ⊆ ℝ, S ≠ ∅ and S bounded above, the step cites: the
last is "b is an upper bound of S", which names the bound, so a "there is"
a lemma asks may be answered from the step's own lines.

Continuity is `elcncf2`, which says what the readable definition says in
other words: it quantifies over ℝ⁺ where the page says ε ∈ ℝ with ε > 0, and
it puts f : D → ℝ on its right side where the page puts it in the
hypothesis. `ralrp` and `rexrp` are set.mm saying that a quantifier over
ℝ⁺ is one over ℝ with the positivity inside, and both are rules of the
standard form (`rules.STANDARD`), so what `elcncf2` unfolds to and what the
page says reach one statement, and the walk rewrites each quantifier where it
stands, under every binder around it. The typing conjunct is one of the parts unfolding
takes apart and is left there. What `elcncf2` asks first, that [a, b] and ℝ
lie in ℂ, the line saying f is continuous says as well, by `cncfrss` and
`cncfrss2`. The letters set.mm binds are the step's last: its x outside
and w inside are the page's c′ and x, so they are moved to letters neither
holds before they are given the page's, or the page's x would be caught.
Spellings are read in one direction, of what a lemma says, and never of a
claim.

The limit of a sequence is `climnnre`, which this corpus proves in
`corpus/elaboration/stdlib/proved.mm`, because set.mm's `clim2` names its index apart
from the map it reads, and a sequence the page writes as a rule in n is a map
binding n. `climnnre` states the limit as the page does — for all ε ∈ ℝ with
ε > 0 a natural number N past which every term is within ε — from
`rlimclim`, `rlim2`, `ralrp` and `rexuzre`. The value of a series is
`sersumlim`, proved there from `isumclim3` and `climuni`. Both are in
deduction form, as set.mm's series lemmas are, and a definition lemma in
deduction form assumes a formula it says nothing else about: that formula is
the step's scope, and the lemma's hypotheses are asked under it.

**What a requires line takes from the line it cites** is the fact as that
line writes it, one of its sentences or what the line unfolds to where its
reason is a definition the notation folds away (`unfolded_at`). Four things
count as the line writing it besides:

- the kernel's sethood of what a let introduces: `let x be an element` and
  `let a ∉ X` give that the thing is a set, which `READERS.md` keeps off the
  page;
- what a membership implies by one lemma: `let k ∈ ℕ` gives k ∈ ℝ and k ≠ 0;
- the same claim over other bound letters: a `fix` elsewhere took n, so the
  line saying every partial sum is real binds another letter, and the
  requires line citing it writes n. The two are one claim, and `same` says
  so (the renaming rule);
- a part: `let X ⊆ A` is read as X ∈ 𝒫A, since set.mm quantifies over the
  set of parts, and the page writes it X ⊆ A, so a requires line writing
  X ⊆ A takes it from that let.

Anything else the line gives only in other words does not count: an
equation or an inequation with its sides turned round, ℝ⁺ for "ℝ with
0 <", and every other rewording the standard form makes. The requires line
names the line that writes the fact, or a step of its own writes the
rewording. Isosceles's lines 5 and 6 are the triangle in two orders, and a
requires line for A ≠ B names line 5, which writes it, not line 6, which
writes B ≠ A.

`mun:stdlib/counting/card-remove` is `hashdifsnp1`, which states it whole: the size is given
as k + 1, so nothing asks that X be finite. `mun:stdlib/counting/card-nonempty` is
`hashgt0elex`, which asks that the size be positive. The page never says so,
and it follows from the line the step cites, `|X| = k + 1`: `settle` reads
`0 < |X|` through that equation as `0 < k + 1`, which `nn0p1gt0` gives from
k ∈ ℕ₀, and the congruence carries it back. Only an equation the step cites
is read this way, and only a term built from others is replaced, never a
name, whose value a `substitute` line puts in its place where a reader can
see it.

`thm:proofs/subsets/powerset-split` has no set.mm label, and is proved in
`proofs/subsets.proof` the way a reader proves two sets equal: each inside
the other. A subset of X either leaves a out, and is a subset of X ∖ {a},
or holds a, and is a subset of X ∖ {a} with a put back; each subset of
X ∖ {a}, with or without a, is a subset of X. Every step cites an item one
set.mm lemma states. Putting a subset with a put back into the image is
`elrnmpt1s`, which names its map and what it reads the map at only in its
hypotheses, so the map is read back out of the naming, and where it is read
comes from the line the step cites.

`thm:proofs/subsets/powerset-split-disjoint` is proved in `proofs/subsets.proof`. Its step
`a ∈ S ∪ {a}` rests, in the kernel, on a being a set, and a is a set there only
because it is an element of X: in set.mm everything is a set, numbers and
points included, so `elex` gives it from `a ∈ X`. A reader told `let a ∈ X`,
with X a set of numbers, does not think a is a set, and `READERS.md` says the
kernel's use of it is apparatus: `run` seals a's sethood as a sort, and the
step names nothing for it.

The assumption count is the measure that says whether a method is written or
only named.

### Steps taken as stated

`GOALS.md` decision 17: what the elaborator cannot build is a defect, or it is
recorded here, and a list in a file's header is not a record. The gate's
"taken as stated" stage (`src/tools/assumed.rs`) reads every elaborated proof
under `corpus/elaboration/proofs/`
and every library test under `corpus/elaboration/tests/`, and is red for any
statement one takes as stated that this list does not name, and for any this
list names that no file states any longer. A record is one entry:

    - `corpus/elaboration/proofs/<theorem>/<file>.mm` `<label>`: why it is not built,
      and what would build it.

A theorem's label is its full name with a dot for each slash,
`proofs.sqrt2-irrational.even-square`, and a statement taken as stated is
labelled after it, `proofs.mean-value.mean-value.itm1`. A label depends on
nothing but its theorem's name, so adding or renaming another theorem never
moves it, and no set.mm label begins `proofs.` or `tests.`.

Definitions are not steps, and the constants and definitions
`corpus/elaboration/stdlib/definitions.mm` declares are decision 12's, not this
list's.

None: every step of every proof and every library test is built.

## The order things are tried in

Where more than one proof would do, the one written is the first a search
reaches, so the order of each search is part of what a proof comes out as.
The orders follow five rules, and each search below is one of them applied.

1. **What the step names comes before what the scope holds.** The facts a
   lemma is answered from (`with_cited`) are, in order: each line the step
   cites, in the order the justification writes them, whole and then its
   conjuncts, left to right; then each `requires` line in the order written;
   then the scope's facts in the order they were established. A theorem's
   hypotheses come in statement order, and then the conjuncts of each; a
   block's opener comes after what held outside it; a proved step comes
   after everything before it. A lemma's open antecedent takes the first
   fact that fits. A witness (`witnessed`) is read from the cited lines and
   then the `requires` lines, and never from the scope. An inequality's
   certificate (`linear::certificate`) eliminates atoms in the order the
   cited facts first name them, and of the combinations that contradict
   takes the one resting on the most cited lines, since every line a step
   cites must do work (R3), then the first of those.
2. **As written comes before read another way.** A lemma is matched as it
   is written before it is read backwards (`settle`: every declared lemma
   forwards, then every one backwards, so that a biconditional turned round
   never stands in for one that says what is wanted outright); a line
   matched as it stands before as the standard form reads it (`opened`,
   `unfolds_from`); an equation facing the way it is written before turned
   round (`witnessed`, `substitute`); a seed as the target writes it before
   read through (`in_other_words`).
3. **The nearer reading comes before the deeper one.** `apply_lemma` fits
   the claim to a lemma's conclusion at each level before peeling another
   antecedent, so a match at an outer level beats one further in; at one
   level the forward read beats the near side of a biconditional turned.
   `allowed` takes the innermost scope a lemma's disjointness conditions
   permit.
4. **The cheaper route comes before the costlier.** Where the routes for a
   claim are alternatives, they are tried in a fixed sequence, and the first
   that builds is the proof:
   - `settle`: a fact exactly; an equation of a term with itself, or one held
     turned round; a numeral's membership worked out from its digits; a set
     from its structure; a membership a `requires` line wrote in another
     system (`bridged`); a compound's membership from its parts; the claim
     over other bound letters; and, with depth left, its conjuncts, a
     witness, a universal generalised, the declared lemmas, a fact in other
     words (`said_otherwise`), and last a rewrite by an equation in hand.
   - `apply_lemma`, where the conclusion does not fit as written: through an
     existential, at the seed the target gives, through a conjunct, a
     universal generalised, and last in other words.
   - `prove_field`: the two sides as one polynomial, then a cited line
     scaled, crossed, or summed.
   - a `requires` line (`by_its_reason`): read from the lines it cites before
     the scope is asked, since the scope may hold the same claim for another
     reason.
5. **A table is walked in the order it is written.** `rules.rs` says so for
   every table (an entry is not moved without a reason), and where a table
   is walked the order decides: `rules::MEMBERSHIP` for the declared lemmas
   (`lemma_index` keeps it), where the lemmas carrying a membership to a
   wider system run from the narrowest system a thing is known in, ℕ ⊂ ℕ₀ ⊂
   ℤ ⊂ ℚ ⊂ ℝ ⊂ ℂ, so the most precise fact is the one a membership rests
   on; `rules::STANDARD` for the standard form (rules
   that ask nothing before rules that ask something), `WITHIN`, `SYSTEM_OF`,
   `IMPLIED` and `RANGE_WITHIN` for what a membership says. An item's
   `target` is tried clause by clause in the order the record writes it
   (`targets::clauses`), which is the database's order to decide.

A lookup by key, an exact fact, and a loop that needs every candidate
depend on no order, and are not listed.

Proofs are written compressed. In deduction form every line is an implication
whose antecedent is the whole scope, and in normal format that antecedent is
written out in full at every use — three nested scopes make it about ninety
tokens, written perhaps two hundred times. So size is driven by copying the
context and grows with steps times scope depth, and the compressed format
disposes of it. The 27 elaborated proofs under `corpus/elaboration/proofs/` come to
371 KB and the largest,
`thm:proofs/triangular-reciprocals/triangular-reciprocals`, is 89 KB; in normal format each is larger by
orders of magnitude, since nothing about the proof changes and only the
repetition is written down differently.

The elaborator never writes normal format. A proof is built as steps
(`spell::Step`), each a label applied to the steps it takes and sharing them
rather than copying them, and the compressed file is written from those
(`compress::shapes_of`). So what a proof costs to build follows its distinct
parts: the intermediate value theorem is 63 million labels written out and
3,030 distinct subproofs, and `parley build` makes it in 1.7 seconds and
0.5GB, reading set.mm included. As a
step is built, each part is checked against the kind its label takes, so a
proof handed where a class belongs fails at the call that made it rather
than in the verifier.

It verifies faster too, because a step that was kept is not checked again.
What makes it safe is that the proof written is the proof that was given:
`compress::expand` reads one back, and `tests/compress.rs` asks that of
every proof in the corpus.

It does not make the expansions smaller. There are still six hundred and
nineteen proofs of `1 e. NN0` in that one step; the file names the first and
points at it.

**Two elaborators need not agree byte for byte.** Hand and program
elaborations of the same theorem do not match, and the multiplier is a count
of closure-method steps rather than anything about the proofs. A hand proof
factors — odd-square's algebra is two lemmas proved beside it and cited — and
the program inlines, because it emits one `$p` per theorem and has no notion of
a lemma worth extracting. So the size is a property of a program that never
factors, measured against a person who always does, and verifiability is what
an elaborator can be held to.

## What the tools check

What checks the tool and what checks the corpus are kept apart. `cargo test`
is whether the tool is right: the planted defects the checker must catch
(`tests/planted_check.rs`), the planted defects the elaborator must report
(`tests/planted_elaborate.rs`), the planted defects each of the gate's other
stages must catch (`tests/planted_gate.rs`), that a compressed proof is the
proof it was made from (`tests/compress.rs`), and that the hand elaborations
write their files (`tests/comparison.rs`). `parley gate` is whether the corpus is right, in seven
stages: the checker over the whole corpus; every artifact built afresh and
compared with the file in the tree; every set.mm label the database names;
that every library item is cited by a proof or tested in `tests/stdlib/`
(`DATABASE.md`); that no elaborated proof or test takes a step as stated
unless "Steps taken as stated" above records it; a verifier over every
proof the elaborator has written; and that every library item with a target
gives its target what it asks, by a theorem restating the item and citing
it from its own lines, built and verified (`src/tools/restated.rs`). `scripts/precommit.sh` runs both.

A route gives back `Route::Declined` when it does not apply, and a caller that
used one as though it were what the route builds would have a proof that is
not one. The compiler is what refuses that, the way it refuses an `Option`
used as the value it may hold: a `Route` is not a term or a proof, and it is
`#[must_use]`. Running
out of kernel variables is a `Problem`, not a decline: it is the tool at its
limit, and never happens on a run where nothing is wrong.

The verifier is the only stage that is evidence the elaborator is right rather
than consistent. The others read the corpus against itself or against a list of
names, and a proof that assumes nothing and proves the wrong thing passes all
of them — which has happened: an `arithmetic` step emitted `1 = 1` for a claim
about `( 1 x. ( 1 + 1 ) ) / 2`, and the assumption count reported it as a win.

`tests/planted_elaborate.rs` is there because nothing else watches what the
elaborator does with a defect. Taking a step as stated is right where it has no
method for it and wrong where the text is wrong, and the difference is what
`Problem` and `Route::Declined` are for: a defect is passed up and nothing
carries on past it, a route declining is returned and asked about. Each case
reads the corpus through an overlay, makes one edit, and requires that
elaborating fails with a message naming where. A case that elaborates cleanly is the failure it is looking for.

### Provenance: what each proof rests on

`GOALS.md` decision 9 says the kernel proof is derived from the readable text.
That is a property of every fact a proof uses, and the elaborator checks it
because every proof carries what on the page it rests on.

A proof is a `spell.Proof`: its text, and its **origin** — the things a reader
can point at that went into it: a hypothesis (`H1`), a block's assumption
(`S`, or `4 assumes` where the text gives it no label), a proved line (`3.1`),
a requires line (`requires@47`). Library labels are never origins. A proof is
not text, and `str` and a format refuse it, so code that handled one as a
string cannot quietly drop what it rests on. `Builder.seq` builds terms and
proofs alike and tells them apart by the last token, which reverse Polish makes
decisive: a term ends in the constructor that builds it, a proof in the
assertion it applies. A proof put together from proofs rests on the union of
what they rest on.

An origin begins where a page item does. `seal` gives a proof the item it now
stands for and records in `rests_on` what it was built from: the hypotheses in
`run`, a block's assumption where `widen` conjoins it, an obtain's source and
what it introduces, a step's result, a block's result, and a requires line
where it is proved. A conjunct taken out of a fact has that fact's origin. A
lemma whose antecedent *is* the scope — `readdcl` asks `( A ∈ ℝ ∧ B ∈ ℝ )`, and
the triangle inequality's scope is exactly that — uses the hypotheses by
standing under them and looks none up, so such a proof rests on everything the
scope says. A variable antecedent bound to the scope is the context a
deduction-form lemma is stated in, and uses nothing. Only a first antecedent
the lemma implies from stands in the scope's place, so that the lemma then
reads `scope → claim` as it stands; one it states a biconditional with, as
`elnnz` does with `( N ∈ ℤ ∧ 0 < N )`, or asks after another, is discharged
as any antecedent is, by `id`.

Three rules follow, each a defect naming the line, checked where the proof is
sealed. A step's proof, a block's, and an obtain's source all pass through
one `check_step` in `src/elab/provenance.rs`, which applies R1 and then R3 and
then seals; what it allows is `named`, the same set `resting_on` offers the
search while the step is built. A requires line is checked by R2 where it is
proved (`discharged_by`).

- **R1 — a step rests only on what it names**: the lines it cites, its own
  requires lines, and the sorts in scope; a block also on its own steps, what it
  assumes, and what a `join` closing it names (requirement 8). *step 3 rests
  on 1, which it does not name.*
- **R2 — a requires line rests only on its reason**: the lines its reason
  cites, and the step's other requires lines, which `parley check` also lets one
  line discharge from another. *the requires line rests on 1, which it does not
  name.*
- **R3 — everything a step names does work.** Divided by who can see it:
  - the elaborator, on every step but an item citation: each cited line is in
    the proof's provenance. On a method step, a requires line the proof does
    not rest on is at work only where the method demands it — the membership
    of an atom of what the certificate combined, or a term of it not zero —
    and each atom combined has its membership on the page, written or cited
    (`METHODS.md`). An atom is what the method treats as a number it knows
    nothing about; sums, products, quotients, negations and numeral powers are
    looked inside, and numerals are not atoms.
  - the checker, on a step citing an item: the item's statement says what is
    needed. Each cited line and each requires line is taken away in turn and
    the step checked again, and one whose absence changes nothing is surplus.
    A "there is" given by an instance needs the instance in the domain, so a
    witness's membership is at work. So does the membership of a name a
    summand is built from and its sum does not bind, where the item reads a
    function hypothesis, `let t : {a, …, b} → ℝ`, as that summand
    (`family_asks`): the hypothesis says every term is real, the page does
    not write that, and the elaborator builds it from those memberships as
    it builds a compound's from its atoms'. Where the value holds no name a
    membership could be asked of — 1/T(k), with T a defined function — the
    hypothesis is said whole, as a requires line "for all k ∈ ℕ, 1/T(k) ∈
    ℝ", and that line is at work when its body, with defined names written
    out, is the value read at the name it binds. An `obtain` citing an item is read the
    same way, except that what it claims is the body of the item's "there
    is", so in place of the conclusion the checker asks that the item give
    one from what the step names: `mun:stdlib/divisibility/odd` gives one only from a line saying
    n is odd.

What a line is *used for* is known too, though nothing reports it: a numbered
line whose every use is by requires lines is a dull fact by `READERS.md`'s
definition — `geometric-sum`'s line 1, `1 − a ≠ 0`, is the one in the corpus.

`tests/planted_elaborate.rs` and `tests/planted_check.rs` plant one case of each rule, and each
is confirmed to have elaborated or checked cleanly before its rule existed.

R1 and R2 are enforced twice, and the planted cases above reach only the
first: `settle` is offered what the step names and nothing else, so a
plant that breaks either rule is caught by the search finding nothing. The
rule checked where the proof is sealed is what catches a route that reads
the scope without asking `settle`, and the nets in `tests/planted_elaborate.rs` plant
one case of each with the search offered the whole scope. Each builds
silently with its rule taken away as well, so the rule is the only thing
catching it.

### What they do not check

**Method steps, in the checker.** It accepts 103 steps resting on a closure
method without checking them; what a method decides, and what it demands, is
the elaborator's.

**That an element is a set.** set.mm has everything a set, so `a ∈ X` makes a a
set by `elex`, and a name a step introduces is a set by `vex`, where a reader
told `let a ∈ X` with X a set of numbers does not think a is one. `READERS.md`
decides it — the kernel's sethood of an element is hidden apparatus — and
`let a ∉ X` and `let x be an element` are how a statement introduces such a
thing: `hypothesis_body` reads each as the thing being a set as well, which
the page never writes. The elaborator proves a term a set from its structure
and from those facts, and never asks the page for it; the checker's reading
of sorts reports a page that claims an element of a set of numbers is a set. See *What a
file states rather than proves* for the proof this let back into `proofs/`.

**Library items no proof restates.** The last stage restates each library
item with a target as a theorem of its own, and nine it cannot, because a
letter in each stands for something a proof cannot introduce. Each is cited
by a proof or tested, at a formula of that proof's own, so what it says is
used and verified there; only the restatement is missing.

- A statement: `stdlib/reasoning/excluded-middle` (P or not P),
  `stdlib/reasoning/double-negation`,
  `stdlib/reasoning/disjunctive-syllogism`, `stdlib/reasoning/or-left` and
  `stdlib/reasoning/or-right`. A proof introduces things and never a
  statement, and has no `let` for one.
- A property: `stdlib/sets/set-builder`, `stdlib/sets/part-builder` and
  `stdlib/sets/set-builder-subset`. A library item may write `let P be a
  property of the elements of X`, and the elaborator cites these at a
  concrete property, as Cantor's proof does. It cannot state a theorem over
  one: set.mm writes a property as a statement variable with its letter
  free, and each application elsewhere as a second one tied to it by an
  implicit-substitution hypothesis (`elrab.1`, `( x = A -> ( ph <-> ps ) )`),
  which a theorem of the corpus would carry as a `$e` the page never writes.
  So `SYNTAX.md` keeps the form to library items.

The stage lists what it skips against this paragraph, and an item skipped
for either reason that is not named here is a defect.

## Geometry

The readable layer writes `∠CAB = ∠CBA`, an equation between numbers, and no
Metamath library has a number to put there: set.mm's Euclidean geometry is
Tarski's axioms, whose angle congruence `cgrA` is a relation with nothing on
either side of an `=`, and its one numeric angle is in analysis, over ℂ, and
signed.

`GEOMETRY.md` weighs the seven candidates and takes the complex plane with the
angle read unsigned. The angle is a constant this corpus declares — `ang`, in
`definitions.mm` — and the items set.mm does not state are proved in
`corpus/elaboration/stdlib/proved.mm`: the four `isosceles` cites, the three of
the angle sum, and those of Pythagoras, each group in a block of its own. All
three proofs elaborate and assume nothing.

What that costs is non-degeneracy: `angval` wants both arguments non-zero and
`ang180` wants three points pairwise distinct, so `mun:stdlib/geometry/triangle` elaborates to
a conjunction taken apart at nearly every step. Synthetic geometry says "A, B,
C form a triangle" once and is done.

## Keeping set.mm where the tools can see it

The gate's labels stage (`src/tools/labels.rs`) reads 609 labels — every token
of a `target` or a `defines`, which are machine-read and so name nothing else,
plus what the rule tables in `src/rules.rs` list — and asks set.mm whether it
has them.

`metamath` is prose meant for a person and names its labels in a sentence, so
it is read only as far as it is certainly naming them: the leading entries that
are a single label-shaped word, stopping at the first that is not. That gives
`df-dvds` out of `df-dvds, whose right side is the same existential` and
nothing out of `Σ over 0...n with fsum1 and fsump1`. Reading that field is not
optional — the one error the check has ever found was a `dvds` that meant
`df-dvds`, and it was there.

set.mm is 51 MB and belongs to metamath, so it is not committed: say where it
is with `SET_MM`, or leave a copy or a link at the root of the working tree.
Missing, the stages that need it say so and the gate is not green: a gate
that skipped them would be saying green about a thing it had not looked at.

What checks these proofs is not code this project wrote. The verify stage
(`src/tools/verify.rs`) runs `metamath-rs`, the verifier of metamath-knife,
which the Metamath project maintains, as a library inside `parley`. It is
handed set.mm and every built file in memory, each under the name the others
include it by, and verifies every proof — the elaborated theorems,
`proved.mm`'s lemmas, and the hand elaborations kept for comparison — in
about three seconds, most of it reading set.mm.
Which files the joined one includes is read off the `$[ ... $]` lines rather
than listed: a proof nothing else includes is a root. A list written down
would leave the gate green on the day a proof was added and not read.

## What the expansion language has to have

1. **Scopes, not just steps.** The expansion of a step is a function of the
   step and of the scopes it sits inside, not of the step alone.

2. **A path-directed congruence.** `substitute` needs the path from the root to
   the occurrence and one congruence lemma per step along it.

3. **A fold for chains.** `calculation` is a fold of transitivity lemmas chosen
   by the relations in the chain.

4. **Witness introduction.** Using a definition to conclude an existence claim
   is `rspcev`, and the membership the `requires` lines carry is its side
   condition.

5. **A normal form for `algebra`.** Atoms into ℂ, one structural lemma chosen
   by the shape, then the numerals — a fixed order, covering every shape the
   corpus contains, with no search.

6. **A `def:` may be a theorem.** Unfolding costs a step and can fail, where a
   definitional replacement could not.

7. **One statement form for every theorem.** Hypotheses conjoined into an
   antecedent, never made essential hypotheses.

8. **Some steps are read by their block.** A step `contradicting` a line
   closes a `contradiction` on the two, and ends a case with the formula the
   other cases claim. So the expansion of a block is not the concatenation
   of the expansions of its steps, and a method's specification has to say what
   it does in each block that can contain it.

9. **An obtain is indexed by how many names it introduces, and renames every
   one of them.**

10. **An orientation policy.** The kernel's definitions write their equations
    the opposite way from the corpus, so an elaborator has to turn an equation
    round and commute a product without either appearing in the text.

11. **`substitute` takes a target.** The claim is the default, not the only
    choice.

12. **A fixed shape for a comma list.** Three conjuncts may be one `w3a` or two
    nested `/\`; nothing in the readable layer decides, so the expansion
    language has to.

13. **The claim read as a function of a variable.** `induction` needs the claim
    at four instances of the variable, and the text writes none of them.

14. **A step may have to be hoisted out of its scope.**

15. **A definition is read whichever of three ways the claim asks for**, and
    its target may name more than one lemma.

16. **A name introduced is not the letter it is spelt with.** The kernel has to
    see two names where the text writes one.

17. **A name and its equation.** `define` introduces a name, the proof is about
    the name, and the standard form reads the name as the thing where a lemma
    needs to see inside, by the equation.

18. **A chain may change relation partway.**

19. **A standalone `fix` is a generalisation**, and which of the two it is is
    settled by whether the block is a part of something.

20. **The corpus and set.mm may state one fact as two formulas.** Four kinds. A
    *rearrangement* is the same operators permuted, and `corpus/db/notation.records`
    names it with `commutes`. A *named equivalence* is two constructs set.mm
    proves equal, and something has to point at the theorem that does. A
    *rebuilt quantifier* is neither and needs a proof, which is why
    `thm:stdlib/divisibility/prime-factor` is not a gap a table could close. A *rescaled denial* is
    the normaliser's, since the polynomials decide it.
