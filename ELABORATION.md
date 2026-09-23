# Elaborating the corpus

A readable proof becomes a Metamath proof that verifies. That is what
`parley/elaborate.py` does, and everything in this repository rests on it
working.

```
parley/elaborate.py <theorem> <set.mm>
```

writes one proof to standard output. `parley/build.py` runs it over the whole
corpus and puts each result where it belongs; `parley/gate.py` checks what was
built. **Build first, every time** — the gate never runs the elaborator over
the corpus, so breaking the elaborator and leaving the built files alone
passes every stage.

Sixteen theorems stand in `proof/`, all of them elaborate, and
`build.py` writes 23 artifacts. `elaboration/elaborated/` holds what the
program writes. The files beside it are hand-written: `geometry.mm`, which is
the only statement of what it proves, and hand elaborations kept for
comparison.

Two things shape the whole design. A step is elaborated in deduction form, so
every line is an implication whose antecedent is the scope it sits in, and a
step's expansion is a function of the step *and of the scopes it sits inside*
rather than of the step alone. And the readable layer writes which side
condition a step needs but never how to prove it, so what the text leaves out
is settled from a declared list of library lemmas.

## The statement a theorem becomes

Hypotheses are conjoined into an antecedent. `thm:odd-square` —

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
cites `thm:abs-bounds` for `x ≤ |x|` alone — and that sentence is taken out of
the whole. The conclusion is read in the sorts the cited theorem's own
hypotheses state, since `|x|` is absolute value only where x is a number.

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

A standalone `fix` gives back everything it took — `ex` for what it supposed,
then one `ralrimiva` per name it fixed, innermost first. Inside an induction
it is one part of the induction, which takes it as it stands.

**Where a step is proved is not always where the text puts it.** A kernel
disjointness condition can make a step's expansion illegal under the antecedent
the readable proof states it under while the same step is provable one scope
out. `fsump1` forbids its summation variable in the antecedent, and
`sum-formula`'s induction hypothesis is an equation between sums, so it holds
that variable; step 1.4.1 is written inside the `fix` block and cannot be
proved there.

`allowed` picks the innermost frame the lemma's disjointness conditions permit,
before anything is built, and `carry` brings the result back in with `adantr`.
Each frame keeps the facts known at it, because a hoisted step is proved from
those rather than from the innermost ones. The readable order is still correct
— the reader needs the step where it stands — so what moves is the
elaborator's order and not the author's.

This is the only rule anywhere in the expansion that is about *where* a step
may be emitted rather than about which lemma it emits.

## What each step becomes

**`obtain`** is not a step. There is no kernel move that hands you a name.
Everything below is proved out of the obtained facts conjoined onto the
antecedent, and the existential is discharged at the end. So one readable step
changes which lemma every step after it uses, and an elaborator cannot expand
a step in isolation and concatenate the results.

**`substitute`** walks the path from the root of the claim to the occurrence
being replaced and emits one congruence lemma per step of that path. The base
of a power is the first argument of `^`, so `oveq1`; the exponent would be
`oveq2`, and inside a function application `fveq2`. Nothing is searched for;
the tree decides. It takes a target — `into line 1` replaces a subterm of a
cited line rather than of the step's own claim, and the claim is the default
rather than the only choice.

A claim may hold its variable in several places at once, so the congruence
machinery changes more than one operand at a time: `eqeq12d` and `oveq12d`
where `eqeq1d` and `oveq1d` change one.

**`calculation`** folds a chain of n relations into n−1 transitivity steps.
The lemma is chosen by the pair of relations either side of each join rather
than fixed for the chain, since a chain may fold equalities into a `≤`. In
deduction form each is the `d`-suffixed variant.

**`join`** is absorbed by the block that contains it. Inside a
`contradiction` it emits nothing — `pm2.65d` closes the block and consumes
both joined lines. Inside a `case` it is `jca`, and it pairs its cited lines
by what they claim rather than by the order the line lists them, because the
readable order is the order they were derived and the conclusion's order is the
theorem's. A join of one line is that line: a case whose assumption is already
the block's claim ends on `join C2`, and the line must be what the step claims.

**`exhibit`, and a definition used to conclude an existence claim,** are
`rspcev`: restricted existential introduction. The witness comes either from a
cited line, which determines it, or from the `requires` lines that name it.
The membership those lines carry is exactly `rspcev`'s side condition.

Witnesses are recovered by matching the body against the cited line, taking
all the marked places together, and the introduction is built from the
innermost quantifier out. A witness is taken from the lines a step cites and
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

**`define`** names a thing and the proof is about the thing. The name is bound
to its term and never emitted, which is what keeps it apart from a bound name
spelt the same.

**A `def:` is a theorem, not a replacement.** `def:odd` targets `2 ∥ n`
negated, so unfolding it is citing a set.mm theorem — it costs a step and it
can fail, where a definitional replacement could not.

A definition is read whichever of three ways the claim asks for: it may reach
an existence claim by supplying a witness, be read right to left from lines the
step already holds, or be unfolded left to right and taken apart. Which one
applies is settled by what the lemma states and what the step claims, not by
how the readable right side is phrased. A definition's target may name more
than one lemma — `rabid` and `elrab` say the same thing of a set-builder and
differ only in what they ask — and a recursive definition is a pair of
theorems, one per `then` group, as `def:S` names `fsum1, fsump1`.

**The kernel writes equations the other way round.** `odd2np1` writes
`( 2 x. n ) + 1 = N` where the corpus writes `n = 2k + 1`, and `divides` does
the same. Each use pays a flip and a commutation — `eqcomd` and `mulcomd` —
that appear nowhere in the readable proof. A `target` says `equation reversed`
where the orientation is neither the readable line's nor the label's.

## Names

A name a proof introduces becomes a variable of the kernel, and it cannot be
one a notation's own target binds: `S(_)` sums over `k`, so a proof that fixes
`k` must be given something else or the sum captures it.

The kernel has to see two names where the text writes one — `prime-above`
obtains a p and concludes that there is a p. Three places choose a variable and
all three must agree: what an `obtain` introduces, what a `fix` fixes, and what
a claim quantifies over. A binder's name may also be one set.mm declares as a
class, as Cantor's `B` is, and then no letter will do.

Block scope is a snapshot. A block records the names before it opens anything
and gives them back where it gives back its frames — in `close_block`, and in
`enter_case`, which resets a `cases` block between its parts. A `define` is
read where it stands rather than all of them at the top, which is what lets
`subsets` write `define U := 𝒫(X ∖ {a})` eighteen columns in, with `X` from a
`fix` and `a` from an `obtain`.

**A notation's fixed parameter is discharged, not looked up.** `G(n)` is the
sum of `a^k` for `k` from 0 to `n`, so the term mentions two things where the
notation has one hole. `@a` in a `target` is filled from the theorem's `let`
lines, taken before the conclusion and before any step and never written again.
A block binding an `a` of its own cannot reach it, and the same `G(n)` is the
same term wherever it appears. A theorem that fixes no `a` cannot write `G(_)`
at all, which is what being local to a definition means.

Which name a notation fixes is derived rather than declared, because it is
already on the page: `def:G` says `let a ∈ ℝ` and `let n ∈ ℕ₀`, and its
sentences put 0, `n + 1` and `n` in the hole. Only the notation a definition
*introduces* counts, or `_ + _` would fix a name and every proof writes `+`.
One notation in the corpus fixes anything. The matching rule about the page —
that a proof may not bind a name some notation fixes — is a checker rule.

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

**`algebra` has a normal form and a fixed order**: carry the atoms into ℂ,
apply the one structural lemma the shape calls for, then reduce the numerals.
Nothing is searched. `field.py` decides a step and `normal.py` proves it, and
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

The one case unwritten is a combination that scales an *inequality* rather
than an equation, which is a different proof and which no step in the corpus
needs.

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

Nothing generic stands after those. A claim that none of them supplies is
either a method stated at the head of the file as unexpanded, or an error
naming the line:

```
proof/isosceles.proof:43  def:triangle, from 6 does not reach -. C = A,
                          which this line claims it supplies
```

The item branch is guarded on the `target` because citing an item without one
runs `assume_item`, which would turn proved facts into assumed ones. The name
ends at the first space, since what follows it is the instantiation:
`thm:abs-real x := a, from H1` names `abs-real`.

A lemma may ask its side conditions as one conjunction where the text writes a
line each — `divides` is `( ( M e. ZZ /\ N e. ZZ ) -> ... )` — so a conjunction
the lines name between them is answered a part at a time. `SPLIT` says how a
fact one holds comes apart, `JOIN` how a goal one wants goes together, and
`conjoined` is the three moves both callers share.

The variables of a cited item are fixed by the lemma the target names rather
than by the item's own letters, which is why a `requires` line needs no
`v := t` of its own, though a few write one.

**Every `requires` line is proved from its reason, once, when its step
starts.** `step` proves them all before the step's method runs and offers them
to the whole of the step as `written`, so a membership wanted while turning
`def:divides`' equation round is the step's as much as one its lemma asks for.
Where the step opens a narrower scope inside itself, a line is carried in by
`lifted_to` — one `simpl` and `syl` per assumption, the way `widen` carries
every fact. `supplied` runs more than once for a step and passes on what each
pass proves; a claim already held is taken as it stands only where the proof
held is this line's own, which its origin says, and otherwise the line is
proved again from its reason. `run` ends by asking which lines were never
proved from their reasons, and one that was not is a defect.

### Facts the text never writes

What no `requires` line spells out is settled from `targets.MEMBERSHIP`: which
set.mm lemma puts a sum of integers in ℤ, which moves an integer into ℂ, which
puts a set-builder over a set in `_V`. That is a fact about the library rather
than about the readable corpus, so no field of a readable database is its home.
It is one list tried by matching, because putting a sum of integers in ℤ and
putting a summation index in ℂ are one question asked twice.

`READERS.md` weighed dropping the `requires` lines and leaving all of this to
be found — the fact never fails, the `let` line is in view, the price is 97
lines — and rejected the exemption, because whether a fact can fail is not the
test and whether the cited item demands it is.

A membership a step needs is looked for in a fixed order, which `part` holds:
the step's own line for exactly that claim; that line carried to another
number system by one of the twelve lemmas `targets.MEMBERSHIP` declares for it
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

## What a file states rather than proves

The head of each file says what is not expanded: a closure method, or an item
the database gives no target for. A method step becomes an axiom claiming
exactly what the readable line claims, under the `requires` lines that line
carries **and** the lines it cites — both, or the axiom says more than the
method does and the proof above it goes unused.

A definition with no target is not stated where a line the step cites already
says the claim: as one of its conjuncts, which `def:congruent` relies on, or
with another letter bound, since the notation reads "b is an upper bound of S"
as every s in S being at most b and the block that proved that fixed a
variable of its own.

A lemma may conclude a three-way disjunction with one constructor, `w3o`,
where the readable "a or b or c" is built from the left: `lttri4` is
trichotomy, and `df-3or` carries it across.

An item becomes an axiom claiming what the item states, under its hypotheses,
and the step owes those hypotheses like any others. What the item states and
what the step claims must be one statement up to the letters they bind, or one
side of it where the item states a biconditional; then the other side is what
the step cites. `thm:abs-difference-lt` says |x − c| < δ exactly when
c − δ < x and x < c + δ, and step 17.11 of `intermediate-value` claims the
first from lines saying the second. Stated with the step's claim under the
item's hypotheses, the axiom would say that every |x − c| is below every δ,
and the kernel accepts whatever is assumed. Anything else is a defect naming
both statements.

Stated as it says, an item is only as true as what it says, and a name it
leaves open is read as anything at all. `thm:card-nonempty` said `assume
|X| = k + 1` without saying what k was, and at k = −1 and X = ∅ the axiom was
false. So `check.py` refuses a name of no known sort standing where a notation
wants a number, in any item's assumptions and any theorem's conclusion; a
bound name is spoken for, and so is the name a definition defines over.
Nothing checks that an item's statement is true beyond that. The list at the
head of each file is what to read when it changes.

Fourteen of the seventeen written files assume nothing. What is left:

| file | `$a` | what |
|---|---|---|
| `definitions.mm` | 2 | `ang`, the angle constant this corpus declares |
| `subsets-count.mm` | 4 | two items set.mm has no label for, two a `target` cannot reach |
| `intermediate-value.mm` | 13 | continuity, two items with no `target`, and ten `inequalities` steps |

`intermediate-value`'s ten `inequalities` steps are decided — the certificate
refuses a step that does not follow — and stated where `prove_order` cannot
build the proof. What else it states is not one lemma away. set.mm's
continuity, `elcncf2`, quantifies over ℝ⁺ and measures |c − x| where the
readable definition says ε ∈ ℝ with ε > 0 and |x − c|. Its completeness,
`sup2`, concludes a supremum where `thm:completeness` concludes a least upper
bound. `thm:point-right` has no set.mm label and wants a readable proof.

`thm:card-remove` and `thm:card-nonempty` have their labels — `hashdifsn` and
`hashnncl` — and no `target`, because what stands between each lemma and its
item is an equation the step cited. `hashdifsn` says the size drops by one and
the item says what it drops to, which is `( k + 1 ) - 1 = k` read through the
hypothesis saying what the size was. Nothing here rewrites by a line's equation
while settling a side condition. `thm:powerset-split` is `open`: no set.mm
label states it, and it wants a proof in the readable layer.

`thm:powerset-split-disjoint` is `open` for a different reason, and its proof
is held out of `proof/` until that is settled. Its step `a ∈ S ∪ {a}` rests,
in the kernel, on a being a set, and a is a set there only because it is an
element of X: in set.mm everything is a set, numbers and points included, so
`elex` gives it from `a ∈ X`. A reader told `let a ∈ X`, with X a set of
numbers, does not think a is a set. The page cannot write the fact without
saying something the reader does not believe, and cannot leave it out without
the kernel proof resting on something the page does not say. `READERS.md` has
no rule for it; which of the two gives way is not decided.

The assumption count is the measure that says whether a method is written or
only named.

## The output format

Proofs are written compressed. In deduction form every line is an implication
whose antecedent is the whole scope, and in normal format that antecedent is
written out in full at every use — three nested scopes make it about ninety
tokens, written perhaps two hundred times. So size is driven by copying the
context and grows with steps times scope depth, and the compressed format
disposes of it. The elaborated corpus is 144 KB and its largest proof,
`thm:least-combination-divides`, is 26 KB; in normal format each is larger by
orders of magnitude, since nothing about the proof changes and only the
repetition is written down differently.

It verifies faster too, because a step that was kept is not checked again.
What makes it safe is that the proof written is the proof that was given:
`compress.expand` reads one back, and `parley/test_compress.py` asks that of
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

`parley/gate.py` runs nine stages: the lint settings, that no caller hands on
a decline without asking whether it has one, the planted shapes that prove that
stage still finds them, the checker over the whole corpus, the planted defects
that prove the checker still catches things, the planted defects that prove the
elaborator still reports things, every set.mm label the database names, that a
compressed proof is the proof it was made from, and a verifier over every proof
the elaborator has written.

`parley/declines.py` reads the tools' own source. A `Declined` is what a route
gives back when it does not apply, and a caller that uses one without asking
`declined()` has a proof that is not one. It reports a decline passed to a
call, bound to a name and then passed on, stored in a dictionary, written into
an f-string, unpacked as a tuple, or spread with `*`, in a function that never
asks about it; asking `is None` is not asking. A function declines if it gives
one back, and the set is closed across files, so `work.normalize` in
`elaborate.py` is `normal.py`'s. Running out of kernel variables is raised, not
declined: it is the tool at its limit, and never happens on a run where nothing
is wrong.

The last is the only one that is evidence the elaborator is right rather than
consistent. The others read the corpus against itself or against a list of
names, and a proof that assumes nothing and proves the wrong thing passes all
of them — which has happened: an `arithmetic` step emitted `1 = 1` for a claim
about `( 1 x. ( 1 + 1 ) ) / 2`, and the assumption count reported it as a win.

`parley/test_elaborate.py` is there because nothing else watches what the
elaborator does with a defect. Taking a step as stated is right where it has no
method for it and wrong where the text is wrong, and the difference is what
`Problem` and `Declined` are for: a defect is raised and nothing carries on past
it, a route declining is returned and asked about. Each case copies the corpus,
makes one edit, and requires that elaborating fails with a message naming
where. A case that elaborates cleanly is the failure it is looking for.

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
deduction-form lemma is stated in, and uses nothing.

Three rules follow, each a defect naming the line, checked where the proof is
sealed:

- **R1 — a step rests only on what it names**: the lines it cites, its own
  requires lines, and the sorts in scope; a block also on its own steps, what it
  assumes, and what a `join` closing it names (requirement 8). *step 3 rests
  on 1, which it does not name.*
- **R2 — a requires line rests only on its reason**: the lines its reason
  cites, and the step's other requires lines, which `check.py` also lets one
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
    witness's membership is at work. An `obtain` citing an item is read the
    same way, except that what it claims is the body of the item's "there
    is", so in place of the conclusion the checker asks that the item give
    one from what the step names: `def:odd` gives one only from a line saying
    n is odd.

What a line is *used for* is known too, though nothing reports it: a numbered
line whose every use is by requires lines is a dull fact by `READERS.md`'s
definition — `geometric-sum`'s line 1, `1 − a ≠ 0`, is the one in the corpus.

`test_elaborate.py` and `test_check.py` plant one case of each rule, and each
is confirmed to have elaborated or checked cleanly before its rule existed.

### What they do not check

**Method steps, in the checker.** It accepts 63 steps resting on a closure
method without checking them; what a method decides, and what it demands, is
the elaborator's.

**That an element is a set.** set.mm has everything a set, so `a ∈ X` makes a a
set by `elex`, and a reader told `let a ∈ X` with X a set of numbers does not
think a is one. `thm:powerset-split-disjoint`'s proof needs it and is held out
of `proof/` until it is decided which gives way; see *What a file states rather
than proves*.

## Geometry

The readable layer writes `∠CAB = ∠CBA`, an equation between numbers, and no
Metamath library has a number to put there: set.mm's Euclidean geometry is
Tarski's axioms, whose angle congruence `cgrA` is a relation with nothing on
either side of an `=`, and its one numeric angle is in analysis, over ℂ, and
signed.

`GEOMETRY.md` weighs the seven candidates and takes the complex plane with the
angle read unsigned. The angle is a constant this corpus declares — `ang`, in
`definitions.mm` — and the four items set.mm does not state are proved in
`elaboration/geometry.mm`. `isosceles` elaborates and assumes nothing.

What that costs is non-degeneracy: `angval` wants both arguments non-zero and
`ang180` wants three points pairwise distinct, so `def:triangle` elaborates to
a conjunction taken apart at nearly every step. Synthetic geometry says "A, B,
C form a triangle" once and is done.

## Keeping set.mm where the tools can see it

`parley/labels.py` reads 278 labels — every token of a `target` or a `defines`,
which are machine-read and so name nothing else, plus what
`targets.MEMBERSHIP` lists — and asks set.mm whether it has them.

`metamath` is prose meant for a person and names its labels in a sentence, so
it is read only as far as it is certainly naming them: the leading entries that
are a single label-shaped word, stopping at the first that is not. That gives
`df-dvds` out of `df-dvds, whose right side is the same existential` and
nothing out of `Σ over 0...n with fsum1 and fsump1`. Reading that field is not
optional — the one error the check has ever found was a `dvds` that meant
`df-dvds`, and it was there.

set.mm is 51 MB and belongs to metamath, so it is not committed: say where it
is with `SET_MM`, or leave a copy or a link at the root of the working tree.
`mmverify.py` is not vendored either — `MMVERIFY`, or a copy or link at the
root — because what checks these proofs should not be a copy this project
maintains. Missing, the stage says so and the gate is not green, the way it
goes for ruff: a gate that skipped either would be saying green about a thing
it had not looked at.

`parley/verify.py` runs `mmverify.py` over all 30 proofs — the sixteen
theorems and `geometry.mm`'s fourteen lemmas — in about nineteen seconds,
nearly all of which is reading set.mm. Given a file whose whole contents are
`$[ set.mm $]` it takes 17.8 seconds, and the proofs add a tenth of one.
Which files that one includes is read off the `$[ ... $]` lines rather than
listed: a proof nothing else includes is a root. A list written down would
leave the gate green on the day a proof was added and not read.

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

8. **Some methods are absorbed by their block.** `join` inside a
   `contradiction` emits nothing; inside a `case` it emits `jca` and pairs its
   cited lines by what they claim rather than by the order the line lists them,
   since the readable order is the order they were derived and the conclusion's
   order is the theorem's. So the expansion of a block is not the concatenation
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

17. **An abbreviation, carried by neither side.** `define` names a thing and the
    proof is about the thing.

18. **A chain may change relation partway.**

19. **A standalone `fix` is a generalisation**, and which of the two it is is
    settled by whether the block is a part of something.

20. **The corpus and set.mm may state one fact as two formulas.** Four kinds. A
    *rearrangement* is the same operators permuted, and `db/notation.records`
    names it with `commutes`. A *named equivalence* is two constructs set.mm
    proves equal, and something has to point at the theorem that does. A
    *rebuilt quantifier* is neither and needs a proof, which is why
    `thm:prime-factor` is not a gap a table could close. A *rescaled denial* is
    the normaliser's, since the polynomials decide it.
