# Elaborating the corpus

Everything in this repository rests on one claim: that a readable proof becomes
a Metamath proof that verifies. Nothing had tested it. The checker had grown to
where it reads every formula, matches every citation against what it cites, and
reports nothing, and none of that touches the kernel.

So five proofs were worked out by hand, end to end, to find what the expansion
language has to be able to say. A program now elaborates those five and three
more, and the last two of those are proofs nothing here was written for, which
is the only test a language read off five examples can be given. The hand work
is below; what the program found is under *Elaborated by a program* and *Three
proofs from outside*.

`GOALS.md` open question 4 says that language can wait until the work has shown
which methods are needed and must be settled before any enriched proof is
written. Both conditions are now met.

The second proof is here because it cites the first. A proof that only uses
set.mm tests the expansion of methods; a proof that uses a theorem this project
elaborated tests whether an elaborated theorem can be cited at all, which is
the claim the whole corpus rests on. It cannot, in the form the first proof was
first written, and that is the finding the closed form below comes from.

The third is the one the other two were written for. `thm:sqrt2-irrational` is
the largest theorem in the corpus, it cites both of the others, and it nests
three scopes inside a supposition. It is where the shapes the first two found
either hold at size or do not.

The fourth covers what the first three could not reach. None of them contains
an `induction`, a `fix`, or a recursive definition, and `thm:sum-formula` has
all three.

The fifth closes the last two gaps. `thm:abs-bounds` is the only small theorem
with a `cases` block, which was the one block form nothing had tested, and its
four `inequalities` steps are the first of that method to be expanded.

**The labels are checked.** They were written from memory first and then read
against set.mm, which has 119,378 labels. Every one used below exists and says
what is claimed of it. The statements are quoted where they matter.

That check covers the whole database and runs in the gate, where it reads 233
labels and finds every one of them in set.mm. Its first run found exactly one
wrong: `def:even` said `dvds`, which is not a label, where it meant `df-dvds`.
Nothing else in three pilots' worth of remembered labels was wrong, which is a
better result than the exercise expected. *Keeping set.mm where the tools can
see it* below says how the check decides what is a label.

## The first proof

`thm:odd-square`, six steps, the smallest theorem in the corpus.

```
theorem odd-square
  let n ∈ ℤ                                                           (H1)
  assume n is odd                                                     (H2)
  then n² is odd

1.  k ∈ ℤ. n = 2k + 1.
    obtain k: def:odd n := n, from H1, H2

2.  n² = (2k + 1)²
    substitute n = 2k + 1 (line 1)

3.  (2k + 1)² = 4k² + 4k + 1
    algebra
    requires k ∈ ℝ: thm:int-real, from 1

4.  4k² + 4k + 1 = 2(2k² + 2k) + 1
    algebra
    requires k ∈ ℝ: thm:int-real, from 1

5.  n² = 2(2k² + 2k) + 1
    calculation
      n² = (2k + 1)²           2
         = 4k² + 4k + 1        3
         = 2(2k² + 2k) + 1     4

6.  n² is odd
    def:odd n := n², from 5
    requires n² ∈ ℤ: thm:int-closure, from H1
    requires 2k² + 2k ∈ ℤ: thm:int-closure, from 1
```

The notation records name the kernel constructors: `ℤ` is `cz`, `=` is `wceq`,
`+` is `caddc`, `·` and juxtaposition are both `cmul`, `²` is `cexp` with the
numeral 2, and "is odd" is `2 ∥ n` negated. `def:odd` says the same thing a
second way, as `there is k ∈ ℤ with n = 2k + 1`.

## What each step becomes

**The statement.** `n` is an integer, so it is a class, and the two hypotheses
become the antecedent of an implication:

```
$p |- ( ( A e. ZZ /\ -. 2 || A ) -> -. 2 || ( A ^ 2 ) )
```

The obvious reading is the other one, with each hypothesis a `$e` statement of
its own and the conclusion standing alone. It is what this proof was written as
first, and it verifies. What it cannot do is be cited by the second proof: a
Metamath essential hypothesis has to be discharged by a proved statement, and
the step that cites odd-square sits inside a contradiction block, where nothing
is proved and every line is an implication out of a supposition.

So the hypotheses go in the antecedent, for every theorem, because any theorem
may someday be cited under a supposition. This is not a fact about odd-square;
it is how the readable layer's `let` and `assume` map onto the kernel at all,
and it took a second proof to find.

**Step 1, the obtain.** This is the finding that matters most, and it is not a
step at all. `def:odd` is a bridge rather than a definition, and the bridge is
one lemma:

```
odd2np1  |- ( N e. ZZ -> ( -. 2 || N <-> E. n e. ZZ ( ( 2 x. n ) + 1 ) = N ) )
```

so the hypotheses yield `E. k e. ZZ ( ( 2 x. k ) + 1 ) = A`. There is no kernel
move that then hands you a `k`. What happens instead is that everything below
is proved out of `k e. ZZ /\ ( ( 2 x. k ) + 1 ) = A`, and the existential is
discharged at the very end with `rexlimdva`, whose result is then applied to
the existential itself with `mpd`.

So one readable step changes the shape of every step after it. Steps 2 to 6
become the body of an implication, and the proof from step 2 onward is written
in deduction form, each line an implication whose antecedent carries the
hypotheses and the obtained facts together. An elaborator cannot expand a step
in isolation and concatenate the results.

The lemma writes the equation as `( 2 x. n ) + 1 = N` where the corpus writes
`n = 2k + 1`. The sides are the other way round. Nothing in the readable layer
says which way an equation faces, so an elaborator has to be ready to flip one,
and here the flip is free because the congruence step wanted that orientation
anyway.

**Step 2, the substitute.** From `A = ( ( 2 x. k ) + 1 )` conclude
`( A ^ 2 ) = ( ( ( 2 x. k ) + 1 ) ^ 2 )`. That is a congruence lemma, and which
one depends on where the replaced subterm sits: the base of a power is the first
argument of `^`, so `oveq1`. Had it been the exponent it would be `oveq2`, and
inside a function application `fveq2`.

So the elaborator walks the path from the root of the claim to the occurrence
being replaced and emits one congruence lemma per step of that path. The rule is
mechanical and the choice is forced by the tree.

**Steps 3 and 4, the algebra.** `( ( ( 2 x. k ) + 1 ) ^ 2 ) = ( ( ( 4 x. ( k ^
2 ) ) + ( 4 x. k ) ) + 1 )` and then the regrouping into `( ( 2 x. ( ( 2 x. ( k
^ 2 ) ) + ( 2 x. k ) ) ) + 1 )`. These are ring identities over the reals, and
they are the one part of this proof with no shape yet. The first is close to a
lemma set.mm already has:

```
binom2  |- ( ( A e. CC /\ B e. CC ) ->
             ( ( A + B ) ^ 2 ) = ( ( ( A ^ 2 ) + ( 2 x. ( A x. B ) ) ) + ( B ^ 2 ) ) )
```

but close is the problem: at `A = 2k` and `B = 1` it gives
`( ( ( 2 x. k ) ^ 2 ) + ( 2 x. ( ( 2 x. k ) x. 1 ) ) ) + ( 1 ^ 2 )`, and
getting from there to `4k² + 4k + 1` is the normalisation that does not exist
yet: `sqmul` for the first term, `mulrid` for the second, `sq1` for the third,
then the arithmetic on the numerals. Each of those needs its arguments in ℂ,
which is exactly what the `requires k ∈ ℝ` line is for.

Naming those four took four lookups, and one of them I first wrote as `mulid1`,
which does not exist. That is the smallest concrete argument for keeping set.mm
where the tools can see it.

This is where the work is. Everything else in this proof has a forced
expansion; `algebra` needs a normalising procedure and a fixed order of lemmas,
or two elaborators will produce different proofs of the same identity.

**Step 5, the calculation.** Three lines chained by equality become two
applications of `eqtri`. A chain of n relations folds into n−1 transitivity
steps, and the relation decides the lemma: all equalities give `eqtri`, a mix
of `=` and `≤` gives the `eqbrtrd` family, and `<` anywhere gives the strict
one. In deduction form each is the `d`-suffixed variant.

**Step 6, the definition used the other way.** From `( A ^ 2 ) = ( ( 2 x. M ) +
1 )` with `M = ( ( 2 x. ( k ^ 2 ) ) + ( 2 x. k ) )` an integer, conclude
`E. j e. ZZ ( A ^ 2 ) = ( ( 2 x. j ) + 1 )`, which is `rspcev`: restricted
existential introduction, with the witness `M`. The witness is never written in
the text, and it does not have to be, because the cited line determines it. Then
the definition is used right to left to get back to `-. 2 || ( A ^ 2 )`.

The two `requires` lines are what `rspcev` needs: that the witness is in the
set it is being quantified over, and that the thing being claimed odd is an
integer.

**Closing.** The existential from step 1 is discharged with `rexlimdva`, which
takes the implication built from steps 2 to 6 and gives an implication from the
existential to the conclusion, free of `k`. `odd2np1` is thus used in both
directions: left to right to open the scope, right to left to close it.

Every one of the twenty-odd inner steps is a `d`-suffixed deduction-form
lemma. The claim that an obtain changes the shape of everything below it is not
a figure of speech: it changes which lemma each later step uses.

## The second proof

`thm:even-square`, six steps, three of them inside a contradiction block.

```
theorem even-square
  let n ∈ ℤ                                                           (H1)
  assume n² is even                                                   (H2)
  then n is even

1.  n is not odd
    contradiction
    suppose n is odd                                                  (S)

    1.1.  n² is odd
          thm:odd-square n := n, from H1, S

    1.2.  n² is not odd
          thm:not-both n := n², from H2
          requires n² ∈ ℤ: thm:int-closure, from H1

    1.3.  n² is odd. n² is not odd.
          join 1.1, 1.2

2.  n is even or n is odd
    thm:even-or-odd n := n, from H1

3.  n is even
    thm:disjunctive-syllogism P := n is even, Q := n is odd, from 2, 1
```

**Step 1.1, the citation.** This is the step the proof was chosen for, and it
is one label: `oddsq`, applied with `syl` to the two hypotheses conjoined by
`jca`. The supposition is a conjunct of the antecedent, not a proved statement,
which is what forces the closed form above. With it, citing an elaborated
theorem costs exactly what citing a set.mm theorem costs.

**Step 1.3, the join, has no expansion of its own.** There is no kernel move
that takes two lines and pairs them into a contradiction. The block closes with
`pm2.65d`, which takes the supposition implying a claim and the supposition
implying its negation, and gives the negated supposition. The join and the
block's close are one lemma, so `join` inside a `contradiction` is absorbed
rather than expanded. Whether `join` has an expansion of its own anywhere else
is open; nothing in this proof needed one.

**Steps 2 and 3 are propositional.** `def:odd` says that `n is odd` is
`-. 2 || n`, so `n is even or n is odd` is `( 2 || A \/ -. 2 || A )`, which is
`exmid`, and needs no integer hypothesis at all. The disjunctive syllogism is
`orel2`, applied in deduction form with `syl` and `mpd`. Step 1.2 is the same
story: from `2 || ( A ^ 2 )` conclude `-. -. 2 || ( A ^ 2 )`, which is
`notnotd`.

So two of the four cited theorems here reduce to propositional logic once the
parity encoding is fixed, and their `metamath` fields said otherwise.
`thm:even-or-odd` named `zeo` and `thm:not-both` named `zeo2, oddm1even`, which
are theorems about `2 || ( N - 1 )` — the right labels for an encoding where
"odd" means `n - 1` is even, and the wrong ones for the encoding `def:odd`
chose. The fields now name `exmid` and `notnot`, and each carries a note saying
why the arithmetic labels are not the ones.

The readable proof never cites double negation, and its expansion is classical
anyway. That is not smuggled in by a method: the classical content is `exmid`,
which the proof cites by name in step 2.

## The third proof

`thm:sqrt2-irrational`, twenty-one steps, three scopes deep. The whole of it is
in `proof/sqrt2-irrational.proof`; what follows is what each new shape in it
became.

**The obtain of two names is one discharge.** Step 3.1 obtains `p` and `q`
together from `thm:lowest-terms`. The kernel move is `rexlimdvva`, whose
hypothesis is `( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps -> ch ) )` — one lemma,
not two nested ones. set.mm has this family indexed by how many names are
obtained at once, so an elaborator picks by arity rather than nesting.

**The kernel's bound variable has to be renamed, and it is not optional.**
`divides` supplies `E. n e. ZZ ( n x. M ) = N`, always with `n`. The readable
proof obtains `r` at 3.6 and `s` at 3.13, both from `def:divides`. The second
scope's antecedent already carries the first obtained name free, so reusing
`n` would break `rexlimdva`'s own disjointness condition. The rename is
`cbvrexv`, and every obtain needs one.

**The orientation tax recurs and compounds.** `odd2np1` wrote the equation
backwards from the corpus, and so does `divides`: `( n x. M ) = N` where the
text writes `n = d·k`. Each use of `def:even` or `def:divides` therefore pays a
flip and a commutation — `eqcomd` and `mulcomd` — which appear nowhere in the
readable proof. There are three of them here.

**Two steps expand to nothing.** Steps 3.14 and 3.15 conclude `2 divides p` and
`2 divides q`, which 3.5 and 3.12 already established as `p is even` and
`q is even`. Once `def:even` and `def:divides` are unfolded these are one
formula: the readable layer has two words where the kernel has one. The steps
are not idle in the text — 3.16 exhibits a `d` that *divides*, and the word has
to match — but their expansion is the identity.

**`substitute into line 1`.** Step 3.2 replaces a subterm of a cited line
rather than of its own claim. The congruence machinery is the same; what
changes is which tree the path is walked in. So `substitute` takes a target,
and the claim is only its default.

**`exhibit` is witness introduction again.** Step 3.16 is `rspcev` with the
witness `2`, exactly as step 6 of odd-square was `rspcev` with the witness read
off a cited line. The difference is where the witness comes from: there the
cited line determined it, here the `requires 2 ∈ ℤ` and `requires 2 > 1` lines
name it. One expansion, two sources for the witness.

**A comma list of three has no forced shape.** "d > 1, d divides p, and d
divides q" became `w3a` here. Nested `/\` would have been just as faithful, and
nothing in the readable layer chooses between them. That is the second place,
after `algebra`, where two elaborators could disagree while both being right.

**`thm:lowest-terms` does not match the label the database names.** The field
says `qredeu or similar`, and the hedge is earned: `qredeu` gives unique
existence of a *pair* in `( ZZ X. NN )` whose `gcd` is 1, where the readable
statement gives two integers with `q > 0` and no common divisor above 1.
Between them sit pair projections, `NN` against `ZZ` with `0 <`, and the
equivalence of `gcd = 1` with having no common divisor above 1. That is a proof
of its own, so `thm:lowest-terms` is an axiom here, in the shape its readable
statement has.

## The fourth proof

`thm:sum-formula`, eight steps, and the first here with an `induction`, a
`fix`, or a recursive definition. It is the induction theorem from the
candidate set `GOALS.md` question 2 names, though that question asks for the
target proofs written at both reader levels, which is a different exercise
from this one.

**`induction` is one lemma, and its two hypotheses are the two blocks the text
writes.** `nnind` wants `|- ps` — a closed statement — and
`( y e. NN -> ( ch -> th ) )`. Those are exactly the readable proof's `base`
block, which stands alone, and its `step` block, which is an implication out of
`let k ∈ ℕ` and `assume IH`. Nothing had to be reshaped to fit.

**But the claim has to be abstracted over a variable, which the text never
does.** `nnind` also takes four biconditionals — the claim at `x = 1`, at
`x = y`, at `x = y + 1`, and at `x = A` — and the readable line says only
"induction on n starting at 1". So the elaborator has to read the claim as a
function of the induction variable and build four instances of it by
congruence. Every other method so far consumed claims whole; this is the first
that takes one apart.

**`fix` cost nothing of its own.** The `fix` block became `ex`, and its `let`
and `assume` became the two conjuncts of an antecedent, exactly as `obtain` and
`contradiction` do. Requirement 1 asserted this about `fix` without evidence;
it now has some.

**A recursive `def:` is a pair of theorems, one per clause.** `def:S` has two
`then` groups and its `metamath` field names `fsum1, fsump1`. Both are right,
and each is used where the readable proof uses the clause it states: `fsum1`
at step 1.1, `fsump1` at step 1.4.1.

**The finding that was not expected: a disjointness condition forced a step out
of the scope the text puts it in.** `fsump1` requires that its bound variable
not occur in the antecedent. The induction hypothesis is an equation between
sums, so it mentions that variable. Step 1.4.1 is written inside the `fix`
block, below `assume S(k) = k(k+1)/2`, and it cannot be proved there. It has to
be proved under `k ∈ ℕ` alone and carried into the scope afterwards.

That is new, and it is the first constraint found that is not about which
lemma to emit but about *where in the proof a step may be emitted at all*. The
readable order is still correct — the reader needs 1.4.1 where it stands — but
the elaborator cannot simply walk the steps in order, accumulating the scope as
it goes. It has to notice that a step's expansion is illegal under the current
antecedent and hoist it. Nothing in the three earlier proofs suggested a step
could fail for a reason that has nothing to do with what it claims.

## The fifth proof

`thm:abs-bounds`, eight steps, the first here with a `cases` block and the
first with an `inequalities` step expanded.

**`cases` is one lemma, and it completes the four block forms.** `mpjaodan`
takes `( ( ph /\ ps ) -> ch )`, `( ( ph /\ th ) -> ch )` and
`( ph -> ( ps \/ th ) )`. Those are the two `case` blocks and the disjunction
step 1 supplies. So every block the readable layer has — `obtain`,
`contradiction`, `fix`, `cases` — opens by conjoining its assumption onto the
antecedent and closes with one lemma, and requirement 1 is now evidence
throughout rather than assertion in part.

**`inequalities` has the same shape `algebra` does.** Its four steps here are
two of each of two kinds. 2.2 and 2.6 turn an equation into a non-strict
inequality: `leid` gives `x ≤ x`, and `breqtrd` rewrites one side using the
definition. 2.3 and 2.7 chain through zero: `le0neg2` or `le0neg1` flips the
sign, `letrd` composes, and `breqtrd` rewrites. The order is the same one
`algebra` follows — carry the atoms into ℝ, apply the ordering lemma the shape
calls for, then rewrite — and nothing searched.

That is not the whole method. `METHODS.md` specifies `inequalities` as linear
arithmetic over an ordered field, and none of these four needs a decision
procedure. It establishes the order for the easy shapes, as the first five
`algebra` steps did, and the equivalent of Bezout's step is still outstanding;
`intermediate-value` is where it lives.

**A `metamath` field may name something more general than the text.** `def:abs`
says "if x < 0 then |x| = −x" and names `absnid`, which holds for `x ≤ 0`. The
field is right and the extra generality is free, but case 2 has to get from
the strict assumption to the non-strict one with `ltle` before the definition
applies. So an unfolding can cost a step for no reason visible in either the
readable line or the field.

**`join` outside a contradiction does have an expansion, and its operands may
need reordering.** Requirement 8 said `join` inside a `contradiction` emits
nothing. Here it closes a `case` block instead, and it is `jca`. What the
readable line gives is derivation order: 2.8 says "join 2.6, 2.7", where 2.6
proved `−x ≤ |x|` and 2.7 proved `x ≤ |x|`, while the theorem states them the
other way round. So the elaborator pairs the cited lines by what they claim,
not by the order they are listed in.

## Elaborated by a program

The five proofs above were written by hand, and the requirements below were
read off them. `parley/elaborate.py` implements that list, and

```
parley/elaborate.py <theorem> <set.mm> > elaboration/auto/<theorem>.mm
```

produces a Metamath proof that verifies against set.mm. Four theorems go
through it — odd-square, even-square, sum-formula and abs-bounds — and nothing
in any of them is hand-written. `elaboration/auto/` holds what the program
writes; the files beside it are the hand elaborations, kept for comparison.

**All four block forms are implemented.** `abs-bounds` brings `cases`, which
closes with `mpjaodan` and is the first block to open a scope for each of its
parts rather than one for all its children. So requirement 1 is executable
throughout: every block widens the antecedent by what it assumes and closes
with one lemma, and the four lemmas are `rexlimdva`, `pm2.65d`, `ex` and
`mpjaodan`.

It also settles `join` outside a contradiction, which requirement 8 described
and nothing had run: it is `jca`, and the two lines are paired by what they
claim rather than by the order the text lists them, because the text lists
them as derived and the conclusion states them in the theorem's order.

**Reading set.mm's statements made the database say less, not more.** When a
theorem citation was described rather than matched, three items carried a
`target` saying which of the lemma's variables each part of the readable
statement filled — `notnot with ph := n is even`. Matching the lemma's
conclusion against the claim recovers all of that, and what the conclusion
does not fix is recovered by matching an antecedent against a line the step
already cites, which is how `orel2` learns which disjunct is ruled out. The
three fills are gone and the items name a label and nothing else.

The scope an `obtain` opens, the congruence path a `substitute` walks, the
fold of a `calculation`, the witness of a definition used to conclude an
existence claim, and every closure fact no `requires` line spells out are all
built from the readable text. What is not built is stated at the head of each
file: a closure method the program does not expand, or a definition the
database gives no target for. Even-square assumes nothing at all.

**Even-square is the one that matters, because it cites odd-square.** The
corpus makes 66 `thm:` citations against 39 `def:` ones, so citing a theorem
is the commonest thing a proof does, and odd-square contains none. Even-square
makes four, one of them to a theorem this corpus proves rather than one set.mm
supplies. The program emits that as a single label applied to the conjunction
of the facts the step gives it — `cA oddsquar syl` — which is the claim the
whole corpus rests on, now tested in code rather than by hand.

It also needs a second block form. `contradiction` conjoins its supposition
onto the antecedent exactly as `obtain` does and closes with `pm2.65d`, and
the `join` inside it emits nothing: the close consumes both joined lines
itself. So requirement 1 and requirement 8 are both executable now rather than
observed.

**Sum-formula tests requirement 13, and shows what a claim being a function
of a name costs.** `nnindd` wants the claim five ways — general, at 1, at the
induction variable, at its successor, and at what the theorem is about — and
the text writes none of them. The program reads the claim with the induction
variable rebound to a variable of the kernel, and ties each instance to the
general one by congruence. That forced the congruence machinery to handle
more than one occurrence at a time, since the claim holds its variable in
three places and `eqeq12d` and `oveq12d` change two operands at once where
`eqeq1d` and `oveq1d` change one. It also needed targets that nest: `S(_)` is
a sum over a range that holds the hole, so reaching the hole passes a `csu`
and then a `co`, and each level wants its own lemma.

Two smaller things fell out. A name a proof introduces becomes a variable of
the kernel, and it cannot be one a notation's own target binds — `S(_)` sums
over `k`, so a proof that fixes `k` must be given something else, or the sum
captures it. And `fix` closes with nothing at all when it is the step of an
induction: the block's own scope is already the shape `nnindd` asks its step
hypothesis to have.

**Requirement 14 fires, and it fires exactly where it was predicted to.**
Step 1.4.1 unfolds `def:S` through `fsump1`, which forbids its summation
variable in the antecedent. The step is written inside the `fix` block, whose
antecedent carries the induction hypothesis, and the induction hypothesis is
an equation between sums — so it holds that variable. The elaborator reports:

```
text puts the step at: ( ( A e. NN /\ j e. NN ) /\ sum_ k e. ( 1 ... j ) k = ( ( j x. ( j + 1 ) ) / 2 ) )
proved instead at    : ( A e. NN /\ j e. NN )
```

It proves the step one frame out and carries the result back in with
`adantr`. So an elaborator cannot walk the steps in order accumulating scope,
which is what this one did until the constraint bit: the scope a step is
proved at is chosen from the lemma's disjointness conditions before anything
is built, and each frame has to keep what was known at it, because the
hoisted step is proved from those facts rather than the innermost ones.

**What made it reachable was reading set.mm's statements.** `fsump1` has
three essential hypotheses — that the index is in the upper integers, that the
summand is complex, and one substitution instance — and none is a `requires`
line, because to a reader none is a step. Describing them in the database
would have meant writing kernel structure into a readable file. Instead
`parley/kernel.py` parses a set.mm statement into a term, so a lemma's own
statement says what it concludes and what it asks; `db/items.db` names
`fsum1, fsump1` and nothing more, and which clause applies is decided by
which one's conclusion is what the step claims.

That parser is an ordinary chart parse over set.mm's 1,472 syntax axioms, and
it round-trips 400 statements drawn at random through parse, reverse Polish
and back. What it buys beyond this one step is that a side condition can be
settled by matching: `parley/targets.py` lists the lemmas the elaborator may
use for a membership, and it tries each against what is wanted — which is how
`k ∈ ℂ` gets proved from `k` running over a range of integers, a fact the
readable proof never mentions because a reader never wonders about it.

The two kinds of citation want different things from the database. A theorem
this corpus proves needs nothing: the elaborator wrote its statement and knows
its shape. A theorem set.mm supplies needs to say which lemma, and how its
variables line up with the readable ones, because nothing derives that —
`thm:not-both` is double negation and its `ph` is what the readable statement
calls `n is even`. So those items carry `target notnot with ph := n is even`,
and the elaborator instantiates the lemma, peels its antecedents one at a
time, and answers each with a fact the step cites.

**Byte-identical output is not what happens.** `GOALS.md` question 4 asks
whether two elaborators must agree byte for byte or only produce something
that verifies, and now there are two elaborations of each of two theorems to
compare. None of them match.

| | by hand | by program | |
| --- | --- | --- | --- |
| odd-square | 1617 | 35504 | the hand proof cites two algebra lemmas, 1171 more |
| even-square | 342 | 436 | |
| sum-formula | 4024 | 68352 | |
| abs-bounds | 1001 | 58444 | |

None match, and neither side assumes anything, so the gap is the whole
result. Even-square is the row where the two are comparable at all, and it is
the one proof of the four with no closure method in it: the program is a
quarter larger, because where the hand proof pulled a fact out of the scope
once and used it twice, the program derives it at each use, since nothing
tells it that a fact is worth keeping.

The other three are twelve to sixty times larger, and the multiplier is a
count of closure-method steps rather than anything about the proofs. A hand
proof factors: odd-square's algebra is `oalg1` and `oalg2`, proved once beside
it and cited as two labels, so the 1617 is what is left after the hard part is
named. The program inlines, because it emits one `$p` per theorem and has no
notion of a lemma worth extracting. Abs-bounds is the extreme — 58× — and four
of its eight steps are `inequalities`, the method whose expansion carries a
Farkas certificate and a rewriting pass per step.

So the size is not a property of the elaboration. It is a property of a
program that never factors, measured against a person who always does.

**`inequalities` did not come cheaply, and it is worth saying why.** The
machinery that settles a side condition — match a lemma's conclusion against
what is wanted, settle what it asks in turn — generalises from memberships to
order relations without change, which is how `absnid` gets `x ≤ 0` from the
case assumption `x < 0` through `ltle`. What it cannot do is rewrite by a
cited equation, and that is what every one of abs-bounds' four
`inequalities` steps needs: each concludes something about `|x|` from a line
saying what `|x|` equals. Forward chaining from facts reaches neither. So the
method needs the same equality-aware rewriting `substitute` has, pointed at a
relation rather than at an equation. That is `from_equation`, and it is
written: all four steps are proved and abs-bounds assumes nothing.

What decides which cited facts a claim is built from, and in what multiple, is
`linear.certificate` — a Farkas certificate read off Fourier–Motzkin. The one
case still unwritten is a combination that scales an *inequality* rather than
an equation, which is a different proof; no step in the nine proofs needs it.

All of them verify. So verifiability is what an elaborator can be held to, and
byte-identity is a property of one implementation rather than of the language
— unless the language is specified far more tightly than these requirements
specify it.

**What the program needed that the databases did not say.** Writing it found
two gaps, and both are now closed by a `target` field beside `metamath`.

The `metamath` field of a notation says which constructor a pattern targets,
and six records wrote it as prose — "cexp with the numeral 2", "wbr with
cdvds", "2 ∥ n and its negation". That is the right thing to write for a
person checking that a label exists, and it is not usable by a program.
`target` says the same thing as a term in reverse Polish, with `_1`, `_2`
for the holes: `_ + _` targets `_1 _2 caddc co`, and `_²` targets
`_1 c2 cexp co`, which is a term carrying an operand the pattern has no hole
for. It also settles something `metamath` could not say at all: `_ > _`
targets `_2 _1 clt wbr`, sharing one constructor with `_ < _` by using its
holes in the other order. Thirty-seven records carry it; the ones that do not
are those whose term is not a constructor applied to their holes, and for
those `metamath` still says in words what it is.

The `metamath` field of an item says what a definition *means*, not which
theorem unfolds it. `def:odd` names `not 2 ∥ n`. An elaborator needs
`odd2np1`, the bridge between that and the existential the readable definition
states, and it appeared in no database. `def:odd` and `def:even` now carry a
`target` naming it, with `equation reversed` for the orientation neither the
readable line nor the label announces.

Neither was a defect. Those fields were written to record what the corpus
claims and to be checked by a person, and they do that. What they lacked was a
field an elaborator could read, and it took a working elaborator to say
exactly which field that was.

What stayed in `parley/targets.py` is closure: which set.mm lemma puts a sum of
integers in ℤ, and which moves an integer into ℂ. That is a fact about the
library rather than about the readable corpus, and no field of a readable
database is obviously its home.

Writing the elaborator also found that the corpus's `requires` lines were
checked for resolving and not for covering. `requires n² ∈ ℤ: thm:int-closure`
pointed at an item stating `a·b ∈ ℤ`, which does not cover a square, because
`square` is its own notation rather than sugar for a product. The checker now
matches a requires line against what it cites, the way it has always matched a
step's citation. Doing it reported ten lines across three proofs, and closing
them needed two statements `thm:int-closure` did not have — `a − b ∈ ℤ` and
`a² ∈ ℤ` — and two dull facts two steps had leaned on without writing.
`CLOSURE.md` records it.

## They verify

All five proofs are checked by a verifier, against set.mm and against a copy
truncated after the last statement they use. Odd-square and even-square are in
`elaboration/parity.mm`; sqrt2-irrational is in `elaboration/sqrt2.mm`, which
is built on `parity.mm` rather than on set.mm, so its citation of even-square
is a citation of a proof rather than of an assumption; sum-formula is in
`elaboration/sum-formula.mm`, abs-bounds in `elaboration/abs-bounds.mm`, and
Bezout's algebra step in `elaboration/algebra.mm`. A deliberately altered
conclusion is rejected in each file, so the check is real.

One statement in the two files is assumed: `thm:lowest-terms`, for the reason
given above. Everything else, every `algebra` step included, is proved
from set.mm's own theorems.

| | readable steps | proof tokens |
| --- | --- | --- |
| `oddsq` | 6 | 1617 |
| `evensq` | 6 | 342 |
| `s2irr` | 21 | 17652 |
| `sumform` | 8 | 4024 |
| `absbnd` | 8 | 1001 |
| the named `algebra` steps | 5 | 3138 |
| `balg1` | 1 | 19670 |

Even-square is the encouraging row: six steps, three of them inside a
contradiction block, and the citation of odd-square is one label. A theorem
costs its own expansion once, and every later use of it costs a citation.

Sqrt2-irrational looks like the discouraging one, and the reason is worth
naming. In deduction form every line is an implication whose antecedent is the
whole scope, and in RPN that antecedent is written out in full at every use.
Three nested scopes make it about ninety tokens long, and it is written perhaps
two hundred times. So proof size here is not driven by the steps; it is driven
by copying the context, and it grows with steps times scope depth.

Set.mm's compressed proof format exists for exactly this, and it disposes of
the problem: the same proof saved compressed is 2,393 bytes against 64,561,
twenty-seven times smaller. Nothing about the proof changes, only how the
repetition is written down. So the size an elaborator produces is a choice of
output format rather than a fact about the expansion, and the format to choose
is the compressed one.

`elaboration/build-parity.py` and `elaboration/build-sqrt2.py` generate the two
files, and those scripts are the first fragment of an elaborator: each builds
its expansions from the readable steps they came from, and the correspondence
is visible in the names. Between them they are 27 KB of Python producing 86 KB
of proof, from 4 KB of readable text.

## What algebra costs

`GOALS.md` question 6 asks how large a closure method's expansion may be, and
says it needs one of them written. Seven are now written: every `algebra` step
these four proofs contain, and the one step in the corpus that the others do
not resemble. Six are named theorems and measured below; the seventh is
sum-formula's step 1.4.3, which divides by 2 and is proved inline there, using
`divdir`, `divcan3` and `adddir` in the same order as the rest.

| | | tokens | compressed |
| --- | --- | --- | --- |
| `salg2` | `( A · 2 )² = 4A²` | 167 | 229 B |
| `oalg1` | `( 2n + 1 )² = 4n² + 4n + 1` | 558 | 519 B |
| `oalg2` | `4n² + 4n + 1 = 2( 2n² + 2n ) + 1` | 613 | 454 B |
| `salg3` | from `2A² = 4B²`, that `A² = 2B²` | 855 | 417 B |
| `salg1` | from `( A / B )² = 2`, that `A² = 2B²` | 945 | 466 B |
| `balg1` | Bezout's three equations, coefficients −1, 1, −q | 19670 | 1564 B |

So one readable word costs a few hundred to a couple of thousand kernel
tokens, and the split is the one the method's specification predicts. The
first three are normalisations with no cited equation, which is thirteen of
the corpus's eighteen steps. The next two each take a cited equation and
multiply through by a coefficient — ideal membership with a single generator — and cost
about half as much again, most of it in carrying the atoms into ℂ and
discharging the nonzero conditions.

**The important one is the last.** `thm:least-combination-divides` step 3
combines three cited equations with coefficients −1, 1 and −q, and is the only
step in the corpus whose coefficients are not constants. It was the case that
would have decided whether `algebra` needs a search. It does not: the order the
five smaller steps follow carries this one unchanged, with `mul12` and
`addsub4` doing the rearrangement and `subdi` read backwards doing the
factoring. Nothing here needed a Gröbner basis and nothing needed a search.
Each of the six is a fixed sequence — get the atoms into ℂ, apply the one
structural lemma the shape calls for, then reduce the numerals — and the reuse
is the evidence that this is a procedure rather than six separate puzzles.

The token column makes `balg1` look like a different animal, and the
compressed column says it is not. Its atoms number ten, all of which have to
be carried into ℂ, and normal format writes that ten-conjunct antecedent into
every line of the proof. Compressed it is 1,564 bytes: three times the other
algebra steps rather than twenty, and smaller than the sqrt2 proof. It is the
same effect scope depth has on sqrt2-irrational, from a wide hypothesis list
instead of a deep one, and the same format choice disposes of it.

What that leaves is a real cost and a measurable one: the price of an
`algebra` step is set by how many atoms it has to place in ℂ, not by how hard
the identity is.

## What the expansion language has to have

1. **Scopes, not just steps.** An `obtain` opens a scope that runs to the end of
   the proof, and every step inside it is elaborated in deduction form. All
   four block forms work the same way: the block's assumption is conjoined
   onto the antecedent, and the block closes with one lemma — `rexlimdva` for
   `obtain`, `pm2.65d` for `contradiction`, `ex` for `fix`, `mpjaodan` for
   `cases`. The expansion of a step is therefore a function of the step and of
   the scopes it sits inside, not of the step alone. `cases` differs in one
   way the others do not prepare for: it opens a scope for each of its parts
   rather than one for all its children, so the scope changes between
   siblings and not only on the way in and out.

2. **A path-directed congruence.** `substitute` needs the path from the root to
   the occurrence and one congruence lemma per step along it. Nothing is
   searched for; the tree decides.

3. **A fold for chains.** `calculation` is a fold of transitivity lemmas chosen
   by the relations in the chain, which is the simplest expansion in the proof.

4. **Witness introduction.** Using a definition to conclude an existence claim
   is `rspcev` with a witness read off a cited line, and the membership the
   `requires` lines carry is exactly its side condition.

5. **A normal form for `algebra`.** Six steps are now written, including the
   only one in the corpus with coefficients that are not constants, and none
   needed a search: atoms into ℂ, one structural lemma chosen by the shape,
   then the numerals. That is the fixed order decision 6 asks for, and it now
   covers every shape the corpus contains. What it costs is set by how many
   atoms have to be placed in ℂ.

6. **A def: may be a theorem.** `def:odd` targets `2 ∥ n` negated, so unfolding
   it is citing a set.mm theorem rather than replacing a definition. The
   database already says this is what `def:` means; the consequence for the
   elaborator is that unfolding costs a step and can fail, where a definitional
   replacement could not.

7. **One statement form for every theorem.** Hypotheses are conjoined into an
   antecedent, never made essential hypotheses, because a theorem cited inside
   a `contradiction`, `cases` or `obtain` block has nothing proved to discharge
   an essential hypothesis with. The form is decided by where the theorem may
   be used, which the theorem itself cannot know.

8. **Some methods are absorbed by their block.** `join` inside a
   `contradiction` emits nothing; `pm2.65d` closes the block and consumes both
   joined lines. Inside a `case` it emits `jca`, and pairs its cited lines by
   what they claim rather than by the order the line lists them, since the
   readable order is the order they were derived and the conclusion's order is
   the theorem's. So the expansion of a block is not the concatenation of the
   expansions of its steps, and a method's specification has to say what it
   does in each block that can contain it.

9. **An obtain is indexed by how many names it introduces, and renames every
   one of them.** Two names at once is `rexlimdvva`, not two nested discharges.
   And the existential the kernel supplies carries the kernel's own bound
   variable, so each obtain alpha-converts it to the name the text uses. Two
   obtains from one definition in nested scopes make the rename compulsory
   rather than cosmetic.

10. **An orientation policy.** The kernel's definitions write their equations
    the opposite way from the corpus, in every case met so far. An elaborator
    has to be willing to turn an equation round, and to commute a product,
    without either appearing as a step in the text.

11. **`substitute` takes a target.** It may replace a subterm of a cited line
    rather than of the step's own claim, which is what `into line 1` says. The
    claim is the default, not the only choice.

12. **A fixed shape for a comma list.** Three conjuncts may be one `w3a` or two
    nested `/\`. Nothing in the readable layer decides, and decision 6 wants
    two elaborators to agree byte for byte, so the expansion language has to.

13. **The claim read as a function of a variable.** `induction` needs the claim
    at four instances of the variable being inducted on, and the text writes
    none of them. Every other method consumes a claim whole; this one takes
    one apart and rebuilds it by congruence, so the expansion language needs
    to be able to say "this claim, with this name replaced".

14. **A step may have to be hoisted out of its scope.** A kernel disjointness
    condition can make a step's expansion illegal under the antecedent the
    readable proof states it under, while the same step is provable one scope
    out. Step 1.4.1 of sum-formula is the case: `fsump1` forbids its bound
    variable in the antecedent, and the induction hypothesis contains it. So
    an elaborator cannot walk the steps in order accumulating scope; it has to
    be able to prove a step earlier than the text states it and carry the
    result in. This is the only constraint found so far that is about where a
    step may be emitted rather than about which lemma it emits, and it is
    implemented: the scope is chosen from the lemma's disjointness conditions
    before anything is built, and each scope keeps the facts known at it.

15. **A definition is read whichever of three ways the claim asks for.** A
    biconditional definition may reach an existence claim by supplying a
    witness, may be read right to left from lines the step already holds, or
    may be unfolded left to right and taken apart. `def:even` does the first,
    `def:irrational` the second, `def:set-builder` the third, and which one
    applies is settled by what the lemma states and what the step claims, not
    by how the readable right side is phrased. A definition's target may also
    name more than one lemma: `rabid` and `elrab` say the same thing of a
    set-builder and differ only in what they ask.

16. **A name introduced is not the letter it is spelt with.** `prime-above`
    obtains a p and concludes that there is a p; Cantor's B collects the x its
    own image leaves out and the proof then fixes an x. The kernel has to see
    two names where the text writes one, or the lemma that discharges the
    second finds the first. Three places choose a variable and all three must
    agree: what an `obtain` introduces, what a `fix` fixes, and what a claim
    quantifies over. A binder's name may also be one set.mm declares as a
    class, as Cantor's B is, and then no letter will do.

17. **An abbreviation, carried by neither side.** `define` names a thing and
    the proof is about the thing. Binding the name to its term and never
    emitting it is what keeps it apart from a bound name spelt the same.

18. **A chain may change relation partway.** `calculation` folds equalities
    into a `≤` in the triangle inequality, so the lemma is chosen by the pair
    of relations either side of each join rather than fixed for the chain.

19. **A standalone `fix` is a generalisation.** Inside an induction the block
    is one part of it and the induction takes it as it stands; on its own it
    closes with `ralrimiva` over the name it fixed. Which of the two is
    settled by whether the block is a part of something.

20. **The corpus and set.mm may state one fact as two formulas.** Three kinds,
    and only the first is a normaliser's. A *rearrangement* — `2k` against
    `k x. 2` — is the same operators permuted, and `db/notation.db` names it
    with `commutes`. A *named equivalence* — `p ∈ ℤ≥2` against `p > 1` — is
    two different constructs that set.mm proves equal, and something has to
    point at the theorem that does. A *rebuilt quantifier* — primality in the
    domain against primality in the body — is neither, and needs a proof. The
    first two can be declared; the third is why `thm:prime-factor` is assumed
    and not a gap to be closed by a table.

## Three proofs from outside

The fourteen above were read off five proofs. A list derived from five
examples is not a language until something it did not see goes through it, so
three more were elaborated: `thm:triangle-inequality`, which the fifth proof
was a lemma for, and then `prime-above` and `cantor`, which nothing here was
written for.

That made eight, and `isosceles` below makes nine. This is the tally for all
of them as it now stands — what each proof still takes as stated rather than
builds:

| proof | assumed | |
|---|---|---|
| odd-square | 0 | |
| even-square | 0 | |
| sum-formula | 0 | |
| abs-bounds | 0 | |
| triangle-inequality | 0 | |
| cantor | 0 | |
| isosceles | 0 | |
| sqrt2-irrational | 1 | `thm:lowest-terms` |
| prime-above | 2 | `thm:prime-factor`, `def:prime` |

All nine verify, and seven of them assume nothing at all. That number was 26
across eight proofs when this section was first written; what closed the gap
was writing the four closure methods out rather than taking their steps as
stated, and the assumption count is the measure that says whether a method is
written or only named.

The three that remain are not closure methods and no amount of emitter work
reaches them. Each is an item whose `metamath` field names a set.mm theorem
that is close and is not the same shape, so the item carries no `target` and
an elaborator has nothing to point at:

- `thm:lowest-terms` — `qredeu or similar`, which is the field admitting it
  has not been pinned down.
- `thm:prime-factor` — `exprmfct` says `E. p e. Prime p || N`, putting
  primality in the domain, where the readable line quantifies over ℕ and says
  it in the body, which is how a reader meets the claim.
- `def:prime` — `isprm2` is the unfolding but writes `p > 1` as `p ∈ ℤ≥2`.
  set.mm proves `p > 1` outright as `prmgt1`, which is what the proof actually
  uses, but naming it in `target` would be naming a consequence rather than an
  unfolding.

All three are the same debt: the readable statement and set.mm's are
equivalent, and the bridge between them is a proof rather than a field. That
is what `elaboration/geometry.mm` already is for four geometry items, so the
mechanism exists and these three have simply not been written.

Six more requirements came out of the three, listed above as 15 to 20. None
contradicts the fourteen and none is a repair to them; they are shapes the
five proofs did not contain. That is the result worth recording — the language
grew, and did not have to be rebuilt.

Two things were found in the elaborator that the five proofs never exercised.
`freeze` and `rewrite` both read a binder's own variable as a term rather than
as the variable, so a claim carrying a binder came out malformed; no proof had
one until Cantor. And an assumed step stated only what its `requires` lines
said and dropped the lines it cited, which meant `thm:abs-bounds` assumed its
own conclusion twice and the triangle inequality assumed the heart of its own
case one. Both verified. A file that verifies is not the same as a theorem
that is proved, and the difference is what the file leaves out.

Three more `metamath` fields were wrong, past the two the five proofs found.
`thm:factorial-nat` named `facnn`, which states the factorial as a sequence
product and says nothing about its closure. Nothing but elaboration finds
these, and each one found is an argument for elaborating the rest.

## The proof that could not be elaborated, and what set.mm has for it

`isosceles` was the ninth proof and it stopped before the elaborator was
reached. Six of the seven items it cites were marked `open` in `db/items.db`,
and five of the notations it uses had no `target`. That was not a gap in the
tools. What blocked it was that the readable layer writes `∠CAB = ∠CBA`, an
equation between numbers, and no Metamath library has a number to put there.

It elaborates now and assumes nothing. `GEOMETRY.md` weighs the seven
candidate geometries and takes the complex plane; the angle is a constant
this corpus declares, and the four items set.mm does not state are proved in
`elaboration/geometry.mm`. The section below is what that decision was made
against, and is kept because the reasoning is what makes the decision
checkable rather than merely recorded.

### What set.mm has

Euclidean geometry in set.mm is **Tarski's axioms**, and only those. It was
asked for as Hilbert, Tarski or Birkhoff in set.mm issue 49, and answered
with Tarski inside set.mm rather than a database of its own.

| | |
| --- | --- |
| `df-trkg` | `TarskiG`, from `TarskiGC`, `TarskiGB`, `TarskiGCB`, `TarskiGE` |
| `df-trkg2d` | `TarskiG2D`, the plane |
| `df-trkgld` | `TarskiGDim>=`, dimension |
| `dist`, `Itv` | distance and betweenness, slots of the structure |
| `df-cgrg`, `df-cgra` | congruence of segments and of angles, as relations |
| `df-lng`, `df-hlg` | lines and half-lines |
| `df-perpg`, `df-hpg`, `df-plng` | perpendicularity, half-planes, planes |
| `df-lmi` | line inversion |
| `df-angmgm` | a magma structure on angles |
| `tgsas` | side-angle-side, proved |
| `df-ee` | `EE = ( n e. NN |-> ( RR ^m ( 1 ... n ) ) )`, the coordinate model |
| `eengtrkg` | that `EEG ` N` is a Tarski geometry, so the model is one |

There is no Hilbert axiomatisation, and no geometry in any other Metamath
database: iset.mm, nf.mm, hol.mm and ql.mm are foundational variants with
less mathematics than set.mm, not subject libraries.

### Why that does not fit

A `TarskiG` structure carries a distance, so `|AC| = |BC|` translates
directly as `( A .- C ) = ( B .- C )`, and `axtgcgrrflx` is
`thm:distance-symmetric` exactly. Distances are not the problem.

Angles are. Tarski geometry has `cgrA`, which is angle **congruence** and a
relation: `<" A B C "> ( cgrA ` G ) <" D E F ">`. There is nothing on either
side of an `=`. `AngMgm` adds angles to each other; it does not measure one.

set.mm's one numeric angle is in analysis rather than geometry, over ℂ:

```
angval   ( A F B ) = ( Im ` ( log ` ( B / A ) ) )
angcld   ( X F Y ) e. ( -u _pi (,] _pi )
```

which is **signed**. `def:angle` already says what that costs: with a signed
angle `thm:angle-symmetric` is false, since ∠PQR = −∠RQP.

### Hilbert, and why writing it would not help

`thm:side-angle-side` records that its statement is "an axiom in Euclid and
in Hilbert", which invites the question of whether Hilbert could be written
for Metamath. It could, by either of two routes, and the mathematics is
charted: Braun and Narboux derived each of Tarski's and Hilbert's axiom
systems from the other in Coq, for plane neutral geometry, by mechanising
the first twelve chapters of Schwabhäuser, Szmielew and Tarski. Whoever
wrote it would be following a proof rather than finding one.

- **As a structure in set.mm**, the way Tarski was done: a `HilbertG`
  carrying points, lines and planes with incidence, betweenness and the two
  congruences. Being three-sorted costs nothing in ZFC.
- **As a database of its own**, with typecodes for point, line and plane and
  its own axioms, the way `hol.mm` and `ql.mm` are their own systems. Closer
  to what Hilbert wrote, since his is a theory and not a structure.

It would not help this corpus. Hilbert's congruence is a relation — `AB ≅ CD`
for segments and `∠ABC ≅ ∠DEF` for angles — exactly as Tarski's `cgrA` is.
Hilbert has no angle measure and no number anywhere in the system. That is
what synthetic geometry is. A second synthetic axiomatisation would leave
`∠CAB = ∠CBA` no more an equation than the first one does.

The obstacle is not which axioms. It is that the readable layer writes a
**measured** angle, and measure is the thing synthetic geometry deliberately
does without. A number appears only in a metric treatment.

### Birkhoff and SMSG, and which of them has the reader's angle

Two more axiom systems are worth writing down, because the obvious guess
about them is wrong and someone will make it again.

**Birkhoff's is metric and still does not help.** Its four postulates take
distance and angle measure as primitives, which is the property the readable
layer wants, and that makes it the natural thing to reach for. But Postulate
III puts the rays through a point in correspondence with the reals **mod 2π**,
and Postulate IV states similarity with `∠B'A'C' = ±∠BAC`. The `±` is there
because the measure is signed. In an isosceles triangle the base angles come
out `+θ` and `−θ`, so `∠CAB = ∠CBA` is false in Birkhoff proper, exactly as
it is over ℂ. Metric and unsigned are different properties and only the
second is the one this corpus needs.

**SMSG has the reader's angle, and is the largest of the options.** Its
Postulate 11 reads "to every angle there corresponds a real number between 0°
and 180°" — unsigned by axiom, which is the school reader's angle and no
other system's. SMSG is a modification of Birkhoff made for teaching, and it
is twenty-two postulates chosen for teachability rather than independence:
11, 12 and 13 are all protractor axioms. Formalising a deliberately redundant
system buys no economy for the redundancy.

Neither is formalised anywhere. GeoCoq lists a "Birkhoff-style system" among
the approaches it surveys, but `theories/Axioms` holds Tarski, Hilbert,
Beeson, Makarios and Gupta and no Birkhoff; its proved equivalences are to
Tarski. Isabelle has Hilbert, Mizar has Tarski, mathlib is analytic.

Two things settle it against both. An axiom system owes a consistency
argument, and the model either would need is the coordinate plane — so
neither replaces building that, each sits on top of it. And the foundation
is below the `target` field: Reader A meets `thm:side-angle-side` as a cited
item, and whether it resolves to an SMSG postulate or to a computation from
`lawcos` leaves the readable text byte for byte the same. The argument from
the reader, which is SMSG's whole case, does not reach the reader.

If the corpus ever does want a geometry that is axiomatic and matches what a
school reader was taught, SMSG is the target and the coordinate plane is the
model it would need first.

### What ℂ costs, which is one thing

The question worth asking of a backend is not what it can prove. ℂ with
`( abs ` ( P − Q ) )` for distance **is** the Euclidean plane, so every
theorem of plane geometry is a theorem about ℂ and nothing is out of reach.
What it costs is four things, of which one matters here.

**Angle addition is the one.** Splitting an angle by a ray —
`∠ABD + ∠DBC = ∠ABC` — is used constantly in traditional proofs, and over ℂ
the choice of convention decides which half of the arithmetic works.

| | addition | symmetry |
| --- | --- | --- |
| signed, as `ang` is | unconditional | `∠PQR = ∠RQP` false |
| unsigned, as `abs` of it | needs D inside the angle | true |

Both are not available. That is not a defect of ℂ: SMSG's own Angle Addition
Postulate carries the same betweenness hypothesis, and it is how unsigned
angles behave anywhere. But it means the corpus has to say which convention
it is in, and a proof that both adds and reverses angles pays at each step.

**Non-degeneracy multiplies.** `angval` wants both arguments non-zero,
`ang180` wants three points pairwise distinct, `lawcos` wants two. Synthetic
geometry says "A, B, C form a triangle" once and is done; over ℂ each angle
carries its own disequalities, so `def:triangle` elaborates to a conjunction
that is taken apart at nearly every step.

**The proof shape turns from citing to computing.** A traditional proof says
"by side-angle-side"; over ℂ that is a calculation through `lawcos`. Reader A
never sees the difference, since the readable text is unchanged — but the
elaborated proof is algebra where a reader of *it* would expect geometry, and
the step count grows to match.

**And it is the plane and nothing else.** No solid geometry and no statement
in n dimensions, ever. Tarski and `EE^n` generalise; ℂ does not.

Against that, set.mm's ℂ section is finished rather than a starting point:
`lawcos`, `pythag`, `isosctr`, `chordthm`, `heron` and `ang180`, and — the
part that is easy to miss — `affineequiv1` through `affineequiv4` and
`angpieqvd`, which are betweenness. `B = ( ( D x. A ) + ( ( 1 - D ) x. C ) )`
with `D e. ( 0 (,) 1 )` is B between A and C, and `angpieqvd` ties that to
the angle being π. So collinearity and betweenness are already there.

Two things are better than synthetic outright: similarity is multiplication,
and orientation is free.

So the summary is narrower than "a compromise". ℂ costs angle symmetry and
buys everything else. The corpus has one geometry proof and its conclusion is
`∠CAB = ∠CBA`, which is the single thing ℂ makes awkward. A dozen Euclidean
proofs would find ℂ mostly congenial; this one lands on its weak spot.

### What that leaves

Four readings, and the corpus has to choose one before `isosceles` can be
elaborated. None is an implementation question. `GEOMETRY.md` weighs all
seven candidates against the criteria `GOALS.md` and `READERS.md` state, and
lands on the second of these with the angle taken unsigned.

1. **ℂ, citing the result.** set.mm proves this theorem. `isosctr` is
   Metamath 100 proof 65, and it is `thm:isosceles` hypothesis for
   hypothesis — three points in ℂ, three disequalities, `( abs ` ( A - C ) )
   = ( abs ` ( B - C ) )`, concluding `( ( C - A ) F ( B - A ) ) = ( ( A - B
   ) F ( C - B ) )`. One citation elaborates the theorem and none of its
   twelve steps.
2. **ℂ, elaborating the steps, with the signed angle.** `isosctr` states the
   conclusion with `F` and is true, because its two angles are read in
   consistent orientations. What is then false is the proof's own
   `thm:angle-symmetric`, which four of its steps use. The text would have
   to be rerouted around it.
3. **Tarski.** `tgsas` is free and so is the rest of the apparatus. The
   readable layer would say angles are congruent rather than equal, which
   changes the theorem statement and five steps.
4. **The coordinate plane, with the angle constructed rather than assumed.**
   A point is a member of `EE 2`, distance is the structure's own `dist`,
   and

   ```
   ∠PQR := ( arccos ` ( ⟨ P − Q , R − Q ⟩ / ( |P − Q| · |R − Q| ) ) )
   ```

   Cauchy–Schwarz puts the ratio in `[ -u 1 , 1 ]` by `ipcau`, `acosrecl`
   makes it real there and `acosbnd` lands it in `( 0 [,] _pi )`. The angle
   is unsigned by construction rather than by a convention or an absolute
   value applied afterwards, so `∠CAB = ∠CBA` is true as the text writes it.

The fourth is the only one that postulates nothing — a definition in ZFC,
with no consistency to argue — and `eengtrkg` leaves Tarski's apparatus
available above the same points. `thm:angle-symmetric` reduces to
`⟨u,v⟩ = ⟨v,u⟩` under it.

What it does not have is anything else. The three developments in set.mm do
not meet.

| development | what it has | what it lacks |
| --- | --- | --- |
| ℂ plane geometry | `isosctr`, `lawcos`, `ang180`, Pythagoras | a signed angle, and no tie to Tarski |
| Tarski | `tgsas`, `cgrA`, the synthetic apparatus | any angle measure |
| `EE^n` | `eengtrkg`, that it models Tarski | any geometry theorem of its own |

A scan of all 50,919 labelled statements finds **no statement mentioning
`EE ` 2`** and **none relating `CC` to `RR ^m`**. `EEhil` is named seven
times and five of those are topological manifolds. The nearest thing to a
bridge is `cnref1o`, a bijection `( RR X. RR ) -1-1-onto-> CC`, and it is
neither an isometry nor about `RR ^m ( 1 ... 2 )`, which is what `EE 2` is.

So `lawcos` is a theorem about ℂ and does not reach the coordinate plane.
Taking the fourth reading means writing the plane geometry that would use
it — the angle, its symmetry, a law of cosines in an inner product space,
and side-angle-side — from `ipcau`, `acosbnd` and the `CPreHil` machinery
upward. That is a chapter, not a few lemmas.

Which turns the choice into a plain one: the second reading rewrites four
steps of one proof, and the fourth writes a geometry development. For
`isosceles` alone the second is proportionate and `isosctr` is its target.
The fourth is the right foundation for a geometry corpus and the wrong one
for a single proof.

What is worth recording past the choice is that `isosctr` exists. `def:angle`
frames the signed angle as an obstacle, and the theorem set.mm proves with it
says the obstacle is `thm:angle-symmetric` rather than the theorem.

## What this says about the corpus

Nothing in any of the five proofs had to change, which is the encouraging
half. The steps the text writes are the steps the kernel needs, in the order it
needs them, and the `requires` lines carry the side conditions rather than
leaving them to be found. That is the design being tested and, on forty-nine
steps across five proofs including the largest in the corpus and every block
form the readable layer has, holding.

The one qualification is step 1.4.1 of sum-formula, which the kernel will not
accept where the text states it: `fsump1` forbids its summation variable in
the antecedent and the induction hypothesis holds that variable. The step is
right and the order is right for a reader, so what moved was the elaborator's
order and not the author's. `allowed` picks the innermost frame the lemma's
disjointness conditions permit, before anything is built, and `carry` brings
the result back in. Requirement 14 above is that rule, and it is the only
constraint found anywhere in this exercise that is about *where* a step may be
emitted rather than which lemma it emits.

One thing outside the proofs had to change: two `metamath` fields in the
database named the wrong set.mm theorems, because they were written for a
different encoding of oddness than `def:odd` settled on. Nothing detected that
until a proof was expanded, and no check the project has could: the fields were
existing labels, correctly spelled, saying something true about integers. What
they were not is what the expansion uses. That is a second kind of wrong field,
past the misspelling the label audit catches, and only elaboration finds it.

`algebra` carries six of these forty-nine steps and eighteen across the corpus,
and it was the one method whose expansion was a question rather than a shape.
All six are written, and so is Bezout's, which none of them resembles — the
only step in the corpus whose coefficients are not constants. All seven follow
one order, none of them searched, and the cost is set by how many atoms have to
be carried into ℂ. `algebra` is no longer the open end of the project.

All four closure methods are now written, and every block form is expanded.
`inequalities` got the decision procedure `METHODS.md` specifies: a Farkas
certificate read off Fourier–Motzkin, which says which cited facts a claim is
built from and in what multiple. Across the nine proofs it settles nine
`inequalities` steps and one `requires` line, and none of them is assumed.

What remains open is not a method. `thm:lowest-terms`, `thm:prime-factor` and
`def:prime` are statements the corpus cites for which set.mm has nothing of
quite the right shape, and they are the only three assumptions left anywhere.
Sixteen more `inequalities` steps sit in `bezout` and `intermediate-value`,
which is the largest untested weight on the method — two thirds of the
corpus's twenty-five. They are untested because those two proofs stop before
the elaborator, for reasons that have nothing to do with inequalities.

## Keeping set.mm where the tools can see it

The label check was run once from a copy fetched into a scratch directory
that did not outlive the session. It found one wrong field and no others,
which sounds like an argument for not bothering again.

It is the opposite. The database is 97 items and will grow, every new item
names a label from memory, and the check is a set membership against a file
that already exists. What it could not do while the file was temporary was
run in the gate, so the next wrong label would sit there as long as that one
did.

It is `parley/labels.py` and the gate's fourth stage. It reads 233 labels —
every token of a `target` or a `defines`, which are machine-read and so name
nothing else, plus what `targets.MEMBERSHIP` lists — and asks set.mm whether
it has them.

`metamath` is prose meant for a person and names its labels in a sentence, so
it is read only as far as it is certainly naming them: the leading entries
that are a single label-shaped word, stopping at the first that is not. That
gives `df-dvds` out of `df-dvds, whose right side is the same existential`
and nothing out of `Σ over 0...n with fsum1 and fsump1`. The two it misses
there are the price of never calling a word a label because it sat in a
sentence — and on this database the rule has no false positives at all.

Reading that field is not optional. The one error the check ever found was a
`dvds` that meant `df-dvds`, and it was in `metamath`. A version that skipped
it would have been a check that could not have found the thing it was built
for.

set.mm is 51 MB and belongs to metamath, so it is still not committed: say
where it is with `SET_MM`, or leave a copy or a link at the root of the
working tree, which `.gitignore` covers. Missing, the stage says so and the
gate is not green, the way it already goes for ruff — a gate that skipped
either would be saying green about a thing it had not looked at.

The check it buys is the only one in this project that compares the corpus
against something outside it.

## The five that do not elaborate

Nine of the corpus's fourteen theorems elaborate and verify. The five that do
not stop for five different reasons, which is worth saying plainly because it
means there is no one thing to build:

| theorem | stops at |
|---|---|
| `geometric-sum` | `notation geometric-function` has no `target` |
| `intermediate-value` | `notation continuous` has no `target` |
| `least-combination-divides` | an `obtain` that names no item is not expanded |
| `subsets-count` | no kernel name for `X` |
| `bezout` | a formula the kernel cannot read |

Only the third is a gap in the elaborator. Two are database fields nobody has
written, and two are failures at the reading stage that have not been
diagnosed.

### What `geometric-sum` turns out to be about

It looks like a missing field and is not. `G(n)` means the sum of `a^k` for
`k` from 0 to `n`, so the term the kernel needs mentions **two** things, `a`
and `n`, where the notation has one hole. `sum-function` is the precedent and
sidesteps it: `S(n)` is the sum of `k` over `1...n` and has no parameter at
all. `G` is the first local definition that has one.

The reader is not being misled by `G(n)`. `let a ∈ ℝ` fixes `a` for the whole
theorem, so inside it `a` is a constant and `G` really is a function of one
variable; `def:G` already declares `a` as its `H1`. The division is a sound
one — the definition declares what is fixed, the notation shows what varies.
What is missing is a place for the fixed parameter to live when the notation
is expanded.

Three places were considered. The `target` could name the proof's variable,
which changes no text the reader sees. The proof could write `G(a, n)`, which
needs nothing built but makes a constant look like an argument. Or `def:G`
could introduce a constant the way `def:angle` introduces `ang`, which does
not help on its own, because the pattern still has one hole and the `a` still
has to come from somewhere.

The first is the one to want, and it is not built, because of two things a
programming language would call by name.

**Dynamic scope.** A `target` naming `a` resolves it against the table of
names the *calling proof* holds. A second proof using `G` whose parameter is
called `r` fails loudly — `no kernel name for 'a'` — but one that happens to
have an unrelated `a` in scope would quietly get that one. Only
`geometric-series` uses `G`, so this cannot happen today.

**Capture.** Two places rewrite that table: a notation that binds, and a
`fix` block. Either would shadow a fixed name inside its body, so a proof
that bound `a` while writing `G(n)` would build a term about the bound `a`
and report nothing. `geometric-series` binds `k` in its induction step, not
`a`, which is the only reason this is invisible.

Neither is contained by design; both are unreachable by accident. A checker
rule refusing a proof that binds a name some notation fixes would close the
second completely and cheaply. The first is the harder one, and the honest
statement of it is that a local definition's parameter has no home: the
notation cannot hold it, the citation supplies it only where the definition
is cited and not where the notation merely appears, and the calling proof's
name table is the wrong place because it belongs to the caller.
