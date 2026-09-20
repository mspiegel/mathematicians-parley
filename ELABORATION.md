# Elaborating four proofs by hand

Everything in this repository rests on one claim: that a readable proof becomes
a Metamath proof that verifies. Nothing had tested it. The checker had grown to
where it reads every formula, matches every citation against what it cites, and
reports nothing, and none of that touches the kernel.

So these are four proofs worked out by hand, end to end, to find what the
expansion language has to be able to say. `GOALS.md` open question 4 says that
language can wait until the work has shown which methods are needed and must be
settled before any enriched proof is written. Both conditions are now met.

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

**The labels are checked.** They were written from memory first and then read
against set.mm, which has 119,378 labels. Every one used below exists and says
what is claimed of it. The statements are quoted where they matter.

That check was extended to the whole database while set.mm was to hand. It
names 193 set.mm labels across 152 records, and all but one exist: `def:even`
said `dvds`, which is not a label, where it meant `df-dvds`. Fixed. Nothing
else in three pilots' worth of remembered labels was wrong, which is a better
result than the exercise expected.

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

## They verify

All four proofs are checked by a verifier, against set.mm and against a copy
truncated after the last statement they use. Odd-square and even-square are in
`elaboration/parity.mm`; sqrt2-irrational is in `elaboration/sqrt2.mm`, which
is built on `parity.mm` rather than on set.mm, so its citation of even-square
is a citation of a proof rather than of an assumption; sum-formula is in
`elaboration/sum-formula.mm` and Bezout's algebra step in
`elaboration/algebra.mm`. A deliberately altered conclusion is rejected in
each file, so the check is real.

One statement in the two files is assumed: `thm:lowest-terms`, for the reason
given above. Everything else, every `algebra` step included, is proved
from set.mm's own theorems.

| | readable steps | proof tokens |
| --- | --- | --- |
| `oddsq` | 6 | 1617 |
| `evensq` | 6 | 342 |
| `s2irr` | 21 | 17652 |
| `sumform` | 8 | 4024 |
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
first three are normalisations with no cited equation, which is twelve of the
corpus's seventeen steps. The next two each take a cited equation and multiply
through by a coefficient — ideal membership with a single generator — and cost
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
   the proof, and every step inside it is elaborated in deduction form. The
   same holds for `contradiction`, and for `fix`, whose `let` and `assume`
   become the conjuncts of an antecedent and whose block closes with `ex`.
   `cases` is the one block form still untested. The expansion of a step is
   therefore a function of the step and of the scopes it sits inside, not of
   the step alone.

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
   joined lines. So the expansion of a block is not the concatenation of the
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
    step may be emitted rather than about which lemma it emits.

## What this says about the corpus

Nothing in any of the four proofs had to change, which is the encouraging
half. The steps the text writes are the steps the kernel needs, in the order it
needs them, and the `requires` lines carry the side conditions rather than
leaving them to be found. That is the design being tested and, on forty-one
steps across four proofs including the largest in the corpus, holding.

The one qualification is step 1.4.1 of sum-formula, which the kernel will not
accept where the text states it. The step is right and the order is right for
a reader; what has to move is the elaborator's, not the author's.

One thing outside the proofs had to change: two `metamath` fields in the
database named the wrong set.mm theorems, because they were written for a
different encoding of oddness than `def:odd` settled on. Nothing detected that
until a proof was expanded, and no check the project has could: the fields were
existing labels, correctly spelled, saying something true about integers. What
they were not is what the expansion uses. That is a second kind of wrong field,
past the misspelling the label audit catches, and only elaboration finds it.

`algebra` carries six of these forty-one steps and eighteen across the corpus,
and it was the one method whose expansion was a question rather than a shape.
All six are written, and so is Bezout's, which none of them resembles — the
only step in the corpus whose coefficients are not constants. All seven follow
one order, none of them searched, and the cost is set by how many atoms have to
be carried into ℂ. `algebra` is no longer the open end of the project.

What remains open is `thm:lowest-terms`: a statement the corpus cites in one
line, for which set.mm has nothing of the right shape. It is the only
assumption in the four proofs. `cases` is the one block form no proof here
contains, and `inequalities` the one closure method with no expansion written.

## Keeping set.mm where the tools can see it

The label check above was run once, from a copy fetched into a scratch
directory that will not outlive the session. It found one wrong field in 193,
which sounds like an argument for not bothering again.

It is the opposite. The database is 97 items and will grow, every new item
names a label from memory, and the check is a set membership against a file
that already exists. What it cannot do while the file is temporary is run in
the gate, so the next wrong label will sit there as long as this one did.

Making it permanent means a large file somewhere stable and a gate that
degrades when it is missing, the way the gate already does for ruff. That is
the whole cost, and the check it buys is the only one in this project that
compares the corpus against something outside it.
