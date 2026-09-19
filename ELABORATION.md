# Elaborating two proofs by hand

Everything in this repository rests on one claim: that a readable proof becomes
a Metamath proof that verifies. Nothing had tested it. The checker had grown to
where it reads every formula, matches every citation against what it cites, and
reports nothing, and none of that touches the kernel.

So this is two proofs worked out by hand, end to end, to find what the
expansion language has to be able to say. `GOALS.md` open question 4 says that
language can wait until the work has shown which methods are needed and must be
settled before any enriched proof is written. Both conditions are now met.

The second proof is here because it cites the first. A proof that only uses
set.mm tests the expansion of methods; a proof that uses a theorem this project
elaborated tests whether an elaborated theorem can be cited at all, which is
the claim the whole corpus rests on. It cannot, in the form the first proof was
first written, and that is the finding the closed form below comes from.

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

`thm:even-square`, three steps, one of them a contradiction block.

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
parity encoding is fixed, and their `metamath` fields say otherwise.
`thm:even-or-odd` names `zeo` and `thm:not-both` names `zeo2, oddm1even`, which
are theorems about `2 || ( N - 1 )` — the right labels for an encoding where
"odd" means `n - 1` is even, and the wrong ones for the encoding `def:odd`
chose. The proposal is to change those two fields to `exmid` and `notnot`; it
is a change to the database and is not made here.

The readable proof never cites double negation, and its expansion is classical
anyway. That is not smuggled in by a method: the classical content is `exmid`,
which the proof cites by name in step 2.

## They verify

Both proofs are written out in `elaboration/parity.mm` and checked by a
verifier, against set.mm and against a copy truncated after the last statement
they use. The two `algebra` steps of odd-square are axioms in that file,
stating exactly what those steps claim; everything else uses set.mm's own
theorems. A deliberately altered conclusion is rejected, so the check is real.

Odd-square is 1617 tokens of proof for six readable steps. Even-square is 342
for three, of which the citation of odd-square is one label. That ratio is the
encouraging number in this exercise: a theorem costs its own expansion once,
and every later use of it costs a citation.

`elaboration/build-parity.py` generates the file, and that script is the first
fragment of an elaborator: it builds each expansion from the readable step it
came from, and the correspondence is visible in the names.

## What the expansion language has to have

1. **Scopes, not just steps.** An `obtain` opens a scope that runs to the end of
   the proof, and every step inside it is elaborated in deduction form. The
   same is true of `fix`, `cases` and `contradiction`, which already have block
   structure in the text. The expansion of a step is therefore a function of
   the step and of the scopes it sits inside, not of the step alone.

2. **A path-directed congruence.** `substitute` needs the path from the root to
   the occurrence and one congruence lemma per step along it. Nothing is
   searched for; the tree decides.

3. **A fold for chains.** `calculation` is a fold of transitivity lemmas chosen
   by the relations in the chain, which is the simplest expansion in the proof.

4. **Witness introduction.** Using a definition to conclude an existence claim
   is `rspcev` with a witness read off a cited line, and the membership the
   `requires` lines carry is exactly its side condition.

5. **A normal form for `algebra`.** The only method here without a forced
   expansion. Two elaborators agreeing byte for byte, which decision 6 asks
   for, is plausible for everything above and impossible for this one until the
   normalisation and the order of lemmas are fixed.

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

## What this says about the corpus

Nothing in either proof had to change, which is the encouraging half. The steps
the text writes are the steps the kernel needs, in the order it needs them, and
the `requires` lines carry the side conditions rather than leaving them to be
found. That is the design being tested and, on two proofs, holding.

One thing outside the proofs had to change: two `metamath` fields in the
database name the wrong set.mm theorems, because they were written for a
different encoding of oddness than `def:odd` settled on. Nothing detected that
until a proof was expanded, and no check the project has could: the fields are
existing labels, correctly spelled, saying something true about integers. What
they are not is what the expansion uses.

The discouraging half is that `algebra` carries two of the nine steps here and
eighteen across the corpus, and it is the one method whose expansion is still a
question rather than a shape. Any estimate of the elaborator's size is really
an estimate of that.

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
