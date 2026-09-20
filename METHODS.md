# Specifications of the methods

`db/methods.db` says what a reader checks when a step cites a method.
`SYNTAX.md` says how the step is written. This document says what the method
decides: which claims it accepts, from which facts, and what it refuses.

A method's specification has six parts:

1. **Facts in.** What the cited lines must supply.
2. **Fact out.** Which claims the method can conclude.
3. **The procedure.** What a reader, and an elaborator, do to check it.
4. **Refusals.** What the method will not do, so that a step needing it fails
   to elaborate rather than being waved through.
5. **Hypotheses.** What the method requires of the terms, and how those are
   discharged.
6. **Expansion.** The kernel steps it targets.

The expansion language of open question 4 in `GOALS.md` is not designed, so
part 6 names the set.mm lemma families rather than giving the expansion.
Everything else is fixed here.

## Two rules every expansion obeys

Decision 6 of `GOALS.md` wants independent elaborators to agree, ideally byte
for byte. Two things would otherwise let two correct elaborators produce
different kernel proofs, so they are fixed here rather than left to each.

**An expansion supplies every sentence of every cited line, in order.** Not the
subset the method turns out to use. A method handed a five-sentence line could
be given all five or only the one it needs, and both are correct, so the choice
has to be made once. All three specified closure methods are monotone in their
premises: `inequalities` negates the claim and shows the system unsatisfiable,
and further true facts cannot make an unsatisfiable system satisfiable;
`algebra` tests ideal membership, and further generators only enlarge the
ideal; propositional entailment behaves the same way. So supplying everything
is always safe and never changes whether a step elaborates.

**A claim of several sentences associates to the left.** Five sentences become
`((((A ∧ B) ∧ C) ∧ D) ∧ E)`. The reason is compatibility rather than
principle: set.mm defines its ternary conjunction as the left-nested binary
one, so the common three-sentence case maps onto it directly and the
projection lemmas are the ones the library already has.

---

## inequalities

`inequalities` decides **linear arithmetic over an ordered field**. It is the
heaviest of the four closure methods, carrying 25 of the 61 steps that rest on
one, and it is the only one that needs a decision procedure rather than a
table of named laws.

### Atoms

Before anything else, both the cited facts and the claim are read as linear
expressions over **atoms**. An atom is a maximal subterm that is not built from
numerals and the operations `+`, `−`, `·` by a numeral, and `/` by a numeral.

So in `f(x₁) − f(c) ≤ |f(x₁) − f(c)|` the atoms are `f(x₁)`, `f(c)` and
`|f(x₁) − f(c)|`, three of them, and the last is an atom even though its own
inside contains the first two. The method never looks inside an atom and knows
nothing about what it means. That `|y|` is at least `y` is not available to it;
that fact reaches a step as a cited line, which is what
`thm:abs-bounds` is for.

### Facts in

Each line named in `from` supplies its claim as a linear fact. A fact is one of

```
e = 0        e ≤ 0        e < 0        not (e = 0)        not (e ≤ 0)
```

after moving everything to one side, where `e` is a linear combination of atoms
with rational coefficients. A cited line of several sentences supplies each
sentence that has this shape and is ignored for the rest, so citing a line that
also states a membership or a quantified sentence is not an error.

### Fact out

The claim must be a single fact of the same five shapes. Both an equation and
the negation of a relation are permitted as conclusions: the corpus concludes
`d = gcd(a, b)` from two inequalities, and concludes `not c ≤ c − δ` from
`δ > 0`.

### The procedure

Negate the claim, add it to the cited facts, and show the set has no solution
over an ordered field. Concretely this is Fourier–Motzkin elimination over the
atoms, with three additions:

- **A negation is a fact, not a special case.** `not (a ≤ b)` is `b < a` and
  `not (a = b)` is `a < b or b < a`. Eight of the 25 steps do nothing but move
  between a relation and the negation of its complement, a cost the
  literal-negation rule of `SYNTAX.md` imposes on every proof that reaches a
  contradiction through an order relation.
- **A disequality splits.** Using `not (e = 0)` means solving twice, once with
  `e < 0` and once with `0 < e`, and both must fail. Two steps need this, each
  turning `≤` together with `≠` into `<`.
- **An equation is two inequalities.** This is what lets the method use a cited
  equation, which four steps of the triangle inequality do when they conclude
  `x ≤ |x|` from `|x| = x`.

### Refusals

- **Anything non-linear.** Multiplying two atoms, or dividing by one. No step
  in the corpus needs this, which is what makes the linear specification
  sufficient rather than merely convenient.
- **Anything about what an atom means.** An exponent law, the definition of
  absolute value, the value of a function. Those are cited items.
- **Strictness it was not given.** From `a ≤ b` alone it will not conclude
  `a < b`; the disequality must be among the cited facts.

### Hypotheses

Every atom must be a real number. This is a hypothesis of the method exactly as
`q ≠ 0` is a hypothesis of a division, so by the dull-fact rule of `READERS.md`
it is discharged by a cited line or written as a requires line. `READERS.md`
already names this kind of fact, "that a product of integers is an integer",
among its examples of dull facts.

The corpus complies. Writing the specification showed that many steps could not
have stated their hypotheses at all, because the facts had no item behind them:
nothing said the absolute value of a real number is real, nothing carried an
integer, a natural or a natural-with-zero into the reals, and nothing said a
power is real. `thm:abs-real`, `thm:int-real`, `thm:nat-real`,
`thm:nat0-real` and `thm:power-real` were added for that, and the sweep then
wrote 97 membership lines across the 42 steps citing this method or `algebra`.

Two shapes are worth knowing. Most are a bare citation of a fact already on the
page, as step 17.9 of the intermediate value proof is with `requires c ∈ ℝ:
from 8`. The heaviest is step 2 of the Bezout lemma, which has ten atoms and so
carries ten.

Every natural bridge is direct rather than through ℤ, for a reason the rule
forces: a requires line carries one citation, so a two-step chain would make
every natural atom need a numbered step of its own.

This is the answer to the "Not settled" item in `SYNTAX.md` about whether
`algebra` and `inequalities` carry their membership hypotheses. They do. If
forty lines is judged too high a price, the thing to change is the dull-fact
rule in `READERS.md`, not this method, because the same argument would exempt
every other dull fact in the corpus.

### Boundary with substitute

Four steps look like rewriting: `x ≤ |x|` from `|x| = x`. They are not, and the
two methods do not overlap.

- `substitute` needs a line to rewrite and produces that line with one term
  replaced. It is syntactic.
- `inequalities` needs no such line. It uses the equation as a linear fact
  among others. Here there is no earlier line stating `x ≤ x`, so `substitute`
  has nothing to act on.

The rule: if the claim is an earlier claim with a term replaced, it is
`substitute`. If the claim follows numerically from facts including an
equation, it is `inequalities`.

### Expansion

The target families in set.mm are the transitivity and ordering lemmas below.
`lelttr`, `ltletr`, `letr`, `lttr` for chaining; `ltnle`, `lenlt`, `ltne`,
`leloe` for the negation and disequality moves; `leadd1`, `ltadd1`, `subge0`,
`ltsub23` and their relatives for rearrangement; `le2add` and `lt2add` for
adding two inequalities; `letri3` for antisymmetry.

Elimination over a fixed set of atoms terminates, so the expansion is total,
which decision 5 of `GOALS.md` requires. Its size grows with the number of
atoms and cited facts, both of which are small: the largest step in the corpus
has four atoms and two cited facts.

---

## algebra

`algebra` decides **equality of rational expressions over a field**. It carries
17 of the 61 closure steps, second to `inequalities`, and differs from it in
two ways: it is not restricted to linear expressions, and it knows nothing
about order.

### Atoms

An atom is a maximal subterm not built from numerals, `+`, `−`, `·`, `/`, and
powers **with a numeral exponent**.

The exponent rule is the whole of the boundary the pilots argued about. In
`(2k + 1)² = 4k² + 4k + 1` the exponent is 2, so the square is expanded and the
only atom is `k`. In `2^k + 2^k = 2^k·2` the exponent is a variable, so `2^k`
is an atom and the step is only `x + x = x·2`. In
`(1 − a^(k + 1))/(1 − a) + a^(k + 1)` the atoms are `a` and `a^(k + 1)`, and
the method cannot connect them. That is why `thm:exponent-step` exists and why
the subsets proof was wrong to fold it in.

### Facts in

Each line named in `from` supplies its claim as an equation or a disequality
between rational expressions. Lines of several sentences supply each sentence
of that shape and are ignored for the rest.

### Fact out

An equation, or a disequality.

### The procedure

For an equation `L = R`, write each cited equation as `lᵢ − rᵢ = 0`. The claim
holds when `L − R` lies in the ideal generated by the `lᵢ − rᵢ` over the
rational functions in the atoms: that is, when

```
L − R  =  Σ pᵢ · (lᵢ − rᵢ)
```

for polynomials `pᵢ`. With no cited equations this is the ordinary test that
`L − R` normalises to zero, which is twelve of the seventeen steps. The
heaviest case is Bezout's step 2, which takes three cited equations with
coefficients −1, 1 and −q, and is the only step in the corpus whose
coefficients are not constants.

For a disequality `e ≠ 0`, the claim holds when `e` is a nonzero rational
multiple of some cited `d ≠ 0` after normalisation. Step 1 of the geometric
series is the only use: `1 − a` is `−1` times `a − 1`, and the cited fact is
`a ≠ 1`. **This answers the open item in `CLOSURE.md`: `algebra` may prove a
disequality, but only this narrowly.** It may not, for instance, conclude
`a² ≠ 0` from `a ≠ 0`, which needs a field to have no zero divisors and is a
fact about the field rather than an identity.

### Refusals

- **Anything about what an atom means.** Exponent laws, function values,
  absolute value, factorial. Those are cited items.
- **Dividing by anything not known to be nonzero.** Every denominator must
  appear among the supplied nonzero facts.
- **Order relations.** Those are `inequalities`.
- **A disequality that is not a multiple of a cited one.**

### Hypotheses

Two kinds, and the corpus is complete on one and silent on the other.

Every denominator is nonzero. Five steps divide, and all five write the
condition as a requires line. This was the last of the three disagreements
reconciled, and it now holds throughout.

Every atom is a real number, as for `inequalities`, and none of the seventeen
steps says so.

### Expansion

set.mm's ring and field lemmas are over ℂ, so the expansion carries the atoms
from ℝ to ℂ itself and the text never mentions ℂ, which is what `READERS.md`
requires of it. The families are `addcom`, `addass`, `mulcom`, `mulass`,
`adddi` for normalisation; `mulcl`, `addcl`, `subcl`, `divcl` for closure;
`divcan`, `divmul`, `divass` for the divisions; and `subeq0` for the
disequality case.

Ideal membership over a fixed set of atoms is decidable, so the expansion is
total. A Gröbner basis is the general method; the corpus never needs it, since
every step is either a normalisation with no cited equation or a combination
with coefficients of degree at most one.

Five steps are written out in `elaboration/`, and `ELABORATION.md` measures
them: 167 to 945 proof tokens each, the three normalisations cheaper than the
two that take a cited equation. Each follows one order — carry the atoms into
ℂ, apply the structural lemma the shape calls for, then reduce the numerals —
and none of them searched. The lemmas they actually used are `binom2`,
`sqmul`, `sqdiv`, `mulass`, `adddi`, `mulcom`, `mulrid`, `mulcand` and
`divmuld`, with `sqcl` and `mulcld` for closure and `sq1`, `sq2` and `2t2e4`
for the numerals. That order is fixed for those shapes only; a coefficient
that is not constant, as in Bezout's step 2, has not been written.

---

## arithmetic

`arithmetic` decides **closed numeral facts**. Counted by step justifications
it is the smallest of the four, at three. Counted by use it is not: eighteen
more uses justify a requires line, which makes it the most common terminator
of a dull fact in the corpus.

| what the claim is | uses |
|---|---|
| membership of a numeral in a number system | 13 |
| a value, as 1 = 1(1 + 1)/2 | 3 |
| an order relation, as 2 ≥ 0 | 3 |
| a disequality, as 2 ≠ 0 | 2 |

### Facts in

None. `arithmetic` takes no `from` list and never has. It is the only method
that cites nothing.

### Fact out

A relation between **closed numeral expressions**, where a closed numeral
expression is built from decimal numerals by `+`, `−`, `·`, `/` and powers,
with every operand closed. The relation is `=`, `≠`, `<`, `≤`, `>`, `≥`, or
membership of ℕ, ℕ₀, ℤ, ℚ or ℝ.

### The procedure

Evaluate each side to a rational in lowest terms and decide the relation. For a
membership, evaluate and test the value: a rational is in ℤ when its
denominator is 1, in ℕ when it is also positive, in ℕ₀ when it is also
non-negative, and in ℚ and ℝ always.

### Refusals

- **Anything containing a variable.** This is the line against `algebra`, and
  it is not a formality: `a^(0 + 1) = a` was once justified this way, and
  refusing it exposed that the claim smuggled in an exponent law. The geometric
  series now pays four steps for that one fact.
- **Anything that does not evaluate to a rational.** `√2 ∈ ℝ` is not
  arithmetic, and the corpus does not treat it as such; it cites `def:sqrt`.

### Hypotheses

None, and that is the point of it. Requires lines do not nest, so whatever
justifies one must need nothing further. `arithmetic` is where that recursion
stops, which is why thirteen of its twenty-one uses are memberships discharging
somebody else's hypothesis.

### Boundary with algebra

On a claim with no variables both would succeed, since `algebra` normalising
`1 − 1(1 + 1)/2` to zero decides the same fact. The text uses `arithmetic`
there, and the rule is that a claim with no atom cites `arithmetic`. A checker
can enforce that once it can tell an atom from a numeral, which needs the
formula grammar.

### Expansion

set.mm's numeral lemmas: `2re`, `2z`, `0z`, `1z`, `1nn`, `2pos`, `2ne0`,
`1lt2` for the small cases in this corpus, and the `deccl` and `decadd`
families for numerals of more than one digit. Evaluating a closed expression
terminates, so the expansion is total and its size is bounded by the numerals
in the claim.

---

## join

`join` decides nothing. It puts together what the cited lines already say.

### Facts in, fact out, procedure

Each cited line supplies its sentences. The claim must be exactly those
sentences, in any order. With one cited line the claim is that line, which is
the case where a `cases` part has to end in the block's common formula and the
part's assumption already is it.

There is no procedure beyond matching. A reader checks that every sentence of
the claim appears among the cited lines and that nothing else does.

### Refusals

Any inference. If the claim says something the cited lines do not already say,
it is not a `join`, and the step needs a theorem or another method.

### Hypotheses

None.

### Expansion

`jca` for the joining, together with the projection lemmas wherever a cited
line contributes one of several sentences. Matching terminates.

### Why this is not called `lines`

It was, until it was specified, and the name is the reason the specification
was needed. Of the fourteen methods, five are named for what you do, three for
a body of knowledge, four for the shape of the argument, and one for its
arguments. The last was this one, because the entry in `READERS.md` that it
grew from is "by ⟨earlier line⟩ and ⟨earlier line⟩", a form rather than a name,
so there was nothing in it to take a name from.

A method named for its inputs makes no claim about what it does, so nothing
resisted when four unrelated jobs collected under it: joining, eliminating a
double negation, a disjunctive syllogism, and restating a case assumption. The
other thirteen names would each have refused something, as `algebra` refused
the exponent law once its boundary was written down.

### Which propositional moves get a pointer

A move needs a cited theorem when it is a choice among logics. It does not when
it is the meaning of a connective.

Joining two facts with "and" is what "and" means, and Reader A can check it
having been told nothing. Eliminating a double negation is the step
intuitionistic logic refuses, so a text that takes it is committing to
something and should say so. Disjunctive syllogism goes with it, and the √2
pilot had already asked for it to be tested on a real reader rather than
assumed.

That criterion also accounts for the two logical items the database already
had, `thm:excluded-middle` and `thm:from-contradiction`, which is the sign that
it was the rule operating implicitly all along. The three moves that left
`join` are now `thm:double-negation`, cited twice, and
`thm:disjunctive-syllogism`, cited once.

---

## contradiction

`contradiction` is the first block method specified here. Its inputs are not
cited lines but the block itself: the supposition it opens with, and the last
step inside it.

### Facts in

The block's supposition, which asserts nothing outside the block, and the
block's last step, whose claim is two sentences, one the negation of the other.

### Fact out

The step's claim.

### The procedure

Compare the supposition with the claim, as trees. Exactly one of two things
holds, and which one decides the expansion:

- the supposition is the claim with a negation in front, which is reductio;
- the claim is the supposition with a negation in front, which is how a
  negation is proved directly.

They cannot both hold, because no formula is its own double negation, so the
reading is never in doubt. A folded negation counts as a negation: the
`negates` line of a notation record makes "n is not odd" the same tree as
"not (n is odd)", so a block may claim either spelling and suppose the other.

Then check that the last step closes: two sentences, one the negation of the
other by the same comparison.

### Refusals

A supposition that is neither the claim negated nor the thing the claim
negates. The two shapes above are the whole of what the method accepts, and a
step whose supposition is merely the opposite in spirit fails to elaborate
rather than being waved through.

A last step that is not a formula and its negation. Two sentences that
contradict each other in meaning but not in form are not a closing pair, and
the step that reconciles them belongs inside the block.

Rewriting the supposition. Where a proof needs the supposition in another form,
as `p ≤ n` for "not p > n", that is a step inside the block citing whatever
justifies it, not something the method does on the way in.

### Hypotheses

None. The method is propositional and asks nothing of the terms.

### Expansion

Both shapes target set.mm's `pm2.65`, which is negation introduction: from
`φ → ψ` and `φ → ¬ψ` conclude `¬φ`. The block's supposition is the antecedent
and its last two sentences are the two consequents.

That is the whole expansion when the claim is a negation. When the claim is
positive the expansion needs `notnotr` on top of it, and that is the classical
step. So the logic each block depends on falls out of which shape it is, rather
than being something the text has to announce. Of the corpus's seven blocks,
five are reductio and two prove a negation directly.

### Why the method accepts two shapes

`db/methods.db` used to say the block assumes "not C" written literally, and
five of the seven blocks do exactly that, two of them writing a doubled
negation and stripping it with `thm:double-negation` in the next line. The
other two suppose the thing the claim negates.

Both are correct, and forcing either one on the other costs something real.
Requiring the literal negation everywhere would put a doubled negation and a
cited classical step into two proofs that need neither, and the note on
`thm:double-negation` says citing it is the text saying which logic it is in,
which is worth nothing if it appears where the logic is not classical.
Requiring the direct form everywhere would rewrite the other two and remove a
step from each. Accepting both changes no proof in the corpus, and the
expansion still says exactly where the classical step is.

---

## What specifying both larger methods cost the corpus

`READERS.md` settles that membership in a number system is a written dull fact
and merits no exception. Applying that to both methods is the largest single
change the corpus has taken.

| | |
|---|---|
| steps citing `algebra` or `inequalities` | 42 |
| membership requires lines written | 97 |
| requires lines in the corpus, before and after | 38 → 139 |
| database items added to make them writable | 5 |

Five items were missing: `thm:abs-real`, `thm:int-real`, `thm:nat-real`,
`thm:nat0-real` and `thm:power-real`. None of them is deep, and none had been
noticed in three passes over the corpus, because nothing had yet had to say
what a method required of its terms.

Three steps could not be reached by a requires line at all and needed numbered
steps instead. The geometric series now states `k + 1 ∈ ℕ₀` as a step, since
`thm:power-real` needs it and it had only ever been a requires line. The
intermediate value proof now states `b ∈ [a, b]` and then `f(b) ∈ ℝ`, neither
of which the proof had ever established, although it used `f(b)` freely.
