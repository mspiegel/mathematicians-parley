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

**The corpus does not comply.** The 25 steps have about fifty atoms between
them, and while some memberships ride along in a cited line of several
sentences, as `x₁ ∈ ℝ` does in step 17.6 of the intermediate value proof, most
are not stated. Bringing the corpus into line means roughly forty new requires
lines, every one of them mechanically collapsible in a viewer, which is what
the collapse rule was designed for.

Writing this specification also showed that fourteen of the twenty-five steps
could not have stated their hypotheses at all, because two facts had no item
behind them. Nothing said the absolute value of a real number is real, which
eight steps need, and nothing carried an integer into the reals, which the six
steps of the Bezout and prime proofs need since they reason over ℤ while the
method works over an ordered field. `thm:abs-real` and `thm:int-real` are now
in `db/items.db` and no proof cites either yet. The largest single case is step
5.2 of the triangle inequality, which has four atoms and today has two lines;
under this rule it has six, two of them citing `thm:abs-real`.

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

---

## What specifying both methods costs the corpus

The membership rule is the same for both, and applying it is a larger job than
it looked when only `inequalities` was specified.

| | atoms needing a membership |
|---|---|
| the 25 inequalities steps | about 54 |
| the 17 algebra steps | about 33 |

Some are already supplied by a cited line and cost nothing. The rest are
requires lines, except where the fact is two citations deep, and there the rule
that a requires line carries exactly one citation bites. A variable introduced
by `let a ∈ ℕ` reaches ℝ through `thm:nat-int` and then `thm:int-real`, which
is two steps, so it cannot be a requires line at all. It has to be a numbered
step. The Bezout proof alone would gain about ten of those, and its step 2,
which has ten atoms, would carry ten requires lines on top.

That is a different order of cost from the forty lines estimated when
`inequalities` stood alone, and it is worth deciding before the sweep rather
than during it. The alternative is to treat membership in a number system as
discharged by the method rather than written: unlike `q ≠ 0`, which is a real
side condition that can fail, membership here never fails, carries no
information a reader does not already have from the `let` line, and would be
the only dull fact in the corpus that routinely needs a numbered step of its
own. Changing that is a change to the dull-fact rule in `READERS.md`, and it
should be made there or not at all.
