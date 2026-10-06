# Specifications of the methods

`corpus/db/methods.records` says what a reader checks when a step cites a method.
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

Six methods are specified below: the four closure methods (`inequalities`,
`algebra`, `arithmetic`, `membership`), `join`, and `contradiction`. The rest
are not yet: the citation form, the block methods `fix`, `cases` and
`induction`, and `substitute`, `instantiate`, `obtain` and `exhibit`. None is
a decision procedure, so each should be shorter than the closure methods
were. What each does is in `SYNTAX.md`, and what the elaborator builds for it
in `ELABORATION.md`.

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
A numeral divided by a term that is not one is that numeral times the term's
reciprocal, and the reciprocal is the atom: `2/(n + 1)` is `2 · (1/(n + 1))`,
the same atom `1/(n + 1)` a line bounding it names. It is the rule for `/` by
a numeral taken one step further, and it is what lets `1/(n + 1) ≤ 1/N` bound
`2/(n + 1)` without a line saying one is twice the other.

So in `f(x₁) − f(c) ≤ |f(x₁) − f(c)|` the atoms are `f(x₁)`, `f(c)` and
`|f(x₁) − f(c)|`, three of them, and the last is an atom even though its own
inside contains the first two. The method never looks inside an atom and knows
nothing about what it means. That `|y|` is at least `y` is not available to it;
that fact reaches a step as a cited line, which is what
`thm:proofs/triangle-inequality/abs-bounds` is for.

A defined name is an atom, unless the step writes what the name names as
well: then each defined name in its claim and its cited lines whose define
the step cites is read as what it names, and every sum as one sum whatever
its letter. Cauchy–Schwarz's `requires A > 0: inequalities, from D1, C3`
claims A > 0 from 0 < Σ(k = 1 to n) a(k)², with A defined as that sum,
citing the define, and the two are one atom. A step that
writes a name without what it names reads the name as one atom, so it rests
on nothing it does not cite. Two sums that
differ only in their letter are one atom too, and a line saying one of them
is real says it of the other.

### Facts in

Each line named in `from` supplies its claim as a linear fact. A fact is one of

```
e = 0        e ≤ 0        e < 0        not (e = 0)        not (e ≤ 0)
```

after moving everything to one side, where `e` is a linear combination of atoms
with rational coefficients. A cited line of several sentences supplies each
sentence that has this shape and is ignored for the rest, so citing a line that
also states a membership or a quantified sentence is not an error.

A membership supplies the bounds it implies (`SYNTAX.md`): a line saying
k ∈ ℕ supplies k ≥ 1 and k ≠ 0, and one saying k ∈ ℕ₀ supplies k ≥ 0. It
also discharges the hypothesis that k is real. So `requires k ≠ 0:
inequalities, from K1` needs nothing but `let k ∈ ℕ (K1)`. A membership that
is one part of a cited line discharges it as a line of its own would: a line
saying `a(k) ∈ ℝ and b(k) ∈ ℝ and a(k) < b(k)` says a(k) and b(k) are real.

A **closed numeral fact is available without being cited**. The combination
that reaches a claim may need one — `n! ≥ 1` gives `n! + 1 > 1`, and the
strictness comes from `1 > 0`, which the step names nowhere. Those facts are
`arithmetic`'s, and the reader writing that step uses this one without writing
it down, as anyone would. Making the text say `requires 1 > 0` to justify
`n! + 1 > 1` would be the readable layer serving the prover rather than the
reader, which `GOALS.md` is against; so the method takes them, and this
sentence is what stops that being a quiet borrowing across the boundary
`arithmetic` otherwise keeps.

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

- **Anything non-linear.** Multiplying two atoms, or dividing an atom by
  one. No step in the corpus needs this, which is what makes the linear
  specification sufficient rather than merely convenient.
- **Anything about what an atom means.** An exponent law, the definition of
  absolute value, the value of a function. Those are cited items.
- **Strictness it was not given.** From `a ≤ b` alone it will not conclude
  `a < b`; the disequality must be among the cited facts.

### Hypotheses

Every atom must be a real number. This is a hypothesis of the method exactly as
`q ≠ 0` is a hypothesis of a division, so by the dull-fact rule of `READERS.md`
it is discharged by a cited line or written as a requires line.

A reciprocal atom brings its divisor's hypothesis with it: `1/(n + 1)` is a
real number when `n + 1` is one and is not zero, and both are the page's to
write. Its membership is then built from those as a sum's is from its
parts', and no line says that `1/(n + 1)` is real. A divisor that is a numeral
other than zero needs no line: that 2 is not zero is a closed numeral fact,
so `δ/2` is real because `δ` is.

An atom is one of the claim or of the facts the step combines — not of every
sentence a cited line says. Line 1 of `least-combination-divides` says
`0 ≤ r` and `r < d` among five things, and step 3.1's `requires 0 < r:
inequalities, from 1, S` takes `0 < r` from the first of them and the
supposition `r ≠ 0`; d is in none of what it combines,
so `d ∈ ℝ` is not one of its hypotheses and is not written. A dull fact is one
that discharges a hypothesis, and one that discharges nothing is a line doing
no work. `READERS.md`
already names this kind of fact, "that a product of integers is an integer",
among its examples of dull facts.

The corpus complies. Writing the specification showed that many steps could not
have stated their hypotheses at all, because the facts had no item behind them:
nothing said the absolute value of a real number is real, nothing carried an
integer, a natural or a natural-with-zero into the reals, and nothing said a
power is real. `mun:stdlib/numbers/abs-real`, `mun:stdlib/numbers/int-real`, `mun:stdlib/numbers/nat-real`,
`mun:stdlib/numbers/nat0-real` and `mun:stdlib/numbers/power-real` were added for that, and the sweep then
wrote 97 membership lines across the 42 steps citing this method or `algebra`.

Two shapes are worth knowing. Most are a bare citation of a fact already on the
page, as step 16.7 of the intermediate value proof is with `requires c ∈ ℝ:
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

### Boundary with algebra, over a disequality

The name misleads, and the misreading costs an afternoon each time. Read
literally an "inequality" is a thing that is not equal, so `≠` looks as
though it must be this method's business. It is not: `inequalities` is about
the **ordering** of numbers. A `≠` reaches it only because the order gives
one a meaning — `a ≠ b` is `a < b or b < a`, which is exactly why using one
splits the refutation.

So a disequality belongs to `inequalities` when the order is what settles it,
and to `algebra` when no order is involved. The corpus has one of each and
they are not alike:

- A requires line of Bezout's step 3.1 turns `0 ≤ r` together with `r ≠ 0`
  into `0 < r`. Every part of that is the order, and the claim is an order
  relation, which `algebra` refuses.
- The geometric series' `requires 1 − a ≠ 0: algebra, from H2` concludes
  `1 − a ≠ 0` from `a ≠ 1`. That holds in any field and has no order in it. Reaching it through trichotomy would
  prove an order-free fact by the order, which is more than the fact needs.

The rule: a disequality whose argument runs through `<` or `≤` is
`inequalities`; one that is a rearrangement of a cited disequality is
`algebra`, as narrowly as the `algebra` section states.

`inequalities` takes a disequality only from a line it cites, and takes it
both ways, below and above: Bezout's 3.1 cites the supposition `r ≠ 0` and
`0 ≤ r`, and the case below contradicts the second. From a requires line
above the one being proved it takes orders and equations, and not two terms
differing: a disequality written above is there for a divisor, which
`membership` and `algebra` ask. Nor does it take one a membership only
implies: `k ∈ ℕ` says k ≠ 0 for a divisor, and the order it says, k ≥ 1, is
what `inequalities` takes from it. The checker and the elaborator read which
lines are above from one place (`Step::requires_above`), and neither counts
a disequality above as asked for by an `inequalities` line below it.

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

Four steps are written out, in `corpus/elaboration/abs-bounds.mm`, and all four are
easy. Two turn an equation into a non-strict inequality with `leid` and
`breqtrd`; two chain through zero with `le0neg1` or `le0neg2`, then `letrd`,
then `breqtrd`. They follow the same order `algebra` does — atoms into ℝ, the
ordering lemma the shape calls for, then the rewrite — and none searched. What
they establish is the lemma order for those shapes. None of them needs the
elimination procedure above, so the method's hard half is still unwritten;
`intermediate-value` is where its heaviest steps are.

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
the method cannot connect them. That is why `mun:stdlib/numbers/exponent-step` exists and why
the subsets proof was wrong to fold it in.

**A finite sum is linear.** A sum over a range {a, …, b} is read through its
summand: each term of the summand, as a polynomial, is split into what is
free of the sum's letter and what holds it, and Σ(k) of the whole is the sum
of each free part times the sum of what holds k — Σ(k = 1 to n) (a(k)·t +
b(k))² is t²·Σa(k)² + 2t·Σa(k)·b(k) + Σb(k)², each of those three sums an
atom. A reader writes this as "by linearity of the sum", one step. Two sums
that differ only in their letter are one atom. A summand that divides, or
holds a sum of its own, or has a term free of the letter, leaves the sum one
atom.

A step reads its sums so when one of them, in its claim or a line it cites,
is linear in something: two parts or more, or a part with a factor free of
its letter. Otherwise each sum is one atom as written, as a reader takes Σ in
x·Σ + 0 = x·Σ. The test is on the text and decides the reading before
anything is proved; nothing is tried one way and then the other. Read as
linear, what the step combines is each part's free factor, whose membership
it writes, and what holds the letter is a number at each index by what the
summand is built from, as a sum's membership is.

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
`L − R` normalises to zero, which is twelve of the seventeen steps.

**At most one `pᵢ` has a letter in it.** The others are numbers: a step
adds and subtracts the equations it cites, scales them, and multiplies at
most one of them by a term. A step does one thing, and multiplying a second
equation by a term is a second thing, written as a step of its own and
joined to the first by a calculation, as `similar-triangles` does with its
two laws of sines (steps 9 to 11). Two steps in the corpus multiply one
equation: Bezout's lemma, step 2, which takes three cited equations with
coefficients −1, 1 and −q, and Pythagoras, step 19, which multiplies
|AD| + |DB| = |AB| by |AB|.

For a disequality `e ≠ 0`, the claim holds when `e` is a nonzero rational
multiple of some cited `d ≠ 0` after normalisation. The geometric series'
`requires 1 − a ≠ 0: algebra, from H2` is the only use: `1 − a` is `−1` times `a − 1`, and the cited fact is
`a ≠ 1`. **`algebra` may prove a disequality, but only this narrowly.** It may not, for instance, conclude
`a² ≠ 0` from `a ≠ 0`, which needs a field to have no zero divisors and is a
fact about the field rather than an identity.

### Refusals

- **Anything about what an atom means.** Exponent laws, function values,
  absolute value, factorial. Those are cited items.
- **Dividing by anything not known to be nonzero.** Every denominator must
  appear among the supplied nonzero facts.
- **Order relations.** Those are `inequalities`.
- **A disequality that is not a multiple of a cited one.**
- **Two cited equations each multiplied by a term.** That is two steps.

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

Six steps are written out in `corpus/elaboration/`, and `ELABORATION.md` measures
them. Five come from the three elaborated proofs; the sixth is step 2 of
`thm:proofs/bezout/least-combination-divides`, the only step in the corpus whose
coefficients are not constants, and it is in `corpus/elaboration/algebra.mm`.

Each follows one order — carry the atoms into ℂ, apply the structural lemma
the shape calls for, then reduce the numerals — and none of them searched,
including the one with three cited equations and coefficients −1, 1 and −q.
The lemmas they used are `binom2`, `sqmul`, `sqdiv`, `mulass`, `mul12`,
`adddi`, `subdi`, `addsub4`, `subadd`, `mulcom`, `mulrid`, `mulcand` and
`divmuld`, with `sqcl`, `mulcld`, `addcld` and `subcld` for closure and `sq1`,
`sq2` and `2t2e4` for the numerals.

What an expansion costs is set by how many atoms it must place in ℂ rather
than by how hard the identity is. The Bezout step has ten atoms and is three
times the size of the others once written compressed; in normal format it
looks twenty times larger, because that ten-conjunct antecedent is rewritten
into every line.

---

## arithmetic

`arithmetic` decides **closed numeral facts**. No step of the corpus is
justified by it: a fact with no letter in it gives a reader nothing to check
but working it out, so it names `arithmetic` where it is used rather than
standing as a step of its own (`SYNTAX.md`). It justifies a requires line,
which makes it the most common terminator of a dull fact in the corpus; it is
the source of a `substitute`, `substitute 0 + 1 = 1 (arithmetic)`; and it is
the reason on a chain line of numerals alone, `= 1(1 + 1)/2    arithmetic`.
In each place the same procedure and the same refusals apply, and the
checker refuses the method for a fact with a letter in it.

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
  arithmetic, and the corpus does not treat it as such; it cites `mun:stdlib/numbers/sqrt`.
  Nor is `4^(1/2)`: a power is taken only with a whole exponent, and no root
  is taken, because a fractional power is in general irrational and could
  only be held as a float, and a float may be inexact, infinite or zero
  without saying so. Every value is an exact fraction.
- **A division by zero,** `3/0` or `0^(−1)`. set.mm gives `A / 0` a
  meaning, a class nobody writes, and a claim about it is not one a reader
  can check.
- **A number too large to work out.** The arithmetic is on integers of any
  size, which do not overflow, so a claim like `9^(9^9)` would take time and
  memory without end. The size
  of a power is estimated before it is computed, and anything past ten
  thousand bits is refused.
- **Anything false.** The claim is worked out before a proof is attempted,
  so a false one is reported as false.

`arithmetic` never takes a step as stated. What it cannot prove is reported:
as false, as one of the refusals above, or, where it is true and past what
the expansion below can show, with the instruction to cite a theorem that
states it.

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
`1lt2` for a digit. A numeral of more than one digit is set.mm's decimal
`; A B`, A the number its digits before the last make and B the last digit,
and the methods read it as its value wherever they read a digit. Its
membership of a number system is built from its digits by `deccl` and
carried on by `nn0zi`, `nn0rei` or `nn0cni`.

A sum, product or order of whole numbers of any length is worked the way it
is worked on paper (`elab/numerals.rs`): the last digits from set.mm's
tables of digits (`9p3e12`, `6t3e18`, `3lt7`), the digits before them by the
same procedure, and a carry where the last digits pass nine (`decadd`,
`decaddc`, `decmul1`, `decmul1c`, `declt`, `decltc`). The tables state a
result past nine only with the larger digit first, and the other order is
turned round by `addcomi` or `mulcomi`. So 10 − 1 = 9 is proved, and so is
the −6·3 = −18 a cut into thirds asks of `inequalities`.

---

## membership

`requires for all k ∈ ℕ, 1/T(k) ∈ ℝ: membership` — a term is in a number
system because its parts are. The method states as a step's claim what `algebra` and
`inequalities` already work out for every atom they touch, and it exists so
that a dull fact of this kind is one line rather than a climb up the term one
library item at a time.

### Facts in

The step's requires lines and the lines it cites, read for what they say
(`SYNTAX.md`: `let k ∈ ℕ` also says k ∈ ℝ and k ≠ 0). A defined name is read
as its rule, T(k) as k(k + 1)/2, where the step cites its define, as it is
wherever a formula is compared: `requires Σ(k = 1 to n) 1/T(k) ∈ ℝ:
membership, from D1`.

A cited equation with the term on one side says the term is in whatever the
other side is in, as a reader takes a(0) = 0 to say a(0) is a number:
`a(0) ∈ ℝ: membership, from 1`, where line 1 says a(0) = 0, and
`a(k + 1) ∈ ℝ: membership, from 4.1, IH`, where 4.1 gives a(k + 1) as a
term in a(k) and b(k) and the induction hypothesis says those are real.
Only this method reads an equation so. Every other method takes an atom's
membership from a line saying it, so that a membership a step uses is one
the page shows.

### Fact out

`t ∈ S`, with S a number system; or "for all k ∈ X, t ∈ S", which is
proved as a `fix` block would prove it: k is taken in X, what that
membership says is laid beside the other facts in, and t ∈ S is proved of
it.

### The procedure

The term is walked by the operation at its head, as `algebra` walks it:

- a sum, difference, product or power is in S when its parts are
  (`readdcld`, `remulcld` and the rest of the closure table);
- a negation is in S when what it negates is, for S that holds negatives;
- a quotient is in ℝ or ℂ when its parts are and its divisor is not zero,
  which a cited line says by saying it, or by saying the divisor is above
  zero or below it (`gt0ne0d`, `lt0ne0d`): −B/A ∈ ℝ from A > 0;
- a remainder a mod b is in ℕ₀, and so in ℤ, ℝ and ℂ, when a is in ℤ and
  b in ℕ (`zmodcl`): (t + 1) mod 10 ∈ ℤ from t ∈ ℤ, the divisor a numeral
  asking nothing, as a binomial coefficient C(n, k) is in ℕ₀ when n is in ℕ₀
  and k in ℤ (`bccl`);
- a sum over a range {a, …, b} is in ℝ or ℂ when its term is, for each index
  in the range (`fsumrecl`, `fsumcl`); the index is in ℕ where the range
  starts at 1, by the table of `SYNTAX.md`, so Σ(k = 1 to n) 1/T(k) ∈ ℝ asks
  the page for nothing;
- anything else is an atom, and its membership is a line the step cites or
  writes, carried to S by at most one lemma (`nnre`, `zcn` and the rest), or
  a cited equation with the atom on one side, the other side's membership
  read the same way and carried across by `eqeltrd`.

A divisor is not zero when a line says so, when it is a numeral other than
zero, when it is built in ℕ (`nnne0`: k + 1 where k ∈ ℕ), or when it is a
product or quotient of parts that are not zero (`mulne0d`, `divne0d`).

### Refusals

- **A search.** Nothing is looked for beyond the parts' own lines; an atom
  nothing says is in S is refused, naming the atom.
- **A difference in ℕ or ℕ₀,** which the closure table does not hold, since
  a difference of whole numbers need not be whole.
- **Anything about what an atom is.** |x| ∈ ℝ is the item `abs-real`, not
  this method.

### Hypotheses

None beyond its facts in: a divisor's disequality and an atom's membership
are the lines the method reads, not conditions it asks of the step.

### Expansion

The closure lemmas the table names, `divcld` and `redivcld` for quotients,
`mulne0d` and `divne0d` for a divisor's disequality, and where the claim
names a define, the claim read as its rule and carried back by the equation
the define gives (`mpbid`).

## join

`join` decides nothing. It puts together what the cited lines already say.

### Facts in, fact out, procedure

Each cited line supplies its sentences. The claim must be exactly those
sentences, in any order. With one cited line the claim is that line. A `cases`
part whose assumption already is the block's common formula does not end on a
join of it: its assumption line says `, which is the claim`, and it has no
steps.

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

That criterion also accounts for the logical item the database already had,
`mun:stdlib/reasoning/excluded-middle`, which is the sign that it was the rule
operating implicitly all along. Disjunctive syllogism, which left `join`, is
`mun:stdlib/reasoning/disjunctive-syllogism`. A doubled negation is not
written at all: a contradiction block proving a negation supposes what the
negation denies.

---

## contradiction

`contradiction` is the first block method specified here. Its inputs are not
cited lines but the block itself: the supposition it opens with, and the last
step inside it.

### Facts in

The block's supposition, which asserts nothing outside the block, and the
block's last step, which reaches the opposite of an earlier line and names it,
`contradicting 3.6`.

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

Then check that the last step closes: its claim and the line it names, or one
sentence of that line, are a formula and that formula negated, by the same
comparison.

### Refusals

A supposition that is neither the claim negated nor the thing the claim
negates. The two shapes above are the whole of what the method accepts, and a
step whose supposition is merely the opposite in spirit fails to elaborate
rather than being waved through.

A last step that names no line, or one whose claim is not that line negated
nor negated by it. Two lines that contradict each other in meaning but not in
form are not a closing pair, and the step that reconciles them belongs inside
the block.

Rewriting the supposition. Where a proof needs the supposition in another form,
as `p ≤ n` for "not p > n", that is a step inside the block citing whatever
justifies it, not something the method does on the way in.

### Hypotheses

None. The method is propositional and asks nothing of the terms.

### Expansion

Both shapes target set.mm's `pm2.65`, which is negation introduction: from
`φ → ψ` and `φ → ¬ψ` conclude `¬φ`. The block's supposition is the antecedent,
and its last step and the line that step contradicts are the two consequents.

That is the whole expansion when the claim is a negation. When the claim is
positive the expansion needs `notnotr` on top of it, and that is the classical
step. So the logic each block depends on falls out of which shape it is, rather
than being something the text has to announce. Of the corpus's twelve blocks,
three are reductio and nine prove a negation directly.

### Why the method accepts two shapes

A claim that is not a negation can only be proved by reductio, supposing its
negation. A claim that is a negation could be proved either way, but supposing
its negation would write a doubled negation, "suppose not not c = b", and then
need a step to strip it. So a negation is proved by supposing what it denies,
"suppose c = b", which is how a textbook writes it and needs no classical
step; `LINTER.md` prefers that form. Both shapes stay in the method because
each is the only way to prove its kind of claim.

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

Five items were missing: `mun:stdlib/numbers/abs-real`, `mun:stdlib/numbers/int-real`, `mun:stdlib/numbers/nat-real`,
`mun:stdlib/numbers/nat0-real` and `mun:stdlib/numbers/power-real`. None of them is deep, and none had been
noticed in three passes over the corpus, because nothing had yet had to say
what a method required of its terms.

Three steps could not be reached by a requires line at all and needed numbered
steps instead. The geometric series now states `k + 1 ∈ ℕ₀` as a step, since
`mun:stdlib/numbers/power-real` needs it and it had only ever been a requires line. The
intermediate value proof now states `b ∈ [a, b]` and then `f(b) ∈ ℝ`, neither
of which the proof had ever established, although it used `f(b)` freely.
