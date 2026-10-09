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

Seven methods are specified below: the four closure methods (`inequalities`,
`algebra`, `arithmetic`, `membership`), `inspection`, `join`, and
`contradiction`. The rest
are not yet: the citation form, the block methods `proof`, `cases`,
`both directions` and `induction`, and `substitute`, `instantiate`, `obtain`
and `exhibit`. None is
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
numerals and the operations `+`, `−`, `·` by a numeral, and `/` by a numeral;
a whole power of a numeral, 365^23, is a numeral here, and the proof scales
by it as exactly as by 2.
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
k ∈ ℕ supplies k ≥ 1 and k ≠ 0, and one saying k ∈ ℕ₀ supplies k ≥ 0. So
`requires k ≠ 0: inequalities, from K1` needs nothing but `let k ∈ ℕ (K1)`.
That k is real the step neither cites nor writes: it is said once, where k
is introduced (`SYNTAX.md`, a membership is said once). A membership that
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
`q ≠ 0` is a hypothesis of a division. Where the atom is a numeral, a letter,
or built from those by +, −, ·, a power to a numeral and /, the page says it
once, where the letters are introduced (`READERS.md`), and the step writes
nothing; any other atom, a function's value or a sum, is discharged by a
cited line or written as a requires line.

A reciprocal atom brings its divisor's hypothesis with it: `1/(n + 1)` is a
real number when `n + 1` is one and is not zero. That `n + 1` is real is said
once, with n; that it is not zero is the page's to write. A divisor that is a
numeral other than zero needs no line: that 2 is not zero is a closed numeral
fact, so `δ/2` is real because `δ` is.

An atom is one of the claim or of the facts the step combines — not of every
sentence a cited line says. Line 1 of `least-combination-divides` says
`0 ≤ r` and `r < d` among five things, and step 3.1's `requires 0 < r:
inequalities, from 1, S` takes `0 < r` from the first of them and the
supposition `r ≠ 0`; d is in none of what it combines,
so `d ∈ ℝ` is not one of its hypotheses. A dull fact is one that discharges a
hypothesis, and one that discharges nothing is a line doing no work.

The memberships a step still writes are those the page does not say once:
the absolute value of a real number (`mun:stdlib/numbers/abs-real`), a power to
a letter (`mun:stdlib/numbers/power-real`), a function's value from its type, a
finite sum from its terms. Every natural bridge is direct rather than through
ℤ, for a reason the rule forces: a requires line carries one citation, so a
two-step chain would make every natural atom need a numbered step of its own.

This is the answer to the "Not settled" item in `SYNTAX.md` about whether
`algebra` and `inequalities` carry their membership hypotheses. They do, and
`READERS.md` says where each is said.

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

Two kinds.

Every denominator is nonzero, unless it is a numeral other than zero, and a
step that divides writes the condition or cites a line saying it.

Every atom is a real number, as for `inequalities`: said once where the atom
is a numeral, a letter or built from them, and otherwise written.

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

`arithmetic` decides **closed numeral facts**. A fact with no letter in it
gives a reader nothing to check but working it out, so it names `arithmetic`
where it is used rather than standing as a step of its own (`SYNTAX.md`). It
justifies a requires line; it is the source of a `substitute`, `substitute 0
+ 1 = 1 (arithmetic)`; and it is the reason on a chain line of numerals alone,
`= 1(1 + 1)/2    arithmetic`. It justifies a numbered step only where the
proof's shape asks a line there: an induction's base case, and a fact a
method takes only from a cited line. One step of the corpus is such, the
birthday problem's step 13.
In each place the same procedure and the same refusals apply, and the
checker refuses the method for a fact with a letter in it.

The requires lines of the corpus that cite it, counted 2026-10-09:

| what the claim is | requires lines |
|---|---|
| membership of a closed term in a number system | 1 |
| a word its record lets it decide, as 3 divides 10 − 1 | 1 |
| an order relation, as 2 ≥ 0 | 3 |
| a disequality, as 2 ≠ 0 | 4 |

A numeral's membership is not written at all (`READERS.md`, said once); the
one membership left is of a product over a range, ∏(k ∈ {0, …, 22}) (365 − k),
which is closed but not built from numerals by the operations the page says
once.

### Facts in

None. `arithmetic` takes no `from` list and never has. It is the only method
that cites nothing.

### Fact out

A relation between **closed numeral expressions**, where a closed numeral
expression is built from decimal numerals by `+`, `−`, `·`, `/`, powers and
`mod`, and by products over a range of numerals, ∏(k ∈ {0, …, 22}) (365 −
k), with every operand closed. `x mod n` is worked out where x is a whole
number and n one of at least 1: `10^0 mod 3 = 1`. `mod` is not one of the
operations arithmetic works out by its nature, and its notation record says
`decided arithmetic` (`DATABASE.md`); an operation whose record does not is
refused. The relation is `=`, `≠`, `<`, `≤`, `>`, `≥`, or
membership of ℕ, ℕ₀, ℤ, ℚ or ℝ.

Or a word whose record names `arithmetic` in its `decided` field
(`DATABASE.md`), said of closed numeral expressions, or its denial: `3
divides 10 − 1`, `5 is odd`, `not (2 divides 7)`, `10^0 ≡ 1 (mod 3)`. The
library's are `divides`, `even`, `odd` and `congruent-mod`. A word whose record does not name the method is
refused however plainly it holds, so what `arithmetic` decides can be read off
the records.

### The procedure

Evaluate each side to a rational in lowest terms and decide the relation; a
remainder `x mod n` is what is left of x after taking away the most whole
multiples of n it holds, so 10 mod 3 is 1. For a
membership, evaluate and test the value: a rational is in ℤ when its
denominator is 1, in ℕ when it is also positive, in ℕ₀ when it is also
non-negative, and in ℚ and ℝ always.

The four words are one relation to set.mm: "n is even" is 2 ∥ n, "n is
odd" is its denial, and a ≡ b (mod n) is n ∥ (a − b), as their notation
records' targets say. So d divides n is
decided by evaluating both, each a whole number with d ≥ 1 and n ≥ 0, and
dividing: it holds when the remainder is 0, and fails otherwise.

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
- **A word whose record does not name `arithmetic`.** "5 is prime" is
  refused, though it holds, until the record of `prime` says the method
  decides it and the method can.
- **A remainder outside the whole numbers,** `(−7) mod 3` or `7 mod 0`:
  set.mm gives each a value, and nothing in the corpus asks one.
- **A divisibility outside the whole numbers,** a divisor below 1 or a
  number below 0: `−2 divides 4` is not worked out. Nothing in the corpus
  asks one, and set.mm's lemma for the denial is stated for those.
- **Anything false.** The claim is worked out before a proof is attempted,
  so a false one is reported as false.

`arithmetic` never takes a step as stated. What it cannot prove is reported:
as false, as one of the refusals above, or, where it is true and past what
the expansion below can show, with the instruction to cite a theorem that
states it.

### Hypotheses

None, and that is the point of it. Requires lines do not nest, so whatever
justifies one must need nothing further. `arithmetic` is where that recursion
stops.

### Boundary with algebra and inequalities

On a claim of numerals alone `algebra` would succeed too, normalising
`1 − 1(1 + 1)/2` to zero, and so would `inequalities` on `not 2 ≤ 1`, from
the closed facts it takes uncited. Both combine what a step says of its
letters, and a claim with none gives a reader nothing to check but working it
out. So a claim whose every leaf is a numeral cites `arithmetic`, whatever
relation it states, and the checker refuses `algebra` or `inequalities` for
one, in a step or a requires line. A claim with no letter but a constant,
`1 + i·0 = 1`, is not numerals alone: `arithmetic` cannot work i out, and the
claim stays `algebra`'s.

Denials of an order are `arithmetic`'s with the rest: not a ≤ b is b < a, and
not a < b is b ≤ a, each turned by the law that says so (`ltnled`, `lenltd`).

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

An order whose sides are sums, differences, products and whole powers of
whole numbers, and products over a range of numerals,
2·∏(k ∈ {0, …, 22}) (365 − k) < 365^23, has each side worked to its numeral
first: a power is its base times one power less (`numexpp1`), a difference
is worked only where it is not negative (`subaddrii`), a product over a
range has its last factor taken off (`fprodp1`) down to its first alone
(`fprod1`), and each part is replaced by its value (`oveq12i`). A side that
divides is a fraction of two such values, and a whole number w on the other
side is w/1 (`div1i`): A/D < C/B is A·B < C·D (`lt2mul2div`), and
A/D ≤ C/B is that C/B < A/D does not hold (`lenlt`), so
(∏(k ∈ {0, …, 22}) (365 − k))/365^23 < 1/2 is decided by its cross
products. The order between the two numerals is proved digit by digit, and
`breq12i` carries it back to the sides as written. A membership of such a
term, ∏(k ∈ {0, …, 22}) (365 − k) ∈ ℝ, is its numeral's, carried back by
`eqeltrrd`. The numbers are held as big integers, so a side of sixty digits
is worked as exactly as a digit.

A remainder of whole numbers, x mod n with x = q·n + r and 0 ≤ r < n, is r
by `modcyc`, which takes the q·n away, and `modid`, which says a number below
n is its own remainder; where q is 0 `modid` alone says it.

A divisibility of whole numbers is proved at their values and carried back to
the terms as written by `breq12d`. That d divides n, with n = d·q, is
`dvdsmul1` at d and q, the product worked out (`breqtri`). That it does not,
with n = d·q + r and 0 < r < d, is `ndvdsi` from the quotient, the remainder
and the sum and order the numeral lemmas prove: 5 is odd because 2·2 + 1 = 5
and 1 < 2.

---

## membership

`requires for all k ∈ ℕ, 1/T(k) ∈ ℝ: membership` — a term is in a number
system because its parts are. The method states as a step's claim what `algebra` and
`inequalities` already work out for every atom they touch, and it exists so
that a dull fact of this kind is one line rather than a climb up the term one
library item at a time. A term built from numerals and letters by +, −, ·, a
power to a numeral and / needs no line at all, since the page says it once
(`SYNTAX.md`); the method is for a term with a defined name, a function's
value, a sum, a remainder or a binomial coefficient in it.

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
proved as a `proof` block would prove it: k is taken in X, what that
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
  writes, or for a letter the line introducing it, carried to S by at most one
  lemma (`nnre`, `zcn` and the rest), or
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

## inspection

`{x ∈ E : A is incident with x} = {a, b, c, d, e}: inspection, from H1` — a
claim about a set listed in full, checked element by element against what
the cited lines say. A textbook writes "by inspection" and its reader runs
down the list; the page does the same, and the cases are not written
(`READERS.md`, "What is seen by inspection").

The method is named for what the reader does, not for a subject: the
Königsberg graph is its first use, and nothing in it knows about graphs.

### Facts in

The lines the step cites, read for four kinds of sentence and nothing else:

- **a set listed in full:** an equation `S = {s₁, …, sₙ}`, or a `let` line
  that names a set by listing it, as "the multigraph with distinct vertices
  V = {A, B, C, D} and distinct edges E = {a, …, g}" names its vertices
  and its edges;
- **distinct names:** that the names of a list are pairwise different, as
  "distinct vertices A, B, C, D" says, and any `≠` between two names;
- **what a listed thing is:** an equation giving a term at a listed name,
  as "a joins A and B" says the ends of a are {A, B}, or a "for all"
  equation over a set the facts list, which gives a term at each of its
  elements, as "for all x ∈ V, deg(x) = |{a ∈ E : x is incident with a}|"
  gives deg(B) once V is listed;
- **what holds of a listed thing:** a line saying the property itself at a
  listed name, or its negation, as "deg(A) is odd" says it of A;
- **what a term is worth:** an equation giving a term a value of numerals
  alone, as "deg(A) = 5" does.

### Fact out

One sentence: `t ∈ S` or `t ∉ S`, or an equation `l = r`, where each side
is something the facts let the reader work out. What a term works out to:

- a set the facts list, or a set-builder `{x ∈ S : P(x)}` over one, is the
  list of its elements: those of S of which P holds, and ∅ lists none;
- the size `|S|` of such a set, once the facts say its names are distinct,
  is the numeral that counts them;
- a term spelt with numerals alone is itself;
- a term a cited "for all" equation gives at a listed element is what the
  other side works out to there.

So `{x ∈ E : A is incident with x} = {b₁, b₂, b₃, b₄, b₅}`, `|{b₁, b₂, b₆}| = 3`
and `deg(B) = 3` are one method, which works out both sides and compares
them.

### The procedure

A membership `t ∈ {s₁, …, sₙ}` holds where t is one of the sᵢ and fails
where the facts say t differs from each of them. A property P is settled at
an element by a cited line that says P there or denies it, or else by
reading P there through what the facts say that element is, until it is a
membership of that kind: "A is incident with f" is A ∈ {B, D} once f joins B
and D, and that fails because A, B and D are distinct. Where P is a word
whose record names `inspection` in its `decided` field (`DATABASE.md`), said
of a term a cited line gives a value of numerals alone, P is decided at that
value as `arithmetic` decides it and carried back by the line's equation:
"deg(A) is odd" from "deg(A) = 5". So Königsberg counts its odd vertices from
the four degrees, and no line says that 5 or 3 is odd. The
set S is replaced by its listing and P is settled at each element in turn.
A size is the length of the list once the facts say its names are distinct.
A term a "for all" line gives is read at the listed element it names, and
what the line's other side says there is worked out the same way. Two sets
are compared as sets, so their order is never asked, and two numbers by
working out the sum that counts one against the other.

### Refusals

- **A set not listed in full**, by a cited line, or a range or a set-builder
  the facts do not list: `inspection` checks a finite list a reader can see,
  and nothing it has to find.
- **A property that does not come down to listed membership** through what
  the cited lines say, nor to a word its record lets `inspection` decide at a
  value the lines give: an element whose case needs a lemma, a calculation or
  a reason of its own is a case to write, and `cases` writes it.
- **Two names not said to differ**, where the answer depends on it.
- **A search.** Only the cited lines are read, never the scope.

### Hypotheses

None beyond its facts in. That the listed things are sets, which the kernel
asks of a pair and a listed set, is apparatus the page never writes.

### Expansion

A listed set is set.mm's pair, triple or union of singletons. A membership
is `elpr`, `eltp` or `elun` with `elsng`, and its failure the same with the
disequalities the facts give (`pm2.65`). A property at each
element is the cited equation carried in (`eleq2d` and the congruences of
`substitute`). The set-builder over a listed set is `rabun2` and `rabsnif`
one element at a time, each element's case decided as above. A size is
`hashprg`, `hashtpg` or `hashunsng` repeated, each new element absent by
its distinctness, and the empty set's is `hash0`. A "for all" line is read
at its element by `rspcdva`. The two sides are joined by `eqtrd` and
`eqtr4d`, two listings in different orders by `eqssd`.

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
`contradicting 3.6`, or reaches a fact of numerals alone that cannot hold and
says so, `2 ≤ 1, which is impossible`. The second is how a reader ends the
argument "so 10 divides 1, which is impossible": nothing earlier says 2 > 1,
and writing a step to say it only so that the last step had a line to
contradict is not a proof anyone writes.

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
comparison. A last step that says it is impossible names no line: its claim
is worked out by `arithmetic`, and its denial, which `arithmetic` proves,
stands in for the line. The claim must name nothing, as `arithmetic`'s must,
and `arithmetic` must decide it false; one it finds true, cannot work out,
or does not decide (10 divides 1, a relation it does not have) is refused,
and the step names a line it contradicts instead. A case that cannot occur
may end the same way.

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

`READERS.md` first settled that membership in a number system is a written
dull fact and merits no exception. Applying that to both methods was then the
largest single change the corpus had taken.

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

### Membership said once

The corpus grew to 1,195 requires lines in its 31 proofs, 990 of them a
membership in a number system and 157 of those a numeral's, eleven on one
step. `READERS.md` now has the membership of a numeral, of a letter and of a
term built from them by +, −, ·, a power to a numeral and / said once, where
the letter is introduced, and the two tools build it (`ELABORATION.md`, a
membership said once). Counted 2026-10-09:

| | before | after |
|---|---|---|
| requires lines in the 31 proofs | 1,195 | 603 |
| of them a membership in a number system | 990 | 398 |
| of them a numeral's | 157 | 0 |
| most membership lines on one step | 11 | 8 |
| requires lines in the corpus and its tests, all needed (`parley gate`) | — | 631 |

Two library items no proof needed once, `half-real` and `nat0-closure`, were
removed.

The memberships still written are those the page does not say once: a power
to a letter (`2^p − 1 ∈ ℤ`), a function's value, a distance or an angle in
the geometry proofs, a sum, |x|, a remainder, C(n, k) and a defined name.
