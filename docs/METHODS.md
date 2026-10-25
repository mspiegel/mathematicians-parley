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

Eight methods are specified below: the five closure methods (`inequalities`,
`algebra`, `arithmetic`, `real arithmetic`, `membership`), `inspection`,
`join`, and `contradiction`. The rest
are not yet: the citation form, the block methods `proof`, `cases`,
`both directions` and `induction`, and `substitute`, `instantiate`, `obtain`
and `exhibit`. None is
a decision procedure, so each should be shorter than the closure methods
were. What each does is in `SYNTAX.md`, and what the elaborator builds for it
in `ELABORATION.md`.

Each method's procedure is in `src/methods`, and the checker runs it on
every step that names the method, without set.mm: a step the procedure
finds false is refused, and one it settles neither way is too ("step N names
inequalities, which does not decide what it claims"). No step is taken
without being examined. The build runs the same procedure before it writes
the proof.

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

## Pairs

Two pairs are compared coordinate by coordinate, by whichever method the
step names: (a, b) = (c, d) holds where a = c and b = d, and (a, b) ≠ (c, d)
where a ≠ c or b ≠ d. `arithmetic`, `real arithmetic`, `algebra` and
`inspection` each decide the coordinates' equations as they decide any of
their own, so `(1, 1) ≠ (2, 3)` is `arithmetic` because 1 ≠ 2,
`(0, √3) ≠ (0, 0)` is `real arithmetic`, `(a, b) ≠ (c, d)` is `algebra`
from a cited a ≠ c, and `(1, 2) ∉ {(3, 4), (1, 5)}` is `inspection`. A
difference is shown at the first coordinate the method shows apart: by its
value for the two calculating methods, by a cited disequality rescaled for
`algebra`, and by values or a cited line for `inspection`. A coordinate is
asked what any term the method reads is asked: `algebra` wants each
coordinate a number, as it wants each atom.

The expansion proves the coordinates by the method, and `opeq12d` carries
two equations to the pairs; for a difference, `opthg` reads two pairs as
equal just where both coordinates are, and the coordinate shown apart
denies that.

Points written as coordinates are not pairs (`GEOMETRY.md`), and a method
compares them as it compares any two points: not at all.

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
a numeral taken one step further, and it is what lets a row `multiplying by
2` take `1/(n + 1) ≤ 1/N` to `2/(n + 1) ≤ 2/N`.

So in `f(x₁) − f(c) ≤ |f(x₁) − f(c)|` the atoms are `f(x₁)`, `f(c)` and
`|f(x₁) − f(c)|`, three of them, and the last is an atom even though its own
inside contains the first two. The method never looks inside an atom and knows
nothing about what it means. That `|y|` is at least `y` is not available to it;
that fact reaches a step as a cited line, which is what
`thm:proofs/wiedijk/triangle-inequality/abs-bounds` is for.

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

### What a step does

**A step adds the lines it cites, side by side, and nothing more.** From
`a ≤ b` and `c ≤ d` it claims `a + c ≤ b + d`: the claim's left side is the
sum of the lines' left sides, and its right side the sum of their right
sides, each compared as a number, so `c + a` is that sum as well. The
lines are added as they stand. A step does not multiply one, cancel what two
share, rewrite a side, or read an equation as an inequality: equations add
to an equation, and orders to an order, strict where one of them is. Each of
those is a row (below), and a chain is `transitivity`.

Along the way it uses, without their being written, what a reader takes in
without thinking:

- **the bounds a membership gives**: `k ∈ ℕ` gives `k ≥ 1`, `k > 0` and
  `k ≠ 0` (Facts in);
- **a closed numeral fact**: `1 > 0` (Facts in);
- **a disequality taken both ways**: `a ≤ b` and `a ≠ b` give `a < b`
  (The procedure);
- **a negation turned round**: `not (a ≤ b)` is `b < a` (The procedure).

A step citing nothing it adds may rest on those alone: `m < m + 1`, `a ≤
a`, and `0 ≤ N` from `N ∈ ℕ` are each one step.

### Rows

A step that makes any other manipulation writes it out, a row at a time,
with the justification `inequalities` and no `from`:

```
1.1.  A < (A + B)/2
      inequalities
        A < B                D1
        A + A < A + B        adding A
        2·A < A + B          algebra
        A < (A + B)/2        multiplying by 1/2
```

The first row is a line the step cites, written out, with the line's label
as its reason; of a line saying several things, `0 < x and x < 1`, it is
one of them, a cited line being read as `SYNTAX.md`, What a cited line
says, reads it: `k ≤ n   K1` where K1 lets k ∈ {1, …, n}. A fact the line
says without writing it has no written orientation, and the row may write
it either way round: `1 ≤ k` or `k ≥ 1` from `k ∈ ℕ`. Each row after it is the row above with the manipulation its
reason names, and the last row is the claim:

| reason | the row is the row above with |
|---|---|
| `adding t` | t added to both sides |
| `multiplying by c` | both sides multiplied by c, a number other than 0; for c negative the relation turned round |
| `symmetry` | an equation's two sides swapped, or a `≠` or an order turned round: `a > 0` to `0 < a` |
| `weakening` | `<` or `=` weakened to `≤`, `>` or `=` to `≥`, or `<` or `>` to `≠` |
| `algebra` | a side written as the same number another way |

Each row keeps its sides where its manipulation leaves them: the first row
is the cited line as it is written, and the last row is the claim as it is
written. Turning a relation round is a `symmetry` row of its own, never
part of another row; `multiplying by` a negative number turns the relation
round, its sides staying where they are. Outside rows a relation is read
either way round without a word (transitivity, an item's hypothesis, a
requires line citing a line).

A row that adds or multiplies may write what it makes as the same number
another way: `multiplying by 1/2` takes `2·A < A + B` to `A < (A + B)/2`,
with `(2·A)/2` written `A`. An `algebra` row is for a rewriting that stands
alone. Each row's atoms are real, as a step's are (Hypotheses), and a row
multiplying by a term other than a numeral is no row: the method is linear.

A requires line has no rows, and names its one manipulation as its reason
instead: `requires q ≠ 0: weakening, from 2.1`, where 2.1 says `q > 0`, is
2.1 with `q > 0` weakened, as a row would be, written the way the
manipulation leaves it: from `0 < q` it is `requires 0 ≠ q: weakening,
from 2.1`. Of a line saying several
things it is one of them. That is how a divisor's
`≠ 0` is most often said. A side condition needing more than one
manipulation is a numbered step with rows, which the requires line cites.

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
k ∈ ℕ supplies k ≥ 1, k > 0 and k ≠ 0, and one saying k ∈ ℕ₀ supplies k ≥ 0. So
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
the negation of a relation are permitted as conclusions: an equation where the
lines added are equations, and the negation of a relation turned round, as
`not c ≤ c − δ` from `δ > 0`. An equation from two orders, `d = gcd(a, b)`
from `d ≤ gcd(a, b)` and `gcd(a, b) ≤ d`, is `antisymmetry`'s.

### The procedure

Negate the claim, add it to the cited facts, and show the set has no solution
over an ordered field, by a combination that adds the facts as they stand,
each once (What a step does). Concretely this is Fourier–Motzkin elimination
over the atoms, with two additions:

- **A negation is a fact, not a special case.** `not (a ≤ b)` is `b < a` and
  `not (a = b)` is `a < b or b < a`. Eight of the 25 steps do nothing but move
  between a relation and the negation of its complement, a cost the
  literal-negation rule of `SYNTAX.md` imposes on every proof that reaches a
  contradiction through an order relation.
- **A disequality splits.** Using `not (e = 0)` means solving twice, once with
  `e < 0` and once with `0 < e`, and both must fail. Two steps need this, each
  turning `≤` together with `≠` into `<`.

An equation is not two inequalities to a step. `x ≤ |x|` from `|x| = x` is
written as rows, `|x| = x`, then `x = |x|` by `symmetry`, then `x ≤ |x|` by
`weakening`, so that the reader sees the equation read as an order.

### Refusals

- **Anything non-linear.** Multiplying two atoms, or dividing an atom by
  one. No step in the corpus needs this, which is what makes the linear
  specification sufficient rather than merely convenient.
- **Anything about what an atom means.** An exponent law, the definition of
  absolute value, the value of a function. Those are cited items.
- **Strictness it was not given.** From `a ≤ b` alone it will not conclude
  `a < b`; the disequality must be among the cited facts.
- **Anything but adding, in a step.** Multiplying a line, cancelling what
  two lines share, rewriting a side, or reading an equation as an order.
  Each is a row, and a chain is `transitivity`.

### Hypotheses

Every atom must be a real number. This is a hypothesis of the method exactly as
`q ≠ 0` is a hypothesis of a division. Where the atom is a numeral, a term of
numerals alone that `arithmetic` works out (`0!`), a letter,
or built from those by +, −, ·, a power to a numeral or to a letter in ℕ or
ℕ₀, and /, the page says it once, where the letters are introduced
(`READERS.md`), and the step writes nothing, as it writes nothing for a sum
whose term is such a number at every index; any other atom, a function's
value or a sum whose term divides, is discharged by a
cited line or written as a requires line. A cited line is read as
`membership` reads it, so an equation the step cites, `a(0) = 0`, says
`a(0)` is real.

A reciprocal atom brings its divisor's hypothesis with it: `1/(n + 1)` is a
real number when `n + 1` is one and is not zero. That `n + 1` is real is said
once, with n; that it is not zero is said once too where n ∈ ℕ₀, since
n + 1 is then a positive integer, and is the page's to write where n ∈ ℤ. A
divisor of numerals alone whose value is not zero needs no line either: that
2 or 1 − 3 is not zero is a closed numeral fact, so `δ/2` and `δ/(1 − 3)` are
real because `δ` is.

An atom is one of the claim or of the facts the step combines — not of every
sentence a cited line says. Line 1 of `least-combination-divides` says
`0 ≤ r` and `r < d` among five things, and step 3.1's `requires 0 < r:
inequalities, from 1, S` takes `0 < r` from the first of them and the
supposition `r ≠ 0`; d is in none of what it combines,
so `d ∈ ℝ` is not one of its hypotheses. A dull fact is one that discharges a
hypothesis, and one that discharges nothing is a line doing no work.

The memberships a step still writes are those the page does not say once:
the absolute value of a real number (`mun:stdlib/numbers/abs-real`), a power to
a letter that is not in ℕ or ℕ₀, 2^k with k ∈ ℤ
(`mun:stdlib/numbers/power-real-integer`, from a base other than 0;
`mun:stdlib/numbers/power-real` takes ℕ₀, and a power to a letter in ℕ or
ℕ₀ is said once, `SYNTAX.md`), a
function's value from its type, a finite sum from its terms. Every natural bridge is direct rather than through
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

### Held to an oracle

`tests/oracle.rs` draws claims around a point. The letters are given whole
values, and each cited fact is a linear fact true there: at most, below,
equal, or at most and not equal. A claim made true is a positive sum of
the cited facts, an equation by a number of either sign, less a number 0
or more, which is Farkas's certificate itself. A claim made false fails at
the point, where every cited fact holds, so nothing it cites gives it. Each
cited fact has a letter of its own that the claim holds, so a true claim
uses every line it cites, and a cited disequality is drawn only where it
is what makes the claim strict. The method must prove each true claim and
refuse each false one as not following.

---

## transitivity

`transitivity, from L₁, …, Lₙ` is the transitive property of `=`, `≤` and
`<`: from `a ≤ b` and `b < c`, `a < c`. The cited lines, in the order they
are cited, make a chain. Each gives one relation between two terms: the
line's, or of a line saying several things, the one of them that meets the
chain. Where a line says several that meet it, the claim decides: the one
taken is the one making a chain from the claim's first term to its last, as
`0 < k` from `k ∈ ℕ` in `0 < n` from `k ∈ ℕ` and `k < n`; where two choices
both reach the claim, the step is refused. A cited line is read as `SYNTAX.md`, What a
cited line says, reads it: `a = b = c` gives `a = c`, and `k ∈ {1, …, n}`
gives `k ≤ n`. A define of a name is cited as its
equation, as a calculation's link citing it is (`SYNTAX.md`, a step may
cite a define): `let e = ⌊A + 1/2⌋ − A (D1)` gives `e = ⌊A + 1/2⌋ − A`, and
a define that also says what kind of number its name is gives the
equation to the chain. Where
one line ends the next begins: the term they share is written the same way
in both, since rewriting a side is a row of `inequalities`. A line is read
from whichever side meets the line before, as an order may be written
either way round (`b > a` is `a < b`). The claim relates the chain's first
term to its last.

Its relation is a calculation's (`SYNTAX.md`, `calculation`): `=` where every
line is `=`; going up, `≤` where every line is `=` or `≤`, and `<` where any
is `<`; going down, `≥` and `>` the same way, each line read the way the
chain takes it. A chain goes one way: `a ≤ b` and `c ≤ b` say nothing of a
against c, and are refused.

It is a calculation whose terms the cited lines write: what the reader of
`a ≤ b < c` follows, said of two lines that each state a link. A step
puts two facts together without an "and", as a calculation's links do.

**Hypotheses.** Where a link is an order, every atom of the chain's terms
is a real number, as an inequalities step's atoms are (inequalities,
Hypotheses): said once, or by a line the step names. A chain of `=` alone
asks nothing, for its terms may be sets.

**Refusals.** Lines that do not chain in the order cited; a middle term
written two ways; a chain that goes both up and down; a claim that is not
the chain's first term related to its last by the chain's relation.

---

## antisymmetry

`antisymmetry, from L₁, L₂` is the antisymmetry of `≤`: from `a ≤ b` and
`b ≤ a`, `a = b`. The two cited lines are those two orders, in either
order, each side written the same way in both, and the claim is the
equation between them, either way round: Bezout's `d = gcd(a, b)` from `d ≤
gcd(a, b)` and `gcd(a, b) ≤ d`. `≥` is `≤` the other way round, so `b ≥ a`
is `a ≤ b`.

**Hypotheses.** Every atom of the two sides is a real number, as an
inequalities step's are.

**Refusals.** Lines that are not one order and its converse; a strict
order, which with its converse is a contradiction and not an equation; a
claim that is not the equation of the two sides.

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

**A defined name is read as `inequalities` reads it.** Where the step cites
its define, the claim and the cited lines are taken with the name written
out, and the proof is carried back to the claim as written: with `let M =
2N + 1 (D1)`, `M − 1 = 2N` by `algebra, from D1` is 2N + 1 − 1 = 2N, and M
is a number as 2N + 1 is, said once.

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

**Dividing both sides by a term is not a second thing.** An equation
that divides is read with its denominators multiplied across, and a
divisor it writes may then be divided out again where it divides what the
equation says. A claim follows when one way of dividing out its divisors
leaves a combination of the cited equations, read with their own divisors
divided out where they divide: from y = 1 and z = 2, (x·y + z)/(x + 3) =
(x + 2)/(x + 3) is x times the first and the second, over x + 3, one step;
and from y² = 9, (x·y² − 2·y² − z)/(y − 3) = (9·x − z − 18)/(y − 3) is
(x − 2)(y − 3) times it with y − 3 kept, since dividing it out would take
it from the cited equation as well. Only the divisors the claim writes are
tried, and only where they divide it exactly.

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
- **A power that costs more than 300 000 to multiply out.** The proof
  raises a power one step of the exponent at a time, and each step puts the
  terms it makes in order one by one, every move rewriting the polynomial so
  far. So a step whose result has T terms, from a base of b terms, costs
  T³·b, and no step less than 50. Measured, a million of these is 3 to 5 GB
  of memory, and the limit keeps a power under the 2 GB a build allows:
  (x + y)^24 costs some 210 000 and (x + y + z)^7 some 250 000, while
  (x + y)^30 and (x + y + z)^8 are refused, and x^27 costs a few hundred. A
  step reading such a power, in its claim or a line it cites, is refused.

### Hypotheses

Two kinds.

Every denominator the step's claim and the cited lines it combines write is
nonzero, and a step that divides writes the condition or cites a line
saying it, unless the page says once that the denominator is not zero, as
of a term of numerals alone whose value is not zero or of a positive integer
(`SYNTAX.md`), or it is a product, a quotient, a negation or a power to a
numeral whose parts are each not zero so: `(x·2 − 1)/(x·2)` asks only for
`x ≠ 0`, and
`(2^j·2 − 1)/(2^j·2)` with j ∈ ℕ₀ asks nothing (`membership`, the same
test).

Every atom of the claim and of the cited lines it combines is a real
number, as for `inequalities`: said once where the atom is a numeral, a
letter, built from them, or a sum whose term is such a number at every
index, and otherwise written or given by a cited equation, as `membership`
decides it: citing `a(0) = 0` says `a(0)` is a number. What the step could
work out from its parts but the page does not say once, as `Σ(k = 1 to n)
1/k` from a line about 1/k, is written.

The checker asks both of each `algebra` step that holds
(`checker::formulas::algebra_unsaid`).

### Expansion

set.mm's ring and field lemmas are over ℂ, so the expansion carries the atoms
from ℝ to ℂ itself and the text never mentions ℂ, which is what `READERS.md`
requires of it. The families are `addcom`, `addass`, `mulcom`, `mulass`,
`adddi` for normalisation; `mulcl`, `addcl`, `subcl`, `divcl` for closure;
`divcan`, `divmul`, `divass` for the divisions; and `subeq0` for the
disequality case.

Ideal membership over a fixed set of atoms is decidable, so the expansion is
total. With at most one `pᵢ` a polynomial, no Gröbner basis is needed: each
cited equation in turn is the one a term may multiply, and dividing by one
polynomial leaves a remainder that is nought exactly for its multiples. The
remainder of a sum is the sum of the remainders, so the numbers the other
equations are taken by solve a linear system, and the polynomial is the
quotient of what is left. A cited equation that divides is read with its
denominators multiplied across, and its multiplier in the proof carries
them. So does the claim: a divisor it writes that every multiplier carries
is divided out of them, and the claim's two sides are multiplied by each
other divisor and the product taken off at the end, that it is not 0 being
what the page says of the divisors as written. Each cited equation is
written into the proof once, times its whole multiplier, in the order the
step cites them.

Six steps are written out in `corpus/elaboration/`, and `ELABORATION.md` measures
them. Five come from the three elaborated proofs; the sixth is step 2 of
`thm:proofs/wiedijk/bezout/least-combination-divides`, the only step in the corpus whose
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

### Held to an oracle

`tests/oracle.rs` draws three kinds of claim and expands each with a
polynomial arithmetic of its own. Identities of letters and numerals by
sums, products, powers and division by a numeral, and those one
coefficient away. Claims made of one or two cited equations, one times a
polynomial of any degree and the other times a number, each equation's
value at a point taken off, and one more on a side to make the claim
false. And claims divided by a term in the letters, which a line says is
not 0, from up to two cited equations. Two equations each multiplied by a
term, in letters they do not share, are drawn as the refusal above.

---

## arithmetic

`arithmetic` decides **closed numeral facts**, a subset of the facts with no
letter in them (Boundary, below). A fact it can work out gives a reader
nothing to check but working it out, so it names `arithmetic`
where it is used rather than standing as a step of its own (`SYNTAX.md`). It
justifies a requires line; it is the source of a `substitute`, `substitute 0
+ 1 = 1 (arithmetic)`; and it is the reason on a chain line of numerals alone,
`= 1(1 + 1)/2    arithmetic`. It justifies a numbered step only where the
proof's shape asks a line there: an induction's base case, and a fact a
method takes only from a cited line, as the birthday problem's step 8,
23 ≤ 365, is for the `transitivity` of step 9.
In each place the same procedure and the same refusals apply, and the
checker refuses the method for a fact with a letter in it.

The requires lines of the corpus that cite it, counted 2026-10-09:

| what the claim is | requires lines |
|---|---|
| membership of a closed term in a number system | 1 |
| a word its record lets it decide, as 3 divides 10 − 1 | 1 |
| an order relation, as 2 ≥ 0 | 3 |
| a disequality, as 2 ≠ 0 | 4 |

A numeral's membership is not written at all (`READERS.md`, said once). A
product over a range, ∏(k ∈ {0, …, 22}) (365 − k), is closed but not built
from numerals by the operations the page says once, so its membership is
written where a step asks it; the birthday problem's claim about it,
(∏(k ∈ {0, …, 22}) (365 − k))/365^23 < 1/2, is one arithmetic works out, and
cites `arithmetic` whole.

### Facts in

None. `arithmetic` takes no `from` list and never has. It is the only method
that cites nothing.

### Fact out

A relation between **closed numeral expressions**, where a closed numeral
expression is built from decimal numerals by `+`, `−`, `·`, `/`, powers,
`mod` and factorials, and by products over a range of numerals,
∏(k ∈ {0, …, 22}) (365 − k), with every operand closed. `x mod n` is worked
out where x is a whole number and n one of at least 1: `10^0 mod 3 = 1`;
`n!` where n is a whole number, `(1 + 1)! = 2`. `mod` and the factorial are
not operations arithmetic works out by its nature, and each notation record
says `decided arithmetic` (`DATABASE.md`); an operation whose record does
not is refused. The relation is `=`, `≠`, `<`, `≤`, `>`, `≥`, or
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
decided by evaluating both, each an integer and d not 0, and dividing: it
holds when the remainder is 0, and fails otherwise. −6 is even, and −3
divides 9.

### Refusals

- **Anything containing a variable.** This is the line against `algebra`, and
  it is not a formality: `a^(0 + 1) = a` was once justified this way, and
  refusing it exposed that the claim smuggled in an exponent law. The geometric
  series now pays four steps for that one fact.
- **Anything that does not evaluate to a rational.** `√2 ∈ ℝ` is not
  arithmetic; a square root of a rational is `real arithmetic`'s, which is
  kept apart so that what arithmetic decides stays small enough to read.
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
- **A divisibility outside the integers, or by 0:** `1/2 divides 4` and
  `0 divides 0` are not worked out. set.mm gives 0 divides 0 a value, and
  no reader asks it.
- **Anything false.** The claim is worked out before a proof is attempted,
  so a false one is reported as false.

`arithmetic` never takes a step as stated. What it cannot prove is reported:
as false, as one of the refusals above, or, should the expansion below not
reach a claim it has worked out as true, with the instruction to cite a
theorem that states it. `tests/oracle.rs` draws claims of every form above,
works each out with an oracle of its own, and requires each true one to be
proved and verified; on thousands of claims it finds none the expansion
does not reach.

### Hypotheses

None, and that is the point of it. Requires lines do not nest, so whatever
justifies one must need nothing further. `arithmetic` is where that recursion
stops.

### Boundary with algebra and inequalities

On a claim of numerals alone `algebra` would succeed too, normalising
`1 − 1(1 + 1)/2` to zero, and so would `inequalities` on `not 2 ≤ 1`, from
the closed facts it takes uncited. Both combine what a step says of its
letters and constants, and a claim `arithmetic` can work out gives a reader
nothing to check but working it out. So a claim arithmetic can work out
cites `arithmetic`, whatever relation it states: one built from numerals by
the operations under *Fact out*, stating a relation it decides. The checker
refuses `algebra` or `inequalities` for one, in a step or a requires line.
A step marked impossible is the exception: `5 = 0, which is impossible`,
the last line of a contradiction, states a false fact that its method
reaches from the lines it cites, `algebra, from H2, S`, and arithmetic,
which finds it false, could not give it. The same holds of `real
arithmetic` and a line like `√2 = 1, which is impossible`.

A claim with no letter that arithmetic cannot work out is not arithmetic's.
`√2·√2 = 2` takes a square root, which is `real arithmetic`'s (below).
`1 + i·0 = 1` holds a constant neither method has a value for, and is
`algebra`'s, which takes i as an atom, as it takes a letter, and cites what
it uses of it as it would of a letter.

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

A factorial of a whole number is 0! = 1 (`fac0`) and (m + 1)! = m!·(m + 1)
(`facp1`), each product worked out as above.

A divisibility of whole numbers is proved at their values and carried back to
the terms as written by `breq12d`. That d divides n, with n = d·q, is
`dvdsmul1` at d and q, the product worked out (`breqtri`). That it does not,
with n = d·q + r and 0 < r < d, is `ndvdsi` from the quotient, the remainder
and the sum and order the numeral lemmas prove: 5 is odd because 2·2 + 1 = 5
and 1 < 2. A divisibility with a side below 0 is proved at the sizes of its
values, and each sign turned by `dvdsnegb` or `negdvdsb`, which say a
divisibility holds exactly where it does with a side negated: 2 divides −8
because 2 divides 8.

Any other claim of closed numeral expressions is said of its sides' values:
a value below 0, a fraction inside a sum, a power of a negative base, a
remainder inside an order, a membership of ℚ. Each side is worked to its
value written plainly, a numeral, its negation, a fraction of two numerals
or the negation of one. The normaliser works a side whole where it reaches
it. Otherwise the side is worked part by part from the inside out: a
remainder or a product over a range by the steps above, the rest by the
normaliser, each part's equation carried up through the operation above it
(`oveq12d`, `negeqd`), a division by a value below 0 as the negation of
one by its opposite (`divneg2d`), and a power to an exponent below 0 as
one over the power (`expnegd`), which the normaliser would hold as an atom
it has no membership for. A membership of a term holding such a power is
its value's, carried back by `eleq1d`. The claim is proved of the values and
carried back to the sides as written (`breq12d`, `eqeq12d`, `eleq1d`).

Between values, two that differ are apart because the lower is below the
higher (`ltne`). A whole number is rational by way of ℤ (`zq`), a fraction
of whole numbers by `znq`, and a negation as what it negates (`qnegcl`); a
value is real or complex by way of ℚ (`qre`, `qcn`). A value strictly
between a whole number and the next is in no system of whole numbers
(`btwnnz`, with `nnz` and `nn0z` for ℕ and ℕ₀). A denominator of closed
numerals is shown not zero the same way, without a line saying it, as a
closed numeral fact is taken anywhere.

### Held to an oracle

`tests/oracle.rs` draws relations, memberships, divisibilities, parities
and congruences of numeral terms up to three deep, of every operation,
powers to exponents from −2 to 3 among them, and works each out in exact
rationals of its own. Each refusal above is drawn
and expected in its own words; a claim with several parts refused may be
refused for any of them.

---

## real arithmetic

`real arithmetic` decides **closed facts about square roots of rationals,
π, e, and logarithms of rationals**: `√8 = 2·√2`, `(1 + √2)² = 3 + 2·√2`,
`1/(√3 − 1) = (√3 + 1)/2`, `√2 − 1 ≠ 0`, `ln 8 = 3·ln 2`, `exp(ln 5) = 5`,
`(π + e)² = π² + 2·π·e + e²`, `ln 2 ≠ ln 3`, `180° = π`, `√2 < 3/2`,
`0 < ln 2`, `e < π`. It stands where
`arithmetic` stands, and for the same reason:
a claim it works out gives a reader nothing to check but working it out. So
it justifies a requires line, `requires √2 − 1 ≠ 0: real arithmetic`; it is
the source of a substitution, `substitute √8 = 2·√2 (real arithmetic)`; it
is the reason on a chain line of closed terms, `= 2·√2    real arithmetic`;
and it justifies a numbered step only where the proof's shape asks a line
there. Like `arithmetic` it is marked mundane, and the checker refuses it
for a fact with a letter in it.

It is a method of its own, and not more of `arithmetic`, so that what
`arithmetic` decides stays small enough to read and its procedure and
expansion stay as they are. `real arithmetic` reads a part with no root in
it by `arithmetic`'s procedure; `arithmetic` reads nothing of this one.

### Facts in

None. It cites nothing.

### Fact out

A relation between **closed real expressions**, where a closed real
expression is built from decimal numerals by the operations `arithmetic`
works out, and by:

- `√`, the square root, taken of a closed real expression whose value is a
  rational of at least 0;
- the constants π and e, Euler's number, which a letter the text names e
  shadows, as it shadows i;
- `ln`, the natural logarithm, taken of a closed real expression whose
  value is a positive rational, or a positive rational times a whole power
  of e: `ln(1/2)`, `ln(e³)`;
- `exp`, taken of a closed real expression whose value is a whole number of
  at least 0 plus whole multiples of logarithms of primes: `exp(ln 5)`,
  `exp(2)`, `exp(1 + ln 3)`;
- `sin` and `cos`, taken of a closed real expression whose value is 0 or a
  rational multiple of π whose denominator divides 4 or 6: `sin(π/6)`,
  `cos(3·π/4)`, `sin(210°)`, `cos(0)`;
- `°`, the degrees notation, x° being x·π/180.

None of these is worked out by the method's nature. Each record says
`decided real arithmetic` (`DATABASE.md`): the notation records of `√`, π, e
and `°`, and the function records of `ln`, `exp`, `sin` and `cos`, which a
proof imports. An operation, a constant or a function whose record does not
name the method is refused, as `gcd(4, 6)` is, and as i always is.

The relations, and their denials:

| relation | decided |
|---|---|
| `=`, `≠` | where neither side holds π, e or a logarithm; otherwise where the two values are equal, or where they differ by a surd or by rational multiples of logarithms of primes (The procedure) |
| `<`, `≤`, `>`, `≥` | where the two values are equal, or their difference is rational, holds no π, e or logarithm, or is rational multiples of logarithms of primes; otherwise where the bounds on π, e and logarithms decide it (Order) |
| membership of ℝ or ℂ | always |
| membership of ℕ, ℕ₀, ℤ or ℚ | where the value is rational, `√(9/4) ∈ ℚ`, `exp(ln 4) ∈ ℕ` |

No word is decided: `√4 is even` is refused, as a word whose record does not
name the method is.

### The procedure

Evaluate each side to a **value**: a sum of rational multiples of square
roots of distinct squarefree whole numbers, Σ qₘ·√m, where m = 1 is the
rational part and no qₘ is 0. Each root is held as the primes whose product
it is the root of.

- A rational r = a/b of at least 0, in lowest terms, has a·b = s²·m for one
  whole s and one squarefree m, and √r is s/b·√m: √8 is 2·√2, and √(1/2) is
  1/2·√2.
- Sums and differences add the coefficients of each root.
- √m·√n is the product of the primes m and n share, times the root of the
  primes only one of them holds: √6·√10 is 2·√15.
- A value holding √p, read as a + b·√p with a and b free of √p, times its
  **conjugate** a − b·√p is a² − p·b², which holds √p no more. Multiplied by
  its conjugate in each of its primes in turn, a value becomes a rational,
  its **norm**, and the product of the conjugates is its **cofactor**. A
  value is not 0 exactly where its norm is not, and one over it is its
  cofactor over its norm: 1/(√3 − 1) is (√3 + 1)/2.
- A power is taken only with a whole exponent, and a negative one is the
  power of one over the base.

Two values are equal exactly where their coefficients are. The square roots
of distinct squarefree whole numbers are linearly independent over ℚ, so a
value has one spelling; that theorem is what makes `=` and `≠` decided
always, and nothing proved here leans on it, since a proof shows each
equation it states.

An order is decided by the sign of the difference of its sides (Order,
below), and a membership of ℕ, ℕ₀, ℤ or ℚ where the value is rational, by
`arithmetic`'s tests. Every value is real.

**π, e and logarithms.** A value is then a polynomial in the atoms π, e and
ln p for primes p, its coefficients values of the square-root kind above:
Σ sₘ·M, M a product of whole powers of atoms.

- A logarithm of a positive rational r = Π p^nₚ, its numerator and
  denominator factored, is Σ nₚ·ln p: ln 8 is 3·ln 2, ln(1/2) is −ln 2, and
  ln 1 is 0. A logarithm of r·eᵏ is that plus k: ln(e³) is 3.
- exp(k + Σ nₚ·ln p), k and each nₚ whole and k at least 0, is eᵏ·Π p^nₚ:
  exp(ln 5) is 5 and exp(2) is e².
- Sums, differences, products and whole powers are those of polynomials.
  A division is taken only by a value with no atom.

Two such values are equal where their coefficients are, and that is proved.
Where they are not, the claim is decided only where their difference D is
one the method can show is not zero:

- D holds no atom: it is a value of the square-root kind, and decided as
  above;
- D is Σ qₚ·ln p, rational multiples of logarithms of primes and nothing
  else: Σ nₚ·ln p = 0, with whole nₚ, would make Π p^nₚ = 1, which unique
  factorisation forbids unless every nₚ is 0, so ln 2 ≠ ln 3 and
  ln 8 ≠ 2·ln 2 hold.

Any other difference is **not decided**: π = e, π² = 10, ln 2 = 1,
√2·ln 2 = ln 3. Each is false, but showing it asks more than the method
proves: that π is irrational, which set.mm does not prove; that e is
transcendental, which a mathbox does and the method does not use; or that
logarithms of primes stay independent over the roots, which is Baker's
theorem. Such a claim is reported as not decided, never as false.

**sin and cos.** An angle of value q·π, q rational with a denominator that
divides 4 or 6, is reduced to r·π with r = q less a whole multiple of 2, so
0 ≤ r < 2, since sin and cos repeat every 2π. Then, for r of at least 1,
sin(t + π) = −sin t and cos(t + π) = −cos t take π away; for r of at least
1/2, sin(π/2 + t) = cos t and cos(π/2 + t) = −sin t take π/2 away; and what
is left is 0, π/6, π/4 or π/3, whose sines and cosines are 0 and 1, 1/2 and
√3/2, √2/2 and √2/2, √3/2 and 1/2. So every value is 0, ±1/2, ±√2/2, ±√3/2
or ±1, a value of the square-root kind, and holds no atom: sin(7·π/6) is
−1/2, cos(3·π/4) is −√2/2, and sin(30°) is 1/2.

**Order.** L < R and L ≤ R are decided by the sign of D = R − L, worked
out as a value:

- D is 0: L ≤ R holds and L < R fails.
- D is rational: its sign is `arithmetic`'s.
- D is Σ qₚ·ln p, rational multiples of logarithms of primes and nothing
  else: with n the least whole number making each n·qₚ whole, n·D is
  ln r, r = Π p^(n·qₚ), and D is above 0 exactly where r is above 1:
  `ln 3 < 2·ln 2`, since 3 < 4.
- Otherwise D's sign is read from **brackets**. Each factor of a part of
  D, a root √p, π, e or ln p, lies strictly between two rationals l < u,
  and l is above 0:
  - √p between ⌊2ʲ·√p⌋/2ʲ and that plus 2⁻ʲ, for a precision j of 4,
    8, 16, 32 or 64 bits, the least that decides;
  - π between 3 and 4, set.mm's `pigt3` and `pigt2lt4`;
  - e between 2 and 3, set.mm's `egt2lt3`;
  - ln p between a/b, the greatest with b at most 8 and 3ᵃ ≤ pᵇ, and
    a′/b′, the least with b′ at most 8 and pᵇ′ ≤ 2ᵃ′, since eᵃ < 3ᵃ and
    2ᵃ′ < eᵃ′: ln 2 between 5/8 and 1, ln 3 between 1 and 8/5.

  A product of factors lies between the products of their ends, a power
  as a product of its factor; a part c·X between c·l and c·u, the other
  way round where c is below 0; and a sum between the sums of its parts'
  ends. D is above 0 where the lower end of the sum is at least 0, and
  below 0 where its upper end is at most 0, strictly in each case, since
  each factor's bracket is strict.

A difference holding no π, e or logarithm is not 0, which is decided
exactly, so some precision decides its sign; it is only too large where
64 bits do not (Refusals). A difference holding one may lie in a bracket
that holds 0 however fine its roots: π² < 10 holds, but π² lies between
9 and 16 by set.mm's bounds, and no tighter bound on π is proved there.
Such an order is reported as not decided, never as false.

### Refusals

- **Anything containing a variable.** As for `arithmetic`.
- **A claim holding nothing beyond what `arithmetic` works out,** no root,
  π, e, logarithm, exponential, sine, cosine or degree. That is
  `arithmetic`'s, and cites it (Boundary, below).
- **An operation, constant or function whose record does not name the
  method:** `gcd(4, 6) = 2`, `i·i = −1`.
- **A sine or cosine of an angle that is not a rational multiple of π,**
  `sin(1)`, `cos(π + 1)`, or **of one whose denominator divides neither 4
  nor 6,** `sin(π/12)`, `cos(π/5)`. Each is a value the method has no
  spelling for.
- **A logarithm of a number not above 0.** set.mm's `log` is taken in ℂ,
  and ln(−1) is i·π there, which is not a real number; ln 0 is no number.
- **A logarithm of a number that is neither a positive rational nor one
  times a whole power of e,** `ln 2^(1/2)`, `ln π`.
- **An exponential of a number not of the form above,** `exp(1/2)`,
  `exp(−1)`, `exp(π)`: √e and 1/e are no values of the method.
- **A division by a value holding π, e or a logarithm,** `1/π`, `2/ln 2`.
- **An equation or a disequality whose difference holds π, e or a
  logarithm otherwise than as rational multiples of logarithms of primes,**
  `π = e`. It is reported as not decided, never as false.
- **A square root of a number below 0.** set.mm's `√` is taken in ℂ, and
  √(−4) is 2·i there, which is not a real number.
- **A square root of a number that is not rational,** √(1 + √2). Whether a
  nested root comes apart is a question of its own, and is not asked.
- **A power with an exponent that is not whole,** `2^(1/2)`. The square root
  is written `√`, and it is the only root taken.
- **A division by zero,** `1/(√2 − √2)`, worked out as its divisor's value.
- **An order the bounds on π, e and logarithms do not decide,** `π² < 10`
  (Order). It is reported as not decided, never as false.
- **A membership of ℕ, ℕ₀, ℤ or ℚ of a value that is not rational, or its
  denial.** That √2 is not in ℚ is the theorem `sqrt2-irrational` proves,
  and a method that worked it out would make that proof one line.
- **A number too large to work out.** A radicand whose numerator times
  denominator passes 40 bits is refused, since its squarefree part is found
  by trial division. A claim holding more than four distinct primes under its
  roots is refused, since each prime doubles how many parts a value may have.
  A true claim's proof is estimated before it is built: each product of two
  values of P and B parts it writes is an identity whose proof restates the
  product at every move, and costs (P·B)³, and a claim costing more than
  100 000 is refused. Measured, (√2 + √3 + √5 + √7)⁴ costs some 59 000 and
  peaks at 1.0 GB, 1/(1 + √2 + √3 + √5) ≠ 0 some 99 000 and 0.8 GB, and
  (√2 + √3 + √5 + √7)⁸ some 190 000 and 2.7 GB of the 2 GB a build allows.
  A claim whose proof would write a numeral past 62 bits is refused too,
  since the normaliser reads a numeral as a number only within 64 bits:
  (1 + √2)⁴⁰ is proved, and (1 + √2)⁸⁰ is refused. An order whose sign
  roots bracketed to 64 bits do not decide is refused, where finer roots
  would decide it.
- **Anything false.** The claim is worked out before a proof is attempted,
  so a false one is reported as false.

What it finds true and cannot prove is reported with the instruction to cite
a theorem that states it; nothing is taken as stated.

### Hypotheses

None. That a radicand is at least 0, a logarithm's argument above 0 and a
divisor not 0 are closed facts of their own, which the procedure works out
with the claim, and which the expansion proves (below).

### Boundary with arithmetic, algebra and inequalities

The line against `arithmetic` is on the text: a closed claim that writes `√`,
π, e, `ln`, `exp`, `sin`, `cos` or `°` is this method's, and one that writes
none of them is `arithmetic`'s. `√4 = 2` writes a root, so it cites
`real arithmetic` though both its values are rational, and so do
`exp(ln 4) = 4` and `cos(0) = 1`. The
checker refuses `real arithmetic` for a claim that writes none of them ("a
claim of numerals alone cites arithmetic").

As against `algebra` and `inequalities`, the rule for an equation, a
disequality and a membership is `arithmetic`'s: a closed one this method
decides cites it, and the checker refuses `algebra` or `inequalities` for
it. `√2·√2 = 2` cites `real arithmetic`. An order is not held to that rule:
`0 ≤ √2/2` may cite `real arithmetic`, or `inequalities`, which takes √2 as
an atom and cites what it uses of it from a line citing `mun:sqrt x := 2`.
A closed order this method's bounds do not reach, `π² < 10`, asks a bound
on π tighter than set.mm proves, and is a theorem to cite. `inequalities`
does not reach it from set.mm's bounds either, since it reads π² as an atom
of its own and knows of it only what a cited line says.

A square root, π, e, a logarithm, a sine or a cosine this method works out
is in ℝ, and so is what the field's operations build from them; that is said
once (`READERS.md`), as a numeral's membership is: `requires √2 ∈ ℝ`,
`requires π + ln 2 ∈ ℝ` and `requires sin(π/6) ∈ ℝ` are not written.

### Expansion

The claim is worked out first, and the proof follows what the procedure
found. Each term is proved equal to the **canon** of its value: an
expression in roots of primes, its parts added from the left, the rational
part first and then by the product under the root, each part a whole
coefficient times a product of roots of primes, and the whole over the
least common denominator of the coefficients where they are not whole. Two
terms of one value have one canon, so an equation is each side proved
equal to it. The normaliser adds fractions without cancelling, so a canon
of eight parts each over N would be read over N⁸; written over N once, it
is read over N.

- **A root.** For √x with x of value r = c²·(p₁·(p₂·…)), `arithmetic` proves
  x equals that product, `fveq2d` carries the equation under the root, the
  root of a product is the product of the roots (`sqrtmuld`, its four side
  conditions facts of numerals), and the root of c² is c (`sqrtsqd`). So √x
  is c·(√p₁·(√p₂·…)).
- **An operation.** Each operand is proved equal to its expression, and the
  equations are carried up through the operation (`oveq12d`, `negeqd`). A
  part with no root is left as written, except a remainder, a factorial or a
  product over a range, which `arithmetic` works to its value first.
- **A power** is built a step at a time, each step the base times one power
  less (`expp1d`) and each product brought back to an expression of the
  value's parts before the next, so a power never expands whole. A negative
  exponent is one over the power (`expnegd`).
- **An identity.** Two expressions with one value, times d, the least
  whole number that makes the coefficients of their difference whole,
  differ by a sum of whole multiples of (√p)² − p, one for each prime: the
  procedure reduces the difference by (√p)² = p, and the multiples are what
  it takes away. Each (√p)² = p is `sqsqrtd`, each multiple of a difference
  that is 0 is 0 (`subeq0ad`, `mul01d`), and the normaliser proves the sum of
  the multiples is the difference itself; `subeq0ad` again, and d is
  cancelled (`mulcanad`). The normaliser is the one `algebra` uses, given
  √p ∈ ℂ for each prime (`sqrtcld`).
- **A value not zero.** For a value D with cofactor C and norm N, the
  identity D·C = N is proved as above, N ≠ 0 by `arithmetic`, and D ≠ 0
  follows (`mulne0bad`). A disequality L ≠ R is L − R not zero (`subne0ad`).
- **A division** A/B is a quotient Q where B·Q = A and B ≠ 0 (`divmuld`).
- **A membership** of a rational value is proved of the value by
  `arithmetic` and carried back to the term as written (`eleq1d`). A
  membership of ℝ is the expression's, built from √p ∈ ℝ
  (`resqrtcld`), π ∈ ℝ (`pire`), e ∈ ℝ (`ere`), ln p ∈ ℝ (`relogcld`) and
  the field's closure (`remulcld`, `readdcld`).

With π, e and logarithms, a canon's part is its coefficient times its roots
times its atoms' powers, the parts in the order of their atoms, π first,
then e, then ln 2, ln 3 and on. The identity above is unchanged: it reduces
(√p)² = p and nothing else, and to the normaliser π, e and each ln p are
atoms like √p, given π ∈ ℂ (`picn`), e ∈ ℂ and ln p ∈ ℂ.

- **A logarithm.** For ln x with x of value Π p^nₚ·eᵏ, x is proved equal to
  that product, by `arithmetic` where k is 0 and by an identity where it is
  not, and `fveq2d` carries the equation under the logarithm. The logarithm
  of a product of positive reals is the sum of the logarithms (`relogmul`,
  each factor in ℝ⁺ by `elrpd` or `rpexpcld`), of a power to a whole
  exponent the exponent times the logarithm (`relogexp`), of e is 1
  (`loge`), and of 1 is 0 (`log1`).
- **An exponential.** For exp x with x of value k + Σ nₚ·ln p, x is proved
  equal to k + ln r, r = Π p^nₚ, by an identity and the logarithm above;
  exp(k + ln r) is exp k · exp(ln r) (`efadd`), exp(ln r) is r (`reeflog`),
  and exp k is (exp 1)ᵏ (`efexp`), which is eᵏ by `df-e`.
- **Degrees.** x° is (x·π)/180 by its notation's target, an operation like
  any other.
- **A sine or a cosine.** For sin x with x of value q·π, q = 2k + r and
  0 ≤ r < 2, x is proved equal to a(r) + k·(2·π), or to a(r) where k is 0,
  by an identity, a(r) being 0, π/6, π/4 or π/3 below π/2, (π/2) + a(r − 1/2)
  from π/2 to π, and a(r − 1) + π from π to 2π; `fveq2d` carries it under
  the sine. sin(t + k·(2·π)) = sin t (`sinper`, `cosper`); sin(t + π) =
  −sin t (`sinppi`, `cosppi`); sin(π/2 + t) = cos t and cos(π/2 + t) =
  −sin t (`sinhalfpip`, `coshalfpip`); and the values at 0, π/6, π/4, π/3
  and π/2 are set.mm's (`sin0`, `cos0`, `sincos6thpi`, `sincos4thpi`,
  `sincos3rdpi`, `sinhalfpi`, `coshalfpi`). What a value lemma says,
  1/√2 for sin(π/4), is brought to the canon as any term is.
- **A logarithm difference not zero.** For D = Σ qₚ·ln p, N·D = ln P − ln Q,
  N the least whole number making each N·qₚ whole and P and Q whole
  numbers, is an identity; ln P − ln Q is ln(P/Q) (`relogdiv`), which is not
  zero because P/Q is not 1 (`logne0`, P/Q ≠ 1 by `arithmetic`); and D is
  not zero because N·D is not (`mulne0bad`).
- **An order.** L < R is 0 < R − L (`posdifd`, each side in ℝ as said
  once), and R − L is proved equal to the canon of D, its value, as for a
  disequality. 0 < D is then shown as the procedure found it:
  - D rational: by `arithmetic`.
  - D logarithms of primes: n·D = ln r is an identity and the logarithm
    above, ln r is above 0 because r is above 1 (`loggt0b`, r > 1 by
    `arithmetic`), and so is D, n being above 0.
  - D by brackets: each factor's bracket is proved. l < √p is l² < p by
    `arithmetic`, then √(l²) < √p (`sqrtltd`) and √(l²) = l (`sqrtsqd`),
    and √p < u likewise; 3 < π < 4 is `pigt3` and `pigt2lt4`, 2 < e < 3
    `egt2lt3`; and a/b < ln p is a < ln(pᵇ), ln(pᵇ) = b·ln p by the
    logarithm above, from eᵃ < 3ᵃ (`ltexp1dd`), 3ᵃ ≤ pᵇ by `arithmetic`,
    ln(eᵃ) = a, and `logltb`, and ln p < a′/b′ likewise. A product's
    bracket is its factors' (`ltmul12ad`), a power's its base's
    (`ltexp1dd`), a part's its coefficient's times its product's
    (`ltmul2dd`, and `ltnegd` where the coefficient is below 0), and the
    sum's its parts' added (`lt2addd`, `leltaddd`, `leidd` for the
    rational part). The sum of the lower ends is at least 0 by
    `arithmetic`, so D's whole part is above 0 (`lelttrd`), and D, over a
    denominator above 0, is too (`divgt0d`).

  L ≤ R is L < R weakened (`ltled`), or L = R where D is 0 (`eqled`); the
  denial of L < R is R ≤ L (`lenltd`), and of L ≤ R is R < L (`ltnled`).

### Held to an oracle

`tests/oracle.rs` draws claims of every form above, true by construction
and one coefficient away: √(s²·m) and s·√m, a value and its conjugate, one
over a + √p, products of roots, squares of sums of roots; equations,
disequalities and orders of terms three deep over the roots of two primes;
memberships of rational values and of values that are not; and each
refusal. It judges them with an evaluator of its own that shares nothing
with the procedure: exact rationals where there is no root, and otherwise
intervals with rational ends 1024 bits fine around each value, a value
being 0 where its interval holds 0 and is narrower than 2⁻⁵¹², and
rational where a fraction of denominator at most 10¹² lies inside it.
Each true claim must be proved and verified, and each refusal given in its
own words. The terms drawn stay inside the method's limits, and a claim
past them is drawn on purpose; on three seeds of 1500 claims it finds no
answer that differs from the judge's.

For π, e and logarithms the judge works by construction rather than by
intervals, since an interval cannot tell a false claim from one the method
does not decide. It draws polynomials in π, e and logarithms of primes and
expands them with polynomial arithmetic of its own, so an equation of a
polynomial and its expansion is true; logarithms and exponentials of
rationals whose values it knows from its own factoring; and each one moved
by a known amount, which is false where the move is rational or rational
multiples of logarithms, and not decided where it holds π or e. A third of
the claims are drawn so (`tests/oracle/atoms.rs`), and on three seeds of
1500 it finds no answer that differs from the judge's.

Sines and cosines of angles written in radians and in degrees are judged
from a table of their own, sin(n·π/12) for each n from 0 to 23 written out
as a value of roots, and not by the reduction above; the values are then
held to the method's answers as any value of roots is. A sine or cosine is
drawn into a claim over √2 and √3 only, which keeps the claim within the
limits; on three seeds of 1500 the answers agree with the judge's.

An order of values of roots is judged by the sign of the interval around
the difference of its sides, a gap narrower than 2⁻⁴⁰ taken as too large to
work out. An order holding π, e or a logarithm is judged by the rule of
Order written again over the judge's own polynomials: equal sides, a
rational difference, logarithms of primes by their ratio, and otherwise
the brackets above, set.mm's bounds on π and e and the logarithms' from
e's; and each sign the rule finds is held to the value worked out from π,
e and the logarithms to 35 digits. π and e are drawn against rationals near
their bounds, against each other, and logarithms against rationals and
against multiples of each other; on three seeds of 1500 the answers agree
with the judge's.

---

## membership

`2.3.  1/T(k) ∈ ℝ: membership, from D1, 2.2` — a term is in a number
system because its parts are. The method states as a step's claim what `algebra` and
`inequalities` already work out for every atom they touch, and it exists so
that a dull fact of this kind is one line rather than a climb up the term one
library item at a time. A term built from numerals and letters by +, −, ·, a
power to a numeral or to a letter in ℕ or ℕ₀, and / needs no line at all, since the page says it once
(`SYNTAX.md`); the method is for a term with a defined name, a function's
value, a sum, a remainder or a binomial coefficient in it.

### Facts in

The step's requires lines and the lines it cites, read for what they say
(`SYNTAX.md`: `let k ∈ ℕ` also says k ∈ ℝ and k ≠ 0); a requires line's are
the lines its reason names and the requires lines above it. A defined name
is read as its rule, T(k) as k(k + 1)/2, where the step cites its define, as
it is wherever a formula is compared: `1/T(k) ∈ ℝ: membership, from D1, 2.2`,
where 2.2 says k(k + 1)/2 ≠ 0. A type the step cites, `a : {1, …, n} → ℝ`,
says a(k) ∈ ℝ where k is in {1, …, n}: a function's type is cited for its
values (`READERS.md`). Inside a sum's terms a type in scope says it too,
since a term at each index is no value the page writes.

A cited equation with the term on one side says the term is in whatever the
other side is in, as a reader takes a(0) = 0 to say a(0) is a number:
`a(0) ∈ ℝ: membership, from 1`, where line 1 says a(0) = 0, and
`a(k + 1) ∈ ℝ: membership, from 4.1, IH`, where 4.1 gives a(k + 1) as a
term in a(k) and b(k) and the induction hypothesis says those are real.

This test is the one every method's side conditions are asked by: an
`algebra` or `inequalities` step whose atom is a(0), citing a(0) = 0, has
a(0)'s membership as this method would, and needs no line saying it. The
methods differ in what they conclude, not in how a side condition is met.
The equation is one the step names, so the membership it gives is still one
the page shows.

### Fact out

`t ∈ S`, with S a number system; or "for all k ∈ X, t ∈ S", which is
proved as a `proof` block would prove it: k is taken in X, what that
membership says is laid beside the other facts in, and t ∈ S is proved of
it. One fact, as a step says one thing: `x(n) + 1 ∈ ℝ. x(n) − 1 ∈ ℝ.` is
two steps, and so is `x(n) + 1 ∈ ℝ and x(n) − 1 ∈ ℝ`; both tools refuse
either as one.

### The procedure

The term is walked by the operation at its head, as `algebra` walks it:

- a sum, difference, product or power is in S when its parts are
  (`readdcld`, `remulcld` and the rest of the closure table), a power's
  exponent in ℕ₀: 2^j ∈ ℤ where j ∈ ℕ₀;
- a negation is in S when what it negates is, for S that holds negatives;
- a quotient is in ℚ, ℝ or ℂ when its parts are and its divisor is not zero,
  which a cited line says by saying it, or by saying the divisor is above
  zero or below it (`gt0ne0d`, `lt0ne0d`): −B/A ∈ ℝ from A > 0;
- a remainder a mod b is in ℕ₀, and so in ℤ, ℚ, ℝ and ℂ, when a is in ℤ and
  b in ℕ (`zmodcl`): (t + 1) mod 10 ∈ ℤ from t ∈ ℤ, the divisor a numeral
  asking nothing, as a binomial coefficient C(n, k) is in ℕ₀ when n is in ℕ₀
  and k in ℤ (`bccl`);
- a sum over a range {a, …, b} is in ℝ or ℂ when its term is, for each index
  in the range (`fsumrecl`, `fsumcl`); the index is in ℕ where the range
  starts at 1, by the table of `SYNTAX.md`. A cited line saying the term at
  every point of a set holding the range says it, whatever the term:
  `Σ(j = 1 to m) q(j) ∈ ℝ` from a line saying for all j ∈ {1, …, m},
  q(j) ∈ ℝ. A term dividing by something that holds the index has a divisor
  no line outside the sum can say is not zero, so only such a line says it:
  `Σ(k = 1 to n) 1/k ∈ ℝ: membership, from 4`, where 4 says for all k ∈ ℕ,
  1/k ∈ ℝ;
- a term by cases, what a define by cases writes out to, is in S when each
  of its values is: s(x) ∈ ℕ₀ where s is 0 or 1;
- anything else is an atom, and its membership is a line the step cites or
  writes, or for a letter the line introducing it, carried to S by at most one
  lemma (`nnre`, `zcn` and the rest), or
  a cited equation with the atom on one side, the other side's membership
  read the same way and carried across by `eqeltrd`.

A divisor is not zero when a line says so, as `d ≠ 0` or as a sign, when it
is a numeral other than zero, or when it is a product, a quotient, a
negation or a power to a numeral whose parts are each not zero by this same
test (`SYNTAX.md`, `mulne0d`, `divne0d`, `negne0d`, `expne0d`); one built in
ℕ, k + 1, says so in a line of its own.

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

The closure lemmas the table names, `divcld`, `redivcld` and `qdivcl` for
quotients (set.mm states ℚ's in closed form, `qaddcl` and the rest, and
`syl2anc` discharges them), `gt0ne0d` and `lt0ne0d` for a divisor's
disequality said as a sign, `rspcv` for a sum's term read off the line saying
it at every point, and where the claim
names a define, the claim read as its rule and carried back by the equation
the define gives (`mpbid`).

### Held to an oracle

`tests/oracle.rs` draws terms of function values, powers to a letter,
remainders, letters and numerals, built by the operations of the table.
It works out the least of ℕ, ℕ₀, ℤ, ℚ, ℝ and ℂ the table puts each in, a
term of numerals alone at its value, and claims the term in one of the
six. The method proves a claim of that system or a larger one, and refuses
one smaller.

## inspection

`{x ∈ E : A is incident with x} = {a, b, c, d, e}: inspection, from H1` — a
claim about a set listed in full, checked element by element against what
the cited lines say. A textbook writes "by inspection" and its reader runs
down the list; the page does the same, and the cases are not written
(`READERS.md`, "What is seen by inspection").

The method is named for what the reader does, not for a subject: the
Königsberg graph is its first use, and nothing in it knows about graphs.

### Facts in

A set the claim itself writes in full, `|{1, 2}| = 2` or `4 ∉ {1, 2, 3}`,
is listed where the reader sees it, and the step cites nothing for it. Two
numerals differ by their values, which no line need say. Otherwise, the
lines the step cites, read for six kinds of sentence and nothing else:

- **a set listed in full:** an equation `S = {s₁, …, sₙ}`, or a `let` line
  that names a set by listing it, as "the multigraph with distinct vertices
  V = {A, B, C, D} and distinct edges E = {a, …, g}" names its vertices
  and its edges;
- **where a thing lies:** a membership `t ∈ S`, which a line of "or"s
  (below) is read against;
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
- a range `{a, …, b}` whose ends work out to integers, as `arithmetic`
  works one out, is the list of
  the integers from a to b, and none where b is below a: `{0, …, 3 − 1}`
  lists 0, 1 and 2, `{−2, …, 0}` lists −2, −1 and 0, and `{1, …, 0}`
  nothing. A range is read so only up to 64 numerals, past which a list of
  its elements is not one a reader runs down;
- the size `|S|` of such a set, once the facts say its names are distinct,
  is the numeral that counts them, a name written twice counted once:
  `|{2, 3, 2}| = 2`;
- a term spelt with numerals alone is itself;
- a term a cited "for all" equation gives at a listed element is what the
  other side works out to there.

So `{x ∈ E : A is incident with x} = {b₁, b₂, b₃, b₄, b₅}`, `|{b₁, b₂, b₆}| = 3`
and `deg(B) = 3` are one method, which works out both sides and compares
them.

Or a line of "or"s, `t = s₁ or t = s₂ or … or t = sₙ`, from a cited line
`t ∈ S` where S is a set the facts list: the line says which element of S
t is, and so splits S into its cases for `cases` to take one at a time.
A set of one element gives a line of one equation: `x = 3` from
`x ∈ {3}`, or from `x ∈ {3, …, 3}`. An equation is read so wherever a
cited line puts one of its sides in a listed set, and otherwise as an
equation of two things worked out, above.

```
5.1.  n mod 3 ∈ {0, …, 3 − 1}
      mun:range-from-bounds, from 4

5.2.  n mod 3 = 0 or n mod 3 = 1 or n mod 3 = 2
      inspection, from 5.1

5.3.  …
      cases, from 5.2
```

The line has one equation for each element of S and none for anything
else, in any order and grouped however its parentheses group it. Each
equation is `t = s` or `s = t`, s being the element as the listing writes
it or a term of numerals alone of the same value: `k = 1 + 2` is the
equation for the 3 of `{0, …, 4}`. The cited line is the first that says t
is in a set, for the t each equation names.

Or `t is prime`, or its denial, where t is a number spelt in numerals or
one a cited line gives such a value: `97 is prime`, `not (91 is prime)`.
The reader tries the primes up to 23 and finds none divides 97, which is
below 23²; and finds 7 divides 91. The record of `prime` names
`inspection` in its `decided` field.

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
A size is the length of the list once the facts say its names are distinct,
a name written again counting nothing.
A term a "for all" line gives is read at the listed element it names, and
what the line's other side says there is worked out the same way. Two sets
are compared as sets, so their order is never asked, and two numbers by
working out the sum that counts one against the other.

A line of "or"s is read against its cited membership `t ∈ S`, the first
cited whose t every equation names and whose S the facts list: S is
replaced by its listing, each element is matched with the equation that
names it, and each equation with the element it names, two numbers being
one where their values are. No element is settled, and no two names need
be said to differ: t is one of the elements, whichever it is, and the line
says no more than that.

### Refusals

- **A set not listed in full**, by a cited line, or a range or a set-builder
  the facts do not list: `inspection` checks a finite list a reader can see,
  and nothing it has to find. A range whose ends are not integers worked
  out from numerals, `{0, …, n}` or `{1/2, …, 1}`, is not listed, and the
  refusal says so.
- **A range of more than 64 numerals.** `{1, …, 100}` is a list of a
  hundred, which no reader runs down by eye.
- **A line of "or"s that is not the listing:** one that leaves out an
  element of S, or names something S does not list. `n mod 3 = 0 or n mod
  3 = 1` does not follow from `n mod 3 ∈ {0, …, 2}`, which leaves 2 open;
  `n mod 3 = 0 or n mod 3 = 1 or n mod 3 = 2 or n mod 3 = 5` does, but it
  is not the list the reader runs down, and a case for 5 is one `cases`
  would ask the writer to settle for nothing.
- **A property that does not come down to listed membership** through what
  the cited lines say, nor to a word its record lets `inspection` decide at a
  value the lines give: an element whose case needs a lemma, a calculation or
  a reason of its own is a case to write, and `cases` writes it.
- **Two names not said to differ**, where the answer depends on it.
- **A prime of 841 or more**, which trial division by the primes up to 23
  does not settle. That a larger number is not prime is still seen, by its
  least factor.
- **A search.** Only the claim and the cited lines are read, never the
  scope.

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
its distinctness, and one written already leaving the union as it was
(`ssequn2`); the empty set's is `hash0`. A prime is `2prm`, `3prm`,
`prmlem1` below 25 or `prmlem2` below 841, each non-division by `ndvdsi`
at the quotient and remainder; a number that is not prime is `0nprm`,
`1nprm`, or `nprmi` at its least factor; and the number is carried back to
the term as written by `eleq1i`, or `eleq1d` where a cited line gives it. A "for all" line is read
at its element by `rspcdva`. The two sides are joined by `eqtrd` and
`eqtr4d`, two listings in different orders by `eqssd`.

A range of integers is its ends worked out, each an equation `arithmetic`
proves (`closed_fact`), carried in (`oveq12i`), and then built up an
integer at a time: the range of one integer is its singleton (`fzsn`), and
a longer one the range below its top joined with the top's singleton
(`fzsuc`, the top ≥ the bottom by `eluz2`); a range whose top is below its
bottom is empty (`fzn`). What each asks of the integers, that each is one,
their order, and that one less plus one is the top, is a closed fact of
numerals `arithmetic` proves, −2 + 1 = −1 as 1 + 1 = 2. A line of "or"s puts t in the union of the
singletons (`eleqtrd`) and follows from each: t ∈ {s} gives t = s
(`elsni`), turned to the equation as the line writes it (`eqeq2d` with a
closed numeral fact, `eqcom`), and the equation widens to the whole line
(`orc`, `olc`). The singletons are joined by `elun` and `jaod`, and the
line drawn by `mpd`.

### Held to an oracle

`tests/oracle.rs` draws sets of numerals a claim writes, with a
membership, a size, two listings compared, and the members "is even" or
"is odd" holds of and how many; and a multigraph a `let` line lists, with
the edges at a vertex, how many, and memberships. It works out each set
itself, and the method proves what holds and refuses the rest.

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

The block uses its supposition: some step under it, or a requires line of
one, cites it. A block that reaches a contradiction without it shows that
the lines above it contradict each other, and supposing the claim false
plays no part in that; it is refused.

### Facts in

The block's supposition, which asserts nothing outside the block, and the
block's last step, which reaches the opposite of an earlier line and names it,
`contradicting 3.6`, or reaches a closed fact that cannot hold and says
so, `2 ≤ 1, which is impossible`, or `√2 = 1, which is impossible`. The second is how a reader ends the
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
is worked out, by `real arithmetic` where it holds a square root, π, e, a
logarithm or an exponential and by `arithmetic` otherwise, and its denial,
which that method proves, stands in for the line. The claim must name
nothing but a library function, ln in ln 2, as those methods' claims must,
and the method must decide it false; one it finds true, cannot work out,
or does not decide (10 divides 1, a relation `arithmetic` does not have)
is refused, and the step names a line it contradicts instead. A case that cannot occur
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
to a letter (`2^p − 1 ∈ ℤ`), a function's value, an angle in the geometry
proofs, a sum, |x|, a remainder, C(n, k) and a defined name.
