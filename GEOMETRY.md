# Which geometry this project should stand on

`proof/isosceles.proof` is the one proof in the corpus that does not
elaborate, and six of the seven items it cites are marked `open`. That is a
question about foundations rather than about tools, and seven answers have
been looked at: the complex plane, Tarski, `EE^n`, Hilbert, Birkhoff, SMSG,
and Euclid's own axioms as Beeson, Narboux and Wiedijk formalised them.

This document settles it against criteria taken from `GOALS.md` and
`READERS.md` rather than against a judgement about geometry.

## The criteria, and where each comes from

**1. The backend adds no mathematical axioms.** `GOALS.md`, on what is kept
from Metamath: *"No mathematical axioms in the kernel. The foundation is a
library."* The corresponding measure in practice is the list at the head of
an elaborated file. Every proof in `elaboration/auto/` states what it assumed
and why, and the work of the last eight proofs has been to shorten those
lists; `cantor.mm` assumes nothing. A backend that enters as an axiom system
makes the corpus's geometry permanently assumed, which is the opposite
direction.

**2. Every construct has something below it.** Design decision 1, *"Growth
lives above the kernel"*. A notation needs a `target`; an item without one is
stated and listed. A backend that leaves five notations and six items with
nothing to point at has not been adopted, only named.

**3. The language is Reader A's, and the backend fits the text.**
`READERS.md`: *"The language is Reader A's"*, and Reader A's background is
*"algebra, functions, basic geometry"*. `∠CAB = ∠CBA` is how that reader
writes the isosceles theorem. A backend that cannot say it is asking the text
to change, which is a corpus decision and a cost, not a neutral choice.

**4. Dull facts are written, and membership merits no exception.**
`READERS.md` argues this at length and records the price: *"97 membership
lines across the 42 steps"* citing `algebra` or `inequalities`, one step
carrying ten. The exemption *"was rejected"*. So whatever non-degeneracy a
backend demands is written on the page, every time, and counts against it.

**5. An expansion emits citations of library theorems.** `GOALS.md` on step
counts: an expansion *"has to emit citations of library theorems, exactly as
a stored proof does. An expansion that inlined its way to the axioms would be
unusable."* A backend needs proved theorems above it, not only primitives.

**6. Expansion terminates.** Design decision 5.

## What the criteria eliminate

**Criterion 1 cuts the field from seven to three.** This is the decisive one
and it is easy to misread, because four of the seven are axiom systems and
three are not — but not along the line one expects.

`TarskiG` is **not** an axiom set the corpus would assert. `df-trkg` is a
definition: it names the class of structures satisfying certain conditions,
and every theorem about a `G e. TarskiG` is proved. `eengtrkg` then proves a
member of that class exists. So Tarski, `EE^n` and the ℂ development are all
definitions plus proved theorems in set.mm, and cost nothing on criterion 1.

Hilbert, Birkhoff, SMSG and Euclid are none of them in Metamath. Each would
enter either as a development of comparable size to Tarski's — Beeson,
Narboux and Wiedijk needed 235 theorems to cover Euclid's 48 propositions —
or as assumptions the corpus states and never discharges. The first is out of
proportion to one proof; the second is the thing this project spends its
effort avoiding.

That Birkhoff and SMSG are *metric*, which is what makes them look like the
answer, does not save them. Birkhoff's angle measure is signed mod 2π, with
the `±` written into his similarity postulate, so `∠CAB = ∠CBA` is false
there as it is over ℂ. SMSG's is the school reader's angle, 0° to 180°, and
is twenty-two postulates chosen for teachability rather than independence.

**Criterion 5 cuts `EE^n`.** Scanning all 50,919 labelled statements in
set.mm: no statement mentions `EE ` 2`, none relates `CC` to `RR ^m`, and
`EEhil` is named seven times of which five are about topological manifolds.
`EE^n` connects upward to Tarski by `eengtrkg` and to nothing else. Taking it
means writing the plane geometry — the angle, its symmetry, a law of cosines
in an inner product space, side-angle-side — from `ipcau` and `CPreHil`
upward. That is a chapter, and criterion 5 is exactly the objection: there
would be no library theorems to cite.

**Criterion 3 decides between what is left.** Tarski has no angle measure at
all. `cgrA` is a relation, `AngMgm` adds angles without measuring one, and
there is nothing to put either side of an `=`. Adopting Tarski means the
readable layer says angles are *congruent* rather than equal, which changes
the theorem statement and five of the twelve steps.

## The answer

**The complex plane, with the angle defined unsigned.**

```
∠PQR  :=  ( abs ` ( ( P − Q ) F ( R − Q ) ) )
|PQ|  :=  ( abs ` ( P − Q ) )
```

where `F` is set.mm's `ang`. It is the only candidate that passes all six:
it adds no axioms, every notation gets a target, the readable text is
unchanged, and the theorems to cite are already written.

### Why the unsigned angle is cheap here, which was not obvious

The objection recorded against it was that taking `abs` costs `isosctr` and
`ang180`, since both are stated with the signed `F`. For `isosctr` that is
wrong, and the reason is worth setting down.

`isosctr` concludes

```
( ( C - A ) F ( B - A ) ) = ( ( A - B ) F ( C - B ) )
```

The corpus's two angles are `∠CAB = abs ( ( C - A ) F ( B - A ) )` and
`∠CBA = abs ( ( C - B ) F ( A - B ) )`. The second differs from `isosctr`'s
right side by the order of its arguments, and `arginv` gives
`( Im ` ( log ` ( 1 / A ) ) ) = -u ( Im ` ( log ` A ) )` — the argument is
antisymmetric. So the two sides of `isosctr` are negatives of the corpus's
two angles, and taking `abs` of both sides yields `∠CAB = ∠CBA` exactly as
the text writes it.

So the unsigned angle makes `thm:angle-symmetric` true *and* keeps
`isosctr`. Both, from one definition.

What it costs is `arginv`'s side condition: the argument is antisymmetric off
the branch cut, and on the cut both directions are π. `abs` is insensitive to
the difference, so the lemma is true unconditionally — but proving it means
handling the cut as a case, which is the one piece of real work.

### The plane is 𝔼² on the page and ℂ in the kernel

A point is a complex number in the kernel and must not be one on the page.
`GRAMMAR.md` states the rule: the readable layer "hides class variables,
set-existence hypotheses and the set-theoretic apparatus from the reader",
and "a reader with school mathematics is not meant to learn that 2 is a pair
of nested empty sets". A dull fact reading `A ∈ ℂ` is that leak, in the same
category as `2 = {∅, {∅}}`, and the same section names the remedy: "the fix
is a database addition, not a redesign".

The addition is one notation, in the shape `number-systems` already uses:

```
notation plane
  pattern     𝔼²
  holes       none
  yields      set
  reads       the Euclidean plane
  metamath    cc, the complex numbers read as the plane
  target      cc
```

`𝔼²` is the established notation for the Euclidean plane as a geometric
object, distinguished from ℝ² or ℂ as algebraic ones, which is the
distinction being drawn. `def:point` then states `A is a point ↔ A ∈ 𝔼²`,
every dull fact reads `requires A ∈ 𝔼²`, and ℂ appears nowhere above the
`target` field. `def:irrational` is the precedent one level up: it names a
word for `ℝ ∖ ℚ` rather than introducing a symbol.

One thing to watch. `𝔼²` and `ℂ` are the same object in the kernel, so
nothing in the terms stops a text writing `A · B` for two points. What stops
it is the sort system — `point` and `number` are different sorts — and the
`distance` record already leans on exactly that to keep `|CA|` from parsing
as a product. The guard exists and has to cover the new notation too.

### What it costs, honestly

**Non-degeneracy, and criterion 4 writes all of it.** `angval` wants both
arguments non-zero, `ang180` wants three points pairwise distinct, `lawcos`
wants two. Synthetic geometry says "A, B, C form a triangle" once and passes
it whole; over ℂ the phrase is taken apart and the pieces cited at each
angle, which `isosceles` would do about sixteen times across twelve steps.

That is an ordinary dull-fact load and not a reason against ℂ. `READERS.md`
records the arithmetic load the corpus already pays without complaint — 97
lines across 42 steps, one step carrying ten — which is about 2.3 a step
against geometry's 1.3. Distinctness of an angle's points is exactly what the
`requires` machinery is for.

Two things do need doing, both one-off. The geometry items do not state the
hypotheses they need: `thm:angle-symmetric` reads `let P be a point` three
times and `then ∠PQR = ∠RQP`, with no disequality anywhere, and the same
holds of `thm:side-angle-side` and `def:congruent`. Those statements are
incomplete as written and would be whatever backend was chosen. And `A ≠ C`
against `C ≠ A` is `necom`, which belongs in `targets.MEMBERSHIP` beside
`nnz` and `zre` — a side condition the text never writes, settled by the
elaborator. No reader should meet a `requires C ≠ A` under a page that says
`A ≠ C`.

**Angle addition.** `∠ABD + ∠DBC = ∠ABC` holds unconditionally for signed
angles and needs a betweenness hypothesis for unsigned ones. Choosing
unsigned buys symmetry and pays here. It is not a defect of ℂ — SMSG's own
Angle Addition Postulate carries the same hypothesis — but a proof that both
adds and reverses angles pays at each step, and no proof in the corpus does
yet.

**Dimension.** ℂ is the plane and nothing else, permanently. Tarski and
`EE^n` generalise.

**Against which**, two things are better than any synthetic backend:
similarity is multiplication, and orientation is free. And the section is
finished rather than a starting point — `lawcos`, `pythag`, `isosctr`,
`chordthm`, `heron`, `ang180`, and `affineequiv1` through `affineequiv4` with
`angpieqvd`, which are betweenness and collinearity already done.

## What the corpus would state

| entry | becomes |
| --- | --- |
| `notation plane` | new: `𝔼²`, `target cc` |
| `notation point` | `target _1 cc wcel`, read as `∈ 𝔼²` |
| `notation distance` | `target` the absolute value of a difference |
| `notation angle` | `target` the absolute value of `ang` |
| `def:point` | `A is a point ↔ A ∈ 𝔼²` |
| `def:angle` | the unsigned angle, and why it is unsigned |
| `def:triangle` | the three disequalities |
| `def:congruent` | three sides and three angles, as it already reads |
| `thm:distance-symmetric` | `abssub` |
| `thm:angle-symmetric` | provable from `arginv`, with the cut as a case |
| `thm:side-angle-side` | provable, or the proof rerouted through `isosctr` |

Three of the items gain the disequality hypotheses they presently omit, and
`necom` joins the membership list.

Six `open` markers cleared.

## What would change the answer

**A second geometry proof that adds angles.** One proof needing
`∠ABD + ∠DBC = ∠ABC` alongside symmetry would make the unsigned choice
painful rather than free, and would be worth weighing before a second proof
is written rather than after.

**Wanting solid geometry.** ℂ cannot. That is the one requirement it cannot
be stretched to meet, and it would force `EE^n` and the chapter of work that
goes with it.

**A geometry corpus rather than a geometry proof.** If the aim were a body of
Euclidean proofs read the way Euclid wrote them, the relevant prior art is
not an axiom system but the area method, whose proofs are short and readable
by design and which has a literature on measuring exactly that. That is a
different project and it does not bear on this one proof.

**Someone formalising SMSG.** It is the only system whose angle is the school
reader's by axiom, and nobody has built it. If it existed, criterion 3 would
favour it and criterion 1 would still not, since it would be twenty-two
postulates the corpus asserts.
