# Which geometry this project should stand on

`proofs/wiedijk/isosceles.proof`, `proofs/wiedijk/angle-sum.proof` and
`proofs/wiedijk/pythagoras.proof` are the corpus's geometry proofs. What they stand on is a question about foundations rather
than about tools, and seven answers have been looked at: the complex plane, Tarski, `EE^n`, Hilbert, Birkhoff,
SMSG, and Euclid's own axioms as Beeson, Narboux and Wiedijk formalised them.

This document settles it against criteria taken from `GOALS.md` and
`READERS.md` rather than against a judgement about geometry. The answer is
the complex plane, and the proof elaborates to a file that assumes nothing.

## The criteria, and where each comes from

**1. The backend adds no mathematical axioms.** `GOALS.md`, on what is kept
from Metamath: *"No mathematical axioms in the kernel. The foundation is a
library."* The corresponding measure in practice is the list at the head of
an elaborated file. Every proof in `corpus/elaboration/proofs/` states what it assumed
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

**4. Dull facts are written.** `READERS.md` lets the page say one kind
once, a membership in a number system, where a letter is introduced, and no
other. So whatever non-degeneracy a backend demands is written on the page,
every time, and counts against it.

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

**Taken.** The complex plane, with the angle defined unsigned and the plane
written `𝔼²` on the page. What follows is why, and what it waits on.

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

So the unsigned angle makes `mun:stdlib/geometry/angle-symmetric` true *and* keeps
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
  sort        → set of point
  reads       the Euclidean plane
  metamath    cc, the complex numbers read as the plane
  target      cc
```

`𝔼²` is the established notation for the Euclidean plane as a geometric
object, distinguished from ℝ² or ℂ as algebraic ones, which is the
distinction being drawn. `mun:stdlib/geometry/point` then states `A is a point ↔ A ∈ 𝔼²`,
every dull fact reads `requires A ∈ 𝔼²`, and ℂ appears nowhere above the
`target` field. `mun:stdlib/numbers/irrational` is the precedent one level up: it names a
word for `ℝ ∖ ℚ` rather than introducing a symbol.

One thing to watch. `𝔼²` and `ℂ` are the same object in the kernel, so
nothing in the terms stops a text writing `A · B` for two points. What stops
it is the sort system — `point` and `number` are different sorts — and the
`distance` record already leans on exactly that to keep `|CA|` from parsing
as a product. The guard exists and has to cover the new notation too.

A point may be written by its coordinates. Where a point is wanted, `(x, y)`
is the point with those coordinates, which the kernel holds as x + i·y
(`point-coordinates`); `A = (1, 2)` and `|(0, 0)(3, 4)|` say nothing of ℂ, as
the rest of the page does not.

**A triangle is a phrase, △PQR, and not an object.** Notations write it as a
school book does: `△PQR is isosceles`, `△PQR is equilateral`, `△PQR is
right-angled at R`, and `△PQR ≅ △P′Q′R′` beside `triangle PQR ≅ triangle
P′Q′R′`. Each stands for a formula of its three points that includes their
forming a triangle, and its definition is `biid`. "Right-angled at V" says V
is one of the vertices and the angle there is 90°, whichever V is;
`mun:stdlib/geometry/right-angled-at-vertex` reads it at the vertex written
last, which is how a proof names it. No sort holds triangles, so a statement
about every triangle quantifies over its three points.

**Lines, midpoints and circles are said of points.** `P is on line AB` is
`A, B, P are collinear` with the point first. `line AB ⊥ line CD` says A ≠ B,
C ≠ D and that the quotient of the two directions has real part 0. Like
`parallel`, it is an `open` definition, read as a right angle by
`perpendicular-by-right-angle` where the lines meet. `M is the midpoint of AB`
says M is between A and B and |AM| = |MB|, a `biid` definition. The kernel's
(A + B)/2 is reached inside `gmidval` and never written. A circle is a set of
points named once, `let ω = {X ∈ 𝔼² : |XO| = r}`, and "A is on ω" is A ∈ ω.
The chord theorems state the circle by distances to its centre.

**Coordinates, the special angles and the triangle's elementary facts are
records.** The distance between points given by coordinates is
distance-by-coordinates, and three such points are collinear, or one between
the others, by collinear-by-coordinates and between-by-coordinates. Two such
points differ just where their pairs of coordinates do
(points-apart-by-coordinates), and `arithmetic` compares the pairs
(`METHODS.md`, Pairs). A distance is never negative, and positive between two
points; a point between two others is apart from both (between-apart). cos 90°,
sin 90°, cos 60° and sin 30° are one record, and angle-by-cosine reads an angle
from its cosine on [0°, 180°]. The triangle inequality for points is set.mm's
`abs3dif`. Its equality case and strict form, supplementary angles and the
addition of angles are proved in `corpus/proved/plane.proved`, since set.mm
states none of them over ℂ.

**The signed angle is a second notation, ∡PQR, beside ∠PQR.** It is `ang`
itself, in (−π, π] and positive counterclockwise. ∠PQR stays unsigned, and
|∡PQR| = ∠PQR is one kernel term. The angle sum by orientation (`ang180`) and
the area need it.

**The area of △PQR is set.mm's own term.** `heron` writes the area as
(1/2)·(|QR|·|PR|)·|sin(∡QRP)|, which is the notation's target, so Heron's
formula is cited as set.mm states it. `area-by-sine` gives the school form,
with ∠QRP.

### What it costs, honestly

**Non-degeneracy, and criterion 4 writes all of it.** `angval` wants both
arguments non-zero, `ang180` wants three points pairwise distinct, `lawcos`
wants two. Synthetic geometry says "A, B, C form a triangle" once and passes
it whole; over ℂ the phrase is taken apart and the pieces cited at each
angle, which `isosceles` would do about sixteen times across twelve steps.

That is an ordinary dull-fact load and not a reason against ℂ: about 1.3
lines a step, each a fact that can fail where the points coincide.

**A triangle is its three points, in no order, and so is a line through
three points.** "A, B, C form a triangle" and "C, A, B form a triangle" are
one claim: the three are distinct and not on one line, whichever is named
first. "A, B, C are collinear" is likewise one claim in any order. It means
A = B, or (C − A)/(B − A) is real, which is true just where the three lie on
one line, two of them coinciding included. Both notation records say
`commutes yes`, and the checker matches their holes in any order. The
elaborator carries a triangle from one order to another by `gtriswap` and
`gtrirotate`, and a collinearity by `gcolswap` and `gcolrotate`, whether the
line is one a proof holds or a record's conclusion. So
an item that needs its three points to form a triangle says so in that
phrase, `mun:stdlib/geometry/angle-symmetric` among them, and a proof cites
its own triangle line for it in whatever order it names the points. Order
matters only where a statement says which vertex is which, as "triangle ACB
≅ triangle BCA" does, and that is another notation.
Distinctness of an angle's points is exactly what the `requires` machinery is
for, and it is not a membership the page says once.

Two things do need doing, both one-off. The geometry items do not state the
hypotheses they need: `mun:stdlib/geometry/angle-symmetric` reads `let P be a point` three
times and `then ∠PQR = ∠RQP`, with no disequality anywhere, and the same
holds of `axi:stdlib/geometry/side-angle-side` and `def:stdlib/geometry/congruent`. Those statements are
incomplete as written and would be whatever backend was chosen. And `A ≠ C`
against `C ≠ A` is `necom`, which belongs in `rules.MEMBERSHIP` beside
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
| `notation is-a-point` | `target _1 cc wcel`, read as `∈ 𝔼²` |
| `notation distance` | `target` the absolute value of a difference |
| `notation angle` | `target` the absolute value of `ang` |
| `mun:stdlib/geometry/point` | `A is a point ↔ A ∈ 𝔼²` |
| `mun:stdlib/geometry/angle` | the unsigned angle, and why it is unsigned |
| `mun:stdlib/geometry/triangle` | the three disequalities |
| `def:stdlib/geometry/congruent` | three sides and three angles, as it already reads |
| `mun:stdlib/geometry/distance-symmetric` | `abssub` |
| `mun:stdlib/geometry/angle-symmetric` | provable from `arginv`, with the cut as a case |
| `axi:stdlib/geometry/side-angle-side` | provable, or the proof rerouted through `isosctr` |

Three of the items gain the disequality hypotheses they presently omit, and
`necom` joins the membership list.

Six `open` markers cleared.

## What it took

`mun:stdlib/geometry/angle` is the first definition in this corpus that introduces a symbol,
and the corpus emits it: `definitions.mm` declares `ang` and `df-ang`, which
is decision 12 of `GOALS.md` exercised for the first time. Inlining the
function instead would have worked and would have left the one definition
this corpus introduces unchecked, which is the thing that decision exists to
prevent.

That choice paid for itself immediately. `lawcos` takes the angle function as
a hypothesis, and the function it takes is `df-ang` to the token, so the law
of cosines applies with the hypothesis discharged by the corpus's own
definition. Had the angle been inlined at each mention, or spelt any other
way, it would not have.

Four items needed theorems set.mm does not have and the readable layer cannot
state, since saying what they say means dividing one point by another and
naming the branch cut of the complex logarithm. They are proved below the
readable layer, in `corpus/elaboration/stdlib/proved.mm`, which is a third way to supply
an item alongside a set.mm label and a proof file:

| lemma | carries |
| --- | --- |
| `gtriswap` | swapping two vertices inverts the collinearity quotient |
| `gtrirotate` | rotating them takes it to `1 − (C−B)/(A−B)` |
| `gcolswap` | collinearity holds with the last two points swapped |
| `gcolrotate` | collinearity holds with the points rotated |
| `gtridef` | a triangle is three distinct points not collinear |
| `gangsym3` | the two directions of an angle have one size |
| `gsas` | side-angle-side |

`gsas` is the law of cosines at each of three vertices in each of two
triangles, six applications which are cyclic rotations of one lemma. It holds
because the angle is unsigned: `cos11` is one to one on `0` to `π` and on
nothing wider, so a signed angle could not be recovered from its cosine. The
choice that makes `mun:stdlib/geometry/angle-symmetric` true is the same one that makes
side-angle-side provable.

The angle sum's three items are proved the same way, in their own block of
`proved.mm`:

| lemma | carries |
| --- | --- |
| `gparthru` | `parallel-through`: D = B + (A − C) and E = B + (C − A), and each side condition |
| `galtang` | `alternate-angles`: the angle at one end is the angle at the other, read back |
| `gline` | `angles-on-a-line`: three angles along a line add to 180° |
| `gargsum` | three numbers on one side of the real line, with a negative real product, have argument sizes adding to π |
| `gargpos` | the same above the line, from `eflogeq` and the bounds on each argument |
| `grecsgn` | 1/Z is on the other side of the real line from Z |
| `gangrp` | lengthening one arm of an angle leaves it unchanged |

Pythagoras, proved by similar triangles, adds a block of its own. Similarity
itself is a theorem of the readable layer, from the angle sum and the law of
sines; these are what it and the proof cite:

| lemma | carries |
| --- | --- |
| `glawsin` | `law-of-sines`: `heron` at two vertices of one triangle, the same area |
| `gsinpos` | `sine-positive`: an angle of a triangle is strictly between 0 and π |
| `galtfoot` | `altitude-foot`: the foot of the altitude from a right angle, between the other two vertices |
| `gangseg` | `angle-along-segment`: a point between P and Q is on the ray from P through Q |
| `gsegadd` | `segment-addition`: the parts of a segment add to it |
| `gbetsym` | `between-symmetric` |
| `gsinabs` | the sine of an angle's size is the size of its sine, between −π and π |
| `g90` | 90° is π/2 |

`galtfoot` puts each point at a coordinate along PQ, P at 0 and Q at 1, so
that every quotient of differences it names is a quotient of coordinates.

## The angle sum, which adds angles

The angle sum is the second geometry proof, and the first that adds angles,
which the section below said should be weighed before it was written. It is
the school proof: draw the line DE through B parallel to AC, read ∠DBA =
∠BAC and ∠EBC = ∠BCA as alternate angles, and see ∠DBA + ∠ABC + ∠EBC make
the straight line DE, 180°.

**The unsigned angle stays.** Adding unsigned angles needs to know which
way round they lie, and that is what it cost: the proof writes out what a
figure shows, that D and C are on opposite sides of line BA, E and A on
opposite sides of line BC, and A and C on the same side of line BD. Those
come with the parallel (`axi:stdlib/geometry/parallel-through`) and are
cited where the angles are added. A signed angle would not need them, and
would lose `angle-symmetric` and side-angle-side, which `isosceles` stands
on. The sides are three sentences in one step; the symmetry is everywhere.

**What a side is, over ℂ.** Which side of the line through P and Q a point X
is on is the sign of the imaginary part of (X − P)/(Q − P). Two points are on
the same side when the two signs multiply to a positive number, and on
opposite sides when to a negative one. Lines are parallel when the quotient
of their directions is real, and R is between S and T when (T − R)/(S − R)
is a negative real. All three are notations with targets and definitions
the readable layer cannot state, as `collinear` is.

**Why the sum is 180°.** The three angles at B are the arguments of three
quotients whose product is (E − B)/(D − B), a negative real. Their
arguments therefore add to π up to whole turns, and the side conditions put
all three quotients on one side of the real line, so each argument is
between 0 and π and the sum is π exactly. set.mm's `ang180` is the same
fact for a triangle, signed, which is why it says π or −π.

**Degrees on the page.** The page writes 180°, the reader's unit. ° is a
notation, x° being x·π/180; the angle is still the number from 0 to π that
`mun:stdlib/geometry/angle` defines, and `isosceles` is unchanged.

The three items and the lemmas under them are listed above, under "What it
took".

## What would change the answer

**A proof that adds angles everywhere.** The angle sum adds once, and its
side conditions are three sentences of one step. A proof that adds and
reverses angles at every step would write sides at every step, and would be
the case for weighing a signed angle again.

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
