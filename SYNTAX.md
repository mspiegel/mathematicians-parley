# Syntax of the readable text

`READERS.md` fixes what a step must contain. This document fixes how it is
written down. It records only what has been settled by writing pilots; a
rule is added here when a pilot has needed it and the decision has been
taken, and changed when a later pilot shows it to be wrong. Anything not
here is still provisional and lives in the pilot that needs it.

## The skeleton is the text

The stored text is the **skeleton**: every line of it is a field that the
elaborator reads, and it contains nothing else. It is also the text a
person reads. It must pass the acceptance test of `READERS.md` on paper,
without a viewer.

A viewer may show a **rendered view** of the skeleton: the fields read back
as sentences, the statement of each cited item pulled in from the database
at its pointer, and links on every pointer. An instantiation that
substitutes a variable for itself, such as `n := n`, is not rendered. A
viewer may fold a calculation with the steps its lines cite, showing each
step's justification on its chain line and hiding the step, which gives
the textbook form of a calculation; like collapsing a block, this changes
nothing in the text and can be undone. The rendered view is a
convenience. It adds no information, it is never authored by hand, and
nothing may depend on it. Where the skeleton is hard to follow, the skeleton
is at fault, not the viewer.

The statement of a cited definition or theorem is a property of the
database item, not of the proof that cites it. It is not copied into the
skeleton, because a copy would drift from the item.

## Theorems

A theorem is a name, its hypotheses, and its conclusion:

```
theorem even-square
  let n ∈ ℤ                    (H1)
  assume n² is even            (H2)
  then n is even
```

- A `let` line introduces a variable and says what it is: `let n ∈ ℕ` for
  an element of a named set, `let A be a set` for an arbitrary set, `let
  A be a point` for a point of the plane, and `let f : A → B` for a
  function with its domain and codomain. An `assume` line states a
  formula. These are the theorem's hypotheses, and they map onto
  Metamath's floating and essential hypotheses; `let A be a set` is
  set.mm's `A e. _V`. They are part of the statement, not of the proof.
  The uniform alternative, `let A ∈ Set` with a named universe for
  everything, was rejected: it attaches a type to the thing, and names
  collections a school reader has never met.
- The `then` line is the conclusion.
- Each hypothesis carries a label in parentheses. The proof cites it by
  label wherever it would cite a line number.
- The one-sentence form "for every integer n, if n² is even then n is even"
  is the same statement read aloud. No step converts one form into the
  other, and no method is involved in opening or closing the hypotheses.

## Steps

A proof is a numbered list of steps. Sub-steps are numbered under their
step: 2.1, 2.2, and 2.1.1 beneath 2.1. A step is:

1. Its number and its **claim**: one or more sentences, each a formula.
   Several sentences mean their conjunction.
2. Its **justification**, on the next line: a method or a cited item, its
   instantiation, and the lines, hypotheses and suppositions it uses. The
   forms are listed below.
3. Zero or more **requires** lines, one per hypothesis of the cited item
   that is not the conclusion of a cited line, each with a justification
   of exactly one citation: a method such as `arithmetic`, an item applied
   to lines already present, or a line that states the fact. Requires
   lines do not nest. A fact that needs more than one citation is a
   numbered step before the step that needs it, cited in `from` like any
   line. The alternative, a tree of requires lines under a step, was
   allowed at first and rejected after one proof grew a tree three deep;
   the rule makes no difference to the kernel proof and only keeps the
   text flat.

The last step of a proof is the theorem's conclusion.

## Blocks

A step whose justification is a subproof states its claim and names its
method on the numbered line. The block is indented under it, opens with the
line that introduces the block's assumption, and its sub-steps are numbered
under the step. The claim always precedes the block. There is no closing
step: the block ends with the sub-step that the method requires it to end
with.

```
1.  n is not odd
    contradiction
    suppose n is odd                                  (S)

    1.1.  ...
    1.3.  n² is odd. n² is not odd.
          join 1.1, 1.2
```

A supposition carries a label, like a hypothesis, and is cited by it.

Some methods divide their block into named **parts**. A part marker is a
bare word on its own line, such as `base` or `step`, placed before the
sub-step that discharges that part of the rule. It is not a claim, a
justification, a requires line or a label; it names which part of the
cited rule the sub-step under it discharges, so that the block reads the
way a textbook proof does. The parts a method has, and their order, are
fixed by the method's definition. Induction has `base` and `step`:

```
1.  S(n) = n(n + 1)/2
    induction on n starting at 1, from H1

    base
    1.1.  S(1) = 1(1 + 1)/2
          ...
    step
    1.2.  For every k ∈ ℕ, if S(k) = k(k + 1)/2 then S(k + 1) = ...
          fix
          ...
```

Alternatives considered: no markers, with the parts identified by their
order and form; the parts named on the method line, as `base 1.1, step
1.2`; and induction cited as a theorem with two hypotheses, as it is in
set.mm. Markers on their own lines were chosen because they read like a
textbook.

A part may carry an assumption. A `case` part of a `cases` block opens
with an `assume` line, labelled like a hypothesis, stating the disjunct
that the part handles:

```
5.  |a + b| ≤ |a| + |b|
    cases, from 2

    case
    assume a + b ≥ 0                                  (C1)
    5.1.  |a + b| ≤ |a| + |b|
          ...
    case
    assume a + b < 0                                  (C2)
    5.2.  |a + b| ≤ |a| + |b|
          ...
```

The disjunction being split is a cited line, here line 2, and the reader
checks that the case assumptions are its disjuncts in order. A case that
is impossible still ends by claiming the common formula: it reaches some
P and not P, and then claims the formula by the theorem "if P and not P
then Q", thm:from-contradiction. Two alternatives were rejected for the
impossible-case problem: refuting each case in its own contradiction
block outside any cases block, which loses the case-split narrative, and
letting a cases step have no claim when each case ends in its own
contradiction, which breaks collapsing and citation for that step. The marker
stays a bare word, and the assumption is a line of the same kind as
`assume` and `suppose`. Alternatives considered and rejected: the
disjunction repeated on the method line; the marker carrying the formula
and label, as `case a + b ≥ 0 (C1)`; and a `cases` step with no claim of
its own. Each case ends by claiming the formula of the step above the
block, as each part of an induction ends in a stated instance.

There is no "similarly". An argument that a textbook makes once and
repeats by analogy is a theorem, stated with every hypothesis the argument
uses, and applied once for each case. The statement is often long, as in
the Bezout pilot's lemma with eleven hypotheses; that is the intended
form. A viewer may fold the second application to its claim, or render it
as "similarly", since "the same theorem applied again" is a mechanical
criterion.

A step whose claim is "for every x ∈ S, if A then B" is proved by a block
that opens with the claim's own `let` and `assume` lines, labelled, and ends
with B. The method is `fix`. The hypotheses are therefore written twice,
once in the claim and once as lines, and the reader checks that they match.
This is the same rule by which a theorem's block proves its statement; at
theorem level no method is named because the `let` and `assume` lines are
the statement. The alternative, letting a step's claim be written in the
`let`, `assume`, `then` form with no method, was considered and rejected
for being less explicit: the claim would no longer be a formula, and the
block would be the one form signalled only by its shape.

This is the shape of Lamport's structured proofs, of Isar's
`have ... proof ... qed`, of Mizar's `proof ... end` and of Lean's
`have ... := by`. Prose textbooks use the same order once the claim they
state above a "Suppose ..." is noticed.

## Formulas

Formulas use the notation of `READERS.md`, with these rules for reading:

- "and", "or" and "not" are written as words, never as ∧ ∨ ¬.
- "there is x ∈ S with ..." is written for ∃, and "there is no x ∈ S with
  ..." for ¬∃. Inside such a phrase, clauses are joined with commas and a
  final "and".
- A claim that is a conjunction is written as separate sentences, so that a
  long "and" is never written: "p ∈ ℤ. q ∈ ℤ. q > 0."
- → and ↔ remain symbols. Where a defined word exists, such as "is even" or
  "divides", the word is used.
- Set-builder notation has two shapes, told apart by what precedes the
  colon. With a variable and its domain, {t ∈ X : P(t)}, membership is
  t ∈ X and P(t). With an expression, {E(s) : s ∈ Y}, membership of u is
  "there is s ∈ Y with u = E(s)". Each is a definition with a pointer,
  def:set-builder and def:set-image, used in both directions by the ↔
  convention. Both are kept because a school reader has met both.

## Justification forms

| form | meaning |
|---|---|
| `def:X v := t, from L` | apply definition X with its variable v set to t, using L for its hypotheses |
| `thm:X v := t, from L` | the same for a theorem |
| `obtain a, b: item, from L` or `obtain a from line L` | the cited item, or with no item the named line, concludes an existence claim; name its objects a and b; the claim is the body. The second form takes one name and one line, and carries neither a colon nor a comma, because there is no item to separate the names from and no hypothesis list to introduce |
| `exhibit, from L` | the claim is a bare "there is" sentence; the lines L state its body with some value in place of the bound variable, and the reader finds the value by comparing. The value is never written, since by the literal-instance rule the cited lines determine it. Where the "there is" is a sentence of a cited definition, no keyword is used: `def:even n := p², from 2.3` proves "p² is even" from a line stating p² = 2k for some k, by the ↔ convention |
| `substitute e (line L1) into line L2` | replace by the equation e, which is part of line L1, inside line L2 |
| `substitute e (line L1)` | the claim is t = t′, where t′ is t with one side of e, which is part of line L1, replaced by the other |
| `instantiate v := t in line L, from L2` | line L claims "for every v ∈ X, B"; the claim is B with t in place of v, and L2 supplies t ∈ X. Several variables may be given at once. L may also be a hypothesis or supposition label. L is never an item: a definition whose sentence is a "for every" is first claimed by a numbered step citing it, and that number is instantiated. This is the rule that keeps an item out of `from` applied to the other slot that says where a fact comes from, and for the same reason, that a reader can look at everything a step names |
| `algebra, from L` | ring and field identities, starting from the equations in L |
| `arithmetic` | a fact about closed numerals: value, order, or membership in ℕ ℤ ℚ ℝ |
| `inequalities, from L` | the rules for inequalities, starting from L |
| `join L` | the claim is the sentences of the lines L put together; with one cited line it is that line. It infers nothing. A propositional law that does infer something, such as eliminating a double negation, is a cited theorem instead |
| `contradiction`, then `suppose not C (S)` | C is the step's claim; the block assumes "not C", written literally, labelled S, and its last step states some P and also not P. Any rewriting of "not C", such as p ≤ n for "not p > n", is a step inside the block |
| `fix`, then `let x ∈ S (K)` and `assume A (H)` | the claim is "for every x ∈ S, if A then B"; the block opens with the claim's `let` and `assume` lines, each labelled, and its last step is B |
| `induction on n starting at m, from H`, with parts `base` and `step` | the claim is P(n), where H gives n ∈ ℕ or n ∈ ℕ₀ and, if m is above the set's first element, n ≥ m; the `base` part's last step claims P(m); the `step` part's last step claims "for every k ∈ ℤ with k ≥ m, if P(k) then P(k + 1)", with P read off the claim. The starting point is written even when the set fixes it, so that every induction reads the same way and inductions from 2 or 4 need no new form |
| `cases, from L`, with one `case` part per disjunct | L claims "P or Q"; each part opens with `assume` of its disjunct, labelled, in the order of L, and its last step claims the same formula as the step above the block |
| `calculation`, then a chain | each line of the chain is `rel t  L`, where rel is =, ≤ or < and L is one cited line whose claim is exactly the previous term rel t; the claim is first term rel last term, with rel being = if every line is =, ≤ if every line is = or ≤, and < if any line is < |

`L` is a list of line numbers, hypothesis labels and supposition labels,
and nothing else: an item's sentence that a step needs as a fact is first
written as a step citing the item, and then cited by number. Citing an
item inside `from`, and leaving the reader to instantiate it, was tried
and rejected. Where a line number is written on its own after a verb, as
in `into line 2.3` and `in line 4`, it carries the word "line"; in a
`from` list, after `join`, and on a calculation line it is bare. Labels
never carry the word.

A `define` line names an object: `define S := E (D1)` is an unnumbered,
labelled line placed where S is first needed, claiming nothing, and cited
by its label wherever a step needs to know what S stands for. It is the
third kind of unnumbered line beside `let` and `assume`.

A calculation only joins. Every line of a chain cites a numbered step or
label that states that line's relation, and all reasoning is in those
steps. A chain therefore never carries a method on a line. The
alternative, letting a line carry `algebra` or `substitute` inline as a
textbook calculation does, was considered and rejected so that every
fact in a proof is a numbered step with its own justification, and the
chain is only the reader's view of how they join.

```
5.4.  |a + b| = −(a + b)
      def:abs x := a + b, from 1, C2

5.5.  −(a + b) = −a + −b
      algebra

5.6.  −a + −b ≤ |a| + |b|
      inequalities, from 3, 4

5.7.  |a + b| ≤ |a| + |b|
      calculation
        |a + b| = −(a + b)              5.4
                = −a + −b               5.5
                ≤ |a| + |b|             5.6
```

Wherever a step's claim must be an instance of a formula, such as P(k + 1)
in an induction step, the conclusion of a theorem applied with `n := p`, or
the body of a definition, the instance is literal: the formula with the
substitution made and nothing else changed. A tidier form is a separate
`algebra` step, before or after the literal instance, and is never written
in its place.

Two conventions apply at every citation and are stated here so that they
are not hidden steps:

- Where a cited item's conclusion is several sentences, a step may claim
  any one of them.
- Where a cited **line** claims several sentences, it supplies each of them
  separately and the step may use any. Thirty lines in the corpus claim more
  than one sentence, and 67 steps cite one; Bezout's line 1 claims five and is
  cited seven times, each time for a different part. The alternative, that a
  line names one formula and so supplies only the conjunction, was rejected:
  every method would need to take a conjunction apart before doing its own
  work, which is propositional reasoning inside methods that have no business
  doing any. At kernel level the line is a conjunction either way, and the
  projection out of it lives in the method's expansion. The cost is that a
  citation of a long line does not say which sentence is meant; the cure is to
  keep a line short when a later step will want only part of it, not to change
  this rule.
- Where a sentence of a cited item is "A ↔ B" and a line stating A is
  given in `from`, the step may claim B, and likewise from B to A. This is
  how a definition is unfolded and folded: the defined phrase is one side
  and its meaning is the other.
- Where a sentence of a cited item is conditional, "if A then B", and a
  line stating A is given in `from`, the step may claim B. This is how a
  definition by cases, such as |x|, is unfolded: the case assumption in
  `from` selects the branch. The alternative of naming the branch with a
  keyword on the citation was considered and rejected as saying what the
  reader can already see.
- A calculation may read a cited equation right to left, and writes "right
  to left" when it does.

Each method is a database item with a specified expansion, as `READERS.md`
requires. The expansions are not yet written; the table above says what a
reader checks, which is what the acceptance test needs.

The working boundary between the closure methods, as the pilots practise
it and pending the methods' definitions: `arithmetic` settles facts about
closed numerals, such as 2 ≥ 0, 1 = 1(1 + 1)/2 or a^(0 + 1) = a;
`algebra` applies ring and field identities in the variables and in named
subterms treated as opaque, so it will turn (1 − a^(k + 1))/(1 − a) +
a^(k + 1) into (1 − a^(k + 1)·a)/(1 − a) but will not turn a^(k + 1)·a into
a^(k + 2); and anything about what a named subterm means, such as an
exponent law, a recursive definition or a function value, is a cited
theorem or definition in a step of its own.

## Not settled

- Settled, and no longer on this list: the hypotheses of `algebra` and
  `inequalities`. "p is a real number" is a requires line, as `READERS.md` now
  says explicitly, and the corpus complies throughout: 97 membership lines
  across the 42 steps that cite one of the two methods.
- Settled, and no longer on this list: whether "line 2.1" names one formula or
  each of its sentences. It supplies each of them, as the citation conventions
  above now say.
- Whether a proof consisting of a single block may omit the step that
  repeats the theorem's `then` line as its claim.
- Whether the statements of cited items, which `READERS.md` requires at the
  point of use, are satisfied by the pointer and the database table alone
  when reading on paper.
