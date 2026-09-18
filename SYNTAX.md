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

- A `let` line introduces a variable and the set it ranges over. An
  `assume` line states a formula. These are the theorem's hypotheses, and
  they map onto Metamath's floating and essential hypotheses. They are part
  of the statement, not of the proof.
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
   that is not the conclusion of a cited line, each with its own
   justification in the same forms. A requires line may have requires lines
   of its own, indented under it.

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
          lines 1.1, 1.2
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
    induction on n, from H1

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
checks that the case assumptions are its disjuncts in order. The marker
stays a bare word, and the assumption is a line of the same kind as
`assume` and `suppose`. Alternatives considered and rejected: the
disjunction repeated on the method line; the marker carrying the formula
and label, as `case a + b ≥ 0 (C1)`; and a `cases` step with no claim of
its own. Each case ends by claiming the formula of the step above the
block, as each part of an induction ends in a stated instance.

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

## Justification forms

| form | meaning |
|---|---|
| `def:X v := t, from L` | apply definition X with its variable v set to t, using L for its hypotheses |
| `thm:X v := t, from L` | the same for a theorem |
| `obtain a, b: item, from L` | the cited item concludes an existence claim; name its objects a and b; the claim is the body |
| `exhibit t: item, from L` | the claim is an existence claim of the cited item, or a bare existence claim when no item is given; t is the witness |
| `substitute e (L1) into L2` | replace by the equation e, which is part of line L1, inside line L2 |
| `substitute e (L1)` | the claim is t = t′, where t′ is t with one side of e, which is part of line L1, replaced by the other |
| `algebra, from L` | ring and field identities, starting from the equations in L |
| `arithmetic` | a fact about closed numerals: value, order, or membership in ℕ ℤ ℚ ℝ |
| `inequalities, from L` | the rules for inequalities, starting from L |
| `lines L` | propositional combination of L |
| `contradiction`, then `suppose F (S)` | the block assumes F, labelled S, and its last step states some P and also not P |
| `fix`, then `let x ∈ S (K)` and `assume A (H)` | the claim is "for every x ∈ S, if A then B"; the block opens with the claim's `let` and `assume` lines, each labelled, and its last step is B |
| `induction on n, from H`, with parts `base` and `step` | the claim is P(n), where H is n ∈ ℕ; the `base` part's last step claims P(1); the `step` part's last step claims "for every k ∈ ℕ, if P(k) then P(k + 1)", with P read off the claim |
| `cases, from L`, with one `case` part per disjunct | L claims "P or Q"; each part opens with `assume` of its disjunct, labelled, in the order of L, and its last step claims the same formula as the step above the block |
| `calculation`, then a chain | each line of the chain is `rel t  L`, where rel is =, ≤ or < and L is one cited line whose claim is exactly the previous term rel t; the claim is first term rel last term, with rel being = if every line is =, ≤ if every line is = or ≤, and < if any line is < |

`L` is a list of line numbers, hypothesis labels and supposition labels.

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

## Not settled

- The hypotheses of `algebra` and `inequalities`: whether "p is a number"
  is a requires line of every such step on an integer, or is discharged
  inside the method.
- Whether "line 2.1" names one formula or each of its sentences.
- Whether a proof consisting of a single block may omit the step that
  repeats the theorem's `then` line as its claim.
- Whether the statements of cited items, which `READERS.md` requires at the
  point of use, are satisfied by the pointer and the database table alone
  when reading on paper.
