# Syntax of the readable text

`READERS.md` fixes what a step must contain. This document fixes how it is
written down. It records only what has been settled by writing pilots; a
rule is added here when a pilot has needed it and the decision has been
taken, and changed when a later pilot shows it to be wrong. Anything not
here is still provisional and lives in the pilot that needs it.

Every example set apart in a block is one the tools accept. Its fence says
what it is: `proof` for text of a proof file, which is found line for line
in a proof the build checks and verifies, the theorem it is quoted from or
one of `tests/docs/` written for it; `records` for text of a records file;
`grammar` for productions. A line `...` stands for lines left out.
`tests/doc_examples.rs` fails on an example no proof says, and on a block
whose fence says none of the three, so an example is changed with the proof
that says it.

## The skeleton is the text

The stored text is the **skeleton**: every line of it is a field that the
elaborator reads, and it contains nothing else. It is also the text a
person reads. It must pass the acceptance test of `READERS.md` on paper,
without a viewer.

A viewer may show a **rendered view** of the skeleton: the fields read back
as sentences, the statement of each cited item pulled in from the database
at its pointer, and links on every pointer. The rendered view is a
convenience. It adds no information, it is never authored by hand, and
nothing may depend on it. Where the skeleton is hard to follow, the skeleton
is at fault, not the viewer.

The statement of a cited definition or theorem is a property of the
database item, not of the proof that cites it. It is not copied into the
skeleton, because a copy would drift from the item.

## Theorems

A theorem is a name, its hypotheses, and its conclusion:

```proof
theorem even-square
  let n ∈ ℤ                    (H1)
  assume n² is even            (H2)
  then n is even
```

- A `let` line introduces a variable and says what it is: `let n ∈ ℕ` for
  an element of a named set, `let a ∉ X` for a thing of the sort X holds
  that is not in X, `let x be an element` for a thing whose sort the text
  decides, `let A be a set` for an arbitrary set, `let
  A be a point` for a point of the plane, `let f be a function on A` for a
  function known by its domain alone, `let f : A → B` for a
  function with its domain and codomain, `let f : A → B be one-to-one`, `be
  onto` or `be one-to-one and onto` for such a function with a property,
  `let p be a polynomial` for a
  polynomial with complex coefficients, and `let G be a group with
  operation · and identity e` for a group. A library item may also write `let P be a
  property of the elements of X`, for a property a statement can be
  written about; a theorem in a proof may not, because the elaborator
  cannot state a theorem over a property (`ELABORATION.md`, "Library items
  no proof restates").
  Neither `∉` nor `be an element` claims the thing is a set, which `be a
  set` does (`READERS.md`, on sorts); the kernel still has it be one, and
  that is apparatus the page never writes.
  An `assume` line states a
  formula. These are the theorem's hypotheses, and they map onto
  Metamath's floating and essential hypotheses; `let A be a set` is
  set.mm's `A e. _V`. They are part of the statement, not of the proof.
  `let X ⊆ A` introduces a part of A, which is a member of 𝒫A, and so
  does `for all X ⊆ A`, `there is X ⊆ A with`, `{X ⊆ A : …}` and a
  define ending `for X ⊆ A`: each is the power-set form written in the
  words a school reader has, and builds the same formula.
  Those eleven are all the forms a `let` line has. It carries an
  introduction, which names something and says what it is, and never a
  formula; `assume` is the line that asserts. The one thing a `let`
  asserts is what `be` says of a function, "be" being how English says
  "is" after "let": `let f : A → B be one-to-one` asserts that f is
  one-to-one, and `let p be a polynomial` that p is one, and a citation of
  an item written so must supply it. A polynomial is said in words
  throughout, "p is a polynomial" and "there is a polynomial q with …",
  and each is the membership or the "there is" of set.mm's polynomials
  with complex coefficients, a set the page never writes (`GRAMMAR.md`,
  `fills`). In the same way "there is f : X → Y with …" is the "there is"
  of the functions from X to Y, which the page never writes either, and an
  obtain from it states f : X → Y as the membership of f.
  In the same way "for all f : X → Y, …" is the "for all" of the
  functions from X to Y. A proof of one is a block that opens with
  `let f : X → Y`, and a step citing one for a function g needs
  g : X → Y. For example, `for all g : X → Y, if g(a) = f(a) for all
  a ∈ X then g = f` says that a function from X to Y is fixed by its
  values.
  `let G be a finite group with operation · and identity e` asserts that G
  is finite, and a step citing the line has that.
  A group's line names its set, its operation and its identity. G is the set
  of the group's elements, `a·b` is the operation, `a⁻¹` is the inverse,
  and `gH` is the coset of a set H of the group's elements by g, written as
  a school reader writes it: the two letters side by side, read so only
  where the first is a group's element and the second a set of them. `·` is
  the one symbol a group's operation has. `assume H is a subgroup of G`
  introduces H as a `let` would, and says what it is.
  A property line never names the thing the property holds of, because that
  name comes from the notation that binds it: in `{t ∈ X : P(t)}` the braces
  introduce `t`, and `t` does not exist on the line above. `P(t)` reads "the
  property P holds of t", which is substitution into a statement and not a
  function applied to an argument; the `holds-of` record says why.
  Three of the eleven, `be an element`, `be a set` and `be a point`, are
  therefore not notations and never appear inside a formula. Quantifying over an arbitrary set
  inside a formula is the separate `for all sets X, ...`, a binder with no
  domain, which is to `let X be a set` what `for all n ∈ ℕ, ...` is to
  `let n ∈ ℕ`.
  The uniform alternative, `let A ∈ Set` with a named universe for
  everything, was rejected: it attaches a type to the thing, and names
  collections a school reader has never met.
- The `then` line is the conclusion.
- Each hypothesis carries a label in parentheses. The proof cites it by
  label wherever it would cite a line number.
- The one-sentence form "for all integers n, if n² is even then n is even"
  is the same statement read aloud. No step converts one form into the
  other, and no method is involved in opening or closing the hypotheses.

## Steps

A proof is a numbered list of steps. Sub-steps are numbered under their
step: 2.1, 2.2, and 2.1.1 beneath 2.1. Each run of steps counts 1, 2, 3 in
the order it is written, with no gaps: a reader meeting 3 after 1 looks for
the 2 that is not there, and the checker reports it. A step is:

1. Its number and its **claim**: one or more sentences, each a formula.
   Several sentences mean their conjunction. A sentence may be a chain of
   equations, `|QA| = |QB| = |QC| = |QD|`, which says that all its terms
   are equal. A chain is a whole sentence: not part of another formula, as
   in `for all x, f(x) = g(x) = h(x)` or after `if`. Its relation is `=`.
   A claim may end on a full stop
   or not, alike. The sentences are cut once, by the rule in `GRAMMAR.md`
   ("One front end"), and every tool reads the same ones.
2. Its **justification**, on the next line: a method or a cited item, its
   instantiation, and the lines, hypotheses and suppositions it uses. The
   forms are listed below.
3. Zero or more **requires** lines, one per hypothesis of the cited item
   that is not the conclusion of a cited line nor a membership the page
   says once (below, what a membership line says), each with a justification
   of exactly one citation: a method that opens no block, such as
   `arithmetic`, an item applied
   to lines already present, or a line that states the fact — or the lines
   that state it together, a function's type and a point of its domain,
   `requires a(k) ∈ ℝ: from H2, K4` (below) — or one manipulation of the
   one line it cites, named as a row of an `inequalities` step names its
   own: `requires q ≠ 0: weakening, from 2.1`, where 2.1 says `q > 0`
   (`METHODS.md`, inequalities, Rows). A side condition that needs more
   than one manipulation is a numbered step with rows. Requires
   lines do not nest. A fact that needs more than one citation is a
   numbered step before the step that needs it, cited in `from` like any
   line. The alternative, a tree of requires lines under a step, was
   allowed at first and rejected after one proof grew a tree three deep;
   the rule makes no difference to the kernel proof and only keeps the
   text flat. An item a requires line applies may take what the step's
   requires lines above it state, read top to bottom as the step's lines
   are: `requires numer(x) ∈ ℤ` written first lets `requires |numer(x)| ∈
   ℕ₀: mun:abs-integer z := numer(x)` below it rest on it. A line below is
   not yet established. The fact ends at the first colon written against the word
   before it, `requires b ≤ b: inequalities`; a colon inside a fact stands
   apart, as in `requires g : [a, b] → ℝ: from 7`.

The last step of a proof is the theorem's conclusion. Every other step is
there to be used: a later step, a requires line, a row or a let's reason
cites it, or it is the last step of its part of a block, which claims what
the part owes. A step nothing cites says something the proof never goes on
to use, and the checker reports it.

## Blocks

A step whose justification is a subproof states its claim and names its
method on the numbered line. The block is indented under it, opens with the
line that introduces the block's assumption, and its sub-steps are numbered
under the step. The claim always precedes the block. There is no closing
step: the block ends with the sub-step that the method requires it to end
with.

```proof
1.  n is not odd
    contradiction
    suppose n is odd                                  (S)

    1.1.  n² is odd
          thm:odd-square, from S

    1.2.  n² is not odd
          mun:not-both n := n², from H2, contradicting 1.1
```

A supposition carries a label, like a hypothesis, and is cited by it.

Some methods divide their block into named **parts**. A part marker is a
bare word on its own line, such as `base` or `step`, placed before the
sub-step that discharges that part of the rule. It is not a claim, a
justification, a requires line or a label; it names which part of the
cited rule the sub-step under it discharges, so that the block reads the
way a textbook proof does. The parts a method has, and their order, are
fixed by the method's definition. Induction has `base` and `step`:

```proof
1.  For all k ∈ ℕ, S(k) = k(k + 1)/2.
    induction on k starting at 1

    base
    1.1.  S(1) = 1(1 + 1)/2
          ...

    step
    let k ∈ ℕ                                                         (K)
    assume step 1 is true for k, the induction hypothesis             (IH)

    1.2.  ...
    1.3.  S(k + 1) = (k + 1)((k + 1) + 1)/2
          ...

2.  Σ(k = 1 to n) k = n(n + 1)/2
    calculation
      Σ(k = 1 to n) k = S(n)              D1
                      = n(n + 1)/2        instantiate k := n in line 1
```

**An induction proves a statement of every k, and its step part opens as a
textbook's does.** The claim is "for all k ∈ X, …"; the `base` part ends on
the statement at the start, and the `step` part opens with `let k ∈ X` and
`assume step N is true for k, the induction hypothesis`, and ends on the
statement at k + 1. The step part's letter is the claim's own, so the
hypothesis is the claim's words after the comma, read where they stand:
"step 1 is true for k" is S(k) = k(k + 1)/2, with nothing put in for
anything. A theorem about its own n, `let n ∈ ℕ`, inducts on another letter
and then instantiates, as step 2 does, since the step part cannot fix the
letter the theorem already holds. Alternatives considered: the claim about n
with the step part fixing k, which makes the reader put k for n in the
hypothesis; the hypothesis written out again on the `assume` line, which
repeats the claim word for word; and the step part as one step claiming "for
all k, if P(k) then P(k + 1)" proved by a `proof` block, which states the induction
rule over again and nests every step a level deeper.

Alternatives considered: no markers, with the parts identified by their
order and form; the parts named on the method line, as `base 1.1, step
1.2`; and induction cited as a theorem with two hypotheses, as it is in
set.mm. Markers on their own lines were chosen because they read like a
textbook.

**An induction over the parts of a finite set runs the same way, a member
at a time.** The claim is "for all Y ⊆ X, P(Y)", with X finite. It starts
at ∅, which it writes, `induction on Y starting at ∅`, and it says on a
requires line that X is finite, since the rule holds of a finite set only.
The `base` part ends on P(∅). The `step` part opens with `let Y ⊆ X`,
`assume step N is true for Y, the induction hypothesis` and `let a ∈ X ∖
Y`, and ends on P(Y ∪ {a}):

```proof
1.  For all Y ⊆ X, ∏(y ∈ Y) 1 = 1.
    induction on Y starting at ∅
    requires X is finite: from H2

    base
    1.1.  ∏(y ∈ ∅) 1 = 1
          mun:product-empty

    step
    let Y ⊆ X                                                         (K)
    assume step 1 is true for Y, the induction hypothesis             (IH)
    let a ∈ X ∖ Y                                                     (K2)
    ...
    1.5.  ∏(y ∈ Y ∪ {a}) 1 = 1
          transitivity, from 1.4, IH
```

A number induction's step names nothing new, since k + 1 is written from k.
This one names the member it adds, which the statement at Y ∪ {a} is about.
Alternatives considered: a claim about X alone, which leaves the hypothesis
nothing smaller to be about; and an induction on the number of members,
"for all k ∈ ℕ₀, for all Y ⊆ X with |Y| = k, …", which says the same thing
in a number's words.

A part may carry an assumption. An induction's `step` part opens with its
`let` and its induction hypothesis, as above. A `case` part of a `cases` block opens
with an `assume` line, labelled like a hypothesis, stating the disjunct
that the part handles:

```proof
2.  |a + b| ≤ |a| + |b|
    cases, from 1

    case
    assume a + b ≥ 0                                  (C1)
    2.1.  |a + b| ≤ |a| + |b|
          ...
    case
    assume a + b < 0                                  (C2)
    2.2.  |a + b| ≤ |a| + |b|
          ...
```

The disjunction being split is a cited line, here line 1, and the reader
checks that the case assumptions are its disjuncts in order. A case that
cannot occur ends on the step that reaches the opposite of an earlier line,
and says so after its reasons, as a textbook says "contradicting 9.1":

```proof
    9.3.  not b(N) + N ≤ N
          inequalities, from 9.2, contradicting 9.1
```

The step's claim is the line negated, or the line, or one sentence of it,
is the claim negated, and the step is the last of its case; the case then
gives the common formula, as every case does. Two alternatives were rejected for the
impossible-case problem: refuting each case in its own contradiction
block outside any cases block, which loses the case-split narrative, and
letting a cases step have no claim when each case ends in its own
contradiction, which breaks collapsing and citation for that step.

A `proof` block whose assumption cannot hold ends the same way. "For all x ∈ V,
if 0 ≤ n and x = v(0) and x ≠ v(0), then …" says nothing of any x, and a
textbook says so without supposing the opposite of what it claims:

```proof
          assume 0 ≤ n and x = v(0) and x ≠ v(0)                      (C2)

          1.1.1.  x = v(0)
                  restate C2

          1.1.2.  x ≠ v(0)
                  restate C2, contradicting 1.1.1
```

The block's last step reaches the opposite of an earlier line and names it,
and the block then gives what it claims of the name it fixes, as a case that
cannot occur gives the common formula. A contradiction block would suppose
the claim's denial and never use it.

A case whose assumption already is the block's claim has nothing to show,
and says so on its assumption line, as a textbook says "if b(N) = 0 there is
nothing to prove":

```proof
    case
    assume b(N) = 0, which is the claim                               (C7)

    case
    assume b(N) ≠ 0                                                   (C8)

    9.1.  b(N) + N ≤ N
          ...
```

Such a case has no steps, and its assumption must be the claim of the step
above the block. Having no step to say which block it is in, it is in the
innermost `cases` block open at its line, so a case of an outer block that is
the claim is written before an inner block opens or after a step of its own
block. The marker
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

A step whose claim is "for all x ∈ S, if A then B" is proved by a block
that opens with the claim's own `let` and `assume` lines, labelled, and ends
with B. The method is `proof`, as a textbook writes "Proof." under a claim
inside a larger argument: the word says only that the argument follows, and
the `let` and `assume` lines under it say what it takes on. A claim "if A
then B" with no "for all" opens with `assume A` alone, as "Suppose
k + 1 ≤ n. …" does. The hypotheses are therefore written twice,
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

- "and", "or" and "not" are written as words, never as ∧ ∨ ¬. A "not" in front
  of a relation written as words takes brackets, as `not (n is odd)` does,
  because `not n is odd` reads as easily as "(not n) is odd". In front of a
  relation written as a symbol it takes none: `not p = 1`.
- "P is between A and B" writes an "and" of its own, so in a sentence joined
  by "and" or "or" it takes brackets: `P = A or (P is between A and B)`, and
  `there is X ∈ 𝔼² with (X is between A and B) and |AX| = r`. Alone, or as
  the whole of what follows "with" or "if", it takes none. A phrase a define
  gives whose own words write "and" or "or" is bracketed the same way.
- Four notations write a negation inside themselves: `≠`, `∉`, "is not odd" and
  "there is no … with …". Each record says which of its patterns is the
  negation of which, so the folded spelling and the "not" spelling are one
  formula and the page writes whichever reads better.
- "there is x ∈ S with ..." is written for ∃, and "there is no x ∈ S with
  ..." for ¬∃, both in full: a phrase after "and" repeats the "there is"
  rather than eliding it. Inside such a phrase, clauses are joined with commas
  and a final "and". The comma list is the declared notation
  `comma-conjunction`, which is the same connective as "and" and builds the
  same tree, so the final "and" is layout and carries no meaning of its own.
- "there exists x ∈ S such that ..." is the same formula as "there is x ∈ S
  with ...", in the words a theorem is often stated in, and so is "there
  exists X ⊆ A such that ..." as "there is X ⊆ A with ...".
- "for all x, y ∈ S, ..." is "for all x ∈ S, for all y ∈ S, ...", two names
  over one set, as a textbook writes "for all a, b ∈ ℝ": the set is each
  name's. It is the same formula as the long form, so either may be written
  where the other is cited, and "for all X, Y ⊆ A" is its twin for parts.
- "there are x ∈ S and y ∈ T with ..." names two at once. Over one set it is
  written "there are x, y ∈ S with ...", or in a theorem's words "there exist
  x, y ∈ S such that ...", and all three build the same formula.
- "for all x ∈ S, ..." is written for ∀, and a side condition on the
  variable goes in a "with" clause: "for all ε ∈ ℝ with ε > 0, ...". The
  "with" means a conjunction after "there is" and an implication here, which
  is what the two phrases mean in English: "for all ε ∈ ℝ with ε > 0, P" is
  "for all ε ∈ ℝ, if ε > 0 then P", the same formula, so either may be
  written where the other is cited.
- A bound may stand where the set would, as a textbook writes "for all
  ε > 0" and "there is δ > 0 with …", where the theorem's statement says
  what the letter ranges over, in a line beside its `let` and `assume`
  lines: `ε, δ range over ℝ`. "for all ε > 0, …" is then "for all ε ∈ ℝ
  with ε > 0, …", and "there is δ > 0 with …" is "there is δ ∈ ℝ with δ > 0
  and …", the same formulas, so either may be written where the other is
  cited. The bound is `>`, `≥`, `<`, `≤` or `≠` with the letter on its left.
  The line introduces nothing and cannot be cited: it covers the statement
  and every line of the proof, and no other theorem, since a statement is
  read wherever it is cited and carries everything it depends on. It is
  refused where no quantifier leaves the letter's set out, where it names a
  letter twice or something that is not a set, and where a `let` puts the
  letter in another set; a short form whose letter has no range line has no
  reading.
- A universal may also be written after what it says, as a textbook writes
  one inside "such that": "f(x) ≠ B for all x ∈ A" is "for all x ∈ A,
  f(x) ≠ B", and "there exists B ⊆ A such that f(x) ≠ B for all x ∈ A" reads
  as it would aloud. What it says is one relation, a word predicate or a
  negation of one: "f(x) ≠ B and g(x) = 0 for all x ∈ A" does not parse,
  since a reader cannot tell whether the "for all" covers both, and the page
  writes "(f(x) ≠ B and g(x) = 0) for all x ∈ A" or the prefix form.
  Two in a row, "… for all x ∈ A for all y ∈ B", are both over what precedes
  them. The bound of a declared letter may stand for the set here too:
  "|x(n) − L| < ε for all n ≥ N" is "for all n ≥ N, |x(n) − L| < ε". And
  it may carry a condition, as a textbook writes continuity:
  "|f(x) − f(c)| < ε for all x ∈ D with |x − c| < δ" is "for all x ∈ D, if
  |x − c| < δ then |f(x) − f(c)| < ε". The condition is one relation too.
  `LINTER.md` says which of the two forms to write where.
- A claim that is a conjunction is written as separate sentences, so that a
  long "and" is never written: "p ∈ ℤ. q ∈ ℤ. q > 0."
- → and ↔ remain symbols. Where a defined word exists, such as "is even" or
  "divides", the word is used, **and it is written in full everywhere**. English
  drops the copula inside a "there is ... with ..." phrase, and the corpus did
  so three times, writing "there is p ∈ ℕ with p prime". It now writes "with p
  is prime", which reads worse and is the same formula in every position. The
  alternative was a second pattern for each word predicate, or a rule letting a
  binder body drop the "is", and both make one notation depend on where it
  stands. It also removed a real defect: step 8 of the prime proof exhibits from
  step 5, whose claim says "p is prime", so under the literal-instance rule the
  two did not match.
- Set-builder notation has two shapes, told apart by what precedes the
  colon. With a variable and its domain, {t ∈ X : P(t)}, membership is
  t ∈ X and P(t). With an expression, {E(s) : s ∈ Y}, membership of u is
  "there is s ∈ Y with u = E(s)". Each is a definition with a pointer,
  def:stdlib/sets/set-builder and def:stdlib/functions/set-image, used in both directions by the ↔
  convention. Both are kept because a school reader has met both.
- `(a, b)` is the pair of a and b, and `A × B` is the set of pairs whose
  first part is in A and whose second is in B. Where the place it fills
  wants a set (the right of ∈, the set a "for all" or "there is" ranges
  over, a function's domain or codomain, a side of ⊆, ∪, ∩ or ∖), the pair
  of ends names the open interval between them: `x ∈ (0, π)` and
  `f : (0, 1) → ℝ` are intervals, and `(a, b) = (c, d)` and `f((1, 2))` are
  pairs. The interval asks nothing of its ends: (3, 1) is the empty set, as
  set.mm has it. Where a point is wanted it names the point with those
  coordinates: `A = (1, 2)` with A a point, and `|(0, 0)(3, 4)|`.

## What a cited line says

A cited line says what it writes and what a reader takes from it on sight.
Every way a step cites a line reads all of it: an item's `from`, a method's
`from`, a requires line's `from`, a calculation's link, an inequalities
block's first row, `transitivity`, `substitute` (the equation taken and the
line put into), `contradicting`, `obtain`, `cases`, `instantiate` and a
definition unfolded. The one exception is `join`, which puts lines together,
and `restate`, the same for one line. They take only what the lines write:
their sentences, and the parts of a sentence joined by "and". Inside a
block, a "for all" line written outside it over the block's set is written
at the block's letter, as `cases` reads it, so they take that too. And
where the step cites a define, a name in a line and what it names are one
formula (below, "A defined name and the term it names"), so they take the
line with the name read either way. And `cases` takes the line as a whole: one of the
several things a line says is not the line's "or".

Besides what it writes, a cited line says:

- **each of its sentences**, and their conjunction: "A. B" and "A and B"
  are one claim (below, "Two conventions apply at every citation").
- **an equation either way round**: `a = b` says `b = a`.
- **every equation of a chain**: `a = b = c` says `a = c`.
- **a congruence either way round**: `b ≡ a (mod n)` says `a ≡ b (mod n)`
  (`congruent-mod`, `commutes any order of holes 1 and 2`).
- **what a membership in a number system implies**: `k ∈ ℕ` says k ∈ ℝ,
  k ≥ 1, k > 0 and k ≠ 0; `k ∈ ℕ₀` says k ≥ 0 (below, "A line saying a
  term is in a number system").
- **the bounds of a range**: `k ∈ {a, …, b}` says a ≤ k and k ≤ b.
- **every wider function type**: `h : X → ℕ` says `h : X → ℝ`.
- **a "for all" of every smaller set**: "for all k ∈ ℕ, P(k)" says it for
  all k ∈ {1, …, n}.
- **a subset as its members**: `A ⊆ B` says "for all x ∈ A, x ∈ B", with
  any letter the line does not use for x.
- **a "for all" at a block's letter**: inside a block that opened with
  `let x ∈ X`, a line written above it saying "for all a ∈ X, P(a)" says
  P(x).
- **a defined name as what it names**, where the step cites the define
  (below, "A step may cite a define").

Nothing past these is read: that an integer above 0 is a natural number is
the item `pos-int-nat`, and a fact that takes reasoning from the line is a
step of its own.

## Justification forms

| form | meaning |
|---|---|
| `def:X v := t, from L` | apply definition X with its variable v set to t, using L for its hypotheses. X is the name the file imports the definition under, as `def:C` after `import definition stdlib/counting/C`. Every definition is cited so, `def:odd` among them: a definition is never mundane |
| `thm:X v := t, from L` | the same for a theorem, and `axi:X` for an axiom; `mun:X` for a theorem a proof takes for granted. A theorem of this proof file is written by its name alone, `thm:odd-square`, with no import; any other item is imported at the head of the file, one to a line after its record's header, `import mundane theorem stdlib/numbers/int-real`, and cited by its name, `mun:int-real`. `GRAMMAR.md` gives the rules under "Names" |
| `obtain a, b: item, from L` or `obtain a, b from line L` | the cited item, or with no item the named line, concludes an existence claim; of a line saying several things, it is the one "there is" among them, and a line saying none or several gives none; name its objects a and b; the claim is the body. The second form takes one line and carries no colon, because there is no item to separate the names from and no hypothesis list to introduce. **The claim states the membership of each name introduced**, as its own sentence, so that nothing has to read the cited item to learn what the name is. See `GRAMMAR.md` on sorts. **Use the first form where the existence comes from an item**, and the second, after a step stating the existence, where it comes from a line. In the first form the name arrives in a claim written above the justification that introduces it, and the claim says all there is of it, so the one line reads as "p = 2r for some integer r" or "choose N with …" does, whatever letter the item uses: the item's text is elsewhere, and its letters never reach the page. `LINTER.md` keeps the rule |
| `D, from L` | D is a define's label; the claim equates the name it gives, applied or not, with what it names, and for a define by cases L says which case |
| `exhibit, from L` | the claim is a bare "there is" sentence; the lines L state its body with some value in place of the bound variable, and the reader finds the value by comparing. The value is never written, since by the literal-instance rule the cited lines determine it. Where the "there is" is a sentence of a cited definition, no keyword is used: `def:even n := p², from 2.3` proves "p² is even" from a line stating p² = 2k for some k, by the ↔ convention |
| `substitute e (line L1) into line L2` | replace by the equation e, which is part of line L1, inside line L2 |
| `substitute e (line L1)` | the claim is t = t′, where t′ is t with one side of e, which is part of line L1, replaced by the other |
| `substitute`, then rows | one substitution after another, a row to each. The first row is a line the step cites, written out, with its number or label as its reason. Each row after it is the row above with one term put for another, in as many places as the row shows. Its reason says why the two terms are equal: `algebra`, `arithmetic`, `substitute line L`, or a theorem or definition. The last row is the claim |
| `instantiate v := t in line L, from L2` | line L claims "for all v ∈ X, B"; the claim is B with t in place of v, and L2 supplies t ∈ X, or says what t is built from as a cited item's lines do: L2 saying q ∈ ℕ₀ supplies 3q + 1 ∈ ℕ₀, though a `let` put q in ℤ (below, "A term that a line the step names"). Several variables may be given at once. L may also be a hypothesis or supposition label. L is never an item: a definition whose sentence is a "for all" is first claimed by a numbered step citing it, and that number is instantiated. This is the rule that keeps an item out of `from` applied to the other slot that says where a fact comes from, and for the same reason, that a reader can look at everything a step names |
| `algebra, from L` | ring and field identities, starting from the equations in L |
| `arithmetic` | a fact about closed numerals: value, order, or membership in ℕ ℤ ℚ ℝ |
| `real arithmetic` | a fact about closed terms with square roots of rationals, π, e, logarithms and exponentials of rationals, and sines and cosines of multiples of π/4 and π/6: value, disequality and order where `METHODS.md` says they are decided, membership in ℝ, and membership in ℕ ℤ ℚ where the value is rational |
| `inequalities, from L` | the lines L added side by side, as they stand, with the bounds a membership gives, closed numeral facts, a disequality taken both ways and a negation turned round taken without being written (`METHODS.md`, inequalities); with nothing in L to add, those alone |
| `inequalities`, then rows | the manipulations of one line written out, a row to each. The first row is a line the step cites, written out, with its label as reason; each row after it is the row above with the manipulation its reason names, `adding t`, `multiplying by c`, `restate`, `weakening` or `algebra` (`METHODS.md`); the last row is the claim |
| `transitivity, from L` | the lines L, in the order cited, make a chain: where one line ends the next begins, the term they share written the same way in both, each line read from whichever side meets the one before; the claim relates the chain's first term to its last, by the relation a calculation's chain would have |
| `antisymmetry, from L` | L is two lines, `a ≤ b` and `b ≤ a`; the claim is `a = b` |
| `join L1, L2, …` | the claim is the sentences of two or more cited lines put together; a chain of equations is the equations between its neighbouring terms. It infers nothing, and takes what the lines write and nothing else a line says (What a cited line says), but for an equation or a congruence either way round, which is the same claim, a "for all" line cited inside a block, read at the block's letter, and a name read as what it names where the step cites its define, which is the same formula. A propositional law that does infer something, such as eliminating a double negation, is a cited theorem instead |
| `restate L` | as `join`, for one cited line: the claim is that line, or what `join` would take from it, such as one of its parts. A define the step cites to read a name is not a line: `restate D1, 1`. A `join` of one line, or a `restate` of several, is refused, and told the word to use |
| `contradiction`, then `suppose B (S)` | C is the step's claim; the block supposes B, labelled S, and its last step reaches the opposite of an earlier line and names it after its reasons, `inequalities, from 3.1, contradicting 3.4`, or reaches a closed fact that `arithmetic`, or `real arithmetic` where it holds a square root, π, e or a logarithm, finds false and says so after its claim, `2 ≤ 1, which is impossible`. Some step of the block cites S. B is either "not C", which is reductio, or the thing C negates, which is how a negation is proved directly; no formula is its own double negation, so which one it is never has to be guessed. Any rewriting of B, such as p ≤ n for "not p > n", is a step inside the block. `METHODS.md` says what each shape expands to and which of them needs the classical step |
| `proof`, then `let x ∈ S (K)` and `assume A (H)` | the claim is "for all x ∈ S, if A then B", or "if A then B" where the block opens with `assume` alone; the block opens with the claim's `let` and `assume` lines, each labelled, and its last step is B, or, where A cannot hold, a step reaching the opposite of an earlier line that names it after its reasons, as a case that cannot occur does. The claim is one sentence: the block proves one statement, and each other sentence is a step of its own |
| `induction on k starting at m`, with parts `base` and `step` | the claim is "for all k ∈ X, P(k)", X being ℕ or ℕ₀ and m its first element; the `base` part's last step claims P(m); the `step` part opens with `let k ∈ X (K)` and `assume step N is true for k, the induction hypothesis (IH)`, those two lines in that order and no other, N being the induction's number, and its last step claims P(k + 1), with P read off the claim. A claim about only some k, "for all k ∈ ℕ₀ with k ≤ n, S", is the formula "for all k ∈ ℕ₀, if k ≤ n then S", so P(k) is "if k ≤ n then S": the base claims "if 0 ≤ n then …", and each part proves its "if" by a `proof` block opening `assume`. The starting point is written even when the set fixes it, so that every induction reads the same way and inductions from 2 or 4 need no new form. k is a letter of the induction's own: one the theorem or a block around the induction has already introduced would be two things at once, and a reader could not tell which a line means. P(k) mentions k: a statement that does not is no induction, and is a step of its own. The claim is one sentence. Over the parts of a finite set, the claim is "for all Y ⊆ X, P(Y)" and the start ∅, and a requires line says X is finite. The `step` part opens with `let Y ⊆ X (K)`, the induction hypothesis and `let a ∈ X ∖ Y`, those three lines in that order, and its last step claims P(Y ∪ {a}) |
| `cases, from L`, with one `case` part per disjunct, two or more: one case is no case split, and is a plain step | L claims "P or Q": the line as a whole is the "or", as written or, for a "for all" line cited inside a block, read at the block's letter (What a cited line says); a line saying the "or" and something besides is not it; each part opens with `assume` of its disjunct, labelled, in the order of L, and its last step claims the same formula as the step above the block |
| `both directions`, with two `direction` parts | the claim is "A ↔ B"; the first part opens with `assume A`, labelled, and its last step claims B; the second opens with `assume B` and its last step claims A. It is how a textbook proves "if and only if", a direction at a time |
| `calculation`, then a chain | each line of the chain is `rel t  reason`, where rel is =, ≤, <, ≥ or >, or `≡ t (mod n)`, and the reason is one of these: a line number or label whose claim is exactly the previous term rel t; `arithmetic` or `real arithmetic`, where the previous term and t differ only in pieces with no letter in them, each piece worked out, or where the line is a congruence of numerals alone; or any other reason a step claiming "previous term rel t" could give: `algebra` or `algebra, from L`, `substitute line L`, `instantiate v := t in line L`, or a theorem or definition cited as a step cites it. Their requires lines go under the calculation step. The chain goes one way, its orders all ≤ and < or all ≥ and >; the claim is first term rel last term, with rel being = if every line is =, ≤ if every line is = or ≤, < if any line is <, ≥ and > the same way going down, and ≡ (mod n) if any line is ≡, every ≡ line saying the same n, none mixed with an order, and every line after the first ≡ a ≡ too (`GRAMMAR.md`). A calculation opens no block: its chain is all of it. A chain that says ≡ relates integers: each term is one, said once, by a line a link cites, or beside one in an equation such a line says |

`L` is a list of line numbers, hypothesis labels and supposition labels,
and nothing else: an item's sentence that a step needs as a fact is first
written as a step citing the item, and then cited by number. Citing an
item inside `from`, and leaving the reader to instantiate it, was tried
and rejected. Where a line number is written on its own after a verb, as
in `into line 2.3` and `in line 4`, it carries the word "line"; in a
`from` list, after `join`, and on a calculation line it is bare. Labels
never carry the word.

**A line is cited once.** A cited line fills every hypothesis of the cited
item that it says, so a list names each line one time however many it fills:
`mun:coprime-product x := a, y := a, n := gcd(b, c), from 1, 11`, where
line 11 says gcd(a, gcd(b, c)) = 1 and fills both hypotheses that x and y
are prime to n. The checker reports a line named twice in one list. The
links of a calculation are each cited on their own, and two links may cite
one line.

**A list is in order.** Labels come first, sorted by their letters and
then their number, and then lines, sorted by step number:
`from A1, C2, D1, H1, H2, H10, K1, S, 2, 3.1, 3.2, 10`. A label with no
number comes before the same letters with one, and `3.2` comes before
`10`. The order says nothing about which hypothesis a line fills, so a
reader looking for a line knows where in the list to find it. The checker
reports a list out of order and gives it in order. A `transitivity` step's
list is the one exception: its order is the chain's, which the reader
follows as it is written (`METHODS.md`, transitivity).

**A line said of every member of a set says it of every member of a set
inside that one.** A hypothesis asking "for all k ∈ {1, …, n}, P(k)" is
answered by a cited line "for all k ∈ ℕ, P(k)", since every k from 1 to n
is a natural number. Which sets lie inside which is a declared table, not a
search: ℕ ⊆ ℕ₀ ⊆ ℤ ⊆ ℚ ⊆ ℝ, {1, …, b} ⊆ ℕ, {0, …, b} ⊆ ℕ₀ and {a, …, b} ⊆ ℤ,
each by the set.mm lemma that says so of a member. The table is in
`src/rules.rs`, and the checker and the elaborator read the same one.

**A line saying a term is in a number system says what that implies.**
`let k ∈ ℕ (K1)` also says k ∈ ℕ₀, k ∈ ℤ, k ∈ ℚ and k ∈ ℝ, by the table
above, and k ≥ 1, k > 0 and k ≠ 0; a line saying k ∈ ℕ₀ also says k ≥ 0. A
step citing the line reads these as well (What a cited line says): a method
(`inequalities, from K1` has k ≥ 1), a requires line (`requires k ≠ 0: from
K1`), and an item's hypothesis (an item asking x ≥ 1, answered by K1). Each is one set.mm lemma
from the line, so the fact still comes from a line the step names, and one
written line counts for what it plainly says. Nothing past the table is
read: that an integer above 0 is a natural number is the item `pos-int-nat`.

**A line saying a term is in a range says its bounds.** `let k ∈ {a, …, b}
(K1)` also says a ≤ k and k ≤ b, and a line saying `f(x) ∈ {0, …, n − 1}`
says 0 ≤ f(x) and f(x) ≤ n − 1. A step citing the line reads them, as it
reads k ≥ 1 in `k ∈ ℕ` (What a cited line says). For example, `inequalities, from K1` has both
bounds, and an item asking k ≤ b is answered by K1. No line restates them
first.

**A line giving a function's type gives every wider one.** A line saying
`h : X → ℕ` also says `h : X → ℤ` and `h : X → ℝ`: every codomain the table
above puts its own inside, as `k ∈ ℕ` says `k ∈ ℝ`. For example, where line 5
says `h : {1, …, n} → ℕ`, a step citing an item that asks
`t : {1, …, n} → ℝ` has it with `requires h : {1, …, n} → ℝ: from 5`, and no
line proves the wider type first.

**A membership in a number system is said once, where a letter is
introduced** (`READERS.md`). A step neither writes nor cites the membership
of
- a numeral, or a term of numerals alone that `arithmetic` works out, in
  each number system its value is in: `3 ∈ ℤ`, `10 − 1 ∈ ℕ`, `0! ∈ ℕ`,
  `7 mod 3 ∈ ℕ₀`;
- a square root, π, e, a logarithm, a sine or a cosine that
  `real arithmetic` works out, in ℝ and ℂ, and what the operations below
  build from them: `√2 ∈ ℝ`, `sin(π/6) ∈ ℝ`,
  `1 + √2 ∈ ℝ`, `π + ln 2 ∈ ℝ`. Its membership of ℕ, ℕ₀, ℤ or ℚ is not said
  once, even where its value is rational: `√4 ∈ ℕ` is a requires line
  `real arithmetic` justifies;
- a letter, in the set the line introducing it names and every number system
  containing that one: a `let` of the theorem or of a block around the
  step, an induction's `let k ∈ X`, or an `obtain`'s sentence `p ∈ ℤ`, which
  every obtain states of each name it introduces;
- a letter introduced in a range, `let k ∈ {a, …, b}`: k ∈ ℤ, and k ∈ ℕ
  where a is 1 and k ∈ ℕ₀ where a is 0, as a sum's index is, with every
  number system containing that one. What else the range says, a ≤ k and
  k ≤ b, is cited, by the line that says the range;
- a letter introduced in an interval, `let x ∈ (a, b)` or `let x ∈ [a, b]`,
  or in one with points taken out, `let x ∈ (a, b) ∖ {c}`: x ∈ ℝ, and x ∈ ℂ, where for [a, b] its ends are numbers said once. What
  else the interval says, a < x and x < b, or a ≤ x and x ≤ b, is cited, by
  the line that says the interval;
- a term built from those by +, −, ·, unary −, a power whose exponent is a
  numeral or a letter introduced in ℕ or ℕ₀, and /, in each number system
  closed under what builds it (the table of closure
  lemmas in `src/rules.rs`): a·x + b·y ∈ ℤ where a, b, x and y are integers.
  A quotient's divisor not being zero is the step's to write or cite, unless
  the page says it once: of a term of numerals alone that `arithmetic`
  works out to a value other than zero, `3`, `1 − 2` and `10^0`; of a
  positive integer, a term these rules put in ℕ, as k, k + 1, j·(j + 1)
  and 2^n are where k, j ∈ ℕ and n ∈ ℕ₀; or of a product, a quotient, a
  negation or a power to a numeral, 0 included, whose parts are each not
  zero by this same rule: `x·2`, `−x` and `x⁰` are not zero where a line
  says `x ≠ 0`, or `x > 0`. A sum's term that divides by something holding the
  sum's own letter, `1/T(k)` in `Σ(k = 1 to n)`, or `1/k` in `Σ(k = 0 to
  n)`, has a divisor no line outside the sum can speak of, so the citation
  names a line saying the term at every point of a set holding the range,
  `for all k ∈ ℕ, 1/T(k) ∈ ℝ`, proved as a step of its own;
- a sum in ℝ or ℂ whose term is a number at every index by these rules and
  the function types in scope: the index is in the system its range starts
  in, and a function's value is one where its type's domain is the sum's
  range or a number system holding the index, `Σ(k = 1 to n) a(k)²` where
  `let a : {1, …, n} → ℝ`. A term dividing by anything but a positive
  integer, as above, is not said once this way.

`let k ∈ ℕ` is still cited for k ≥ 1 and k ≠ 0, which the line says beyond
the membership. A citation made only for one of these memberships is a line
doing no work, in a step's citation and in a requires line's reason alike,
and the checker reports both. A step resting on a method uses each line it
cites in the same sense: taken away, the method no longer decides the
claim, or leaves one of its hypotheses unsaid
(`checker::formulas::check_method_cites_used`).

A term that a line the step names puts in a number system is a part as a
letter is, for a method's atoms and a cited item's hypotheses alike: where
a requires line says `N(n) ∈ ℝ`, `N(n) + 1`, `2·N(n)` and `N(n)²` are real
too, and a line saying so does no work. A letter is such a term as well: a
line the step names saying q ∈ ℕ₀ puts q there though a `let` or an
`obtain` put it in ℤ, the narrower system standing. A line putting a letter
in a range says its bounds and nothing past them, and that r ∈ {0, …, n − 1} is whole is
`mun:range-integer`, cited; but a step said of every member of a range,
"for all j ∈ {1, …, m}, …" justified as at a member, introduces j as its
block's `let` would, in ℕ here. Everything else a step needs to be
a number is written as before: a defined name, a function's value outside a
sum, a sum the rule above does not reach, a power whose exponent is any
other term, 2^(j + 1) or 2^k with k ∈ ℤ, |x|,
n!, a remainder, C(n, k), and anything a library item builds.

**A function's type and a point of its domain say the value is in the
codomain.** `let a : {1, …, n} → ℝ (H2)` and `let k ∈ {1, …, n} (K4)`, cited
together, say a(k) ∈ ℝ, and what that membership implies by the table:
`requires a(k) ∈ ℝ: from H2, K4`, or an item asking x ∈ ℝ at x := a(k),
answered by H2 and K4. The domain is the one the type writes. This is the one
place a sort is cited (`READERS.md`).

**A step said of every member.** A step claiming "for all k ∈ X, P" may be
justified as P would be, read at a member k of X, with no `proof` block:

    2.  For all k ∈ {1, …, n}, a(k)² ≥ 0.
        mun:square-nonneg x := a(k), from H2

is the block `proof`, `let k ∈ {1, …, n} (K)`, and one step proving a(k)² ≥ 0
from H2 and K. The membership k ∈ X is what the claim's own "for all" gives,
so no line is cited for it, and a requires line speaks of the member by the
claim's letter and has its membership as the step does:

    9.  For all x ∈ [a, b], F(x) ∈ ℝ.
        membership, from D1, D2
        requires f(x) ∈ ℝ: from H4
        requires b − a ≠ 0: weakening, from 1
        requires (f(a) − f(b))/(b − a) ∈ ℝ: membership, from H1, H2, H4, 2, 3

reads f(x) ∈ ℝ off H4 at the member x, as the block's line `from H4, K`
would. "for all X ⊆ A" is read at a part of A. Which reading a
citation takes is read off what it cites, never tried one way and then the
other: an item whose conclusions say "for all" anywhere is read as written,
as `sum-zero-terms` gives one and `upper-bound` unfolds to one, and an item
whose conclusions do not is applied at a member; a define, which says one
equation, is read at a member, and so are `membership`, `algebra` and
`inequalities`, which each prove one fact. A step whose body needs more than
one step is still a block.

A naming line gives an object a name. In a theorem it opens with `let` and
`=`, is labelled rather than numbered, and stands where the name is first
needed:

```proof
let m = gcd(s, w), a positive integer                               (D1)
    def:gcd a := s, b := w, from 4, 32
    reads the number whose square is s

46. s = m²
    calculation
      s = gcd(s, w)²    45
        = m²            D1
```

It introduces m and states that m is gcd(s, w), as a textbook's "let x₁ =
min(b, c + δ/2)" does, and a step that needs what m stands for cites it by
its label. After a comma it may say which numbers m is among, in the words
the number system's notation record gives (`member`): a natural number or a
positive integer, a natural number or 0 or a nonnegative integer, an
integer, a rational number, a real number, a complex number. The record
gives a set more than one wording where textbooks use more than one, and
each is the same set: `a positive integer` says ℕ. A sign is no part of a
kind beyond those, since that a number is positive is a fact that can fail,
and a step that needs it cites the line saying it. So the let above says
gcd(s, w) ∈ ℕ, and the line under it gives the reason, written as a
requires line's reason is: a method or an item, and what it cites, all of it
above the let.

Where the item asks for a fact nothing above the let says, a requires line
under the reason gives it, as one under a step does:

```proof
let c = cos(∠APB), a real number                                     (D1)
    mun:cos-real a := ∠APB
    requires ∠APB ∈ ℝ: mun:angle-real P := A, Q := P, R := B, from H12, 1, 2
    reads the cosine of the angle the diagonals make at P
```

The equation is what the name means
and needs no reason. The membership m ∈ ℕ is then said there once, as an
`obtain`'s membership sentence is: no later step writes it, and a step that
cites the let has it as a line the let says, as `inequalities, from D1`
reads m ≥ 1 off it (`READERS.md`). A naming line that says no kind of number
has no reason line, and one that names a function says none.

A naming line in a theorem's statement, between its hypotheses and `then`,
says no kind of number: the statement is what the theorem assumes, and a
reason is a step of its proof.

What follows the name tells a naming line from the `let` that takes any
member: `let x ∈ ℝ` lets x be anything in ℝ, and `let m = gcd(s, w)` names
this one number. The name is new, so the line is never read as assuming
something of a letter already in use.

Above a file's first theorem a name belongs to the whole file, and another
file may import it (`import definition`). There it is a `define`, with `:=`:
`define T(k) := k(k + 1)/2, for k ∈ ℕ (D1)`. The word says where the name
lives: a `define` is the file's and may travel, a naming `let` is one
theorem's and goes no further. A `define` inside a theorem, and a naming
`let` above one, are reported. Each is cited by its label, each carries a
`reads` line, and what this document says of a define says it of either.

**A defined name and the term it names are one formula in a step that cites
the define.** A define states that the name is the term and nothing more, so
where a step cites it the name is expanded before two formulas are compared: a
step claiming `𝒫X = U ∪ T`, citing the defines of U and T, and a theorem
concluding the same thing with both sets written out say the same thing, and
the citation is checked as such. Expansion repeats, since a define may be
written in terms of an earlier one, and the step cites each define it passes
through: F(x) ∈ ℝ, where F(x) = f(x) + g(x), cites the defines of F and g.
A defined function applied is its rule at the argument, and standing alone it
is the rule itself, so `f : S → S` and a line saying every f(r) lies in S are
about one function however each is written (Euler's theorem, steps 8 to 10).

One exception: a step citing a theorem of its own file that is stated in
terms of that file's defines needs not cite those defines. The theorem and the
step speak of the same name, so nothing is expanded on the page:
`s(D(f(n), n)) ≠ D(f(n), n)` cites `thm:digit-step`, which is stated of s,
and not the define of s. A domain the define gives still has to be written:
where the theorem applies s to a term the step builds, as `digit-step-twice`
cited at D(f(n), n) applies it to s(D(f(n), n)), the step writes `requires
s(D(f(n), n)) ∈ ℤ`. A theorem of another file reaches the step's names only
through an import, which the step cites.

**A step that does not cite a define keeps the name as a name.** `x₁ ∈ S`,
from the define of S and lines saying x₁ ∈ [a, b] and f(x₁) < 0, uses what S
is and nothing of what x₁ is, and cites the one define
(intermediate-value, step 16.19). A reader asking where x₁ came from follows
the lines it cites back to the steps that cite the define of x₁.

**A define may name a function.** `let S(m) = Σ(j = 1 to m) j, for m ∈ ℕ
(D1)` is "let S(m) = 1 + 2 + … + m", with the domain said beside the rule.
`S(n)` is then S applied to n, and a step that needs what that is writes it
and cites the define: `S(k + 1) = Σ(j = 1 to k + 1) j` is a link cited `D1`,
with a `requires` line saying k + 1 is in the domain. A define may stand
where the proof first needs it, as the sum formula's S does, or in the
theorem's header, between its `let` and `assume` lines and `then`, as a
textbook says "let M, N ∈ ℕ₀ and define …; then …". A define in the header
is in the context of the theorem and its names: it may use any name the
`let` lines above it introduce, the statement may use it, and so may every
step. Euclid's algorithm is stated of the sequences it defines there, and a
walk's parity can be stated of `c(k, x)`, the count of its first k edges at
x, which names the walk's edges e (`tests/elaborator/induction-under-a-condition.proof`).
The statement means its define written out: the
kernel states it so, and a theorem citing it compares its own lines with
the rule, never with the name, which the citing proof does not have. A
function only one proof needs is defined there and nowhere else: it takes
no letter from any other proof.

**A define may name a function of two arguments**, each with its domain, in
order: `define G(a, n) := Σ(j = 0 to n) a^j, for a ∈ ℝ, n ∈ ℕ₀ (D1)` is "the
geometric series G(a, n) = 1 + a + … + aⁿ". G(a, k) is G applied to both, and
a step that needs what that is cites the define with a `requires` line for
each argument's domain the step does not otherwise have. A define names one
or two arguments; a function of more is not yet needed. Written above a
theorem, it lets the statement be about the object, as the geometric series
is stated `then G(a, n) = (1 − a^(n + 1))/(1 − a)`: the theorem is a fact about
G, and the reader meets G before the fact. A define over the theorem's own
`let` names, which do not exist above the theorem, goes in its header.

**A map is a function without a name.** `the map sending x ∈ A to e` is read
as a define's function is. Applied to a value it is e at that value: `(the
map sending y ∈ ℝ to y + 1)(x)` is x + 1, and a step reading it so says x ∈ A
where the page does not say it once. It is a function on A, which the page
says once. It may be given for an item's function letter, `thm:mean-value f
:= (the map sending x ∈ [a, b] to F(x))`, and what the item says of f(x) is
then said of F(x). A map of two arguments, `the map sending i ∈ I, j ∈ J to
e`, is read the same way at two values.

**A function may be defined by cases**, one case to a line, as a textbook
prints it inside a brace:

```proof
let h(x) = f(x)      if x ∈ C
           g⁻¹(x)    otherwise,  for x ∈ A                    (D2)
```

Every line but the last gives a value and the condition it is taken under;
the last gives the value `otherwise`, which is what makes the cases cover
the domain and never overlap without anything having to say so. A define
continues until the line carrying its label. The lines are one term,
`f(x) if x ∈ C, g⁻¹(x) otherwise`, which may also be written on one line,
and three or more cases nest from the right: `a if P, b if Q, c otherwise`
on three lines is `a if P, (b if Q, c otherwise) otherwise`. A step that
needs a value writes it and cites the define, from the line saying which
case it is in: `h(t) = g⁻¹(t)`, justified `D2, from` a line saying t ∉ C.
The line gives a case's condition or its negation, and the value claimed
is the one that case gives. That t is in h's domain, A, comes from a line
the step cites or from a `requires` line, as for any defined function.

**Sequences may be defined by recursion**, from a value at 0 and a rule
for the value at k + 1, and several together, as a textbook writes an
algorithm that keeps several numbers:

```proof
let a(0) = M,  b(0) = N,
    a(k + 1) = a(k)             if b(k) = 0
               b(k)             otherwise,
    b(k + 1) = 0                if b(k) = 0
               a(k) mod b(k)    otherwise,   for k ∈ ℕ₀                   (D1)
```

Each name has one value at 0 and one rule at k + 1, and a rule may be by
cases, written as above. The index is the letter after `for`, and runs over
ℕ₀, since the values start at 0. A rule says the value at k + 1 from the
values at k, of this name or another the define gives, from k itself, and
from what was named before the define; it names no value at any other index.
A value at 0 names no k, since there is none: the uncountability proof's
rules take f(k + 1), the term the interval after k + 1 steps must miss. The define
states the sequences and nothing about them, so a name is never unfolded
into its rule: a step that needs a value writes it and cites the define.
`a(0) = M` cites `D1`; `b(k + 1) = a(k) mod b(k)` cites `D1, from` a line
saying b(k) ≠ 0, the case being taken as for a define by cases, with a
`requires` line saying k ∈ ℕ₀. What holds of every value is proved by
induction on k, as anything true for all k ∈ ℕ₀ is.

A theorem stated over a sequence it defines by recursion speaks of that
sequence, and a step citing it speaks of the citing proof's sequence of the
same name, defined in its statement or its proof. The citation holds where
the two are one recursion: the same names in the same order, each with the
same value at 0 and the same rule at k + 1 as written, the index letter
apart and the cited theorem's letters given what the citation gives them.
A rule written another way, `1 + F(k)` for `F(k) + 1`, or with an identity
element more, defines another sequence, as set.mm writes it.

**A step may cite a define** by its label alone, `D1`, or with the lines it
uses, `D1, from 3`. Its claim is an equation with the name on one side,
applied or not, and on the other what the define says the name is: `M(C) =
{g(y) : y ∈ B ∖ {f(x) : x ∈ C}}` cites `D1, from` a line saying C ∈ 𝒫A.
This is the reading a calculation link citing the define makes, as a step
of its own.

**A define with a parameter also states what its function is on**, since the
domain is written beside the rule: `let t(c) = g·c, for c ∈ H (D2)`
gives `t is a function on H`, cited `D2` as a step or `from D2` in a
`requires` line. It states nothing about where the values lie, save what
the page says once of its rule: `t : H → gH`
is proved, from a line saying each value is in gH, as Lagrange's step 8.2
does. The domain may be a set another define names, as Euler's `let f(r) =
(r·a) mod n, for r ∈ S` is on S. A cited item whose `let g : D → ℝ` the citation fills with a defined
function, `g := g`, asks that type in a `requires` line citing the step that
proves it, as the mean value theorem's steps 10 to 15 do. The page says the
type once where the define's domain holds D and its rule, at a point of D,
is in ℝ by what the page says once: `t(j) = j + 1, for j ∈ ℕ` is a function
from ℕ into ℝ, and no line says so, while `t(j) = j/x` needs one. A citation
that writes the define out as its rule asks the same of it.

**A define outside a theorem belongs to the file.** Written above a theorem,
it may be used in that theorem's statement, as a textbook writes "let
Tₖ = k(k + 1)/2" once and then states results about Tₖ:

```proof
define T(k) := k(k + 1)/2, for k ∈ ℕ                     (D1)
       reads the k-th triangular number

theorem tri-one
  then T(1) = 1
```

Another file uses it by importing it, `import definition proofs/tri/T`, or
under a name of its own, `import definition proofs/tri/T as U`. Where a step
writes T out, the import gives a label and the step cites it,
`import definition proofs/tri/T (D1)`; an import gives no label that nothing
cites. Every define is imported as a `definition`, whether or not it takes an
argument. What the statement says in set.mm writes the rule out, so a
theorem citing `tri-one` needs nothing of T imported and its own T, if it has
one, is a different thing.

**A define may name a phrase**, a new way to say "A is a B", and give its
meaning:

```proof
define triangular-number: n is a triangular number means
       n ∈ ℕ and there is k ∈ ℕ with n = k(k + 1)/2                    (D1)
       reads n is k(k + 1)/2 for some natural number k
```

After `define` come the name the phrase is imported and cited by, a colon,
the phrase, `means`, and the meaning, which is a statement. The phrase opens
with a letter, `is`, and `a` or `an`. A letter in it is a slot, where a term
goes; a word of two letters or more is a word; and a letter joined to the
word after it by a hyphen is an attached slot, the p of `H is a Sylow
p-subgroup of G`, which takes one letter or one numeral and nothing longer.
A phrase has one, two or three slots, never two side by side. Its slots are
the letters its meaning leaves free: a letter of the phrase the meaning does
not use, or one the meaning uses and the phrase does not write, is a defect.
What a slot takes is what the meaning says it is, and a meaning that leaves
a slot's sort open is a defect.

Being a B includes being what a B is: the meaning says `n ∈ ℕ` itself, so a
line saying n is a triangular number gives n ∈ ℕ to a step citing the
define. A phrase with nothing to belong to says nothing of it, as `u is an
upper bound of S means for all s ∈ S, s ≤ u` does.

**A `where` part says what a slot is** where the meaning alone does not.
`|W|` could be the size of a set or the absolute value of a number, and
`a(i)` a function's value, a property holding of i, or a times i, so a
meaning that writes only those leaves W and a open. The define says them
after its meaning:

```proof
define clique: W is a clique in E of size at least n means
       n ≤ |W| and for all Y ⊆ W, if |Y| = 2 then Y ∈ E, where W is a set   (D1)
       reads W has at least n points, and every pair of them is in E
```

Each piece after `where`, between commas, is `<slot> is a set` or `<slot> is
a function from <things> to <things>`, things being numbers or points. It
says a kind and no fact. The meaning is what follows `means`, up to the
comma before `where`, and a fact the phrase should bring, such as `W is
finite`, is written in the meaning. A `where` part names only slots, each
once, and only a slot the meaning does not settle by itself; naming one it
settles already is a defect. Slots the meaning relates share what it leaves
open: here W holds things of any sort, and E holds sets of those things.

Every phrase also gives its negation: `4 is not a triangular number` is
`not (4 is a triangular number)`, one formula written two ways, so the not
is the whole meaning's, and π is not a triangular number because π ∉ ℕ. A
phrase whose own words write "and" or "or", `d is a common divisor of a and
b`, is bracketed beside "and" and "or" as betweenness is (Formulas).

A define of a phrase is an item of its file. A step uses what the phrase
means by citing it, by its label in its own file, `D1 n := 6, from 2`, and
in another file as a definition, `def:triangular-number n := 10, from 2`,
after `import definition proofs/tri/triangular-number`; the phrase and its
meaning are then one formula. A file writes a phrase only where it defines
it above the theorem or imports it. A define of a phrase is never mundane,
in the standard library or anywhere else: a proof imports the library's
`upper-bound` with `import definition stdlib/calculus/upper-bound` and cites
`def:upper-bound`. In set.mm a phrase is its meaning written out, so set.mm gets no symbol for
it.

The alternative was to make the name opaque and require a `substitute` step at
every crossing, which is what this document's rule about unfolding a definition
would ask for if a define were one. It is not: unfolding `even` or `divides`
tells a reader something, and unfolding a local name tells them nothing, while
costing fifteen bridging steps that each put back the long expression the name
was introduced to avoid.

**A define is followed by a `reads` line** giving, in words, what the name
means: one line, directly under the define, required on every one. Because a
define states only what its name is, the acceptance test has nothing to check
about it, and
a reader can meet a construction with no idea why it is there. The subsets
proof is where this was noticed: it named one half of a split and wrote the
other half out in full, so the two halves did not look like two halves.

**A block opener may carry a `note` line** saying in one line what the block
is doing. That is the only prose in a proof that is not about a single named
thing, and it is allowed because some of what a reader needs is not a formula:
that a proof is splitting a set into two families is not something any step
claims. It is one line, it sits under the method, and it is optional, because
most blocks do not need one. A part of a block may carry one too, directly
under its marker: a proof by cases says what each case does where the case
begins, rather than both at once above them.

Neither line is read by the elaborator, and nothing can judge the words. What
is checked is that a define has a reading, and that a note belongs to a block.
Prose anywhere a step can go is deliberately not allowed: the pressure to name
things well and to split blocks legibly is what makes the formal text the
readable one, and a free comment takes that pressure off.

**A calculation shows its working.** Each line of the chain gives its own
reason, as a textbook calculation does:

```proof
2.  n² = 2(2k² + 2k) + 1
    calculation
      n² = (2k + 1)²           substitute line 1
         = 4k² + 4k + 1        algebra
         = 2(2k² + 2k) + 1     algebra
```

- A chain line's reason is checked as if the line were a step of its own,
  claiming "the term above relates to this term".
- On a chain line, `algebra, from L` uses the equations line L says, as
  a step would. A link that only puts one side of L's equation for the
  other is better written `substitute line L` (`LINTER.md`).
- The requires lines of every chain line go under the calculation step,
  each written once.
- A chain line has no number, so nothing can cite it. A fact another step
  needs stays a numbered step, and a chain line may cite it by number.
- A reason that opens a block or names something new, such as `obtain` or
  `cases`, is never a chain line's reason.
- A statement that is not a chain shows its working the same way, with
  `substitute` and rows:

```proof
2.  d divides 1
    substitute
      d divides (n + 1) − n      1
      d divides 1                algebra
```

- Whether a step that only one chain line uses should move onto that line
  is the linter's question (`LINTER.md`). The checker accepts both.

**Every fact with a letter in it is written where a reader checks it**: as
a numbered step, or as a chain line or a substitute row with its reason
beside it. An identity `algebra` proves, an exponent law, a function value:
each is written out, never left for the reader to supply.

**A fact about closed numerals is not.** `0 + 1 = 1` has no letter in it and
gives a reader nothing to check but working it out, so it names
`arithmetic` where it is used rather than standing as a step for one line
to cite: as the source of a substitution, `substitute 0 + 1 = 1
(arithmetic)`; as the reason on a chain line, `= 1(1 + 1)/2    arithmetic`;
and as a `requires` line an item's hypothesis reads, `requires 9 = 3·3:
arithmetic` under `3 divides 9`. The checker refuses `arithmetic` in any of
these places for a fact with a letter in it, and the elaborator works each
fact out before proving it, as it does a step's.

A closed fact that takes a square root, or writes π, e, `ln`, `exp`, `sin`,
`cos` or `°`,
names `real arithmetic` in the same
places, and for the same reason: `substitute √8 = 2·√2 (real arithmetic)`,
`= 2·√2    real arithmetic` on a chain line, `requires √2 − 1 ≠ 0: real
arithmetic`. What each of the two decides, and the line between them, is in
`METHODS.md`.

Where none of those places can carry it, the fact is a numbered step after
all, justified by `arithmetic`: where the proof's shape asks a line and not a
reason. An induction's base case of numerals alone is one, read by the
induction as its base, and so is a fact a method takes only from the lines it
cites, as `transitivity` takes the birthday problem's 23 ≤ 365. A step a
numeral fact could have been written beside
instead is still a line too many.

A chain line whose terms have a letter in them may still name `arithmetic`
where the only change between them is closed: `2/1 − 2/(n + 1)` to
`2 − 2/(n + 1)` uses the fact `2/1 = 2` and nothing else. The two terms are
compared where they differ, and every differing piece must have no letter in
it; each is worked out as a closed fact is. A change touching a letter,
`k(k + 1)/2 + (k + 1)` to `(k + 1)((k + 1) + 1)/2`, is still `algebra`'s.

`real arithmetic` is named the same way, where each piece that changes is
closed and real arithmetic works it out: `cos(x)·cos(π)` to `cos(x)·(−1)`
uses the fact `cos(π) = −1` and nothing else.

```proof
4.3.  −a + −b ≤ |a| + |b|
      inequalities, from 2, 3
      requires |a| ∈ ℝ: mun:abs-real x := a
      requires |b| ∈ ℝ: mun:abs-real x := b

4.4.  |a + b| ≤ |a| + |b|
      calculation
        |a + b| = −(a + b)              def:abs x := a + b, from C2
                = −a + −b               algebra
                ≤ |a| + |b|             4.3
```

**A substitution names its variable, and its place in the list says
nothing.** Each `v := t` gives the value of the variable v, found by its
name: `def:divides n := c, d := d` and `d := d, n := c`
are one citation, and so are `instantiate x := 1, y := 2` and
`instantiate y := 2, x := 1`. This holds wherever `:=` is written: citing a
definition or a theorem, obtaining from one, and `instantiate`.

**No pair says what goes without saying.** A theorem's or an axiom's
variable is found by matching its statement against what the step claims
and cites, and its pair is written only where that does not fix it: `thm:
triple-from-parameters, from 1.2`, not `a := a, b := b, …`. A definition
folded or obtained from is about one letter, its subject, and with no pair
for it the subject is the proof's letter of the same name: `mun:coset, from
K1, K2` is about the proof's u. Its pair is written where the subject is
anything else, `mun:coset u := x`. So a definition's pair never names its
subject for itself, and a theorem's, `n := n`, only where matching does not
find n; the gate reports one a step is checked and built without.

Wherever a step's claim must be an instance of a formula, such as P(k + 1)
in an induction step, the conclusion of a theorem applied with `n := p`, or
the body of a definition, the instance is literal: the formula with the
substitution made and nothing else changed. A tidier form is a separate
`algebra` step, before or after the literal instance, and is never written
in its place.

**An identity element goes without saying, wherever it stands.** Two
formulas that are the same once their identity elements are dropped are one
formula, wherever the tools compare two: a claim and the instance it must
be, a `substitute` and the line it makes, a calculation's links, a cited
line and what it answers. P(n) saying L(p) ≤ L(p + n) has the base case
L(p) ≤ L(p), not L(p) ≤ L(p + 0); substituting p(a) = 0 into p(x) = (x −
a)·q(x) + p(a) gives p(x) = (x − a)·q(x); and no step says p = p + 0.
Nothing is cited for it. Which element is an identity, and on which side,
is the operation's notation record's to say (`identity`): 0 on either side
of +, and on the right of −; 1 on either side of ·, and on the right of /
and of a power. So x − 0 is x and 0 − x is not, x^1 is x and 1^x is not.
Nothing else is tidied: 0·x stays 0·x, since 0 is not an identity of the
product, terms are not reordered, and an element is never supposed where
none is written, to read x as x + 0. And an equation whose two sides are
then the same needs no line, as a set-builder's "t = a·m + b·n" at t :=
a·x + b·y with m := x and n := y.

An identity law holds of a number, so dropping an element asks that what is
left be one. That is said once where it is a letter's or a numeral's
(`READERS.md`), and is a `requires` line like any other membership where it
is not: x + 0 is x for a function's value only where the step says b(0) ∈ ℝ.

"The substitution made" is made on the parsed formula, not on the characters.
Replacing the characters of n with those of k + 1 in n(n + 1)/2 would give
k + 1(k + 1 + 1)/2, and the sum formula writes (k + 1)((k + 1) + 1)/2. The
parentheses are whatever the text needs in order to parse to the right shape.
Three consequences:

- **Parentheses are not compared.** Two texts that parse the same are the same
  instance, so a redundant parenthesis changes nothing. "Nothing else changed"
  is therefore a statement about the parsed formula and not about the
  characters a reader sees.
- **A substitution may not capture.** If the term being substituted names a
  variable that is bound where it lands, the step is rejected rather than the
  variable quietly renamed, and the text carries the condition in words, as
  `READERS.md` allows: "x does not appear in the expression". Renaming in
  silence would make the machine do something the page does not show. No
  substitution in the corpus is near this.
- **An unwritten pattern abstracts every occurrence.** Where P is read off a
  claim rather than written, as in an induction, it is the claim with every
  occurrence of the variable abstracted. That is what turns n(n + 1)/2 into
  (k + 1)((k + 1) + 1)/2 and it needs no further choice.

Two conventions apply at every citation and are stated here so that they
are not hidden steps:

- Where a cited item's conclusion is several sentences, a step may claim
  any one of them.
- Where a cited **line** claims several sentences, it supplies each of them
  separately and the step may use any, and it supplies their conjunction,
  joined from the left as a claim of several sentences is: "A. B" and
  "A and B" are one claim, so a line written either way gives `or-right` the
  B that is "A and B". Supplying the conjunction as well as the sentences asks
  nothing of a method, since an extra true fact never changes whether a step
  elaborates (`METHODS.md`). Thirty lines in the corpus claim more
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
- A cited equation may be read from either side — in a calculation, a
  `substitute`, or as an item's hypothesis — and nothing is written to say
  which: an equation says the same thing both ways, and the reader sees
  which side the line uses.
- Where a cited line claims a chain of equations, it supplies the equation
  between any two of its terms, either way round: `|QA| = |QB| = |QC| =
  |QD|` gives `|QA| = |QD|` as well as `|QA| = |QB|`. A step claiming a
  chain shows each equation between neighbouring terms, and the rest follow
  from those. `join` gives the chain from lines saying the neighbouring
  equations, and infers nothing, as it never does. From lines saying other
  pairs, a neighbouring equation is a deduction, made by a method such as
  `algebra`:

  ```
  4.  |QA| = |QB| = |QC| = |QD|
      join 1, 2, 3
  ```

  where lines 1, 2 and 3 say `|QA| = |QB|`, `|QB| = |QC|` and
  `|QC| = |QD|`.
- Inside a block that opened with `let x ∈ X`, a cited line saying "for
  all a ∈ X, P(a)" supplies P(x). The block is already about every member
  of X, and x names the one it is about, so the line is read as the block
  reads it: `5.8. For all a ∈ {2, …, p − 2}, a·f(a) ≡ 1 (mod p)`, cited in
  a block opened by `let x ∈ {2, …, p − 2}`, supplies `x·f(x) ≡ 1
  (mod p)`. The letters need not agree; the sets are written the same.
  Where blocks around the step open with two letters of X, the citation
  does not say which is meant, and the step is an `instantiate` instead.
  The line at any other term, such as f(x), is an `instantiate` too: the
  page says that the term is in X, which no `let` has said.

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
  `inequalities`. "p is a real number" is said once, where p is introduced,
  and a requires line where p is not a letter, a numeral or built from them
  (above, a membership is said once).
- Settled, and no longer on this list: whether "line 2.1" names one formula or
  each of its sentences. It supplies each of them, as the citation conventions
  above now say.
- Whether a proof consisting of a single block may omit the step that
  repeats the theorem's `then` line as its claim.
- Whether the statements of cited items, which `READERS.md` requires at the
  point of use, are satisfied by the pointer and the database table alone
  when reading on paper.
