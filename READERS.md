# The two readers

Every readable proof in this project is written once, in one language, at
full expansion. Every step states a claim and names its justification. There
is no such thing as an obvious step, and no step is ever written without a
justification. What one reader finds obvious and another does not is never a
criterion anywhere in the system.

The language is Reader A's. Reader B reads the same text. The difference
between the two readers is only in how they use the viewer.

Nothing is assumed known. Every symbol, term, method and theorem used in a
step points explicitly to where it was defined or proved earlier in the
database. This holds for √, ∈, "even" and "prime" exactly as it holds for
limits or the axiom of choice. The pointer is always present; the reader
decides whether to follow it. A reader who does not know a term follows the
pointer and reads the definition, which is itself written in the same
language. This is what lets the acceptance test be about the text and not
about the reader's background.

## Reader A: school background

**Who.** Has completed high-school mathematics: algebra, functions, basic
geometry, perhaps an introduction to calculus. Has seen a handful of proofs,
such as the irrationality of √2 or the infinitude of primes, and possibly
induction. Has never studied logic or set theory as subjects.

**Brings nothing that is not in the database.** Reader A's school background
determines the language the text is written in, not a body of facts the text
may assume. Arithmetic, algebraic identities, the rules for inequalities,
"even", "prime", set membership, the number systems and function application
are all defined or proved in the database, in this language, and every use of
them in a step points to that place. What the school background buys is that
these pointers are ones Reader A will rarely need to follow.

**What one step may do.** Whatever the method it cites does. Every method,
including each quantifier move, each algebraic closure and each unfolding of
a definition, is a database item with a definition and is pointed to like any
other item. This document does not list permitted moves. Whether a method is
acceptable is decided by the acceptance test below, applied to each step that
uses it.

**Every step is written out.** In particular:

- Every case of a case analysis, each with its own conclusion.
- The induction hypothesis, stated in full, and both the base case and the
  step as separate parts.
- Every unfolding of a definition, marked as such.
- Every use of an earlier result, with the statement of that result shown at
  the point of use, not only its name.
- The assumption in a proof by contradiction, and the contradiction reached.
- Any step that introduces a new object ("let d be the greatest common
  divisor of a and b"), including why the object exists.
- Any use of the axiom of choice or of a non-obvious existence principle.
- The exact witness in an existence proof.
- A variable condition when it matters, written in words such as "x does not
  appear in the expression", never as a Metamath disjointness clause.

**Dull facts.** Some steps exist only to satisfy a hypothesis of a cited
definition, theorem or method: that a divisor is not zero, that a product of
integers is an integer, that 2 > 1. These are dull facts. The name describes
how they read, but they are classified by role, never by how obvious they
look: a step is a dull fact exactly when its only use is to discharge a
hypothesis of an item cited by another step, which the elaborator can
determine mechanically.

Dull facts are written, because nothing is assumed, but they are not written
as standalone lines the reader meets before knowing their purpose. They are
attached to the step they serve, with the word "requires" and the reason they
hold: "By algebra from line 3.3. Requires q ≠ 0, which holds since q > 0 in
line 3.1." The word "requires" tells the reader the fact is there because the
cited item demands it, not because there is a subtlety to find. A step that
bundles a dull fact together with a claim used in the argument is split, so
that each line has one role.

The viewer may collapse dull facts by default, since it can tell them apart
mechanically. That is a viewer setting and changes nothing in the text.

**Membership in a number system is a dull fact and merits no exception.**
That p is a real number is written, exactly as q ≠ 0 is, wherever a cited item
or method requires it. Exempting it was tempting: such a fact never fails, the
`let` line that states it is always in view, and writing it is expensive,
since the closure methods of `METHODS.md` work over a field and so need it for
every atom of every algebra and inequalities step. That is 97 lines across 42
steps in the current corpus, and one step carries ten. The exemption was
rejected. Whether a fact can fail is not the test. Whether the cited item
demands it is, and that is the test every other dull fact is held to. An
exemption here would be the first place the text asked a reader to supply
something the page does not say.

**Justification vocabulary.** The initial list of methods a step may cite.
Each is defined in the database with a specified expansion, and each use
points to that definition.

- by arithmetic
- by algebra
- by the rules for inequalities
- by definition of ⟨word⟩
- by ⟨earlier line⟩ and ⟨earlier line⟩
- by ⟨theorem⟩, with its statement shown
- by cases on ⟨condition⟩
- by induction on ⟨variable⟩
- suppose, for contradiction, that ⟨claim⟩

**Notation.** Standard mathematical notation: + · = < ≤ fractions, exponents,
√, |x|, braces for sets, ∈ for membership, f(x) for application, the names
ℕ ℤ ℚ ℝ, and the logical symbols ∀ ∃ ¬ ∧ ∨ → ↔. Every symbol, these
included, is defined in the database and every use points to its definition.
New notation is defined in the database before its first use, in the same
way. This is the whole notation of the language. How the connectives and
quantifiers are written in the text, as words where words exist, is fixed
in `SYNTAX.md`.

**Hidden entirely.** Metamath labels, class variables, deduction-form
contexts, disjoint-variable conditions, the distinction between wff, class
and set variables, and every syntax step. A set-existence hypothesis is
not hidden but written as "Let A be a set", which is what it says.

## Reader B: graduate degree in mathematics

**Who.** Holds a graduate degree in mathematics. Knows the standard results,
recognises routine arguments at a glance, and does not need them on screen.

**What Reader B gets.** The same text, and a viewer that can collapse any
step or block into its claim alone, hiding the justification and the
sub-steps beneath it. Collapsing is a presentation operation. It changes
nothing in the stored text, it carries no judgment about which steps are
routine, and the reader can reopen any collapsed step at any moment.

**What Reader B does not get.** A different text. No notation beyond
Reader A's. No justification vocabulary beyond Reader A's. No step written
with less justification because a knowledgeable reader would not need it.
Jargon, and steps justified by "clearly" or "so", are not permitted for any
reader, because they draw a line between what is obvious and what is only
obvious to some, and that line is gatekeeping.

## The acceptance test

There is one test, and it does not depend on who is reading. For every step:

1. Every symbol, term, method and theorem the step uses points to a
   definition or statement earlier in the database.
2. Given those pointed-to items and the earlier lines the step cites, a reader
   with Reader A's background can check with pen and paper, and without
   running any tool, that the step follows.

The reader may follow pointers as far as they like. A step that fails the
test is either split into smaller steps or given a method from the
vocabulary that it does satisfy. A step that uses anything without a pointer
fails the test.

## What every proof shares

- Every step states the claim it makes, in formula form. No step is a bare
  instruction.
- Every step names its justification, from the vocabulary above.
- Hypotheses are written as "Let x be a ..." and "Assume ...".
- The text has a kernel expansion, produced by the elaborator, never by hand.

## What is not decided here

- The concrete syntax of steps, blocks and methods. This document fixes what
  a step must contain, not how it is written down. What has been settled by
  the pilots is in `SYNTAX.md`.
- The exact boundary of "by algebra" and the other closure methods. Each
  method is itself defined in the database and pointed to like any other
  item; the boundary is set by what Reader A can check in one step, and the
  expansion that implements it is a later design question.
- How the viewer decides which steps to collapse by default, if any. That is
  a viewer setting and never a property of the text. Whatever the setting,
  its criterion is mechanical: by the method a step names, such as every
  `algebra` step; by a step's role, such as every requires line; or by
  repetition, such as the second application of a theorem the proof has
  already applied, which a textbook writes as "similarly". It is never a
  judgment about whether a step is obvious.
