# Pilot: √2 is irrational

A first hand-written artifact in the language defined by `READERS.md`. Its
purpose was to discover the skeleton of the readable text. The syntax it
settled is now in `SYNTAX.md`, and the proofs below are written to that
document. What remains provisional is listed in its "Not settled" section
and in the findings at the end of this file.

The file has three parts. The **skeleton** is the text as stored and
checked: every line of it is a field the elaborator reads, and nothing else.
The **rendered view** is what a viewer shows Reader A, produced from the
skeleton and the database with no human input; one theorem is rendered here
so the two can be compared line by line. The **database items** are the
definitions, theorems and methods the skeleton points to, with the statement
the viewer pulls in at each point of use.

---

## Theorem sqrt2-irrational

The skeleton is in `proof/sqrt2-irrational.proof`, which holds all three
theorems of this pilot. They are stored in dependency order, odd-square then
even-square then sqrt2-irrational, so that every pointer resolves to
something earlier; this file presents them the other way round, main theorem
first.

---

## Theorem odd-square

In `proof/sqrt2-irrational.proof`, first of the three.

---

## Theorem even-square

In `proof/sqrt2-irrational.proof`, second of the three. The rendered view
below is of this theorem.

---

## Rendered view of even-square

What a viewer shows for the skeleton above. Every sentence here is one of
three things: a field of the skeleton read back in words, the statement of
a database item pulled in at its pointer, or glue. Nothing in it was
written by hand for this theorem.

**Theorem even-square.** Let n be an integer. Assume n² is even. Then n is
even.

*Proof.*

1. n is not odd.
   By contradiction. Suppose that n is odd.

   1.1. n² is odd.
        By the theorem odd-square, from the hypothesis n ∈ ℤ and the
        supposition. That theorem states: let n be an integer; assume n is
        odd; then n² is odd.

   1.2. n² is not odd.
        By the theorem not-both, with n² as n, from the hypothesis n² is
        even. That theorem states: let n be an integer; assume n is even;
        then n is not odd.
        Requires n² ∈ ℤ, by the theorem int-closure from the hypothesis
        n ∈ ℤ. That theorem states: let a and b be integers; then a + b and
        a·b are integers.

   1.3. n² is odd and n² is not odd.
        By lines 1.1 and 1.2.

2. n is even or n is odd.
   By the theorem even-or-odd, from the hypothesis n ∈ ℤ. That theorem
   states: let n be an integer; then n is even or n is odd.

3. n is even.
   By lines 1 and 2.

∎

The glue is the words "By", "with ... as", "from the hypothesis", "That
theorem states", "Requires", "Suppose that", and the joining of the two
sentences of step 1.3 with "and". The view omits an instantiation that
substitutes a variable for itself: the skeleton's `n := n` at steps 1.1
and 2 is not rendered, while `n := n²` at step 1.2 is. Every pointer in the
skeleton is a link in the view. Which glue words to use is a viewer
question and not a property of the text.

---

## Database items

This pilot introduced most of the database. In `db/items.db`: `def:sqrt`,
`def:rational`, `def:irrational`, `def:even`, `def:odd`, `def:divides`,
`thm:lowest-terms`, `thm:int-closure`, `thm:even-or-odd`, `thm:not-both`,
`thm:odd-square`, `thm:even-square` and `thm:sqrt2-irrational`. In
`db/notation.db`: the number systems, the relations, the arithmetic
operations and the logical symbols. In `db/methods.db`: `arithmetic`,
`algebra`, `inequalities`, `substitute`, `lines`, `obtain`, `exhibit`,
`contradiction` and `calculation`, nine of the fourteen. The tables that used
to stand here were merged into those files; `DATABASE.md` records what the
merge decided.

`thm:sqrt2-irrational` was not in the table. It was the only pilot's main
theorem missing a row of its own, and the merge added it.

---

## What the pilot reveals

Findings about the vocabulary in `READERS.md`:

1. **Substitution of equals is missing.** Steps 3.2 and 3.7, and step 2 of
   odd-square, replace one side of an equation inside an earlier line. This
   is not "algebra" and not "by lines". It needs its own method.
2. **Calculation blocks are needed.** Three chained equalities read far
   better as a block than as three separate steps, and the block form has
   a clean elaboration into transitivity lemmas. The rule settled by the
   third pilot keeps the block and the steps: each equality is a numbered
   step with its own justification, and the block that follows only joins
   them, its lines citing those steps. Steps 3.7 to 3.9 and steps 2 to 5
   of odd-square are in that form. A viewer may fold the cited steps into
   the chain to show the textbook calculation.
3. **A block belongs to the claim it proves, and a theorem's Let/Assume
   is its statement.** A block is the justification of the step above it,
   and there is no separate closing step. The method on the step says what
   a reader checks about the block; for `contradiction` it is that the
   last sub-step is "P and not P". An earlier draft opened each lemma's
   proof with "Let n be any integer. Assume n² is even." as a step, closed
   it with a step named `generalise`, and stated the lemma as "for every
   integer n, if ...". The name misled: it read as widening to all integers
   when the block fixes one arbitrary n. `READERS.md` already settles this:
   Let and Assume are the theorem's hypotheses, so they belong in the
   statement, and the proof's last step is the conclusion. No method is
   involved. A Let/Assume block inside a proof, establishing an
   intermediate "for every" claim, would need a method, and this pilot has
   none; the induction pilot will, and its name should say what the reader
   checks, such as "by fixing n", not "generalise".
4. **"By lines" hides propositional logic.** Step 3 of even-square is a
   disjunctive syllogism. Whether a school reader can check that on paper is
   exactly the acceptance test, and it should be tried on a real reader.
5. **Dull facts are a category of their own.** The first draft wrote
   "q ≠ 0", "2 > 1" and four "is an integer" facts as numbered steps, and
   they read as if they hid a subtlety. Attaching each to the step it serves
   with "requires" removes that. Two further things came out of doing it:
   the first draft bundled "(√2)² = 2", which is an argument step, with
   "√2 ∈ ℝ" and "√2 ≥ 0", which are dull facts, in one line, and that
   bundle was what made the line look suspicious; and the first draft had
   silently omitted the dull fact "2 ∈ ℤ" at step 3.16, which the
   role-based classification surfaced.
6. **Dull facts do not nest.** The first draft wrote "√2 ∈ ℝ" as a
   requires line of the final step, and it needed "2 ∈ ℝ" and "2 ≥ 0"
   under it, a small tree. Later decided, after the intermediate value
   pilot grew a tree three deep and lost its numbering: a requires line
   has one citation and no more, and a fact that needs more is a numbered
   step before the step that needs it. So "√2 ∈ ℝ" is step 2, beside step
   1 which unfolds the same definition, and the final step cites it. The
   cost is a step whose purpose the reader meets only at the end; it is
   placed beside its twin so that the proof reads as two facts about √2,
   the argument, then the conclusion.
7. **A contradiction step does have a formula.** An earlier draft wrote
   line 3.17, and line 1.3 of even-square, as "lines X and Y contradict
   each other", with no claim and no pointer, and proposed an exception to
   the rule that every step states a claim. No exception is needed: the
   step claims "P and not P", by lines, and it is the last step of the
   block under the claim that the supposition serves. The rule in
   `READERS.md` stands as written.
8. **Quantifier moves need names.** "Call it r" takes an object from an
   existence claim, and "with witness q²" proves one. The first draft wrote
   both without a pointer, and wrote the existence claim at step 3.16 as
   "by lines", which is the propositional method. `READERS.md` says each
   quantifier move is a database item; the pilot now names two, `obtain`
   and `exhibit`, and they belong in the vocabulary. Later decided: the
   witness is never written, because the literal-instance rule makes the
   cited line determine it, so `exhibit q²: def:even n := p², from 3.3`
   became `def:even n := p², from 3.3`, and a bare "there is" claim is
   justified by `exhibit, from L`. `obtain` keeps its names, since a new
   name is a choice the reader cannot infer.
9. **Hypotheses of cited items are easy to miss by hand.** A second review
   listed, for every cited definition and theorem, each hypothesis of the
   item and checked that the step discharged it. That found seven missing
   dull facts in thirty steps: 2 ∈ ℝ for the square-root definition twice,
   p² ∈ ℤ and q² ∈ ℤ for the definition of even, 2 ≠ 0 for a division,
   2 ∈ ℤ for the definition of divides twice, and n² ∈ ℤ for not-both. It
   also found four steps applying a theorem to p, q or n without citing the
   line that makes it an integer. Rewriting the prose as the skeleton found
   four more: the definitions of even, odd and divides carry "Let n ∈ ℤ"
   and every `obtain` from them, and both `exhibit` steps for divides, had
   left that hypothesis uncited. This is exactly the check the elaborator
   performs mechanically, and it is the strongest argument yet that the
   text must be checked and not only read.
10. **The hypotheses of "by algebra" are not stated.** Steps 3.3, 3.8 and
    3.10 apply algebra to p, q and r, which are integers. The set.mm lemmas
    the method would expand to need p ∈ ℂ, so, by the role-based rule, "p is
    a number" is a dull fact of every algebra step. The pilot does not write
    it, because the method's definition does not yet say what it requires.
    Whether the method's expansion discharges membership in ℂ from ℤ by
    itself, or whether the text carries "requires p ∈ ℝ" on every algebra
    step, is decided when the method is defined.
11. **Two conventions hide a step each.** A calculation reads a cited
    equation right to left: line 3.9 opens with "2q² = p², by 3.3", and
    line 3.3 states p² = 2q². And a step claims one conjunct of a cited
    item's conclusion: step 1 takes "(√2)² = 2" out of the three conjuncts
    of def:sqrt, and the requires line at step 3 takes "√2 ∈ ℝ" out of the
    same three. Symmetry of equality and conjunction elimination are steps
    the kernel will see. Either the language says both are allowed at every
    citation, or they become explicit. The pilot allows both and marks them
    with "right to left" where the direction matters.
12. **Block shape: the claim is the step, the block is under it.** The
    first draft used two shapes. In one, the supposition was a numbered
    step, its consequences were sub-steps, and a later step at the outer
    level closed it. In the other, the claim was the step and the
    supposition opened its subproof. The second is now used throughout,
    for the reason that a reader meets the claim before the supposition,
    and it is what decision 3 of `GOALS.md` describes. It is also the
    shape of every hierarchical proof system in the reading list: Lamport's
    structured proofs, Isar's `have ... proof ... qed`, Mizar's
    `proof ... end`, and Lean's `have ... := by`. Isar and Mizar both also
    have a raw block form with the shape of the first draft, and treat the
    claim-first form as the structured one. Prose textbooks, Hammack and
    Velleman among them, look like the first shape on the page, but only
    because the claim is always stated just above, either as the theorem or
    as "We now show that P". Every Let/Assume block and every induction
    will take this shape.
13. **The text has three kinds of content, and only one is authored.** The
    first draft was prose, and in it three things were indistinguishable:
    the fields a checker reads (claim, method, cited items and lines,
    instantiation, witness, bound names, requires); the statements of cited
    items, which `READERS.md` requires at the point of use but which belong
    to the database and would drift if copied into the proof; and glue
    words such as "by", "applied to", "which holds since". The skeleton
    form keeps only the first. The viewer produces the other two. This also
    answers the first draft's open question about collecting symbol
    pointers in a table: in the skeleton every pointer is inline, because
    pointers are the text, and only the notation table remains. Nothing in
    the first draft was commentary in the sense of a sentence added purely
    to explain; if such sentences are wanted they are a fourth kind, and
    the skeleton has no place for them yet.
14. **Hypotheses and suppositions are cited by label.** Once the Let and
    Assume lines are part of the statement, the proof needs a way to cite
    them. The skeleton labels each hypothesis (H1, H2) and each supposition
    (S) and cites the label wherever a line number would be cited. Isar and
    Lean do the same.
15. **Connectives as words, conjunctions as sentences.** A draft of the
    skeleton wrote claims with ∧ ∨ ¬ and ∃, and step 3.1 was a five-part
    conjunction on two lines. Both were hard to read. The skeleton now
    writes "and", "or", "not" as words, writes ∃ as "there is ... with"
    and ¬∃ as "there is no ... with", and lets a claim be several
    sentences meaning their conjunction, so that step 3.1 is five short
    sentences and step 3.17 is "There is d ... . There is no d ... ." The
    symbols ∀ ∃ ¬ ∧ ∨ → ↔ stay in the notation table of `READERS.md`;
    what changes is that the text prefers the words where they exist. The
    symbols still appear where words would be worse, → and ↔ in the
    database items among them. Whether a claim of several sentences is one
    formula or several, for the purpose of citing "line 3.1", is a question
    the elaborator will have to answer; the pilot treats the whole step as
    one line.

Findings about set.mm:

16. **The kernel proof will not be set.mm's proof.** set.mm proves the
    theorem by descent with strong induction. Elaborating this text produces
    a different proof of the same statement, `( sqrt ` 2 ) e/ QQ`. That is
    expected and fine, and it means the up direction applied to set.mm's
    sqrt2irr would produce a different readable text, one built around
    induction.
17. **Even and odd are not set.mm primitives.** set.mm writes "2 ∥ n". The
    database for this project needs a definition of "even" in this language
    that elaborates to that.

Numbers, for the record: the main theorem has 21 numbered steps and 19
requires lines; the two lemmas together have 12 numbered steps and 5
requires lines. set.mm's proof has 99 essential steps in sqrt2irr and 69 in
sqrt2irrlem, and the parity lemma zesq has 74.
