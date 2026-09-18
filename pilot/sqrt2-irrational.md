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

```
theorem sqrt2-irrational
  then √2 is irrational

1.  (√2)² = 2
    def:sqrt x := 2
    requires 2 ∈ ℝ: arithmetic
    requires 2 ≥ 0: arithmetic

2.  √2 ∈ ℝ
    def:sqrt x := 2
    requires 2 ∈ ℝ: arithmetic
    requires 2 ≥ 0: arithmetic

3.  √2 ∉ ℚ
    contradiction
    suppose √2 ∈ ℚ                                                    (S)

    3.1.  p ∈ ℤ. q ∈ ℤ. q > 0. √2 = p/q.
          There is no d ∈ ℤ with d > 1, d divides p, and d divides q.
          obtain p, q: thm:lowest-terms x := √2, from S

    3.2.  (p/q)² = 2
          substitute √2 = p/q (line 3.1) into line 1

    3.3.  p² = 2q²
          algebra, from 3.2
          requires q ≠ 0: inequalities, from 3.1

    3.4.  p² is even
          def:even n := p², from 3.3
          requires p² ∈ ℤ: thm:int-closure, from 3.1
          requires q² ∈ ℤ: thm:int-closure, from 3.1

    3.5.  p is even
          thm:even-square n := p, from 3.1, 3.4

    3.6.  r ∈ ℤ. p = 2r.
          obtain r: def:even n := p, from 3.1, 3.5

    3.7.  p² = (2r)²
          substitute p = 2r (line 3.6)

    3.8.  (2r)² = 4r²
          algebra

    3.9.  2q² = 4r²
          calculation
            2q² = p²        3.3, right to left
                = (2r)²     3.7
                = 4r²       3.8

    3.10. q² = 2r²
          algebra, from 3.9
          requires 2 ≠ 0: arithmetic

    3.11. q² is even
          def:even n := q², from 3.10
          requires q² ∈ ℤ: thm:int-closure, from 3.1
          requires r² ∈ ℤ: thm:int-closure, from 3.6

    3.12. q is even
          thm:even-square n := q, from 3.1, 3.11

    3.13. s ∈ ℤ. q = 2s.
          obtain s: def:even n := q, from 3.1, 3.12

    3.14. 2 divides p
          def:divides d := 2, n := p, from 3.1, 3.6
          requires 2 ∈ ℤ: arithmetic

    3.15. 2 divides q
          def:divides d := 2, n := q, from 3.1, 3.13
          requires 2 ∈ ℤ: arithmetic

    3.16. There is d ∈ ℤ with d > 1, d divides p, and d divides q.
          exhibit, from 3.14, 3.15
          requires 2 ∈ ℤ: arithmetic
          requires 2 > 1: arithmetic

    3.17. There is d ∈ ℤ with d > 1, d divides p, and d divides q.
          There is no d ∈ ℤ with d > 1, d divides p, and d divides q.
          lines 3.16, 3.1

4.  √2 is irrational
    def:irrational x := √2, from 3, 2
```

---

## Theorem odd-square

```
theorem odd-square
  let n ∈ ℤ                                                           (H1)
  assume n is odd                                                     (H2)
  then n² is odd

1.  k ∈ ℤ. n = 2k + 1.
    obtain k: def:odd n := n, from H1, H2

2.  n² = (2k + 1)²
    substitute n = 2k + 1 (line 1)

3.  (2k + 1)² = 4k² + 4k + 1
    algebra

4.  4k² + 4k + 1 = 2(2k² + 2k) + 1
    algebra

5.  n² = 2(2k² + 2k) + 1
    calculation
      n² = (2k + 1)²           2
         = 4k² + 4k + 1        3
         = 2(2k² + 2k) + 1     4

6.  n² is odd
    def:odd n := n², from 5
    requires n² ∈ ℤ: thm:int-closure, from H1
    requires 2k² + 2k ∈ ℤ: thm:int-closure, from 1
```

---

## Theorem even-square

```
theorem even-square
  let n ∈ ℤ                                                           (H1)
  assume n² is even                                                   (H2)
  then n is even

1.  n is not odd
    contradiction
    suppose n is odd                                                  (S)

    1.1.  n² is odd
          thm:odd-square n := n, from H1, S

    1.2.  n² is not odd
          thm:not-both n := n², from H2
          requires n² ∈ ℤ: thm:int-closure, from H1

    1.3.  n² is odd. n² is not odd.
          lines 1.1, 1.2

2.  n is even or n is odd
    thm:even-or-odd n := n, from H1

3.  n is even
    lines 1, 2
```

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

Every item below must exist in the database, written in this language,
before this file can be accepted. The middle column is the statement the
viewer shows at each point of use. The right-hand column is the set.mm item
the elaborator would most plausibly target, where one exists.

Notation. Every symbol has a pointer in the database; in the skeleton the
pointers for symbols are not written at each occurrence.

| symbols | what they are | set.mm |
|---|---|---|
| ℝ ℤ ℚ | the number systems | cr, cz, cq |
| ∈ ∉ = ≠ < > ≥ | membership, equality, order | wcel, wnel, wceq, wne, clt, ... |
| + · / ² √ | arithmetic operations | caddc, cmul, cdiv, cexp, csqrt |
| ∀ ∃ ¬ ∧ ∨ → ↔ | logical symbols | wal, wex, wn, wa, wo, wi, wb |

Definitions and theorems.

| pointer | statement | set.mm |
|---|---|---|
| def:sqrt | Let x ∈ ℝ. Assume x ≥ 0. Then √x ∈ ℝ. √x ≥ 0. (√x)² = x. | df-sqrt, sqrtth, sqrtge0, resqrtcl |
| def:rational | x ∈ ℚ ↔ there are p ∈ ℤ and q ∈ ℤ with q ≠ 0 and x = p/q | elq |
| def:irrational | x is irrational ↔ x ∈ ℝ and x ∉ ℚ | (ℝ ∖ ℚ, as in sqrt2irr0) |
| def:even | Let n ∈ ℤ. n is even ↔ there is k ∈ ℤ with n = 2k | (set.mm: 2 ∥ n, dvds) |
| def:odd | Let n ∈ ℤ. n is odd ↔ there is k ∈ ℤ with n = 2k + 1 | (set.mm: ¬ 2 ∥ n) |
| def:divides | Let d ∈ ℤ, n ∈ ℤ. d divides n ↔ there is k ∈ ℤ with n = d·k | df-dvds |
| thm:lowest-terms | Let x ∈ ℚ. Then there are p ∈ ℤ and q ∈ ℤ with q > 0, x = p/q, and no d ∈ ℤ with d > 1, d divides p, and d divides q. | qredeu or similar |
| thm:int-closure | Let a ∈ ℤ, b ∈ ℤ. Then a + b ∈ ℤ. a·b ∈ ℤ. | zaddcl, zmulcl |
| thm:even-or-odd | Let n ∈ ℤ. Then n is even or n is odd. | zeo |
| thm:not-both | Let n ∈ ℤ. Assume n is even. Then n is not odd. | (from zeo2 / oddm1even) |
| thm:odd-square | proved above | (zesq covers it) |
| thm:even-square | proved above | zesq |

Methods. The middle column is what a reader checks when a step cites the
method.

| pointer | what the reader checks | set.mm |
|---|---|---|
| arithmetic | a closed numeral expression has the stated value, order, or membership in ℕ ℤ ℚ ℝ | decimal arithmetic lemmas, 2re, 2z |
| algebra | the claim follows from the cited equations by ring and field identities | (a normaliser over ℂ lemmas) |
| inequalities | the claim follows from the cited order facts by the rules for inequalities | ltne, ... |
| substitute | the claim is the cited line with one side of the cited equation replaced by the other | oveq1d, eqtrd, ... |
| lines | the claim follows from the cited lines by propositional logic | syl, mpd, jca, ... |
| obtain | the cited item concludes an existence claim; the new names stand for its objects and the claim is its body | exlimiv, eximd, ... |
| exhibit | the claim is a bare "there is" sentence; the cited lines are its body with some value in place of the variable, which the reader finds by comparison | rspcev, spcev, ... |
| contradiction | the block under the step assumes the negation of the claim and ends by stating some P and also not P | pm2.65, condan, ... |
| calculation | each line of the chain is justified and the claim is first term = last term | eqtrd, 3eqtrd, ... |

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

Numbers, for the record: the main theorem has 21 numbered steps and 14
requires lines; the two lemmas together have 12 numbered steps and 3
requires lines. set.mm's proof has 99 essential steps in sqrt2irr and 69 in
sqrt2irrlem, and the parity lemma zesq has 74.
