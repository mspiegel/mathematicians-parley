# Pilot: 1 + 2 + ... + n = n(n + 1)/2

The second pilot, and the first written to `SYNTAX.md` from the start. Its
purpose is to exercise induction, which `READERS.md` requires to be written
with the hypothesis stated in full and the base case and the step as
separate parts, and which forces the one item on the "Not settled" list of
`SYNTAX.md` that the √2 pilot did not reach: a Let/Assume block inside a
proof, establishing an intermediate "for every" claim.

The theorem appears in the induction chapter of Hammack's Book of Proof
and is `arisum` in set.mm. Two forms in this file are new and provisional: the
`induction` justification with its `base` and `step` parts, and the `fix`
justification for the step case. Both are described in the database items
table and discussed in the findings.

The sum 1 + 2 + ... + n is not notation in `READERS.md`, and "..." hides a
definition. The pilot defines S(n) by recursion instead, and the theorem is
stated about S.

---

## Theorem sum-formula

The skeleton is `proof/sum-formula.proof`. The items it cites are in `db/`.

---

## Rendered view

**Theorem sum-formula.** Let n be a natural number. Then S(n) = n(n + 1)/2.

*Proof.*

1. S(n) = n(n + 1)/2.
   By induction on n starting at 1, from the hypothesis n ∈ ℕ. The principle states: let
   n be a natural number; assume P(1), and assume that for every natural
   number k, if P(k) then P(k + 1); then P(n).

   Base case.

   1.1. S(1) = 1.
        By the definition of S. That definition states: S(1) = 1; for
        every natural number n, S(n + 1) = S(n) + (n + 1).

   1.2. 1 = 1(1 + 1)/2.
        By arithmetic.

   1.3. S(1) = 1(1 + 1)/2.
        Calculation:
        S(1) = 1, by line 1.1,
        = 1(1 + 1)/2, by line 1.2.

   Step case.

   1.4. For every natural number k, if S(k) = k(k + 1)/2 then
        S(k + 1) = (k + 1)((k + 1) + 1)/2.
        Fix k. Let k be a natural number. Assume S(k) = k(k + 1)/2.

        1.4.1. S(k + 1) = S(k) + (k + 1).
               By the definition of S with k as n, from k ∈ ℕ.

        1.4.2. S(k) + (k + 1) = k(k + 1)/2 + (k + 1).
               By substituting the assumption S(k) = k(k + 1)/2.

        1.4.3. k(k + 1)/2 + (k + 1) = (k + 1)((k + 1) + 1)/2.
               By algebra.

        1.4.4. S(k + 1) = (k + 1)((k + 1) + 1)/2.
               Calculation:
               S(k + 1) = S(k) + (k + 1), by line 1.4.1,
               = k(k + 1)/2 + (k + 1), by line 1.4.2,
               = (k + 1)((k + 1) + 1)/2, by line 1.4.3.

∎

---

## Database items

This pilot introduced `def:S` and `thm:sum-formula` in `db/items.db`, the ℕ
and S rows in `db/notation.db`, and the `induction` and `fix` methods in
`db/methods.db`. The table that used to stand here was merged into those
files; `DATABASE.md` records what the merge decided.

---

## What the pilot reveals

1. **Induction is a block with two named parts.** The `base` and `step`
   words are not steps and not claims; they mark which of the two parts of
   the induction principle a sub-step discharges. They are the first
   markers in the syntax that are neither a claim, a justification, a
   requires line, nor a label. Three alternatives were considered: no
   markers, with the reader matching the two sub-steps to the principle by
   their form; the parts named on the method line, as `base 1.1, step
   1.2`; and induction cited as a theorem with two hypotheses, which is
   what set.mm's `nnind` is. Markers on their own lines were chosen
   because they read like a textbook. "Part markers" are now a line kind
   in `SYNTAX.md`, available to any method whose definition names parts;
   a case analysis is the obvious next user.
2. **The step case is the missing method.** Step 1.4 claims a "for every
   ... if ... then" formula and proves it with a block that opens with
   `let` and `assume` lines, exactly as a theorem's statement does. The
   pilot names the method `fix`, after the first thing the block does. At
   theorem level no method is named, because the `let` and `assume` are
   the statement; inside a proof they are introduced by a step and so need
   a method. The two are the same rule, and the reader checks the same
   thing: the last step of the block is the conclusion of the claim, with
   the block's `let` and `assume` in force. An alternative was to write
   the step's claim itself as `let`, `assume`, `then` lines with no method,
   making the step a small unnamed theorem. It was rejected as less
   explicit: the claim would not be a formula, and the block would be the
   only one whose rule is not named on the line above it. The form here is
   now in `SYNTAX.md`.
3. **Instances are literal.** The step case must conclude P(k + 1) exactly
   as P reads with k + 1 in place of n, which is (k + 1)((k + 1) + 1)/2, not
   the tidier (k + 1)(k + 2)/2. Writing the tidy form would hide an algebra
   step inside the induction. The algebra step 1.4.3 and the chain at
   1.4.4 therefore end at the literal form. The rule is now in `SYNTAX.md`: instances are
   literal, and a tidier form is a separate `algebra` step, before or after
   the literal one, never in its place. Two alternatives were rejected: a
   requires line on the step bridging the tidy claim to the literal
   instance, which would widen what requires lines do; and matching
   instances up to arithmetic, which is a hidden method.
4. **"..." is a definition in disguise.** The theorem as a textbook states
   it, 1 + 2 + ... + n, has no formula behind the dots. The pilot defines
   S by recursion, with two sentences that a step cites one at a time, and
   the base case cites the first without any hypothesis while the step
   cites the second with n := k. set.mm writes the sum with Σ over an
   interval, and its two recursion facts are separate theorems; def:S will
   have to elaborate to those. A reader who wants the theorem about
   1 + 2 + ... + n gets it only through the definition of S, which is the
   honest state of affairs.
5. **A one-step proof.** The whole proof is step 1, whose claim is the
   theorem's conclusion. That is the claim-first shape applied at the top
   level with nothing else to say, and it is not wrong, but it means the
   theorem's conclusion is written twice, once as `then` and once as the
   claim of step 1. Whether a proof may consist of the block alone, with
   the `then` line serving as the claim, is a syntax question to decide
   when a second single-block proof appears.
6. **The hypotheses of `algebra` again.** Step 1.4.3 applies
   algebra to k, a natural number. As in the √2 pilot, the requires line
   for "k is a number" is not written, and the gap is the one recorded in
   `SYNTAX.md`.
7. **ℕ starts at 1.** The base case is S(1), because set.mm's ℕ is
   1, 2, 3, ... and its induction principle `nnind` starts there. A reader
   taught that the natural numbers begin at 0 will need the pointer on ℕ
   to say so. Nothing in the text assumes either convention beyond that
   pointer.

Numbers, for the record: 9 numbered steps, 1 requires line. The essential
step count of set.mm's arisum has not been measured; set.mm is not on disk
at the moment, and the count belongs in the selection table planned in
`GOALS.md`.
