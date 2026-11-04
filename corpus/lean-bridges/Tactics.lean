module

public import Mathlib
public import Factorials

/-!
# Tactics every generated proof uses

Each closes a goal of one kind the page leaves to its reader, and is named
for that kind, so a generated proof says what it asks and the search for
how is written once, here. Every alternative closes the goal or fails:
`ring`, `norm_num` and `apply` can succeed while leaving a goal open, so
each alternative ends in `done`, and `ring1` is used for `ring`.

This module holds the two nearly every file calls, and that the other
tactic modules call: `parley_side` and `parley_norm`. The rest are in one
module for each family (`AlgebraTactics`, `SubstTactics`,
`OrderTactics`, `PowerTactics`, `ComplexTactics`, `ArithTactics`), which a
generated file imports only when it calls one of them, since every file
importing a module is rebuilt when it changes.
-/

public section

/-- What a page leaves to its reader: a side condition of a cited item, a
membership said once, a line restated or joined from lines above, or a
block's last line taken as what the block owes. The lines above are taken
apart at each "and" first: `cases_type* And` leaves whole an "and" beside a
`Set.InjOn` (it reports no match), which `casesm* _ ∧ _` takes apart. -/
macro "parley_side" : tactic =>
  `(tactic| ((try cases_type* And) <;> (try casesm* _ ∧ _) <;> first
    | (assumption; done)
    -- An integer in ℕ₀, said `0 ≤ x` of an integer and `∃ m : ℕ, ↑m = x`
    -- where an item over any ring says it. Tried only on such a goal: on
    -- another, d ∣ 1 among them, the unifying recurses past Lean's limit,
    -- which ends `first`.
    | (show ∃ _ : ℕ, _; exact ⟨_, Int.toNat_of_nonneg (by omega)⟩; done)
    | ((cases_type* Exists); omega; done)
    -- A line that says the goal with its casts set otherwise, ((n : ℤ) : ℝ)
    -- for (n : ℝ), as an item on a range of integers gives a sequence's term.
    | (push_cast at *; assumption; done)
    | (apply Eq.symm; assumption; done)
    | (apply Ne.symm; assumption; done)
    | (constructor <;> assumption; done)
    | (constructor <;> assumption_mod_cast; done)
    -- Two sides that differ only in where a cast stands, x ↑(n + 1) and
    -- x (↑n + 1).
    | (push_cast; done)
    -- Something said of every integer of a range from 1, given of every
    -- natural number: each such integer is a natural above 0.
    | (intro k; intros; (try simp only [Finset.mem_Icc] at *); lift k to ℕ using (by omega);
        push_cast; apply_assumption; omega; done)
    | (positivity; done)
    | (omega; done)
    | (linarith; done)
    | (assumption_mod_cast; done)
    | (push_cast at *; linarith; done)
    | (qify at *; linarith; done)
    | (rify at *; linarith; done)
    | (apply lt_of_le_of_ne <;> (first | linarith | assumption | (apply Ne.symm; assumption)); done)
    | (norm_num at *; done)
    | (norm_num at *; subst_vars; norm_num; done)
    | (norm_cast at *; subst_vars; norm_num; done)
    | (norm_num at *; omega; done)
    | (norm_num at *; norm_cast at *; omega; done)
    | (contradiction; done)
    | (exfalso; apply ‹¬ _›; exact Int.ModEq.symm ‹_›; done)
    -- An integer a line gives as a quotient, (M! + 1)/N, in an equation of
    -- integers: in ℚ, with the division cleared, it is linear.
    | (qify at *; field_simp at *; linarith; done)
    -- A line about every natural number, in another type than the goal's:
    -- (n : ℚ) ≤ 2^n from "for all k ∈ ℕ, k ≤ 2^k" in ℤ, each cast moved
    -- out and the line applied.
    | (norm_cast at *; solve_by_elim; done)
    | (simp_all; done)))

/-- An identity of `algebra` with no line cited: a ring identity, or one
once the divisions are cleared. -/
-- The check `linear_combination` ends with: `ring1`, or `ring1` after the
-- casts are pushed in, where a function's argument is cast two ways,
-- C(↑m + 1, 1) beside C(↑(m + 1), 1), which ring1 takes as two atoms.
macro "parley_norm" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (push_cast; ring1; done)
    -- A function of numerals written two ways, (1 + 1)! beside 2!.
    | (norm_num [LeanBridges.Counting.factorial, Nat.factorial]; done))

end
