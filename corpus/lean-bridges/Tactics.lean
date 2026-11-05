module

public import Mathlib
public import ParleySimp

/-!
# Tactics every generated proof uses

Each closes a goal of one kind the page leaves to its reader, and is named
for that kind, so a generated proof says what it asks and the search for
how is written once, here. Every alternative closes the goal or fails:
`ring`, `norm_num` and `apply` can succeed while leaving a goal open, so
each alternative ends in `done`, and `ring1` is used for `ring`.

## How the tactic modules are laid out

Lean rebuilds every file that imports a module, directly or through
another, whenever that module changes. The layout keeps each change's
rebuild to the files that use what changed.

- This module, the core, holds only `parley_side` and `parley_norm`, which
  nearly every generated file calls and every other tactic module calls in
  turn. A change here rebuilds every file, so it imports nothing but
  Mathlib and changes only when these two must.
- Each family of tactics most files do not call is a module of its own,
  imported only by the files that name one of its tactics:
  `AlgebraTactics`, `SubstTactics`, `OrderTactics`, `PowerTactics`,
  `ComplexTactics`, `ArithTactics`, `SetTactics`, `RealTactics`,
  `WholeTactics`.
- A definition only some files write, which a tactic called everywhere
  must see through, is not imported here. The tactic calls `norm_num` or
  `field_simp` with the simp set `parley_unfold` (`ParleySimp`, which
  imports nothing but Mathlib) at the place in its list that way belongs,
  and a module imported only by the files that write the definition tags it
  into the set. Elsewhere the set is empty and the call is a plain one. The
  factorial and the binomial coefficient are tagged so, in
  `FactorialTactics`, and a change to `Factorials` rebuilds only the files
  that write them. A `macro_rules` rule for the tactic would be tried
  before its own alternatives, and a hook with a default would be tried
  again after the rule failed; the set changes neither the order nor the
  number of tries.
- A case for a goal the writer can recognise where it writes the call goes
  in a tactic of its own with its own name, as `parley_whole_side`, rather
  than among `parley_side`'s alternatives.

Which file imports which module is decided by the build from the file's
Lean text (`library_imports` in `src/tools/build/lean.rs`).
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
    -- A function of numerals written two ways, (1 + 1)! beside 2!, where
    -- the file's modules tag the function into `parley_unfold`.
    | (norm_num [parley_unfold]; done))

end
