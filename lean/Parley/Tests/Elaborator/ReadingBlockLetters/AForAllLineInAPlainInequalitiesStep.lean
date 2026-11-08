module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInAPlainInequalitiesStep

theorem a_for_all_line_in_a_plain_inequalities_step (hH1 : ∀ x : ℝ, ¬ x ^ 2 < 0) :
    (∀ y : ℝ, y ^ 2 ≥ 0) := by
  -- 1. proof
  intro y
  -- 1.1. inequalities, from H1
  have := (hH1 y); parley_order

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInAPlainInequalitiesStep
