module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInATransitivity

theorem a_for_all_line_in_a_transitivity (b : ℝ) (hH2 : ∀ x : ℝ, x < x + 1) :
    (∀ y : ℝ, y + 1 < b → y < b) := by
  -- 1. proof
  intro y
  intro hA1
  -- 1.1. transitivity, from H2, A1
  have := (hH2 y); parley_order

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInATransitivity
