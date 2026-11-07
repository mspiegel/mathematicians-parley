module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartInACalculationLink

theorem an_and_part_in_a_calculation_link (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ b = 2) :
    b = 1 + 1 := by
  -- 1. calculation
  have s1 : b = 1 + 1 := by
    calc b = 2 := by parley_side
      _ = 1 + 1 := by norm_num
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartInACalculationLink
