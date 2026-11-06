module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ASquareOfASumWithARoot

theorem a_square_of_a_sum_with_a_root :
    (1 + Real.sqrt (2 : ℝ)) ^ 2 = 3 + 2 * Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : (1 + Real.sqrt (2 : ℝ)) ^ 2 = 3 + 2 * Real.sqrt (2 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.ASquareOfASumWithARoot
