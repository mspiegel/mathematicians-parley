module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ASquareOfASumOfThreeRoots

theorem a_square_of_a_sum_of_three_roots :
    (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ)) ^ 2 = 10 + 2 * Real.sqrt (6 : ℝ) + 2 * Real.sqrt (10 : ℝ) + 2 * Real.sqrt (15 : ℝ) := by
  -- 1. real arithmetic
  have s1 : (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ)) ^ 2 = 10 + 2 * Real.sqrt (6 : ℝ) + 2 * Real.sqrt (10 : ℝ) + 2 * Real.sqrt (15 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.ASquareOfASumOfThreeRoots
