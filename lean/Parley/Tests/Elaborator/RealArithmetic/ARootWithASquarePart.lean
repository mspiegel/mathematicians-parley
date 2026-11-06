module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootWithASquarePart

theorem a_root_with_a_square_part :
    Real.sqrt (8 : ℝ) = 2 * Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt (2 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.ARootWithASquarePart
