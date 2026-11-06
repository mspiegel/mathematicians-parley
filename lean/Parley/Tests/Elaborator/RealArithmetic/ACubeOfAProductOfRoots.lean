module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ACubeOfAProductOfRoots

theorem a_cube_of_a_product_of_roots :
    (Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ)) ^ 3 = 6 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) := by
  -- 1. real arithmetic
  have s1 : (Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ)) ^ 3 = 6 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.ACubeOfAProductOfRoots
