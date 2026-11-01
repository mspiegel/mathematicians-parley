module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ACubeOfAProductOfRoots

theorem a_cube_of_a_product_of_roots :
    (Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ)) ^ 3 = 6 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) := by
  -- 1. real arithmetic
  have s1 : (Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ)) ^ 3 = 6 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmetic.ACubeOfAProductOfRoots
