module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.AFortiethPower

theorem a_fortieth_power :
    (1 + Real.sqrt (2 : ℝ)) ^ 40 = 1023286908188737 + 723573111879672 * Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : (1 + Real.sqrt (2 : ℝ)) ^ 40 = 1023286908188737 + 723573111879672 * Real.sqrt (2 : ℝ) := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmetic.AFortiethPower
