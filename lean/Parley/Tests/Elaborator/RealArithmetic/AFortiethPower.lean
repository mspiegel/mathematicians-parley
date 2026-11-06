module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.AFortiethPower

theorem a_fortieth_power :
    (1 + Real.sqrt (2 : ℝ)) ^ 40 = 1023286908188737 + 723573111879672 * Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : (1 + Real.sqrt (2 : ℝ)) ^ 40 = 1023286908188737 + 723573111879672 * Real.sqrt (2 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.AFortiethPower
