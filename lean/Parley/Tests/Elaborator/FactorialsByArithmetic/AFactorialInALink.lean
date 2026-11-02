module

public import LeanBridges

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialInALink

theorem a_factorial_in_a_link (x : ℝ) (hH2 : x = 1 / (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℝ)) :
    x = 1 - 1 / (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℝ) := by
  -- 1. calculation
  have s1 : x = 1 - 1 / (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℝ) := by
    calc x = 1 / (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℝ) := by parley_side
      _ = 1 - 1 / (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℝ) := by norm_num
  all_goals parley_side

end Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialInALink
