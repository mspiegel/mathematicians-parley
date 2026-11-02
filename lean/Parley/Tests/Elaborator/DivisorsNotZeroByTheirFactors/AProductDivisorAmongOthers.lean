module

public import LeanBridges

/-! Written from tests/elaborator/divisors-not-zero-by-their-factors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.AProductDivisorAmongOthers

theorem a_product_divisor_among_others (m : ℤ) (hH2 : m > 0) :
    1 - 1 / (m : ℚ) + 1 / ((m : ℚ) * ((m : ℚ) + 1)) = 1 - 1 / ((m : ℚ) + 1) := by
  -- 1. inequalities, from H2
  have s1 : m + 1 > 0 := by parley_side
  -- 2. algebra
  have r30_1 : m ≠ 0 := by parley_side
  have r30_2 : m + 1 ≠ 0 := by parley_side
  have s2 : 1 - 1 / (m : ℚ) + 1 / ((m : ℚ) * ((m : ℚ) + 1)) = 1 - 1 / ((m : ℚ) + 1) := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.AProductDivisorAmongOthers
