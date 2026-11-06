module

public import OrderTactics
public import Tactics

/-! Written from tests/elaborator/a-quotient-divisor-said-not-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AQuotientDivisorSaidNotZero.AQuotientDivisorSaidNotZero

theorem a_quotient_divisor_said_not_zero (ε : ℝ) (d : ℝ) (n : ℤ) (hH3 : 0 < n) (hH4 : ε / (2 * d) > 0) (hH5 : 1 / (n : ℚ) > 0) (hH6 : d > 0) :
    0 - ε / (2 * d) < 1 / (n : ℝ) := by
  -- 1. inequalities
  have s1 : 2 * d ≠ 0 := by parley_side
  -- 2. inequalities
  have r17_1 : 2 * d ≠ 0 := by parley_side
  have s2 : 0 - ε / (2 * d) < 0 := by parley_order
  -- 3. transitivity, from 2, H5
  have r23_1 : 2 * d ≠ 0 := by parley_side
  have s3 : 0 - ε / (2 * d) < 1 / (n : ℝ) := by parley_order
  all_goals exact s3

end Parley.Tests.Elaborator.AQuotientDivisorSaidNotZero.AQuotientDivisorSaidNotZero
