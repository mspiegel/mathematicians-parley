module

public import Parley.Library

/-! Written from tests/elaborator/a-quotient-divisor-said-not-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AQuotientDivisorSaidNotZero.AQuotientDivisorSaidNotZero

theorem a_quotient_divisor_said_not_zero (ε : ℝ) (d : ℝ) (n : ℕ) (H3 : 0 < n) (H4 : ε / (2 * d) > 0) (H5 : 1 / (n : ℚ) > 0) (H6 : d > 0) :
    0 - ε / (2 * d) < 1 / (n : ℝ) := by
  -- 1. inequalities
  have s1 : 2 * d ≠ 0 := by parley_side
  -- 2. inequalities
  have r17_1 : 2 * d ≠ 0 := by parley_side
  have s2 : 0 - ε / (2 * d) < 0 := by parley_side
  -- 3. transitivity, from 2, H5
  have r23_1 : 2 * d ≠ 0 := by parley_side
  have s3 : 0 - ε / (2 * d) < 1 / (n : ℝ) := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.AQuotientDivisorSaidNotZero.AQuotientDivisorSaidNotZero
