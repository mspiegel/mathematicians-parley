module

public import Tactics

/-! Written from tests/elaborator/a-negative-power-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANegativePowerByArithmetic.ANegativePowerInASystem

theorem a_negative_power_in_a_system :
    (∃ m : ℕ, 0 < m ∧ (m : ℚ) = 1 ^ (-1 : ℤ)) := by
  -- 1. arithmetic
  have s1 : ∃ m : ℕ, 0 < m ∧ (m : ℚ) = 1 ^ (-1 : ℤ) := by parley_arith
  all_goals parley_side

end Parley.Tests.Elaborator.ANegativePowerByArithmetic.ANegativePowerInASystem
