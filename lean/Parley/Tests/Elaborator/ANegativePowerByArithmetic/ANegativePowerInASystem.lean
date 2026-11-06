module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init

/-! Written from tests/elaborator/a-negative-power-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANegativePowerByArithmetic.ANegativePowerInASystem

theorem a_negative_power_in_a_system :
    (∃ m : ℤ, 0 < m ∧ (m : ℚ) = 1 ^ (-1 : ℤ)) := by
  -- 1. arithmetic
  have s1 : ∃ m : ℤ, 0 < m ∧ (m : ℚ) = 1 ^ (-1 : ℤ) := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.ANegativePowerByArithmetic.ANegativePowerInASystem
