module

public import LeanBridges

/-! Written from tests/elaborator/a-power-said-not-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APowerSaidNotZero.APowerSaidNotZero

theorem a_power_said_not_zero (n : ℕ) (hH1 : 0 < n) (ε : ℝ) (x : ℝ) (hH4 : x ^ n > 0) (hH5 : 1 / x ^ n < ε) :
    1 - ε < 1 - 1 / x ^ n := by
  -- 1. inequalities
  have r10_1 : x ^ n ≠ 0 := by parley_side
  have s1 : 1 - ε < 1 - 1 / x ^ n := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.APowerSaidNotZero.APowerSaidNotZero
