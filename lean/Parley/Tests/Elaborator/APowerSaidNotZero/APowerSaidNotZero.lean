module

public import OrderTactics
public import Tactics

/-! Written from tests/elaborator/a-power-said-not-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APowerSaidNotZero.APowerSaidNotZero

theorem a_power_said_not_zero (n : ℤ) (hH1 : 0 < n) (ε : ℝ) (x : ℝ) (hH4 : x ^ n.toNat > 0) (hH5 : 1 / x ^ n.toNat < ε) :
    1 - ε < 1 - 1 / x ^ n.toNat := by
  -- 1. inequalities
  have r10_1 : x ^ n.toNat ≠ 0 := by parley_side
  have s1 : 1 - ε < 1 - 1 / x ^ n.toNat := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.APowerSaidNotZero.APowerSaidNotZero
