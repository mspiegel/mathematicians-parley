module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/order-chains.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.OrderChains.TwoBoundsInARow

theorem two_bounds_in_a_row (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a ≤ b) (hH5 : b ≤ c) :
    a ≤ c := by
  -- 1. calculation
  calc a ≤ b := by parley_side
    _ ≤ c := by parley_side

end Parley.Tests.Elaborator.OrderChains.TwoBoundsInARow
