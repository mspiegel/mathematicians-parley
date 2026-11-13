module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/order-chains.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.OrderChains.TwoBoundsInARow

theorem two_bounds_in_a_row (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a ≤ b) (hH5 : b ≤ c) :
    a ≤ c := by
  -- 1. calculation
  calc a ≤ b := hH4
    _ ≤ c := hH5

end Parley.Tests.Elaborator.OrderChains.TwoBoundsInARow
