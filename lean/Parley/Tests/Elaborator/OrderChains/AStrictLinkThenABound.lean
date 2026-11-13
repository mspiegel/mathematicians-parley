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

namespace Parley.Tests.Elaborator.OrderChains.AStrictLinkThenABound

theorem a_strict_link_then_a_bound (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (hH5 : a < b) (hH6 : b ≤ c) (hH7 : c < d) :
    a < d := by
  -- 1. calculation
  calc a < b := hH5
    _ ≤ c := hH6
    _ < d := hH7

end Parley.Tests.Elaborator.OrderChains.AStrictLinkThenABound
