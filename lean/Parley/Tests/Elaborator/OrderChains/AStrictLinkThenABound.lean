module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/order-chains.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.OrderChains.AStrictLinkThenABound

theorem a_strict_link_then_a_bound (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (hH5 : a < b) (hH6 : b ≤ c) (hH7 : c < d) :
    a < d := by
  -- 1. calculation
  calc a < b := by parley_side
    _ ≤ c := by parley_side
    _ < d := by parley_side

end Parley.Tests.Elaborator.OrderChains.AStrictLinkThenABound
