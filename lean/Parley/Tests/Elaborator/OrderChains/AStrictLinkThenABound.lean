module

public import Tactics

/-! Written from tests/elaborator/order-chains.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.OrderChains.AStrictLinkThenABound

theorem a_strict_link_then_a_bound (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (hH5 : a < b) (hH6 : b ≤ c) (hH7 : c < d) :
    a < d := by
  -- 1. calculation
  have s1 : a < d := by
    calc a < b := by parley_side
      _ ≤ c := by parley_side
      _ < d := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.OrderChains.AStrictLinkThenABound
