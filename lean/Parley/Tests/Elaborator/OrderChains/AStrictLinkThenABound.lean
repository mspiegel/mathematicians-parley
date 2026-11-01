module

public import Parley.Library

/-! Written from tests/elaborator/order-chains.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.OrderChains.AStrictLinkThenABound

theorem a_strict_link_then_a_bound (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (H5 : a < b) (H6 : b ≤ c) (H7 : c < d) :
    a < d := by
  -- 1. calculation
  have s1 : a < d := by
    calc a < b := by parley_side
      _ ≤ c := by parley_side
      _ < d := by parley_side
  parley_side

end Parley.Tests.Elaborator.OrderChains.AStrictLinkThenABound
