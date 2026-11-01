module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/elaborator/implied-bounds.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ImpliedBounds.ANaturalAtLeastOneForAnItem

theorem a_natural_at_least_one_for_an_item (n : ℕ) (hH1 : 0 < n) (c : ℝ) (hH3 : c > 0) :
    c * 1 ≤ c * (n : ℝ) := by
  -- 1. mun:multiply-le x := 1, y := n, from H1, H3
  have s1 : c * 1 ≤ c * (n : ℝ) := by linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (1 : ℝ)) (y := (n : ℝ)) (c := c) (by parley_side) (by parley_side))]
  all_goals parley_side

end Parley.Tests.Elaborator.ImpliedBounds.ANaturalAtLeastOneForAnItem
