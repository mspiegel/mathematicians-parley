module

public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-function-on-a-longer-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFunctionOnALongerRange.AFunctionOnALongerRange

theorem a_function_on_a_longer_range (n : ℕ) (hH1 : 0 < n) (t : ℤ → ℝ) (m : ℕ) (hH3 : 0 < m) (hH4 : True) :
    True := by
  -- 1. mun:product-real a := 1, b := m, from H4
  all_goals parley_side

end Parley.Tests.Elaborator.AFunctionOnALongerRange.AFunctionOnALongerRange
