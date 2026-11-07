module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-function-on-a-longer-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFunctionOnALongerRange.AFunctionOnALongerRange

theorem a_function_on_a_longer_range (n : ℤ) (hH1 : 0 < n) (t : ℤ → ℝ) (m : ℤ) (hH3 : 0 < m) (hH4 : True) :
    True := by
  -- 1. mun:product-real a := 1, b := m, from H4
  all_goals parley_side

end Parley.Tests.Elaborator.AFunctionOnALongerRange.AFunctionOnALongerRange
