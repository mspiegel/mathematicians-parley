module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.QuotientReal

theorem quotient_real (x : ℝ) (y : ℝ) (hH3 : y ≠ 0) :
    True := by
  -- 1. mun:numbers-quotient-real, from H3
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.QuotientReal
