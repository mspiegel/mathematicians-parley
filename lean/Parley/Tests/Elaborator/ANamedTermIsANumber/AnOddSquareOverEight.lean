module

public import Parley.Library

/-! Written from tests/elaborator/a-named-term-is-a-number.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANamedTermIsANumber.AnOddSquareOverEight

theorem an_odd_square_over_eight (N : ℤ) :
    ((2 * (N : ℚ) + 1) ^ 2 - 1) / 8 = (N : ℚ) * ((N : ℚ) + 1) / 2 := by
  set M : ℤ := 2 * N + 1 with hD1
  -- 1. algebra, from D1
  have s1 : ((M : ℚ) ^ 2 - 1) / 8 = (N : ℚ) * ((N : ℚ) + 1) / 2 := by
    have hD1_w : (M : ℚ) = 2 * (N : ℚ) + 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) hD1; push_cast at h; linear_combination h
    linear_combination ((2 * (M : ℚ) + 4 * (N : ℚ) + 2) / ((8) * (2))) * hD1_w
  all_goals parley_side

end Parley.Tests.Elaborator.ANamedTermIsANumber.AnOddSquareOverEight
