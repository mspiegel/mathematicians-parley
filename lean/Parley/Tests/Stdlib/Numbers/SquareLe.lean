module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.SquareLe

theorem square_le (x : ℝ) (y : ℝ) (hH3 : x ≥ 0) (hH4 : y ≥ 0) :
    (x ≤ y ↔ x ^ 2 ≤ y ^ 2) := by
  -- 1. mun:numbers-square-le, from H3, H4
  have s1 : x ≤ y ↔ x ^ 2 ≤ y ^ 2 := by first | exact (Parley.Items.Stdlib.Numbers.mun_square_le (x := x) (y := y) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_square_le (x := x) (y := y) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_square_le (x := x) (y := y) (by parley_side) (by parley_side))
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.SquareLe
