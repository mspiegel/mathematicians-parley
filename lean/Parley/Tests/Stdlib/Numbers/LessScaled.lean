module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.LessScaled

theorem less_scaled (x : ℝ) (y : ℝ) (c : ℝ) (hH4 : c > 0) :
    (x < y ↔ c * x < c * y) := by
  -- 1. mun:numbers-less-scaled, from H4
  have s1 : x < y ↔ c * x < c * y := by first | exact (Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := c) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := c) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := c) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := c) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := c) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.LessScaled
