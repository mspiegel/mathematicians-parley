module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.LeCases

theorem le_cases (x : ℝ) (y : ℝ) :
    (x ≤ y ↔ x < y ∨ x = y) := by
  -- 1. mun:numbers-le-cases
  have s1 : x ≤ y ↔ x < y ∨ x = y := by first | exact (Parley.Items.Stdlib.Numbers.mun_le_cases (x := x) (y := y)) | exact ((Parley.Items.Stdlib.Numbers.mun_le_cases (x := x) (y := y))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_le_cases (x := x) (y := y)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_le_cases (x := x) (y := y))
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.LeCases
