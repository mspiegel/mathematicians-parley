module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.LeMaxRight

theorem le_max_right (x : ℝ) (y : ℝ) :
    y ≤ max x y := by
  -- 1. mun:le-max
  have s1 : y ≤ max x y := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := x) (y := y))] | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := x) (y := y)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := x) (y := y)) | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := x) (y := y)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.LeMaxRight
