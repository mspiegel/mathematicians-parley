module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.LeMaxLeft

theorem le_max_left (x : ℝ) (y : ℝ) :
    x ≤ max x y := by
  -- 1. mun:le-max
  have s1 : x ≤ max x y := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := x) (y := y))] | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := x) (y := y)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := x) (y := y)) | (have h := (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := x) (y := y)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.LeMaxLeft
