module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsNonneg

theorem abs_nonneg (x : ℝ) :
    abs x ≥ 0 := by
  -- 1. mun:numbers-abs-nonneg
  have s1 : abs x ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (x : ℂ)))] | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (x : ℂ))); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_nonneg (x := (x : ℂ))); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.AbsNonneg
