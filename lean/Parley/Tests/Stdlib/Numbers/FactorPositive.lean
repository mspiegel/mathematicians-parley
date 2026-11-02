module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.FactorPositive

theorem factor_positive (u : ℝ) (v : ℝ) (hH3 : u ≥ 0) (hH4 : u * v > 0) :
    v > 0 := by
  -- 1. mun:numbers-factor-positive a := u, b := v, from H3, H4
  have s1 : v > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_factor_positive (a := u) (b := v) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := u) (b := v) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := u) (b := v) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_factor_positive (a := u) (b := v) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.FactorPositive
