module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.QuotientNonneg

theorem quotient_nonneg (x : ℝ) (y : ℝ) (hH3 : x ≥ 0) (hH4 : y > 0) :
    x / y ≥ 0 := by
  -- 1. mun:numbers-quotient-nonneg, from H3, H4
  have s1 : x / y ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := x) (y := y) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := x) (y := y) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := x) (y := y) (by parley_side) (by parley_side))
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.QuotientNonneg
