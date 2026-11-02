module

public import LeanBridges
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.RangeBetween

theorem range_between (k : ℤ) (a : ℤ) (b : ℤ) (hH4 : a ≤ k) (hH5 : k ≤ b) :
    k ∈ Finset.Icc a b := by
  -- 1. def:sums-range-between, from H4, H5
  have s1 : k ∈ Finset.Icc a b := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := k) (a := a) (b := b))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := k) (a := a) (b := b))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Sums.RangeBetween
