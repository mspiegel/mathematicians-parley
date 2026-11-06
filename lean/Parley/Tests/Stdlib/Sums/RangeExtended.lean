module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.RangeExtended

theorem range_extended (m : ℤ) (n : ℤ) (j : ℤ) (hH3 : j ∈ Finset.Icc m n) :
    j ∈ Finset.Icc m (n + 1) := by
  -- 1. mun:sums-range-extended k := j, a := m, b := n, from H3
  have s1 : j ∈ Finset.Icc m (n + 1) := by first | exact (Parley.Items.Stdlib.Sums.mun_range_extended (a := m) (b := n) (k := j) hH3) | exact ((Parley.Items.Stdlib.Sums.mun_range_extended (a := m) (b := n) (k := j) hH3)).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_extended (a := m) (b := n) (k := j) hH3) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_extended (a := m) (b := n) (k := j) hH3) | (have h := (Parley.Items.Stdlib.Sums.mun_range_extended (a := m) (b := n) (k := j) hH3); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sums.RangeExtended
