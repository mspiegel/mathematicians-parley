module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.RangeNat0

theorem range_nat0 (n : ℤ) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) n) :
    0 ≤ k := by
  -- 1. mun:sums-range-nat0, from H2
  have s1 : 0 ≤ k := by first | exact (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := n) (k := k) hH2) | exact ((Parley.Items.Stdlib.Sums.mun_range_nat0 (n := n) (k := k) hH2)).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := n) (k := k) hH2) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := n) (k := k) hH2) | (have h := (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := n) (k := k) hH2); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sums.RangeNat0
