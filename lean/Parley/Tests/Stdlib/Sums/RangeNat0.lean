module

public import LeanBridges
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.RangeNat0

theorem range_nat0 (n : ℤ) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) n) :
    0 ≤ k := by
  -- 1. mun:sums-range-nat0, from H2
  have s1 : 0 ≤ k := by first | exact (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := n) (k := k) (by parley_side)) | exact ((Parley.Items.Stdlib.Sums.mun_range_nat0 (n := n) (k := k) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := n) (k := k) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := n) (k := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := n) (k := k) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := n) (k := k) (by parley_side)); parley_side)
  lift k to ℕ using (id s1)
  all_goals parley_side

end Parley.Tests.Stdlib.Sums.RangeNat0
