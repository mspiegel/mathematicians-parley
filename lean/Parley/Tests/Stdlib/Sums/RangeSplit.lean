module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.RangeSplit

theorem range_split (m : ℤ) (n : ℤ) (k : ℤ) (hH3 : k ∈ Finset.Icc m n) :
    (Set.Icc m n : Set ℤ) = (Set.Icc m k : Set ℤ) ∪ (Set.Icc (k + 1) n : Set ℤ) := by
  -- 1. mun:sums-range-split, from H3
  have s1 : (Set.Icc m n : Set ℤ) = (Set.Icc m k : Set ℤ) ∪ (Set.Icc (k + 1) n : Set ℤ) := by first | exact (Parley.Items.Stdlib.Sums.mun_range_split (m := m) (n := n) (k := k) hH3) | exact ((Parley.Items.Stdlib.Sums.mun_range_split (m := m) (n := n) (k := k) hH3)).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_split (m := m) (n := n) (k := k) hH3) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_split (m := m) (n := n) (k := k) hH3) | (have h := (Parley.Items.Stdlib.Sums.mun_range_split (m := m) (n := n) (k := k) hH3); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sums.RangeSplit
