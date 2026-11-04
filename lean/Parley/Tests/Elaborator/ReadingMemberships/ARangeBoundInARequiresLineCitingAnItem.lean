module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInARequiresLineCitingAnItem

theorem a_range_bound_in_a_requires_line_citing_an_item (n : ℕ) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    0 < (n : ℤ) - k + 1 := by
  -- 1. mun:nat0-successor k := n − k
  have r52_1 : 0 ≤ (n : ℤ) - k := by first | exact (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))) | exact ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side)))).symm | simpa using (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))) | exact_mod_cast (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))); parley_side)
  have s1 : 0 < (n : ℤ) - k + 1 := by first | exact (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - k) by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := ((n : ℤ) - k).toNat))) | exact ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - k) by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := ((n : ℤ) - k).toNat)))).symm | simpa using (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - k) by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := ((n : ℤ) - k).toNat))) | exact_mod_cast (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - k) by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := ((n : ℤ) - k).toNat))) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - k) by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := ((n : ℤ) - k).toNat))); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInARequiresLineCitingAnItem
