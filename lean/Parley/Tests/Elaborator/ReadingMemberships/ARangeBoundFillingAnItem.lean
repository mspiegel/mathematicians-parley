module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundFillingAnItem

theorem a_range_bound_filling_an_item (n : ℕ) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    0 ≤ (n : ℤ) - k := by
  -- 1. mun:difference-nat0, from H2
  have s1 : 0 ≤ (n : ℤ) - k := by first | exact (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))) | exact ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side)))).symm | simpa using (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))) | exact_mod_cast (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundFillingAnItem
