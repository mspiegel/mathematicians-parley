module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInARequiresLineCitingAnItem

theorem a_range_bound_in_a_requires_line_citing_an_item (n : ℕ) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) (n : ℤ)) :
    0 < (n : ℤ) - k + 1 := by
  -- 1. mun:nat0-successor k := n − k
  have r52_1 : 0 ≤ (n : ℤ) - k := by first | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))); exact h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))); exact h.symm) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))); simpa using h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))); exact_mod_cast h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))); simp (disch := parley_side) only [parley_cast_toNat] at h; (try push_cast at h ⊢); exact h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k.toNat) (n := n) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ k by parley_side)]); parley_side))); parley_side)
  have s1 : 0 < (n : ℤ) - k + 1 := by first | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - k) by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := ((n : ℤ) - k).toNat))); exact h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - k) by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := ((n : ℤ) - k).toNat))); exact h.symm) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - k) by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := ((n : ℤ) - k).toNat))); simpa using h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - k) by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := ((n : ℤ) - k).toNat))); exact_mod_cast h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - k) by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := ((n : ℤ) - k).toNat))); simp (disch := parley_side) only [parley_cast_toNat] at h; (try push_cast at h ⊢); exact h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((n : ℤ) - k) by parley_side) ▸ (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := ((n : ℤ) - k).toNat))); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInARequiresLineCitingAnItem
