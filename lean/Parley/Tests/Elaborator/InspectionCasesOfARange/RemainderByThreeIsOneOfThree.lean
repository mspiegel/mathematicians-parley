module

public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.RemainderByThreeIsOneOfThree

theorem remainder_by_three_is_one_of_three (n : ℤ) :
    n % (3 : ℤ) ≤ 2 := by
  -- 1. mun:mod-natural b := 3
  have s1 : 0 ≤ n % (3 : ℤ) := by first | exact (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := 3) (by parley_side)) | exact ((Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := 3) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := 3) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := 3) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_natural (a := n) (b := 3) (by parley_side)); parley_side)
  -- 2. mun:mod-less b := 3
  have s2 : n % (3 : ℤ) < 3 := by first | linarith [(Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := 3) (by parley_side))] | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := 3) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := 3) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_less (a := n) (b := 3) (by parley_side)); parley_side)
  -- 3. mun:range-from-bounds, from 1, 2
  have s3 : n % (3 : ℤ) ∈ Finset.Icc (0 : ℤ) (3 - 1 : ℤ) := by first | exact (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side) ▸ (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := 3) (by parley_side) (x := (n % (3 : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side)]); parley_side))) | exact ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side) ▸ (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := 3) (by parley_side) (x := (n % (3 : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side)]); parley_side)))).symm | simpa using (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side) ▸ (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := 3) (by parley_side) (x := (n % (3 : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side)]); parley_side))) | exact_mod_cast (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side) ▸ (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := 3) (by parley_side) (x := (n % (3 : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side)]); parley_side))) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side) ▸ (Parley.Items.Stdlib.Sums.mun_range_from_bounds (m := 3) (by parley_side) (x := (n % (3 : ℤ)).toNat) (by (try rw [Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n % (3 : ℤ)) by parley_side)]); parley_side))); parley_side)
  -- 4. inspection, from 3
  have s4 : (n % (3 : ℤ) = 0 ∨ n % (3 : ℤ) = 1) ∨ n % (3 : ℤ) = 2 := by parley_side
  -- 5. cases, from 4
  have s5 : n % (3 : ℤ) ≤ 2 := by
    rcases s4 with (hC1 | hC2) | hC3
    · skip
      -- 5.1. calculation
      have s5_1 : n % (3 : ℤ) ≤ 2 := by
        calc n % (3 : ℤ) = 0 := by parley_side
          _ ≤ 2 := by norm_num
      all_goals parley_side
    · skip
      -- 5.2. calculation
      have s5_2 : n % (3 : ℤ) ≤ 2 := by
        calc n % (3 : ℤ) = 1 := by parley_side
          _ ≤ 2 := by norm_num
      all_goals parley_side
    · skip
      -- 5.3. calculation
      have s5_3 : n % (3 : ℤ) ≤ 2 := by
        calc n % (3 : ℤ) = 2 := by parley_side
          _ ≤ 2 := by norm_num
      all_goals parley_side
  all_goals exact s5

end Parley.Tests.Elaborator.InspectionCasesOfARange.RemainderByThreeIsOneOfThree
