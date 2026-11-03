module

public import Counting
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/factorial-by-predecessor.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor

theorem factorial_by_predecessor (N : ℕ) (hH1 : 0 < N) :
    (LeanBridges.Counting.factorial (N : ℤ) : ℤ) = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) * (N : ℤ) := by
  -- 1. mun:nat-minus-one n := N
  have s1 : 0 ≤ (N : ℤ) - 1 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := N) (by parley_side)); parley_side)
  -- 2. def:nat0 n := N − 1, from 1
  have s2 : 0 < (N : ℤ) - 1 ∨ (N : ℤ) - 1 = 0 := by first | exact ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ) - 1))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ) - 1))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ) - 1))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ) - 1))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ) - 1))).mp (by parley_side); parley_side)
  -- 3. cases, from 2
  have s3 : (LeanBridges.Counting.factorial (N : ℤ) : ℤ) = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) * (N : ℤ) := by
    rcases s2 with hC1 | hC2
    · skip
      -- 3.1. algebra
      have s3_1 : (N : ℤ) - 1 + 1 = (N : ℤ) := by parley_ring
      -- 3.2. calculation
      have s3_2 : (LeanBridges.Counting.factorial (N : ℤ) : ℤ) = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) * (N : ℤ) := by
        calc (LeanBridges.Counting.factorial (N : ℤ) : ℤ) = (LeanBridges.Counting.factorial ((N : ℤ) - 1 + 1) : ℤ) := by parley_subst s3_1
          _ = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) * ((N : ℤ) - 1 + 1) := by first | linear_combination (norm := parley_norm) (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.def_factorial_3 (n := ((N : ℤ) - 1).toNat))) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.def_factorial_3 (n := ((N : ℤ) - 1).toNat))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.def_factorial_3 (n := ((N : ℤ) - 1).toNat))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.def_factorial_3 (n := ((N : ℤ) - 1).toNat))) | exact_mod_cast ((Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.def_factorial_3 (n := ((N : ℤ) - 1).toNat)))).symm | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.def_factorial_3 (n := ((N : ℤ) - 1).toNat))); rify; linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.def_factorial_3 (n := ((N : ℤ) - 1).toNat))); qify; linear_combination (norm := parley_norm) h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.def_factorial_3 (n := ((N : ℤ) - 1).toNat))); parley_int_power h) | (have h := (Int.toNat_of_nonneg (show (0 : ℤ) ≤ ((N : ℤ) - 1) by parley_side) ▸ (Parley.Items.Stdlib.Counting.def_factorial_3 (n := ((N : ℤ) - 1).toNat))); parley_side)
          _ = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) * (N : ℤ) := by parley_subst s3_1
      all_goals parley_side
    · skip
      -- 3.3. algebra, from C2
      have s3_3 : (N : ℤ) = 1 := by linear_combination (norm := parley_norm) hC2
      -- 3.4. calculation
      have s3_4 : (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) = 1 := by
        calc (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) = (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) := by parley_subst hC2
          _ = 1 := by norm_num
      -- 3.5. restate 3.3
      have s3_5 : 1 * (N : ℤ) = 1 := by parley_side
      -- 3.6. calculation
      have s3_6 : (LeanBridges.Counting.factorial (N : ℤ) : ℤ) = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) * (N : ℤ) := by
        calc (LeanBridges.Counting.factorial (N : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) := by parley_subst s3_3
          _ = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Counting.def_factorial_2 | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Counting.def_factorial_2 | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_2).symm | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_int_power h) | (have h := Parley.Items.Stdlib.Counting.def_factorial_2; parley_side)
          _ = 1 * (N : ℤ) := by parley_side
          _ = (LeanBridges.Counting.factorial ((N : ℤ) - 1) : ℤ) * (N : ℤ) := by parley_subst s3_4
      all_goals parley_side
  all_goals exact s3

end Parley.Proofs.Setmm.FactorialByPredecessor.FactorialByPredecessor
