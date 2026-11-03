module

public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.OneToThreeSummed

theorem one_to_three_summed :
    (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) = 6 := by
  -- 1. mun:sum-single a := 1
  have s1 : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (k : ℤ)) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k)) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k)) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k)) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k)) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k)) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k)) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k)) (a := (1 : ℤ))); parley_side)
  -- 2. mun:sum-extended a := 1, n := 1
  have r26_1 : (1 : ℤ) ≥ 1 := by parley_arith
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (1 + 1 : ℤ), (k : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (k : ℤ)) + (1 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (1 : ℤ)) (by parley_side)); parley_side)
  -- 3. mun:sum-extended a := 1, n := 2
  have r30_1 : (2 : ℤ) ≥ 1 := by parley_arith
  have s3 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 + 1 : ℤ), (k : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (2 : ℤ), (k : ℤ)) + (2 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (2 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (2 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (2 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (2 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (2 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (2 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (2 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k)) (a := (1 : ℤ)) (n := (2 : ℤ)) (by parley_side)); parley_side)
  -- 4. arithmetic
  have s4 : (1 + 1 : ℤ) = 2 := by parley_arith
  -- 5. substitute 1 + 1 = 2 (line 4) into line 2
  have s5 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 : ℤ), (k : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (k : ℤ)) + 2 := by parley_subst_at s4 s2
  -- 6. substitute Σ(k = 1 to 1) k = 1 (line 1) into line 5
  have s6 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 : ℤ), (k : ℤ)) = 1 + 2 := by parley_subst_at s1 s5
  -- 7. calculation
  have s7 : (∑ k ∈ Finset.Icc (1 : ℤ) (2 : ℤ), (k : ℤ)) = 3 := by
    calc (∑ k ∈ Finset.Icc (1 : ℤ) (2 : ℤ), (k : ℤ)) = 1 + 2 := by parley_side
      _ = 3 := by norm_num
  -- 8. arithmetic
  have s8 : (2 + 1 : ℤ) = 3 := by parley_arith
  -- 9. substitute 2 + 1 = 3 (line 8) into line 3
  have s9 : (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (2 : ℤ), (k : ℤ)) + 3 := by parley_subst_at s8 s3
  -- 10. substitute Σ(k = 1 to 2) k = 3 (line 7) into line 9
  have s10 : (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) = 3 + 3 := by parley_subst_at s7 s9
  -- 11. calculation
  have s11 : (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) = 6 := by
    calc (∑ k ∈ Finset.Icc (1 : ℤ) (3 : ℤ), (k : ℤ)) = 3 + 3 := by parley_side
      _ = 6 := by norm_num
  all_goals exact s11

end Parley.Tests.Notations.Sums.OneToThreeSummed
