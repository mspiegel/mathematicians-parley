module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/empty-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.EmptySum.EmptySum

theorem empty_sum (B : ℤ → ℝ) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (B k : ℝ)) = 0 := by
  -- 1. mun:sum-single a := 0
  have s1 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (B k : ℝ)) = B 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := B) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := B) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := B) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := B) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := B) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := B) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := B) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := B) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := B) (a := (0 : ℤ))); parley_side)
  -- 2. mun:sum-first n := 0
  have s2 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (B k : ℝ)) = B 0 + (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (B k : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_first (t := B) (n := (0 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := B) (n := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := B) (n := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_first (t := B) (n := (0 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_first (t := B) (n := (0 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := B) (n := (0 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := B) (n := (0 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := B) (n := (0 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := B) (n := (0 : ℤ)) (by parley_side)); parley_side)
  -- 3. algebra, from 1, 2
  have s3 : (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (B k : ℝ)) = 0 := by linear_combination (norm := parley_norm) s1 + (-1) * s2
  all_goals exact s3

end Parley.Proofs.Setmm.EmptySum.EmptySum
