module

public import OrderTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-for-all-over-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AForAllOverARange.AForAllOverAWiderSet

theorem a_for_all_over_a_wider_set (k : ℕ) (hH1 : 0 < k) (x : ℝ) (hH3 : True) :
    (∑ j ∈ Finset.Icc (1 : ℤ) ((k : ℤ) + 1), ((j : ℝ) / x : ℝ)) = (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ), ((j : ℝ) / x : ℝ)) + ((k : ℝ) + 1) / x := by
  -- 1. mun:sum-extended a := 1, n := k, from H3
  have r31_1 : (k : ℤ) ≥ 1 := by parley_order
  have s1 : (∑ j ∈ Finset.Icc (1 : ℤ) ((k : ℤ) + 1), ((j : ℝ) / x : ℝ)) = (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ), ((j : ℝ) / x : ℝ)) + ((k : ℝ) + 1) / x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (j : ℝ) / x)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (j : ℝ) / x)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (j : ℝ) / x)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (j : ℝ) / x)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (j : ℝ) / x)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (j : ℝ) / x)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (j : ℝ) / x)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (j : ℝ) / x)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (j : ℝ) / x)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.AForAllOverARange.AForAllOverAWiderSet
