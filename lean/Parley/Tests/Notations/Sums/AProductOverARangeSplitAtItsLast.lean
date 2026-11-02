module

public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.AProductOverARangeSplitAtItsLast

theorem a_product_over_a_range_split_at_its_last (n : ℕ) (hH1 : 0 < n) (t : ℤ → ℝ) :
    (∏ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (t k : ℝ)) = (∏ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (t k : ℝ)) * t ((n : ℤ) + 1) := by
  -- 1. mun:product-extended a := 1
  have r110_1 : (n : ℤ) ≥ 1 := by parley_side
  have s1 : (∏ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (t k : ℝ)) = (∏ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (t k : ℝ)) * t ((n : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := (n : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := (n : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := (n : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := (n : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := (n : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := (n : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := (n : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := (n : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_product_extended (t := t) (a := (1 : ℤ)) (n := (n : ℤ)) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Notations.Sums.AProductOverARangeSplitAtItsLast
