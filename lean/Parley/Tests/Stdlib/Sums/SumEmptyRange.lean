module

public import ArithTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.SumEmptyRange

theorem sum_empty_range :
    (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 0 := by
  -- 1. mun:sums-sum-empty-range a := 1, b := 0
  have r16_1 : (0 : ℤ) < 1 := by parley_arith
  have s1 : (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_empty_range (t := (fun k : ℤ => 2 * k - 1)) (a := (1 : ℤ)) (b := (0 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_empty_range (t := (fun k : ℤ => 2 * k - 1)) (a := (1 : ℤ)) (b := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_empty_range (t := (fun k : ℤ => 2 * k - 1)) (a := (1 : ℤ)) (b := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_empty_range (t := (fun k : ℤ => 2 * k - 1)) (a := (1 : ℤ)) (b := (0 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_empty_range (t := (fun k : ℤ => 2 * k - 1)) (a := (1 : ℤ)) (b := (0 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_empty_range (t := (fun k : ℤ => 2 * k - 1)) (a := (1 : ℤ)) (b := (0 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_empty_range (t := (fun k : ℤ => 2 * k - 1)) (a := (1 : ℤ)) (b := (0 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_empty_range (t := (fun k : ℤ => 2 * k - 1)) (a := (1 : ℤ)) (b := (0 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_empty_range (t := (fun k : ℤ => 2 * k - 1)) (a := (1 : ℤ)) (b := (0 : ℤ)) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sums.SumEmptyRange
