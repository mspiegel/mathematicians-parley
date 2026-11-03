module

public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-factorial-quotients.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfFactorialQuotients.NextTermSum

theorem next_term_sum (k : ℕ) (hH1 : 0 < k) (t : ℤ → ℝ) :
    (∑ j ∈ Finset.Icc (1 : ℤ) ((k : ℤ) + 1), (t j : ℝ)) = (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ), (t j : ℝ)) + t ((k : ℤ) + 1) := by
  -- 1. mun:sum-extended a := 1, n := k
  have r40_1 : (k : ℤ) ≥ 1 := by parley_side
  have s1 : (∑ j ∈ Finset.Icc (1 : ℤ) ((k : ℤ) + 1), (t j : ℝ)) = (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ), (t j : ℝ)) + t ((k : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Proofs.Hammack.SumOfFactorialQuotients.NextTermSum
