module

public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/sum-letter-in-scope.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SumLetterInScope.TermwiseUnderAHypothesisOverItsLetter

theorem termwise_under_a_hypothesis_over_its_letter (n : ℕ) (hH1 : 0 < n) (hH2 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (k : ℤ)) ≥ 0) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (k + 0 : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (k : ℤ)) := by
  -- 1. proof
  have s1 : ∀ k : ℤ, k ∈ Finset.Icc 1 (n : ℤ) → k + 0 = k := by
    intro k hJ
    -- 1.1. algebra
    have s1_1 : k + 0 = k := by parley_ring
    all_goals parley_side
  -- 2. mun:sum-termwise a := 1, b := n, from 1
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (k + 0 : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (k : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => k + 0)) (u := (fun k : ℤ => k)) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => k + 0)) (u := (fun k : ℤ => k)) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => k + 0)) (u := (fun k : ℤ => k)) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => k + 0)) (u := (fun k : ℤ => k)) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => k + 0)) (u := (fun k : ℤ => k)) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => k + 0)) (u := (fun k : ℤ => k)) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => k + 0)) (u := (fun k : ℤ => k)) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => k + 0)) (u := (fun k : ℤ => k)) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => k + 0)) (u := (fun k : ℤ => k)) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.SumLetterInScope.TermwiseUnderAHypothesisOverItsLetter
