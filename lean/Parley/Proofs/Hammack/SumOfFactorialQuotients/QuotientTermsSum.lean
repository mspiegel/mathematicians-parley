module

public import Parley.Items.Stdlib.Sums
public import Parley.Library

/-! Written from proofs/hammack/sum-of-factorial-quotients.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfFactorialQuotients.QuotientTermsSum

theorem quotient_terms_sum (n : ℕ) (hH1 : 0 < n) (t : ℤ → ℝ) (hH3 : ∀ k : ℕ, 0 < k → t (k : ℤ) = (k : ℝ) / (Parley.Library.factorial ((k : ℤ) + 1) : ℝ)) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), t k) = (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (k : ℝ) / (Parley.Library.factorial (k + 1) : ℝ)) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. mun:sum-termwise a := 1, b := n, from H3, 1
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), t k) = (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (k : ℝ) / (Parley.Library.factorial (k + 1) : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (Parley.Library.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (Parley.Library.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (Parley.Library.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (Parley.Library.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (Parley.Library.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (Parley.Library.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Proofs.Hammack.SumOfFactorialQuotients.QuotientTermsSum
