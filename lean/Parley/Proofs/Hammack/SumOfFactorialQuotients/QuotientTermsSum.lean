module

public import Counting
public import FactorialTactics
public import PowerTactics
public import RealTactics
public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-factorial-quotients.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfFactorialQuotients.QuotientTermsSum

theorem quotient_terms_sum (n : ℤ) (hH1 : 0 < n) (t : ℤ → ℝ) (hH3 : ∀ k : ℤ, 0 < k → t k = (k : ℝ) / (LeanBridges.Counting.factorial (k + 1) : ℝ)) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℝ) / (LeanBridges.Counting.factorial (k + 1) : ℝ) : ℝ)) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. mun:sum-termwise a := 1, b := n, from H3, 1
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (t k : ℝ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℝ) / (LeanBridges.Counting.factorial (k + 1) : ℝ) : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (LeanBridges.Counting.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (LeanBridges.Counting.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (LeanBridges.Counting.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (LeanBridges.Counting.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (LeanBridges.Counting.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (LeanBridges.Counting.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (LeanBridges.Counting.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (LeanBridges.Counting.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (LeanBridges.Counting.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := n) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (k : ℝ) / (LeanBridges.Counting.factorial (k + 1) : ℝ))) (a := (1 : ℤ)) (b := n) (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.SumOfFactorialQuotients.QuotientTermsSum
