module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne

/-! Written from proofs/hammack/sum-of-first-naturals-is-a-binomial.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfFirstNaturalsIsABinomial.SumOfFirstNaturalsIsABinomial

set_option maxHeartbeats 400000 in
theorem sum_of_first_naturals_is_a_binomial (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (k : ℤ)) = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by
  set S : ℤ → ℤ := fun m => ∑ j ∈ Finset.Icc (1 : ℤ) m, (j : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → S k = (LeanBridges.Counting.choose (k + 1) (2 : ℤ) : ℤ) := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (1 : ℤ) < 2 := by parley_arith
      -- 1.2. def:C n := 1, k := 2, from 1.1
      have s1_2 : (LeanBridges.Counting.choose (1 : ℤ) (2 : ℤ) : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))) (by parley_side); parley_side)
      -- 1.3. thm:pascal n := 1, k := 2
      have s1_3 : (LeanBridges.Counting.choose (1 : ℤ) (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose (1 : ℤ) (2 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (1 + 1 : ℤ) (2 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := (1 : ℤ)) (by parley_side) (k := (2 : ℤ))); parley_side)
      -- 1.4. substitute 2 − 1 = 1 (arithmetic) into line 1.3
      have s1_4 : (LeanBridges.Counting.choose (1 : ℤ) (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose (1 : ℤ) (1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (1 + 1 : ℤ) (2 : ℤ) : ℤ) := by parley_subst_at (show (2 - 1 : ℤ) = 1 by parley_side) s1_3
      -- 1.5. thm:binomial-of-one m := 1
      have s1_5 : (LeanBridges.Counting.choose (1 : ℤ) (1 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := (1 : ℤ)) (by parley_side)) | (have h := (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := (1 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := (1 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := (1 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := (1 : ℤ)) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := (1 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := (1 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := (1 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := (1 : ℤ)) (by parley_side)); parley_side)
      -- 1.6. calculation
      have s1_6 : S 1 = (LeanBridges.Counting.choose (1 + 1 : ℤ) (2 : ℤ) : ℤ) := by
        calc S 1 = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (j : ℤ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
          _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => j)) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => j)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => j)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => j)) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => j)) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => j)) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => j)) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => j)) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => j)) (a := (1 : ℤ))); parley_side)
          _ = 0 + 1 := by norm_num
          _ = 0 + (LeanBridges.Counting.choose (1 : ℤ) (1 : ℤ) : ℤ) := by parley_subst s1_5
          _ = (LeanBridges.Counting.choose (1 : ℤ) (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose (1 : ℤ) (1 : ℤ) : ℤ) := by parley_subst s1_2
          _ = (LeanBridges.Counting.choose (1 + 1 : ℤ) (2 : ℤ) : ℤ) := by parley_side
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.7. calculation
      have r49_1 : k ≥ 1 := by parley_side
      have s1_7 : S (k + 1) = S k + (k + 1) := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (j : ℤ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) k, (j : ℤ)) + (k + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j)) (a := (1 : ℤ)) (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j)) (a := (1 : ℤ)) (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j)) (a := (1 : ℤ)) (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j)) (a := (1 : ℤ)) (n := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j)) (a := (1 : ℤ)) (n := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j)) (a := (1 : ℤ)) (n := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j)) (a := (1 : ℤ)) (n := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j)) (a := (1 : ℤ)) (n := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j)) (a := (1 : ℤ)) (n := k) (by parley_side)); parley_side)
          _ = S k + (k + 1) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      -- 1.8. thm:binomial-of-one m := k + 1
      have s1_8 : (LeanBridges.Counting.choose (k + 1) (1 : ℤ) : ℤ) = k + 1 := by exact (Parley.Proofs.Hammack.BinomialOfOne.BinomialOfOne.binomial_of_one (m := k + 1) (by parley_side))
      -- 1.9. thm:pascal n := k + 1, k := 2
      have s1_9 : (LeanBridges.Counting.choose (k + 1) (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose (k + 1) (2 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (k + 1 + 1) (2 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := k + 1) (by parley_side) (k := (2 : ℤ))) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := k + 1) (by parley_side) (k := (2 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := k + 1) (by parley_side) (k := (2 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := k + 1) (by parley_side) (k := (2 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := k + 1) (by parley_side) (k := (2 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := k + 1) (by parley_side) (k := (2 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := k + 1) (by parley_side) (k := (2 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := k + 1) (by parley_side) (k := (2 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := k + 1) (by parley_side) (k := (2 : ℤ))); parley_side)
      -- 1.10. substitute 2 − 1 = 1 (arithmetic) into line 1.9
      have s1_10 : (LeanBridges.Counting.choose (k + 1) (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose (k + 1) (1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (k + 1 + 1) (2 : ℤ) : ℤ) := by parley_subst_at (show (2 - 1 : ℤ) = 1 by parley_side) s1_9
      -- 1.11. calculation
      have s1_11 : S (k + 1) = (LeanBridges.Counting.choose (k + 1 + 1) (2 : ℤ) : ℤ) := by
        calc S (k + 1) = S k + (k + 1) := by parley_side
          _ = (LeanBridges.Counting.choose (k + 1) (2 : ℤ) : ℤ) + (k + 1) := by parley_subst hIH
          _ = (LeanBridges.Counting.choose (k + 1) (2 : ℤ) : ℤ) + (LeanBridges.Counting.choose (k + 1) (1 : ℤ) : ℤ) := by parley_subst s1_8
          _ = (LeanBridges.Counting.choose (k + 1 + 1) (2 : ℤ) : ℤ) := by parley_side
      all_goals parley_side
  -- 2. calculation
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (k : ℤ)) = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by
    calc (∑ k ∈ Finset.Icc (1 : ℤ) n, (k : ℤ)) = S n := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      _ = (LeanBridges.Counting.choose (n + 1) (2 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.SumOfFirstNaturalsIsABinomial.SumOfFirstNaturalsIsABinomial
