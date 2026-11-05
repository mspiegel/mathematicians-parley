module

public import ArithTactics
public import Counting
public import FactorialTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Binomial.Binomial

/-! Written from proofs/hammack/weighted-binomial-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.WeightedBinomialSum.BinomialRowSum

theorem binomial_row_sum (m : ℕ) :
    (∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ), ((LeanBridges.Counting.choose (m : ℤ) k : ℤ) : ℤ)) = 2 ^ m := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. proof
  have s2 : ∀ k : ℤ, k ∈ Finset.Icc 0 (m : ℤ) → (LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ ((m : ℤ) - k) * 1 ^ k = (LeanBridges.Counting.choose (m : ℤ) k : ℚ) := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 2.1. mun:one-power m := m − k
    have s2_1 : (1 ^ ((m : ℤ) - k) : ℚ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_one_power (m := (m : ℤ) - k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (m : ℤ) - k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (m : ℤ) - k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_one_power (m := (m : ℤ) - k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_one_power (m := (m : ℤ) - k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (m : ℤ) - k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (m : ℤ) - k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (m : ℤ) - k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (m : ℤ) - k)); parley_side)
    -- 2.2. mun:one-power m := k
    have s2_2 : (1 ^ k : ℚ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_one_power (m := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); parley_side)
    -- 2.3. calculation
    have s2_3 : (LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ ((m : ℤ) - k) * 1 ^ k = (LeanBridges.Counting.choose (m : ℤ) k : ℚ) := by
      calc (LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ ((m : ℤ) - k) * 1 ^ k = (LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ k := by parley_subst s2_1
        _ = (LeanBridges.Counting.choose (m : ℤ) k : ℚ) := by parley_subst s2_2
    all_goals exact s2_3
  -- 3. arithmetic
  have s3 : (1 + 1 : ℤ) = 2 := by parley_arith
  -- 4. calculation
  have s4 : (∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ), ((LeanBridges.Counting.choose (m : ℤ) k : ℤ) : ℤ)) = 2 ^ m := by
    qify
    calc (∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ), ((LeanBridges.Counting.choose (m : ℤ) k : ℚ) : ℚ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ), ((LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ ((m : ℤ) - k) * 1 ^ k : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ ((m : ℤ) - k) * 1 ^ k)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ ((m : ℤ) - k) * 1 ^ k)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ ((m : ℤ) - k) * 1 ^ k)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ ((m : ℤ) - k) * 1 ^ k)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ ((m : ℤ) - k) * 1 ^ k)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ ((m : ℤ) - k) * 1 ^ k)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ ((m : ℤ) - k) * 1 ^ k)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ ((m : ℤ) - k) * 1 ^ k)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m : ℤ) k : ℚ) * 1 ^ ((m : ℤ) - k) * 1 ^ k)) (a := (0 : ℤ)) (b := (m : ℤ)) (by parley_side)); parley_side)
      _ = (1 + 1) ^ m := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m)) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m)) | exact_mod_cast ((Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m))).symm | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := m)); parley_side)
      _ = 2 ^ m := by
          have s3_w : (1 + 1 : ℚ) = 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s3; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s3_w | parley_subst s3
  all_goals exact s4

end Parley.Proofs.Hammack.WeightedBinomialSum.BinomialRowSum
