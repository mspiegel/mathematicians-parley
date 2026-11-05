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

/-! Written from proofs/setmm/binomial-coefficients-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BinomialCoefficientsSum.BinomialCoefficientsSum

theorem binomial_coefficients_sum (N : ℕ) :
    2 ^ N = (∑ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), ((LeanBridges.Counting.choose (N : ℤ) k : ℤ) : ℤ)) := by
  -- 1. proof
  have s1 : ∀ k : ℤ, k ∈ Finset.Icc 0 (N : ℤ) → (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ ((N : ℤ) - k) * 1 ^ k = (LeanBridges.Counting.choose (N : ℤ) k : ℚ) := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 1.1. mun:one-power m := N − k
    have s1_1 : (1 ^ ((N : ℤ) - k) : ℚ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_one_power (m := (N : ℤ) - k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (N : ℤ) - k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (N : ℤ) - k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_one_power (m := (N : ℤ) - k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_one_power (m := (N : ℤ) - k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (N : ℤ) - k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (N : ℤ) - k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (N : ℤ) - k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (N : ℤ) - k)); parley_side)
    -- 1.2. mun:one-power m := k
    have s1_2 : (1 ^ k : ℚ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_one_power (m := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := k)); parley_side)
    -- 1.3. calculation
    have s1_3 : (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ ((N : ℤ) - k) * 1 ^ k = (LeanBridges.Counting.choose (N : ℤ) k : ℚ) := by
      calc (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ ((N : ℤ) - k) * 1 ^ k = (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ k := by linear_combination (norm := parley_norm) (1 ^ k * (LeanBridges.Counting.choose (N : ℤ) k : ℚ)) * s1_1
        _ = (LeanBridges.Counting.choose (N : ℤ) k : ℚ) := by linear_combination (norm := parley_norm) ((LeanBridges.Counting.choose (N : ℤ) k : ℚ)) * s1_2
    all_goals exact s1_3
  -- 2. arithmetic
  have s2 : (1 + 1 : ℤ) = 2 := by parley_arith
  -- 3. calculation
  have s3 : 2 ^ N = (∑ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), ((LeanBridges.Counting.choose (N : ℤ) k : ℤ) : ℤ)) := by
    try qify
    calc (2 ^ N : ℚ) = (1 + 1) ^ N := by
          have s2_w : (1 + 1 : ℚ) = 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s2_w | parley_subst s2
      _ = (∑ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), ((LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ ((N : ℤ) - k) * 1 ^ k : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N)) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N)) | exact_mod_cast ((Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N))).symm | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (1 : ℝ)) (n := N)); parley_side)
      _ = (∑ k ∈ Finset.Icc (0 : ℤ) (N : ℤ), ((LeanBridges.Counting.choose (N : ℤ) k : ℚ) : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ ((N : ℤ) - k) * 1 ^ k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ))) (a := (0 : ℤ)) (b := (N : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ ((N : ℤ) - k) * 1 ^ k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ))) (a := (0 : ℤ)) (b := (N : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ ((N : ℤ) - k) * 1 ^ k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ))) (a := (0 : ℤ)) (b := (N : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ ((N : ℤ) - k) * 1 ^ k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ))) (a := (0 : ℤ)) (b := (N : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ ((N : ℤ) - k) * 1 ^ k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ))) (a := (0 : ℤ)) (b := (N : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ ((N : ℤ) - k) * 1 ^ k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ))) (a := (0 : ℤ)) (b := (N : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ ((N : ℤ) - k) * 1 ^ k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ))) (a := (0 : ℤ)) (b := (N : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ ((N : ℤ) - k) * 1 ^ k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ))) (a := (0 : ℤ)) (b := (N : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ) * 1 ^ ((N : ℤ) - k) * 1 ^ k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose (N : ℤ) k : ℚ))) (a := (0 : ℤ)) (b := (N : ℤ)) (by parley_side)); parley_side)
  all_goals exact s3

end Parley.Proofs.Setmm.BinomialCoefficientsSum.BinomialCoefficientsSum
