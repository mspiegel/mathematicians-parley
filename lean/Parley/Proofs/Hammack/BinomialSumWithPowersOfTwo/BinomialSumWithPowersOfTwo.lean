module

public import ArithTactics
public import Counting
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Binomial.Binomial

/-! Written from proofs/hammack/binomial-sum-with-powers-of-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialSumWithPowersOfTwo.BinomialSumWithPowersOfTwo

theorem binomial_sum_with_powers_of_two (n : ℕ) :
    (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ) : ℚ)) = 3 ^ n := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. membership
  -- 3. proof
  have s3 : ∀ k : ℤ, k ∈ Finset.Icc 0 (n : ℤ) → (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * 1 ^ ((n : ℤ) - k) * 2 ^ k = 2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ) := by
    intro k hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 3.1. mun:one-power m := n − k
    have s3_1 : (1 ^ ((n : ℤ) - k) : ℚ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_one_power (m := (n : ℤ) - k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (n : ℤ) - k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (n : ℤ) - k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_one_power (m := (n : ℤ) - k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_one_power (m := (n : ℤ) - k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (n : ℤ) - k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (n : ℤ) - k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (n : ℤ) - k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := (n : ℤ) - k)); parley_side)
    -- 3.2. algebra, from 3.1
    have s3_2 : (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * 1 ^ ((n : ℤ) - k) * 2 ^ k = 2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ) := by linear_combination (norm := parley_norm) (2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ)) * s3_1
    all_goals exact s3_2
  -- 4. arithmetic
  have s4 : (1 + 2 : ℤ) = 3 := by parley_arith
  -- 5. calculation
  have s5 : (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ) : ℚ)) = 3 ^ n := by
    calc (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ) : ℚ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), ((LeanBridges.Counting.choose (n : ℤ) k : ℚ) * 1 ^ ((n : ℤ) - k) * 2 ^ k : ℚ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * 1 ^ ((n : ℤ) - k) * 2 ^ k)) (a := (0 : ℤ)) (b := (n : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * 1 ^ ((n : ℤ) - k) * 2 ^ k)) (a := (0 : ℤ)) (b := (n : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * 1 ^ ((n : ℤ) - k) * 2 ^ k)) (a := (0 : ℤ)) (b := (n : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * 1 ^ ((n : ℤ) - k) * 2 ^ k)) (a := (0 : ℤ)) (b := (n : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * 1 ^ ((n : ℤ) - k) * 2 ^ k)) (a := (0 : ℤ)) (b := (n : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * 1 ^ ((n : ℤ) - k) * 2 ^ k)) (a := (0 : ℤ)) (b := (n : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * 1 ^ ((n : ℤ) - k) * 2 ^ k)) (a := (0 : ℤ)) (b := (n : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * 1 ^ ((n : ℤ) - k) * 2 ^ k)) (a := (0 : ℤ)) (b := (n : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k * (LeanBridges.Counting.choose (n : ℤ) k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose (n : ℤ) k : ℚ) * 1 ^ ((n : ℤ) - k) * 2 ^ k)) (a := (0 : ℤ)) (b := (n : ℤ)) (by parley_side)); parley_side)
      _ = (1 + 2) ^ n := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n)) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n)) | exact_mod_cast ((Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n))).symm | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n)); parley_side)
      _ = 3 ^ n := by
          have s4_w : (1 + 2 : ℚ) = 3 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s4; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s4_w | parley_subst s4
  all_goals exact s5

end Parley.Proofs.Hammack.BinomialSumWithPowersOfTwo.BinomialSumWithPowersOfTwo
