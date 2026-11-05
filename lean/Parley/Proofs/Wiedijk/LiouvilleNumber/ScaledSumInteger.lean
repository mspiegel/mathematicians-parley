module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumReal
public import Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep
public import Parley.Proofs.Wiedijk.LiouvilleNumber.TermsReal

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.ScaledSumInteger

set_option maxHeartbeats 400000 in
theorem scaled_sum_integer :
    (∀ n : ℕ, 0 < n → (∃ m : ℤ, (m : ℚ) = 2 ^ LeanBridges.Counting.factorial (n : ℤ) * (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)))) := by
  -- the theorem. induction on n starting at 1
  have sThm : ∀ n : ℕ, 0 < n → (∃ m : ℤ, (m : ℚ) = 2 ^ LeanBridges.Counting.factorial (n : ℤ) * (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) := by
    intro n h_n
    replace h_n : 1 ≤ n := h_n
    induction n, h_n using Nat.le_induction with
    | base =>
      -- 1. thm:terms-real m := 1
      -- 2. mun:sum-single a := 1, from 1
      have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = 1 / 2 ^ LeanBridges.Counting.factorial (1 : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ))); parley_side)
      -- 3. algebra, from D0, 2
      have s3 : 2 ^ LeanBridges.Counting.factorial (1 : ℤ) * (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = 1 := by linear_combination (norm := parley_field) (2 ^ LeanBridges.Counting.factorial (1 : ℤ)) * s2
      -- 4. membership, from 3
      have s4 : ∃ m : ℤ, (m : ℚ) = 2 ^ LeanBridges.Counting.factorial (1 : ℤ) * (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := ⟨(1 : ℤ), by first | (push_cast; linarith [s3]) | (rw [s3]; push_cast; ring) | (rw [← s3]; push_cast; ring) | exact s3 | exact s3.symm⟩
      all_goals parley_side
    | succ n hK hIH =>
      -- 5. thm:partial-sum-step
      have s5 : (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial ((n : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n) (by parley_side))).symm | (have h := (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep.partial_sum_step (n := n) (by parley_side)); parley_side)
      -- 6. def:factorial
      have s6 : (LeanBridges.Counting.factorial ((n : ℤ) + 1) : ℤ) = (LeanBridges.Counting.factorial (n : ℤ) : ℤ) * ((n : ℤ) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_factorial_3 (n := n))).symm | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_factorial_3 (n := n)); parley_side)
      -- 7. calculation
      have s7 : (2 ^ LeanBridges.Counting.factorial ((n : ℤ) + 1) : ℤ) = (2 ^ LeanBridges.Counting.factorial (n : ℤ)) ^ n * 2 ^ LeanBridges.Counting.factorial (n : ℤ) := by
        calc (2 ^ LeanBridges.Counting.factorial ((n : ℤ) + 1) : ℤ) = 2 ^ (LeanBridges.Counting.factorial (n : ℤ) * (n + 1)) := by parley_subst s6
          _ = (2 ^ LeanBridges.Counting.factorial (n : ℤ)) ^ (n + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := (2 : ℤ)) (m := LeanBridges.Counting.factorial (n : ℤ)) (n := n + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := (2 : ℤ)) (m := LeanBridges.Counting.factorial (n : ℤ)) (n := n + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := (2 : ℤ)) (m := LeanBridges.Counting.factorial (n : ℤ)) (n := n + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := (2 : ℤ)) (m := LeanBridges.Counting.factorial (n : ℤ)) (n := n + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_power_of_power (a := (2 : ℤ)) (m := LeanBridges.Counting.factorial (n : ℤ)) (n := n + 1))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := (2 : ℤ)) (m := LeanBridges.Counting.factorial (n : ℤ)) (n := n + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := (2 : ℤ)) (m := LeanBridges.Counting.factorial (n : ℤ)) (n := n + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := (2 : ℤ)) (m := LeanBridges.Counting.factorial (n : ℤ)) (n := n + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := (2 : ℤ)) (m := LeanBridges.Counting.factorial (n : ℤ)) (n := n + 1)); parley_side)
          _ = (2 ^ LeanBridges.Counting.factorial (n : ℤ)) ^ n * 2 ^ LeanBridges.Counting.factorial (n : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 ^ LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (m := n)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 ^ LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (m := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 ^ LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (m := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 ^ LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (m := n)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 ^ LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (m := n))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 ^ LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (m := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 ^ LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (m := n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 ^ LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (m := n)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 ^ LeanBridges.Counting.factorial (n : ℤ) : ℤ)) (m := n)); parley_side)
      -- 8. algebra, from 5
      have s8 : 2 ^ LeanBridges.Counting.factorial ((n : ℤ) + 1) * (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = 2 ^ LeanBridges.Counting.factorial ((n : ℤ) + 1) * (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 := by linear_combination (norm := parley_field) (2 ^ LeanBridges.Counting.factorial ((n : ℤ) + 1)) * s5
      -- 9. substitute
      have s9 : 2 ^ LeanBridges.Counting.factorial ((n : ℤ) + 1) * (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (2 ^ LeanBridges.Counting.factorial (n : ℤ)) ^ n * (2 ^ LeanBridges.Counting.factorial (n : ℤ) * (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) + 1 := by
        have c1 : 2 ^ LeanBridges.Counting.factorial ((n : ℤ) + 1) * (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (2 ^ LeanBridges.Counting.factorial (n : ℤ)) ^ n * (2 ^ LeanBridges.Counting.factorial (n : ℤ) * (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) := by
          have s7_w : (2 ^ LeanBridges.Counting.factorial ((n : ℤ) + 1) : ℚ) = (2 ^ LeanBridges.Counting.factorial (n : ℤ)) ^ n * 2 ^ LeanBridges.Counting.factorial (n : ℤ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s7; push_cast at h; linear_combination (norm := parley_norm) h
          linear_combination (norm := parley_norm) ((∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) * s7_w
        have row1 : 2 ^ LeanBridges.Counting.factorial ((n : ℤ) + 1) * (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (2 ^ LeanBridges.Counting.factorial (n : ℤ)) ^ n * (2 ^ LeanBridges.Counting.factorial (n : ℤ) * (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) + 1 := by parley_subst_at c1 s8
        exact row1
      -- 10. membership, from IH
      have s10 : ∃ m : ℤ, (m : ℚ) = (2 ^ LeanBridges.Counting.factorial (n : ℤ)) ^ n * (2 ^ LeanBridges.Counting.factorial (n : ℤ) * (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) + 1 := by (exact ⟨(2 ^ LeanBridges.Counting.factorial (n : ℤ)) ^ n * (Classical.choose hIH) + 1, by push_cast; (try simp only [Classical.choose_spec hIH]); first | done | parley_ring⟩)
      -- 11. substitute (2^(n!))^n·(2^(n!)·s(n)) + 1 = 2^((n + 1)!)·s(n + 1) (line 9) into line 10
      have s11 : ∃ m : ℤ, (m : ℚ) = 2 ^ LeanBridges.Counting.factorial ((n : ℤ) + 1) * (∑ k ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) := by parley_subst_at s9 s10
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Wiedijk.LiouvilleNumber.ScaledSumInteger
