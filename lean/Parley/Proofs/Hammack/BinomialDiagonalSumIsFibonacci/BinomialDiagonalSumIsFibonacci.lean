module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import FactorialTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural

/-! Written from proofs/hammack/binomial-diagonal-sum-is-fibonacci.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialDiagonalSumIsFibonacci.BinomialDiagonalSumIsFibonacci

set_option maxHeartbeats 400000 in
theorem binomial_diagonal_sum_is_fibonacci (n : ℕ) (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k) :
    (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), ((LeanBridges.Counting.choose ((n : ℤ) - k) k : ℤ) : ℤ)) = F ((n : ℤ) + 1) := by
  set S : ℤ → ℤ := fun m => ∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose (m - k) k : ℤ) : ℤ) with hD2
  -- 1. thm:fibonacci-natural
  have s1 : ∀ i : ℕ, 0 ≤ F (i : ℤ) ∧ 0 ≤ G (i : ℤ) := by first | exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side)) | exact ((Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side))).symm | simpa using (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side)) | exact_mod_cast (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side)) | (have h := (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side)); parley_side)
  -- 2. induction on j starting at 0
  have s2 : ∀ j : ℕ, S (j : ℤ) = G (j : ℤ) ∧ S ((j : ℤ) + 1) = G ((j : ℤ) + 1) := by
    intro j
    induction j with
    | zero =>
      -- 2.1. proof
      -- what this block shows, Lean's types give
      -- 2.2. D1
      have s2_2 : G 0 = 1 := by have h := hD1.2.1; (try ring_nf at h ⊢); linarith
      -- 2.3. calculation
      have s2_3 : S 0 = G 0 := by
        calc S 0 = (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (0 - k) k : ℤ) : ℤ)) := by first | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
          _ = (LeanBridges.Counting.choose (0 : ℤ) (0 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))); parley_side)
          _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 0)); parley_side)
          _ = G 0 := by parley_side
      -- 2.4. proof
      -- what this block shows, Lean's types give
      -- 2.5. proof
      -- what this block shows, Lean's types give
      -- 2.6. mun:sum-single a := 0, from 2.5
      have s2_6 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) = (LeanBridges.Counting.choose (1 : ℤ) (0 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))); parley_side)
      -- 2.7. mun:binomial-zero-index n := 1
      have s2_7 : (LeanBridges.Counting.choose (1 : ℤ) (0 : ℤ) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := 1)); parley_side)
      -- 2.8. arithmetic
      have s2_8 : (1 - 1 : ℤ) = 0 := by parley_arith
      -- 2.9. arithmetic
      have s2_9 : (0 : ℤ) < 1 := by parley_arith
      -- 2.10. calculation
      have s2_10 : (LeanBridges.Counting.choose (1 - 1 : ℤ) (1 : ℤ) : ℤ) = 0 := by
        calc (LeanBridges.Counting.choose (1 - 1 : ℤ) (1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (0 : ℤ) (1 : ℤ) : ℤ) := by parley_subst s2_8
          _ = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (1 : ℤ))) (by parley_side); parley_side)
      -- 2.11. calculation
      have s2_11 : (∑ k ∈ Finset.Icc (0 : ℤ) (1 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) = 1 := by
        calc (∑ k ∈ Finset.Icc (0 : ℤ) (1 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) + (LeanBridges.Counting.choose (1 - 1 : ℤ) (1 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := 0)); parley_side)
          _ = (LeanBridges.Counting.choose (1 : ℤ) (0 : ℤ) : ℤ) + (LeanBridges.Counting.choose (1 - 1 : ℤ) (1 : ℤ) : ℤ) := by parley_subst s2_6
          _ = 1 + (LeanBridges.Counting.choose (1 - 1 : ℤ) (1 : ℤ) : ℤ) := by parley_subst s2_7
          _ = 1 := by parley_subst s2_10
      -- 2.12. D1
      have s2_12 : G (0 + 1) = F 0 + G 0 := by have h := (hD1.2.2 ((0 + 1 : ℤ) - 1) (by omega)).2; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
      -- 2.13. D1
      have s2_13 : F 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
      -- 2.14. calculation
      have s2_14 : S 1 = G 1 := by
        calc S 1 = (∑ k ∈ Finset.Icc (0 : ℤ) (1 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) := by first | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
          _ = 1 := by parley_side
          _ = 0 + 1 := by norm_num
          _ = 0 + G 0 := by parley_subst s2_2
          _ = F 0 + G 0 := by parley_subst s2_13
          _ = G 1 := by parley_side
      -- 2.15. join 2.3, 2.14
      have s2_15a : S 0 = G 0 := by parley_side
      have s2_15b : S 1 = G 1 := by parley_side
      all_goals parley_side
    | succ j hIH =>
      -- 2.16. calculation
      have s2_16 : S ((j : ℤ) + 1) = G ((j : ℤ) + 1) := by parley_side
      -- 2.17. calculation
      have s2_17 : S ((j : ℤ) + 1 + 1) = S ((j : ℤ) + 1) + S (j : ℤ) := by
        calc S ((j : ℤ) + 1 + 1) = (∑ k ∈ Finset.Icc (0 : ℤ) ((j : ℤ) + 1 + 1), ((LeanBridges.Counting.choose ((j : ℤ) + 1 + 1 - k) k : ℤ) : ℤ)) := by first | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
          _ = (∑ k ∈ Finset.Icc (0 : ℤ) ((j : ℤ) + 1), ((LeanBridges.Counting.choose ((j : ℤ) + 1 - k) k : ℤ) : ℤ)) + (∑ k ∈ Finset.Icc (0 : ℤ) (j : ℤ), ((LeanBridges.Counting.choose ((j : ℤ) - k) k : ℤ) : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep.fibonacci_binomial_step (m := j)) | (have h := (Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep.fibonacci_binomial_step (m := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep.fibonacci_binomial_step (m := j)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep.fibonacci_binomial_step (m := j)) | exact_mod_cast ((Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep.fibonacci_binomial_step (m := j))).symm | (have h := (Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep.fibonacci_binomial_step (m := j)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep.fibonacci_binomial_step (m := j)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep.fibonacci_binomial_step (m := j)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep.fibonacci_binomial_step (m := j)); parley_side)
          _ = S ((j : ℤ) + 1) + (∑ k ∈ Finset.Icc (0 : ℤ) (j : ℤ), ((LeanBridges.Counting.choose ((j : ℤ) - k) k : ℤ) : ℤ)) := by first | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
          _ = S ((j : ℤ) + 1) + S (j : ℤ) := by first | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
      -- 2.18. instantiate i := j + 1 in line 1
      have s2_18 : 0 ≤ F ((j : ℤ) + 1) ∧ 0 ≤ G ((j : ℤ) + 1) := by first | exact (s1 (j + 1)) | exact ((s1 (j + 1))).symm | simpa using (s1 (j + 1)) | exact_mod_cast (s1 (j + 1)) | (have h := (s1 (j + 1)); parley_side)
      -- 2.19. instantiate i := j in line 1
      have s2_19 : 0 ≤ F (j : ℤ) ∧ 0 ≤ G (j : ℤ) := by first | exact (s1 j) | exact ((s1 j)).symm | simpa using (s1 j) | exact_mod_cast (s1 j) | (have h := (s1 j); parley_side)
      -- 2.20. D1
      have s2_20 : G ((j : ℤ) + 1 + 1) = F ((j : ℤ) + 1) + G ((j : ℤ) + 1) := by have h := (hD1.2.2 (((j : ℤ) + 1 + 1) - 1) (by omega)).2; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
      -- 2.21. D1
      have s2_21 : F ((j : ℤ) + 1) = G (j : ℤ) := by have h := (hD1.2.2 (((j : ℤ) + 1) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
      -- 2.22. calculation
      have r151_1 : 0 ≤ G ((j : ℤ) + 1) := by parley_side
      have r151_2 : 0 ≤ G (j : ℤ) := by parley_side
      have s2_22 : S ((j : ℤ) + 1 + 1) = G ((j : ℤ) + 1 + 1) := by
        calc S ((j : ℤ) + 1 + 1) = S ((j : ℤ) + 1) + S (j : ℤ) := by parley_side
          _ = G ((j : ℤ) + 1) + S (j : ℤ) := by parley_subst hIH.2
          _ = G ((j : ℤ) + 1) + G (j : ℤ) := by parley_subst hIH.1
          _ = G (j : ℤ) + G ((j : ℤ) + 1) := by parley_ring
          _ = F ((j : ℤ) + 1) + G ((j : ℤ) + 1) := by parley_subst s2_21
          _ = G ((j : ℤ) + 1 + 1) := by parley_side
      -- 2.23. join 2.16, 2.22
      have s2_23a : S ((j : ℤ) + 1) = G ((j : ℤ) + 1) := by parley_side
      have s2_23b : S ((j : ℤ) + 1 + 1) = G ((j : ℤ) + 1 + 1) := by parley_side
      all_goals parley_side
  -- 3. instantiate j := n in line 2
  have s3 : S (n : ℤ) = G (n : ℤ) ∧ S ((n : ℤ) + 1) = G ((n : ℤ) + 1) := by first | exact (s2 n) | exact ((s2 n)).symm | simpa using (s2 n) | exact_mod_cast (s2 n) | (have h := (s2 n); parley_side)
  -- 4. calculation
  have s4 : S (n : ℤ) = G (n : ℤ) := by parley_side
  -- 5. D1
  have s5 : F ((n : ℤ) + 1) = G (n : ℤ) := by have h := (hD1.2.2 (((n : ℤ) + 1) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
  -- 6. calculation
  have s6 : (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), ((LeanBridges.Counting.choose ((n : ℤ) - k) k : ℤ) : ℤ)) = F ((n : ℤ) + 1) := by
    calc (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), ((LeanBridges.Counting.choose ((n : ℤ) - k) k : ℤ) : ℤ)) = S (n : ℤ) := by first | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
      _ = G (n : ℤ) := by parley_side
      _ = F ((n : ℤ) + 1) := by parley_side
  all_goals exact s6

end Parley.Proofs.Hammack.BinomialDiagonalSumIsFibonacci.BinomialDiagonalSumIsFibonacci
