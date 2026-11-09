module

public import AlgebraTactics
public import ArithTactics
public import Counting
public import FactorialTactics
public import Functions
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
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
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep
public import Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural

/-! Written from proofs/hammack/binomial-diagonal-sum-is-fibonacci.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialDiagonalSumIsFibonacci.BinomialDiagonalSumIsFibonacci

set_option maxHeartbeats 800000 in
theorem binomial_diagonal_sum_is_fibonacci (n : ℤ) (hH1 : 0 ≤ n) (F : ℤ → ℤ) (G : ℤ → ℤ) (hD1 : F 0 = (0 : ℤ) ∧ G 0 = (1 : ℤ) ∧ (∀ k : ℤ, 0 ≤ k → F (k + 1) = G k ∧ G (k + 1) = F k + G k)) :
    (∑ k ∈ Finset.Icc (0 : ℤ) n, ((LeanBridges.Counting.choose (n - k) k : ℤ) : ℤ)) = F (n + 1) := by
  set S : ℤ → ℤ := fun m : ℤ => ∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose (m - k) k : ℤ) : ℤ) with hD2
  -- 1. thm:fibonacci-natural
  have s1 : ∀ i : ℤ, 0 ≤ i → 0 ≤ F i ∧ 0 ≤ G i := by exact (Parley.Proofs.Hammack.FibonacciNumbers.FibonacciNatural.fibonacci_natural (F := F) (G := G) (by parley_side))
  -- 2. induction on j starting at 0
  have s2 : ∀ j : ℤ, 0 ≤ j → S j = G j ∧ S (j + 1) = G (j + 1) := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 2.1. proof
      -- what this block shows, Lean's types give
      -- 2.2. D1
      have s2_2 : G 0 = 1 := by have h := hD1.2.1; (try ring_nf at h ⊢); linarith
      -- 2.3. calculation
      have s2_3 : S 0 = G 0 := by
        calc S 0 = (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (0 - k) k : ℤ) : ℤ)) := by simp (disch := omega) only [hD2]
          _ = (LeanBridges.Counting.choose (0 : ℤ) (0 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (0 - k) k : ℤ))) (a := (0 : ℤ))); parley_side)
          _ = 1 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (0 : ℤ)) (by parley_side))
          _ = G 0 := by parley_side
      -- 2.4. proof
      -- what this block shows, Lean's types give
      -- 2.5. proof
      -- what this block shows, Lean's types give
      -- 2.6. mun:sum-single a := 0, from 2.5
      have s2_6 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) = (LeanBridges.Counting.choose (1 : ℤ) (0 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (a := (0 : ℤ))); parley_side)
      -- 2.7. mun:binomial-zero-index n := 1
      have s2_7 : (LeanBridges.Counting.choose (1 : ℤ) (0 : ℤ) : ℤ) = 1 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := (1 : ℤ)) (by parley_side))
      -- 2.8. arithmetic
      have s2_8 : (1 - 1 : ℤ) = 0 := by parley_arith
      -- 2.9. arithmetic
      have s2_9 : (0 : ℤ) < 1 := by parley_arith
      -- 2.10. calculation
      have s2_10 : (LeanBridges.Counting.choose (1 - 1 : ℤ) (1 : ℤ) : ℤ) = 0 := by
        calc (LeanBridges.Counting.choose (1 - 1 : ℤ) (1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (0 : ℤ) (1 : ℤ) : ℤ) := by parley_subst s2_8
          _ = 0 := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := (1 : ℤ))) s2_9
      -- 2.11. calculation
      have s2_11 : (∑ k ∈ Finset.Icc (0 : ℤ) (1 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) = 1 := by
        calc (∑ k ∈ Finset.Icc (0 : ℤ) (1 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) + (LeanBridges.Counting.choose (1 - 1 : ℤ) (1 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := (0 : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := (0 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := (0 : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := (0 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := (0 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := (0 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose (1 - k) k : ℤ))) (n := (0 : ℤ)) (by parley_side)); parley_side)
          _ = (LeanBridges.Counting.choose (1 : ℤ) (0 : ℤ) : ℤ) + (LeanBridges.Counting.choose (1 - 1 : ℤ) (1 : ℤ) : ℤ) := by parley_subst s2_6
          _ = 1 + (LeanBridges.Counting.choose (1 - 1 : ℤ) (1 : ℤ) : ℤ) := by parley_subst s2_7
          _ = 1 := by parley_subst s2_10
      -- 2.12. D1
      have s2_12 : G (0 + 1) = F 0 + G 0 := by have h := (hD1.2.2 ((0 + 1 : ℤ) - 1) (by omega)).2; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
      -- 2.13. D1
      have s2_13 : F 0 = 0 := by have h := hD1.1; (try ring_nf at h ⊢); linarith
      -- 2.14. calculation
      have s2_14 : S 1 = G 1 := by
        calc S 1 = (∑ k ∈ Finset.Icc (0 : ℤ) (1 : ℤ), ((LeanBridges.Counting.choose (1 - k) k : ℤ) : ℤ)) := by simp (disch := omega) only [hD2]
          _ = 1 := by parley_side
          _ = 0 + 1 := by norm_num
          _ = 0 + G 0 := by parley_subst s2_2
          _ = F 0 + G 0 := by parley_subst s2_13
          _ = G 1 := by parley_side
      -- 2.15. join 2.3, 2.14
      have s2_15a : S 0 = G 0 := by parley_side
      have s2_15b : S 1 = G 1 := by parley_side
      exact ⟨s2_15a, by simpa only [zero_add] using s2_15b⟩
    | succ j hK hIH =>
      -- 2.16. calculation
      have s2_16 : S (j + 1) = G (j + 1) := by parley_side
      -- 2.17. calculation
      have s2_17 : S (j + 1 + 1) = S (j + 1) + S j := by
        calc S (j + 1 + 1) = (∑ k ∈ Finset.Icc (0 : ℤ) (j + 1 + 1), ((LeanBridges.Counting.choose (j + 1 + 1 - k) k : ℤ) : ℤ)) := by simp (disch := omega) only [hD2]
          _ = (∑ k ∈ Finset.Icc (0 : ℤ) (j + 1), ((LeanBridges.Counting.choose (j + 1 - k) k : ℤ) : ℤ)) + (∑ k ∈ Finset.Icc (0 : ℤ) j, ((LeanBridges.Counting.choose (j - k) k : ℤ) : ℤ)) := by exact (Parley.Proofs.Hammack.FibonacciBinomialStep.FibonacciBinomialStep.fibonacci_binomial_step (m := j) (by parley_side))
          _ = S (j + 1) + (∑ k ∈ Finset.Icc (0 : ℤ) j, ((LeanBridges.Counting.choose (j - k) k : ℤ) : ℤ)) := by simp (disch := omega) only [hD2]
          _ = S (j + 1) + S j := by simp (disch := omega) only [hD2]
      -- 2.18. instantiate i := j + 1 in line 1
      have s2_18 : 0 ≤ F (j + 1) ∧ 0 ≤ G (j + 1) := by exact (s1 (j + 1) (by parley_side))
      -- 2.19. instantiate i := j in line 1
      have s2_19 : 0 ≤ F j ∧ 0 ≤ G j := by exact (s1 j (by parley_side))
      -- 2.20. D1
      have s2_20 : G (j + 1 + 1) = F (j + 1) + G (j + 1) := by have h := (hD1.2.2 ((j + 1 + 1) - 1) (by omega)).2; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
      -- 2.21. D1
      have s2_21 : F (j + 1) = G j := by have h := (hD1.2.2 ((j + 1) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
      -- 2.22. calculation
      have r151_1 : 0 ≤ G (j + 1) := by parley_side
      have r151_2 : 0 ≤ G j := by parley_side
      have s2_22 : S (j + 1 + 1) = G (j + 1 + 1) := by
        calc S (j + 1 + 1) = S (j + 1) + S j := by parley_side
          _ = G (j + 1) + S j := by parley_subst hIH.2
          _ = G (j + 1) + G j := by parley_subst hIH.1
          _ = G j + G (j + 1) := by parley_ring
          _ = F (j + 1) + G (j + 1) := by parley_subst s2_21
          _ = G (j + 1 + 1) := by parley_side
      -- 2.23. join 2.16, 2.22
      have s2_23a : S (j + 1) = G (j + 1) := by parley_side
      have s2_23b : S (j + 1 + 1) = G (j + 1 + 1) := by parley_side
      exact ⟨s2_23a, s2_23b⟩
  -- 3. instantiate j := n in line 2
  have s3 : S n = G n ∧ S (n + 1) = G (n + 1) := by exact (s2 n (by parley_side))
  -- 4. calculation
  have s4 : S n = G n := by parley_side
  -- 5. D1
  have s5 : F (n + 1) = G n := by have h := (hD1.2.2 ((n + 1) - 1) (by omega)).1; simp only [sub_add_cancel] at h; (try ring_nf at h ⊢); linarith
  -- 6. calculation
  calc (∑ k ∈ Finset.Icc (0 : ℤ) n, ((LeanBridges.Counting.choose (n - k) k : ℤ) : ℤ)) = S n := by simp (disch := omega) only [hD2]
    _ = G n := by parley_side
    _ = F (n + 1) := by parley_side

end Parley.Proofs.Hammack.BinomialDiagonalSumIsFibonacci.BinomialDiagonalSumIsFibonacci
