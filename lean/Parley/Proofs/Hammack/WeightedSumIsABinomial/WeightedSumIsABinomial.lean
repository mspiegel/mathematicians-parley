module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Functions
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.BinomialOnTheDiagonal.BinomialOnTheDiagonal
public import Parley.Proofs.Hammack.SumOfFirstNaturalsIsABinomial.SumOfFirstNaturalsIsABinomial

/-! Written from proofs/hammack/weighted-sum-is-a-binomial.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.WeightedSumIsABinomial.WeightedSumIsABinomial

set_option maxHeartbeats 400000 in
theorem weighted_sum_is_a_binomial (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (k * (n - k + 1) : ℤ)) = (LeanBridges.Counting.choose (n + 2) (3 : ℤ) : ℤ) := by
  set T : ℤ → ℤ := fun m : ℤ => ∑ i ∈ Finset.Icc (1 : ℤ) m, (i * (m - i + 1) : ℤ) with hD1
  -- 1. induction on j starting at 1
  have s1 : ∀ j : ℤ, 0 < j → T j = (LeanBridges.Counting.choose (j + 2) (3 : ℤ) : ℤ) := by
    intro j h_j
    replace h_j : 1 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      calc T 1 = (∑ i ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (i * (1 - i + 1) : ℤ)) := by simp (disch := omega) only [hD1]
        _ = 1 * (1 - 1 + 1) := by exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun i : ℤ => i * (1 - i + 1))) (a := (1 : ℤ)))
        _ = 1 := by norm_num
        _ = (LeanBridges.Counting.choose (3 : ℤ) (3 : ℤ) : ℤ) := by exact (Parley.Proofs.Hammack.BinomialOnTheDiagonal.BinomialOnTheDiagonal.binomial_on_the_diagonal (m := (3 : ℤ)) (by parley_side)).symm
        _ = (LeanBridges.Counting.choose (1 + 2 : ℤ) (3 : ℤ) : ℤ) := by norm_num
    | succ j hK hIH =>
      -- 1.2. proof
      have s1_2 : ∀ i : ℤ, i ∈ Finset.Icc 1 (j + 1) → i * (j + 1 - i + 1) = i * (j - i + 1) + i := by
        intro i hL
        try push_cast at hL
        try have hL_bounds := Finset.mem_Icc.mp hL
        -- 1.2.1. algebra
        parley_ring
      -- 1.3. membership
      -- 1.4. membership
      -- 1.5. membership
      -- 1.6. membership
      -- 1.7. mun:sum-extended a := 1, n := j, from 1.5
      have r56_1 : j ≥ 1 := by parley_side
      have s1_7 : (∑ i ∈ Finset.Icc (1 : ℤ) (j + 1), (i * (j - i + 1) : ℤ)) = (∑ i ∈ Finset.Icc (1 : ℤ) j, (i * (j - i + 1) : ℤ)) + (j + 1) * (j - (j + 1) + 1) := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun i : ℤ => i * (j - i + 1))) (a := (1 : ℤ)) (n := j) r56_1)
      -- 1.8. thm:sum-of-first-naturals-is-a-binomial n := j + 1
      have s1_8 : (∑ i ∈ Finset.Icc (1 : ℤ) (j + 1), (i : ℤ)) = (LeanBridges.Counting.choose (j + 1 + 1) (2 : ℤ) : ℤ) := by exact (Parley.Proofs.Hammack.SumOfFirstNaturalsIsABinomial.SumOfFirstNaturalsIsABinomial.sum_of_first_naturals_is_a_binomial (n := j + 1) (by parley_side))
      -- 1.9. thm:pascal n := j + 2, k := 3
      have s1_9 : (LeanBridges.Counting.choose (j + 2) (3 : ℤ) : ℤ) + (LeanBridges.Counting.choose (j + 2) (3 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose (j + 2 + 1) (3 : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := j + 2) (by parley_side) (k := (3 : ℤ)))
      -- 1.10. substitute 3 − 1 = 2 (arithmetic) into line 1.9
      have s1_10 : (LeanBridges.Counting.choose (j + 2) (3 : ℤ) : ℤ) + (LeanBridges.Counting.choose (j + 2) (2 : ℤ) : ℤ) = (LeanBridges.Counting.choose (j + 2 + 1) (3 : ℤ) : ℤ) := by parley_subst_at (show (3 - 1 : ℤ) = 2 by parley_side) s1_9
      -- 1.11. substitute
      have s1_11 : (LeanBridges.Counting.choose (j + 2) (3 : ℤ) : ℤ) + (LeanBridges.Counting.choose (j + 2) (2 : ℤ) : ℤ) = (LeanBridges.Counting.choose (j + 1 + 2) (3 : ℤ) : ℤ) := by
        have c1 : j + 2 + 1 = j + 1 + 2 := by parley_ring
        have row1 : (LeanBridges.Counting.choose (j + 2) (3 : ℤ) : ℤ) + (LeanBridges.Counting.choose (j + 2) (2 : ℤ) : ℤ) = (LeanBridges.Counting.choose (j + 1 + 2) (3 : ℤ) : ℤ) := by parley_subst_at c1 s1_10
        exact row1
      -- 1.12. substitute
      have s1_12 : (∑ i ∈ Finset.Icc (1 : ℤ) (j + 1), (i : ℤ)) = (LeanBridges.Counting.choose (j + 2) (2 : ℤ) : ℤ) := by
        have c1 : j + 1 + 1 = j + 2 := by parley_ring
        have row1 : (∑ i ∈ Finset.Icc (1 : ℤ) (j + 1), (i : ℤ)) = (LeanBridges.Counting.choose (j + 2) (2 : ℤ) : ℤ) := by parley_subst_at c1 s1_8
        exact row1
      -- 1.13. substitute
      have s1_13 : (∑ i ∈ Finset.Icc (1 : ℤ) (j + 1), (i * (j - i + 1) : ℤ)) = (∑ i ∈ Finset.Icc (1 : ℤ) j, (i * (j - i + 1) : ℤ)) := by
        have c1 : (∑ i ∈ Finset.Icc (1 : ℤ) j, (i * (j - i + 1) : ℤ)) + (j + 1) * (j - (j + 1) + 1) = (∑ i ∈ Finset.Icc (1 : ℤ) j, (i * (j - i + 1) : ℤ)) := by parley_ring
        have row1 : (∑ i ∈ Finset.Icc (1 : ℤ) (j + 1), (i * (j - i + 1) : ℤ)) = (∑ i ∈ Finset.Icc (1 : ℤ) j, (i * (j - i + 1) : ℤ)) := by parley_subst_at c1 s1_7
        exact row1
      -- 1.14. calculation
      have s1_14 : (∑ i ∈ Finset.Icc (1 : ℤ) (j + 1), (i * (j - i + 1) : ℤ)) = T j := by
        calc (∑ i ∈ Finset.Icc (1 : ℤ) (j + 1), (i * (j - i + 1) : ℤ)) = (∑ i ∈ Finset.Icc (1 : ℤ) j, (i * (j - i + 1) : ℤ)) := by exact s1_13
          _ = T j := by simp (disch := omega) only [hD1]
      -- 1.15. calculation
      calc T (j + 1) = (∑ i ∈ Finset.Icc (1 : ℤ) (j + 1), (i * (j + 1 - i + 1) : ℤ)) := by simp (disch := omega) only [hD1]
        _ = (∑ i ∈ Finset.Icc (1 : ℤ) (j + 1), (i * (j - i + 1) + i : ℤ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun i : ℤ => i * (j + 1 - i + 1))) (u := (fun i : ℤ => i * (j - i + 1) + i)) (a := (1 : ℤ)) (b := j + 1) s1_2)
        _ = (∑ i ∈ Finset.Icc (1 : ℤ) (j + 1), (i * (j - i + 1) : ℤ)) + (∑ i ∈ Finset.Icc (1 : ℤ) (j + 1), (i : ℤ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_add (t := (fun i : ℤ => i * (j - i + 1))) (u := (fun i : ℤ => i)) (a := (1 : ℤ)) (b := j + 1))
        _ = T j + (∑ i ∈ Finset.Icc (1 : ℤ) (j + 1), (i : ℤ)) := by parley_subst s1_14
        _ = T j + (LeanBridges.Counting.choose (j + 2) (2 : ℤ) : ℤ) := by parley_subst s1_12
        _ = (LeanBridges.Counting.choose (j + 2) (3 : ℤ) : ℤ) + (LeanBridges.Counting.choose (j + 2) (2 : ℤ) : ℤ) := by parley_subst hIH
        _ = (LeanBridges.Counting.choose (j + 1 + 2) (3 : ℤ) : ℤ) := by exact s1_11
  -- 2. calculation
  calc (∑ k ∈ Finset.Icc (1 : ℤ) n, (k * (n - k + 1) : ℤ)) = T n := by simp (disch := omega) only [hD1]
    _ = (LeanBridges.Counting.choose (n + 2) (3 : ℤ) : ℤ) := by exact (s1 n (by parley_side))

end Parley.Proofs.Hammack.WeightedSumIsABinomial.WeightedSumIsABinomial
