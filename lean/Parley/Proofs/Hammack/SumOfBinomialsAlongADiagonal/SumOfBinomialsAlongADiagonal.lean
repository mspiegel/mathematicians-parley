module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Functions
public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
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
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-binomials-along-a-diagonal.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfBinomialsAlongADiagonal.SumOfBinomialsAlongADiagonal

theorem sum_of_binomials_along_a_diagonal (n : ℤ) (hH1 : 0 ≤ n) (k : ℤ) (hH2 : 0 ≤ k) (S : ℤ → ℤ) (hD1 : ∀ m : ℤ, 0 ≤ m → S m = (∑ j ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose (n + j) j : ℤ) : ℤ))) :
    (∑ j ∈ Finset.Icc (0 : ℤ) k, ((LeanBridges.Counting.choose (n + j) j : ℤ) : ℤ)) = (LeanBridges.Counting.choose (n + k + 1) k : ℤ) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℤ, 0 ≤ m → S m = (LeanBridges.Counting.choose (n + m + 1) m : ℤ) := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : S 0 = (LeanBridges.Counting.choose (n + 1) (0 : ℤ) : ℤ) := by
        calc S 0 = (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (n + j) j : ℤ) : ℤ)) := by simp (disch := omega) only [hD1]
          _ = (LeanBridges.Counting.choose n (0 : ℤ) : ℤ) := by
              have hI : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (n + k) k : ℤ) : ℤ)) = (LeanBridges.Counting.choose (n + 0) (0 : ℤ) : ℤ) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ))))
              simpa only [Int.cast_zero, add_zero] using hI
          _ = 1 := by exact (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n) hH1)
          _ = (LeanBridges.Counting.choose (n + 1) (0 : ℤ) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1) (add_nonneg (hH1) (by norm_num))).symm
      simpa only [add_zero, Int.cast_zero] using s1_1
    | succ m hK hIH =>
      -- 1.2. calculation
      have r31_1 : m ≥ 0 := by parley_side
      have s1_2 : S (m + 1) = S m + (LeanBridges.Counting.choose (n + (m + 1)) (m + 1) : ℤ) := by
        calc S (m + 1) = (∑ j ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (n + j) j : ℤ) : ℤ)) := by simp (disch := omega) only [hD1]
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose (n + j) j : ℤ) : ℤ)) + (LeanBridges.Counting.choose (n + (m + 1)) (m + 1) : ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ)) (n := m) r31_1)
          _ = S m + (LeanBridges.Counting.choose (n + (m + 1)) (m + 1) : ℤ) := by simp (disch := omega) only [hD1]
      -- 1.3. algebra
      have s1_3 : n + (m + 1) = n + m + 1 := by parley_ring
      -- 1.4. thm:pascal n := n + m + 1, k := m + 1
      have s1_4 : (LeanBridges.Counting.choose (n + m + 1) (m + 1) : ℤ) + (LeanBridges.Counting.choose (n + m + 1) (m + 1 - 1) : ℤ) = (LeanBridges.Counting.choose (n + m + 1 + 1) (m + 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (add_nonneg (add_nonneg (hH1) (hK)) (by norm_num)) (k := m + 1))
      -- 1.5. substitute
      have s1_5 : (LeanBridges.Counting.choose (n + m + 1) (m + 1) : ℤ) + (LeanBridges.Counting.choose (n + m + 1) m : ℤ) = (LeanBridges.Counting.choose (n + m + 1 + 1) (m + 1) : ℤ) := by
        have c1 : m + 1 - 1 = m := by parley_ring
        have row1 : (LeanBridges.Counting.choose (n + m + 1) (m + 1) : ℤ) + (LeanBridges.Counting.choose (n + m + 1) m : ℤ) = (LeanBridges.Counting.choose (n + m + 1 + 1) (m + 1) : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.choose (n + m + 1) (m + 1) : ℤ) + (LeanBridges.Counting.choose (n + m + 1) t : ℤ) = (LeanBridges.Counting.choose (n + m + 1 + 1) (m + 1) : ℤ))) c1 s1_4; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 1.6. algebra
      have s1_6 : n + m + 1 + 1 = n + (m + 1) + 1 := by parley_ring
      -- 1.7. substitute n + (m + 1) = n + m + 1 (line 1.3)
      have s1_7 : (LeanBridges.Counting.choose (n + (m + 1)) (m + 1) : ℤ) = (LeanBridges.Counting.choose (n + m + 1) (m + 1) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose t (m + 1) : ℤ)) s1_3; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 1.8. calculation
      calc S (m + 1) = S m + (LeanBridges.Counting.choose (n + (m + 1)) (m + 1) : ℤ) := by exact s1_2
        _ = (LeanBridges.Counting.choose (n + m + 1) m : ℤ) + (LeanBridges.Counting.choose (n + (m + 1)) (m + 1) : ℤ) := by (have h := congrArg (fun t : ℤ => t + (LeanBridges.Counting.choose (n + (m + 1)) (m + 1) : ℤ)) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = (LeanBridges.Counting.choose (n + m + 1) m : ℤ) + (LeanBridges.Counting.choose (n + m + 1) (m + 1) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose (n + m + 1) m : ℤ) + t) s1_7; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = (LeanBridges.Counting.choose (n + m + 1) (m + 1) : ℤ) + (LeanBridges.Counting.choose (n + m + 1) m : ℤ) := by parley_ring
        _ = (LeanBridges.Counting.choose (n + m + 1 + 1) (m + 1) : ℤ) := by exact s1_5
        _ = (LeanBridges.Counting.choose (n + (m + 1) + 1) (m + 1) : ℤ) := by (have h := congrArg (fun t : ℤ => (LeanBridges.Counting.choose t (m + 1) : ℤ)) s1_6; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. calculation
  calc (∑ j ∈ Finset.Icc (0 : ℤ) k, ((LeanBridges.Counting.choose (n + j) j : ℤ) : ℤ)) = S k := by simp (disch := omega) only [hD1]
    _ = (LeanBridges.Counting.choose (n + k + 1) k : ℤ) := by exact (s1 k hH2)

end Parley.Proofs.Hammack.SumOfBinomialsAlongADiagonal.SumOfBinomialsAlongADiagonal
