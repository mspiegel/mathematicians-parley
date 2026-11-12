module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Functions
public import InstanceTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/weighted-binomial-column-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.WeightedBinomialColumnSum.WeightedBinomialColumnSum

theorem weighted_binomial_column_sum (m : ℤ) (hH1 : 0 < m) (n : ℤ) (hH2 : 0 < n) :
    (∑ k ∈ Finset.Icc (0 : ℤ) n, (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) = n * (LeanBridges.Counting.choose (m + n + 1) (m + 1) : ℤ) - (LeanBridges.Counting.choose (m + n + 1) (m + 2) : ℤ) := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℤ, 0 ≤ j → (∑ k ∈ Finset.Icc (0 : ℤ) j, (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) = j * (LeanBridges.Counting.choose (m + j + 1) (m + 1) : ℤ) - (LeanBridges.Counting.choose (m + j + 1) (m + 2) : ℤ) := by
    intro j h_j
    replace h_j : 0 ≤ j := by omega
    induction j, h_j using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. mun:sum-single a := 0
      have s1_1 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) = 0 * (LeanBridges.Counting.choose m m : ℤ) := by
        have hI : (∑ b ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (b * (LeanBridges.Counting.choose (m + b) m : ℤ) : ℤ)) = 0 * (LeanBridges.Counting.choose (m + 0) m : ℤ) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k * (LeanBridges.Counting.choose (m + k) m : ℤ))) (a := (0 : ℤ))))
        simpa only [add_zero] using hI
      -- 1.2. inequalities
      have s1_2 : m + 1 < m + 2 := by linarith
      -- 1.3. def:C n := m + 1, k := m + 2, from 1.2
      have s1_3 : (LeanBridges.Counting.choose (m + 1) (m + 2) : ℤ) = 0 := by exact (Parley.Items.Stdlib.Counting.def_C_3 (n := m + 1) (by parley_side) (k := m + 2)) s1_2
      -- 1.4. algebra, from 1.1, 1.3
      have s1_4 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) = 0 * (LeanBridges.Counting.choose (m + 1) (m + 1) : ℤ) - (LeanBridges.Counting.choose (m + 1) (m + 2) : ℤ) := by linear_combination (norm := parley_norm) s1_1 + s1_3
      simpa only [add_zero] using s1_4
    | succ j hK hIH =>
      -- 1.5. mun:sum-extended a := 0, n := j
      have r35_1 : j ≥ 0 := by parley_side
      have s1_5 : (∑ k ∈ Finset.Icc (0 : ℤ) (j + 1), (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) j, (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) + (j + 1) * (LeanBridges.Counting.choose (m + (j + 1)) m : ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k * (LeanBridges.Counting.choose (m + k) m : ℤ))) (a := (0 : ℤ)) (n := j) r35_1)
      -- 1.6. substitute
      have s1_6 : (∑ k ∈ Finset.Icc (0 : ℤ) (j + 1), (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) j, (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) + (j + 1) * (LeanBridges.Counting.choose (m + j + 1) m : ℤ) := by
        have c1 : m + (j + 1) = m + j + 1 := by parley_ring
        have row1 : (∑ k ∈ Finset.Icc (0 : ℤ) (j + 1), (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) j, (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) + (j + 1) * (LeanBridges.Counting.choose (m + j + 1) m : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (∑ k ∈ Finset.Icc (0 : ℤ) (j + 1), (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) j, (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) + (j + 1) * (LeanBridges.Counting.choose t m : ℤ))) c1 s1_5; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 1.7. thm:pascal n := m + j + 1, k := m + 1
      have s1_7 : (LeanBridges.Counting.choose (m + j + 1) (m + 1) : ℤ) + (LeanBridges.Counting.choose (m + j + 1) (m + 1 - 1) : ℤ) = (LeanBridges.Counting.choose (m + j + 1 + 1) (m + 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (by parley_side) (k := m + 1))
      -- 1.8. substitute
      have s1_8 : (LeanBridges.Counting.choose (m + j + 1) (m + 1) : ℤ) + (LeanBridges.Counting.choose (m + j + 1) m : ℤ) = (LeanBridges.Counting.choose (m + j + 1 + 1) (m + 1) : ℤ) := by
        have c1 : m + 1 - 1 = m := by parley_ring
        have row1 : (LeanBridges.Counting.choose (m + j + 1) (m + 1) : ℤ) + (LeanBridges.Counting.choose (m + j + 1) m : ℤ) = (LeanBridges.Counting.choose (m + j + 1 + 1) (m + 1) : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.choose (m + j + 1) (m + 1) : ℤ) + (LeanBridges.Counting.choose (m + j + 1) t : ℤ) = (LeanBridges.Counting.choose (m + j + 1 + 1) (m + 1) : ℤ))) c1 s1_7; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 1.9. thm:pascal n := m + j + 1, k := m + 2
      have s1_9 : (LeanBridges.Counting.choose (m + j + 1) (m + 2) : ℤ) + (LeanBridges.Counting.choose (m + j + 1) (m + 2 - 1) : ℤ) = (LeanBridges.Counting.choose (m + j + 1 + 1) (m + 2) : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (by parley_side) (k := m + 2))
      -- 1.10. substitute
      have s1_10 : (LeanBridges.Counting.choose (m + j + 1) (m + 2) : ℤ) + (LeanBridges.Counting.choose (m + j + 1) (m + 1) : ℤ) = (LeanBridges.Counting.choose (m + j + 1 + 1) (m + 2) : ℤ) := by
        have c1 : m + 2 - 1 = m + 1 := by parley_ring
        have row1 : (LeanBridges.Counting.choose (m + j + 1) (m + 2) : ℤ) + (LeanBridges.Counting.choose (m + j + 1) (m + 1) : ℤ) = (LeanBridges.Counting.choose (m + j + 1 + 1) (m + 2) : ℤ) := by (have h := Eq.subst (motive := (fun t : ℤ => (LeanBridges.Counting.choose (m + j + 1) (m + 2) : ℤ) + (LeanBridges.Counting.choose (m + j + 1) t : ℤ) = (LeanBridges.Counting.choose (m + j + 1 + 1) (m + 2) : ℤ))) c1 s1_9; push_cast at h ⊢; all_goals exact_mod_cast h)
        exact row1
      -- 1.11. algebra, from IH, 1.6, 1.8, 1.10
      have s1_11 : (∑ k ∈ Finset.Icc (0 : ℤ) (j + 1), (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) = (j + 1) * (LeanBridges.Counting.choose (m + j + 1 + 1) (m + 1) : ℤ) - (LeanBridges.Counting.choose (m + j + 1 + 1) (m + 2) : ℤ) := by linear_combination (norm := parley_norm) hIH + s1_6 + (j + 1) * s1_8 + (-1) * s1_10
      -- 1.12. algebra
      have s1_12 : m + j + 1 + 1 = m + (j + 1) + 1 := by parley_ring
      -- 1.13. substitute (m + j + 1) + 1 = m + (j + 1) + 1 (line 1.12) into line 1.11
      (have h := Eq.subst (motive := (fun t : ℤ => (∑ k ∈ Finset.Icc (0 : ℤ) (j + 1), (k * (LeanBridges.Counting.choose (m + k) m : ℤ) : ℤ)) = (j + 1) * (LeanBridges.Counting.choose t (m + 1) : ℤ) - (LeanBridges.Counting.choose t (m + 2) : ℤ))) s1_12 s1_11; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. instantiate j := n in line 1
  exact (s1 n (le_of_lt hH2))

end Parley.Proofs.Hammack.WeightedBinomialColumnSum.WeightedBinomialColumnSum
