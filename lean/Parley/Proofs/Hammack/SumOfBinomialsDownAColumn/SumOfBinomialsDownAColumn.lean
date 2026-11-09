module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Functions
public import OrderTactics
public import SubstTactics
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
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-binomials-down-a-column.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfBinomialsDownAColumn.SumOfBinomialsDownAColumn

theorem sum_of_binomials_down_a_column (n : ℤ) (hH1 : 0 < n) (r : ℤ) (hH2 : 0 < r) (hH3 : r ≤ n) (S : ℤ → ℤ) (hD1 : ∀ m : ℤ, 0 ≤ m → S m = (∑ j ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose j r : ℤ) : ℤ))) :
    (∑ k ∈ Finset.Icc (0 : ℤ) n, ((LeanBridges.Counting.choose k r : ℤ) : ℤ)) = (LeanBridges.Counting.choose (n + 1) (r + 1) : ℤ) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℤ, 0 ≤ m → S m = (LeanBridges.Counting.choose (m + 1) (r + 1) : ℤ) := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. inequalities, from H2
      have s1_1 : 0 < r := by parley_order
      -- 1.2. inequalities, from H2
      have s1_2 : 1 < r + 1 := by parley_order
      -- 1.3. calculation
      have s1_3 : S 0 = (LeanBridges.Counting.choose (1 : ℤ) (r + 1) : ℤ) := by
        calc S 0 = (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose j r : ℤ) : ℤ)) := by simp (disch := omega) only [hD1]
          _ = (LeanBridges.Counting.choose (0 : ℤ) r : ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ)))
          _ = 0 := by exact (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := r)) s1_1
          _ = (LeanBridges.Counting.choose (1 : ℤ) (r + 1) : ℤ) := by exact ((Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := r + 1)) s1_2).symm
      simpa only [zero_add] using s1_3
    | succ m hK hIH =>
      -- 1.4. calculation
      have r38_1 : m ≥ 0 := by parley_side
      have s1_4 : S (m + 1) = S m + (LeanBridges.Counting.choose (m + 1) r : ℤ) := by
        calc S (m + 1) = (∑ j ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose j r : ℤ) : ℤ)) := by simp (disch := omega) only [hD1]
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose j r : ℤ) : ℤ)) + (LeanBridges.Counting.choose (m + 1) r : ℤ) := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ)) (n := m) r38_1)
          _ = S m + (LeanBridges.Counting.choose (m + 1) r : ℤ) := by simp (disch := omega) only [hD1]
      -- 1.5. thm:pascal n := m + 1, k := r + 1
      have s1_5 : (LeanBridges.Counting.choose (m + 1) (r + 1) : ℤ) + (LeanBridges.Counting.choose (m + 1) (r + 1 - 1) : ℤ) = (LeanBridges.Counting.choose (m + 1 + 1) (r + 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (by parley_side) (k := r + 1))
      -- 1.6. substitute
      have s1_6 : (LeanBridges.Counting.choose (m + 1) (r + 1) : ℤ) + (LeanBridges.Counting.choose (m + 1) r : ℤ) = (LeanBridges.Counting.choose (m + 1 + 1) (r + 1) : ℤ) := by
        have c1 : r + 1 - 1 = r := by parley_ring
        have row1 : (LeanBridges.Counting.choose (m + 1) (r + 1) : ℤ) + (LeanBridges.Counting.choose (m + 1) r : ℤ) = (LeanBridges.Counting.choose (m + 1 + 1) (r + 1) : ℤ) := by parley_subst_at c1 s1_5
        exact row1
      -- 1.7. calculation
      calc S (m + 1) = S m + (LeanBridges.Counting.choose (m + 1) r : ℤ) := by exact s1_4
        _ = (LeanBridges.Counting.choose (m + 1) (r + 1) : ℤ) + (LeanBridges.Counting.choose (m + 1) r : ℤ) := by parley_subst hIH
        _ = (LeanBridges.Counting.choose (m + 1 + 1) (r + 1) : ℤ) := by exact s1_6
  -- 2. calculation
  calc (∑ k ∈ Finset.Icc (0 : ℤ) n, ((LeanBridges.Counting.choose k r : ℤ) : ℤ)) = S n := by simp (disch := omega) only [hD1]
    _ = (LeanBridges.Counting.choose (n + 1) (r + 1) : ℤ) := by exact (s1 n (by parley_side))

end Parley.Proofs.Hammack.SumOfBinomialsDownAColumn.SumOfBinomialsDownAColumn
