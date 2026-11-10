module

public import Functions
public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep

/-! Written from proofs/hammack/reciprocal-product-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalProductSum

theorem reciprocal_product_sum (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / ((k : ℚ) * ((k : ℚ) + 1)) : ℚ)) = 1 - 1 / ((n : ℚ) + 1) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. induction on k starting at 1
  have s2 : ∀ k : ℤ, 0 < k → (∑ j ∈ Finset.Icc (1 : ℤ) k, (1 / ((j : ℚ) * ((j : ℚ) + 1)) : ℚ)) = 1 - 1 / ((k : ℚ) + 1) := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 2.1. calculation
      have s2_1 : (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / ((j : ℚ) * ((j : ℚ) + 1)) : ℚ)) = 1 - 1 / (1 + 1) := by
        calc (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / ((j : ℚ) * ((j : ℚ) + 1)) : ℚ)) = 1 / (1 * (1 + 1)) := by
              have hI : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / ((k : ℚ) * ((k : ℚ) + 1)) : ℚ)) = 1 / (1 * (1 + 1)) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ))))
              exact hI
          _ = 1 - 1 / (1 + 1) := by norm_num
      (have h := s2_1; push_cast at h ⊢; all_goals exact h)
    | succ k hK hIH =>
      -- 2.2. calculation
      have r43_1 : k ≥ 1 := by parley_side
      have s2_2 : (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (1 / ((j : ℚ) * ((j : ℚ) + 1)) : ℚ)) = 1 - 1 / ((k : ℚ) + 1 + 1) := by
        calc (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (1 / ((j : ℚ) * ((j : ℚ) + 1)) : ℚ)) = (∑ j ∈ Finset.Icc (1 : ℤ) k, (1 / ((j : ℚ) * ((j : ℚ) + 1)) : ℚ)) + 1 / (((k : ℚ) + 1) * ((k : ℚ) + 1 + 1)) := by
              have hI : (∑ b ∈ Finset.Icc (1 : ℤ) (k + 1), (1 / ((b : ℚ) * ((b : ℚ) + 1)) : ℚ)) = (∑ b ∈ Finset.Icc (1 : ℤ) k, (1 / ((b : ℚ) * ((b : ℚ) + 1)) : ℚ)) + 1 / (((k : ℚ) + 1) * ((k : ℚ) + 1 + 1)) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ)) (n := k) r43_1))
              exact hI
          _ = 1 - 1 / ((k : ℚ) + 1) + 1 / (((k : ℚ) + 1) * ((k : ℚ) + 1 + 1)) := by (have h := congrArg (fun t : ℚ => t + 1 / (((k : ℚ) + 1) * ((k : ℚ) + 1 + 1))) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 1 - 1 / ((k : ℚ) + 1 + 1) := by
              have hI : 1 - 1 / ((k : ℚ) + 1) + 1 / (((k : ℚ) + 1) * ((k : ℚ) + 1 + 1)) = 1 - 1 / ((k : ℚ) + 1 + 1) := by parley_instance ((Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep.reciprocal_step (m := k + 1) (by parley_side)))
              exact hI
      (have h := s2_2; push_cast at h ⊢; all_goals exact h)
  -- 3. instantiate k := n in line 2
  exact (s2 n (by parley_side))

end Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalProductSum
