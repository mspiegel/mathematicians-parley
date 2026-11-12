module

public import Counting
public import FactorialTactics
public import Functions
public import InstanceTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.SumOfFactorialQuotients.FactorialQuotientStep

/-! Written from proofs/hammack/sum-of-factorial-quotients.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfFactorialQuotients.SumOfFactorialQuotients

theorem sum_of_factorial_quotients (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℚ) / (LeanBridges.Counting.factorial (k + 1) : ℚ) : ℚ)) = 1 - 1 / (LeanBridges.Counting.factorial (n + 1) : ℚ) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. induction on k starting at 1
  have s2 : ∀ k : ℤ, 0 < k → (∑ j ∈ Finset.Icc (1 : ℤ) k, ((j : ℚ) / (LeanBridges.Counting.factorial (j + 1) : ℚ) : ℚ)) = 1 - 1 / (LeanBridges.Counting.factorial (k + 1) : ℚ) := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 2.1. def:factorial
      have s2_1 : (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) = 1 := by exact Parley.Items.Stdlib.Counting.def_factorial_2
      -- 2.2. calculation
      have s2_2 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = 2 := by
        calc (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = (LeanBridges.Counting.factorial (1 : ℤ) : ℤ) * (1 + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := (1 : ℤ)) (by norm_num))
          _ = 1 * (1 + 1) := by (have h := congrArg (fun t : ℤ => t * (1 + 1)) s2_1; push_cast at h ⊢; all_goals exact_mod_cast h)
          _ = 2 := by norm_num
      -- 2.3. calculation
      calc (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), ((j : ℚ) / (LeanBridges.Counting.factorial (j + 1) : ℚ) : ℚ)) = 1 / (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℚ) := by
            have hI : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), ((k : ℚ) / (LeanBridges.Counting.factorial (k + 1) : ℚ) : ℚ)) = 1 / (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℚ) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) / (LeanBridges.Counting.factorial (j + 1) : ℚ))) (a := (1 : ℤ))))
            exact hI
        _ = 1 / 2 := by
            have e_w : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℚ) = 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_2; push_cast at h; linear_combination (norm := parley_norm) h
            (have h := congrArg (fun t : ℚ => 1 / t) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 1 - 1 / 2 := by norm_num
        _ = 1 - 1 / (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℚ) := by
            have e_w : 2 = (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_2.symm; push_cast at h; linear_combination (norm := parley_norm) h
            (have h := congrArg (fun t : ℚ => 1 - 1 / t) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
    | succ k hK hIH =>
      -- 2.4. def:factorial n := k + 1
      have s2_4 : (LeanBridges.Counting.factorial (k + 1 + 1) : ℤ) = (LeanBridges.Counting.factorial (k + 1) : ℤ) * (k + 1 + 1) := by exact (Parley.Items.Stdlib.Counting.def_factorial_3 (n := k + 1) (add_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hK)) (by norm_num)))
      -- 2.5. mun:factorial-nat n := k + 1
      have s2_5 : 0 < (LeanBridges.Counting.factorial (k + 1) : ℤ) := by exact (Parley.Items.Stdlib.Counting.mun_factorial_nat (n := k + 1) (add_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hK)) (by norm_num)))
      -- 2.6. calculation
      have r133_1 : k ≥ 1 := by parley_side
      calc (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), ((j : ℚ) / (LeanBridges.Counting.factorial (j + 1) : ℚ) : ℚ)) = (∑ j ∈ Finset.Icc (1 : ℤ) k, ((j : ℚ) / (LeanBridges.Counting.factorial (j + 1) : ℚ) : ℚ)) + ((k : ℚ) + 1) / (LeanBridges.Counting.factorial (k + 1 + 1) : ℚ) := by
            have hI : (∑ b ∈ Finset.Icc (1 : ℤ) (k + 1), ((b : ℚ) / (LeanBridges.Counting.factorial (b + 1) : ℚ) : ℚ)) = (∑ b ∈ Finset.Icc (1 : ℤ) k, ((b : ℚ) / (LeanBridges.Counting.factorial (b + 1) : ℚ) : ℚ)) + ((k : ℚ) + 1) / (LeanBridges.Counting.factorial (k + 1 + 1) : ℚ) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (j : ℚ) / (LeanBridges.Counting.factorial (j + 1) : ℚ))) (a := (1 : ℤ)) (n := k) r133_1))
            exact hI
        _ = 1 - 1 / (LeanBridges.Counting.factorial (k + 1) : ℚ) + ((k : ℚ) + 1) / (LeanBridges.Counting.factorial (k + 1 + 1) : ℚ) := by (have h := congrArg (fun t : ℚ => t + ((k : ℚ) + 1) / (LeanBridges.Counting.factorial (k + 1 + 1) : ℚ)) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 1 - 1 / (LeanBridges.Counting.factorial (k + 1) : ℚ) + ((k : ℚ) + 1) / ((LeanBridges.Counting.factorial (k + 1) : ℚ) * ((k : ℚ) + 1 + 1)) := by
            have e_w : (LeanBridges.Counting.factorial (k + 1 + 1) : ℚ) = (LeanBridges.Counting.factorial (k + 1) : ℚ) * ((k : ℚ) + 1 + 1) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_4; push_cast at h; linear_combination (norm := parley_norm) h
            (have h := congrArg (fun t : ℚ => 1 - 1 / (LeanBridges.Counting.factorial (k + 1) : ℚ) + ((k : ℚ) + 1) / t) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 1 - 1 / ((LeanBridges.Counting.factorial (k + 1) : ℚ) * ((k : ℚ) + 1 + 1)) := by
            have hI : 1 - 1 / (LeanBridges.Counting.factorial (k + 1) : ℚ) + ((k : ℚ) + 1) / ((LeanBridges.Counting.factorial (k + 1) : ℚ) * ((k : ℚ) + 1 + 1)) = 1 - 1 / ((LeanBridges.Counting.factorial (k + 1) : ℚ) * ((k : ℚ) + 1 + 1)) := by parley_instance_real ((Parley.Proofs.Hammack.SumOfFactorialQuotients.FactorialQuotientStep.factorial_quotient_step (c := k + 1) (add_pos (lt_of_lt_of_le zero_lt_one hK) (by norm_num)) (F := (LeanBridges.Counting.factorial (k + 1) : ℝ)) (by exact_mod_cast s2_5.ne')))
            exact hI
        _ = 1 - 1 / (LeanBridges.Counting.factorial (k + 1 + 1) : ℚ) := by
            have e_w : (LeanBridges.Counting.factorial (k + 1) : ℚ) * ((k : ℚ) + 1 + 1) = (LeanBridges.Counting.factorial (k + 1 + 1) : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) s2_4.symm; push_cast at h; linear_combination (norm := parley_norm) h
            (have h := congrArg (fun t : ℚ => 1 - 1 / t) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 3. instantiate k := n in line 2
  exact (s2 n hH1)

end Parley.Proofs.Hammack.SumOfFactorialQuotients.SumOfFactorialQuotients
