module

public import AlgebraTactics
public import Functions
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-first-naturals.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfFirstNaturals.SumOfFirstNaturals

theorem sum_of_first_naturals (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℚ) : ℚ)) = ((n : ℚ) ^ 2 + (n : ℚ)) / 2 := by
  set S : ℤ → ℤ := fun m => ∑ j ∈ Finset.Icc (1 : ℤ) m, (j : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → (S k : ℚ) = ((k : ℚ) ^ 2 + (k : ℚ)) / 2 := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : (S 1 : ℚ) = (1 ^ 2 + 1) / 2 := by
        calc (S 1 : ℚ) = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), ((j : ℚ) : ℚ)) := by simp (disch := omega) only [hD1]; push_cast; norm_num
          _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ))) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ))) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ))) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ))) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ))) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ))) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ))) (a := (1 : ℤ))); parley_side)
          _ = (1 ^ 2 + 1) / 2 := by norm_num
      first | exact_mod_cast s1_1 | (have h := s1_1; push_cast at h ⊢; exact h) | simpa using s1_1
    | succ k hK hIH =>
      -- 1.2. calculation
      have r27_1 : k ≥ 1 := by parley_side
      have s1_2 : S (k + 1) = S k + (k + 1) := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (j : ℤ)) := by simp (disch := omega) only [hD1]
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) k, (j : ℤ)) + (k + 1) := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j)) (a := (1 : ℤ)) (n := k) r27_1)
          _ = S k + (k + 1) := by simp (disch := omega) only [hD1]
      -- 1.3. calculation
      have s1_3 : (S (k + 1) : ℚ) = (((k : ℚ) + 1) ^ 2 + ((k : ℚ) + 1)) / 2 := by
        calc (S (k + 1) : ℚ) = (S k : ℚ) + ((k : ℚ) + 1) := by parley_side
          _ = ((k : ℚ) ^ 2 + (k : ℚ)) / 2 + ((k : ℚ) + 1) := by parley_subst hIH
          _ = (((k : ℚ) + 1) ^ 2 + ((k : ℚ) + 1)) / 2 := by parley_ring
      first | exact_mod_cast s1_3 | (have h := s1_3; push_cast at h ⊢; exact h) | simpa using s1_3
  -- 2. calculation
  calc (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℚ) : ℚ)) = (S n : ℚ) := by simp (disch := omega) only [hD1]; push_cast; norm_num
    _ = ((n : ℚ) ^ 2 + (n : ℚ)) / 2 := by exact (s1 n (by parley_side))

end Parley.Proofs.Hammack.SumOfFirstNaturals.SumOfFirstNaturals
