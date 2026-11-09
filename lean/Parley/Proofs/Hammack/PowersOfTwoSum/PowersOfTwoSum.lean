module

public import AlgebraTactics
public import Functions
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/powers-of-two-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PowersOfTwoSum.PowersOfTwoSum

theorem powers_of_two_sum (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (2 ^ k.toNat : ℤ)) = 2 ^ (n + 1).toNat - 2 := by
  set S : ℤ → ℤ := fun m : ℤ => ∑ j ∈ Finset.Icc (1 : ℤ) m, (2 ^ j.toNat : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → S k = 2 ^ (k + 1).toNat - 2 := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      calc S 1 = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (2 ^ j.toNat : ℤ)) := by simp (disch := omega) only [hD1]
        _ = 2 ^ 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ))); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ))); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ))); parley_side)
        _ = 2 ^ (1 + 1) - 2 := by norm_num
    | succ k hK hIH =>
      -- 1.2. calculation
      have r28_1 : k ≥ 1 := by parley_side
      have s1_2 : S (k + 1) = S k + 2 ^ (k + 1).toNat := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (2 ^ j.toNat : ℤ)) := by simp (disch := omega) only [hD1]
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) k, (2 ^ j.toNat : ℤ)) + 2 ^ (k + 1).toNat := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ)) (n := k) r28_1) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ)) (n := k) r28_1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ)) (n := k) r28_1); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ)) (n := k) r28_1) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ)) (n := k) r28_1)).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ)) (n := k) r28_1); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ)) (n := k) r28_1); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ)) (n := k) r28_1); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ)) (n := k) r28_1); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ)) (n := k) r28_1); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ)) (n := k) r28_1); parley_side)
          _ = S k + 2 ^ (k + 1).toNat := by simp (disch := omega) only [hD1]
      -- 1.3. mun:exponent-step m := k + 1
      have s1_3 : (2 ^ (k + 1 + 1).toNat : ℤ) = 2 ^ (k + 1).toNat * 2 := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side))
      -- 1.4. calculation
      calc S (k + 1) = S k + 2 ^ (k + 1).toNat := by first | parley_side | parley_line_toNat s1_2
        _ = 2 ^ (k + 1).toNat - 2 + 2 ^ (k + 1).toNat := by parley_subst hIH
        _ = 2 ^ (k + 1).toNat * 2 - 2 := by parley_ring
        _ = 2 ^ (k + 1 + 1).toNat - 2 := by parley_subst s1_3
  -- 2. calculation
  calc (∑ k ∈ Finset.Icc (1 : ℤ) n, (2 ^ k.toNat : ℤ)) = S n := by simp (disch := omega) only [hD1]
    _ = 2 ^ (n + 1).toNat - 2 := by exact (s1 n (by parley_side))

end Parley.Proofs.Hammack.PowersOfTwoSum.PowersOfTwoSum
