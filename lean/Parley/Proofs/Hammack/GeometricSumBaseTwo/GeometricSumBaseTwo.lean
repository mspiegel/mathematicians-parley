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

/-! Written from proofs/hammack/geometric-sum-base-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GeometricSumBaseTwo.GeometricSumBaseTwo

theorem geometric_sum_base_two (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (0 : ℤ) n, (2 ^ k.toNat : ℤ)) = 2 ^ (n + 1).toNat - 1 := by
  set S : ℤ → ℤ := fun m => ∑ j ∈ Finset.Icc (0 : ℤ) m, (2 ^ j.toNat : ℤ) with hD1
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → S k = 2 ^ (k + 1).toNat - 1 := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : S 0 = 2 ^ 1 - 1 := by
        calc S 0 = (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (2 ^ j.toNat : ℤ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side | parley_line_toNat hD1
          _ = 2 ^ 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ))); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ))); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ))); parley_side)
          _ = 2 ^ 1 - 1 := by norm_num
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. calculation
      have r28_1 : k ≥ 0 := by parley_side
      have s1_2 : S (k + 1) = S k + 2 ^ (k + 1).toNat := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (0 : ℤ) (k + 1), (2 ^ j.toNat : ℤ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side | parley_line_toNat hD1
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) k, (2 ^ j.toNat : ℤ)) + 2 ^ (k + 1).toNat := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ)) (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ)) (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ)) (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ)) (n := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ)) (n := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ)) (n := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ)) (n := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ)) (n := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ)) (n := k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ)) (n := k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ)) (n := k) (by parley_side)); parley_side)
          _ = S k + 2 ^ (k + 1).toNat := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side | parley_line_toNat hD1
      -- 1.3. mun:exponent-step a := 2, m := k + 1
      have s1_3 : (2 ^ (k + 1 + 1).toNat : ℤ) = 2 ^ (k + 1).toNat * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side)); parley_side)
      -- 1.4. calculation
      have s1_4 : S (k + 1) = 2 ^ (k + 1 + 1).toNat - 1 := by
        calc S (k + 1) = S k + 2 ^ (k + 1).toNat := by first | parley_side | parley_line_toNat s1_2
          _ = 2 ^ (k + 1).toNat - 1 + 2 ^ (k + 1).toNat := by parley_subst hIH
          _ = 2 ^ (k + 1).toNat * 2 - 1 := by parley_ring
          _ = 2 ^ (k + 1 + 1).toNat - 1 := by parley_subst s1_3
      all_goals parley_side
  -- 2. calculation
  have s2 : (∑ k ∈ Finset.Icc (0 : ℤ) n, (2 ^ k.toNat : ℤ)) = 2 ^ (n + 1).toNat - 1 := by
    calc (∑ k ∈ Finset.Icc (0 : ℤ) n, (2 ^ k.toNat : ℤ)) = S n := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side | parley_line_toNat hD1
      _ = 2 ^ (n + 1).toNat - 1 := by first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s1 n (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.GeometricSumBaseTwo.GeometricSumBaseTwo
