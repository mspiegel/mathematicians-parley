module

public import AlgebraTactics
public import Functions
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/geometric-series.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.GeometricSeries.GeometricSum

theorem geometric_sum (a : ℝ) (hH2 : a ≠ 1) (n : ℤ) (hH3 : 0 ≤ n) :
    (∑ j ∈ Finset.Icc (0 : ℤ) n, (a ^ j.toNat : ℝ)) = (1 - a ^ (n + 1).toNat) / (1 - a) := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (∑ j ∈ Finset.Icc (0 : ℤ) k, (a ^ j.toNat : ℝ)) = (1 - a ^ (k + 1).toNat) / (1 - a) := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j.toNat : ℝ)) = 1 := by
        calc (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j.toNat : ℝ)) = (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j.toNat : ℝ)) := by parley_side
          _ = a ^ 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j.toNat)) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j.toNat)) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j.toNat)) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j.toNat)) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j.toNat)) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j.toNat)) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j.toNat)) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j.toNat)) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j.toNat)) (a := (0 : ℤ))); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j.toNat)) (a := (0 : ℤ))); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j.toNat)) (a := (0 : ℤ))); parley_side)
          _ = 1 := by parley_ring
      -- 1.2. calculation
      have r26_1 : 1 - a ≠ 0 := by intro h; exact hH2 (by linear_combination (norm := parley_norm) (-1) * h)
      have s1_2 : (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j.toNat : ℝ)) = (1 - a) / (1 - a) := by
        calc (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j.toNat : ℝ)) = 1 := by first | parley_side | parley_line_toNat s1_1
          _ = (1 - a) / (1 - a) := by parley_ring
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.3. calculation
      have s1_3 : (∑ j ∈ Finset.Icc (0 : ℤ) (k + 1), (a ^ j.toNat : ℝ)) = (∑ j ∈ Finset.Icc (0 : ℤ) k, (a ^ j.toNat : ℝ)) + a ^ (k + 1).toNat := by
        calc (∑ j ∈ Finset.Icc (0 : ℤ) (k + 1), (a ^ j.toNat : ℝ)) = (∑ j ∈ Finset.Icc (0 : ℤ) (k + 1), (a ^ j.toNat : ℝ)) := by parley_side
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) k, (a ^ j.toNat : ℝ)) + a ^ (k + 1).toNat := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j.toNat)) (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j.toNat)) (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j.toNat)) (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j.toNat)) (n := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j.toNat)) (n := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j.toNat)) (n := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j.toNat)) (n := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j.toNat)) (n := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j.toNat)) (n := k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j.toNat)) (n := k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j.toNat)) (n := k) (by parley_side)); parley_side)
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) k, (a ^ j.toNat : ℝ)) + a ^ (k + 1).toNat := by parley_side
      -- 1.4. mun:exponent-step m := k + 1
      have s1_4 : a ^ (k + 1 + 1).toNat = a ^ (k + 1).toNat * a := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1) (by parley_side)); parley_side)
      -- 1.5. calculation
      have r45_1 : 1 - a ≠ 0 := by intro h; exact hH2 (by linear_combination (norm := parley_norm) (-1) * h)
      have s1_5 : (∑ j ∈ Finset.Icc (0 : ℤ) (k + 1), (a ^ j.toNat : ℝ)) = (1 - a ^ (k + 1 + 1).toNat) / (1 - a) := by
        calc (∑ j ∈ Finset.Icc (0 : ℤ) (k + 1), (a ^ j.toNat : ℝ)) = (∑ j ∈ Finset.Icc (0 : ℤ) k, (a ^ j.toNat : ℝ)) + a ^ (k + 1).toNat := by first | parley_side | parley_line_toNat s1_3
          _ = (1 - a ^ (k + 1).toNat) / (1 - a) + a ^ (k + 1).toNat := by parley_subst hIH
          _ = (1 - a ^ (k + 1).toNat * a) / (1 - a) := by parley_ring
          _ = (1 - a ^ (k + 1 + 1).toNat) / (1 - a) := by parley_subst s1_4
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : (∑ j ∈ Finset.Icc (0 : ℤ) n, (a ^ j.toNat : ℝ)) = (1 - a ^ (n + 1).toNat) / (1 - a) := by first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (s1 n (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Wiedijk.GeometricSeries.GeometricSum
