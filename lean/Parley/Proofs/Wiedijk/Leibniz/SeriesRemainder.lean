module

public import AlgebraTactics
public import Functions
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
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
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Leibniz.IntegralBounds
public import Parley.Proofs.Wiedijk.Leibniz.IntegralOfArctanDerivative
public import Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence

/-! Written from proofs/wiedijk/leibniz.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Leibniz.SeriesRemainder

theorem series_remainder :
    (∀ n : ℤ, 0 ≤ n → Real.pi / 4 - (∑ j ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ j.toNat / (2 * (j : ℝ) + 1) : ℝ)) = (-1) ^ (n + 1).toNat * (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ))) := by
  -- 1. membership
  have r682_1 : ∀ j : ℤ, 0 ≤ j → 0 < 2 * j + 1 := by intro j h_j; (exact (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := 2 * j) (by parley_side)))
  -- 2. induction on n starting at 0
  intro n h_n
  replace h_n : 0 ≤ n := by omega
  induction n, h_n using LeanBridges.Functions.le_induction with
  | base =>
    -- 2.1. calculation
    have s2_1 : (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((-1) ^ j.toNat / (2 * (j : ℚ) + 1) : ℚ)) = 1 := by
      calc (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((-1) ^ j.toNat / (2 * (j : ℚ) + 1) : ℚ)) = (-1) ^ 0 / (2 * 0 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (a := (0 : ℤ))); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (a := (0 : ℤ))); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (a := (0 : ℤ))); parley_side)
        _ = 1 := by norm_num
    -- 2.2. thm:integral-recurrence n := 0
    have s2_2 : (∫ t in 0..1, (t ^ (2 * 1) / (1 + t ^ 2) : ℝ)) = 1 / (2 * 0 + 1) - (∫ t in 0..1, (t ^ (2 * 0) / (1 + t ^ 2) : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence.integral_recurrence (n := (0 : ℤ)) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence.integral_recurrence (n := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence.integral_recurrence (n := (0 : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence.integral_recurrence (n := (0 : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence.integral_recurrence (n := (0 : ℤ)) (by parley_side))).symm | (have h := (Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence.integral_recurrence (n := (0 : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence.integral_recurrence (n := (0 : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence.integral_recurrence (n := (0 : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence.integral_recurrence (n := (0 : ℤ)) (by parley_side)); parley_side)
    -- 2.3. substitute
    have s2_3 : (∫ t in 0..1, (t ^ (2 * 1) / (1 + t ^ 2) : ℝ)) = 1 / (2 * 0 + 1) - Real.pi / 4 := by
      have c1 : (∫ t in 0..1, (t ^ (2 * 0) / (1 + t ^ 2) : ℝ)) = Real.pi / 4 := by exact Parley.Proofs.Wiedijk.Leibniz.IntegralOfArctanDerivative.integral_of_arctan_derivative
      have row1 : (∫ t in 0..1, (t ^ (2 * 1) / (1 + t ^ 2) : ℝ)) = 1 / (2 * 0 + 1) - Real.pi / 4 := by parley_subst_at c1 s2_2
      exact row1
    -- 2.4. calculation
    have s2_4 : Real.pi / 4 - (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((-1) ^ j.toNat / (2 * (j : ℝ) + 1) : ℝ)) = -1 * (∫ t in 0..1, (t ^ (2 * 1) / (1 + t ^ 2) : ℝ)) := by
      calc Real.pi / 4 - (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((-1) ^ j.toNat / (2 * (j : ℝ) + 1) : ℝ)) = Real.pi / 4 - 1 := by
            have s2_1_w : (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((-1) ^ j.toNat / (2 * (j : ℝ) + 1) : ℝ)) = 1 := by have h := congrArg (fun x : ℚ => (x : ℝ)) s2_1; push_cast at h; linear_combination (norm := parley_norm) h
            first | parley_subst s2_1_w | parley_subst s2_1
        _ = -1 * (∫ t in 0..1, (t ^ (2 * 1) / (1 + t ^ 2) : ℝ)) := by linear_combination (norm := parley_norm) ((16) / ((4) * (4))) * s2_3
    simpa only [zero_add, pow_one, Int.reduceAdd, Int.reduceMul, Int.reduceToNat, Nat.reduceAdd, Nat.reduceMul] using s2_4
  | succ n hK hIH =>
    -- 2.5. mun:sum-last, from 1
    have s2_5 : (∑ j ∈ Finset.Icc (0 : ℤ) (n + 1), ((-1) ^ j.toNat / (2 * (j : ℚ) + 1) : ℚ)) = (∑ j ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ j.toNat / (2 * (j : ℚ) + 1) : ℚ)) + (-1) ^ (n + 1).toNat / (2 * ((n : ℚ) + 1) + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (n := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (n := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (n := n) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (n := n) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => (-1) ^ j.toNat / (2 * (j : ℚ) + 1))) (n := n) (by parley_side)); parley_side)
    -- 2.6. thm:integral-recurrence n := n + 1
    have s2_6 : (∫ t in 0..1, (t ^ (2 * (n + 1 + 1)).toNat / (1 + t ^ 2) : ℝ)) = 1 / (2 * ((n : ℝ) + 1) + 1) - (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) := by simpa using (Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence.integral_recurrence (n := n + 1) (by parley_side))
    -- 2.7. mun:exponent-step a := −1, m := n + 1
    have s2_7 : ((-1) ^ (n + 1 + 1).toNat : ℤ) = (-1) ^ (n + 1).toNat * -1 := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := n + 1) (by parley_side))
    -- 2.8. calculation
    have r721_2 : 0 < 2 * (n + 1) + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := 2 * (n + 1)) (by parley_side))
    calc Real.pi / 4 - (∑ j ∈ Finset.Icc (0 : ℤ) (n + 1), ((-1) ^ j.toNat / (2 * (j : ℝ) + 1) : ℝ)) = Real.pi / 4 - ((∑ j ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ j.toNat / (2 * (j : ℝ) + 1) : ℝ)) + (-1) ^ (n + 1).toNat / (2 * ((n : ℝ) + 1) + 1)) := by
          have s2_5_w : (∑ j ∈ Finset.Icc (0 : ℤ) (n + 1), ((-1) ^ j.toNat / (2 * (j : ℝ) + 1) : ℝ)) = (∑ j ∈ Finset.Icc (0 : ℤ) n, ((-1) ^ j.toNat / (2 * (j : ℝ) + 1) : ℝ)) + (-1) ^ (n + 1).toNat / (2 * ((n : ℝ) + 1) + 1) := by have h := congrArg (fun x : ℚ => (x : ℝ)) s2_5; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s2_5_w | parley_subst s2_5
      _ = (-1) ^ (n + 1).toNat * (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) - (-1) ^ (n + 1).toNat / (2 * ((n : ℝ) + 1) + 1) := by linear_combination (norm := parley_field) ((4) / ((4))) * hIH
      _ = (-1) ^ (n + 1).toNat * -1 * (∫ t in 0..1, (t ^ (2 * (n + 1 + 1)).toNat / (1 + t ^ 2) : ℝ)) := by linear_combination (norm := parley_field) ((-1) ^ (n + 1).toNat) * s2_6
      _ = (-1) ^ (n + 1 + 1).toNat * (∫ t in 0..1, (t ^ (2 * (n + 1 + 1)).toNat / (1 + t ^ 2) : ℝ)) := by
          have s2_7_w : ((-1) ^ (n + 1 + 1).toNat : ℝ) = (-1) ^ (n + 1).toNat * -1 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s2_7; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s2_7_w | parley_subst s2_7

end Parley.Proofs.Wiedijk.Leibniz.SeriesRemainder
