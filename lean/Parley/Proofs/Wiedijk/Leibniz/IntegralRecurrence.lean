module

public import AlgebraTactics
public import ArithTactics
public import InstanceTactics
public import NormTactics
public import OrderTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous
public import Parley.Proofs.Wiedijk.Leibniz.PowerIntegral

/-! Written from proofs/wiedijk/leibniz.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence

set_option maxHeartbeats 600000 in
theorem integral_recurrence (n : ℤ) (hH1 : 0 ≤ n) :
    (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) = 1 / (2 * (n : ℝ) + 1) - (∫ t in 0..1, (t ^ (2 * n).toNat / (1 + t ^ 2) : ℝ)) := by
  set f : ℝ → ℝ := fun x : ℝ => x ^ (2 * n).toNat with hD1
  set g : ℝ → ℝ := fun x : ℝ => x ^ (2 * n).toNat / (1 + x ^ 2) with hD2
  set h : ℝ → ℝ := fun x : ℝ => x ^ (2 * (n + 1)).toNat / (1 + x ^ 2) with hD3
  -- 1. proof
  have s1 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), h x = f x - g x := by
    intro x hK1
    -- 1.1. algebra
    have s1_1 : 2 * (n + 1) = 2 * n + 2 := by parley_ring
    -- 1.2. calculation
    have s1_2 : x ^ (2 * (n + 1)).toNat = x ^ (2 * n).toNat * x ^ 2 := by
      calc x ^ (2 * (n + 1)).toNat = x ^ (2 * n + 2).toNat := by
            have s1_1_w : 2 * ((n : ℝ) + 1) = 2 * (n : ℝ) + 2 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s1_1; push_cast at h; linear_combination (norm := parley_norm) h
            first | parley_subst s1_1_w | parley_subst s1_1
        _ = x ^ (2 * n).toNat * x ^ 2 := by
            have hI : x ^ (2 * n + 2).toNat = x ^ (2 * n).toNat * x ^ 2 := by parley_instance ((Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := x) (m := 2 * n) (by parley_set_side) (n := (2 : ℤ)) (by parley_set_side)))
            exact hI
    -- 1.3. mun:square-nonneg
    have s1_3 : x ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
    -- 1.4. inequalities, from 1.3
    have s1_4 : 1 + x ^ 2 > 0 := by parley_order
    -- 1.5. D3, from K1
    have s1_5 : h x = x ^ (2 * (n + 1)).toNat / (1 + x ^ 2) := by simp (disch := omega) only [hD3]
    -- 1.6. calculation
    have r461_1 : 1 + x ^ 2 ≠ 0 := by parley_set_side
    calc h x = x ^ (2 * (n + 1)).toNat / (1 + x ^ 2) := by exact s1_5
      _ = x ^ (2 * n).toNat - x ^ (2 * n).toNat / (1 + x ^ 2) := by linear_combination (norm := parley_field) ((1) / ((x ^ 2 + 1))) * s1_2
      _ = f x - g x := by parley_ring
  -- 2. D1
  have s2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), f x = x ^ (2 * n).toNat := by simp (disch := omega) only [hD1, implies_true]
  -- 3. D2
  have s3 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), g x = x ^ (2 * n).toNat / (1 + x ^ 2) := by simp (disch := omega) only [hD2, implies_true]
  -- 4. mun:interval-real
  have s4 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))
  -- 5. membership, from D1
  have s5 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 6. membership, from D2
  have r480_1 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), x ^ 2 ≥ 0 := by intro x h_x; (exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)))
  have r480_2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), 1 + x ^ 2 > 0 := by intro x h_x; (parley_order)
  have s6 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 7. membership, from D3
  have r485_1 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), x ^ 2 ≥ 0 := by intro x h_x; (exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)))
  have r485_2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), 1 + x ^ 2 > 0 := by intro x h_x; (parley_order)
  have s7 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 8. mun:function-into, from 5
  have s8 : Set.MapsTo f (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := f) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  -- 9. mun:function-into, from 6
  have s9 : Set.MapsTo g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  -- 10. mun:function-into, from 7
  have s10 : Set.MapsTo h (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  -- 11. thm:continuous-power D := [0, 1], n := 2n, from 2, 4, 8
  have s11 : ContinuousOn f (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := f) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s4 (n := 2 * n) (by parley_set_side) s2)
  -- 12. thm:integrand-continuous, from 3, 9
  have s12 : ContinuousOn g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := n) (by parley_set_side) (g := g) (by parley_set_side) (by parley_set_side))
  -- 13. arithmetic
  have s13 : (0 : ℤ) < 1 := by parley_arith
  -- 14. D1
  have s14 : (∫ t in 0..1, (f t : ℝ)) = (∫ t in 0..1, (t ^ (2 * n).toNat : ℝ)) := by simp (disch := omega) only [hD1]
  -- 15. calculation
  have s15 : (∫ t in 0..1, (f t : ℝ)) = 1 / (2 * (n : ℝ) + 1) := by
    calc (∫ t in 0..1, (f t : ℝ)) = (∫ t in 0..1, (t ^ (2 * n).toNat : ℝ)) := by exact s14
      _ = 1 / (2 * (n : ℝ) + 1) := by
          have hI : (∫ t in 0..1, (t ^ (2 * n).toNat : ℝ)) = 1 / (2 * (n : ℝ) + 1) := by parley_instance ((Parley.Proofs.Wiedijk.Leibniz.PowerIntegral.power_integral (m := 2 * n) (by parley_set_side)))
          exact hI
  -- 16. D0, from D3
  have s16 : (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (h t : ℝ)) := by simp (disch := omega) only [hD3]
  -- 17. D0, from D2
  have s17 : (∫ t in 0..1, (t ^ (2 * n).toNat / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (g t : ℝ)) := by simp (disch := omega) only [hD2]
  -- 18. calculation
  calc (∫ t in 0..1, (t ^ (2 * (n + 1)).toNat / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (h t : ℝ)) := by exact s16
    _ = (∫ t in 0..1, (f t : ℝ)) - (∫ t in 0..1, (g t : ℝ)) := by exact (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := f) (g := g) (h := h) (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (by parley_set_side))
    _ = 1 / (2 * (n : ℝ) + 1) - (∫ t in 0..1, (g t : ℝ)) := by parley_subst s15
    _ = 1 / (2 * (n : ℝ) + 1) - (∫ t in 0..1, (t ^ (2 * n).toNat / (1 + t ^ 2) : ℝ)) := by parley_subst s17

end Parley.Proofs.Wiedijk.Leibniz.IntegralRecurrence
