module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import PowerTactics
public import SetTactics
public import Tactics
public import WholeTactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus

/-! Written from proofs/wiedijk/leibniz.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Leibniz.PowerIntegral

theorem power_integral (m : ℤ) (hH1 : 0 ≤ m) :
    (∫ t in 0..1, (t ^ m.toNat : ℝ)) = 1 / ((m : ℝ) + 1) := by
  set p : ℝ → ℝ := fun x : ℝ => x ^ m.toNat with hD1
  set q : ℝ → ℝ := fun x : ℝ => x ^ (m + 1).toNat with hD2
  set F : ℝ → ℝ := fun x : ℝ => 1 / ((m : ℝ) + 1) * q x with hD3
  -- 1. mun:nat0-successor k := m
  have s1 : 0 < m + 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat0_successor (k := m) hH1)
  -- 2. mun:interval-real
  have s2 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))
  -- 3. D1
  have s3 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), p x = x ^ m.toNat := by simp (disch := omega) only [hD1, implies_true]
  -- 4. D2
  have s4 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), q x = x ^ (m + 1).toNat := by simp (disch := omega) only [hD2, implies_true]
  -- 5. D3
  have s5 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), F x = 1 / ((m : ℝ) + 1) * q x := by simp (disch := omega) only [hD3, implies_true]
  -- 6. membership, from D1
  have s6 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 7. membership, from D2
  have s7 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 8. membership, from D2, D3
  have r85_1 : m + 1 ≠ 0 := by parley_set_side
  have s8 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; parley_set_side
  -- 9. mun:function-into, from 6
  have s9 : Set.MapsTo p (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := p) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  -- 10. mun:function-into, from 7
  have s10 : Set.MapsTo q (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := q) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  -- 11. mun:function-into, from 8
  have s11 : Set.MapsTo F (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  -- 12. thm:continuous-power D := [0, 1], n := m, from 2, 3, 9
  have s12 : ContinuousOn p (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := p) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s2 (n := m) hH1 s3)
  -- 13. thm:continuous-power D := [0, 1], n := m + 1, from 2, 4, 10
  have s13 : ContinuousOn q (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := q) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s2 (n := m + 1) (by parley_set_side) s4)
  -- 14. thm:continuous-scaled D := [0, 1], c := 1/(m + 1), f := q, from 2, 5, 10, 11, 13
  have r107_1 : m + 1 ≠ 0 := by parley_set_side
  have s14 : ContinuousOn F (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_scaled (F := F) (f := q) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s2 (c := 1 / ((m : ℝ) + 1)) s5 s13)
  -- 15. thm:derivative-power D := [0, 1], U := (0, 1), n := m, from 2, 4, 10
  have r111_1 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r111_2 : IsOpen (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ)))
  have s15 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ q x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_power_1 (g := q) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s2 r111_1 r111_2 (n := m) hH1 s4)
  -- 16. thm:derivative-power D := [0, 1], U := (0, 1), n := m, from 2, 4, 10
  have r116_1 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r116_2 : IsOpen (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ)))
  have s16 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (deriv q) x = ((m : ℝ) + 1) * x ^ m.toNat := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_power_2 (g := q) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s2 r116_1 r116_2 (n := m) hH1 s4)
  -- 17. thm:derivative-scaled D := [0, 1], U := (0, 1), c := 1/(m + 1), f := q, from 2, 5, 10, 11, 15
  have r121_1 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r121_2 : m + 1 ≠ 0 := by parley_set_side
  have s17 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ F x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_1 (F := F) (f := q) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s2 r121_1 (c := 1 / ((m : ℝ) + 1)) s5 s15)
  -- 18. thm:derivative-scaled D := [0, 1], U := (0, 1), c := 1/(m + 1), f := q, from 2, 5, 10, 11, 15
  have r126_1 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r126_2 : m + 1 ≠ 0 := by parley_set_side
  have s18 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (deriv F) x = 1 / ((m : ℝ) + 1) * (deriv q) x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_2 (F := F) (f := q) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s2 r126_1 (c := 1 / ((m : ℝ) + 1)) s5 s15)
  -- 19. proof
  have s19 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (deriv F) x = p x := by
    intro x hK1
    -- 19.1. mun:in-subset, from K1
    have r135_1 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))
    have s19_1 : x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (u := x) r135_1 hK1)
    -- 19.2. D1, from 19.1
    have s19_2 : p x = x ^ m.toNat := by simp (disch := omega) only [hD1]
    -- 19.3. calculation
    have r142_1 : m + 1 ≠ 0 := by parley_set_side
    calc (deriv F) x = 1 / ((m : ℝ) + 1) * (deriv q) x := by exact (s18 x hK1)
      _ = 1 / ((m : ℝ) + 1) * (((m : ℝ) + 1) * x ^ m.toNat) := by (have h := congrArg (fun t : ℝ => 1 / ((m : ℝ) + 1) * t) (s16 x hK1); push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = x ^ m.toNat := by parley_ring
      _ = p x := by exact s19_2
  -- 20. arithmetic
  have s20 : (0 : ℤ) < 1 := by parley_arith
  -- 21. def:interval a := 0, b := 1, x := 0
  have r153_1 : (0 : ℤ) ≤ 0 := by parley_arith
  have r153_2 : (0 : ℤ) ≤ 1 := by parley_arith
  have s21 : (0 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := (0 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr ⟨⟨by parley_set_side, by parley_set_side⟩, by parley_set_side⟩
  -- 22. def:interval a := 0, b := 1, x := 1
  have r158_1 : (0 : ℤ) ≤ 1 := by parley_arith
  have r158_2 : (1 : ℤ) ≤ 1 := by parley_arith
  have s22 : (1 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := (1 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr ⟨⟨by parley_set_side, by parley_set_side⟩, by parley_set_side⟩
  -- 23. D2, from 22
  have s23 : q 1 = 1 ^ (m + 1).toNat := by simp (disch := omega) only [hD2]
  -- 24. mun:one-power m := m + 1
  have s24 : (1 ^ (m + 1).toNat : ℤ) = 1 := by (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := m + 1)); simp only [parley_zpow_toNat (n := m + 1) (h := le_of_lt s1)] at h ⊢; exact_mod_cast h)
  -- 25. D2, from 21
  have s25 : q 0 = 0 ^ (m + 1).toNat := by simp (disch := omega) only [hD2]
  -- 26. mun:zero-power n := m + 1, from 1
  have s26 : (0 ^ (m + 1).toNat : ℤ) = 0 := by exact (Parley.Items.Stdlib.Numbers.mun_zero_power (n := m + 1) s1)
  -- 27. D3, from 22
  have s27 : F 1 = 1 / ((m : ℝ) + 1) * q 1 := by simp (disch := omega) only [hD3]
  -- 28. D3, from 21
  have s28 : F 0 = 1 / ((m : ℝ) + 1) * q 0 := by simp (disch := omega) only [hD3]
  -- 29. calculation
  have s29 : F 1 = 1 / ((m : ℝ) + 1) * 1 := by
    calc F 1 = 1 / ((m : ℝ) + 1) * q 1 := by exact s27
      _ = 1 / ((m : ℝ) + 1) * 1 ^ (m + 1).toNat := by (have h := congrArg (fun t : ℝ => 1 / ((m : ℝ) + 1) * t) s23; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 1 / ((m : ℝ) + 1) * 1 := by
          have e_w : (1 ^ (m + 1).toNat : ℚ) = 1 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s24; push_cast at h; linear_combination (norm := parley_norm) h
          (have h := congrArg (fun t : ℚ => 1 / ((m : ℚ) + 1) * t) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 30. calculation
  have s30 : F 0 = 1 / ((m : ℝ) + 1) * 0 := by
    calc F 0 = 1 / ((m : ℝ) + 1) * q 0 := by exact s28
      _ = 1 / ((m : ℝ) + 1) * 0 ^ (m + 1).toNat := by (have h := congrArg (fun t : ℝ => 1 / ((m : ℝ) + 1) * t) s25; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 1 / ((m : ℝ) + 1) * 0 := by
          have e_w : (0 ^ (m + 1).toNat : ℚ) = 0 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s26; push_cast at h; linear_combination (norm := parley_norm) h
          (have h := congrArg (fun t : ℚ => 1 / ((m : ℚ) + 1) * t) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 31. calculation
  have r193_1 : m + 1 ≠ 0 := by parley_set_side
  calc (∫ t in 0..1, (t ^ m.toNat : ℝ)) = (∫ t in 0..1, (p t : ℝ)) := by simp (disch := omega) only [hD1]
    _ = F 1 - F 0 := by exact (Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus.fundamental_calculus (a := (0 : ℝ)) (b := (1 : ℝ)) (by parley_set_side) (f := p) (by parley_set_side) s12 (F := F) (by parley_set_side) s14 s17 s19)
    _ = 1 / ((m : ℝ) + 1) * 1 - F 0 := by (have h := congrArg (fun t : ℝ => t - F 0) s29; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = 1 / ((m : ℝ) + 1) * 1 - 1 / ((m : ℝ) + 1) * 0 := by (have h := congrArg (fun t : ℝ => 1 / ((m : ℝ) + 1) * 1 - t) s30; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = 1 / ((m : ℝ) + 1) := by parley_ring

end Parley.Proofs.Wiedijk.Leibniz.PowerIntegral
