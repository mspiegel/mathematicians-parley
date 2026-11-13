module

public import AlgebraTactics
public import ArithTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Field.Basic
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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
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
public import Parley.Items.Stdlib.Trigonometry
public import Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus
public import Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous

/-! Written from proofs/wiedijk/leibniz.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Leibniz.IntegralOfArctanDerivative

theorem integral_of_arctan_derivative :
    (∫ t in 0..1, (t ^ (2 * 0) / (1 + t ^ 2) : ℝ)) = Real.pi / 4 := by
  set g : ℝ → ℝ := fun x : ℝ => x ^ (2 * 0) / (1 + x ^ 2) with hD1
  set F : ℝ → ℝ := fun x : ℝ => Real.arctan x with hD2
  -- 1. mun:interval-real
  have s1 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))
  -- 2. D1
  have s2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), g x = x ^ (2 * 0) / (1 + x ^ 2) := by simp (disch := omega) only [hD1, implies_true]
  -- 3. D2
  have s3 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), F x = Real.arctan x := by simp (disch := omega) only [hD2, implies_true]
  -- 4. mun:arctan-real, from D2
  have s4 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by intro x h_x; (trivial)
  -- 5. mun:function-into, from 4
  have s5 : Set.MapsTo F (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 6. proof
  have s6 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), True := by
    intro x hK1
    -- 6.1. mun:square-nonneg
    have s6_1 : x ^ 2 ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
    -- 6.2. membership, from D1, K1
    have r339_1 : 1 + x ^ 2 > 0 := by linarith only [s6_1]
    exact trivial
  -- 7. mun:function-into, from 6
  have s7 : Set.MapsTo g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 8. thm:integrand-continuous n := 0, from 2, 7
  have s8 : ContinuousOn g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Proofs.Wiedijk.Leibniz.IntegrandContinuous.integrand_continuous (n := (0 : ℤ)) (by norm_num) (g := g) (Set.mapsTo_univ _ _) (by simpa only [Int.cast_zero, Int.reduceMul, Int.reduceToNat, Nat.reduceMul] using s2))
  -- 9. thm:continuous-arctan D := [0, 1], from 1, 3, 5
  have s9 : ContinuousOn F (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Trigonometry.thm_continuous_arctan (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 s3)
  -- 10. thm:derivative-arctan D := [0, 1], U := (0, 1), from 1, 3, 5
  have r353_1 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r353_2 : IsOpen (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ)))
  have s10 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ F x := by exact (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_1 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 r353_1 r353_2 s3)
  -- 11. thm:derivative-arctan D := [0, 1], U := (0, 1), from 1, 3, 5
  have r358_1 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r358_2 : IsOpen (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ)))
  have s11 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (deriv F) x = 1 / (1 + x ^ 2) := by exact (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := F) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) s1 r358_1 r358_2 s3)
  -- 12. proof
  have s12 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (deriv F) x = g x := by
    intro x hK2
    -- 12.1. mun:in-subset, from K2
    have r367_1 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))
    have s12_1 : x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (Y := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (u := x) r367_1 hK2)
    -- 12.2. calculation
    have s12_2 : x ^ (2 * 0) = 1 := by
      calc x ^ (2 * 0) = x ^ 0 := by norm_num
        _ = 1 := by parley_ring
    -- 12.3. D1, from 12.1
    have s12_3 : g x = x ^ (2 * 0) / (1 + x ^ 2) := by simp (disch := omega) only [hD1]
    -- 12.4. calculation
    calc (deriv F) x = 1 / (1 + x ^ 2) := (s11 x hK2)
      _ = x ^ (2 * 0) / (1 + x ^ 2) := by (have h := congrArg (fun t : ℝ => t / (1 + x ^ 2)) s12_2.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = g x := s12_3.symm
  -- 13. arithmetic
  have s13 : (0 : ℤ) < 1 := by parley_arith
  -- 14. def:interval a := 0, b := 1, x := 0
  have r388_1 : (0 : ℤ) ≤ 0 := by parley_arith
  have r388_2 : (0 : ℤ) ≤ 1 := by parley_arith
  have s14 : (0 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := (0 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr ⟨⟨by trivial, by norm_num⟩, by norm_num⟩
  -- 15. def:interval a := 0, b := 1, x := 1
  have r393_1 : (0 : ℤ) ≤ 1 := by parley_arith
  have r393_2 : (1 : ℤ) ≤ 1 := by parley_arith
  have s15 : (1 : ℝ) ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := (1 : ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))).mpr ⟨⟨by trivial, by norm_num⟩, by norm_num⟩
  -- 16. mun:arctan-values
  have s16a : Real.arctan (0 : ℝ) = 0 := by exact Parley.Items.Stdlib.Trigonometry.mun_arctan_values_1
  have s16b : Real.arctan (1 : ℝ) = Real.pi / 4 := by exact Parley.Items.Stdlib.Trigonometry.mun_arctan_values_2
  -- 17. D2, from 15
  have s17 : F 1 = Real.arctan (1 : ℝ) := by simp (disch := omega) only [hD2]
  -- 18. D2, from 14
  have s18 : F 0 = Real.arctan (0 : ℝ) := by simp (disch := omega) only [hD2]
  -- 19. calculation
  have s19 : F 1 = Real.pi / 4 := by
    calc F 1 = Real.arctan (1 : ℝ) := s17
      _ = Real.pi / 4 := s16b
  -- 20. calculation
  have s20 : F 0 = 0 := by
    calc F 0 = Real.arctan (0 : ℝ) := s18
      _ = 0 := s16a
  -- 21. D0, from D1
  have s21 : (∫ t in 0..1, (t ^ (2 * 0) / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (g t : ℝ)) := by simp (disch := omega) only [hD1]
  -- 22. calculation
  calc (∫ t in 0..1, (t ^ (2 * 0) / (1 + t ^ 2) : ℝ)) = (∫ t in 0..1, (g t : ℝ)) := s21
    _ = F 1 - F 0 := by exact (Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus.fundamental_calculus (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num) (f := g) (Set.mapsTo_univ _ _) s8 (F := F) (Set.mapsTo_univ _ _) s9 s10 s12)
    _ = Real.pi / 4 - F 0 := by (have h := congrArg (fun t : ℝ => t - F 0) s19; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Real.pi / 4 := by (have h := congrArg (fun t : ℝ => Real.pi / 4 - t) s20; push_cast [sub_zero] at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Wiedijk.Leibniz.IntegralOfArctanDerivative
