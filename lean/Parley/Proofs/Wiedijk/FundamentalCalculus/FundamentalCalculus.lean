module

public import NormTactics
public import SetTactics
public import Tactics
public import Batteries.Util.ExtendedBinder
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds

/-! Written from proofs/wiedijk/fundamental-calculus.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus

theorem fundamental_calculus (a : ℝ) (b : ℝ) (hH3 : a < b) (f : ℝ → ℝ) (hH4 : Set.MapsTo f (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ)) (hH5 : ContinuousOn f (Set.Icc a b : Set ℝ)) (F : ℝ → ℝ) (hH6 : Set.MapsTo F (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ)) (hH7 : ContinuousOn F (Set.Icc a b : Set ℝ)) (hH8 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ F x) (hH9 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv F) x = f x) :
    (∫ t in a..b, (f t : ℝ)) = F b - F a := by
  set G : ℝ → ℝ := fun x : ℝ => ∫ t in a..x, (f t : ℝ) with hD1
  set H : ℝ → ℝ := fun x : ℝ => G x - F x with hD2
  -- 1. def:interval x := a
  have r78_1 : a ≤ a := by linarith
  have r78_2 : a ≤ b := by linarith only [hH3]
  have s1 : a ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := a) (a := a) (b := b))).mpr ⟨⟨by trivial, r78_1⟩, r78_2⟩
  -- 2. def:interval x := b
  have r83_1 : a ≤ b := by linarith only [hH3]
  have r83_2 : b ≤ b := by linarith
  have s2 : b ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := b) (a := a) (b := b))).mpr ⟨⟨by trivial, r83_1⟩, r83_2⟩
  -- 3. mun:interval-real
  have s3 : (Set.Icc a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b))
  -- 4. mun:open-within-closed
  have s4 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b))
  -- 5. D1
  have s5 : ∀ x ∈ (Set.Icc a b : Set ℝ), G x = (∫ t in a..x, (f t : ℝ)) := by simp (disch := omega) only [hD1, implies_true]
  -- 6. D2
  have s6 : ∀ x ∈ (Set.Icc a b : Set ℝ), H x = G x - F x := by simp (disch := omega) only [hD2, implies_true]
  -- 7. proof
  have s7 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by
    intro x hK1
    -- 7.1. mun:integral-real, from D1, H3, H5, K1
    exact trivial
  -- 8. mun:function-into, from 7
  have s8 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := G) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 9. membership, from D2
  have s9 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by intro x h_x; exact by trivial
  -- 10. mun:function-into, from 9
  have s10 : Set.MapsTo H (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := H) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 11. thm:area-function, from H3, H5, 5
  have r120_1 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s8
  have s11 : ContinuousOn G (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_area_function_1 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5)
  -- 12. thm:area-function, from H3, H5, 5
  have r124_1 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s8
  have s12 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ G x := by exact (Parley.Items.Stdlib.Calculus.thm_area_function_2 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5)
  -- 13. thm:area-function, from H3, H5, 5
  have r128_1 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s8
  have s13 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv G) x = f x := by exact (Parley.Items.Stdlib.Calculus.thm_area_function_3 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5)
  -- 14. thm:continuous-difference D := [a, b], F := H, f := G, g := F, from H7, 3, 6, 11
  have r132_1 : Set.MapsTo H (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s10
  have r132_2 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s8
  have s14 : ContinuousOn H (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_difference (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) s3 s6 s11 hH7)
  -- 15. thm:derivative-difference D := [a, b], U := (a, b), F := H, f := G, g := F, from H8, 3, 6, 12
  have r137_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by exact s4
  have r137_2 : Set.MapsTo H (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s10
  have r137_3 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s8
  have s15 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ H x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_difference_1 (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s3 r137_1 s6 s12 hH8)
  -- 16. thm:derivative-difference D := [a, b], U := (a, b), F := H, f := G, g := F, from H8, 3, 6, 12
  have r143_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by exact s4
  have r143_2 : Set.MapsTo H (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s10
  have r143_3 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s8
  have s16 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv H) x = (deriv G) x - (deriv F) x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s3 r143_1 s6 s12 hH8)
  -- 17. proof
  have s17 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv H) x = 0 := by
    intro x hK1
    -- 17.1. substitute G′(x) = f(x) (line 13) into line 16
    have s17_1 : (deriv H) x = f x - (deriv F) x := by (have h := Eq.subst (motive := (fun t : ℝ => (deriv H) x = t - (deriv F) x)) (s13 x hK1) (s16 x hK1); push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 17.2. substitute F′(x) = f(x) (H9) into line 17.1
    have s17_2 : (deriv H) x = f x - f x := by (have h := Eq.subst (motive := (fun t : ℝ => (deriv H) x = f x - t)) (hH9 x hK1) s17_1; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 17.3. mun:in-subset, from K1, 4
    have s17_3 : x ∈ (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Icc a b : Set ℝ)) (u := x) s4 hK1)
    -- 17.4. algebra, from 17.2
    linear_combination (norm := parley_norm) s17_2
  -- 18. D2, from 1
  have s18 : H a = G a - F a := by simp (disch := omega) only [hD2]
  -- 19. D2, from 2
  have s19 : H b = G b - F b := by simp (disch := omega) only [hD2]
  -- 20. D1, from 1
  have s20 : G a = (∫ t in a..a, (f t : ℝ)) := by simp (disch := omega) only [hD1]
  -- 21. D1, from 2
  have s21 : G b = (∫ t in a..b, (f t : ℝ)) := by simp (disch := omega) only [hD1]
  -- 22. calculation
  have r178_1 : Set.MapsTo H (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s10
  have s22 : G b - F b = G a - F a := by
    calc G b - F b = H b := s19
      _ = H a := by exact (Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds.zero_derivative_ends (a := a) (b := b) hH3 (H := H) (Set.mapsTo_univ _ _) s14 s15 s17)
      _ = G a - F a := s18
  -- 23. calculation
  have s23 : G a = 0 := by
    calc G a = (∫ t in a..a, (f t : ℝ)) := s20
      _ = 0 := by exact (Parley.Items.Stdlib.Calculus.mun_integral_point (f := f) (X := (Set.Icc a b : Set ℝ)) (a := a))
  -- 24. substitute G(a) = 0 (line 23) into line 22
  have s24 : G b - F b = 0 - F a := by (have h := Eq.subst (motive := (fun t : ℝ => G b - F b = t - F a)) s23 s22; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 25. calculation
  calc (∫ t in a..b, (f t : ℝ)) = G b := s21
    _ = F b - F a := by linear_combination (norm := parley_norm) s24

end Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus
