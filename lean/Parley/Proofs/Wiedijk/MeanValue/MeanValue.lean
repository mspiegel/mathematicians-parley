module

public import AlgebraTactics
public import SetTactics
public import Tactics
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/wiedijk/mean-value.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.MeanValue.MeanValue

theorem mean_value (a : ℝ) (b : ℝ) (hH3 : a < b) (f : ℝ → ℝ) (hH4 : Set.MapsTo f (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ)) (hH5 : ContinuousOn f (Set.Icc a b : Set ℝ)) (hH6 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ f x) :
    (∃ c ∈ (Set.Ioo a b : Set ℝ), (deriv f) c = (f b - f a) / (b - a)) := by
  -- 1. inequalities
  have s1 : b - a > 0 := by linarith only [hH3]
  -- 2. def:interval x := a
  have r32_1 : a ≤ a := by linarith
  have r32_2 : a ≤ b := by linarith only [hH3]
  have s2 : a ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := a) (a := a) (b := b))).mpr ⟨⟨by trivial, r32_1⟩, r32_2⟩
  -- 3. def:interval x := b
  have r37_1 : a ≤ b := by linarith only [hH3]
  have r37_2 : b ≤ b := by linarith
  have s3 : b ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := b) (a := a) (b := b))).mpr ⟨⟨by trivial, r37_1⟩, r37_2⟩
  -- 4. mun:interval-real
  have s4 : (Set.Icc a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b))
  set m : ℝ := (f a - f b) / (b - a) with hD1
  set g : ℝ → ℝ := fun x : ℝ => m * x with hD2
  set F : ℝ → ℝ := fun x : ℝ => f x + g x with hD3
  -- 5. D2
  have s5 : ∀ x ∈ (Set.Icc a b : Set ℝ), g x = m * x := by simp (disch := omega) only [hD2, implies_true]
  -- 6. D3
  have s6 : ∀ x ∈ (Set.Icc a b : Set ℝ), F x = f x + g x := by simp (disch := omega) only [hD3, implies_true]
  -- 7. membership, from D2
  have s7 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by intro x h_x; exact by trivial
  -- 8. mun:function-into, from 7
  have s8 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 9. membership, from D2, D3
  have s9 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by intro x h_x; exact by trivial
  -- 10. mun:function-into, from 9
  have s10 : Set.MapsTo F (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 11. thm:continuous-linear D := [a, b], from 4, 5
  have r76_1 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s8
  have s11 : ContinuousOn g (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_linear (g := g) (D := (Set.Icc a b : Set ℝ)) s4 (m := m) s5)
  -- 12. thm:continuous-sum D := [a, b], from H5, 4, 6, 11
  have r80_1 : Set.MapsTo F (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s10
  have r80_2 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s8
  have s12 : ContinuousOn F (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_sum (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) s4 s6 hH5 s11)
  -- 13. thm:derivative-linear D := [a, b], U := (a, b), from 4, 5
  have r85_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b))
  have r85_2 : IsOpen (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b))
  have r85_3 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s8
  have s13 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ g x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 r85_1 r85_2 (m := m) s5)
  -- 14. thm:derivative-linear D := [a, b], U := (a, b), from 4, 5
  have r91_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b))
  have r91_2 : IsOpen (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b))
  have r91_3 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s8
  have s14 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv g) x = m := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 r91_1 r91_2 (m := m) s5)
  -- 15. thm:derivative-sum D := [a, b], U := (a, b), from H6, 4, 6, 13
  have r97_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b))
  have r97_2 : Set.MapsTo F (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s10
  have r97_3 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s8
  have s15 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ F x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_sum_1 (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 r97_1 s6 hH6 s13)
  -- 16. thm:derivative-sum D := [a, b], U := (a, b), from H6, 4, 6, 13
  have r103_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b))
  have r103_2 : Set.MapsTo F (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s10
  have r103_3 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s8
  have s16 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv F) x = (deriv f) x + (deriv g) x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_sum_2 (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 r103_1 s6 hH6 s13)
  -- 17. D3, from 2
  have s17 : F a = f a + g a := by simp (disch := omega) only [hD3]
  -- 18. D2, from 2
  have s18 : g a = m * a := by simp (disch := omega) only [hD2]
  -- 19. D3, from 3
  have s19 : F b = f b + g b := by simp (disch := omega) only [hD3]
  -- 20. D2, from 3
  have s20 : g b = m * b := by simp (disch := omega) only [hD2]
  -- 21. calculation
  have r121_1 : b - a ≠ 0 := ne_of_gt (by linarith only [s1])
  have s21 : F a = F b := by
    calc F a = f a + g a := s17
      _ = f a + m * a := by (have h := congrArg (fun t : ℝ => f a + t) s18; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = f b + m * b := by
          try simp only [hD1] at s17 s18 s19 s20 r121_1 ⊢
          try push_cast at s17 s18 s19 s20 r121_1 ⊢
          parley_ring
      _ = f b + g b := by (have h := congrArg (fun t : ℝ => f b + t) s20.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = F b := s19
  -- 22. obtain c: thm:rolle f := F, from H3, 12, 15, 21
  have r132_1 : Set.MapsTo F (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact s10
  obtain ⟨c, s22a, s22b⟩ := (Parley.Items.Stdlib.Calculus.thm_rolle (f := F) (a := a) (b := b) hH3 s12 s15 s21)
  -- 23. instantiate x := c in line 14, from 22
  have s23 : (deriv g) c = m := by exact (s14 c s22a)
  -- 24. calculation
  have s24 : (deriv f) c + m = 0 := by
    calc (deriv f) c + m = (deriv f) c + (deriv g) c := by (have h := congrArg (fun t : ℝ => (deriv f) c + t) s23.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (deriv F) c := by exact (s16 c s22a).symm
      _ = 0 := s22b
  -- 25. algebra, from D1, 24
  have r145_1 : b - a ≠ 0 := ne_of_gt (by linarith only [s1])
  have s25 : (deriv f) c = (f b - f a) / (b - a) := by
    try simp only [hD1] at s24 r145_1 ⊢
    try push_cast at s24 r145_1 ⊢
    linear_combination (norm := parley_field) s24
  -- 26. exhibit, from 22, 25
  exact ⟨c, s22a, s25⟩

end Parley.Proofs.Wiedijk.MeanValue.MeanValue
