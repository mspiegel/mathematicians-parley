module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from corpus/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Calculus.CauchyMeanValue

theorem cauchy_mean_value (D : Set ℝ) (hH1 : D ⊆ (Set.univ : Set ℝ)) (a : ℝ) (b : ℝ) (hH4 : a < b) (hH5 : (Set.Icc a b : Set ℝ) ⊆ D) (f : ℝ → ℝ) (hH6 : Set.MapsTo f D (Set.univ : Set ℝ)) (g : ℝ → ℝ) (hH7 : Set.MapsTo g D (Set.univ : Set ℝ)) (hH8 : ContinuousOn f (Set.Icc a b : Set ℝ)) (hH9 : ContinuousOn g (Set.Icc a b : Set ℝ)) (hH10 : ∀ x ∈ (Set.Ioo a b : Set ℝ), D ∈ nhds x ∧ DifferentiableAt ℝ f x) (hH11 : ∀ x ∈ (Set.Ioo a b : Set ℝ), D ∈ nhds x ∧ DifferentiableAt ℝ g x) :
    (∃ c ∈ (Set.Ioo a b : Set ℝ), (f b - f a) * (deriv g) c = (g b - g a) * (deriv f) c) := by
  set p : ℝ → ℝ := (fun t : ℝ => f t) with hD1
  set q : ℝ → ℝ := (fun t : ℝ => g t) with hD2
  set u : ℝ → ℝ := fun x : ℝ => (f b - f a) * q x with hD3
  set v : ℝ → ℝ := fun x : ℝ => (g b - g a) * p x with hD4
  set h : ℝ → ℝ := fun x : ℝ => u x - v x with hD5
  -- 1. mun:interval-real
  have s1 : (Set.Icc a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b))
  -- 2. mun:open-within-closed
  have s2 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b))
  -- 3. mun:subset-transitive, from H5, 2
  have s3 : (Set.Ioo a b : Set ℝ) ⊆ D := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Icc a b : Set ℝ)) (Z := D) s2 hH5)
  -- 4. mun:open-interval-open
  have s4 : IsOpen (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b))
  -- 5. def:interval x := a
  have r75_1 : a ≤ a := by linarith
  have r75_2 : a ≤ b := by linarith only [hH4]
  have s5 : a ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := a) (a := a) (b := b))).mpr ⟨⟨by trivial, r75_1⟩, r75_2⟩
  -- 6. def:interval x := b
  have r80_1 : a ≤ b := by linarith only [hH4]
  have r80_2 : b ≤ b := by linarith
  have s6 : b ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := b) (a := a) (b := b))).mpr ⟨⟨by trivial, r80_1⟩, r80_2⟩
  -- 7. mun:in-subset, from H5, 5
  have s7 : a ∈ D := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc a b : Set ℝ)) (Y := D) (u := a) hH5 s5)
  -- 8. mun:in-subset, from H5, 6
  have s8 : b ∈ D := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc a b : Set ℝ)) (Y := D) (u := b) hH5 s6)
  -- 9. mun:map-continuous-on-part S := [a, b], from D1, H1, H5, H6, H8
  have s9 : ContinuousOn p (Set.Icc a b : Set ℝ) := by
    simp only [hD1] at ⊢
    push_cast at ⊢
    (have h := (Parley.Items.Stdlib.Calculus.mun_map_continuous_on_part (f := f) (D := D) (S := (Set.Icc a b : Set ℝ)) hH1 hH5 hH8); push_cast at h; exact h)
  -- 10. mun:map-continuous-on-part S := [a, b], f := g, from D2, H1, H5, H7, H9
  have s10 : ContinuousOn q (Set.Icc a b : Set ℝ) := by
    simp only [hD2] at ⊢
    push_cast at ⊢
    (have h := (Parley.Items.Stdlib.Calculus.mun_map_continuous_on_part (f := g) (D := D) (S := (Set.Icc a b : Set ℝ)) hH1 hH5 hH9); push_cast at h; exact h)
  -- 11. proof
  have s11 : ∀ t ∈ (Set.Icc a b : Set ℝ), True := by
    intro t hK1
    -- 11.1. mun:in-subset, from H5, K1
    have s11_1 : t ∈ D := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc a b : Set ℝ)) (Y := D) (u := t) hH5 hK1)
    -- 11.2. membership, from D1, H6, 11.1
    have r104_1 : t ∈ (Set.Icc a b : Set ℝ) := by exact hK1
    exact trivial
  -- 12. proof
  have s12 : ∀ t ∈ (Set.Icc a b : Set ℝ), True := by
    intro t hK1
    -- 12.1. mun:in-subset, from H5, K1
    have s12_1 : t ∈ D := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc a b : Set ℝ)) (Y := D) (u := t) hH5 hK1)
    -- 12.2. membership, from D2, H7, 12.1
    have r115_1 : t ∈ (Set.Icc a b : Set ℝ) := by exact hK1
    exact trivial
  -- 13. mun:function-into, from D1, 11
  have s13 : Set.MapsTo p (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := p) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 14. mun:function-into, from D2, 12
  have s14 : Set.MapsTo q (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := q) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 15. D1
  have r125_1 : ∀ x ∈ (Set.Ioo a b : Set ℝ), x ∈ (Set.Icc a b : Set ℝ) := by intro x h_x; (exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Icc a b : Set ℝ)) (u := x) s2 h_x))
  have s15 : ∀ x ∈ (Set.Ioo a b : Set ℝ), p x = f x := by simp (disch := omega) only [hD1, implies_true]
  -- 16. D2
  have r129_1 : ∀ x ∈ (Set.Ioo a b : Set ℝ), x ∈ (Set.Icc a b : Set ℝ) := by intro x h_x; (exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Icc a b : Set ℝ)) (u := x) s2 h_x))
  have s16 : ∀ x ∈ (Set.Ioo a b : Set ℝ), q x = g x := by simp (disch := omega) only [hD2, implies_true]
  -- 17. mun:derivative-local E := [a, b], U := (a, b), F := p, from H1, H10, 1, 2, 3, 4, 13, 15
  have s17 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ p x := by exact (Parley.Items.Stdlib.Calculus.mun_derivative_local_1 (f := f) (F := p) (D := D) (E := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) hH1 s1 s3 s2 s4 s15 hH10)
  -- 18. mun:derivative-local E := [a, b], U := (a, b), F := p, from H1, H10, 1, 2, 3, 4, 13, 15
  have s18 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv p) x = (deriv f) x := by exact (Parley.Items.Stdlib.Calculus.mun_derivative_local_2 (f := f) (F := p) (D := D) (E := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) hH1 s1 s3 s2 s4 s15 hH10)
  -- 19. mun:derivative-local E := [a, b], U := (a, b), f := g, F := q, from H1, H11, 1, 2, 3, 4, 14, 16
  have s19 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ q x := by exact (Parley.Items.Stdlib.Calculus.mun_derivative_local_1 (f := g) (F := q) (D := D) (E := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) hH1 s1 s3 s2 s4 s16 hH11)
  -- 20. mun:derivative-local E := [a, b], U := (a, b), f := g, F := q, from H1, H11, 1, 2, 3, 4, 14, 16
  have s20 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv q) x = (deriv g) x := by exact (Parley.Items.Stdlib.Calculus.mun_derivative_local_2 (f := g) (F := q) (D := D) (E := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) hH1 s1 s3 s2 s4 s16 hH11)
  -- 21. D3
  have s21 : ∀ x ∈ (Set.Icc a b : Set ℝ), u x = (f b - f a) * q x := by simp (disch := omega) only [hD3, implies_true]
  -- 22. D4
  have s22 : ∀ x ∈ (Set.Icc a b : Set ℝ), v x = (g b - g a) * p x := by simp (disch := omega) only [hD4, implies_true]
  -- 23. D5
  have s23 : ∀ x ∈ (Set.Icc a b : Set ℝ), h x = u x - v x := by simp (disch := omega) only [hD5, implies_true]
  -- 24. membership, from H6, 7, 8
  -- 25. membership, from H7, 7, 8
  -- 26. membership, from D3
  have s26 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by intro x h_x; exact by trivial
  -- 27. membership, from D4
  have s27 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by intro x h_x; exact by trivial
  -- 28. mun:function-into, from 26
  have s28 : Set.MapsTo u (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := u) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 29. mun:function-into, from 27
  have s29 : Set.MapsTo v (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := v) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 30. membership, from D5
  have s30 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by intro x h_x; exact by trivial
  -- 31. mun:function-into, from 30
  have s31 : Set.MapsTo h (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := h) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 32. thm:continuous-scaled D := [a, b], c := f(b) − f(a), F := u, f := q, from 1, 10, 14, 21, 24, 28
  have s32 : ContinuousOn u (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_scaled (F := u) (f := q) (D := (Set.Icc a b : Set ℝ)) s1 (c := f b - f a) s21 s10)
  -- 33. thm:continuous-scaled D := [a, b], c := g(b) − g(a), F := v, f := p, from 1, 9, 13, 22, 25, 29
  have s33 : ContinuousOn v (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_scaled (F := v) (f := p) (D := (Set.Icc a b : Set ℝ)) s1 (c := g b - g a) s22 s9)
  -- 34. thm:continuous-difference D := [a, b], F := h, f := u, g := v, from 1, 23, 28, 29, 31, 32, 33
  have s34 : ContinuousOn h (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_difference (F := h) (f := u) (g := v) (D := (Set.Icc a b : Set ℝ)) s1 s23 s32 s33)
  -- 35. thm:derivative-scaled D := [a, b], U := (a, b), c := f(b) − f(a), F := u, f := q, from 1, 2, 14, 19, 21, 24, 28
  have s35 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ u x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_1 (F := u) (f := q) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s1 s2 (c := f b - f a) s21 s19)
  -- 36. thm:derivative-scaled D := [a, b], U := (a, b), c := f(b) − f(a), F := u, f := q, from 1, 2, 14, 19, 21, 24, 28
  have s36 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv u) x = (f b - f a) * (deriv q) x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_2 (F := u) (f := q) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s1 s2 (c := f b - f a) s21 s19)
  -- 37. thm:derivative-scaled D := [a, b], U := (a, b), c := g(b) − g(a), F := v, f := p, from 1, 2, 13, 17, 22, 25, 29
  have s37 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ v x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_1 (F := v) (f := p) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s1 s2 (c := g b - g a) s22 s17)
  -- 38. thm:derivative-scaled D := [a, b], U := (a, b), c := g(b) − g(a), F := v, f := p, from 1, 2, 13, 17, 22, 25, 29
  have s38 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv v) x = (g b - g a) * (deriv p) x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_2 (F := v) (f := p) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s1 s2 (c := g b - g a) s22 s17)
  -- 39. thm:derivative-difference D := [a, b], U := (a, b), F := h, f := u, g := v, from 1, 2, 23, 28, 29, 31, 35, 37
  have s39 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ h x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_difference_1 (F := h) (f := u) (g := v) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s1 s2 s23 s35 s37)
  -- 40. thm:derivative-difference D := [a, b], U := (a, b), F := h, f := u, g := v, from 1, 2, 23, 28, 29, 31, 35, 37
  have s40 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv h) x = (deriv u) x - (deriv v) x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := h) (f := u) (g := v) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s1 s2 s23 s35 s37)
  -- 41. D5, from 5
  have s41 : h a = u a - v a := by simp (disch := omega) only [hD5]
  -- 42. D3, from 5
  have s42 : u a = (f b - f a) * q a := by simp (disch := omega) only [hD3]
  -- 43. D4, from 5
  have s43 : v a = (g b - g a) * p a := by simp (disch := omega) only [hD4]
  -- 44. D2, from 5
  have s44 : q a = g a := by simp (disch := omega) only [hD2]
  -- 45. D1, from 5
  have s45 : p a = f a := by simp (disch := omega) only [hD1]
  -- 46. D5, from 6
  have s46 : h b = u b - v b := by simp (disch := omega) only [hD5]
  -- 47. D3, from 6
  have s47 : u b = (f b - f a) * q b := by simp (disch := omega) only [hD3]
  -- 48. D4, from 6
  have s48 : v b = (g b - g a) * p b := by simp (disch := omega) only [hD4]
  -- 49. D2, from 6
  have s49 : q b = g b := by simp (disch := omega) only [hD2]
  -- 50. D1, from 6
  have s50 : p b = f b := by simp (disch := omega) only [hD1]
  -- 51. substitute q(a) = g(a) (line 44) into line 42
  have s51 : u a = (f b - f a) * g a := Eq.subst (motive := (fun t : ℝ => u a = (f b - f a) * t)) s44 s42
  -- 52. substitute p(a) = f(a) (line 45) into line 43
  have s52 : v a = (g b - g a) * f a := Eq.subst (motive := (fun t : ℝ => v a = (g b - g a) * t)) s45 s43
  -- 53. substitute
  have s53 : h a = (f b - f a) * g a - (g b - g a) * f a := by
    have c1 : u a = (f b - f a) * g a := congrArg (fun t : ℝ => t) s51
    have row1 : h a = (f b - f a) * g a - v a := Eq.subst (motive := (fun t : ℝ => h a = t - v a)) c1 s41
    have c2 : v a = (g b - g a) * f a := congrArg (fun t : ℝ => t) s52
    have row2 : h a = (f b - f a) * g a - (g b - g a) * f a := Eq.subst (motive := (fun t : ℝ => h a = (f b - f a) * g a - t)) c2 row1
    exact row2
  -- 54. substitute q(b) = g(b) (line 49) into line 47
  have s54 : u b = (f b - f a) * g b := Eq.subst (motive := (fun t : ℝ => u b = (f b - f a) * t)) s49 s47
  -- 55. substitute p(b) = f(b) (line 50) into line 48
  have s55 : v b = (g b - g a) * f b := Eq.subst (motive := (fun t : ℝ => v b = (g b - g a) * t)) s50 s48
  -- 56. substitute
  have s56 : h b = (f b - f a) * g b - (g b - g a) * f b := by
    have c1 : u b = (f b - f a) * g b := congrArg (fun t : ℝ => t) s54
    have row1 : h b = (f b - f a) * g b - v b := Eq.subst (motive := (fun t : ℝ => h b = t - v b)) c1 s46
    have c2 : v b = (g b - g a) * f b := congrArg (fun t : ℝ => t) s55
    have row2 : h b = (f b - f a) * g b - (g b - g a) * f b := Eq.subst (motive := (fun t : ℝ => h b = (f b - f a) * g b - t)) c2 row1
    exact row2
  -- 57. calculation
  have s57 : h a = h b := by
    calc h a = (f b - f a) * g a - (g b - g a) * f a := s53
      _ = (f b - f a) * g b - (g b - g a) * f b := by ring1
      _ = h b := s56.symm
  -- 58. obtain c: thm:rolle f := h, from H4, 31, 34, 39, 57
  obtain ⟨c, s58a, s58b⟩ := (Parley.Items.Stdlib.Calculus.thm_rolle (f := h) (a := a) (b := b) hH4 s34 s39 s57)
  -- 59. instantiate x := c in line 40, from 58
  have s59 : (deriv h) c = (deriv u) c - (deriv v) c := by exact (s40 c s58a)
  -- 60. instantiate x := c in line 36, from 58
  have s60 : (deriv u) c = (f b - f a) * (deriv q) c := by exact (s36 c s58a)
  -- 61. instantiate x := c in line 38, from 58
  have s61 : (deriv v) c = (g b - g a) * (deriv p) c := by exact (s38 c s58a)
  -- 62. instantiate x := c in line 20, from 58
  have s62 : (deriv q) c = (deriv g) c := by exact (s20 c s58a)
  -- 63. instantiate x := c in line 18, from 58
  have s63 : (deriv p) c = (deriv f) c := by exact (s18 c s58a)
  -- 64. substitute q′(c) = g′(c) (line 62) into line 60
  have s64 : (deriv u) c = (f b - f a) * (deriv g) c := Eq.subst (motive := (fun t : ℝ => (deriv u) c = (f b - f a) * t)) s62 s60
  -- 65. substitute p′(c) = f′(c) (line 63) into line 61
  have s65 : (deriv v) c = (g b - g a) * (deriv f) c := Eq.subst (motive := (fun t : ℝ => (deriv v) c = (g b - g a) * t)) s63 s61
  -- 66. substitute
  have s66 : (deriv h) c = (f b - f a) * (deriv g) c - (g b - g a) * (deriv f) c := by
    have c1 : (deriv u) c = (f b - f a) * (deriv g) c := congrArg (fun t : ℝ => t) s64
    have row1 : (deriv h) c = (f b - f a) * (deriv g) c - (deriv v) c := Eq.subst (motive := (fun t : ℝ => (deriv h) c = t - (deriv v) c)) c1 s59
    have c2 : (deriv v) c = (g b - g a) * (deriv f) c := congrArg (fun t : ℝ => t) s65
    have row2 : (deriv h) c = (f b - f a) * (deriv g) c - (g b - g a) * (deriv f) c := Eq.subst (motive := (fun t : ℝ => (deriv h) c = (f b - f a) * (deriv g) c - t)) c2 row1
    exact row2
  -- 67. calculation
  have s67 : (f b - f a) * (deriv g) c - (g b - g a) * (deriv f) c = 0 := by
    calc (f b - f a) * (deriv g) c - (g b - g a) * (deriv f) c = (deriv h) c := s66.symm
      _ = 0 := s58b
  -- 68. algebra, from 67
  have s68 : (f b - f a) * (deriv g) c = (g b - g a) * (deriv f) c := by linear_combination s67
  -- 69. exhibit, from 58, 68
  exact ⟨c, s58a, s68⟩

end Parley.Stdlib.Calculus.CauchyMeanValue
