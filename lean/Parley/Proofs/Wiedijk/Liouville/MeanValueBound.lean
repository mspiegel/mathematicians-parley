module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
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
public import Parley.Proofs.Wiedijk.MeanValue.MeanValue

/-! Written from proofs/wiedijk/liouville.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Liouville.MeanValueBound

theorem mean_value_bound (f : ℝ → ℝ) (hH2 : ContinuousOn f (Set.univ : Set ℝ)) (hH3 : ∀ x ∈ (Set.univ : Set ℝ), (Set.univ : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ f x) (a : ℝ) (b : ℝ) (hH6 : a < b) (M : ℝ) (hH8 : ∀ t ∈ (Set.Icc a b : Set ℝ), abs ((deriv f) t) ≤ M) :
    abs (f b - f a) ≤ M * (b - a) := by
  set g : ℝ → ℝ := (fun t : ℝ => f t) with hD1
  -- 1. mun:interval-real
  have s1 : (Set.Icc a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b))
  -- 2. mun:subset-self
  have s2 : (Set.univ : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.univ : Set ℝ)))
  -- 3. mun:continuous-on-part D := ℝ, S := [a, b], from H2, 1, 2
  have s3 : ContinuousOn f (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_continuous_on_part (f := f) (D := (Set.univ : Set ℝ)) (S := (Set.Icc a b : Set ℝ)) s2 s1 hH2)
  -- 4. mun:map-continuous-on-part D := ℝ, S := [a, b], from D1, 1, 2, 3
  have s4 : ContinuousOn g (Set.Icc a b : Set ℝ) := by
    simp only [hD1] at ⊢
    push_cast at ⊢
    exact (Parley.Items.Stdlib.Calculus.mun_map_continuous_on_part (f := f) (D := (Set.univ : Set ℝ)) (S := (Set.Icc a b : Set ℝ)) s2 s1 s3)
  -- 5. membership, from D1, H1
  have s5 : ∀ t ∈ (Set.Icc a b : Set ℝ), True := by intro t h_t; exact by trivial
  -- 6. mun:function-into, from D1, 5
  have s6 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by
    simp only [hD1] at ⊢
    push_cast at ⊢
    exact (Parley.Items.Stdlib.Functions.mun_function_into (E := (fun t : ℝ => f t)) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by intro x _; exact Set.mem_univ _))
  -- 7. mun:open-within-closed
  have s7 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b))
  -- 8. mun:open-interval-real
  have s8 : (Set.Ioo a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b))
  -- 9. mun:open-interval-open
  have s9 : IsOpen (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b))
  -- 10. mun:differentiable-on-part D := ℝ, U := ℝ, S := (a, b), from H3, 2, 8
  have s10 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.univ : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ f x := by exact (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := f) (D := (Set.univ : Set ℝ)) (U := (Set.univ : Set ℝ)) (S := (Set.Ioo a b : Set ℝ)) s2 s2 s8 hH3)
  -- 11. D1
  have r95_1 : ∀ x ∈ (Set.Ioo a b : Set ℝ), x ∈ (Set.Icc a b : Set ℝ) := by intro x h_x; (exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Icc a b : Set ℝ)) (u := x) s7 h_x))
  have s11 : ∀ x ∈ (Set.Ioo a b : Set ℝ), g x = f x := by simp (disch := omega) only [hD1, implies_true]
  -- 12. mun:derivative-local D := ℝ, E := [a, b], U := (a, b), F := g, from 1, 2, 6, 7, 8, 9, 10, 11
  have s12 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ g x := by exact (Parley.Items.Stdlib.Calculus.mun_derivative_local_1 (f := f) (F := g) (D := (Set.univ : Set ℝ)) (E := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s2 s1 s8 s7 s9 s11 s10)
  -- 13. mun:derivative-local D := ℝ, E := [a, b], U := (a, b), F := g, from 1, 2, 6, 7, 8, 9, 10, 11
  have s13 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv g) x = (deriv f) x := by exact (Parley.Items.Stdlib.Calculus.mun_derivative_local_2 (f := f) (F := g) (D := (Set.univ : Set ℝ)) (E := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s2 s1 s8 s7 s9 s11 s10)
  -- 14. obtain c: thm:mean-value f := g, from H6, 4, 6, 12
  obtain ⟨c, s14a, s14b⟩ := (Parley.Proofs.Wiedijk.MeanValue.MeanValue.mean_value (a := a) (b := b) hH6 (f := g) (Set.mapsTo_univ _ _) s4 s12)
  -- 15. def:interval x := a
  have r108_1 : a ≤ a := by linarith
  have r108_2 : a ≤ b := by linarith only [hH6]
  have s15 : a ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := a) (a := a) (b := b))).mpr ⟨⟨by trivial, r108_1⟩, r108_2⟩
  -- 16. def:interval x := b
  have r113_1 : a ≤ b := by linarith only [hH6]
  have r113_2 : b ≤ b := by linarith
  have s16 : b ∈ (Set.Icc a b : Set ℝ) := ((Parley.Items.Stdlib.Calculus.def_interval (x := b) (a := a) (b := b))).mpr ⟨⟨by trivial, r113_1⟩, r113_2⟩
  -- 17. D1, from 15
  have s17 : g a = f a := by simp (disch := omega) only [hD1]
  -- 18. D1, from 16
  have s18 : g b = f b := by simp (disch := omega) only [hD1]
  -- 19. calculation
  have s19 : (deriv f) c = (f b - f a) / (b - a) := by
    calc (deriv f) c = (deriv g) c := by exact (s13 c s14a).symm
      _ = (g b - g a) / (b - a) := s14b
      _ = (f b - g a) / (b - a) := congrArg (fun t : ℝ => (t - g a) / (b - a)) s18
      _ = (f b - f a) / (b - a) := congrArg (fun t : ℝ => (f b - t) / (b - a)) s17
  -- 20. inequalities
  have s20 : b - a > 0 := by linarith only [hH6]
  -- 21. mun:derivative-real-on D := ℝ, U := ℝ, x := c, from H3, 2
  -- 22. algebra, from 19
  have r140_3 : b - a ≠ 0 := ne_of_gt (by linarith only [s20])
  have s22 : f b - f a = (deriv f) c * (b - a) := by have hz1 : b - a ≠ 0 := r140_3; linear_combination (norm := (field)) (a - b) * s19
  -- 23. mun:in-subset, from 7, 14
  have s23 : c ∈ (Set.Icc a b : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Icc a b : Set ℝ)) (u := c) s7 s14a)
  -- 24. instantiate t := c in H8, from 23
  have s24 : abs ((deriv f) c) ≤ M := by exact (hH8 c s23)
  -- 25. inequalities
  have s25 : b - a ≥ 0 := by linarith only [s20]
  -- 26. def:abs x := b − a, from 25
  have s26 : abs (b - a) = b - a := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := b - a)) s25
  -- 27. calculation
  have s27 : abs (f b - f a) = abs ((deriv f) c) * (b - a) := by
    calc abs (f b - f a) = abs ((deriv f) c * (b - a)) := congrArg (fun t : ℝ => abs t) s22
      _ = abs ((deriv f) c) * abs (b - a) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_product (x := (deriv f) c) (y := b - a))
      _ = abs ((deriv f) c) * (b - a) := congrArg (fun t : ℝ => abs ((deriv f) c) * t) s26
  -- 28. mun:multiply-le-nonneg x := |f′(c)|, y := M, c := b − a, from 24, 25
  have s28 : abs ((deriv f) c) * (b - a) ≤ M * (b - a) := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := abs ((deriv f) c)) (y := M) (c := b - a) s24 s25)
  -- 29. transitivity, from 27, 28
  exact Eq.trans_le s27 s28

end Parley.Proofs.Wiedijk.Liouville.MeanValueBound
