module

public import AlgebraTactics
public import NormTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
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
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Lhopital.QuotientTwoPoints

/-! Written from proofs/wiedijk/lhopital.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Lhopital.QuotientBetween

set_option maxHeartbeats 1400000 in
theorem quotient_between (a : ℝ) (b : ℝ) (c : ℝ) (hH3 : c ∈ (Set.Ioo a b : Set ℝ)) (f : ℝ → ℝ) (hH4 : Set.MapsTo f ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (Set.univ : Set ℝ)) (g : ℝ → ℝ) (hH5 : Set.MapsTo g ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (Set.univ : Set ℝ)) (hH6 : ∀ x ∈ ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)), ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) ∈ nhds x ∧ DifferentiableAt ℝ f x) (hH7 : ∀ x ∈ ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)), ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) ∈ nhds x ∧ DifferentiableAt ℝ g x) (hH8 : Filter.Tendsto f (nhdsWithin c (((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) \ {c})) (nhds 0)) (hH9 : Filter.Tendsto g (nhdsWithin c (((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) \ {c})) (nhds 0)) (hH10 : ∀ t ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), (deriv g) t ≠ 0) (x : ℝ) (hH11 : x ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) :
    g x ≠ 0 ∧ (∃ ξ ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), abs (ξ - c) < abs (x - c) ∧ f x / g x = (deriv f) ξ / (deriv g) ξ) := by
  set F : ℝ → ℝ := fun t => @ite _ (t = c) (Classical.propDecidable (t = c)) 0 (f t) with hD1
  set G : ℝ → ℝ := fun t => @ite _ (t = c) (Classical.propDecidable (t = c)) 0 (g t) with hD2
  -- 1. mun:open-interval-real
  have s1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b))
  -- 2. mun:difference-subset
  have s2 : (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.Ioo a b : Set ℝ)) (Y := ({c} : Set ℝ)))
  -- 3. mun:subset-transitive X := (a, b) ∖ {c}, Y := (a, b), Z := ℝ, from 1, 2
  have s3 : (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (Y := (Set.Ioo a b : Set ℝ)) (Z := (Set.univ : Set ℝ)) s2 (by parley_whole_side))
  -- 4. mun:subset-self
  have s4 : (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)))
  -- 5. algebra
  have s5 : c = c := by parley_ring
  -- 6. D1, from H3, 5
  have s6 : F c = 0 := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
  -- 7. D2, from H3, 5
  have s7 : G c = 0 := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_set_side
  -- 8. proof
  have s8 : ∀ t ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), F t = f t := by
    intro t hK1
    -- 8.1. mun:remove-member, from K1
    have s8_1 : t ∈ (Set.Ioo a b : Set ℝ) ∧ t ≠ c := ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.Ioo a b : Set ℝ)) (a := c) (u := t))).mp hK1
    -- 8.2. D1, from 8.1
    first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
  -- 9. proof
  have s9 : ∀ t ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), G t = g t := by
    intro t hK2
    -- 9.1. mun:remove-member, from K2
    have s9_1 : t ∈ (Set.Ioo a b : Set ℝ) ∧ t ≠ c := ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.Ioo a b : Set ℝ)) (a := c) (u := t))).mp hK2
    -- 9.2. D2, from 9.1
    first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_set_side
  -- 10. proof
  have s10 : ∀ t ∈ (Set.Ioo a b : Set ℝ), True := by
    intro t hK3
    -- 10.1. axi:excluded-middle
    have s10_1 : t = c ∨ t ≠ c := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t = c))
    -- 10.2. cases, from 10.1
    -- what this block shows, Lean's types give
    exact trivial
  -- 11. mun:function-into, from 10
  have s11 : Set.MapsTo F (Set.Ioo a b : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  -- 12. proof
  have s12 : ∀ t ∈ (Set.Ioo a b : Set ℝ), True := by
    intro t hK4
    -- 12.1. axi:excluded-middle
    have s12_1 : t = c ∨ t ≠ c := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t = c))
    -- 12.2. cases, from 12.1
    -- what this block shows, Lean's types give
    exact trivial
  -- 13. mun:function-into, from 12
  have s13 : Set.MapsTo G (Set.Ioo a b : Set ℝ) (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Functions.mun_function_into (E := G) (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))
  -- 14. thm:continuous-extension U := (a, b), L := 0, from H3, H6, H8, 1, 6, 8, 11
  have r432_1 : IsOpen (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b))
  have s14 : ContinuousOn F (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_extension (f := f) (F := F) (U := (Set.Ioo a b : Set ℝ)) (c := c) s1 r432_1 hH3 (L := (0 : ℝ)) (by simpa using s8) (by parley_set_side) hH6 (by parley_set_side))
  -- 15. thm:continuous-extension U := (a, b), L := 0, f := g, F := G, from H3, H7, H9, 1, 7, 9, 13
  have r436_1 : IsOpen (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b))
  have s15 : ContinuousOn G (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.thm_continuous_extension (f := g) (F := G) (U := (Set.Ioo a b : Set ℝ)) (c := c) s1 r436_1 hH3 (L := (0 : ℝ)) (by simpa using s9) (by parley_set_side) hH7 (by parley_set_side))
  -- 16. mun:open-without-point U := (a, b), from H3, 1
  have r440_1 : IsOpen (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b))
  have s16 : IsOpen ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) := by exact (Parley.Items.Stdlib.Calculus.mun_open_without_point (U := (Set.Ioo a b : Set ℝ)) (c := c) s1 r440_1 hH3)
  -- 17. mun:derivative-local D := (a, b) ∖ {c}, E := (a, b), U := (a, b) ∖ {c}, from H6, 1, 2, 3, 4, 8, 11, 16
  have s17 : ∀ y ∈ ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)), (Set.Ioo a b : Set ℝ) ∈ nhds y ∧ DifferentiableAt ℝ F y := (Parley.Items.Stdlib.Calculus.mun_derivative_local_1 (f := f) (F := F) (D := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (E := (Set.Ioo a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) s3 s1 s4 s2 s16 (by simpa using s8) hH6)
  -- 18. mun:derivative-local D := (a, b) ∖ {c}, E := (a, b), U := (a, b) ∖ {c}, from H6, 1, 2, 3, 4, 8, 11, 16
  have s18 : ∀ t ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), (deriv F) t = (deriv f) t := by exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_derivative_local_2 (f := f) (F := F) (D := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (E := (Set.Ioo a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) s3 s1 s4 s2 s16 (by simpa using s8) hH6)
  -- 19. mun:derivative-local D := (a, b) ∖ {c}, E := (a, b), U := (a, b) ∖ {c}, f := g, F := G, from H7, 1, 2, 3, 4, 9, 13, 16
  have s19 : ∀ y ∈ ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)), (Set.Ioo a b : Set ℝ) ∈ nhds y ∧ DifferentiableAt ℝ G y := (Parley.Items.Stdlib.Calculus.mun_derivative_local_1 (f := g) (F := G) (D := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (E := (Set.Ioo a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) s3 s1 s4 s2 s16 (by simpa using s9) hH7)
  -- 20. mun:derivative-local D := (a, b) ∖ {c}, E := (a, b), U := (a, b) ∖ {c}, f := g, F := G, from H7, 1, 2, 3, 4, 9, 13, 16
  have s20 : ∀ t ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), (deriv G) t = (deriv g) t := by exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_derivative_local_2 (f := g) (F := G) (D := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) (E := (Set.Ioo a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) s3 s1 s4 s2 s16 (by simpa using s9) hH7)
  -- 21. proof
  have s21 : ∀ t ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), (deriv G) t ≠ 0 := by
    intro t hK5
    -- 21.1. restate 20
    have s21_1 : (deriv G) t = (deriv g) t := by parley_set_side
    -- 21.2. substitute G′(t) = g′(t) (line 21.1) into H10
    have at0 := (hH10 t (by parley_set_side))
    parley_subst_at s21_1 at0
  -- 22. mun:remove-member, from H11
  have s22 : x ∈ (Set.Ioo a b : Set ℝ) ∧ x ≠ c := ((Parley.Items.Stdlib.Sets.mun_remove_member (Y := (Set.Ioo a b : Set ℝ)) (a := c) (u := x))).mp hH11
  -- 23. thm:quotient-two-points u := c, v := x, from H3, 11, 13, 14, 15, 17, 19, 21, 22
  have s23a : G c ≠ G x := by exact (Parley.Proofs.Wiedijk.Lhopital.QuotientTwoPoints.quotient_two_points (a := a) (b := b) (u := c) hH3 (v := x) s22.1 s22.2 (F := F) (by parley_set_side) (G := G) (by parley_set_side) s14 s15 s17 s19 s21).1
  have s23b : ∃ ξ ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), abs (ξ - c) < abs (x - c) ∧ (F x - F c) / (G x - G c) = (deriv F) ξ / (deriv G) ξ := by exact (Parley.Proofs.Wiedijk.Lhopital.QuotientTwoPoints.quotient_two_points (a := a) (b := b) (u := c) hH3 (v := x) s22.1 s22.2 (F := F) (by parley_set_side) (G := G) (by parley_set_side) s14 s15 s17 s19 s21).2
  -- 24. restate 23
  have s24 : G c ≠ G x := by parley_set_side
  -- 25. substitute G(c) = 0 (line 7) into line 24
  have s25 : 0 ≠ G x := by parley_subst_at s7 s24
  -- 26. inequalities
  have s26 : G x ≠ 0 := by parley_set_side
  -- 27. obtain ξ from line 23
  obtain ⟨ξ, s27a, s27b⟩ := s23b
  -- 28. restate 27
  have s28 : (F x - F c) / (G x - G c) = (deriv F) ξ / (deriv G) ξ := by parley_set_side
  -- 29. substitute
  have s29 : F x / G x = (deriv F) ξ / (deriv G) ξ := by
    have c1 : F x - F c = F x := by parley_subst s6
    have row1 : F x / (G x - G c) = (deriv F) ξ / (deriv G) ξ := by parley_subst_at c1 s28
    have c2 : G x - G c = G x := by parley_subst s7
    have row2 : F x / G x = (deriv F) ξ / (deriv G) ξ := by parley_subst_at c2 row1
    exact row2
  -- 30. instantiate t := x in line 8, from H11
  have s30 : F x = f x := by first | linear_combination (norm := parley_norm) (s8 x (by parley_set_side)) | (have h := (s8 x (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s8 x (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s8 x (by parley_set_side)) | exact_mod_cast ((s8 x (by parley_set_side))).symm | (have h := (s8 x (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s8 x (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s8 x (by parley_set_side)); parley_int_power h) | (have h := (s8 x (by parley_set_side)); parley_set_side)
  -- 31. instantiate t := x in line 9, from H11
  have s31 : G x = g x := by first | linear_combination (norm := parley_norm) (s9 x (by parley_set_side)) | (have h := (s9 x (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s9 x (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s9 x (by parley_set_side)) | exact_mod_cast ((s9 x (by parley_set_side))).symm | (have h := (s9 x (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s9 x (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s9 x (by parley_set_side)); parley_int_power h) | (have h := (s9 x (by parley_set_side)); parley_set_side)
  -- 32. instantiate t := ξ in line 18, from 27
  have s32 : (deriv F) ξ = (deriv f) ξ := by first | linear_combination (norm := parley_norm) (s18 ξ (by parley_set_side)) | (have h := (s18 ξ (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s18 ξ (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s18 ξ (by parley_set_side)) | exact_mod_cast ((s18 ξ (by parley_set_side))).symm | (have h := (s18 ξ (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s18 ξ (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s18 ξ (by parley_set_side)); parley_int_power h) | (have h := (s18 ξ (by parley_set_side)); parley_set_side)
  -- 33. instantiate t := ξ in line 20, from 27
  have s33 : (deriv G) ξ = (deriv g) ξ := by first | linear_combination (norm := parley_norm) (s20 ξ (by parley_set_side)) | (have h := (s20 ξ (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s20 ξ (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s20 ξ (by parley_set_side)) | exact_mod_cast ((s20 ξ (by parley_set_side))).symm | (have h := (s20 ξ (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s20 ξ (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s20 ξ (by parley_set_side)); parley_int_power h) | (have h := (s20 ξ (by parley_set_side)); parley_set_side)
  -- 34. substitute F(x) = f(x) (line 30) into line 29
  have s34 : f x / G x = (deriv F) ξ / (deriv G) ξ := by parley_subst_at s30 s29
  -- 35. substitute G(x) = g(x) (line 31) into line 34
  have s35 : f x / g x = (deriv F) ξ / (deriv G) ξ := by parley_subst_at s31 s34
  -- 36. substitute F′(ξ) = f′(ξ) (line 32) into line 35
  have s36 : f x / g x = (deriv f) ξ / (deriv G) ξ := by parley_subst_at s32 s35
  -- 37. substitute G′(ξ) = g′(ξ) (line 33) into line 36
  have s37 : f x / g x = (deriv f) ξ / (deriv g) ξ := by parley_subst_at s33 s36
  -- 38. restate 27
  have s38 : abs (ξ - c) < abs (x - c) := by parley_set_side
  -- 39. exhibit, from 27, 37, 38
  have s39 : ∃ ξ ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), abs (ξ - c) < abs (x - c) ∧ f x / g x = (deriv f) ξ / (deriv g) ξ := ⟨ξ, by parley_set_side, ⟨by parley_set_side, by parley_set_side⟩⟩
  -- 40. substitute G(x) = g(x) (line 31) into line 26
  have s40 : g x ≠ 0 := by parley_subst_at s31 s26
  -- 41. join 39, 40
  have s41a : g x ≠ 0 := by parley_set_side
  have s41b : ∃ ξ ∈ (Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ), abs (ξ - c) < abs (x - c) ∧ f x / g x = (deriv f) ξ / (deriv g) ξ := by parley_set_side
  exact ⟨s41a, s41b⟩

end Parley.Proofs.Wiedijk.Lhopital.QuotientBetween
