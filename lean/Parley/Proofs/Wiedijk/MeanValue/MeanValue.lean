module

public import AlgebraTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/wiedijk/mean-value.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.MeanValue.MeanValue

theorem mean_value (a : ℝ) (b : ℝ) (hH3 : a < b) (f : ℝ → ℝ) (hH4 : Set.MapsTo f (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ)) (hH5 : ContinuousOn f (Set.Icc a b : Set ℝ)) (hH6 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ f x) :
    (∃ c ∈ (Set.Ioo a b : Set ℝ), (deriv f) c = (f b - f a) / (b - a)) := by
  -- 1. inequalities
  have s1 : b - a > 0 := by parley_order
  -- 2. def:interval x := a
  have r32_1 : a ≤ a := by parley_order
  have r32_2 : a ≤ b := by parley_set_side
  have s2 : a ∈ (Set.Icc a b : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := a) (a := a) (b := b))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := a) (a := a) (b := b))).mpr (by parley_set_side); parley_set_side)
  -- 3. def:interval x := b
  have r37_1 : a ≤ b := by parley_set_side
  have r37_2 : b ≤ b := by parley_order
  have s3 : b ∈ (Set.Icc a b : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := b) (a := a) (b := b))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := b) (a := a) (b := b))).mpr (by parley_set_side); parley_set_side)
  -- 4. mun:interval-real
  have s4 : (Set.Icc a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b)); parley_set_side)
  set m : ℝ := (f a - f b) / (b - a) with hD1
  set g : ℝ → ℝ := fun x => m * x with hD2
  set F : ℝ → ℝ := fun x => f x + g x with hD3
  -- 5. D2
  have s5 : ∀ x ∈ (Set.Icc a b : Set ℝ), g x = m * x := by parley_set_side
  -- 6. D3
  have s6 : ∀ x ∈ (Set.Icc a b : Set ℝ), F x = f x + g x := by parley_set_side
  -- 7. membership, from D2
  have s7 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by intro x h_x; parley_set_side
  -- 8. mun:function-into, from 7
  have s8 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := g) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 9. membership, from D2, D3
  have r68_1 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by intro x h_x; (parley_set_side)
  have s9 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by intro x h_x; parley_set_side
  -- 10. mun:function-into, from 9
  have s10 : Set.MapsTo F (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := F) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 11. thm:continuous-linear D := [a, b], from 4, 5
  have r76_1 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have s11 : ContinuousOn g (Set.Icc a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.thm_continuous_linear (g := g) (D := (Set.Icc a b : Set ℝ)) s4 (m := m) s5 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_continuous_linear (g := g) (D := (Set.Icc a b : Set ℝ)) s4 (m := m) s5 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_continuous_linear (g := g) (D := (Set.Icc a b : Set ℝ)) s4 (m := m) s5 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_continuous_linear (g := g) (D := (Set.Icc a b : Set ℝ)) s4 (m := m) s5 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_continuous_linear (g := g) (D := (Set.Icc a b : Set ℝ)) s4 (m := m) s5 (by parley_set_side)); parley_set_side)
  -- 12. thm:continuous-sum D := [a, b], from H5, 4, 6, 11
  have r80_1 : Set.MapsTo F (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have r80_2 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have s12 : ContinuousOn F (Set.Icc a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.thm_continuous_sum (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) s4 s6 hH5 s11 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_continuous_sum (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) s4 s6 hH5 s11 (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_continuous_sum (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) s4 s6 hH5 s11 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_continuous_sum (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) s4 s6 hH5 s11 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_continuous_sum (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) s4 s6 hH5 s11 (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 13. thm:derivative-linear D := [a, b], U := (a, b), from 4, 5
  have r85_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)); parley_set_side)
  have r85_2 : IsOpen (Set.Ioo a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b)); parley_set_side)
  have r85_3 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have s13 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ g x := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) (by parley_set_side) (m := m) s5 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) (by parley_set_side) (m := m) s5 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) (by parley_set_side) (m := m) s5 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) (by parley_set_side) (m := m) s5 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) (by parley_set_side) (m := m) s5 (by parley_set_side)); parley_set_side)
  -- 14. thm:derivative-linear D := [a, b], U := (a, b), from 4, 5
  have r91_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)); parley_set_side)
  have r91_2 : IsOpen (Set.Ioo a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b)); parley_set_side)
  have r91_3 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have s14 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv g) x = m := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) (by parley_set_side) (m := m) s5 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) (by parley_set_side) (m := m) s5 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) (by parley_set_side) (m := m) s5 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) (by parley_set_side) (m := m) s5 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_linear_2 (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) (by parley_set_side) (m := m) s5 (by parley_set_side)); parley_set_side)
  -- 15. thm:derivative-sum D := [a, b], U := (a, b), from H6, 4, 6, 13
  have r97_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)); parley_set_side)
  have r97_2 : Set.MapsTo F (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have r97_3 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have s15 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ F x := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_sum_1 (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) s6 hH6 s13 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_sum_1 (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) s6 hH6 s13 (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_sum_1 (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) s6 hH6 s13 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_sum_1 (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) s6 hH6 s13 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_sum_1 (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) s6 hH6 s13 (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 16. thm:derivative-sum D := [a, b], U := (a, b), from H6, 4, 6, 13
  have r103_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)); parley_set_side)
  have r103_2 : Set.MapsTo F (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have r103_3 : Set.MapsTo g (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have s16 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv F) x = (deriv f) x + (deriv g) x := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_sum_2 (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) s6 hH6 s13 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_sum_2 (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) s6 hH6 s13 (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_sum_2 (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) s6 hH6 s13 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_sum_2 (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) s6 hH6 s13 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_sum_2 (F := F) (f := f) (g := g) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s4 (by parley_set_side) s6 hH6 s13 (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  -- 17. D3, from 2
  have s17 : F a = f a + g a := by parley_set_side
  -- 18. D2, from 2
  have s18 : g a = m * a := by parley_set_side
  -- 19. D3, from 3
  have s19 : F b = f b + g b := by parley_set_side
  -- 20. D2, from 3
  have s20 : g b = m * b := by parley_set_side
  -- 21. calculation
  have r121_1 : b - a ≠ 0 := by parley_set_side
  have s21 : F a = F b := by
    calc F a = f a + g a := by parley_set_side
      _ = f a + m * a := by parley_subst s18
      _ = f b + m * b := by
          try simp only [hD1] at *
          try push_cast at *
          parley_ring
      _ = f b + g b := by parley_subst s20
      _ = F b := by parley_set_side
  -- 22. obtain c: thm:rolle f := F, from H3, 12, 15, 21
  have r132_1 : Set.MapsTo F (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  obtain ⟨c, s22a, s22b⟩ := (Parley.Items.Stdlib.Calculus.thm_rolle (f := F) (a := a) (b := b) hH3 s12 s15 s21 (by parley_set_side))
  -- 23. instantiate x := c in line 14, from 22
  have s23 : (deriv g) c = m := by first | linear_combination (norm := parley_norm) (s14 c (by parley_set_side)) | (have h := (s14 c (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s14 c (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s14 c (by parley_set_side)) | exact_mod_cast ((s14 c (by parley_set_side))).symm | (have h := (s14 c (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s14 c (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s14 c (by parley_set_side)); parley_int_power h) | (have h := (s14 c (by parley_set_side)); parley_set_side)
  -- 24. calculation
  have s24 : (deriv f) c + m = 0 := by
    calc (deriv f) c + m = (deriv f) c + (deriv g) c := by parley_subst s23
      _ = (deriv F) c := by first | linear_combination (norm := parley_norm) (s16 c (by parley_set_side)) | (have h := (s16 c (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s16 c (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s16 c (by parley_set_side)) | exact_mod_cast ((s16 c (by parley_set_side))).symm | (have h := (s16 c (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s16 c (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s16 c (by parley_set_side)); parley_int_power h) | (have h := (s16 c (by parley_set_side)); parley_set_side)
      _ = 0 := by parley_set_side
  -- 25. algebra, from D1, 24
  have r145_1 : b - a ≠ 0 := by parley_set_side
  have s25 : (deriv f) c = (f b - f a) / (b - a) := by
    try simp only [hD1] at *
    try push_cast at *
    linear_combination (norm := parley_field) s24
  -- 26. exhibit, from 22, 25
  have s26 : ∃ c ∈ (Set.Ioo a b : Set ℝ), (deriv f) c = (f b - f a) / (b - a) := ⟨c, by parley_set_side, by parley_set_side⟩
  all_goals exact s26

end Parley.Proofs.Wiedijk.MeanValue.MeanValue
