module

public import OrderTactics
public import PowerTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import WholeTactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds

/-! Written from proofs/wiedijk/fundamental-calculus.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus

set_option maxHeartbeats 600000 in
theorem fundamental_calculus (a : ℝ) (b : ℝ) (hH3 : a < b) (f : ℝ → ℝ) (hH4 : Set.MapsTo f (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ)) (hH5 : ContinuousOn f (Set.Icc a b : Set ℝ)) (F : ℝ → ℝ) (hH6 : Set.MapsTo F (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ)) (hH7 : ContinuousOn F (Set.Icc a b : Set ℝ)) (hH8 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ F x) (hH9 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv F) x = f x) :
    (∫ t in a..b, (f t : ℝ)) = F b - F a := by
  set G : ℝ → ℝ := fun x => ∫ t in a..x, (f t : ℝ) with hD1
  set H : ℝ → ℝ := fun x => G x - F x with hD2
  -- 1. def:interval x := a
  have r78_1 : a ≤ a := by parley_order
  have r78_2 : a ≤ b := by parley_set_side
  have s1 : a ∈ (Set.Icc a b : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := a) (a := a) (b := b))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := a) (a := a) (b := b))).mpr (by parley_set_side); parley_set_side)
  -- 2. def:interval x := b
  have r83_1 : a ≤ b := by parley_set_side
  have r83_2 : b ≤ b := by parley_order
  have s2 : b ∈ (Set.Icc a b : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := b) (a := a) (b := b))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := b) (a := a) (b := b))).mpr (by parley_set_side); parley_set_side)
  -- 3. mun:interval-real
  have s3 : (Set.Icc a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Calculus.mun_interval_real (a := a) (b := b)); parley_set_side)
  -- 4. mun:open-within-closed
  have s4 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | exact ((Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)) | (have h := (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := a) (b := b)); parley_set_side)
  -- 5. D1
  have s5 : ∀ x ∈ (Set.Icc a b : Set ℝ), G x = (∫ t in a..x, (f t : ℝ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
  -- 6. D2
  have s6 : ∀ x ∈ (Set.Icc a b : Set ℝ), H x = G x - F x := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_set_side
  -- 7. proof
  have s7 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by
    intro x hK1
    -- 7.1. mun:integral-real, from D1, H3, H5, K1
    all_goals parley_set_side
  -- 8. mun:function-into, from 7
  have s8 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := G) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := G) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := G) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := G) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := G) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 9. membership, from D2
  have r111_1 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by intro x h_x; (parley_set_side)
  have r111_2 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by intro x h_x; (parley_set_side)
  have s9 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by intro x h_x; parley_set_side
  -- 10. mun:function-into, from 9
  have s10 : Set.MapsTo H (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by first | exact (Parley.Items.Stdlib.Functions.mun_function_into (E := H) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_into (E := H) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_into (E := H) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_into (E := H) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_into (E := H) (X := (Set.Icc a b : Set ℝ)) (Y := (Set.univ : Set ℝ)) (by parley_set_side) (by parley_whole_side)); parley_set_side)
  -- 11. thm:area-function, from H3, H5, 5
  have r120_1 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have s11 : ContinuousOn G (Set.Icc a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.thm_area_function_1 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5) | exact ((Parley.Items.Stdlib.Calculus.thm_area_function_1 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5)).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_area_function_1 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_area_function_1 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5) | (have h := (Parley.Items.Stdlib.Calculus.thm_area_function_1 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5); parley_set_side)
  -- 12. thm:area-function, from H3, H5, 5
  have r124_1 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have s12 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ G x := by first | exact (Parley.Items.Stdlib.Calculus.thm_area_function_2 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5) | exact ((Parley.Items.Stdlib.Calculus.thm_area_function_2 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5)).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_area_function_2 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_area_function_2 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5) | (have h := (Parley.Items.Stdlib.Calculus.thm_area_function_2 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5); parley_set_side)
  -- 13. thm:area-function, from H3, H5, 5
  have r128_1 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have s13 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv G) x = f x := by first | exact (Parley.Items.Stdlib.Calculus.thm_area_function_3 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5) | exact ((Parley.Items.Stdlib.Calculus.thm_area_function_3 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5)).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_area_function_3 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_area_function_3 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5) | (have h := (Parley.Items.Stdlib.Calculus.thm_area_function_3 (f := f) (G := G) (a := a) (b := b) hH3 hH5 s5); parley_set_side)
  -- 14. thm:continuous-difference D := [a, b], F := H, f := G, g := F, from H7, 3, 6, 11
  have r132_1 : Set.MapsTo H (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have r132_2 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have s14 : ContinuousOn H (Set.Icc a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Calculus.thm_continuous_difference (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) s3 s6 s11 hH7) | exact ((Parley.Items.Stdlib.Calculus.thm_continuous_difference (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) s3 s6 s11 hH7)).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_continuous_difference (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) s3 s6 s11 hH7) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_continuous_difference (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) s3 s6 s11 hH7) | (have h := (Parley.Items.Stdlib.Calculus.thm_continuous_difference (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) s3 s6 s11 hH7); parley_set_side)
  -- 15. thm:derivative-difference D := [a, b], U := (a, b), F := H, f := G, g := F, from H8, 3, 6, 12
  have r137_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by parley_set_side
  have r137_2 : Set.MapsTo H (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have r137_3 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have s15 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (Set.Icc a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ H x := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_difference_1 (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s3 (by parley_set_side) s6 s12 hH8) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_difference_1 (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s3 (by parley_set_side) s6 s12 hH8)).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_difference_1 (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s3 (by parley_set_side) s6 s12 hH8) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_difference_1 (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s3 (by parley_set_side) s6 s12 hH8) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_difference_1 (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s3 (by parley_set_side) s6 s12 hH8); parley_set_side)
  -- 16. thm:derivative-difference D := [a, b], U := (a, b), F := H, f := G, g := F, from H8, 3, 6, 12
  have r143_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.Icc a b : Set ℝ) := by parley_set_side
  have r143_2 : Set.MapsTo H (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have r143_3 : Set.MapsTo G (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have s16 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv H) x = (deriv G) x - (deriv F) x := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s3 (by parley_set_side) s6 s12 hH8) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s3 (by parley_set_side) s6 s12 hH8)).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s3 (by parley_set_side) s6 s12 hH8) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s3 (by parley_set_side) s6 s12 hH8) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_difference_2 (F := H) (f := G) (g := F) (D := (Set.Icc a b : Set ℝ)) (U := (Set.Ioo a b : Set ℝ)) s3 (by parley_set_side) s6 s12 hH8); parley_set_side)
  -- 17. proof
  have s17 : ∀ x ∈ (Set.Ioo a b : Set ℝ), (deriv H) x = 0 := by
    intro x hK1
    -- 17.1. substitute G′(x) = f(x) (line 13) into line 16
    have s17_1 : (deriv H) x = f x - (deriv F) x := by parley_subst_at s13 s16
    -- 17.2. substitute F′(x) = f(x) (H9) into line 17.1
    have s17_2 : (deriv H) x = f x - f x := by parley_subst_at hH9 s17_1
    -- 17.3. mun:in-subset, from K1, 4
    have s17_3 : x ∈ (Set.Icc a b : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Icc a b : Set ℝ)) (u := x) s4 hK1) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Icc a b : Set ℝ)) (u := x) s4 hK1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Icc a b : Set ℝ)) (u := x) s4 hK1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Icc a b : Set ℝ)) (u := x) s4 hK1) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Icc a b : Set ℝ)) (u := x) s4 hK1); parley_set_side)
    -- 17.4. algebra, from 17.2
    have s17_4 : (deriv H) x = 0 := by linear_combination (norm := parley_norm) s17_2
    all_goals exact s17_4
  -- 18. D2, from 1
  have s18 : H a = G a - F a := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_set_side
  -- 19. D2, from 2
  have s19 : H b = G b - F b := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_set_side
  -- 20. D1, from 1
  have s20 : G a = (∫ t in a..a, (f t : ℝ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
  -- 21. D1, from 2
  have s21 : G b = (∫ t in a..b, (f t : ℝ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_set_side
  -- 22. calculation
  have r178_1 : Set.MapsTo H (Set.Icc a b : Set ℝ) (Set.univ : Set ℝ) := by parley_set_side
  have s22 : G b - F b = G a - F a := by
    calc G b - F b = H b := by parley_set_side
      _ = H a := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds.zero_derivative_ends (a := a) (b := b) hH3 (H := H) (by parley_set_side) s14 s15 s17) | (have h := (Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds.zero_derivative_ends (a := a) (b := b) hH3 (H := H) (by parley_set_side) s14 s15 s17); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds.zero_derivative_ends (a := a) (b := b) hH3 (H := H) (by parley_set_side) s14 s15 s17); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds.zero_derivative_ends (a := a) (b := b) hH3 (H := H) (by parley_set_side) s14 s15 s17) | exact_mod_cast ((Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds.zero_derivative_ends (a := a) (b := b) hH3 (H := H) (by parley_set_side) s14 s15 s17)).symm | (have h := (Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds.zero_derivative_ends (a := a) (b := b) hH3 (H := H) (by parley_set_side) s14 s15 s17); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds.zero_derivative_ends (a := a) (b := b) hH3 (H := H) (by parley_set_side) s14 s15 s17); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds.zero_derivative_ends (a := a) (b := b) hH3 (H := H) (by parley_set_side) s14 s15 s17); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.FundamentalCalculus.ZeroDerivativeEnds.zero_derivative_ends (a := a) (b := b) hH3 (H := H) (by parley_set_side) s14 s15 s17); parley_set_side)
      _ = G a - F a := by parley_set_side
  -- 23. calculation
  have s23 : G a = 0 := by
    calc G a = (∫ t in a..a, (f t : ℝ)) := by parley_set_side
      _ = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Calculus.mun_integral_point (f := f) (X := (Set.Icc a b : Set ℝ)) (a := a)) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := f) (X := (Set.Icc a b : Set ℝ)) (a := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := f) (X := (Set.Icc a b : Set ℝ)) (a := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_integral_point (f := f) (X := (Set.Icc a b : Set ℝ)) (a := a)) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.mun_integral_point (f := f) (X := (Set.Icc a b : Set ℝ)) (a := a))).symm | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := f) (X := (Set.Icc a b : Set ℝ)) (a := a)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := f) (X := (Set.Icc a b : Set ℝ)) (a := a)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := f) (X := (Set.Icc a b : Set ℝ)) (a := a)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Calculus.mun_integral_point (f := f) (X := (Set.Icc a b : Set ℝ)) (a := a)); parley_set_side)
  -- 24. substitute G(a) = 0 (line 23) into line 22
  have s24 : G b - F b = 0 - F a := by parley_subst_at s23 s22
  -- 25. calculation
  have s25 : (∫ t in a..b, (f t : ℝ)) = F b - F a := by
    calc (∫ t in a..b, (f t : ℝ)) = G b := by parley_set_side
      _ = F b - F a := by linear_combination (norm := parley_norm) s24
  all_goals exact s25

end Parley.Proofs.Wiedijk.FundamentalCalculus.FundamentalCalculus
