module

public import AlgebraTactics
public import ArithTactics
public import OrderTactics
public import SetTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/lhopital.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Lhopital.CauchyQuotient

set_option maxHeartbeats 400000 in
theorem cauchy_quotient (E : Set ℝ) (hH1 : E ⊆ (Set.univ : Set ℝ)) (U : Set ℝ) (hH2 : U ⊆ E) (p : ℝ) (q : ℝ) (hH5 : p < q) (hH6 : (Set.Icc p q : Set ℝ) ⊆ E) (hH7 : (Set.Ioo p q : Set ℝ) ⊆ U) (F : ℝ → ℝ) (hH8 : Set.MapsTo F E (Set.univ : Set ℝ)) (G : ℝ → ℝ) (hH9 : Set.MapsTo G E (Set.univ : Set ℝ)) (hH10 : ContinuousOn F (Set.Icc p q : Set ℝ)) (hH11 : ContinuousOn G (Set.Icc p q : Set ℝ)) (hH12 : ∀ x ∈ U, E ∈ nhds x ∧ DifferentiableAt ℝ F x) (hH13 : ∀ x ∈ U, E ∈ nhds x ∧ DifferentiableAt ℝ G x) (hH14 : ∀ t ∈ U, (deriv G) t ≠ 0) :
    G p ≠ G q ∧ (∃ ξ ∈ (Set.Ioo p q : Set ℝ), (F q - F p) / (G q - G p) = (deriv F) ξ / (deriv G) ξ) := by
  -- 1. mun:differentiable-on-part D := E, S := (p, q), f := F, from H1, H2, H7, H12
  have s1 : ∀ x ∈ (Set.Ioo p q : Set ℝ), E ∈ nhds x ∧ DifferentiableAt ℝ F x := by first | exact (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := F) (D := E) (U := U) (S := (Set.Ioo p q : Set ℝ)) hH1 hH2 hH7 hH12) | exact ((Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := F) (D := E) (U := U) (S := (Set.Ioo p q : Set ℝ)) hH1 hH2 hH7 hH12)).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := F) (D := E) (U := U) (S := (Set.Ioo p q : Set ℝ)) hH1 hH2 hH7 hH12) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := F) (D := E) (U := U) (S := (Set.Ioo p q : Set ℝ)) hH1 hH2 hH7 hH12) | (have h := (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := F) (D := E) (U := U) (S := (Set.Ioo p q : Set ℝ)) hH1 hH2 hH7 hH12); parley_set_side)
  -- 2. mun:differentiable-on-part D := E, S := (p, q), f := G, from H1, H2, H7, H13
  have s2 : ∀ x ∈ (Set.Ioo p q : Set ℝ), E ∈ nhds x ∧ DifferentiableAt ℝ G x := by first | exact (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := G) (D := E) (U := U) (S := (Set.Ioo p q : Set ℝ)) hH1 hH2 hH7 hH13) | exact ((Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := G) (D := E) (U := U) (S := (Set.Ioo p q : Set ℝ)) hH1 hH2 hH7 hH13)).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := G) (D := E) (U := U) (S := (Set.Ioo p q : Set ℝ)) hH1 hH2 hH7 hH13) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := G) (D := E) (U := U) (S := (Set.Ioo p q : Set ℝ)) hH1 hH2 hH7 hH13) | (have h := (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := G) (D := E) (U := U) (S := (Set.Ioo p q : Set ℝ)) hH1 hH2 hH7 hH13); parley_set_side)
  -- 3. contradiction
  have s3 : G p ≠ G q := by
    by_contra hc_hS
    have hS : G p = G q := by parley_suppose hc_hS
    -- 3.1. obtain ξ: thm:rolle-on-part D := E, a := p, b := q, f := G, from H1, H5, H6, H11, S, 2
    obtain ⟨ξ, s3_1a, s3_1b⟩ := (Parley.Items.Stdlib.Calculus.thm_rolle_on_part (f := G) (D := E) hH1 (a := p) (b := q) hH5 hH6 hH11 s2 hS)
    -- 3.2. mun:in-subset, from H7, 3.1
    have s3_2 : ξ ∈ U := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo p q : Set ℝ)) (Y := U) (u := ξ) hH7 s3_1a) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo p q : Set ℝ)) (Y := U) (u := ξ) hH7 s3_1a)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo p q : Set ℝ)) (Y := U) (u := ξ) hH7 s3_1a) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo p q : Set ℝ)) (Y := U) (u := ξ) hH7 s3_1a) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo p q : Set ℝ)) (Y := U) (u := ξ) hH7 s3_1a); parley_set_side)
    -- 3.3. instantiate t := ξ in H14, from 3.2
    have s3_3 : (deriv G) ξ ≠ 0 := by first | exact (hH14 ξ (by parley_set_side)) | exact ((hH14 ξ (by parley_set_side))).symm | simpa using (hH14 ξ (by parley_set_side)) | exact_mod_cast (hH14 ξ (by parley_set_side)) | (have h := (hH14 ξ (by parley_set_side)); parley_set_side)
    all_goals parley_set_side
  -- 4. obtain ξ: thm:cauchy-mean-value D := E, a := p, b := q, f := F, g := G, from H1, H5, H6, H10, H11, 1, 2
  obtain ⟨ξ, s4a, s4b⟩ := (Parley.Items.Stdlib.Calculus.thm_cauchy_mean_value (f := F) (g := G) (D := E) hH1 (a := p) (b := q) hH5 hH6 hH10 hH11 s1 s2)
  -- 5. mun:in-subset, from H7, 4
  have s5 : ξ ∈ U := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo p q : Set ℝ)) (Y := U) (u := ξ) hH7 s4a) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo p q : Set ℝ)) (Y := U) (u := ξ) hH7 s4a)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo p q : Set ℝ)) (Y := U) (u := ξ) hH7 s4a) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo p q : Set ℝ)) (Y := U) (u := ξ) hH7 s4a) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo p q : Set ℝ)) (Y := U) (u := ξ) hH7 s4a); parley_set_side)
  -- 6. instantiate t := ξ in H14, from 5
  have s6 : (deriv G) ξ ≠ 0 := by first | exact (hH14 ξ (by parley_set_side)) | exact ((hH14 ξ (by parley_set_side))).symm | simpa using (hH14 ξ (by parley_set_side)) | exact_mod_cast (hH14 ξ (by parley_set_side)) | (have h := (hH14 ξ (by parley_set_side)); parley_set_side)
  -- 7. def:interval a := p, b := q, x := p
  have r76_1 : p ≤ p := by parley_order
  have r76_2 : p ≤ q := by parley_set_side
  have s7 : p ∈ (Set.Icc p q : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := p) (a := p) (b := q))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := p) (a := p) (b := q))).mpr (by parley_set_side); parley_set_side)
  -- 8. def:interval a := p, b := q, x := q
  have r81_1 : p ≤ q := by parley_set_side
  have r81_2 : q ≤ q := by parley_order
  have s8 : q ∈ (Set.Icc p q : Set ℝ) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_interval (x := q) (a := p) (b := q))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_interval (x := q) (a := p) (b := q))).mpr (by parley_set_side); parley_set_side)
  -- 9. mun:in-subset, from H6, 7
  have s9 : p ∈ E := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc p q : Set ℝ)) (Y := E) (u := p) hH6 s7) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc p q : Set ℝ)) (Y := E) (u := p) hH6 s7)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc p q : Set ℝ)) (Y := E) (u := p) hH6 s7) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc p q : Set ℝ)) (Y := E) (u := p) hH6 s7) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc p q : Set ℝ)) (Y := E) (u := p) hH6 s7); parley_set_side)
  -- 10. mun:in-subset, from H6, 8
  have s10 : q ∈ E := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc p q : Set ℝ)) (Y := E) (u := q) hH6 s8) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc p q : Set ℝ)) (Y := E) (u := q) hH6 s8)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc p q : Set ℝ)) (Y := E) (u := q) hH6 s8) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc p q : Set ℝ)) (Y := E) (u := q) hH6 s8) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Icc p q : Set ℝ)) (Y := E) (u := q) hH6 s8); parley_set_side)
  -- 11. algebra, from 4
  have r92_5 : G q - G p ≠ 0 := by intro h; exact s3 (by linear_combination (norm := parley_norm) (-1) * h)
  have r92_8 : (deriv G) ξ ≠ 0 := by parley_set_side
  have s11 : (F q - F p) / (G q - G p) = (deriv F) ξ / (deriv G) ξ := by linear_combination (norm := parley_field) ((1) / ((-G p + G q) * ((deriv G) ξ))) * s4b
  -- 12. exhibit, from 4, 11
  have s12 : ∃ ξ ∈ (Set.Ioo p q : Set ℝ), (F q - F p) / (G q - G p) = (deriv F) ξ / (deriv G) ξ := ⟨ξ, by parley_set_side, by parley_set_side⟩
  -- 13. join 3, 12
  have s13a : G p ≠ G q := by parley_set_side
  have s13b : ∃ ξ ∈ (Set.Ioo p q : Set ℝ), (F q - F p) / (G q - G p) = (deriv F) ξ / (deriv G) ξ := by parley_set_side
  exact ⟨by parley_set_side, by parley_set_side⟩

end Parley.Proofs.Wiedijk.Lhopital.CauchyQuotient
