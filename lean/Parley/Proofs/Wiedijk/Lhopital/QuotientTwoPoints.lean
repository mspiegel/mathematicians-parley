module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import SetTactics
public import Tactics
public import Batteries.Tactic.Init
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
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sets
public import Parley.Proofs.Wiedijk.Lhopital.CauchyQuotient

/-! Written from proofs/wiedijk/lhopital.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Lhopital.QuotientTwoPoints

set_option maxHeartbeats 800000 in
theorem quotient_two_points (a : ℝ) (b : ℝ) (u : ℝ) (hH3 : u ∈ (Set.Ioo a b : Set ℝ)) (v : ℝ) (hH4 : v ∈ (Set.Ioo a b : Set ℝ)) (hH5 : v ≠ u) (F : ℝ → ℝ) (hH6 : Set.MapsTo F (Set.Ioo a b : Set ℝ) (Set.univ : Set ℝ)) (G : ℝ → ℝ) (hH7 : Set.MapsTo G (Set.Ioo a b : Set ℝ) (Set.univ : Set ℝ)) (hH8 : ContinuousOn F (Set.Ioo a b : Set ℝ)) (hH9 : ContinuousOn G (Set.Ioo a b : Set ℝ)) (hH10 : ∀ x ∈ ((Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ)), (Set.Ioo a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ F x) (hH11 : ∀ x ∈ ((Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ)), (Set.Ioo a b : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ G x) (hH12 : ∀ t ∈ (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ), (deriv G) t ≠ 0) :
    G u ≠ G v ∧ (∃ ξ ∈ (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ), abs (ξ - u) < abs (v - u) ∧ (F v - F u) / (G v - G u) = (deriv F) ξ / (deriv G) ξ) := by
  -- 1. mun:open-interval-real
  have s1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b))
  -- 2. mun:difference-subset
  have s2 : (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := (Set.Ioo a b : Set ℝ)) (Y := ({u} : Set ℝ)))
  -- 3. mun:unequal-cases x := v, y := u, from H5
  have s3 : v < u ∨ u < v := by first | exact ((Parley.Items.Stdlib.Numbers.mun_unequal_cases (x := v) (y := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Numbers.mun_unequal_cases (x := v) (y := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_unequal_cases (x := v) (y := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_unequal_cases (x := v) (y := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_unequal_cases (x := v) (y := u))).mp (by parley_set_side); parley_set_side)
  -- 4. cases, from 3
  have s4a_all : G u ≠ G v ∧ (∃ ξ ∈ (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ), abs (ξ - u) < abs (v - u) ∧ (F v - F u) / (G v - G u) = (deriv F) ξ / (deriv G) ξ) := by
    rcases s3 with hC1 | hC2
    · skip
      -- 4.1. mun:closed-within-open p := v, q := u, from H3, H4
      have s4_1 : (Set.Icc v u : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_closed_within_open (p := v) (q := u) (a := a) (b := b) hH4 hH3)
      -- 4.2. mun:subset-transitive X := (v, u), Y := [v, u], Z := (a, b), from 4.1
      have r147_1 : (Set.Ioo v u : Set ℝ) ⊆ (Set.Icc v u : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := v) (b := u))
      have s4_2 : (Set.Ioo v u : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := (Set.Ioo v u : Set ℝ)) (Y := (Set.Icc v u : Set ℝ)) (Z := (Set.Ioo a b : Set ℝ)) (by parley_set_side) s4_1)
      -- 4.3. contradiction
      have s4_3 : ¬ u ∈ (Set.Ioo v u : Set ℝ) := by
        by_contra hc_hS1
        have hS1 : u ∈ (Set.Ioo v u : Set ℝ) := by parley_suppose hc_hS1
        -- 4.3.1. def:open-interval a := v, b := u, x := u, from S1
        have s4_3_1 : u < u := by first | linarith [(((Parley.Items.Stdlib.Calculus.def_open_interval (x := u) (a := v) (b := u))).mp (by parley_set_side)).2] | (have h := (((Parley.Items.Stdlib.Calculus.def_open_interval (x := u) (a := v) (b := u))).mp (by parley_set_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Calculus.def_open_interval (x := u) (a := v) (b := u))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Calculus.def_open_interval (x := u) (a := v) (b := u))).mp (by parley_set_side)).2; parley_set_side)
        -- 4.3.2. inequalities
        have s4_3_2 : ¬ u < u := by parley_set_side
        all_goals parley_set_side
      -- 4.4. mun:subset-into-difference a := u, X := (a, b), Y := (v, u), from 4.2, 4.3
      have s4_4 : (Set.Ioo v u : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Ioo v u : Set ℝ)) (a := u) s4_2 s4_3) | exact ((Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Ioo v u : Set ℝ)) (a := u) s4_2 s4_3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Ioo v u : Set ℝ)) (a := u) s4_2 s4_3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Ioo v u : Set ℝ)) (a := u) s4_2 s4_3) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Ioo v u : Set ℝ)) (a := u) s4_2 s4_3); parley_set_side)
      -- 4.5. thm:cauchy-quotient E := (a, b), U := (a, b) ∖ {u}, p := v, q := u, from C1, H10, H11, H12, 1, 2, 4.1, 4.4
      have r164_1 : ContinuousOn F (Set.Icc v u : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_continuous_on_part (f := F) (D := (Set.Ioo a b : Set ℝ)) (S := (Set.Icc v u : Set ℝ)) s1 s4_1 hH8)
      have r164_2 : ContinuousOn G (Set.Icc v u : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_continuous_on_part (f := G) (D := (Set.Ioo a b : Set ℝ)) (S := (Set.Icc v u : Set ℝ)) s1 s4_1 hH9)
      have s4_5a : G v ≠ G u := by exact (Parley.Proofs.Wiedijk.Lhopital.CauchyQuotient.cauchy_quotient (E := (Set.Ioo a b : Set ℝ)) s1 (U := (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ)) s2 (p := v) (q := u) hC1 s4_1 s4_4 (F := F) (by parley_set_side) (G := G) (by parley_set_side) (by parley_set_side) (by parley_set_side) hH10 hH11 hH12).1
      have s4_5b : ∃ ξ ∈ (Set.Ioo v u : Set ℝ), (F u - F v) / (G u - G v) = (deriv F) ξ / (deriv G) ξ := by exact (Parley.Proofs.Wiedijk.Lhopital.CauchyQuotient.cauchy_quotient (E := (Set.Ioo a b : Set ℝ)) s1 (U := (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ)) s2 (p := v) (q := u) hC1 s4_1 s4_4 (F := F) (by parley_set_side) (G := G) (by parley_set_side) (by parley_set_side) (by parley_set_side) hH10 hH11 hH12).2
      -- 4.6. restate 4.5
      have s4_6 : G v ≠ G u := by parley_set_side
      -- 4.7. inequalities
      have s4_7 : G u ≠ G v := by parley_set_side
      -- 4.8. obtain ξ from line 4.5
      obtain ⟨ξ, s4_8a, s4_8b⟩ := s4_5b
      -- 4.9. mun:in-subset, from 4.4, 4.8
      have s4_9 : ξ ∈ (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo v u : Set ℝ)) (Y := (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ)) (u := ξ) s4_4 s4_8a)
      -- 4.10. algebra, from 4.8
      have r186_5 : G u - G v ≠ 0 := by intro h; exact s4_6 (by linear_combination (norm := parley_norm) (-1) * h)
      have r186_6 : G v - G u ≠ 0 := by intro h; exact s4_6 (by linear_combination (norm := parley_norm) h)
      have r186_9 : (deriv G) ξ ≠ 0 := by first | exact (hH12 ξ (by parley_set_side)) | exact ((hH12 ξ (by parley_set_side))).symm | simpa using (hH12 ξ (by parley_set_side)) | exact_mod_cast (hH12 ξ (by parley_set_side)) | (have h := (hH12 ξ (by parley_set_side)); parley_set_side)
      have s4_10 : (F v - F u) / (G v - G u) = (deriv F) ξ / (deriv G) ξ := by linear_combination (norm := parley_field) s4_8b
      -- 4.11. def:open-interval a := v, b := u, x := ξ, from 4.8
      have s4_11a : v < ξ := by first | linarith [(((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := v) (b := u))).mp (by parley_set_side)).1.2] | (have h := (((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := v) (b := u))).mp (by parley_set_side)).1.2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := v) (b := u))).mp (by parley_set_side)).1.2 | (have h := (((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := v) (b := u))).mp (by parley_set_side)).1.2; parley_set_side)
      have s4_11b : ξ < u := by first | linarith [(((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := v) (b := u))).mp (by parley_set_side)).2] | (have h := (((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := v) (b := u))).mp (by parley_set_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := v) (b := u))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := v) (b := u))).mp (by parley_set_side)).2; parley_set_side)
      -- 4.12. inequalities
      have s4_12 : -(ξ - u) < -(v - u) := by parley_order
      -- 4.13. calculation
      have r208_1 : ξ - u < 0 := by parley_set_side
      have r208_2 : v - u < 0 := by parley_set_side
      have s4_13 : abs (ξ - u) < abs (v - u) := by
        calc abs (ξ - u) = -(ξ - u) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_2 (x := ξ - u)) (by parley_set_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := ξ - u)) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := ξ - u)) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_2 (x := ξ - u)) (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_2 (x := ξ - u)) (by parley_set_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := ξ - u)) (by parley_set_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := ξ - u)) (by parley_set_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := ξ - u)) (by parley_set_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := ξ - u)) (by parley_set_side); parley_set_side)
          _ < -(v - u) := by parley_set_side
          _ = abs (v - u) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_2 (x := v - u)) (by parley_set_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := v - u)) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := v - u)) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_2 (x := v - u)) (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_2 (x := v - u)) (by parley_set_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := v - u)) (by parley_set_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := v - u)) (by parley_set_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := v - u)) (by parley_set_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := v - u)) (by parley_set_side); parley_set_side)
      -- 4.14. exhibit, from 4.9, 4.10, 4.13
      have s4_14 : ∃ ξ ∈ (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ), abs (ξ - u) < abs (v - u) ∧ (F v - F u) / (G v - G u) = (deriv F) ξ / (deriv G) ξ := ⟨ξ, by parley_set_side, ⟨by parley_set_side, by parley_set_side⟩⟩
      -- 4.15. join 4.7, 4.14
      have s4_15a : G u ≠ G v := by parley_set_side
      have s4_15b : ∃ ξ ∈ (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ), abs (ξ - u) < abs (v - u) ∧ (F v - F u) / (G v - G u) = (deriv F) ξ / (deriv G) ξ := by parley_set_side
      all_goals parley_set_side
    · skip
      -- 4.16. mun:closed-within-open p := u, q := v, from H3, H4
      have s4_16 : (Set.Icc u v : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_closed_within_open (p := u) (q := v) (a := a) (b := b) hH3 hH4)
      -- 4.17. mun:subset-transitive X := (u, v), Y := [u, v], Z := (a, b), from 4.16
      have r229_1 : (Set.Ioo u v : Set ℝ) ⊆ (Set.Icc u v : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := u) (b := v))
      have s4_17 : (Set.Ioo u v : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := (Set.Ioo u v : Set ℝ)) (Y := (Set.Icc u v : Set ℝ)) (Z := (Set.Ioo a b : Set ℝ)) (by parley_set_side) s4_16)
      -- 4.18. contradiction
      have s4_18 : ¬ u ∈ (Set.Ioo u v : Set ℝ) := by
        by_contra hc_hS2
        have hS2 : u ∈ (Set.Ioo u v : Set ℝ) := by parley_suppose hc_hS2
        -- 4.18.1. def:open-interval a := u, b := v, x := u, from S2
        have s4_18_1 : u < u := by first | linarith [(((Parley.Items.Stdlib.Calculus.def_open_interval (x := u) (a := u) (b := v))).mp (by parley_set_side)).1.2] | (have h := (((Parley.Items.Stdlib.Calculus.def_open_interval (x := u) (a := u) (b := v))).mp (by parley_set_side)).1.2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Calculus.def_open_interval (x := u) (a := u) (b := v))).mp (by parley_set_side)).1.2 | (have h := (((Parley.Items.Stdlib.Calculus.def_open_interval (x := u) (a := u) (b := v))).mp (by parley_set_side)).1.2; parley_set_side)
        -- 4.18.2. inequalities
        have s4_18_2 : ¬ u < u := by parley_set_side
        all_goals parley_set_side
      -- 4.19. mun:subset-into-difference a := u, X := (a, b), Y := (u, v), from 4.17, 4.18
      have s4_19 : (Set.Ioo u v : Set ℝ) ⊆ (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Ioo u v : Set ℝ)) (a := u) s4_17 s4_18) | exact ((Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Ioo u v : Set ℝ)) (a := u) s4_17 s4_18)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Ioo u v : Set ℝ)) (a := u) s4_17 s4_18) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Ioo u v : Set ℝ)) (a := u) s4_17 s4_18) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := (Set.Ioo a b : Set ℝ)) (Y := (Set.Ioo u v : Set ℝ)) (a := u) s4_17 s4_18); parley_set_side)
      -- 4.20. thm:cauchy-quotient E := (a, b), U := (a, b) ∖ {u}, p := u, q := v, from C2, H10, H11, H12, 1, 2, 4.16, 4.19
      have r246_1 : ContinuousOn F (Set.Icc u v : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_continuous_on_part (f := F) (D := (Set.Ioo a b : Set ℝ)) (S := (Set.Icc u v : Set ℝ)) s1 s4_16 hH8)
      have r246_2 : ContinuousOn G (Set.Icc u v : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_continuous_on_part (f := G) (D := (Set.Ioo a b : Set ℝ)) (S := (Set.Icc u v : Set ℝ)) s1 s4_16 hH9)
      have s4_20a : G u ≠ G v := by exact (Parley.Proofs.Wiedijk.Lhopital.CauchyQuotient.cauchy_quotient (E := (Set.Ioo a b : Set ℝ)) s1 (U := (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ)) s2 (p := u) (q := v) hC2 s4_16 s4_19 (F := F) (by parley_set_side) (G := G) (by parley_set_side) (by parley_set_side) (by parley_set_side) hH10 hH11 hH12).1
      have s4_20b : ∃ ξ ∈ (Set.Ioo u v : Set ℝ), (F v - F u) / (G v - G u) = (deriv F) ξ / (deriv G) ξ := by exact (Parley.Proofs.Wiedijk.Lhopital.CauchyQuotient.cauchy_quotient (E := (Set.Ioo a b : Set ℝ)) s1 (U := (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ)) s2 (p := u) (q := v) hC2 s4_16 s4_19 (F := F) (by parley_set_side) (G := G) (by parley_set_side) (by parley_set_side) (by parley_set_side) hH10 hH11 hH12).2
      -- 4.21. restate 4.20
      have s4_21 : G u ≠ G v := by parley_set_side
      -- 4.22. obtain ξ from line 4.20
      obtain ⟨ξ, s4_22a, s4_22b⟩ := s4_20b
      -- 4.23. mun:in-subset, from 4.19, 4.22
      have s4_23 : ξ ∈ (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ) := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := (Set.Ioo u v : Set ℝ)) (Y := (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ)) (u := ξ) s4_19 s4_22a)
      -- 4.24. def:open-interval a := u, b := v, x := ξ, from 4.22
      have s4_24a : u < ξ := by first | linarith [(((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := u) (b := v))).mp (by parley_set_side)).1.2] | (have h := (((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := u) (b := v))).mp (by parley_set_side)).1.2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := u) (b := v))).mp (by parley_set_side)).1.2 | (have h := (((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := u) (b := v))).mp (by parley_set_side)).1.2; parley_set_side)
      have s4_24b : ξ < v := by first | linarith [(((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := u) (b := v))).mp (by parley_set_side)).2] | (have h := (((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := u) (b := v))).mp (by parley_set_side)).2; push_cast at h; linarith) | exact_mod_cast (((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := u) (b := v))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Calculus.def_open_interval (x := ξ) (a := u) (b := v))).mp (by parley_set_side)).2; parley_set_side)
      -- 4.25. inequalities
      have s4_25 : ξ - u > 0 := by parley_order
      -- 4.26. inequalities
      have s4_26 : v - u > 0 := by parley_order
      -- 4.27. inequalities
      have s4_27 : ξ - u < v - u := by parley_order
      -- 4.28. calculation
      have r281_1 : ξ - u ≥ 0 := by parley_set_side
      have r281_2 : v - u ≥ 0 := by parley_set_side
      have s4_28 : abs (ξ - u) < abs (v - u) := by
        calc abs (ξ - u) = ξ - u := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := ξ - u)) (by parley_set_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := ξ - u)) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := ξ - u)) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := ξ - u)) (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := ξ - u)) (by parley_set_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := ξ - u)) (by parley_set_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := ξ - u)) (by parley_set_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := ξ - u)) (by parley_set_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := ξ - u)) (by parley_set_side); parley_set_side)
          _ < v - u := by parley_set_side
          _ = abs (v - u) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_1 (x := v - u)) (by parley_set_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := v - u)) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := v - u)) (by parley_set_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_1 (x := v - u)) (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_1 (x := v - u)) (by parley_set_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := v - u)) (by parley_set_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := v - u)) (by parley_set_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := v - u)) (by parley_set_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := v - u)) (by parley_set_side); parley_set_side)
      -- 4.29. exhibit, from 4.22, 4.23, 4.28
      have s4_29 : ∃ ξ ∈ (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ), abs (ξ - u) < abs (v - u) ∧ (F v - F u) / (G v - G u) = (deriv F) ξ / (deriv G) ξ := ⟨ξ, by parley_set_side, ⟨by parley_set_side, by parley_set_side⟩⟩
      -- 4.30. join 4.21, 4.29
      have s4_30a : G u ≠ G v := by parley_set_side
      have s4_30b : ∃ ξ ∈ (Set.Ioo a b : Set ℝ) \ ({u} : Set ℝ), abs (ξ - u) < abs (v - u) ∧ (F v - F u) / (G v - G u) = (deriv F) ξ / (deriv G) ξ := by parley_set_side
      all_goals parley_set_side
  obtain ⟨s4a, s4b⟩ := s4a_all
  exact ⟨by parley_set_side, by parley_set_side⟩

end Parley.Proofs.Wiedijk.Lhopital.QuotientTwoPoints
