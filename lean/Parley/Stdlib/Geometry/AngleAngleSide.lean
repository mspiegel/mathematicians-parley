module

public import Geometry
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.ExteriorAngleGreaterOther
public import Parley.Stdlib.Geometry.RayPoint

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.AngleAngleSide

theorem angle_angle_side (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (E : ℂ) (F : ℂ) (hH7 : LeanBridges.Geometry.Triangle A B C) (hH8 : LeanBridges.Geometry.Triangle D E F) (hH9 : EuclideanGeometry.angle C A B = EuclideanGeometry.angle F D E) (hH10 : EuclideanGeometry.angle A B C = EuclideanGeometry.angle D E F) (hH11 : dist B C = dist E F) :
    (dist A B = dist D E ∧ dist B C = dist E F ∧ dist C A = dist F D ∧ EuclideanGeometry.angle A B C = EuclideanGeometry.angle D E F ∧ EuclideanGeometry.angle B C A = EuclideanGeometry.angle E F D ∧ EuclideanGeometry.angle C A B = EuclideanGeometry.angle F D E) := by
  -- 1. axi:distance-positive P := B, Q := A, from H7
  have s1 : dist B A > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := B) (Q := A) (Ne.symm hH7.1))
  -- 2. obtain G: mun:ray-point A := E, B := D, C := F, r := |BA|, from H8, 1
  obtain ⟨G, s2a, ⟨⟨s2b, s2c⟩, s2d⟩⟩ := (Parley.Stdlib.Geometry.RayPoint.ray_point (A := E) (B := D) (C := F) (r := dist B A) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E D F) s1)
  -- 3. mun:same-side-off-line A := E, B := F, P := G, Q := D, from 2
  have s3 : ¬ G ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := E) (B := F) (P := G) (Q := D) s2c)
  -- 4. mun:off-line-apart A := E, B := F, P := G, from H8, 3
  have s4a : G ≠ E := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := E) (B := F) (P := G) hH8.2.1 s3)
  have s4b : G ≠ F := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := E) (B := F) (P := G) hH8.2.1 s3)
  -- 5. mun:triangle-off-line P := G, Q := E, R := F, from H8, 3
  have s5 : LeanBridges.Geometry.Triangle G E F := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := G) (Q := E) (R := F) hH8.2.1 s3)
  -- 6. restate 2
  have s6 : dist A B = dist G E := by exact (by (have h := s2d.symm; rw [dist_comm B A, dist_comm E G] at h; exact h) : dist A B = dist G E)
  -- 7. calculation
  have s7 : EuclideanGeometry.angle A B C = EuclideanGeometry.angle G E F := by
    calc EuclideanGeometry.angle A B C = EuclideanGeometry.angle D E F := hH10
      _ = EuclideanGeometry.angle F E D := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := F) (Q := E) (R := D) (Ne.symm hH8.2.1) hH8.1 (Ne.symm hH8.2.2.1)).symm
      _ = EuclideanGeometry.angle F E G := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := E) (Q := D) (R := F) (X := G) s2b s2c).symm
      _ = EuclideanGeometry.angle G E F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := G) (Q := E) (R := F) s4a (Ne.symm hH8.2.1) s4b).symm
  -- 8. axi:side-angle-side P′ := G, Q′ := E, R′ := F, from H7, H11, 5, 6, 7
  have s8 : dist A B = dist G E ∧ dist B C = dist E F ∧ dist C A = dist F G ∧ EuclideanGeometry.angle A B C = EuclideanGeometry.angle G E F ∧ EuclideanGeometry.angle B C A = EuclideanGeometry.angle E F G ∧ EuclideanGeometry.angle C A B = EuclideanGeometry.angle F G E := by exact (Parley.Items.Stdlib.Geometry.axi_side_angle_side (P := A) (P' := G) (Q := B) (Q' := E) (R := C) (R' := F) hH7 s5 s6 s7 hH11)
  -- 9. calculation
  have s9 : EuclideanGeometry.angle F G E = EuclideanGeometry.angle F D E := by
    calc EuclideanGeometry.angle F G E = EuclideanGeometry.angle C A B := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := G) (Q := B) (Q' := E) (R := C) (R' := F) hH7 s5)).mp s8).2.symm
      _ = EuclideanGeometry.angle F D E := hH9
  -- 10. mun:on-line-ends A := E, B := F, from H8
  have s10 : E ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := E) (B := F) hH8.2.1)
  -- 11. contradiction
  have s11 : G = D := by
    by_contra (hS1 : G ≠ D)
    -- 11.1. mun:on-line-cases P := G, Q := E, R := D, from H8, 2
    have s11_1 : (((G = E ∨ Sbtw ℝ E G D) ∨ G = D) ∨ Sbtw ℝ E D G) ∨ Sbtw ℝ G E D := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := G) (Q := E) (R := D) (Ne.symm hH8.1) s2b)
    -- 11.2. cases, from 11.1
    have s11_2 : EuclideanGeometry.angle F G E ≠ EuclideanGeometry.angle F D E := by
      rcases s11_1 with (((hC1 | hC2) | hC3) | hC4) | hC5
      · skip
        -- 11.2.1. restate 4
        have s11_2_1 : G ≠ E := by exact s4a
        exact absurd hC1 s11_2_1
      · skip
        -- 11.2.2. mun:triangle-on-side P := F, Q := D, R := E, S := G, from C2, H8
        have s11_2_2 : LeanBridges.Geometry.Triangle F D G := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := F) (Q := D) (R := E) (S := G) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_rot_312 D E F] at h; exact h) : LeanBridges.Geometry.Triangle F D E) (by (have h := hC2; rw [sbtw_comm (x := E) (y := G) (z := D)] at h; exact h) : Sbtw ℝ D G E))
        -- 11.2.3. thm:exterior-angle-greater-other A := F, B := D, C := G, D := E, from C2, 11.2.2
        have r2629_1 : LeanBridges.Geometry.Triangle F G E := (by (have h := (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := F) (Q := E) (R := D) (S := G) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_13 D E F] at h; exact h) : LeanBridges.Geometry.Triangle F E D) hC2); rw [LeanBridges.Geometry.triangle_swap_23 F E G] at h; exact h) : LeanBridges.Geometry.Triangle F G E)
        have s11_2_3 : EuclideanGeometry.angle F G E > EuclideanGeometry.angle F D G := by exact (Parley.Stdlib.Geometry.ExteriorAngleGreaterOther.exterior_angle_greater_other (A := F) (B := D) (C := G) (D := E) s11_2_2 (by (have h := hC2; rw [sbtw_comm (x := E) (y := G) (z := D)] at h; exact h) : Sbtw ℝ D G E) r2629_1)
        -- 11.2.4. mun:angle-along-segment P := D, Q := E, S := G, R := F, from C2, H8, 4
        have s11_2_4 : EuclideanGeometry.angle G D F = EuclideanGeometry.angle E D F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := D) (Q := E) (R := F) (S := G) (by (have h := hC2; rw [sbtw_comm (x := E) (y := G) (z := D)] at h; exact h) : Sbtw ℝ D G E) (Ne.symm hH8.2.2.1) (Ne.symm s4b) (Ne.symm hH8.2.1))
        -- 11.2.5. calculation
        have s11_2_5 : EuclideanGeometry.angle F G E > EuclideanGeometry.angle F D E := by
          calc EuclideanGeometry.angle F G E > EuclideanGeometry.angle F D G := s11_2_3
            _ = EuclideanGeometry.angle G D F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := F) (Q := D) (R := G) (Ne.symm hH8.2.2.1) hS1 (Ne.symm s4b))
            _ = EuclideanGeometry.angle E D F := s11_2_4
            _ = EuclideanGeometry.angle F D E := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := E) (Q := D) (R := F) (Ne.symm hH8.1) (Ne.symm hH8.2.2.1) hH8.2.1)
        -- 11.2.6. inequalities
        exact ne_of_gt (by linarith only [s11_2_5])
      · skip
        -- 11.2.7. restate S1
        have s11_2_7 : G ≠ D := by exact hS1
        exact absurd hC3 s11_2_7
      · skip
        -- 11.2.8. mun:triangle-on-side P := F, Q := G, R := E, S := D, from C4, 5
        have s11_2_8 : LeanBridges.Geometry.Triangle F G D := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := F) (Q := G) (R := E) (S := D) (by (have h := s5; rw [LeanBridges.Geometry.triangle_rot_312 G E F] at h; exact h) : LeanBridges.Geometry.Triangle F G E) (by (have h := hC4; rw [sbtw_comm (x := E) (y := D) (z := G)] at h; exact h) : Sbtw ℝ G D E))
        -- 11.2.9. thm:exterior-angle-greater-other A := F, B := G, C := D, D := E, from C4, H8, 11.2.8
        have s11_2_9 : EuclideanGeometry.angle F D E > EuclideanGeometry.angle F G D := by exact (Parley.Stdlib.Geometry.ExteriorAngleGreaterOther.exterior_angle_greater_other (A := F) (B := G) (C := D) (D := E) s11_2_8 (by (have h := hC4; rw [sbtw_comm (x := E) (y := D) (z := G)] at h; exact h) : Sbtw ℝ G D E) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_rot_312 D E F] at h; exact h) : LeanBridges.Geometry.Triangle F D E))
        -- 11.2.10. mun:angle-along-segment P := G, Q := E, S := D, R := F, from C4, H8, 4
        have s11_2_10 : EuclideanGeometry.angle D G F = EuclideanGeometry.angle E G F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := G) (Q := E) (R := F) (S := D) (by (have h := hC4; rw [sbtw_comm (x := E) (y := D) (z := G)] at h; exact h) : Sbtw ℝ G D E) (Ne.symm s4b) (Ne.symm hH8.2.2.1) (Ne.symm hH8.2.1))
        -- 11.2.11. calculation
        have s11_2_11 : EuclideanGeometry.angle F D E > EuclideanGeometry.angle F G E := by
          calc EuclideanGeometry.angle F D E > EuclideanGeometry.angle F G D := s11_2_9
            _ = EuclideanGeometry.angle D G F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := F) (Q := G) (R := D) (Ne.symm s4b) (Ne.symm hS1) (Ne.symm hH8.2.2.1))
            _ = EuclideanGeometry.angle E G F := s11_2_10
            _ = EuclideanGeometry.angle F G E := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := E) (Q := G) (R := F) (Ne.symm s4a) (Ne.symm s4b) hH8.2.1)
        -- 11.2.12. inequalities
        exact ne_of_lt (by linarith only [s11_2_11])
      · skip
        -- 11.2.13. mun:segment-across-line A := E, B := F, P := G, Q := D, M := E, from C5, H8, 3, 10
        have s11_2_13 : Complex.im ((G - E) / (F - E)) * Complex.im ((D - E) / (F - E)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := E) (B := F) (M := E) (P := G) (Q := D) hH8.2.1 s10 s3 hC5)
        -- 11.2.14. mun:same-not-opposite A := E, B := F, P := G, Q := D, from 2
        have s11_2_14 : ¬ Complex.im ((G - E) / (F - E)) * Complex.im ((D - E) / (F - E)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_not_opposite (A := E) (B := F) (P := G) (Q := D) s2c)
        exact absurd s11_2_13 s11_2_14
    -- 11.3. restate 11.2
    have s11_3 : EuclideanGeometry.angle F G E ≠ EuclideanGeometry.angle F D E := by exact s11_2
    exact s11_3 s9
  -- 12. substitute G = D (line 11) into line 8
  exact Eq.subst (motive := (fun t : ℂ => dist A B = dist t E ∧ dist B C = dist E F ∧ dist C A = dist F t ∧ EuclideanGeometry.angle A B C = EuclideanGeometry.angle t E F ∧ EuclideanGeometry.angle B C A = EuclideanGeometry.angle E F t ∧ EuclideanGeometry.angle C A B = EuclideanGeometry.angle F t E)) s11 s8

end Parley.Stdlib.Geometry.AngleAngleSide
