module

public import Geometry
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
public import Mathlib.Data.Set.Defs
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Interval.Finset.Defs
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
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.CrossingTriangle
public import Parley.Stdlib.Geometry.IsoscelesBasePoint
public import Parley.Stdlib.Geometry.OffLineAlong

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.KiteAngles

theorem kite_angles (D : ℂ) (E : ℂ) (F : ℂ) (G : ℂ) (hH5 : LeanBridges.Geometry.Triangle D E F) (hH6 : Complex.im ((D - E) / (F - E)) * Complex.im ((G - E) / (F - E)) < 0) (hH7 : dist E D = dist E G) (hH8 : dist F D = dist F G) :
    EuclideanGeometry.angle E D F = EuclideanGeometry.angle E G F := by
  -- 1. obtain X: axi:plane-separation-crossing A := E, B := F, P := D, Q := G, from H5, H6
  obtain ⟨X, s1a, ⟨s1b, s1c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_plane_separation_crossing (A := E) (B := F) (P := D) (Q := G) hH5.2.1 hH6)
  -- 2. mun:opposite-sides-off-line A := E, B := F, P := D, Q := G, from H6
  have s2 : ¬ G ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_3 (A := E) (B := F) (P := D) (Q := G) hH6)
  -- 3. mun:off-line-apart A := E, B := F, P := G, from H5, 2
  have s3a : G ≠ E := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := E) (B := F) (P := G) hH5.2.1 s2)
  have s3b : G ≠ F := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := E) (B := F) (P := G) hH5.2.1 s2)
  -- 4. mun:between-apart R := X, S := D, T := G, from 1
  have s4a : D ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := X) (S := D) (T := G) s1c)
  have s4b : G ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := X) (S := D) (T := G) s1c)
  -- 5. mun:triangle-off-line P := G, Q := E, R := F, from H5, 2
  have s5 : LeanBridges.Geometry.Triangle G E F := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := G) (Q := E) (R := F) hH5.2.1 s2)
  -- 6. mun:triangle-not-on-line P := D, Q := E, R := F, from H5
  have s6 : ¬ D ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := D) (Q := E) (R := F) hH5)
  -- 7. mun:triangle-not-on-line P := D, Q := F, R := E, from H5
  have s7 : ¬ D ∈ LeanBridges.Geometry.line F E := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := D) (Q := F) (R := E) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_23 D E F] at h; exact h) : LeanBridges.Geometry.Triangle D F E))
  -- 8. mun:triangle-not-on-line P := G, Q := F, R := E, from 5
  have s8 : ¬ G ∈ LeanBridges.Geometry.line F E := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := G) (Q := F) (R := E) (by (have h := s5; rw [LeanBridges.Geometry.triangle_swap_23 G E F] at h; exact h) : LeanBridges.Geometry.Triangle G F E))
  -- 9. mun:on-line-cases P := X, Q := E, R := F, from H5, 1
  have s9 : (((X = E ∨ Sbtw ℝ E X F) ∨ X = F) ∨ Sbtw ℝ E F X) ∨ Sbtw ℝ X E F := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := X) (Q := E) (R := F) hH5.2.1 s1b)
  -- 10. cases, from 9
  rcases s9 with (((hC1 | hC2) | hC3) | hC4) | hC5
  · skip
    -- 10.1. substitute X = E (C1) into line 1
    have s10_1 : Sbtw ℝ D E G := Eq.subst (motive := (fun t : ℂ => Sbtw ℝ D t G)) hC1 s1c
    -- 10.2. mun:on-line-ends A := F, B := E, from H5
    have s10_2 : E ∈ LeanBridges.Geometry.line F E := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := F) (B := E) (Ne.symm hH5.2.1))
    -- 10.3. mun:crossing-triangle E := F, F := E, X := E, from H5, 10.1, 10.2
    have s10_3 : LeanBridges.Geometry.Triangle D G F := by exact (Parley.Stdlib.Geometry.CrossingTriangle.crossing_triangle (D := D) (E := F) (F := E) (G := G) (X := E) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_23 D E F] at h; exact h) : LeanBridges.Geometry.Triangle D F E) s10_2 s10_1 hH5.2.1)
    -- 10.4. calculation
    calc EuclideanGeometry.angle E D F = EuclideanGeometry.angle F D E := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := E) (Q := D) (R := F) (Ne.symm hH5.1) (Ne.symm hH5.2.2.1) hH5.2.1)
      _ = EuclideanGeometry.angle F G E := by exact (Parley.Stdlib.Geometry.IsoscelesBasePoint.isosceles_base_point (D := D) (G := G) (E := F) (X := E) s10_3 hH8 s10_1 (by (have h := hH5; rw [LeanBridges.Geometry.triangle_rot_312 D E F] at h; exact h) : LeanBridges.Geometry.Triangle F D E))
      _ = EuclideanGeometry.angle E G F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := F) (Q := G) (R := E) (Ne.symm s3b) (Ne.symm s3a) (Ne.symm hH5.2.1))
  · skip
    -- 10.5. mun:between-apart R := X, S := E, T := F, from C2
    have s10_5a : E ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := X) (S := E) (T := F) hC2)
    have s10_5b : F ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := X) (S := E) (T := F) hC2)
    -- 10.6. mun:crossing-triangle, from H5, 1, 10.5
    have s10_6 : LeanBridges.Geometry.Triangle D G E := by exact (Parley.Stdlib.Geometry.CrossingTriangle.crossing_triangle (D := D) (E := E) (F := F) (G := G) (X := X) hH5 s1b s1c (Ne.symm s10_5a))
    -- 10.7. mun:between-collinear R := X, S := E, T := F, from C2
    have s10_7 : Collinear ℝ {F, X, E} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := X) (S := E) (T := F) hC2)
    -- 10.8. def:on-line P := X, A := F, B := E, from H5, 10.7
    have s10_8 : X ∈ LeanBridges.Geometry.line F E := ((Parley.Items.Stdlib.Geometry.def_on_line (A := F) (B := E) (P := X) (Ne.symm hH5.2.1))).mpr (by (have h := s10_7; rw [LeanBridges.Geometry.collinear_swap_23 F X E] at h; exact h) : Collinear ℝ {F, E, X})
    -- 10.9. mun:crossing-triangle E := F, F := E, from H5, 1, 10.5, 10.8
    have s10_9 : LeanBridges.Geometry.Triangle D G F := by exact (Parley.Stdlib.Geometry.CrossingTriangle.crossing_triangle (D := D) (E := F) (F := E) (G := G) (X := X) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_23 D E F] at h; exact h) : LeanBridges.Geometry.Triangle D F E) s10_8 s1c (Ne.symm s10_5b))
    -- 10.10. thm:isosceles-base-point, from H7, 1, 10.6
    have r2881_1 : LeanBridges.Geometry.Triangle E D X := (by (have h := (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := D) (Q := E) (R := F) (S := X) hH5 hC2); rw [LeanBridges.Geometry.triangle_swap_12 D E X] at h; exact h) : LeanBridges.Geometry.Triangle E D X)
    have s10_10 : EuclideanGeometry.angle E D X = EuclideanGeometry.angle E G X := by exact (Parley.Stdlib.Geometry.IsoscelesBasePoint.isosceles_base_point (D := D) (G := G) (E := E) (X := X) s10_6 hH7 s1c r2881_1)
    -- 10.11. thm:isosceles-base-point E := F, from H8, 1, 10.9
    have r2885_1 : LeanBridges.Geometry.Triangle F D X := (by (have h := (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := D) (Q := F) (R := E) (S := X) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_23 D E F] at h; exact h) : LeanBridges.Geometry.Triangle D F E) (by (have h := hC2; rw [sbtw_comm (x := E) (y := X) (z := F)] at h; exact h) : Sbtw ℝ F X E)); rw [LeanBridges.Geometry.triangle_swap_12 D F X] at h; exact h) : LeanBridges.Geometry.Triangle F D X)
    have s10_11 : EuclideanGeometry.angle F D X = EuclideanGeometry.angle F G X := by exact (Parley.Stdlib.Geometry.IsoscelesBasePoint.isosceles_base_point (D := D) (G := G) (E := F) (X := X) s10_9 hH8 s1c r2885_1)
    -- 10.12. mun:angle-addition A := E, B := F, C := D, M := X, from C2, H5, 4
    have s10_12 : EuclideanGeometry.angle E D X + EuclideanGeometry.angle X D F = EuclideanGeometry.angle E D F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_addition (A := E) (B := F) (C := D) (M := X) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_rot_231 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E F D) hC2 s4a)
    -- 10.13. mun:angle-addition A := E, B := F, C := G, M := X, from C2, 4, 5
    have s10_13 : EuclideanGeometry.angle E G X + EuclideanGeometry.angle X G F = EuclideanGeometry.angle E G F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_addition (A := E) (B := F) (C := G) (M := X) (by (have h := s5; rw [LeanBridges.Geometry.triangle_rot_231 G E F] at h; exact h) : LeanBridges.Geometry.Triangle E F G) hC2 s4b)
    -- 10.14. mun:angle-turned P := X, Q := D, R := F, from H5, 4, 10.5
    have s10_14 : EuclideanGeometry.angle X D F = EuclideanGeometry.angle F D X := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := X) (Q := D) (R := F) (Ne.symm s4a) (Ne.symm hH5.2.2.1) (Ne.symm s10_5b))
    -- 10.15. mun:angle-turned P := X, Q := G, R := F, from 3, 4, 10.5
    have s10_15 : EuclideanGeometry.angle X G F = EuclideanGeometry.angle F G X := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := X) (Q := G) (R := F) (Ne.symm s4b) (Ne.symm s3b) (Ne.symm s10_5b))
    -- 10.16. algebra, from 10.10, 10.11, 10.12, 10.13, 10.14, 10.15
    linear_combination s10_10 + s10_11 + (-1) * s10_12 + s10_13 + s10_14 + (-1) * s10_15
  · skip
    -- 10.17. substitute X = F (C3) into line 1
    have s10_17 : Sbtw ℝ D F G := Eq.subst (motive := (fun t : ℂ => Sbtw ℝ D t G)) hC3 s1c
    -- 10.18. mun:on-line-ends A := E, B := F, from H5
    have s10_18 : F ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := E) (B := F) hH5.2.1)
    -- 10.19. mun:crossing-triangle X := F, from H5, 10.17, 10.18
    have s10_19 : LeanBridges.Geometry.Triangle D G E := by exact (Parley.Stdlib.Geometry.CrossingTriangle.crossing_triangle (D := D) (E := E) (F := F) (G := G) (X := F) hH5 s10_18 s10_17 (Ne.symm hH5.2.1))
    -- 10.20. thm:isosceles-base-point X := F, from H5, H7, 10.17, 10.19
    exact (Parley.Stdlib.Geometry.IsoscelesBasePoint.isosceles_base_point (D := D) (G := G) (E := E) (X := F) s10_19 hH7 s10_17 (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_12 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E D F))
  · skip
    -- 10.21. mun:between-ends-apart R := F, S := E, T := X, from C4
    have s10_21 : E ≠ X := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := F) (S := E) (T := X) hC4)
    -- 10.22. mun:between-apart R := F, S := E, T := X, from C4
    have s10_22a : E ≠ F := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := F) (S := E) (T := X) hC4)
    have s10_22b : X ≠ F := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := F) (S := E) (T := X) hC4)
    -- 10.23. mun:crossing-triangle, from H5, 1, 10.21
    have s10_23 : LeanBridges.Geometry.Triangle D G E := by exact (Parley.Stdlib.Geometry.CrossingTriangle.crossing_triangle (D := D) (E := E) (F := F) (G := G) (X := X) hH5 s1b s1c (Ne.symm s10_21))
    -- 10.24. mun:between-collinear R := F, S := E, T := X, from C4
    have s10_24 : Collinear ℝ {X, F, E} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := F) (S := E) (T := X) hC4)
    -- 10.25. def:on-line P := X, A := F, B := E, from H5, 10.24
    have s10_25 : X ∈ LeanBridges.Geometry.line F E := ((Parley.Items.Stdlib.Geometry.def_on_line (A := F) (B := E) (P := X) (Ne.symm hH5.2.1))).mpr (by (have h := s10_24; rw [LeanBridges.Geometry.collinear_rot_231 X F E] at h; exact h) : Collinear ℝ {F, E, X})
    -- 10.26. mun:crossing-triangle E := F, F := E, from H5, 1, 10.22, 10.25
    have s10_26 : LeanBridges.Geometry.Triangle D G F := by exact (Parley.Stdlib.Geometry.CrossingTriangle.crossing_triangle (D := D) (E := F) (F := E) (G := G) (X := X) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_23 D E F] at h; exact h) : LeanBridges.Geometry.Triangle D F E) s10_25 s1c s10_22b)
    -- 10.27. thm:isosceles-base-point, from H7, 1, 10.23
    have r2940_1 : ¬ D ∈ LeanBridges.Geometry.line E X := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := E) (B := F) (X := X) (P := D) hH5.2.1 s1b (Ne.symm s10_21) s6)
    have r2940_2 : LeanBridges.Geometry.Triangle E D X := (by (have h := (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := D) (Q := E) (R := X) s10_21 r2940_1); rw [LeanBridges.Geometry.triangle_swap_12 D E X] at h; exact h) : LeanBridges.Geometry.Triangle E D X)
    have s10_27 : EuclideanGeometry.angle E D X = EuclideanGeometry.angle E G X := by exact (Parley.Stdlib.Geometry.IsoscelesBasePoint.isosceles_base_point (D := D) (G := G) (E := E) (X := X) s10_23 hH7 s1c r2940_2)
    -- 10.28. thm:isosceles-base-point E := F, from H8, 1, 10.26
    have r2945_1 : LeanBridges.Geometry.Triangle F D X := (by (have h := (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := D) (Q := F) (R := E) (S := X) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_23 D E F] at h; exact h) : LeanBridges.Geometry.Triangle D F E) hC4); rw [LeanBridges.Geometry.triangle_swap_12 D F X] at h; exact h) : LeanBridges.Geometry.Triangle F D X)
    have s10_28 : EuclideanGeometry.angle F D X = EuclideanGeometry.angle F G X := by exact (Parley.Stdlib.Geometry.IsoscelesBasePoint.isosceles_base_point (D := D) (G := G) (E := F) (X := X) s10_26 hH8 s1c r2945_1)
    -- 10.29. mun:off-line-along A := E, B := F, P := D, from H5, 1, 6, 10.21
    have s10_29 : ¬ D ∈ LeanBridges.Geometry.line E X := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := E) (B := F) (X := X) (P := D) hH5.2.1 s1b (Ne.symm s10_21) s6)
    -- 10.30. mun:triangle-off-line P := D, Q := E, R := X, from 10.21, 10.29
    have s10_30 : LeanBridges.Geometry.Triangle D E X := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := D) (Q := E) (R := X) s10_21 s10_29)
    -- 10.31. mun:off-line-along A := E, B := F, P := G, from H5, 1, 2, 10.21
    have s10_31 : ¬ G ∈ LeanBridges.Geometry.line E X := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := E) (B := F) (X := X) (P := G) hH5.2.1 s1b (Ne.symm s10_21) s2)
    -- 10.32. mun:triangle-off-line P := G, Q := E, R := X, from 10.21, 10.31
    have s10_32 : LeanBridges.Geometry.Triangle G E X := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := G) (Q := E) (R := X) s10_21 s10_31)
    -- 10.33. mun:angle-addition A := E, B := X, C := D, M := F, from C4, H5, 10.30
    have s10_33 : EuclideanGeometry.angle E D F + EuclideanGeometry.angle F D X = EuclideanGeometry.angle E D X := by exact (Parley.Items.Stdlib.Geometry.mun_angle_addition (A := E) (B := X) (C := D) (M := F) (by (have h := s10_30; rw [LeanBridges.Geometry.triangle_rot_231 D E X] at h; exact h) : LeanBridges.Geometry.Triangle E X D) hC4 hH5.2.2.1)
    -- 10.34. mun:angle-addition A := E, B := X, C := G, M := F, from C4, 3, 10.32
    have s10_34 : EuclideanGeometry.angle E G F + EuclideanGeometry.angle F G X = EuclideanGeometry.angle E G X := by exact (Parley.Items.Stdlib.Geometry.mun_angle_addition (A := E) (B := X) (C := G) (M := F) (by (have h := s10_32; rw [LeanBridges.Geometry.triangle_rot_231 G E X] at h; exact h) : LeanBridges.Geometry.Triangle E X G) hC4 s3b)
    -- 10.35. algebra, from 10.27, 10.28, 10.33, 10.34
    linear_combination s10_27 + (-1) * s10_28 + s10_33 + (-1) * s10_34
  · skip
    -- 10.36. mun:between-apart R := E, S := X, T := F, from C5
    have s10_36a : X ≠ E := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := E) (S := X) (T := F) hC5)
    have s10_36b : F ≠ E := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := E) (S := X) (T := F) hC5)
    -- 10.37. mun:between-ends-apart R := E, S := X, T := F, from C5
    have s10_37 : X ≠ F := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := E) (S := X) (T := F) hC5)
    -- 10.38. mun:crossing-triangle, from H5, 1, 10.36
    have s10_38 : LeanBridges.Geometry.Triangle D G E := by exact (Parley.Stdlib.Geometry.CrossingTriangle.crossing_triangle (D := D) (E := E) (F := F) (G := G) (X := X) hH5 s1b s1c s10_36a)
    -- 10.39. mun:between-collinear R := E, S := X, T := F, from C5
    have s10_39 : Collinear ℝ {F, E, X} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := E) (S := X) (T := F) hC5)
    -- 10.40. def:on-line P := X, A := F, B := E, from H5, 10.39
    have s10_40 : X ∈ LeanBridges.Geometry.line F E := ((Parley.Items.Stdlib.Geometry.def_on_line (A := F) (B := E) (P := X) (Ne.symm hH5.2.1))).mpr s10_39
    -- 10.41. mun:crossing-triangle E := F, F := E, from H5, 1, 10.37, 10.40
    have s10_41 : LeanBridges.Geometry.Triangle D G F := by exact (Parley.Stdlib.Geometry.CrossingTriangle.crossing_triangle (D := D) (E := F) (F := E) (G := G) (X := X) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_23 D E F] at h; exact h) : LeanBridges.Geometry.Triangle D F E) s10_40 s1c s10_37)
    -- 10.42. thm:isosceles-base-point, from H7, 1, 10.38
    have r2991_1 : LeanBridges.Geometry.Triangle E D X := (by (have h := (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := D) (Q := E) (R := F) (S := X) hH5 (by (have h := hC5; rw [sbtw_comm (x := X) (y := E) (z := F)] at h; exact h) : Sbtw ℝ F E X)); rw [LeanBridges.Geometry.triangle_swap_12 D E X] at h; exact h) : LeanBridges.Geometry.Triangle E D X)
    have s10_42 : EuclideanGeometry.angle E D X = EuclideanGeometry.angle E G X := by exact (Parley.Stdlib.Geometry.IsoscelesBasePoint.isosceles_base_point (D := D) (G := G) (E := E) (X := X) s10_38 hH7 s1c r2991_1)
    -- 10.43. thm:isosceles-base-point E := F, from H8, 1, 10.41
    have r2995_1 : ¬ D ∈ LeanBridges.Geometry.line F X := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := F) (B := E) (X := X) (P := D) (Ne.symm hH5.2.1) s10_40 s10_37 s7)
    have r2995_2 : LeanBridges.Geometry.Triangle F D X := (by (have h := (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := D) (Q := F) (R := X) (Ne.symm s10_37) r2995_1); rw [LeanBridges.Geometry.triangle_swap_12 D F X] at h; exact h) : LeanBridges.Geometry.Triangle F D X)
    have s10_43 : EuclideanGeometry.angle F D X = EuclideanGeometry.angle F G X := by exact (Parley.Stdlib.Geometry.IsoscelesBasePoint.isosceles_base_point (D := D) (G := G) (E := F) (X := X) s10_41 hH8 s1c r2995_2)
    -- 10.44. mun:off-line-along A := F, B := E, P := D, from H5, 7, 10.37, 10.40
    have s10_44 : ¬ D ∈ LeanBridges.Geometry.line F X := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := F) (B := E) (X := X) (P := D) (Ne.symm hH5.2.1) s10_40 s10_37 s7)
    -- 10.45. mun:triangle-off-line P := D, Q := F, R := X, from 10.37, 10.44
    have s10_45 : LeanBridges.Geometry.Triangle D F X := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := D) (Q := F) (R := X) (Ne.symm s10_37) s10_44)
    -- 10.46. mun:off-line-along A := F, B := E, P := G, from H5, 8, 10.37, 10.40
    have s10_46 : ¬ G ∈ LeanBridges.Geometry.line F X := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := F) (B := E) (X := X) (P := G) (Ne.symm hH5.2.1) s10_40 s10_37 s8)
    -- 10.47. mun:triangle-off-line P := G, Q := F, R := X, from 10.37, 10.46
    have s10_47 : LeanBridges.Geometry.Triangle G F X := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := G) (Q := F) (R := X) (Ne.symm s10_37) s10_46)
    -- 10.48. mun:angle-addition A := X, B := F, C := D, M := E, from C5, H5, 10.45
    have s10_48 : EuclideanGeometry.angle X D E + EuclideanGeometry.angle E D F = EuclideanGeometry.angle X D F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_addition (A := X) (B := F) (C := D) (M := E) (by (have h := s10_45; rw [LeanBridges.Geometry.triangle_swap_13 D F X] at h; exact h) : LeanBridges.Geometry.Triangle X F D) hC5 hH5.1)
    -- 10.49. mun:angle-addition A := X, B := F, C := G, M := E, from C5, 3, 10.47
    have s10_49 : EuclideanGeometry.angle X G E + EuclideanGeometry.angle E G F = EuclideanGeometry.angle X G F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_addition (A := X) (B := F) (C := G) (M := E) (by (have h := s10_47; rw [LeanBridges.Geometry.triangle_swap_13 G F X] at h; exact h) : LeanBridges.Geometry.Triangle X F G) hC5 s3a)
    -- 10.50. mun:angle-turned P := X, Q := D, R := E, from H5, 4, 10.36
    have s10_50 : EuclideanGeometry.angle X D E = EuclideanGeometry.angle E D X := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := X) (Q := D) (R := E) (Ne.symm s4a) (Ne.symm hH5.1) s10_36a)
    -- 10.51. mun:angle-turned P := X, Q := G, R := E, from 3, 4, 10.36
    have s10_51 : EuclideanGeometry.angle X G E = EuclideanGeometry.angle E G X := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := X) (Q := G) (R := E) (Ne.symm s4b) (Ne.symm s3a) s10_36a)
    -- 10.52. mun:angle-turned P := X, Q := D, R := F, from H5, 4, 10.37
    have s10_52 : EuclideanGeometry.angle X D F = EuclideanGeometry.angle F D X := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := X) (Q := D) (R := F) (Ne.symm s4a) (Ne.symm hH5.2.2.1) s10_37)
    -- 10.53. mun:angle-turned P := X, Q := G, R := F, from 3, 4, 10.37
    have s10_53 : EuclideanGeometry.angle X G F = EuclideanGeometry.angle F G X := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := X) (Q := G) (R := F) (Ne.symm s4b) (Ne.symm s3b) s10_37)
    -- 10.54. algebra, from 10.42, 10.43, 10.48, 10.49, 10.50, 10.51, 10.52, 10.53
    linear_combination (-1) * s10_42 + s10_43 + s10_48 + (-1) * s10_49 + (-1) * s10_50 + s10_51 + s10_52 + (-1) * s10_53

end Parley.Stdlib.Geometry.KiteAngles
