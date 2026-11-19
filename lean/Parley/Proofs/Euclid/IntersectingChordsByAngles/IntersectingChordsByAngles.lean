module

public import Geometry
public import Mathlib.Algebra.Group.Semigroup
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
public import Parley.Stdlib.Geometry.AngleAngleSimilar
public import Parley.Stdlib.Geometry.SameArcAngles
public import Parley.Stdlib.Geometry.VerticalAngles

/-! Written from proofs/euclid/intersecting-chords-by-angles.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.IntersectingChordsByAngles.IntersectingChordsByAngles

theorem intersecting_chords_by_angles (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (P : ℂ) (O : ℂ) (hH7 : Sbtw ℝ A P B) (hH8 : Sbtw ℝ C P D) (hH9 : ¬ C ∈ LeanBridges.Geometry.line A B) (hH10 : dist A O = dist B O) (hH11 : dist A O = dist C O) (hH12 : dist A O = dist D O) :
    dist P A * dist P B = dist P C * dist P D := by
  -- 1. mun:between-ends-apart R := P, S := A, T := B, from H7
  have s1 : A ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := P) (S := A) (T := B) hH7)
  -- 2. mun:triangle-off-line P := C, Q := A, R := B, from H9, 1
  have s2 : LeanBridges.Geometry.Triangle C A B := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := C) (Q := A) (R := B) s1 hH9)
  -- 3. mun:triangle-not-on-line P := A, Q := C, R := B, from 2
  have s3 : ¬ A ∈ LeanBridges.Geometry.line C B := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := A) (Q := C) (R := B) (by (have h := s2; rw [LeanBridges.Geometry.triangle_swap_12 C A B] at h; exact h) : LeanBridges.Geometry.Triangle A C B))
  -- 4. mun:on-line-ends A := C, from 2
  have s4 : B ∈ LeanBridges.Geometry.line C B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := C) (B := B) s2.2.2.1)
  -- 5. mun:on-line-ends A := C, from 2
  have s5 : C ∈ LeanBridges.Geometry.line C B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := C) (B := B) s2.2.2.1)
  -- 6. mun:segment-off-line A := C, P := A, Q := B, X := P, from H7, 2, 3, 4
  have s6 : 0 < Complex.im ((P - C) / (B - C)) * Complex.im ((A - C) / (B - C)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := C) (B := B) (P := A) (Q := B) (X := P) s2.2.2.1 s4 s3 hH7)
  -- 7. mun:same-side-off-line A := C, Q := A, from 6
  have s7 : ¬ P ∈ LeanBridges.Geometry.line C B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := C) (B := B) (P := P) (Q := A) s6)
  -- 8. mun:segment-beyond-off-line A := C, P := D, Q := C, X := P, from H8, 2, 5, 7
  have s8 : 0 < Complex.im ((D - C) / (B - C)) * Complex.im ((P - C) / (B - C)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_beyond_off_line (A := C) (B := B) (P := D) (Q := C) (X := P) s2.2.2.1 s5 s7 (by (have h := hH8; rw [sbtw_comm (x := C) (y := P) (z := D)] at h; exact h) : Sbtw ℝ D P C))
  -- 9. mun:same-side-same A := C, P := A, Q := P, R := D, from 6, 8
  have s9 : 0 < Complex.im ((A - C) / (B - C)) * Complex.im ((D - C) / (B - C)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := C) (B := B) (P := A) (Q := P) (R := D) (by (have h := s6; rw [mul_comm (Complex.im ((P - C) / (B - C))) (Complex.im ((A - C) / (B - C)))] at h; exact h) : 0 < Complex.im ((A - C) / (B - C)) * Complex.im ((P - C) / (B - C))) (by (have h := s8; rw [mul_comm (Complex.im ((D - C) / (B - C))) (Complex.im ((P - C) / (B - C)))] at h; exact h) : 0 < Complex.im ((P - C) / (B - C)) * Complex.im ((D - C) / (B - C))))
  -- 10. calculation
  have s10 : dist C O = dist B O := by
    calc dist C O = dist A O := hH11.symm
      _ = dist B O := hH10
  -- 11. calculation
  have s11 : dist C O = dist D O := by
    calc dist C O = dist A O := hH11.symm
      _ = dist D O := hH12
  -- 12. mun:same-side-off-line A := C, P := D, Q := P, from 8
  have s12 : ¬ D ∈ LeanBridges.Geometry.line C B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := C) (B := B) (P := D) (Q := P) s8)
  -- 13. mun:triangle-off-line P := D, Q := C, R := B, from 2, 12
  have s13 : LeanBridges.Geometry.Triangle D C B := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := D) (Q := C) (R := B) s2.2.2.1 s12)
  -- 14. mun:triangle-on-side P := C, Q := A, R := B, S := P, from H7, 2
  have s14 : LeanBridges.Geometry.Triangle C A P := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := C) (Q := A) (R := B) (S := P) s2 hH7)
  -- 15. mun:triangle-on-side P := B, Q := D, R := C, S := P, from H8, 13
  have s15 : LeanBridges.Geometry.Triangle B D P := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := B) (Q := D) (R := C) (S := P) (by (have h := s13; rw [LeanBridges.Geometry.triangle_rot_312 D C B] at h; exact h) : LeanBridges.Geometry.Triangle B D C) (by (have h := hH8; rw [sbtw_comm (x := C) (y := P) (z := D)] at h; exact h) : Sbtw ℝ D P C))
  -- 16. mun:between-collinear R := P, S := A, T := B, from H7
  have s16 : Collinear ℝ {B, P, A} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := P) (S := A) (T := B) hH7)
  -- 17. def:on-line, from 1, 16
  have s17 : P ∈ LeanBridges.Geometry.line A B := ((Parley.Items.Stdlib.Geometry.def_on_line (A := A) (B := B) (P := P) s1)).mpr (by (have h := s16; rw [LeanBridges.Geometry.collinear_rot_312 B P A] at h; exact h) : Collinear ℝ {A, B, P})
  -- 18. mun:on-line-ends B := C, from 2
  have s18 : A ∈ LeanBridges.Geometry.line A C := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := C) (Ne.symm s2.1))
  -- 19. mun:triangle-not-on-line P := B, Q := A, R := C, from 2
  have s19 : ¬ B ∈ LeanBridges.Geometry.line A C := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := B) (Q := A) (R := C) (by (have h := s2; rw [LeanBridges.Geometry.triangle_swap_13 C A B] at h; exact h) : LeanBridges.Geometry.Triangle B A C))
  -- 20. mun:segment-off-line B := C, P := B, Q := A, X := P, from H7, 2, 18, 19
  have s20 : 0 < Complex.im ((P - A) / (C - A)) * Complex.im ((B - A) / (C - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := A) (B := C) (P := B) (Q := A) (X := P) (Ne.symm s2.1) s18 s19 (by (have h := hH7; rw [sbtw_comm (x := A) (y := P) (z := B)] at h; exact h) : Sbtw ℝ B P A))
  -- 21. mun:between-collinear R := P, S := C, T := D, from H8
  have s21 : Collinear ℝ {C, P, D} := (by (have h := (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := P) (S := C) (T := D) hH8); rw [LeanBridges.Geometry.collinear_swap_13 D P C] at h; exact h) : Collinear ℝ {C, P, D})
  -- 22. def:on-line A := D, B := C, from 13, 21
  have s22 : P ∈ LeanBridges.Geometry.line D C := ((Parley.Items.Stdlib.Geometry.def_on_line (A := D) (B := C) (P := P) s13.1)).mpr (by (have h := s21; rw [LeanBridges.Geometry.collinear_rot_312 C P D] at h; exact h) : Collinear ℝ {D, C, P})
  -- 23. mun:on-line-ends A := D, from 13
  have s23 : D ∈ LeanBridges.Geometry.line D B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := D) (B := B) s13.2.2.1)
  -- 24. mun:triangle-not-on-line P := C, Q := D, R := B, from 13
  have s24 : ¬ C ∈ LeanBridges.Geometry.line D B := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := C) (Q := D) (R := B) (by (have h := s13; rw [LeanBridges.Geometry.triangle_swap_12 D C B] at h; exact h) : LeanBridges.Geometry.Triangle C D B))
  -- 25. mun:segment-off-line A := D, P := C, Q := D, X := P, from H8, 13, 23, 24
  have s25 : 0 < Complex.im ((P - D) / (B - D)) * Complex.im ((C - D) / (B - D)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := D) (B := B) (P := C) (Q := D) (X := P) s13.2.2.1 s23 s24 hH8)
  -- 26. calculation
  have s26 : EuclideanGeometry.angle P A C = EuclideanGeometry.angle P D B := by
    calc EuclideanGeometry.angle P A C = EuclideanGeometry.angle C A P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := P) (Q := A) (R := C) (by (have h := s14; rw [LeanBridges.Geometry.triangle_swap_13 C A P] at h; exact h) : LeanBridges.Geometry.Triangle P A C))
      _ = EuclideanGeometry.angle C A B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := A) (Q := B) (R := C) (X := P) s17 s20)
      _ = EuclideanGeometry.angle C D B := by exact (Parley.Stdlib.Geometry.SameArcAngles.same_arc_angles (A := C) (B := B) (C := A) (D := D) (O := O) s10 hH11.symm s11 s9)
      _ = EuclideanGeometry.angle B D C := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := C) (Q := D) (R := B) (by (have h := s13; rw [LeanBridges.Geometry.triangle_swap_12 D C B] at h; exact h) : LeanBridges.Geometry.Triangle C D B))
      _ = EuclideanGeometry.angle B D P := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := D) (Q := C) (R := B) (X := P) s22 s25).symm
      _ = EuclideanGeometry.angle P D B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := B) (Q := D) (R := P) s15)
  -- 27. calculation
  have s27 : EuclideanGeometry.angle A P C = EuclideanGeometry.angle D P B := by
    calc EuclideanGeometry.angle A P C = EuclideanGeometry.angle B P D := by exact (Parley.Stdlib.Geometry.VerticalAngles.vertical_angles (A := A) (B := C) (C := B) (D := D) (O := P) hH7 hH8 (by (have h := s14; rw [LeanBridges.Geometry.triangle_rot_231 C A P] at h; exact h) : LeanBridges.Geometry.Triangle A P C) (by (have h := s15; rw [LeanBridges.Geometry.triangle_swap_23 B D P] at h; exact h) : LeanBridges.Geometry.Triangle B P D))
      _ = EuclideanGeometry.angle D P B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := B) (Q := P) (R := D) (by (have h := s15; rw [LeanBridges.Geometry.triangle_swap_23 B D P] at h; exact h) : LeanBridges.Geometry.Triangle B P D))
  -- 28. thm:angle-angle-similar Q := A, R := C, P′ := P, Q′ := D, R′ := B, from 14, 15, 26, 27
  have s28 : dist P A * dist P B = dist P D * dist P C := by exact (Parley.Stdlib.Geometry.AngleAngleSimilar.angle_angle_similar (P := P) (Q := A) (R := C) (P' := P) (Q' := D) (R' := B) (by (have h := s14; rw [LeanBridges.Geometry.triangle_swap_13 C A P] at h; exact h) : LeanBridges.Geometry.Triangle P A C) (by (have h := s15; rw [LeanBridges.Geometry.triangle_swap_13 B D P] at h; exact h) : LeanBridges.Geometry.Triangle P D B) s27 s26)
  -- 29. algebra, from 28
  linear_combination s28

end Parley.Proofs.Euclid.IntersectingChordsByAngles.IntersectingChordsByAngles
