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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
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
public import Parley.Stdlib.Geometry.IsoscelesAngles

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.GreaterSideGreaterAngle

theorem greater_side_greater_angle (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) (hH5 : dist A C > dist A B) :
    EuclideanGeometry.angle A B C > EuclideanGeometry.angle A C B := by
  -- 1. axi:distance-positive P := A, Q := B, from H4
  have s1 : dist A B > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := A) (Q := B) hH4.1)
  -- 2. obtain D: mun:segment-point B := C, r := |AB|, from H5, 1
  obtain ⟨D, s2a, ⟨s2b, s2c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_point (A := A) (B := C) (r := dist A B) s1 hH5)
  -- 3. mun:triangle-on-side P := B, Q := A, R := C, S := D, from H4, 2
  have s3 : LeanBridges.Geometry.Triangle B A D := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := B) (Q := A) (R := C) (S := D) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C) s2b)
  -- 4. mun:triangle-on-side P := B, Q := C, R := A, S := D, from H4, 2
  have s4 : LeanBridges.Geometry.Triangle B C D := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := B) (Q := C) (R := A) (S := D) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A) (by (have h := s2b; rw [sbtw_comm (x := A) (y := D) (z := C)] at h; exact h) : Sbtw ℝ C D A))
  -- 5. restate 2
  have s5 : dist A B = dist A D := by exact s2c.symm
  -- 6. mun:triangle-not-on-line P := C, Q := B, R := A, from H4
  have s6 : ¬ C ∈ LeanBridges.Geometry.line B A := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := C) (Q := B) (R := A) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_13 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C B A))
  -- 7. mun:on-line-ends A := B, B := A, from H4
  have s7 : A ∈ LeanBridges.Geometry.line B A := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := B) (B := A) (Ne.symm hH4.1))
  -- 8. mun:segment-off-line A := B, B := A, P := C, Q := A, X := D, from H4, 2, 6, 7
  have s8 : 0 < Complex.im ((D - B) / (A - B)) * Complex.im ((C - B) / (A - B)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := B) (B := A) (P := C) (Q := A) (X := D) (Ne.symm hH4.1) s7 s6 (by (have h := s2b; rw [sbtw_comm (x := A) (y := D) (z := C)] at h; exact h) : Sbtw ℝ C D A))
  -- 9. mun:triangle-not-on-line P := A, Q := B, R := C, from H4
  have s9 : ¬ A ∈ LeanBridges.Geometry.line B C := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := A) (Q := B) (R := C) hH4)
  -- 10. mun:on-line-ends A := B, B := C, from H4
  have s10 : C ∈ LeanBridges.Geometry.line B C := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := B) (B := C) hH4.2.1)
  -- 11. mun:segment-off-line A := B, B := C, P := A, Q := C, X := D, from H4, 2, 9, 10
  have s11 : 0 < Complex.im ((D - B) / (C - B)) * Complex.im ((A - B) / (C - B)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := B) (B := C) (P := A) (Q := C) (X := D) hH4.2.1 s10 s9 s2b)
  -- 12. axi:angle-addition-inside A := B, B := A, from H4, 8, 11
  have s12 : EuclideanGeometry.angle A B D + EuclideanGeometry.angle D B C = EuclideanGeometry.angle A B C := by exact (Parley.Items.Stdlib.Geometry.axi_angle_addition_inside (A := B) (B := A) (C := C) (D := D) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C) s8 s11)
  -- 13. axi:angle-measure P := D, Q := B, R := C, from 4
  have s13a : EuclideanGeometry.angle D B C > (0 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_1 (P := D) (Q := B) (R := C) (by (have h := s4; rw [LeanBridges.Geometry.triangle_rot_312 B C D] at h; exact h) : LeanBridges.Geometry.Triangle D B C))
  have s13b : EuclideanGeometry.angle D B C < (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_2 (P := D) (Q := B) (R := C) (by (have h := s4; rw [LeanBridges.Geometry.triangle_rot_312 B C D] at h; exact h) : LeanBridges.Geometry.Triangle D B C))
  -- 14. mun:between-apart R := D, S := A, T := C, from 2
  have s14a : A ≠ D := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := D) (S := A) (T := C) s2b)
  have s14b : C ≠ D := by exact (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := D) (S := A) (T := C) s2b)
  -- 15. inequalities
  have s15 : EuclideanGeometry.angle A B D + EuclideanGeometry.angle D B C > EuclideanGeometry.angle A B D := by linarith only [s13a]
  -- 16. thm:exterior-angle-greater-other A := B, B := C, C := D, D := A, from 2, 4
  have r304_1 : LeanBridges.Geometry.Triangle B D A := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := B) (Q := D) (R := C) (S := A) (by (have h := s4; rw [LeanBridges.Geometry.triangle_swap_23 B C D] at h; exact h) : LeanBridges.Geometry.Triangle B D C) (by (have h := s2b; rw [sbtw_comm (x := A) (y := D) (z := C)] at h; exact h) : Sbtw ℝ C D A))
  have s16 : EuclideanGeometry.angle B D A > EuclideanGeometry.angle B C D := by exact (Parley.Stdlib.Geometry.ExteriorAngleGreaterOther.exterior_angle_greater_other (A := B) (B := C) (C := D) (D := A) s4 (by (have h := s2b; rw [sbtw_comm (x := A) (y := D) (z := C)] at h; exact h) : Sbtw ℝ C D A) r304_1)
  -- 17. restate 12
  have s17 : EuclideanGeometry.angle A B C = EuclideanGeometry.angle A B D + EuclideanGeometry.angle D B C := by exact s12.symm
  -- 18. calculation
  calc EuclideanGeometry.angle A B C = EuclideanGeometry.angle A B D + EuclideanGeometry.angle D B C := s17
    _ > EuclideanGeometry.angle A B D := s15
    _ = EuclideanGeometry.angle A D B := by exact (Parley.Stdlib.Geometry.IsoscelesAngles.isosceles_angles (A := B) (B := D) (C := A) (by (have h := s3; rw [LeanBridges.Geometry.triangle_swap_23 B A D] at h; exact h) : LeanBridges.Geometry.Triangle B D A) s5)
    _ = EuclideanGeometry.angle B D A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := A) (Q := D) (R := B) s14a s4.2.2.1 hH4.1)
    _ > EuclideanGeometry.angle B C D := s16
    _ = EuclideanGeometry.angle D C B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := B) (Q := C) (R := D) s4.1 (Ne.symm s4.2.1) s4.2.2.1)
    _ = EuclideanGeometry.angle A C B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := C) (Q := A) (R := B) (S := D) (by (have h := s2b; rw [sbtw_comm (x := A) (y := D) (z := C)] at h; exact h) : Sbtw ℝ C D A) hH4.2.1 s4.2.2.1 (Ne.symm hH4.1))

end Parley.Stdlib.Geometry.GreaterSideGreaterAngle
