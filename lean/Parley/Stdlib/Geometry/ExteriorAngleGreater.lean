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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
public import Parley.Stdlib.Geometry.VerticalAngles

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.ExteriorAngleGreater

theorem exterior_angle_greater (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (hH5 : LeanBridges.Geometry.Triangle A B C) (hH6 : Sbtw ℝ B C D) (hH7 : LeanBridges.Geometry.Triangle A C D) :
    EuclideanGeometry.angle A C D > EuclideanGeometry.angle B A C := by
  -- 1. obtain M: mun:midpoint-exists B := C, from H5
  obtain ⟨M, s1a, s1b⟩ := (Parley.Items.Stdlib.Geometry.mun_midpoint_exists (A := A) (B := C) hH5.2.2.1)
  -- 2. def:midpoint, from 1
  have s2a : Sbtw ℝ A M C := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := C) (M := M))).mp s1b).1
  have s2b : dist A M = dist M C := by exact (((Parley.Items.Stdlib.Geometry.def_midpoint (A := A) (B := C) (M := M))).mp s1b).2
  -- 3. mun:triangle-on-side P := B, Q := A, R := C, S := M, from H5, 2
  have s3 : LeanBridges.Geometry.Triangle B A M := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := B) (Q := A) (R := C) (S := M) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C) s2a)
  -- 4. mun:triangle-on-side P := B, Q := C, R := A, S := M, from H5, 2
  have s4 : LeanBridges.Geometry.Triangle B C M := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := B) (Q := C) (R := A) (S := M) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A) (by (have h := s2a; rw [sbtw_comm (x := A) (y := M) (z := C)] at h; exact h) : Sbtw ℝ C M A))
  -- 5. axi:distance-positive P := B, Q := M, from 3
  have s5 : dist B M > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := B) (Q := M) s3.2.2.1)
  -- 6. obtain E: mun:segment-extension A := B, B := M, r := |BM|, from 3, 5
  obtain ⟨E, s6a, ⟨s6b, s6c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := B) (B := M) (r := dist B M) s3.2.2.1 s5)
  -- 7. mun:triangle-extension P := C, Q := M, R := B, S := E, from 4, 6
  have s7 : LeanBridges.Geometry.Triangle C M E := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := C) (Q := M) (R := B) (S := E) (by (have h := s4; rw [LeanBridges.Geometry.triangle_rot_231 B C M] at h; exact h) : LeanBridges.Geometry.Triangle C M B) s6b)
  -- 8. thm:vertical-angles O := M, D := E, from 2, 3, 6, 7
  have s8 : EuclideanGeometry.angle A M B = EuclideanGeometry.angle C M E := by exact (Parley.Stdlib.Geometry.VerticalAngles.vertical_angles (A := A) (B := B) (C := C) (D := E) (O := M) s2a s6b (by (have h := s3; rw [LeanBridges.Geometry.triangle_rot_231 B A M] at h; exact h) : LeanBridges.Geometry.Triangle A M B) s7)
  -- 9. restate 6
  have s9 : dist M B = dist M E := by exact (by (have h := s6c.symm; rw [dist_comm B M] at h; exact h) : dist M B = dist M E)
  -- 10. axi:side-angle-side P := A, Q := M, R := B, P′ := C, Q′ := M, R′ := E, from 2, 3, 7, 8, 9
  have s10 : dist A M = dist C M ∧ dist M B = dist M E ∧ dist B A = dist E C ∧ EuclideanGeometry.angle A M B = EuclideanGeometry.angle C M E ∧ EuclideanGeometry.angle M B A = EuclideanGeometry.angle M E C ∧ EuclideanGeometry.angle B A M = EuclideanGeometry.angle E C M := by exact (Parley.Items.Stdlib.Geometry.axi_side_angle_side (P := A) (P' := C) (Q := M) (Q' := M) (R := B) (R' := E) (by (have h := s3; rw [LeanBridges.Geometry.triangle_rot_231 B A M] at h; exact h) : LeanBridges.Geometry.Triangle A M B) s7 (by (have h := s2b; rw [dist_comm M C] at h; exact h) : dist A M = dist C M) s8 s9)
  -- 11. mun:between-apart R := M, S := A, T := C, from 2
  have s11a : M ≠ A := by exact Ne.symm (Parley.Items.Stdlib.Geometry.mun_between_apart_1 (R := M) (S := A) (T := C) s2a)
  have s11b : M ≠ C := by exact Ne.symm (Parley.Items.Stdlib.Geometry.mun_between_apart_2 (R := M) (S := A) (T := C) s2a)
  -- 12. mun:triangle-extension P := E, Q := M, R := C, S := A, from 2, 7
  have s12 : LeanBridges.Geometry.Triangle E M A := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := E) (Q := M) (R := C) (S := A) (by (have h := s7; rw [LeanBridges.Geometry.triangle_swap_13 C M E] at h; exact h) : LeanBridges.Geometry.Triangle E M C) (by (have h := s2a; rw [sbtw_comm (x := A) (y := M) (z := C)] at h; exact h) : Sbtw ℝ C M A))
  -- 13. mun:angle-turned P := A, Q := C, R := E, from H5, 7, 12
  have s13 : EuclideanGeometry.angle A C E = EuclideanGeometry.angle E C A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := A) (Q := C) (R := E) hH5.2.2.1 (Ne.symm s7.2.2.1) (Ne.symm s12.2.2.1))
  -- 14. calculation
  have s14 : EuclideanGeometry.angle B A C = EuclideanGeometry.angle E C A := by
    calc EuclideanGeometry.angle B A C = EuclideanGeometry.angle C A B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := B) (Q := A) (R := C) (Ne.symm hH5.1) (Ne.symm hH5.2.2.1) hH5.2.1)
      _ = EuclideanGeometry.angle M A B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := A) (Q := C) (R := B) (S := M) s2a (Ne.symm hH5.1) s3.2.2.1 hH5.2.1).symm
      _ = EuclideanGeometry.angle B A M := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := M) (Q := A) (R := B) (Ne.symm s3.2.1) s3.1 (Ne.symm s3.2.2.1))
      _ = EuclideanGeometry.angle E C M := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := C) (Q := M) (Q' := M) (R := B) (R' := E) (by (have h := s3; rw [LeanBridges.Geometry.triangle_rot_231 B A M] at h; exact h) : LeanBridges.Geometry.Triangle A M B) s7)).mp s10).2
      _ = EuclideanGeometry.angle M C E := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := E) (Q := C) (R := M) (Ne.symm s7.2.2.1) (Ne.symm s7.1) (Ne.symm s7.2.1))
      _ = EuclideanGeometry.angle A C E := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := C) (Q := A) (R := E) (S := M) (by (have h := s2a; rw [sbtw_comm (x := A) (y := M) (z := C)] at h; exact h) : Sbtw ℝ C M A) (Ne.symm s7.2.2.1) (Ne.symm s7.2.1) s12.2.2.1)
      _ = EuclideanGeometry.angle E C A := s13
  -- 15. mun:triangle-not-on-line P := B, Q := C, R := A, from H5
  have s15 : ¬ B ∈ LeanBridges.Geometry.line C A := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := B) (Q := C) (R := A) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A))
  -- 16. mun:between-collinear R := M, S := A, T := C, from 2
  have s16 : Collinear ℝ {C, M, A} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := M) (S := A) (T := C) s2a)
  -- 17. def:on-line P := M, A := C, B := A, from H5, 16
  have s17 : M ∈ LeanBridges.Geometry.line C A := ((Parley.Items.Stdlib.Geometry.def_on_line (A := C) (B := A) (P := M) (Ne.symm hH5.2.2.1))).mpr (by (have h := s16; rw [LeanBridges.Geometry.collinear_swap_23 C M A] at h; exact h) : Collinear ℝ {C, A, M})
  -- 18. mun:on-line-ends A := C, B := A, from H5
  have s18 : C ∈ LeanBridges.Geometry.line C A := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := C) (B := A) (Ne.symm hH5.2.2.1))
  -- 19. mun:segment-across-line A := C, B := A, P := B, Q := E, from H5, 6, 15, 17
  have s19 : Complex.im ((B - C) / (A - C)) * Complex.im ((E - C) / (A - C)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := C) (B := A) (M := M) (P := B) (Q := E) (Ne.symm hH5.2.2.1) s17 s15 s6b)
  -- 20. mun:segment-across-line A := C, B := A, P := B, Q := D, M := C, from H5, H6, 15, 18
  have s20 : Complex.im ((B - C) / (A - C)) * Complex.im ((D - C) / (A - C)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := C) (B := A) (M := C) (P := B) (Q := D) (Ne.symm hH5.2.2.1) s18 s15 hH6)
  -- 21. mun:opposite-opposite-same A := C, B := A, P := E, Q := B, R := D, from 19, 20
  have s21 : 0 < Complex.im ((E - C) / (A - C)) * Complex.im ((D - C) / (A - C)) := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_opposite_same (A := C) (B := A) (P := E) (Q := B) (R := D) (by (have h := s19; rw [mul_comm (Complex.im ((B - C) / (A - C))) (Complex.im ((E - C) / (A - C)))] at h; exact h) : Complex.im ((E - C) / (A - C)) * Complex.im ((B - C) / (A - C)) < 0) s20)
  -- 22. mun:triangle-extension P := A, Q := C, R := B, S := D, from H5, H6
  have s22 : LeanBridges.Geometry.Triangle A C D := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := A) (Q := C) (R := B) (S := D) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) hH6)
  -- 23. mun:triangle-not-on-line P := A, Q := C, R := D, from 22
  have s23 : ¬ A ∈ LeanBridges.Geometry.line C D := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := A) (Q := C) (R := D) s22)
  -- 24. mun:on-line-ends A := C, B := D, from 22
  have s24 : C ∈ LeanBridges.Geometry.line C D := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := C) (B := D) s22.2.1)
  -- 25. mun:segment-off-line A := C, B := D, P := A, Q := C, X := M, from 2, 22, 23, 24
  have s25 : 0 < Complex.im ((M - C) / (D - C)) * Complex.im ((A - C) / (D - C)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := C) (B := D) (P := A) (Q := C) (X := M) s22.2.1 s24 s23 s2a)
  -- 26. mun:same-side-off-line A := C, B := D, P := M, Q := A, from 25
  have s26 : ¬ M ∈ LeanBridges.Geometry.line C D := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := C) (B := D) (P := M) (Q := A) s25)
  -- 27. mun:between-collinear R := C, S := B, T := D, from H6
  have s27 : Collinear ℝ {D, C, B} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := C) (S := B) (T := D) hH6)
  -- 28. def:on-line P := B, A := C, B := D, from H7, 27
  have s28 : B ∈ LeanBridges.Geometry.line C D := ((Parley.Items.Stdlib.Geometry.def_on_line (A := C) (B := D) (P := B) hH7.2.1)).mpr (by (have h := s27; rw [LeanBridges.Geometry.collinear_swap_12 D C B] at h; exact h) : Collinear ℝ {C, D, B})
  -- 29. mun:segment-beyond-off-line A := C, B := D, P := E, Q := B, X := M, from 6, 22, 26, 28
  have s29 : 0 < Complex.im ((E - C) / (D - C)) * Complex.im ((M - C) / (D - C)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_beyond_off_line (A := C) (B := D) (P := E) (Q := B) (X := M) s22.2.1 s28 s26 (by (have h := s6b; rw [sbtw_comm (x := B) (y := M) (z := E)] at h; exact h) : Sbtw ℝ E M B))
  -- 30. mun:same-side-same A := C, B := D, P := E, Q := M, R := A, from 25, 29
  have s30 : 0 < Complex.im ((E - C) / (D - C)) * Complex.im ((A - C) / (D - C)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := C) (B := D) (P := E) (Q := M) (R := A) s29 s25)
  -- 31. mun:same-side-off-line A := C, B := D, P := E, Q := A, from 30
  have s31 : ¬ E ∈ LeanBridges.Geometry.line C D := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := C) (B := D) (P := E) (Q := A) s30)
  -- 32. mun:triangle-off-line P := E, Q := C, R := D, from 22, 31
  have s32 : LeanBridges.Geometry.Triangle E C D := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := E) (Q := C) (R := D) s22.2.1 s31)
  -- 33. axi:angle-addition-inside A := C, B := A, C := D, D := E, from 21, 22, 30
  have s33 : EuclideanGeometry.angle A C E + EuclideanGeometry.angle E C D = EuclideanGeometry.angle A C D := by exact (Parley.Items.Stdlib.Geometry.axi_angle_addition_inside (A := C) (B := A) (C := D) (D := E) (by (have h := s22; rw [LeanBridges.Geometry.triangle_swap_12 A C D] at h; exact h) : LeanBridges.Geometry.Triangle C A D) s21 s30)
  -- 34. axi:angle-measure P := E, Q := C, R := D, from 32
  have s34a : EuclideanGeometry.angle E C D > (0 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_1 (P := E) (Q := C) (R := D) s32)
  have s34b : EuclideanGeometry.angle E C D < (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_2 (P := E) (Q := C) (R := D) s32)
  -- 35. inequalities
  have s35 : EuclideanGeometry.angle A C E + EuclideanGeometry.angle E C D > EuclideanGeometry.angle A C E := by linarith only [s34a]
  -- 36. restate 33
  have s36 : EuclideanGeometry.angle A C D = EuclideanGeometry.angle A C E + EuclideanGeometry.angle E C D := by exact s33.symm
  -- 37. restate 14
  have s37 : EuclideanGeometry.angle E C A = EuclideanGeometry.angle B A C := by exact s14.symm
  -- 38. calculation
  calc EuclideanGeometry.angle A C D = EuclideanGeometry.angle A C E + EuclideanGeometry.angle E C D := s36
    _ > EuclideanGeometry.angle A C E := s35
    _ = EuclideanGeometry.angle E C A := s13
    _ = EuclideanGeometry.angle B A C := s37

end Parley.Stdlib.Geometry.ExteriorAngleGreater
