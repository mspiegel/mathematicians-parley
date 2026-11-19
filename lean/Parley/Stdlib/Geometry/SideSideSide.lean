module

public import Geometry
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
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
public import Parley.Stdlib.Geometry.KiteAngles
public import Parley.Stdlib.Geometry.RayPoint

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.SideSideSide

theorem side_side_side (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (E : ℂ) (F : ℂ) (hH7 : LeanBridges.Geometry.Triangle A B C) (hH8 : LeanBridges.Geometry.Triangle D E F) (hH9 : dist A B = dist D E) (hH10 : dist B C = dist E F) (hH11 : dist C A = dist F D) :
    (dist A B = dist D E ∧ dist B C = dist E F ∧ dist C A = dist F D ∧ EuclideanGeometry.angle A B C = EuclideanGeometry.angle D E F ∧ EuclideanGeometry.angle B C A = EuclideanGeometry.angle E F D ∧ EuclideanGeometry.angle C A B = EuclideanGeometry.angle F D E) := by
  -- 1. axi:distance-positive P := D, Q := E, from H8
  have s1 : dist D E > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := D) (Q := E) hH8.1)
  -- 2. obtain H: mun:segment-extension A := D, B := E, r := |DE|, from H8, 1
  obtain ⟨H, s2a, ⟨s2b, s2c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := D) (B := E) (r := dist D E) hH8.1 s1)
  -- 3. mun:on-line-ends A := E, B := F, from H8
  have s3 : E ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := E) (B := F) hH8.2.1)
  -- 4. mun:triangle-not-on-line P := D, Q := E, R := F, from H8
  have s4 : ¬ D ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := D) (Q := E) (R := F) hH8)
  -- 5. mun:segment-across-line A := E, B := F, P := D, Q := H, M := E, from H8, 2, 3, 4
  have s5 : Complex.im ((D - E) / (F - E)) * Complex.im ((H - E) / (F - E)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := E) (B := F) (M := E) (P := D) (Q := H) hH8.2.1 s3 s4 s2b)
  -- 6. mun:opposite-sides-off-line A := E, B := F, P := D, Q := H, from 5
  have s6 : ¬ H ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_3 (A := E) (B := F) (P := D) (Q := H) s5)
  -- 7. mun:triangle-off-line P := H, Q := E, R := F, from H8, 6
  have s7 : LeanBridges.Geometry.Triangle H E F := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := H) (Q := E) (R := F) hH8.2.1 s6)
  -- 8. axi:angle-measure, from H7
  have s8a : EuclideanGeometry.angle A B C > (0 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_1 (P := A) (Q := B) (R := C) hH7)
  have s8b : EuclideanGeometry.angle A B C < (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_2 (P := A) (Q := B) (R := C) hH7)
  -- 9. obtain G′: axi:angle-construction A := E, B := F, C := H, x := ∠ABC, from 7, 8
  obtain ⟨G', s9a, ⟨s9b, s9c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_angle_construction (A := E) (B := F) (C := H) (x := EuclideanGeometry.angle A B C) (by (have h := s7; rw [LeanBridges.Geometry.triangle_rot_231 H E F] at h; exact h) : LeanBridges.Geometry.Triangle E F H) s8a s8b)
  -- 10. mun:same-side-off-line A := E, B := F, P := G′, Q := H, from 9
  have s10 : ¬ G' ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := E) (B := F) (P := G') (Q := H) s9b)
  -- 11. mun:triangle-off-line P := G′, Q := E, R := F, from H8, 10
  have s11 : LeanBridges.Geometry.Triangle G' E F := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := G') (Q := E) (R := F) hH8.2.1 s10)
  -- 12. axi:distance-positive P := B, Q := A, from H7
  have s12 : dist B A > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := B) (Q := A) (Ne.symm hH7.1))
  -- 13. obtain G: mun:ray-point A := E, B := G′, C := F, r := |BA|, from 11, 12
  obtain ⟨G, s13a, ⟨⟨s13b, s13c⟩, s13d⟩⟩ := (Parley.Stdlib.Geometry.RayPoint.ray_point (A := E) (B := G') (C := F) (r := dist B A) (by (have h := s11; rw [LeanBridges.Geometry.triangle_swap_12 G' E F] at h; exact h) : LeanBridges.Geometry.Triangle E G' F) s12)
  -- 14. mun:same-side-same A := E, B := F, P := G, Q := G′, R := H, from 9, 13
  have s14 : 0 < Complex.im ((G - E) / (F - E)) * Complex.im ((H - E) / (F - E)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := E) (B := F) (P := G) (Q := G') (R := H) s13c s9b)
  -- 15. mun:same-opposite-opposite A := E, B := F, P := G, Q := H, R := D, from 5, 14
  have s15 : Complex.im ((G - E) / (F - E)) * Complex.im ((D - E) / (F - E)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := E) (B := F) (P := G) (Q := H) (R := D) s14 (by (have h := s5; rw [mul_comm (Complex.im ((D - E) / (F - E))) (Complex.im ((H - E) / (F - E)))] at h; exact h) : Complex.im ((H - E) / (F - E)) * Complex.im ((D - E) / (F - E)) < 0))
  -- 16. mun:same-side-off-line A := E, B := F, P := G, Q := H, from 14
  have s16 : ¬ G ∈ LeanBridges.Geometry.line E F := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := E) (B := F) (P := G) (Q := H) s14)
  -- 17. mun:off-line-apart A := E, B := F, P := G, from H8, 16
  have s17a : G ≠ E := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := E) (B := F) (P := G) hH8.2.1 s16)
  have s17b : G ≠ F := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := E) (B := F) (P := G) hH8.2.1 s16)
  -- 18. mun:triangle-off-line P := G, Q := E, R := F, from H8, 16
  have s18 : LeanBridges.Geometry.Triangle G E F := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := G) (Q := E) (R := F) hH8.2.1 s16)
  -- 19. mun:angle-turned P := F, Q := E, R := G, from H8, 17
  have s19 : EuclideanGeometry.angle F E G = EuclideanGeometry.angle G E F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := F) (Q := E) (R := G) (Ne.symm hH8.2.1) s17a (Ne.symm s17b))
  -- 20. calculation
  have s20 : EuclideanGeometry.angle A B C = EuclideanGeometry.angle G E F := by
    calc EuclideanGeometry.angle A B C = EuclideanGeometry.angle F E G' := s9c.symm
      _ = EuclideanGeometry.angle F E G := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := E) (Q := G') (R := F) (X := G) s13b s13c).symm
      _ = EuclideanGeometry.angle G E F := s19
  -- 21. restate 13
  have s21 : dist A B = dist G E := by exact (by (have h := s13d.symm; rw [dist_comm B A, dist_comm E G] at h; exact h) : dist A B = dist G E)
  -- 22. axi:side-angle-side P′ := G, Q′ := E, R′ := F, from H7, H10, 18, 20, 21
  have s22 : dist A B = dist G E ∧ dist B C = dist E F ∧ dist C A = dist F G ∧ EuclideanGeometry.angle A B C = EuclideanGeometry.angle G E F ∧ EuclideanGeometry.angle B C A = EuclideanGeometry.angle E F G ∧ EuclideanGeometry.angle C A B = EuclideanGeometry.angle F G E := by exact (Parley.Items.Stdlib.Geometry.axi_side_angle_side (P := A) (P' := G) (Q := B) (Q' := E) (R := C) (R' := F) hH7 s18 s21 s20 hH10)
  -- 23. def:congruent, from H7, 18, 22
  have s23a : dist C A = dist F G := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := G) (Q := B) (Q' := E) (R := C) (R' := F) hH7 s18)).mp s22).1.1.1.2
  have s23b : EuclideanGeometry.angle B C A = EuclideanGeometry.angle E F G := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := G) (Q := B) (Q' := E) (R := C) (R' := F) hH7 s18)).mp s22).1.2
  have s23c : EuclideanGeometry.angle C A B = EuclideanGeometry.angle F G E := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := G) (Q := B) (Q' := E) (R := C) (R' := F) hH7 s18)).mp s22).2
  -- 24. transitivity, from H9, 13
  have s24 : dist E D = dist E G := by
    rw [dist_comm B A] at s13d
    rw [dist_comm E D]
    exact (by linarith only [hH9, s13d])
  -- 25. transitivity, from H11, 23
  have s25 : dist F D = dist F G := by exact Eq.trans hH11.symm s23a
  -- 26. thm:kite-angles, from H8, 15, 24, 25
  have s26 : EuclideanGeometry.angle E D F = EuclideanGeometry.angle E G F := by exact (Parley.Stdlib.Geometry.KiteAngles.kite_angles (D := D) (E := E) (F := F) (G := G) hH8 (by (have h := s15; rw [mul_comm (Complex.im ((G - E) / (F - E))) (Complex.im ((D - E) / (F - E)))] at h; exact h) : Complex.im ((D - E) / (F - E)) * Complex.im ((G - E) / (F - E)) < 0) s24 s25)
  -- 27. restate 25
  have s27 : dist D F = dist G F := by exact (by (have h := s25; rw [dist_comm F D, dist_comm F G] at h; exact h) : dist D F = dist G F)
  -- 28. axi:side-angle-side P := E, Q := D, R := F, P′ := E, Q′ := G, R′ := F, from H8, 18, 24, 26, 27
  have s28 : dist E D = dist E G ∧ dist D F = dist G F ∧ dist F E = dist F E ∧ EuclideanGeometry.angle E D F = EuclideanGeometry.angle E G F ∧ EuclideanGeometry.angle D F E = EuclideanGeometry.angle G F E ∧ EuclideanGeometry.angle F E D = EuclideanGeometry.angle F E G := by exact (Parley.Items.Stdlib.Geometry.axi_side_angle_side (P := E) (P' := E) (Q := D) (Q' := G) (R := F) (R' := F) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E D F) (by (have h := s18; rw [LeanBridges.Geometry.triangle_swap_12 G E F] at h; exact h) : LeanBridges.Geometry.Triangle E G F) s24 s26 s27)
  -- 29. def:congruent, from H8, 18, 28
  have s29a : EuclideanGeometry.angle D F E = EuclideanGeometry.angle G F E := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := E) (P' := E) (Q := D) (Q' := G) (R := F) (R' := F) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E D F) (by (have h := s18; rw [LeanBridges.Geometry.triangle_swap_12 G E F] at h; exact h) : LeanBridges.Geometry.Triangle E G F))).mp s28).1.2
  have s29b : EuclideanGeometry.angle F E D = EuclideanGeometry.angle F E G := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := E) (P' := E) (Q := D) (Q' := G) (R := F) (R' := F) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E D F) (by (have h := s18; rw [LeanBridges.Geometry.triangle_swap_12 G E F] at h; exact h) : LeanBridges.Geometry.Triangle E G F))).mp s28).2
  -- 30. calculation
  have s30 : EuclideanGeometry.angle A B C = EuclideanGeometry.angle D E F := by
    calc EuclideanGeometry.angle A B C = EuclideanGeometry.angle G E F := s20
      _ = EuclideanGeometry.angle F E G := s19.symm
      _ = EuclideanGeometry.angle F E D := s29b.symm
      _ = EuclideanGeometry.angle D E F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := F) (Q := E) (R := D) (Ne.symm hH8.2.1) hH8.1 (Ne.symm hH8.2.2.1))
  -- 31. calculation
  have s31 : EuclideanGeometry.angle B C A = EuclideanGeometry.angle E F D := by
    calc EuclideanGeometry.angle B C A = EuclideanGeometry.angle E F G := s23b
      _ = EuclideanGeometry.angle G F E := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := E) (Q := F) (R := G) hH8.2.1 s17b (Ne.symm s17a))
      _ = EuclideanGeometry.angle D F E := s29a.symm
      _ = EuclideanGeometry.angle E F D := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := D) (Q := F) (R := E) hH8.2.2.1 hH8.2.1 hH8.1)
  -- 32. calculation
  have s32 : EuclideanGeometry.angle C A B = EuclideanGeometry.angle F D E := by
    calc EuclideanGeometry.angle C A B = EuclideanGeometry.angle F G E := s23c
      _ = EuclideanGeometry.angle E G F := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := F) (Q := G) (R := E) (Ne.symm s17b) (Ne.symm s17a) (Ne.symm hH8.2.1))
      _ = EuclideanGeometry.angle E D F := s26.symm
      _ = EuclideanGeometry.angle F D E := by exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := E) (Q := D) (R := F) (Ne.symm hH8.1) (Ne.symm hH8.2.2.1) hH8.2.1)
  -- 33. def:congruent P := A, Q := B, R := C, P′ := D, Q′ := E, R′ := F, from H7, H8, H9, H10, H11, 30, 31, 32
  exact ((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := D) (Q := B) (Q' := E) (R := C) (R' := F) hH7 hH8)).mpr ⟨⟨⟨⟨⟨hH9, hH10⟩, hH11⟩, s30⟩, s31⟩, s32⟩

end Parley.Stdlib.Geometry.SideSideSide
