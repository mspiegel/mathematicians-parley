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
public import Mathlib.Order.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.RayPoint
public import Parley.Stdlib.Geometry.TriangleInequalityStrict

/-! Written from proofs/euclid/hinge.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.Hinge.Hinge

theorem hinge (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (E : ℂ) (F : ℂ) (hH7 : LeanBridges.Geometry.Triangle A B C) (hH8 : LeanBridges.Geometry.Triangle D E F) (hH9 : dist A B = dist D E) (hH10 : dist A C = dist D F) (hH11 : EuclideanGeometry.angle B A C > EuclideanGeometry.angle E D F) :
    dist B C > dist E F := by
  -- 1. axi:angle-measure P := E, Q := D, R := F, from H8
  have s1a : EuclideanGeometry.angle E D F > (0 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_1 (P := E) (Q := D) (R := F) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E D F))
  have s1b : EuclideanGeometry.angle E D F < (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_2 (P := E) (Q := D) (R := F) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E D F))
  -- 2. obtain G′: axi:angle-construction x := ∠EDF, from H7, 1
  obtain ⟨G', s2a, ⟨s2b, s2c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_angle_construction (A := A) (B := B) (C := C) (x := EuclideanGeometry.angle E D F) hH7 s1a s1b)
  -- 3. mun:same-side-off-line P := G′, Q := C, from 2
  have s3 : ¬ G' ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := A) (B := B) (P := G') (Q := C) s2b)
  -- 4. mun:triangle-off-line P := G′, Q := A, R := B, from H7, 3
  have s4 : LeanBridges.Geometry.Triangle G' A B := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := G') (Q := A) (R := B) hH7.1 s3)
  -- 5. axi:distance-positive P := A, Q := C, from H7
  have s5 : dist A C > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := A) (Q := C) hH7.2.2.1)
  -- 6. obtain G: mun:ray-point B := G′, C := B, r := |AC|, from 4, 5
  obtain ⟨G, s6a, ⟨⟨s6b, s6c⟩, s6d⟩⟩ := (Parley.Stdlib.Geometry.RayPoint.ray_point (A := A) (B := G') (C := B) (r := dist A C) (by (have h := s4; rw [LeanBridges.Geometry.triangle_swap_12 G' A B] at h; exact h) : LeanBridges.Geometry.Triangle A G' B) s5)
  -- 7. mun:same-side-same P := G, Q := G′, R := C, from 2, 6
  have s7 : 0 < Complex.im ((G - A) / (B - A)) * Complex.im ((C - A) / (B - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := A) (B := B) (P := G) (Q := G') (R := C) s6c s2b)
  -- 8. mun:same-side-off-line P := G, Q := C, from 7
  have s8 : ¬ G ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := A) (B := B) (P := G) (Q := C) s7)
  -- 9. mun:triangle-off-line P := G, Q := A, R := B, from H7, 8
  have s9 : LeanBridges.Geometry.Triangle G A B := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := G) (Q := A) (R := B) hH7.1 s8)
  -- 10. calculation
  have s10 : EuclideanGeometry.angle B A G = EuclideanGeometry.angle E D F := by
    calc EuclideanGeometry.angle B A G = EuclideanGeometry.angle B A G' := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := A) (Q := G') (R := B) (X := G) s6b s6c)
      _ = EuclideanGeometry.angle E D F := s2c
  -- 11. transitivity, from H10, 6
  have s11 : dist A G = dist D F := by exact (Eq.trans hH10.symm s6d.symm).symm
  -- 12. axi:side-angle-side P := B, Q := A, R := G, P′ := E, Q′ := D, R′ := F, from H8, H9, 9, 10, 11
  have s12 : dist B A = dist E D ∧ dist A G = dist D F ∧ dist G B = dist F E ∧ EuclideanGeometry.angle B A G = EuclideanGeometry.angle E D F ∧ EuclideanGeometry.angle A G B = EuclideanGeometry.angle D F E ∧ EuclideanGeometry.angle G B A = EuclideanGeometry.angle F E D := by exact (Parley.Items.Stdlib.Geometry.axi_side_angle_side (P := B) (P' := E) (Q := A) (Q' := D) (R := G) (R' := F) (by (have h := s9; rw [LeanBridges.Geometry.triangle_swap_13 G A B] at h; exact h) : LeanBridges.Geometry.Triangle B A G) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E D F) (by (have h := hH9; rw [dist_comm A B, dist_comm D E] at h; exact h) : dist B A = dist E D) s10 s11)
  -- 13. def:congruent P := B, Q := A, R := G, P′ := E, Q′ := D, R′ := F, from H8, 9, 12
  have s13 : dist B G = dist E F := (by (have h := (((Parley.Items.Stdlib.Geometry.def_congruent (P := B) (P' := E) (Q := A) (Q' := D) (R := G) (R' := F) (by (have h := s9; rw [LeanBridges.Geometry.triangle_swap_13 G A B] at h; exact h) : LeanBridges.Geometry.Triangle B A G) (by (have h := hH8; rw [LeanBridges.Geometry.triangle_swap_12 D E F] at h; exact h) : LeanBridges.Geometry.Triangle E D F))).mp s12).1.1.1.2; rw [dist_comm G B, dist_comm F E] at h; exact h) : dist B G = dist E F)
  -- 14. transitivity, from 10, H11
  have s14 : EuclideanGeometry.angle B A G < EuclideanGeometry.angle B A C := by exact Eq.trans_lt s10 hH11
  -- 15. contradiction
  have s15 : ¬ G ∈ LeanBridges.Geometry.line A C := by
    intro hS
    -- 15.1. mun:angle-same-ray R := B, P := A, Q := C, X := G, from S, 7
    have s15_1 : EuclideanGeometry.angle B A G = EuclideanGeometry.angle B A C := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := A) (Q := C) (R := B) (X := G) hS s7)
    -- 15.2. substitute ∠BAG = ∠BAC (line 15.1) into line 14
    have s15_2 : EuclideanGeometry.angle B A C < EuclideanGeometry.angle B A C := Eq.subst (motive := (fun t : ℝ => t < EuclideanGeometry.angle B A C)) s15_1 s14
    -- 15.3. inequalities
    have s15_3 : (0 : ℝ) < 0 := by exact_mod_cast (show (0 : ℝ) < 0 by linarith only [s15_2])
    exact absurd s15_3 (by norm_num)
  -- 16. mun:triangle-not-on-line P := B, Q := A, R := C, from H7
  have s16 : ¬ B ∈ LeanBridges.Geometry.line A C := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := B) (Q := A) (R := C) (by (have h := hH7; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C))
  -- 17. axi:plane-separation B := C, P := G, Q := B, from H7, 15, 16
  have s17 : 0 < Complex.im ((G - A) / (C - A)) * Complex.im ((B - A) / (C - A)) ∨ Complex.im ((G - A) / (C - A)) * Complex.im ((B - A) / (C - A)) < 0 := by exact (Parley.Items.Stdlib.Geometry.axi_plane_separation (A := A) (B := C) (P := G) (Q := B) hH7.2.2.1 s15 s16)
  -- 18. cases, from 17
  have s18 : 0 < Complex.im ((G - A) / (C - A)) * Complex.im ((B - A) / (C - A)) := by
    rcases s17 with hC1 | hC2
    · skip
      exact hC1
    · skip
      -- 18.1. obtain Z: axi:plane-separation-crossing B := C, P := G, Q := B, from C2, H7
      obtain ⟨Z, s18_1a, ⟨s18_1b, s18_1c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_plane_separation_crossing (A := A) (B := C) (P := G) (Q := B) hH7.2.2.1 hC2)
      -- 18.2. mun:on-line-ends, from H7
      have s18_2 : B ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := A) (B := B) hH7.1)
      -- 18.3. mun:segment-off-line P := G, Q := B, X := Z, from H7, 8, 18.1, 18.2
      have s18_3 : 0 < Complex.im ((Z - A) / (B - A)) * Complex.im ((G - A) / (B - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := A) (B := B) (P := G) (Q := B) (X := Z) hH7.1 s18_2 s8 s18_1c)
      -- 18.4. mun:same-side-same P := Z, Q := G, R := C, from 7, 18.3
      have s18_4 : 0 < Complex.im ((Z - A) / (B - A)) * Complex.im ((C - A) / (B - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := A) (B := B) (P := Z) (Q := G) (R := C) s18_3 s7)
      -- 18.5. mun:angle-same-ray R := B, P := A, Q := C, X := Z, from 18.1, 18.4
      have s18_5 : EuclideanGeometry.angle B A Z = EuclideanGeometry.angle B A C := by exact (Parley.Items.Stdlib.Geometry.mun_angle_same_ray (P := A) (Q := C) (R := B) (X := Z) s18_1b s18_4)
      -- 18.6. mun:same-side-off-line P := Z, Q := G, from 18.3
      have s18_6 : ¬ Z ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := A) (B := B) (P := Z) (Q := G) s18_3)
      -- 18.7. mun:off-line-apart P := Z, from H7, 18.6
      have s18_7 : Z ≠ A := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := A) (B := B) (P := Z) hH7.1 s18_6)
      -- 18.8. mun:angle-addition A := B, B := G, C := A, M := Z, from 9, 18.1, 18.7
      have s18_8 : EuclideanGeometry.angle B A Z + EuclideanGeometry.angle Z A G = EuclideanGeometry.angle B A G := by exact (Parley.Items.Stdlib.Geometry.mun_angle_addition (A := B) (B := G) (C := A) (M := Z) (by (have h := s9; rw [LeanBridges.Geometry.triangle_rot_312 G A B] at h; exact h) : LeanBridges.Geometry.Triangle B G A) (by (have h := s18_1c; rw [sbtw_comm (x := G) (y := Z) (z := B)] at h; exact h) : Sbtw ℝ B Z G) (Ne.symm s18_7))
      -- 18.9. mun:triangle-on-side P := A, Q := G, R := B, S := Z, from 9, 18.1
      have s18_9 : LeanBridges.Geometry.Triangle A G Z := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := A) (Q := G) (R := B) (S := Z) (by (have h := s9; rw [LeanBridges.Geometry.triangle_swap_12 G A B] at h; exact h) : LeanBridges.Geometry.Triangle A G B) s18_1c)
      -- 18.10. axi:angle-measure P := Z, Q := A, R := G, from 18.9
      have s18_10a : EuclideanGeometry.angle Z A G > (0 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_1 (P := Z) (Q := A) (R := G) (by (have h := s18_9; rw [LeanBridges.Geometry.triangle_rot_312 A G Z] at h; exact h) : LeanBridges.Geometry.Triangle Z A G))
      have s18_10b : EuclideanGeometry.angle Z A G < (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_angle_measure_2 (P := Z) (Q := A) (R := G) (by (have h := s18_9; rw [LeanBridges.Geometry.triangle_rot_312 A G Z] at h; exact h) : LeanBridges.Geometry.Triangle Z A G))
      -- 18.11. inequalities
      have s18_11 : EuclideanGeometry.angle B A Z + EuclideanGeometry.angle Z A G > EuclideanGeometry.angle B A Z := by linarith only [s18_10a]
      -- 18.12. restate 18.8
      have s18_12 : EuclideanGeometry.angle B A G = EuclideanGeometry.angle B A Z + EuclideanGeometry.angle Z A G := by exact s18_8.symm
      -- 18.13. calculation
      have s18_13 : EuclideanGeometry.angle B A G > EuclideanGeometry.angle B A C := by
        calc EuclideanGeometry.angle B A G = EuclideanGeometry.angle B A Z + EuclideanGeometry.angle Z A G := s18_12
          _ > EuclideanGeometry.angle B A Z := s18_11
          _ = EuclideanGeometry.angle B A C := s18_5
      -- 18.14. inequalities
      have s18_14 : EuclideanGeometry.angle B A C ≤ EuclideanGeometry.angle B A G := by linarith only [s18_13]
      -- 18.15. inequalities, from 18.14
      have s18_15 : ¬ EuclideanGeometry.angle B A G < EuclideanGeometry.angle B A C := by linarith only [s18_14]
      exact absurd s14 s18_15
  -- 19. mun:triangle-off-line P := G, Q := A, R := C, from H7, 15
  have s19 : LeanBridges.Geometry.Triangle G A C := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := G) (Q := A) (R := C) hH7.2.2.1 s15)
  -- 20. mun:triangle-not-on-line P := C, Q := A, R := G, from 19
  have s20 : ¬ C ∈ LeanBridges.Geometry.line A G := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := C) (Q := A) (R := G) (by (have h := s19; rw [LeanBridges.Geometry.triangle_swap_13 G A C] at h; exact h) : LeanBridges.Geometry.Triangle C A G))
  -- 21. mun:triangle-not-on-line P := B, Q := A, R := G, from 9
  have s21 : ¬ B ∈ LeanBridges.Geometry.line A G := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := B) (Q := A) (R := G) (by (have h := s9; rw [LeanBridges.Geometry.triangle_swap_13 G A B] at h; exact h) : LeanBridges.Geometry.Triangle B A G))
  -- 22. axi:plane-separation B := G, P := B, Q := C, from 9, 20, 21
  have s22 : 0 < Complex.im ((B - A) / (G - A)) * Complex.im ((C - A) / (G - A)) ∨ Complex.im ((B - A) / (G - A)) * Complex.im ((C - A) / (G - A)) < 0 := by exact (Parley.Items.Stdlib.Geometry.axi_plane_separation (A := A) (B := G) (P := B) (Q := C) (Ne.symm s9.1) s21 s20)
  -- 23. cases, from 22
  have s23 : Complex.im ((B - A) / (G - A)) * Complex.im ((C - A) / (G - A)) < 0 := by
    rcases s22 with hC1 | hC2
    · skip
      -- 23.1. axi:distance-positive P := A, Q := B, from H7
      have s23_1 : dist A B > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := A) (Q := B) hH7.1)
      -- 23.2. obtain B′: mun:segment-extension A := B, B := A, r := |AB|, from H7, 23.1
      obtain ⟨B', s23_2a, ⟨s23_2b, s23_2c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := B) (B := A) (r := dist A B) (Ne.symm hH7.1) s23_1)
      -- 23.3. mun:on-line-ends B := G, from 9
      have s23_3 : A ∈ LeanBridges.Geometry.line A G := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := G) (Ne.symm s9.1))
      -- 23.4. mun:segment-across-line B := G, P := B, Q := B′, M := A, from 9, 21, 23.2, 23.3
      have s23_4 : Complex.im ((B - A) / (G - A)) * Complex.im ((B' - A) / (G - A)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := A) (B := G) (M := A) (P := B) (Q := B') (Ne.symm s9.1) s23_3 s21 s23_2b)
      -- 23.5. mun:same-opposite-opposite B := G, P := C, Q := B, R := B′, from C1, 23.4
      have s23_5 : Complex.im ((C - A) / (G - A)) * Complex.im ((B' - A) / (G - A)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := A) (B := G) (P := C) (Q := B) (R := B') (by (have h := hC1; rw [mul_comm (Complex.im ((B - A) / (G - A))) (Complex.im ((C - A) / (G - A)))] at h; exact h) : 0 < Complex.im ((C - A) / (G - A)) * Complex.im ((B - A) / (G - A))) s23_4)
      -- 23.6. obtain Y: axi:plane-separation-crossing B := G, P := C, Q := B′, from 9, 23.5
      obtain ⟨Y, s23_6a, ⟨s23_6b, s23_6c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_plane_separation_crossing (A := A) (B := G) (P := C) (Q := B') (Ne.symm s9.1) s23_5)
      -- 23.7. mun:between-collinear R := A, S := B, T := B′, from 23.2
      have s23_7 : Collinear ℝ {B', A, B} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := A) (S := B) (T := B') s23_2b)
      -- 23.8. def:on-line P := B′, from H7, 23.7
      have s23_8 : B' ∈ LeanBridges.Geometry.line A B := ((Parley.Items.Stdlib.Geometry.def_on_line (A := A) (B := B) (P := B') hH7.1)).mpr (by (have h := s23_7; rw [LeanBridges.Geometry.collinear_rot_231 B' A B] at h; exact h) : Collinear ℝ {A, B, B'})
      -- 23.9. mun:triangle-not-on-line P := C, Q := A, R := B, from H7
      have s23_9 : ¬ C ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := C) (Q := A) (R := B) (by (have h := hH7; rw [LeanBridges.Geometry.triangle_rot_312 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C A B))
      -- 23.10. mun:segment-off-line P := C, Q := B′, X := Y, from H7, 23.6, 23.8, 23.9
      have s23_10 : 0 < Complex.im ((Y - A) / (B - A)) * Complex.im ((C - A) / (B - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := A) (B := B) (P := C) (Q := B') (X := Y) hH7.1 s23_8 s23_9 s23_6c)
      -- 23.11. mun:same-side-same P := Y, Q := C, R := G, from 7, 23.10
      have s23_11 : 0 < Complex.im ((Y - A) / (B - A)) * Complex.im ((G - A) / (B - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := A) (B := B) (P := Y) (Q := C) (R := G) s23_10 (by (have h := s7; rw [mul_comm (Complex.im ((G - A) / (B - A))) (Complex.im ((C - A) / (B - A)))] at h; exact h) : 0 < Complex.im ((C - A) / (B - A)) * Complex.im ((G - A) / (B - A))))
      -- 23.12. mun:on-line-ends B := C, from H7
      have s23_12 : A ∈ LeanBridges.Geometry.line A C := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := C) hH7.2.2.1)
      -- 23.13. mun:segment-across-line B := C, P := B, Q := B′, M := A, from H7, 16, 23.2, 23.12
      have s23_13 : Complex.im ((B - A) / (C - A)) * Complex.im ((B' - A) / (C - A)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := A) (B := C) (M := A) (P := B) (Q := B') hH7.2.2.1 s23_12 s16 s23_2b)
      -- 23.14. mun:opposite-sides-off-line B := C, P := B, Q := B′, from 23.13
      have s23_14 : ¬ B' ∈ LeanBridges.Geometry.line A C := by exact (Parley.Items.Stdlib.Geometry.mun_opposite_sides_off_line_3 (A := A) (B := C) (P := B) (Q := B') s23_13)
      -- 23.15. mun:on-line-ends B := C, from H7
      have s23_15 : C ∈ LeanBridges.Geometry.line A C := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := A) (B := C) hH7.2.2.1)
      -- 23.16. mun:segment-off-line B := C, P := B′, Q := C, X := Y, from H7, 23.6, 23.14, 23.15
      have s23_16 : 0 < Complex.im ((Y - A) / (C - A)) * Complex.im ((B' - A) / (C - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := A) (B := C) (P := B') (Q := C) (X := Y) hH7.2.2.1 s23_15 s23_14 (by (have h := s23_6c; rw [sbtw_comm (x := C) (y := Y) (z := B')] at h; exact h) : Sbtw ℝ B' Y C))
      -- 23.17. mun:same-opposite-opposite B := C, P := Y, Q := B′, R := B, from 23.13, 23.16
      have s23_17 : Complex.im ((Y - A) / (C - A)) * Complex.im ((B - A) / (C - A)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := A) (B := C) (P := Y) (Q := B') (R := B) s23_16 (by (have h := s23_13; rw [mul_comm (Complex.im ((B - A) / (C - A))) (Complex.im ((B' - A) / (C - A)))] at h; exact h) : Complex.im ((B' - A) / (C - A)) * Complex.im ((B - A) / (C - A)) < 0))
      -- 23.18. mun:same-opposite-opposite B := C, P := G, Q := B, R := Y, from 18, 23.17
      have s23_18 : Complex.im ((G - A) / (C - A)) * Complex.im ((Y - A) / (C - A)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_opposite_opposite (A := A) (B := C) (P := G) (Q := B) (R := Y) s18 (by (have h := s23_17; rw [mul_comm (Complex.im ((Y - A) / (C - A))) (Complex.im ((B - A) / (C - A)))] at h; exact h) : Complex.im ((B - A) / (C - A)) * Complex.im ((Y - A) / (C - A)) < 0))
      -- 23.19. mun:line-crossing-between R := A, P := C, S := G, X := Y, from 23.6, 23.18
      have s23_19 : Sbtw ℝ G A Y := by exact (Parley.Items.Stdlib.Geometry.mun_line_crossing_between (P := C) (R := A) (S := G) (X := Y) s23_6b s23_18)
      -- 23.20. mun:on-line-ends, from H7
      have s23_20 : A ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := B) hH7.1)
      -- 23.21. mun:segment-across-line P := G, Q := Y, M := A, from H7, 8, 23.19, 23.20
      have s23_21 : Complex.im ((G - A) / (B - A)) * Complex.im ((Y - A) / (B - A)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := A) (B := B) (M := A) (P := G) (Q := Y) hH7.1 s23_20 s8 s23_19)
      -- 23.22. mun:same-not-opposite P := G, Q := Y, from 23.11
      have s23_22 : ¬ Complex.im ((G - A) / (B - A)) * Complex.im ((Y - A) / (B - A)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_not_opposite (A := A) (B := B) (P := G) (Q := Y) (by (have h := s23_11; rw [mul_comm (Complex.im ((Y - A) / (B - A))) (Complex.im ((G - A) / (B - A)))] at h; exact h) : 0 < Complex.im ((G - A) / (B - A)) * Complex.im ((Y - A) / (B - A))))
      exact absurd s23_21 s23_22
    · skip
      exact hC2
  -- 24. obtain X: axi:plane-separation-crossing B := G, P := B, Q := C, from 9, 23
  obtain ⟨X, s24a, ⟨s24b, s24c⟩⟩ := (Parley.Items.Stdlib.Geometry.axi_plane_separation_crossing (A := A) (B := G) (P := B) (Q := C) (Ne.symm s9.1) s23)
  -- 25. mun:triangle-not-on-line P := C, Q := A, R := B, from H7
  have s25 : ¬ C ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := C) (Q := A) (R := B) (by (have h := hH7; rw [LeanBridges.Geometry.triangle_rot_312 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C A B))
  -- 26. mun:segment-off-line P := C, Q := B, from H7, 24, 25
  have r294_1 : B ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := A) (B := B) hH7.1)
  have s26 : 0 < Complex.im ((X - A) / (B - A)) * Complex.im ((C - A) / (B - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := A) (B := B) (P := C) (Q := B) (X := X) hH7.1 r294_1 s25 (by (have h := s24c; rw [sbtw_comm (x := B) (y := X) (z := C)] at h; exact h) : Sbtw ℝ C X B))
  -- 27. mun:same-side-same P := X, Q := C, R := G, from 7, 26
  have s27 : 0 < Complex.im ((X - A) / (B - A)) * Complex.im ((G - A) / (B - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_same (A := A) (B := B) (P := X) (Q := C) (R := G) s26 (by (have h := s7; rw [mul_comm (Complex.im ((G - A) / (B - A))) (Complex.im ((C - A) / (B - A)))] at h; exact h) : 0 < Complex.im ((C - A) / (B - A)) * Complex.im ((G - A) / (B - A))))
  -- 28. mun:same-side-off-line P := X, Q := G, from 27
  have s28 : ¬ X ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := A) (B := B) (P := X) (Q := G) s27)
  -- 29. mun:on-line-ends B := C, from H7
  have s29 : C ∈ LeanBridges.Geometry.line A C := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_2 (A := A) (B := C) hH7.2.2.1)
  -- 30. mun:segment-off-line B := C, P := B, Q := C, from H7, 16, 24, 29
  have s30 : 0 < Complex.im ((X - A) / (C - A)) * Complex.im ((B - A) / (C - A)) := by exact (Parley.Items.Stdlib.Geometry.mun_segment_off_line (A := A) (B := C) (P := B) (Q := C) (X := X) hH7.2.2.1 s29 s16 s24c)
  -- 31. mun:same-side-off-line B := C, P := X, Q := B, from 30
  have s31 : ¬ X ∈ LeanBridges.Geometry.line A C := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := A) (B := C) (P := X) (Q := B) s30)
  -- 32. mun:triangle-off-line P := X, Q := A, R := C, from H7, 31
  have s32 : LeanBridges.Geometry.Triangle X A C := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := X) (Q := A) (R := C) hH7.2.2.1 s31)
  -- 33. mun:segment-addition P := B, Q := C, S := X, from 24
  have s33 : dist B X + dist X C = dist B C := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := B) (Q := C) (S := X) s24c)
  -- 34. mun:on-line-cases P := X, Q := A, R := G, from 9, 24
  have s34 : (((X = A ∨ Sbtw ℝ A X G) ∨ X = G) ∨ Sbtw ℝ A G X) ∨ Sbtw ℝ X A G := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_cases (P := X) (Q := A) (R := G) (Ne.symm s9.1) s24b)
  -- 35. cases, from 34
  have s35 : dist B G < dist B C := by
    rcases s34 with (((hC1 | hC2) | hC3) | hC4) | hC5
    · skip
      -- 35.1. substitute X = A (C1) into line 28
      have s35_1 : ¬ A ∈ LeanBridges.Geometry.line A B := Eq.subst (motive := (fun t : ℂ => ¬ t ∈ LeanBridges.Geometry.line A B)) hC1 s28
      -- 35.2. mun:on-line-ends, from H7
      have s35_2 : A ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := B) hH7.1)
      exact absurd s35_2 s35_1
    · skip
      -- 35.3. mun:segment-addition P := A, Q := G, S := X, from C2
      have s35_3 : dist A X + dist X G = dist A G := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := G) (S := X) hC2)
      -- 35.4. thm:triangle-inequality-strict P := A, Q := X, R := C, from 32
      have s35_4 : dist A C < dist A X + dist X C := by exact (Parley.Stdlib.Geometry.TriangleInequalityStrict.triangle_inequality_strict (P := A) (Q := X) (R := C) (by (have h := s32; rw [LeanBridges.Geometry.triangle_swap_12 X A C] at h; exact h) : LeanBridges.Geometry.Triangle A X C))
      -- 35.5. inequalities
      have s35_5 : dist B X + dist A C - dist A X < dist B X + dist X C := by linarith only [s35_4]
      -- 35.6. calculation
      calc dist B G ≤ dist B X + dist X G := by exact (Parley.Items.Stdlib.Geometry.thm_triangle_inequality_points (P := B) (Q := X) (R := G))
        _ = dist B X + dist A C - dist A X := by linear_combination s6d + s35_3
        _ < dist B X + dist X C := s35_5
        _ = dist B C := s33
    · skip
      -- 35.7. substitute X = G (C3) into line 24
      have s35_7 : Sbtw ℝ B G C := Eq.subst (motive := (fun t : ℂ => Sbtw ℝ B t C)) hC3 s24c
      -- 35.8. mun:segment-addition P := B, Q := C, S := G, from 35.7
      have s35_8 : dist B G + dist G C = dist B C := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := B) (Q := C) (S := G) s35_7)
      -- 35.9. axi:distance-positive P := G, Q := C
      have r366_1 : G ≠ C := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := A) (B := C) (P := G) hH7.2.2.1 s15)
      have s35_9 : dist G C > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := G) (Q := C) r366_1)
      -- 35.10. inequalities
      have s35_10 : dist B G < dist B G + dist G C := by linarith only [s35_9]
      -- 35.11. calculation
      calc dist B G < dist B G + dist G C := s35_10
        _ = dist B C := s35_8
    · skip
      -- 35.12. mun:segment-addition P := A, Q := X, S := G, from C4
      have s35_12 : dist A G + dist G X = dist A X := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := A) (Q := X) (S := G) hC4)
      -- 35.13. thm:triangle-inequality-strict P := A, Q := C, R := X, from 32
      have s35_13 : dist A X < dist A C + dist C X := by exact (Parley.Stdlib.Geometry.TriangleInequalityStrict.triangle_inequality_strict (P := A) (Q := C) (R := X) (by (have h := s32; rw [LeanBridges.Geometry.triangle_rot_231 X A C] at h; exact h) : LeanBridges.Geometry.Triangle A C X))
      -- 35.14. inequalities
      have s35_14 : dist B X + dist A X - dist A C < dist B X + dist X C := by
        rw [dist_comm X C]
        exact (by linarith only [s35_13])
      -- 35.15. calculation
      calc dist B G ≤ dist B X + dist X G := by exact (Parley.Items.Stdlib.Geometry.thm_triangle_inequality_points (P := B) (Q := X) (R := G))
        _ = dist B X + dist A X - dist A C := by
            rw [dist_comm X G]
            exact (by linear_combination (-1) * s6d + s35_12)
        _ < dist B X + dist X C := s35_14
        _ = dist B C := s33
    · skip
      -- 35.16. mun:on-line-ends, from H7
      have s35_16 : A ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_on_line_ends_1 (A := A) (B := B) hH7.1)
      -- 35.17. mun:segment-across-line P := X, Q := G, M := A, from C5, H7, 28, 35.16
      have s35_17 : Complex.im ((X - A) / (B - A)) * Complex.im ((G - A) / (B - A)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_segment_across_line (A := A) (B := B) (M := A) (P := X) (Q := G) hH7.1 s35_16 s28 hC5)
      -- 35.18. mun:same-not-opposite P := X, Q := G, from 27
      have s35_18 : ¬ Complex.im ((X - A) / (B - A)) * Complex.im ((G - A) / (B - A)) < 0 := by exact (Parley.Items.Stdlib.Geometry.mun_same_not_opposite (A := A) (B := B) (P := X) (Q := G) s27)
      exact absurd s35_17 s35_18
  -- 36. calculation
  calc dist B C > dist B G := s35
    _ = dist E F := s13

end Parley.Proofs.Euclid.Hinge.Hinge
