module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
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
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry
public import Parley.Stdlib.Geometry.AngleSideAngle
public import Parley.Stdlib.Geometry.AngleSum
public import Parley.Stdlib.Geometry.OffLineAlong

/-! Written from proofs/euclid/thirty-sixty-ninety.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.ThirtySixtyNinety.ThirtySixtyNinety

theorem thirty_sixty_ninety (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) (hH5 : EuclideanGeometry.angle A C B = (90 : ℝ) * Real.pi / 180) (hH6 : EuclideanGeometry.angle B A C = (30 : ℝ) * Real.pi / 180) :
    dist B C = dist A B / 2 := by
  -- 1. axi:distance-positive P := B, Q := C, from H4
  have s1 : dist B C > 0 := by exact (Parley.Items.Stdlib.Geometry.axi_distance_positive (P := B) (Q := C) hH4.2.1)
  -- 2. obtain D: mun:segment-extension A := B, B := C, r := |BC|, from H4, 1
  obtain ⟨D, s2a, ⟨s2b, s2c⟩⟩ := (Parley.Items.Stdlib.Geometry.mun_segment_extension (A := B) (B := C) (r := dist B C) hH4.2.1 s1)
  -- 3. mun:triangle-extension P := A, Q := C, R := B, S := D, from H4, 2
  have s3 : LeanBridges.Geometry.Triangle A C D := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_extension (P := A) (Q := C) (R := B) (S := D) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) s2b)
  -- 4. axi:supplementary-angles A := B, B := C, C := D, D := A, from H4, 2, 3
  have s4 : EuclideanGeometry.angle B C A + EuclideanGeometry.angle A C D = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := B) (B := C) (C := D) (D := A) s2b hH4.2.2.1 hH4.1 s3.2.2.1)
  -- 5. calculation
  have s5 : EuclideanGeometry.angle B C A = (90 : ℝ) * Real.pi / 180 := by
    calc EuclideanGeometry.angle B C A = EuclideanGeometry.angle A C B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := B) (Q := C) (R := A) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A))
      _ = (90 : ℝ) * Real.pi / 180 := hH5
  -- 6. algebra, from 4, 5
  have s6 : EuclideanGeometry.angle A C D = (90 : ℝ) * Real.pi / 180 := by linear_combination ((32400) / ((180) * (180))) * s4 + ((-32400) / ((180) * (180))) * s5
  -- 7. calculation
  have s7 : EuclideanGeometry.angle A C B = EuclideanGeometry.angle A C D := by
    calc EuclideanGeometry.angle A C B = (90 : ℝ) * Real.pi / 180 := hH5
      _ = EuclideanGeometry.angle A C D := s6.symm
  -- 8. restate 2
  have s8 : dist C B = dist C D := by exact (by (have h := s2c.symm; rw [dist_comm B C] at h; exact h) : dist C B = dist C D)
  -- 9. axi:side-angle-side P := A, Q := C, R := B, P′ := A, Q′ := C, R′ := D, from H4, 3, 7, 8
  have s9 : dist A C = dist A C ∧ dist C B = dist C D ∧ dist B A = dist D A ∧ EuclideanGeometry.angle A C B = EuclideanGeometry.angle A C D ∧ EuclideanGeometry.angle C B A = EuclideanGeometry.angle C D A ∧ EuclideanGeometry.angle B A C = EuclideanGeometry.angle D A C := by exact (Parley.Items.Stdlib.Geometry.axi_side_angle_side (P := A) (P' := A) (Q := C) (Q' := C) (R := B) (R' := D) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) s3 rfl s7 s8)
  -- 10. def:congruent, from H4, 3, 9
  have s10a : dist B A = dist D A := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := A) (Q := C) (Q' := C) (R := B) (R' := D) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) s3)).mp s9).1.1.1.2
  have s10b : EuclideanGeometry.angle C B A = EuclideanGeometry.angle C D A := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := A) (Q := C) (Q' := C) (R := B) (R' := D) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) s3)).mp s9).1.2
  have s10c : EuclideanGeometry.angle B A C = EuclideanGeometry.angle D A C := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := A) (Q := C) (Q' := C) (R := B) (R' := D) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) s3)).mp s9).2
  -- 11. thm:angle-sum, from H4
  have s11 : EuclideanGeometry.angle B A C + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Stdlib.Geometry.AngleSum.angle_sum (A := A) (B := B) (C := C) hH4)
  -- 12. algebra, from H6, 5, 11
  have s12 : EuclideanGeometry.angle A B C = (60 : ℝ) * Real.pi / 180 := by linear_combination ((-32400) / ((180) * (180))) * hH6 + ((-32400) / ((180) * (180))) * s5 + ((32400) / ((180) * (180))) * s11
  -- 13. mun:between-collinear R := C, S := B, T := D, from 2
  have s13 : Collinear ℝ {D, C, B} := by exact (Parley.Items.Stdlib.Geometry.mun_between_collinear (R := C) (S := B) (T := D) s2b)
  -- 14. def:on-line P := D, A := B, B := C, from H4, 13
  have s14 : D ∈ LeanBridges.Geometry.line B C := ((Parley.Items.Stdlib.Geometry.def_on_line (A := B) (B := C) (P := D) hH4.2.1)).mpr (by (have h := s13; rw [LeanBridges.Geometry.collinear_swap_13 D C B] at h; exact h) : Collinear ℝ {B, C, D})
  -- 15. mun:between-ends-apart R := C, S := B, T := D, from 2
  have s15 : B ≠ D := by exact (Parley.Items.Stdlib.Geometry.mun_between_ends_apart (R := C) (S := B) (T := D) s2b)
  -- 16. mun:triangle-not-on-line P := A, Q := B, R := C, from H4
  have s16 : ¬ A ∈ LeanBridges.Geometry.line B C := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := A) (Q := B) (R := C) hH4)
  -- 17. mun:off-line-along A := B, B := C, X := D, P := A, from H4, 14, 15, 16
  have s17 : ¬ A ∈ LeanBridges.Geometry.line B D := by exact (Parley.Stdlib.Geometry.OffLineAlong.off_line_along (A := B) (B := C) (X := D) (P := A) hH4.2.1 s14 (Ne.symm s15) s16)
  -- 18. mun:triangle-off-line P := A, Q := B, R := D, from 15, 17
  have s18 : LeanBridges.Geometry.Triangle A B D := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := A) (Q := B) (R := D) s15 s17)
  -- 19. mun:angle-addition A := B, B := D, C := A, M := C, from H4, 2, 18
  have s19 : EuclideanGeometry.angle B A C + EuclideanGeometry.angle C A D = EuclideanGeometry.angle B A D := by exact (Parley.Items.Stdlib.Geometry.mun_angle_addition (A := B) (B := D) (C := A) (M := C) (by (have h := s18; rw [LeanBridges.Geometry.triangle_rot_231 A B D] at h; exact h) : LeanBridges.Geometry.Triangle B D A) s2b hH4.2.2.1)
  -- 20. calculation
  have s20 : EuclideanGeometry.angle C A D = EuclideanGeometry.angle B A C := by
    calc EuclideanGeometry.angle C A D = EuclideanGeometry.angle D A C := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := C) (Q := A) (R := D) (by (have h := s3; rw [LeanBridges.Geometry.triangle_swap_12 A C D] at h; exact h) : LeanBridges.Geometry.Triangle C A D))
      _ = EuclideanGeometry.angle B A C := s10c.symm
  -- 21. algebra, from H6, 19, 20
  have s21 : EuclideanGeometry.angle B A D = (60 : ℝ) * Real.pi / 180 := by linear_combination ((64800) / ((180) * (180))) * hH6 + ((-180) / ((180))) * s19 + ((180) / ((180))) * s20
  -- 22. calculation
  have s22 : EuclideanGeometry.angle A D B = (60 : ℝ) * Real.pi / 180 := by
    calc EuclideanGeometry.angle A D B = EuclideanGeometry.angle B D A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := A) (Q := D) (R := B) (by (have h := s18; rw [LeanBridges.Geometry.triangle_swap_23 A B D] at h; exact h) : LeanBridges.Geometry.Triangle A D B))
      _ = EuclideanGeometry.angle C D A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := D) (Q := B) (R := A) (S := C) (by (have h := s2b; rw [sbtw_comm (x := B) (y := C) (z := D)] at h; exact h) : Sbtw ℝ D C B) s3.2.2.1 s3.1 s18.1).symm
      _ = EuclideanGeometry.angle C B A := s10b.symm
      _ = EuclideanGeometry.angle A B C := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := C) (Q := B) (R := A) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_13 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C B A))
      _ = (60 : ℝ) * Real.pi / 180 := s12
  -- 23. restate 10
  have s23 : dist A D = dist B A := by exact (by (have h := s10a.symm; rw [dist_comm D A] at h; exact h) : dist A D = dist B A)
  -- 24. calculation
  have s24 : EuclideanGeometry.angle B A D = EuclideanGeometry.angle D B A := by
    calc EuclideanGeometry.angle B A D = (60 : ℝ) * Real.pi / 180 := s21
      _ = EuclideanGeometry.angle A B C := s12.symm
      _ = EuclideanGeometry.angle C B A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := A) (Q := B) (R := C) hH4)
      _ = EuclideanGeometry.angle D B A := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := B) (Q := D) (R := A) (S := C) s2b hH4.1 hH4.2.2.1 s18.2.2.1)
  -- 25. calculation
  have s25 : EuclideanGeometry.angle A D B = EuclideanGeometry.angle B A D := by
    calc EuclideanGeometry.angle A D B = (60 : ℝ) * Real.pi / 180 := s22
      _ = EuclideanGeometry.angle B A D := s21.symm
  -- 26. thm:angle-side-angle B := D, C := B, D := B, E := A, F := D, from 18, 23, 24, 25
  have s26 : dist A D = dist B A ∧ dist D B = dist A D ∧ dist B A = dist D B ∧ EuclideanGeometry.angle A D B = EuclideanGeometry.angle B A D ∧ EuclideanGeometry.angle D B A = EuclideanGeometry.angle A D B ∧ EuclideanGeometry.angle B A D = EuclideanGeometry.angle D B A := by exact (Parley.Stdlib.Geometry.AngleSideAngle.angle_side_angle (A := A) (B := D) (C := B) (D := B) (E := A) (F := D) (by (have h := s18; rw [LeanBridges.Geometry.triangle_swap_23 A B D] at h; exact h) : LeanBridges.Geometry.Triangle A D B) (by (have h := s18; rw [LeanBridges.Geometry.triangle_swap_12 A B D] at h; exact h) : LeanBridges.Geometry.Triangle B A D) s24 s23 s25)
  -- 27. def:congruent, from 18, 26
  have s27 : dist D B = dist A D := by exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := A) (P' := B) (Q := D) (Q' := A) (R := B) (R' := D) (by (have h := s18; rw [LeanBridges.Geometry.triangle_swap_23 A B D] at h; exact h) : LeanBridges.Geometry.Triangle A D B) (by (have h := s18; rw [LeanBridges.Geometry.triangle_swap_12 A B D] at h; exact h) : LeanBridges.Geometry.Triangle B A D))).mp s26).1.1.1.1.2
  -- 28. mun:segment-addition P := B, Q := D, S := C, from 2
  have s28 : dist B C + dist C D = dist B D := by exact (Parley.Items.Stdlib.Geometry.mun_segment_addition (P := B) (Q := D) (S := C) s2b)
  -- 29. calculation
  have s29 : dist A B = 2 * dist B C := by
    calc dist A B = dist A D := (by (have h := s23.symm; rw [dist_comm B A] at h; exact h) : dist A B = dist A D)
      _ = dist D B := s27.symm
      _ = dist B C + dist C D := (by (have h := s28.symm; rw [dist_comm B D] at h; exact h) : dist D B = dist B C + dist C D)
      _ = 2 * dist B C := by linear_combination s2c
  -- 30. algebra, from 29
  linear_combination ((-1) / (((2 : ℝ)))) * s29

end Parley.Proofs.Euclid.ThirtySixtyNinety.ThirtySixtyNinety
