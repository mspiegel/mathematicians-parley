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
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
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
public import Parley.Stdlib.Geometry.AngleSum
public import Parley.Stdlib.Geometry.IsoscelesAngles

/-! Written from proofs/euclid/thales.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.Thales.Thales

theorem thales (A : ℂ) (B : ℂ) (C : ℂ) (M : ℂ) (hH5 : LeanBridges.Geometry.Triangle A B C) (hH6 : Sbtw ℝ A M B) (hH7 : dist M A = dist M C ∧ dist M C = dist M B) :
    EuclideanGeometry.angle A C B = (90 : ℝ) * Real.pi / 180 := by
  -- 1. mun:triangle-on-side P := C, Q := A, R := B, S := M, from H5, H6
  have s1 : LeanBridges.Geometry.Triangle C A M := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := C) (Q := A) (R := B) (S := M) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_rot_312 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C A B) hH6)
  -- 2. mun:triangle-on-side P := C, Q := B, R := A, S := M, from H5, H6
  have s2 : LeanBridges.Geometry.Triangle C B M := by exact (Parley.Items.Stdlib.Geometry.mun_triangle_on_side (P := C) (Q := B) (R := A) (S := M) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_13 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C B A) (by (have h := hH6; rw [sbtw_comm (x := A) (y := M) (z := B)] at h; exact h) : Sbtw ℝ B M A))
  -- 3. thm:isosceles-angles B := C, C := M, from H7, 1
  have s3 : EuclideanGeometry.angle M A C = EuclideanGeometry.angle M C A := by exact (Parley.Stdlib.Geometry.IsoscelesAngles.isosceles_angles (A := A) (B := C) (C := M) (by (have h := s1; rw [LeanBridges.Geometry.triangle_swap_12 C A M] at h; exact h) : LeanBridges.Geometry.Triangle A C M) hH7.1)
  -- 4. thm:isosceles-angles A := C, C := M, from H7, 2
  have s4 : EuclideanGeometry.angle M C B = EuclideanGeometry.angle M B C := by exact (Parley.Stdlib.Geometry.IsoscelesAngles.isosceles_angles (A := C) (B := B) (C := M) s2 hH7.2)
  -- 5. mun:angle-addition, from H5, H6, 1
  have s5 : EuclideanGeometry.angle A C M + EuclideanGeometry.angle M C B = EuclideanGeometry.angle A C B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_addition (A := A) (B := B) (C := C) (M := M) hH5 hH6 s1.2.2.1)
  -- 6. thm:angle-sum, from H5
  have s6 : EuclideanGeometry.angle B A C + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Stdlib.Geometry.AngleSum.angle_sum (A := A) (B := B) (C := C) hH5)
  -- 7. mun:angle-along-segment P := A, Q := B, R := C, S := M, from H5, H6, 1
  have s7 : EuclideanGeometry.angle M A C = EuclideanGeometry.angle B A C := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := A) (Q := B) (R := C) (S := M) hH6 (Ne.symm hH5.2.2.1) s1.2.2.1 (Ne.symm hH5.2.1))
  -- 8. mun:angle-along-segment P := B, Q := A, R := C, S := M, from H5, H6, 2
  have s8 : EuclideanGeometry.angle M B C = EuclideanGeometry.angle A B C := by exact (Parley.Items.Stdlib.Geometry.mun_angle_along_segment (P := B) (Q := A) (R := C) (S := M) (by (have h := hH6; rw [sbtw_comm (x := A) (y := M) (z := B)] at h; exact h) : Sbtw ℝ B M A) (Ne.symm hH5.2.1) s2.2.2.1 (Ne.symm hH5.2.2.1))
  -- 9. mun:angle-symmetric P := M, Q := C, R := A, from 1
  have s9 : EuclideanGeometry.angle M C A = EuclideanGeometry.angle A C M := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := M) (Q := C) (R := A) (by (have h := s1; rw [LeanBridges.Geometry.triangle_rot_312 C A M] at h; exact h) : LeanBridges.Geometry.Triangle M C A))
  -- 10. mun:angle-symmetric P := B, Q := C, R := A, from H5
  have s10 : EuclideanGeometry.angle B C A = EuclideanGeometry.angle A C B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := B) (Q := C) (R := A) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A))
  -- 11. calculation
  have s11 : EuclideanGeometry.angle B A C + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A = EuclideanGeometry.angle A C B + EuclideanGeometry.angle A C B := by
    calc EuclideanGeometry.angle B A C + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A = EuclideanGeometry.angle M A C + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A := congrArg (fun t : ℝ => t + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A) s7.symm
      _ = EuclideanGeometry.angle M C A + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A := congrArg (fun t : ℝ => t + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A) s3
      _ = EuclideanGeometry.angle A C M + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A := congrArg (fun t : ℝ => t + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A) s9
      _ = EuclideanGeometry.angle A C M + EuclideanGeometry.angle M B C + EuclideanGeometry.angle B C A := congrArg (fun t : ℝ => EuclideanGeometry.angle A C M + t + EuclideanGeometry.angle B C A) s8.symm
      _ = EuclideanGeometry.angle A C M + EuclideanGeometry.angle M C B + EuclideanGeometry.angle B C A := congrArg (fun t : ℝ => EuclideanGeometry.angle A C M + t + EuclideanGeometry.angle B C A) s4.symm
      _ = EuclideanGeometry.angle A C B + EuclideanGeometry.angle B C A := congrArg (fun t : ℝ => t + EuclideanGeometry.angle B C A) s5
      _ = EuclideanGeometry.angle A C B + EuclideanGeometry.angle A C B := congrArg (fun t : ℝ => EuclideanGeometry.angle A C B + t) s10
  -- 12. algebra, from 6, 11
  linear_combination ((16200) / ((180) * (180))) * s6 + ((-90) / ((180))) * s11

end Parley.Proofs.Euclid.Thales.Thales
