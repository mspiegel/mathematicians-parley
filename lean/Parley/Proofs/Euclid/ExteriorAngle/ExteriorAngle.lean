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
public import Parley.Items.Stdlib.Geometry
public import Parley.Proofs.Wiedijk.AngleSum.AngleSum

/-! Written from proofs/euclid/exterior-angle.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.ExteriorAngle.ExteriorAngle

theorem exterior_angle (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (hH5 : LeanBridges.Geometry.Triangle A B C) (hH6 : Sbtw ℝ C B D) (hH7 : LeanBridges.Geometry.Triangle A B D) :
    EuclideanGeometry.angle A B D = EuclideanGeometry.angle B A C + EuclideanGeometry.angle B C A := by
  -- 1. axi:supplementary-angles A := C, C := D, D := A, from H5, H6, H7
  have s1 : EuclideanGeometry.angle C B A + EuclideanGeometry.angle A B D = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Items.Stdlib.Geometry.axi_supplementary_angles (A := C) (B := B) (C := D) (D := A) hH6 hH5.1 hH5.2.2.1 hH7.2.2.1)
  -- 2. thm:angle-sum, from H5
  have s2 : EuclideanGeometry.angle B A C + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Proofs.Wiedijk.AngleSum.AngleSum.angle_sum (A := A) (B := B) (C := C) hH5)
  -- 3. mun:angle-symmetric P := C, Q := B, R := A, from H5
  have s3 : EuclideanGeometry.angle C B A = EuclideanGeometry.angle A B C := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := C) (Q := B) (R := A) (by (have h := hH5; rw [LeanBridges.Geometry.triangle_swap_13 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C B A))
  -- 4. algebra, from 1, 2, 3
  linear_combination ((180) / ((180))) * s1 + ((-180) / ((180))) * s2 + (-1) * s3

end Parley.Proofs.Euclid.ExteriorAngle.ExteriorAngle
