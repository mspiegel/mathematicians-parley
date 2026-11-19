module

public import Geometry
public import Mathlib.Algebra.Group.DivInvMonoid
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

/-! Written from proofs/euclid/equilateral-angle-sixty.proof by parley build lean. -/

public section

namespace Parley.Proofs.Euclid.EquilateralAngleSixty.EquilateralAngleSixty

theorem equilateral_angle_sixty (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) (hH5 : dist A B = dist B C ∧ dist B C = dist C A) :
    EuclideanGeometry.angle A B C = (60 : ℝ) * Real.pi / 180 := by
  -- 1. restate H5
  have s1 : dist C A = dist C B := by exact (by (have h := hH5.2.symm; rw [dist_comm B C] at h; exact h) : dist C A = dist C B)
  -- 2. thm:isosceles-angles, from H4, 1
  have s2 : EuclideanGeometry.angle C A B = EuclideanGeometry.angle C B A := by exact (Parley.Stdlib.Geometry.IsoscelesAngles.isosceles_angles (A := A) (B := B) (C := C) hH4 s1)
  -- 3. calculation
  have s3 : dist A B = dist A C := by
    have h := by
      calc dist A B = dist B C := hH5.1
        _ = dist C A := hH5.2
    rw [dist_comm C A] at h
    exact h
  -- 4. thm:isosceles-angles A := B, B := C, C := A, from H4, 3
  have s4 : EuclideanGeometry.angle A B C = EuclideanGeometry.angle A C B := by exact (Parley.Stdlib.Geometry.IsoscelesAngles.isosceles_angles (A := B) (B := C) (C := A) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A) s3)
  -- 5. thm:angle-sum, from H4
  have s5 : EuclideanGeometry.angle B A C + EuclideanGeometry.angle A B C + EuclideanGeometry.angle B C A = (180 : ℝ) * Real.pi / 180 := by exact (Parley.Stdlib.Geometry.AngleSum.angle_sum (A := A) (B := B) (C := C) hH4)
  -- 6. calculation
  have s6 : EuclideanGeometry.angle B A C = EuclideanGeometry.angle A B C := by
    calc EuclideanGeometry.angle B A C = EuclideanGeometry.angle C A B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := B) (Q := A) (R := C) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_12 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B A C))
      _ = EuclideanGeometry.angle C B A := s2
      _ = EuclideanGeometry.angle A B C := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := C) (Q := B) (R := A) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_13 A B C] at h; exact h) : LeanBridges.Geometry.Triangle C B A))
  -- 7. calculation
  have s7 : EuclideanGeometry.angle B C A = EuclideanGeometry.angle A B C := by
    calc EuclideanGeometry.angle B C A = EuclideanGeometry.angle A C B := by exact (Parley.Items.Stdlib.Geometry.mun_angle_symmetric (P := B) (Q := C) (R := A) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A))
      _ = EuclideanGeometry.angle A B C := s4.symm
  -- 8. algebra, from 5, 6, 7
  linear_combination ((10800) / ((180) * (180))) * s5 + ((-60) / ((180))) * s6 + ((-60) / ((180))) * s7

end Parley.Proofs.Euclid.EquilateralAngleSixty.EquilateralAngleSixty
