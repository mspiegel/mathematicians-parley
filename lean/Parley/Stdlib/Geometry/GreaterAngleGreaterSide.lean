module

public import Geometry
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
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
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Numbers
public import Parley.Stdlib.Geometry.GreaterSideGreaterAngle
public import Parley.Stdlib.Geometry.IsoscelesAngles

/-! Written from corpus/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Stdlib.Geometry.GreaterAngleGreaterSide

theorem greater_angle_greater_side (A : ℂ) (B : ℂ) (C : ℂ) (hH4 : LeanBridges.Geometry.Triangle A B C) (hH5 : EuclideanGeometry.angle A B C > EuclideanGeometry.angle A C B) :
    dist A C > dist A B := by
  -- 1. axi:trichotomy x := |AC| − |AB|
  have s1 : (dist A C - dist A B < 0 ∨ dist A C - dist A B = 0) ∨ 0 < dist A C - dist A B := by exact (Parley.Items.Stdlib.Numbers.axi_trichotomy (x := dist A C - dist A B))
  -- 2. cases, from 1
  rcases s1 with (hC1 | hC2) | hC3
  · skip
    -- 2.1. inequalities
    have s2_1 : dist A B > dist A C := by linarith only [hC1]
    -- 2.2. thm:greater-side-greater-angle B := C, C := B, from H4, 2.1
    have s2_2 : EuclideanGeometry.angle A C B > EuclideanGeometry.angle A B C := by exact (Parley.Stdlib.Geometry.GreaterSideGreaterAngle.greater_side_greater_angle (A := A) (B := C) (C := B) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_swap_23 A B C] at h; exact h) : LeanBridges.Geometry.Triangle A C B) s2_1)
    -- 2.3. inequalities
    have s2_3 : EuclideanGeometry.angle A B C ≤ EuclideanGeometry.angle A C B := by linarith only [s2_2]
    -- 2.4. inequalities, from 2.3
    have s2_4 : ¬ EuclideanGeometry.angle A B C > EuclideanGeometry.angle A C B := by linarith only [s2_3]
    exact absurd hH5 s2_4
  · skip
    -- 2.5. algebra, from C2
    have s2_5 : dist A B = dist A C := by linear_combination (-1) * hC2
    -- 2.6. thm:isosceles-angles A := B, B := C, C := A, from H4, 2.5
    have s2_6 : EuclideanGeometry.angle A B C = EuclideanGeometry.angle A C B := by exact (Parley.Stdlib.Geometry.IsoscelesAngles.isosceles_angles (A := B) (B := C) (C := A) (by (have h := hH4; rw [LeanBridges.Geometry.triangle_rot_231 A B C] at h; exact h) : LeanBridges.Geometry.Triangle B C A) s2_5)
    -- 2.7. inequalities
    have s2_7 : EuclideanGeometry.angle A B C ≤ EuclideanGeometry.angle A C B := by linarith only [s2_6]
    -- 2.8. inequalities, from 2.7
    have s2_8 : ¬ EuclideanGeometry.angle A B C > EuclideanGeometry.angle A C B := by linarith only [s2_7]
    exact absurd hH5 s2_8
  · skip
    -- 2.9. inequalities
    linarith only [hC3]

end Parley.Stdlib.Geometry.GreaterAngleGreaterSide
