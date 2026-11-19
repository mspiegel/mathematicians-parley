module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
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
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.AngleAdditionInside

theorem angle_addition_inside (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (hH5 : LeanBridges.Geometry.Triangle A B C) (hH6 : 0 < Complex.im ((D - A) / (B - A)) * Complex.im ((C - A) / (B - A))) (hH7 : 0 < Complex.im ((D - A) / (C - A)) * Complex.im ((B - A) / (C - A))) :
    EuclideanGeometry.angle B A D + EuclideanGeometry.angle D A C = EuclideanGeometry.angle B A C := by
  -- 1. axi:geometry-angle-addition-inside, from H5, H6, H7
  exact (Parley.Items.Stdlib.Geometry.axi_angle_addition_inside (A := A) (B := B) (C := C) (D := D) hH5 hH6 hH7)

end Parley.Tests.Stdlib.Geometry.AngleAdditionInside
