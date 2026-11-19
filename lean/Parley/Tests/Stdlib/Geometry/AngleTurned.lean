module

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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.AngleTurned

theorem angle_turned (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : P ≠ Q) (hH5 : R ≠ Q) (hH6 : P ≠ R) :
    EuclideanGeometry.angle P Q R = EuclideanGeometry.angle R Q P := by
  -- 1. mun:geometry-angle-turned, from H4, H5, H6
  exact (Parley.Items.Stdlib.Geometry.mun_angle_turned (P := P) (Q := Q) (R := R) hH4 hH5 hH6)

end Parley.Tests.Stdlib.Geometry.AngleTurned
