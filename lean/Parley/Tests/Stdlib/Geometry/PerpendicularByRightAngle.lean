module

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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.PerpendicularByRightAngle

theorem perpendicular_by_right_angle (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : P ≠ Q) (hH5 : R ≠ Q) (hH6 : P ≠ R) (hH7 : EuclideanGeometry.angle P Q R = (90 : ℝ) * Real.pi / 180) :
    (Q ≠ P ∧ Q ≠ R ∧ Complex.re ((R - Q) / (P - Q)) = 0) := by
  -- 1. mun:geometry-perpendicular-by-right-angle, from H4, H5, H6, H7
  exact ((Parley.Items.Stdlib.Geometry.mun_perpendicular_by_right_angle (P := P) (Q := Q) (R := R) hH4 hH5 hH6)).mpr hH7

end Parley.Tests.Stdlib.Geometry.PerpendicularByRightAngle
