module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
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

namespace Parley.Tests.Stdlib.Geometry.AngleEqualByCosine

theorem angle_equal_by_cosine (P : ℂ) (Q : ℂ) (R : ℂ) (P' : ℂ) (Q' : ℂ) (R' : ℂ) (hH7 : P ≠ Q) (hH8 : R ≠ Q) (hH9 : P' ≠ Q') (hH10 : R' ≠ Q') (hH11 : P ≠ R) (hH12 : P' ≠ R') (hH13 : Real.cos (EuclideanGeometry.angle P Q R) = Real.cos (EuclideanGeometry.angle P' Q' R')) :
    EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R' := by
  -- 1. mun:geometry-angle-equal-by-cosine, from H7, H8, H9, H10, H11, H12, H13
  exact (Parley.Items.Stdlib.Geometry.mun_angle_equal_by_cosine (P := P) (P' := P') (Q := Q) (Q' := Q') (R := R) (R' := R') hH7 hH8 hH9 hH10 hH13 hH11 hH12)

end Parley.Tests.Stdlib.Geometry.AngleEqualByCosine
