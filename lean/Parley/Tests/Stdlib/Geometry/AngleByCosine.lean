module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
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
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.AngleByCosine

theorem angle_by_cosine (P : ℂ) (Q : ℂ) (R : ℂ) (x : ℝ) (hH5 : P ≠ Q) (hH6 : R ≠ Q) (hH7 : 0 ≤ x) (hH8 : x ≤ (180 : ℝ) * Real.pi / 180) (hH9 : P ≠ R) :
    (EuclideanGeometry.angle P Q R = x ↔ Real.cos (EuclideanGeometry.angle P Q R) = Real.cos x) := by
  -- 1. mun:geometry-angle-by-cosine, from H5, H6, H7, H8, H9
  exact (Parley.Items.Stdlib.Geometry.mun_angle_by_cosine (P := P) (Q := Q) (R := R) (x := x) hH5 hH6 hH7 hH8 hH9)

end Parley.Tests.Stdlib.Geometry.AngleByCosine
