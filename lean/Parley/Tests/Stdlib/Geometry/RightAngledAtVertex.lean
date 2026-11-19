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

namespace Parley.Tests.Stdlib.Geometry.RightAngledAtVertex

theorem right_angled_at_vertex (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : LeanBridges.Geometry.Triangle P Q R) (hH5 : EuclideanGeometry.angle P R Q = (90 : ℝ) * Real.pi / 180) :
    (LeanBridges.Geometry.Triangle P Q R ∧ (R = P ∧ EuclideanGeometry.angle Q P R = Real.pi / 2 ∨ R = Q ∧ EuclideanGeometry.angle P Q R = Real.pi / 2 ∨ R = R ∧ EuclideanGeometry.angle P R Q = Real.pi / 2)) := by
  -- 1. mun:geometry-right-angled-at-vertex, from H4, H5
  exact ((Parley.Items.Stdlib.Geometry.mun_right_angled_at_vertex (P := P) (Q := Q) (R := R))).mpr ⟨hH4, hH5⟩

end Parley.Tests.Stdlib.Geometry.RightAngledAtVertex
