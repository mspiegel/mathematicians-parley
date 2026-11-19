module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.AreaCongruent

theorem area_congruent (P : ℂ) (Q : ℂ) (R : ℂ) (P' : ℂ) (Q' : ℂ) (R' : ℂ) (hH7 : LeanBridges.Geometry.Triangle P Q R) (hH8 : LeanBridges.Geometry.Triangle P' Q' R') (hH9 : dist P Q = dist P' Q' ∧ dist Q R = dist Q' R' ∧ dist R P = dist R' P' ∧ EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R' ∧ EuclideanGeometry.angle Q R P = EuclideanGeometry.angle Q' R' P' ∧ EuclideanGeometry.angle R P Q = EuclideanGeometry.angle R' P' Q') :
    1 / 2 * (dist Q R * dist P R) * abs (Real.sin (Complex.arg ((P - R) / (Q - R)))) = 1 / 2 * (dist Q' R' * dist P' R') * abs (Real.sin (Complex.arg ((P' - R') / (Q' - R')))) := by
  -- 1. axi:geometry-area-congruent, from H7, H8, H9
  exact (Parley.Items.Stdlib.Geometry.axi_area_congruent (P := P) (P' := P') (Q := Q) (Q' := Q') (R := R) (R' := R') hH7 hH8 hH9)

end Parley.Tests.Stdlib.Geometry.AreaCongruent
