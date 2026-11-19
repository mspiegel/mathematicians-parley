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
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.CongruentBySymbol

theorem congruent_by_symbol (P : ℂ) (Q : ℂ) (R : ℂ) (P' : ℂ) (Q' : ℂ) (R' : ℂ) (hH7 : dist P Q = dist P' Q' ∧ dist Q R = dist Q' R' ∧ dist R P = dist R' P' ∧ EuclideanGeometry.angle P Q R = EuclideanGeometry.angle P' Q' R' ∧ EuclideanGeometry.angle Q R P = EuclideanGeometry.angle Q' R' P' ∧ EuclideanGeometry.angle R P Q = EuclideanGeometry.angle R' P' Q') (hH8 : LeanBridges.Geometry.Triangle P Q R) (hH9 : LeanBridges.Geometry.Triangle P' Q' R') :
    dist P Q = dist P' Q' := by
  -- 1. def:geometry-congruent, from H7, H8, H9
  exact (((Parley.Items.Stdlib.Geometry.def_congruent (P := P) (P' := P') (Q := Q) (Q' := Q') (R := R) (R' := R') hH8 hH9)).mp hH7).1.1.1.1.1

end Parley.Tests.Stdlib.Geometry.CongruentBySymbol
