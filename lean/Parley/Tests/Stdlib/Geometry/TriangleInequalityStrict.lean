module

public import Geometry
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Parley.Stdlib.Geometry.TriangleInequalityStrict

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.TriangleInequalityStrict

theorem triangle_inequality_strict (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : LeanBridges.Geometry.Triangle P Q R) :
    dist P R < dist P Q + dist Q R := by
  -- 1. thm:geometry-triangle-inequality-strict, from H4
  exact (Parley.Stdlib.Geometry.TriangleInequalityStrict.triangle_inequality_strict (P := P) (Q := Q) (R := R) hH4)

end Parley.Tests.Stdlib.Geometry.TriangleInequalityStrict
