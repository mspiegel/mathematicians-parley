module

public import Geometry
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.TriangleNotOnLine

theorem triangle_not_on_line (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : LeanBridges.Geometry.Triangle P Q R) :
    ¬ P ∈ LeanBridges.Geometry.line Q R := by
  -- 1. mun:geometry-triangle-not-on-line, from H4
  exact (Parley.Items.Stdlib.Geometry.mun_triangle_not_on_line (P := P) (Q := Q) (R := R) hH4)

end Parley.Tests.Stdlib.Geometry.TriangleNotOnLine
