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

namespace Parley.Tests.Stdlib.Geometry.TriangleOffLine

theorem triangle_off_line (P : ℂ) (Q : ℂ) (R : ℂ) (hH4 : Q ≠ R) (hH5 : ¬ P ∈ LeanBridges.Geometry.line Q R) :
    LeanBridges.Geometry.Triangle P Q R := by
  -- 1. mun:geometry-triangle-off-line, from H4, H5
  exact (Parley.Items.Stdlib.Geometry.mun_triangle_off_line (P := P) (Q := Q) (R := R) hH4 hH5)

end Parley.Tests.Stdlib.Geometry.TriangleOffLine
