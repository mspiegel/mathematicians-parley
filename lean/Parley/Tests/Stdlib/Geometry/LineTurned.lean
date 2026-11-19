module

public import Geometry
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
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

namespace Parley.Tests.Stdlib.Geometry.LineTurned

theorem line_turned (A : ℂ) (B : ℂ) :
    LeanBridges.Geometry.line A B = LeanBridges.Geometry.line B A := by
  -- 1. mun:geometry-line-turned
  exact (Parley.Items.Stdlib.Geometry.mun_line_turned (A := A) (B := B))

end Parley.Tests.Stdlib.Geometry.LineTurned
