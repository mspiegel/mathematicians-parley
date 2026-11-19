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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.Line

theorem line (P : ℂ) (A : ℂ) (B : ℂ) (hH4 : P ∈ LeanBridges.Geometry.line A B) (hH5 : A ≠ B) :
    P ∈ LeanBridges.Geometry.line A B := by
  -- 1. def:geometry-line, from H4, H5
  exact ((Parley.Items.Stdlib.Geometry.def_line (P := P) (A := A) (B := B) hH5)).mpr hH4

end Parley.Tests.Stdlib.Geometry.Line
