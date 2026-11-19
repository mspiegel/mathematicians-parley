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

namespace Parley.Tests.Stdlib.Geometry.OffLineThrough

theorem off_line_through (R : ℂ) (P : ℂ) (S : ℂ) (X : ℂ) (hH5 : ¬ S ∈ LeanBridges.Geometry.line R P) (hH6 : X ∈ LeanBridges.Geometry.line R S) (hH7 : X ≠ R) :
    ¬ X ∈ LeanBridges.Geometry.line R P := by
  -- 1. mun:geometry-off-line-through, from H5, H6, H7
  exact (Parley.Items.Stdlib.Geometry.mun_off_line_through (P := P) (R := R) (S := S) (X := X) hH5 hH6 hH7)

end Parley.Tests.Stdlib.Geometry.OffLineThrough
