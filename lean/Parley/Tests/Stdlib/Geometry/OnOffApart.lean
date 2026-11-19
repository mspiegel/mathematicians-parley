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

namespace Parley.Tests.Stdlib.Geometry.OnOffApart

theorem on_off_apart (A : ℂ) (B : ℂ) (X : ℂ) (Y : ℂ) (hH5 : X ∈ LeanBridges.Geometry.line A B) (hH6 : ¬ Y ∈ LeanBridges.Geometry.line A B) :
    X ≠ Y := by
  -- 1. mun:geometry-on-off-apart, from H5, H6
  exact (Parley.Items.Stdlib.Geometry.mun_on_off_apart (A := A) (B := B) (X := X) (Y := Y) hH5 hH6)

end Parley.Tests.Stdlib.Geometry.OnOffApart
