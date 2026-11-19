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

namespace Parley.Tests.Stdlib.Geometry.LineUniqueness

theorem line_uniqueness (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (hH5 : A ≠ B) (hH6 : C ≠ D) (hH7 : A ∈ LeanBridges.Geometry.line C D) (hH8 : B ∈ LeanBridges.Geometry.line C D) :
    LeanBridges.Geometry.line A B = LeanBridges.Geometry.line C D := by
  -- 1. axi:geometry-line-uniqueness, from H5, H6, H7, H8
  exact (Parley.Items.Stdlib.Geometry.axi_line_uniqueness (A := A) (B := B) (C := C) (D := D) hH5 hH6 hH7 hH8)

end Parley.Tests.Stdlib.Geometry.LineUniqueness
