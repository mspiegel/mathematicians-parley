module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.ParallelAlong

theorem parallel_along (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (E : ℂ) (hH6 : Complex.im ((B - A) / (D - C)) = 0) (hH7 : A ≠ B) (hH8 : E ∈ LeanBridges.Geometry.line A B) (hH9 : E ≠ A) :
    Complex.im ((E - A) / (C - D)) = 0 := by
  -- 1. mun:geometry-parallel-along, from H6, H7, H8, H9
  exact (Parley.Items.Stdlib.Geometry.mun_parallel_along (A := A) (B := B) (C := C) (D := D) (E := E) hH6 hH7 hH8 hH9)

end Parley.Tests.Stdlib.Geometry.ParallelAlong
