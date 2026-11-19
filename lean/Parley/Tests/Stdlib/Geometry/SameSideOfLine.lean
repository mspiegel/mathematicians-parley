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
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.SameSideOfLine

theorem same_side_of_line (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (P : ℂ) (Q : ℂ) (hH7 : A ≠ B) (hH8 : C ≠ D) (hH9 : C ∈ LeanBridges.Geometry.line A B) (hH10 : D ∈ LeanBridges.Geometry.line A B) (hH11 : 0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A))) :
    0 < Complex.im ((P - C) / (D - C)) * Complex.im ((Q - C) / (D - C)) := by
  -- 1. mun:geometry-same-side-of-line, from H7, H8, H9, H10, H11
  exact (Parley.Items.Stdlib.Geometry.mun_same_side_of_line (A := A) (B := B) (C := C) (D := D) (P := P) (Q := Q) hH7 hH8 hH9 hH10 hH11)

end Parley.Tests.Stdlib.Geometry.SameSideOfLine
