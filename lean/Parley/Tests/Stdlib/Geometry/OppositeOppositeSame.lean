module

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

namespace Parley.Tests.Stdlib.Geometry.OppositeOppositeSame

theorem opposite_opposite_same (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (R : ℂ) (hH6 : Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0) (hH7 : Complex.im ((Q - A) / (B - A)) * Complex.im ((R - A) / (B - A)) < 0) :
    0 < Complex.im ((P - A) / (B - A)) * Complex.im ((R - A) / (B - A)) := by
  -- 1. mun:geometry-opposite-opposite-same, from H6, H7
  exact (Parley.Items.Stdlib.Geometry.mun_opposite_opposite_same (A := A) (B := B) (P := P) (Q := Q) (R := R) hH6 hH7)

end Parley.Tests.Stdlib.Geometry.OppositeOppositeSame
