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

namespace Parley.Tests.Stdlib.Geometry.RaySideTransfer

theorem ray_side_transfer (R : ℂ) (P : ℂ) (S : ℂ) (Q : ℂ) (X : ℂ) (hH6 : X ∈ LeanBridges.Geometry.line R P) (hH7 : 0 < Complex.im ((X - R) / (S - R)) * Complex.im ((P - R) / (S - R))) (hH8 : R ≠ Q) (hH9 : ¬ P ∈ LeanBridges.Geometry.line R Q) :
    0 < Complex.im ((X - R) / (Q - R)) * Complex.im ((P - R) / (Q - R)) := by
  -- 1. mun:geometry-ray-side-transfer, from H6, H7, H8, H9
  exact (Parley.Items.Stdlib.Geometry.mun_ray_side_transfer (P := P) (Q := Q) (R := R) (S := S) (X := X) hH6 hH7 hH8 hH9)

end Parley.Tests.Stdlib.Geometry.RaySideTransfer
