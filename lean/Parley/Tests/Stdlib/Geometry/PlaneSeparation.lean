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

namespace Parley.Tests.Stdlib.Geometry.PlaneSeparation

theorem plane_separation (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (hH5 : A ≠ B) (hH6 : ¬ P ∈ LeanBridges.Geometry.line A B) (hH7 : ¬ Q ∈ LeanBridges.Geometry.line A B) :
    (0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) ∨ Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A)) < 0) := by
  -- 1. axi:geometry-plane-separation, from H5, H6, H7
  exact (Parley.Items.Stdlib.Geometry.axi_plane_separation (A := A) (B := B) (P := P) (Q := Q) hH5 hH6 hH7)

end Parley.Tests.Stdlib.Geometry.PlaneSeparation
