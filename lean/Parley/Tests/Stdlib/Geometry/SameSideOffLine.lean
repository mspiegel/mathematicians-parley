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

namespace Parley.Tests.Stdlib.Geometry.SameSideOffLine

theorem same_side_off_line (A : ℂ) (B : ℂ) (P : ℂ) (Q : ℂ) (hH5 : 0 < Complex.im ((P - A) / (B - A)) * Complex.im ((Q - A) / (B - A))) :
    A ≠ B ∧ ¬ P ∈ LeanBridges.Geometry.line A B ∧ ¬ Q ∈ LeanBridges.Geometry.line A B := by
  -- 1. mun:geometry-same-side-off-line, from H5
  have s1a : A ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_1 (A := A) (B := B) (P := P) (Q := Q) hH5)
  have s1b : ¬ P ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_2 (A := A) (B := B) (P := P) (Q := Q) hH5)
  have s1c : ¬ Q ∈ LeanBridges.Geometry.line A B := by exact (Parley.Items.Stdlib.Geometry.mun_same_side_off_line_3 (A := A) (B := B) (P := P) (Q := Q) hH5)
  exact ⟨s1a, s1b, s1c⟩

end Parley.Tests.Stdlib.Geometry.SameSideOffLine
