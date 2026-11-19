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

namespace Parley.Tests.Stdlib.Geometry.OffLineApart

theorem off_line_apart (A : ℂ) (B : ℂ) (P : ℂ) (hH4 : A ≠ B) (hH5 : ¬ P ∈ LeanBridges.Geometry.line A B) :
    P ≠ A ∧ P ≠ B := by
  -- 1. mun:geometry-off-line-apart, from H4, H5
  have s1a : P ≠ A := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_1 (A := A) (B := B) (P := P) hH4 hH5)
  have s1b : P ≠ B := by exact (Parley.Items.Stdlib.Geometry.mun_off_line_apart_2 (A := A) (B := B) (P := P) hH4 hH5)
  exact ⟨s1a, s1b⟩

end Parley.Tests.Stdlib.Geometry.OffLineApart
