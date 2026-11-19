module

public import Geometry
public import Mathlib.Algebra.Order.Field.Basic
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
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Geometry

/-! Written from tests/stdlib/geometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Geometry.Parallel

theorem parallel (A : ℂ) (B : ℂ) (C : ℂ) (D : ℂ) (hH5 : A ≠ B) (hH6 : C ≠ D) (hH7 : Complex.im ((B - A) / (D - C)) = 0) :
    (LeanBridges.Geometry.line A B = LeanBridges.Geometry.line C D ∨ ¬ (∃ X ∈ (Set.univ : Set ℂ), X ∈ LeanBridges.Geometry.line A B ∧ X ∈ LeanBridges.Geometry.line C D)) := by
  -- 1. def:geometry-parallel, from H5, H6, H7
  exact ((Parley.Items.Stdlib.Geometry.def_parallel (A := A) (B := B) (C := C) (D := D) hH5 hH6)).mp hH7

end Parley.Tests.Stdlib.Geometry.Parallel
