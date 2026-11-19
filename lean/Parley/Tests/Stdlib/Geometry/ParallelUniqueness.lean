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

namespace Parley.Tests.Stdlib.Geometry.ParallelUniqueness

theorem parallel_uniqueness (A : ℂ) (B : ℂ) (P : ℂ) (C : ℂ) (D : ℂ) (hH6 : A ≠ B) (hH7 : ¬ P ∈ LeanBridges.Geometry.line A B) (hH8 : P ≠ C) (hH9 : P ≠ D) (hH10 : Complex.im ((C - P) / (B - A)) = 0) (hH11 : Complex.im ((D - P) / (B - A)) = 0) :
    LeanBridges.Geometry.line P C = LeanBridges.Geometry.line P D := by
  -- 1. axi:geometry-parallel-uniqueness, from H6, H7, H8, H9, H10, H11
  exact (Parley.Items.Stdlib.Geometry.axi_parallel_uniqueness (A := A) (B := B) (C := C) (D := D) (P := P) hH6 hH7 hH8 hH9 hH10 hH11)

end Parley.Tests.Stdlib.Geometry.ParallelUniqueness
