module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.CosBounded

theorem cos_bounded (a : ℝ) :
    -1 ≤ Real.cos a ∧ Real.cos a ≤ 1 := by
  -- 1. mun:trigonometry-cos-bounded
  have s1a : -1 ≤ Real.cos a := by exact (Parley.Items.Stdlib.Trigonometry.mun_cos_bounded_1 (a := a))
  have s1b : Real.cos a ≤ 1 := by exact (Parley.Items.Stdlib.Trigonometry.mun_cos_bounded_2 (a := a))
  exact ⟨s1a, s1b⟩

end Parley.Tests.Stdlib.Trigonometry.CosBounded
