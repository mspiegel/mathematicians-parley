module

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
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.MaxLe

theorem max_le (x : ℝ) (y : ℝ) (z : ℝ) :
    (max x y ≤ z ↔ x ≤ z ∧ y ≤ z) := by
  -- 1. mun:numbers-max-le
  exact (Parley.Items.Stdlib.Numbers.mun_max_le (x := x) (y := y) (z := z))

end Parley.Tests.Stdlib.Numbers.MaxLe
