module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
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
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-value-at-a-point-said-once.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AValueAtAPointSaidOnce.AnItemAtAValue

theorem an_item_at_a_value (a : ℤ → ℝ) (n : ℤ) (hH2 : 0 < n) :
    True := by
  -- 1. mun:abs-real x := a(n), from H1
  exact trivial

end Parley.Tests.Elaborator.AValueAtAPointSaidOnce.AnItemAtAValue
