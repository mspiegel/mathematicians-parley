module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-map-applied.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMapApplied.AValueAssumed

theorem a_value_assumed (f : ℝ → ℝ) (x : ℝ) (hH3 : f x = 3) :
    f x = 3 := by
  -- 1. restate H3
  exact hH3

end Parley.Tests.Elaborator.AMapApplied.AValueAssumed
