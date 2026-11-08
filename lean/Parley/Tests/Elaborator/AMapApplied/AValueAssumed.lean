module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/a-map-applied.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMapApplied.AValueAssumed

theorem a_value_assumed (f : ℝ → ℝ) (x : ℝ) (hH3 : f x = 3) :
    f x = 3 := by
  -- 1. restate H3
  parley_side

end Parley.Tests.Elaborator.AMapApplied.AValueAssumed
