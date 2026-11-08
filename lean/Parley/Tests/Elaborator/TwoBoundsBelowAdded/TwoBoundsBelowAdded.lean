module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/two-bounds-below-added.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TwoBoundsBelowAdded.TwoBoundsBelowAdded

theorem two_bounds_below_added (x : ℝ) (hH2 : x ≥ 4) (hH3 : x ≥ 0) :
    x + x ≥ 4 := by
  -- 1. inequalities, from H2, H3
  parley_order

end Parley.Tests.Elaborator.TwoBoundsBelowAdded.TwoBoundsBelowAdded
