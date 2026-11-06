module

public import AlgebraTactics
public import Tactics
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/inequality-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InequalityRows.ADivisorNotZeroByWeakening

theorem a_divisor_not_zero_by_weakening (p : ℝ) (q : ℝ) (hH3 : q > 0) :
    p / q * q = p := by
  -- 1. algebra
  have r50_1 : q ≠ 0 := by parley_side
  have s1 : p / q * q = p := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.InequalityRows.ADivisorNotZeroByWeakening
