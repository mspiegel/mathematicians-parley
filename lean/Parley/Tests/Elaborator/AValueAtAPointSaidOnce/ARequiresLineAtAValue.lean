module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-value-at-a-point-said-once.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AValueAtAPointSaidOnce.ARequiresLineAtAValue

theorem a_requires_line_at_a_value (a : ℤ → ℝ) (n : ℕ) (hH2 : 0 < n) (L : ℝ) :
    True := by
  -- 1. mun:abs-real x := a(n) − L
  all_goals parley_side

end Parley.Tests.Elaborator.AValueAtAPointSaidOnce.ARequiresLineAtAValue
