module

public import Parley.Items.Stdlib.Reasoning
public import Parley.Library

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.DoubleNegation

theorem double_negation (x : ℝ) (hH2 : ¬ x ≠ 0) :
    x = 0 := by
  -- 1. mun:reasoning-double-negation P := x = 0, from H2
  have s1 : x = 0 := by linear_combination (Parley.Items.Stdlib.Reasoning.mun_double_negation (P := x = 0) (by parley_side))
  all_goals parley_side

end Parley.Tests.Stdlib.Reasoning.DoubleNegation
