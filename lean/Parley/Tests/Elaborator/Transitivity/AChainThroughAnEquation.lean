module

public import Tactics

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainThroughAnEquation

theorem a_chain_through_an_equation (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : b = a) (hH5 : b ≤ c) :
    c ≥ a := by
  -- 1. transitivity, from H4, H5
  have s1 : c ≥ a := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.Transitivity.AChainThroughAnEquation
