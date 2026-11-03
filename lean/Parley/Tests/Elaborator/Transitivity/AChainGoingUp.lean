module

public import Tactics

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainGoingUp

theorem a_chain_going_up (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a ≤ b) (hH5 : b < c) :
    a < c := by
  -- 1. transitivity, from H4, H5
  have s1 : a < c := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.Transitivity.AChainGoingUp
