module

public import Parley.Library

/-! Written from tests/elaborator/a-chain-going-down.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainGoingDown.AChainGoingDown

theorem a_chain_going_down (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a ≥ b) (hH5 : b > c) (hH6 : c = 2) :
    a > 2 := by
  -- 1. calculation
  have s1 : a > 2 := by
    calc a ≥ b := by parley_side
      _ > c := by parley_side
      _ = 2 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.AChainGoingDown.AChainGoingDown
