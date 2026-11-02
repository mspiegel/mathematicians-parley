module

public import LeanBridges

/-! Written from tests/elaborator/a-chain-going-down.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainGoingDown.AChainGoingDownFromAnEquation

theorem a_chain_going_down_from_an_equation (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a = b) (hH5 : b ≥ c) :
    a ≥ c := by
  -- 1. calculation
  have s1 : a ≥ c := by
    calc a = b := by parley_side
      _ ≥ c := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.AChainGoingDown.AChainGoingDownFromAnEquation
