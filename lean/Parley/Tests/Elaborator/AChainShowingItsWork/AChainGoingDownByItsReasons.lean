module

public import Parley.Library

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainGoingDownByItsReasons

theorem a_chain_going_down_by_its_reasons (a : ℝ) (hH2 : a ≥ 3) :
    a + a ≥ 6 := by
  -- 1. inequalities
  have s1 : 2 * a ≥ 6 := by parley_side
  -- 2. calculation
  have s2 : a + a ≥ 6 := by
    calc a + a = 2 * a := by parley_ring
      _ ≥ 6 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainGoingDownByItsReasons
