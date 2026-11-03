module

public import Tactics

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineUsingALine

theorem a_chain_line_using_a_line (a : ℝ) (b : ℝ) (hH3 : a = 2 * b) :
    3 * a + 1 = 1 + 6 * b := by
  -- 1. calculation
  have s1 : 3 * a + 1 = 1 + 6 * b := by
    calc 3 * a + 1 = 6 * b + 1 := by linear_combination (norm := parley_norm) (3) * hH3
      _ = 1 + 6 * b := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineUsingALine
