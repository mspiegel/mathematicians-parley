module

public import Parley.Library

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineUsingALine

theorem a_chain_line_using_a_line (a : ℝ) (b : ℝ) (H3 : a = 2 * b) :
    3 * a + 1 = 1 + 6 * b := by
  -- 1. calculation
  have s1 : 3 * a + 1 = 1 + 6 * b := by
    calc 3 * a + 1 = 6 * b + 1 := by linear_combination (3) * H3
      _ = 1 + 6 * b := by ring
  parley_side

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineUsingALine
