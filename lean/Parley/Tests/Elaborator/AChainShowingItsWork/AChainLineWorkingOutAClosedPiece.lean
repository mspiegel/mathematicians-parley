module

public import AlgebraTactics
public import RealTactics
public import Tactics

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineWorkingOutAClosedPiece

theorem a_chain_line_working_out_a_closed_piece (x : ℝ) :
    x * Real.sqrt (4 : ℝ) = 2 * x := by
  -- 1. calculation
  have s1 : x * Real.sqrt (4 : ℝ) = 2 * x := by
    calc x * Real.sqrt (4 : ℝ) = x * 2 := by parley_real
      _ = 2 * x := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineWorkingOutAClosedPiece
