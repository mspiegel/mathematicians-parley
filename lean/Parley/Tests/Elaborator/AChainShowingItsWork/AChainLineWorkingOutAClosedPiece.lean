module

public import AlgebraTactics
public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineWorkingOutAClosedPiece

theorem a_chain_line_working_out_a_closed_piece (x : ℝ) :
    x * Real.sqrt (4 : ℝ) = 2 * x := by
  -- 1. calculation
  calc x * Real.sqrt (4 : ℝ) = x * 2 := by parley_real
    _ = 2 * x := by parley_ring

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainLineWorkingOutAClosedPiece
