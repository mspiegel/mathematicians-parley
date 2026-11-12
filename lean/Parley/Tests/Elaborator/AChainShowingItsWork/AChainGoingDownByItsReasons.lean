module

public import AlgebraTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-chain-showing-its-work.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainShowingItsWork.AChainGoingDownByItsReasons

theorem a_chain_going_down_by_its_reasons (a : ℝ) (hH2 : a ≥ 3) :
    a + a ≥ 6 := by
  -- 1. inequalities
  have s1 : 2 * a ≥ 6 := by linarith only [hH2]
  -- 2. calculation
  calc a + a = 2 * a := by parley_ring
    _ ≥ 6 := by exact s1

end Parley.Tests.Elaborator.AChainShowingItsWork.AChainGoingDownByItsReasons
