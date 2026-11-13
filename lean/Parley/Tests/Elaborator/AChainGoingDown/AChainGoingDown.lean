module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/a-chain-going-down.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainGoingDown.AChainGoingDown

theorem a_chain_going_down (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a ≥ b) (hH5 : b > c) (hH6 : c = 2) :
    a > 2 := by
  -- 1. calculation
  calc a ≥ b := hH4
    _ > c := hH5
    _ = 2 := hH6

end Parley.Tests.Elaborator.AChainGoingDown.AChainGoingDown
