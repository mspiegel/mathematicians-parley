module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainGoingDown

theorem a_chain_going_down (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : c > b) (hH5 : b ≥ a) :
    c > a := by
  -- 1. transitivity, from H4, H5
  have s1 : c > a := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.Transitivity.AChainGoingDown
