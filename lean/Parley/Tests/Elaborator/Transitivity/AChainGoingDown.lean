module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainGoingDown

theorem a_chain_going_down (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : c > b) (hH5 : b ≥ a) :
    c > a := by
  -- 1. transitivity, from H4, H5
  exact lt_of_le_of_lt hH5 hH4

end Parley.Tests.Elaborator.Transitivity.AChainGoingDown
