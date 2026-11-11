module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainGoingUp

theorem a_chain_going_up (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a ≤ b) (hH5 : b < c) :
    a < c := by
  -- 1. transitivity, from H4, H5
  exact lt_of_le_of_lt hH4 hH5

end Parley.Tests.Elaborator.Transitivity.AChainGoingUp
