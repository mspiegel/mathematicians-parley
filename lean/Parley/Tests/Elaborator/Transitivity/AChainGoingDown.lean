module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainGoingDown

theorem a_chain_going_down (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : c > b) (hH5 : b ≥ a) :
    c > a := by
  -- 1. transitivity, from H4, H5
  exact lt_of_le_of_lt hH5 hH4

end Parley.Tests.Elaborator.Transitivity.AChainGoingDown
