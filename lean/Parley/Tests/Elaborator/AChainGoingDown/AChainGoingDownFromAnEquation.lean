module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-chain-going-down.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AChainGoingDown.AChainGoingDownFromAnEquation

theorem a_chain_going_down_from_an_equation (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a = b) (hH5 : b ≥ c) :
    a ≥ c := by
  -- 1. calculation
  calc a = b := hH4
    _ ≥ c := hH5

end Parley.Tests.Elaborator.AChainGoingDown.AChainGoingDownFromAnEquation
