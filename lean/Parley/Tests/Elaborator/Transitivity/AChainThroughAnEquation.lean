module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainThroughAnEquation

theorem a_chain_through_an_equation (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : b = a) (hH5 : b ≤ c) :
    c ≥ a := by
  -- 1. transitivity, from H4, H5
  exact Eq.trans_le hH4.symm hH5

end Parley.Tests.Elaborator.Transitivity.AChainThroughAnEquation
