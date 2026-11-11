module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainThroughAnEquation

theorem a_chain_through_an_equation (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : b = a) (hH5 : b ≤ c) :
    c ≥ a := by
  -- 1. transitivity, from H4, H5
  exact Eq.trans_le hH4.symm hH5

end Parley.Tests.Elaborator.Transitivity.AChainThroughAnEquation
