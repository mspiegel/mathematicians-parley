module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainCitedInItsOwnOrder

theorem a_chain_cited_in_its_own_order (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : b < c) (hH5 : a ≤ b) :
    a < c := by
  -- 1. transitivity, from H5, H4
  parley_order

end Parley.Tests.Elaborator.Transitivity.AChainCitedInItsOwnOrder
