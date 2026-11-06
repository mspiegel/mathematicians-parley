module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainCitedInItsOwnOrder

theorem a_chain_cited_in_its_own_order (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : b < c) (hH5 : a ≤ b) :
    a < c := by
  -- 1. transitivity, from H5, H4
  have s1 : a < c := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.Transitivity.AChainCitedInItsOwnOrder
