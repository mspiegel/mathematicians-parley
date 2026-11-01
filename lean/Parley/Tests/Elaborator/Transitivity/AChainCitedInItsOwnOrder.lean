module

public import Parley.Library

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainCitedInItsOwnOrder

theorem a_chain_cited_in_its_own_order (a : ℝ) (b : ℝ) (c : ℝ) (H4 : b < c) (H5 : a ≤ b) :
    a < c := by
  -- 1. transitivity, from H5, H4
  have s1 : a < c := by parley_side
  parley_side

end Parley.Tests.Elaborator.Transitivity.AChainCitedInItsOwnOrder
