module

public import Parley.Library

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainGoingDown

theorem a_chain_going_down (a : ℝ) (b : ℝ) (c : ℝ) (H4 : c > b) (H5 : b ≥ a) :
    c > a := by
  -- 1. transitivity, from H4, H5
  have s1 : c > a := by parley_side
  parley_side

end Parley.Tests.Elaborator.Transitivity.AChainGoingDown
