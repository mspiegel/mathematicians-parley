module

public import Parley.Library

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AChainGoingUp

theorem a_chain_going_up (a : ℝ) (b : ℝ) (c : ℝ) (H4 : a ≤ b) (H5 : b < c) :
    a < c := by
  -- 1. transitivity, from H4, H5
  have s1 : a < c := by linarith
  parley_side

end Parley.Tests.Elaborator.Transitivity.AChainGoingUp
