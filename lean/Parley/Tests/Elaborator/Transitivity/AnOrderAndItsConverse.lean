module

public import Parley.Library

/-! Written from tests/elaborator/transitivity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Transitivity.AnOrderAndItsConverse

theorem an_order_and_its_converse (a : ℝ) (b : ℝ) (H3 : a ≤ b) (H4 : a ≥ b) :
    b = a := by
  -- 1. antisymmetry, from H3, H4
  have s1 : b = a := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.Transitivity.AnOrderAndItsConverse
