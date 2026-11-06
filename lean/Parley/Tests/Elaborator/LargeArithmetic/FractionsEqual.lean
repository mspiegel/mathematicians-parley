module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Rat.Init

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.FractionsEqual

theorem fractions_equal :
    (2 / 4 : ℚ) ≤ 3 / 6 := by
  -- 1. arithmetic
  have s1 : (2 / 4 : ℚ) ≤ 3 / 6 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.LargeArithmetic.FractionsEqual
