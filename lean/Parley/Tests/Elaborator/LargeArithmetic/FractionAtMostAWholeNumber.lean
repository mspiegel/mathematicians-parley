module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Rat.Init

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.FractionAtMostAWholeNumber

theorem fraction_at_most_a_whole_number :
    ((3 + 4) / 2 : ℚ) ≤ 2 ^ 2 := by
  -- 1. arithmetic
  have s1 : ((3 + 4) / 2 : ℚ) ≤ 2 ^ 2 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.LargeArithmetic.FractionAtMostAWholeNumber
