module

public import ArithTactics
public import Tactics

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusPlus

theorem minus_plus :
    (-3 + 5 : ℤ) = 2 := by
  -- 1. arithmetic
  have s1 : (-3 + 5 : ℤ) = 2 := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Negatives.MinusPlus
