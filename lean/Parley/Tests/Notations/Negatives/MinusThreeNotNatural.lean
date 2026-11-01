module

public import Parley.Library

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusThreeNotNatural

theorem minus_three_not_natural :
    ¬ 0 ≤ -3 := by
  -- 1. arithmetic
  have s1 : ¬ 0 ≤ -3 := by norm_num
  parley_side

end Parley.Tests.Notations.Negatives.MinusThreeNotNatural
