module

public import Parley.Library

/-! Written from tests/elaborator/a-divisor-negating-a-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADivisorNegatingAQuotient.AnAbsoluteValueOverItsNegation

theorem an_absolute_value_over_its_negation (p : ℝ) (H2 : |p / 2| = p / 2) (H3 : |-(p / 2)| = |p / 2|) (H4 : -(p / 2) ≠ 0) :
    |-(p / 2)| / -(p / 2) = -1 := by
  -- 1. algebra, from H2, H3
  have r22_1 : -(p / 2) ≠ 0 := by parley_side
  have s1 : |-(p / 2)| / -(p / 2) = -1 := by linear_combination (norm := parley_field) ((4) / ((-p) * (2))) * H2 + ((2) / ((-p))) * H3
  all_goals parley_side

end Parley.Tests.Elaborator.ADivisorNegatingAQuotient.AnAbsoluteValueOverItsNegation
