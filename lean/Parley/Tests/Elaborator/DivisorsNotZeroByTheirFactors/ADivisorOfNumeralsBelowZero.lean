module

public import Parley.Library

/-! Written from tests/elaborator/divisors-not-zero-by-their-factors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.ADivisorOfNumeralsBelowZero

theorem a_divisor_of_numerals_below_zero (c : ℤ) (x : ℝ) :
    x * (((c : ℝ) - (c : ℝ)) / (2 - 5)) = ((c : ℝ) - (c : ℝ)) / (2 - 5) * x := by
  -- 1. algebra
  have s1 : x * (((c : ℝ) - (c : ℝ)) / (2 - 5)) = ((c : ℝ) - (c : ℝ)) / (2 - 5) * x := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.DivisorsNotZeroByTheirFactors.ADivisorOfNumeralsBelowZero
