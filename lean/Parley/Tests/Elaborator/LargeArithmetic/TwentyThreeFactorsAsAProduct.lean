module

public import ArithTactics
public import Tactics

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.TwentyThreeFactorsAsAProduct

theorem twenty_three_factors_as_a_product :
    2 * (∏ k ∈ Finset.Icc (0 : ℤ) (22 : ℤ), (365 - k : ℤ)) < 365 ^ 23 := by
  -- 1. arithmetic
  have s1 : 2 * (∏ k ∈ Finset.Icc (0 : ℤ) (22 : ℤ), (365 - k : ℤ)) < 365 ^ 23 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.LargeArithmetic.TwentyThreeFactorsAsAProduct
