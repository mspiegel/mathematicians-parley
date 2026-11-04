module

public import ArithTactics
public import Tactics

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.ProductOverARange

theorem product_over_a_range :
    (∏ k ∈ Finset.Icc (0 : ℤ) (3 : ℤ), (7 - k : ℤ)) ≤ 840 := by
  -- 1. arithmetic
  have s1 : (∏ k ∈ Finset.Icc (0 : ℤ) (3 : ℤ), (7 - k : ℤ)) ≤ 840 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.LargeArithmetic.ProductOverARange
