module

public import ArithTactics
public import Tactics

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.AProductOverARangeWorkedOut

theorem a_product_over_a_range_worked_out :
    (∏ k ∈ Finset.Icc (1 : ℤ) (4 : ℤ), (k : ℤ)) = 24 := by
  -- 1. arithmetic
  have s1 : (∏ k ∈ Finset.Icc (1 : ℤ) (4 : ℤ), (k : ℤ)) = 24 := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Sums.AProductOverARangeWorkedOut
