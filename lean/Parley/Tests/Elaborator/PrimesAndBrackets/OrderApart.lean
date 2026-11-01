module

public import Parley.Library

/-! Written from tests/elaborator/primes-and-brackets.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PrimesAndBrackets.OrderApart

theorem order_apart (a : ℝ) (b : ℝ) (H3 : a < b) :
    b - a ≠ 0 := by
  -- 1. inequalities
  have s1 : b - a ≠ 0 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.PrimesAndBrackets.OrderApart
