module

public import Parley.Library

/-! Written from tests/elaborator/primes-and-brackets.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PrimesAndBrackets.PrimeName

theorem prime_name (c : ℝ) (c' : ℝ) (H3 : c' = c + 1) :
    c' - c = 1 := by
  -- 1. algebra, from H3
  have s1 : c' - c = 1 := by linear_combination H3
  parley_side

end Parley.Tests.Elaborator.PrimesAndBrackets.PrimeName
