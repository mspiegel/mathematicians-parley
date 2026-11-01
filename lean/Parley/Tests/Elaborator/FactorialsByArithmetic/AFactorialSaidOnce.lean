module

public import Parley.Library

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialSaidOnce

theorem a_factorial_said_once (x : ℝ) :
    x * (Parley.Library.factorial (0 : ℤ) : ℝ) = (Parley.Library.factorial (0 : ℤ) : ℝ) * x := by
  -- 1. algebra
  have s1 : x * (Parley.Library.factorial (0 : ℤ) : ℝ) = (Parley.Library.factorial (0 : ℤ) : ℝ) * x := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialSaidOnce
