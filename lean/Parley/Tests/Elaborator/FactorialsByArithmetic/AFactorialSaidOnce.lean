module

public import Parley.Library

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialSaidOnce

theorem a_factorial_said_once (x : ℝ) :
    x * (Nat.factorial 0 : ℝ) = (Nat.factorial 0 : ℝ) * x := by
  -- 1. algebra
  have s1 : x * (Nat.factorial 0 : ℝ) = (Nat.factorial 0 : ℝ) * x := by ring
  parley_side

end Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialSaidOnce
