module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialSaidOnce

theorem a_factorial_said_once (x : ℝ) :
    x * (LeanBridges.Counting.factorial (0 : ℤ) : ℝ) = (LeanBridges.Counting.factorial (0 : ℤ) : ℝ) * x := by
  -- 1. algebra
  have s1 : x * (LeanBridges.Counting.factorial (0 : ℤ) : ℝ) = (LeanBridges.Counting.factorial (0 : ℤ) : ℝ) * x := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialSaidOnce
