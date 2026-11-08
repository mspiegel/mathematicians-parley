module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfASum

theorem a_factorial_of_a_sum :
    (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = 2 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfASum
