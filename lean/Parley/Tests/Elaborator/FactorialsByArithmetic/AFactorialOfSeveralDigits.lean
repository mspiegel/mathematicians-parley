module

public import ArithTactics
public import Counting
public import FactorialTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfSeveralDigits

theorem a_factorial_of_several_digits :
    (LeanBridges.Counting.factorial (12 : ℤ) : ℤ) = 479001600 := by
  -- 1. arithmetic
  have s1 : (LeanBridges.Counting.factorial (12 : ℤ) : ℤ) = 479001600 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfSeveralDigits
