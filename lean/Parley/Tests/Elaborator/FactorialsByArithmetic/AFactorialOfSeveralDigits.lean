module

public import Counting
public import FactorialTactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfSeveralDigits

theorem a_factorial_of_several_digits :
    (LeanBridges.Counting.factorial (12 : ℤ) : ℤ) = 479001600 := by
  -- 1. arithmetic
  norm_num [Nat.factorial]

end Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfSeveralDigits
