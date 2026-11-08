module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.RemainderOfASmallNumber

theorem remainder_of_a_small_number :
    (4 : ℤ) % (7 : ℤ) = 4 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Elaborator.LargeArithmetic.RemainderOfASmallNumber
