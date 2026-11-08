module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.ANegativeDivisor

theorem a_negative_divisor :
    (-3 : ℤ) ∣ (9 : ℤ) := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Elaborator.SignedDivisibility.ANegativeDivisor
