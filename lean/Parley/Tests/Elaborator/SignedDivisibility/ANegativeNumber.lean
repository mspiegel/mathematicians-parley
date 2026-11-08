module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.DivMod

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.ANegativeNumber

theorem a_negative_number :
    (2 : ℤ) ∣ (-8 : ℤ) := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Elaborator.SignedDivisibility.ANegativeNumber
