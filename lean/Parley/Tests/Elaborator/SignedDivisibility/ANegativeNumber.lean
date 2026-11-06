module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.ANegativeNumber

theorem a_negative_number :
    (2 : ℤ) ∣ (-8 : ℤ) := by
  -- 1. arithmetic
  have s1 : (2 : ℤ) ∣ (-8 : ℤ) := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.SignedDivisibility.ANegativeNumber
