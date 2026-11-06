module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.ASideWorkedBelowZero

theorem a_side_worked_below_zero :
    (4 : ℤ) ∣ (3 - 11 : ℤ) := by
  -- 1. arithmetic
  have s1 : (4 : ℤ) ∣ (3 - 11 : ℤ) := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.SignedDivisibility.ASideWorkedBelowZero
